// Copyright © Aptos Foundation

use crate::{
    dag::{
        dag_driver::DagDriver,
        dag_fetcher::{FetchRequestHandler, FetchWaiter},
        dag_network::RpcHandler,
        dag_state_sync::{StateSyncTrigger, SyncOutcome},
        errors::{
            DAGError, DAGRpcError, DagDriverError, FetchRequestHandleError,
            NodeBroadcastHandleError,
        },
        rb_handler::NodeBroadcastHandler,
        types::{DAGMessage, DAGRpcResult},
        CertifiedNode, Node,
    },
    monitor,
    network::{IncomingDAGRequest, RpcResponder},
};
use aptos_bounded_executor::{concurrent_map, BoundedExecutor};
use aptos_channels::aptos_channel;
use aptos_consensus_types::common::{Author, Round};
use aptos_logger::{debug, error, warn};
use aptos_types::epoch_state::EpochState;
use futures::{stream::FuturesUnordered, StreamExt};
use std::sync::Arc;
use tokio::{runtime::Handle, select, task::block_in_place};

pub(crate) struct NetworkHandler {
    epoch_state: Arc<EpochState>,
    node_receiver: Arc<NodeBroadcastHandler>,
    dag_driver: Arc<DagDriver>,
    node_fetch_waiter: FetchWaiter<Node>,
    certified_node_fetch_waiter: FetchWaiter<CertifiedNode>,
    new_round_event: tokio::sync::mpsc::Receiver<Round>,
    verified_msg_processor: Arc<VerifiedMessageProcessor>,
}

impl NetworkHandler {
    pub(super) fn new(
        epoch_state: Arc<EpochState>,
        node_receiver: NodeBroadcastHandler,
        dag_driver: DagDriver,
        fetch_receiver: FetchRequestHandler,
        node_fetch_waiter: FetchWaiter<Node>,
        certified_node_fetch_waiter: FetchWaiter<CertifiedNode>,
        state_sync_trigger: StateSyncTrigger,
        new_round_event: tokio::sync::mpsc::Receiver<Round>,
    ) -> Self {
        let node_receiver = Arc::new(node_receiver);
        let dag_driver = Arc::new(dag_driver);
        Self {
            epoch_state: epoch_state.clone(),
            node_receiver: node_receiver.clone(),
            dag_driver: dag_driver.clone(),
            node_fetch_waiter,
            certified_node_fetch_waiter,
            new_round_event,
            verified_msg_processor: Arc::new(VerifiedMessageProcessor {
                node_receiver,
                dag_driver,
                fetch_receiver,
                state_sync_trigger,
                epoch_state,
            }),
        }
    }

    pub async fn run(
        self,
        dag_rpc_rx: &mut aptos_channel::Receiver<Author, IncomingDAGRequest>,
        executor: BoundedExecutor,
        _buffer: Vec<DAGMessage>,
    ) -> SyncOutcome {
        // TODO: process buffer
        let NetworkHandler {
            epoch_state,
            node_receiver,
            dag_driver,
            mut node_fetch_waiter,
            mut certified_node_fetch_waiter,
            mut new_round_event,
            verified_msg_processor,
            ..
        } = self;

        let mut verified_msg_stream = concurrent_map(
            dag_rpc_rx,
            executor.clone(),
            move |rpc_request: IncomingDAGRequest| {
                let epoch_state = epoch_state.clone();
                async move {
                    let result = rpc_request
                        .req
                        .try_into()
                        .and_then(|dag_message: DAGMessage| {
                            monitor!(
                                "dag_message_verify",
                                dag_message.verify(rpc_request.sender, &epoch_state.verifier)
                            )?;
                            Ok(dag_message)
                        });
                    (result, rpc_request.sender, rpc_request.responder)
                }
            },
        );

        let dag_driver_clone = dag_driver.clone();
        let node_receiver_clone = node_receiver.clone();
        let task1 = tokio::spawn(async move {
            loop {
                if let Some(new_round) = new_round_event.recv().await {
                    dag_driver_clone.enter_new_round(new_round).await;
                    node_receiver_clone.gc();
                }
            }
        });

        let node_receiver_clone = node_receiver.clone();
        let task2 = tokio::spawn(async move {
            loop {
                match node_fetch_waiter.select_next_some().await {
                    Ok(node) => {
                        if let Err(e) = node_receiver_clone.process(node).await {
                            warn!(error = ?e, "error processing node fetch notification");
                        }
                    },
                    Err(e) => {
                        debug!("sender dropped channel: {}", e);
                    },
                };
            }
        });

        let dag_driver_clone = dag_driver.clone();
        let task3 = tokio::spawn(async move {
            loop {
                match certified_node_fetch_waiter.select_next_some().await {
                    Ok(certified_node) => {
                        if let Err(e) = dag_driver_clone.process(certified_node).await {
                            warn!(error = ?e, "error processing certified node fetch notification");
                        }
                    },
                    Err(e) => {
                        debug!("sender dropped channel: {}", e);
                    },
                };
            }
        });

        defer!({
            task1.abort();
            task2.abort();
            task3.abort();

            block_in_place(move || {
                Handle::current().block_on(async {
                    _ = task1.await;
                    _ = task2.await;
                    _ = task3.await;
                })
            });
        });

        let mut futures = FuturesUnordered::new();
        // A separate executor to ensure the message verification sender (above) and receiver (below) are
        // not blocking each other.
        let executor = BoundedExecutor::new(8, Handle::current());
        loop {
            select! {
                (msg, author, responder) = verified_msg_stream.select_next_some() => {
                    let verified_msg_processor = verified_msg_processor.clone();
                    let f = executor.spawn(async move {
                        match verified_msg_processor.process_verified_message(msg, author, responder).await {
                            Ok(sync_status) => {
                                if matches!(
                                    sync_status,
                                    SyncOutcome::NeedsSync(_) | SyncOutcome::EpochEnds
                                ) {
                                    return Some(sync_status);
                                }
                            },
                            Err(e) => {
                                warn!(error = ?e, "error processing rpc");
                            },
                        }
                        None
                    }).await;
                    futures.push(f);
                },
                Some(status) = futures.next() => {
                    if let Some(status) = status.expect("must finish") {
                        return status;
                    }
                },
            }
        }
    }
}

struct VerifiedMessageProcessor {
    node_receiver: Arc<NodeBroadcastHandler>,
    dag_driver: Arc<DagDriver>,
    fetch_receiver: FetchRequestHandler,
    state_sync_trigger: StateSyncTrigger,
    epoch_state: Arc<EpochState>,
}

impl VerifiedMessageProcessor {
    async fn process_verified_message(
        &self,
        dag_message_result: anyhow::Result<DAGMessage>,
        author: Author,
        responder: RpcResponder,
    ) -> anyhow::Result<SyncOutcome> {
        let response: Result<DAGMessage, DAGError> = {
            match dag_message_result {
                Ok(dag_message) => {
                    debug!(
                        author = author,
                        message = dag_message,
                        "process verified message"
                    );
                    match dag_message {
                        DAGMessage::NodeMsg(node) => self
                            .node_receiver
                            .process(node)
                            .await
                            .map(|r| r.into())
                            .map_err(|err| {
                                err.downcast::<NodeBroadcastHandleError>()
                                    .map_or(DAGError::Unknown, |err| {
                                        DAGError::NodeBroadcastHandleError(err)
                                    })
                            }),
                        DAGMessage::CertifiedNodeMsg(certified_node_msg) => {
                            match self.state_sync_trigger.check(certified_node_msg).await? {
                                SyncOutcome::Synced(Some(certified_node_msg)) => self
                                    .dag_driver
                                    .process(certified_node_msg.certified_node())
                                    .await
                                    .map(|r| r.into())
                                    .map_err(|err| {
                                        err.downcast::<DagDriverError>()
                                            .map_or(DAGError::Unknown, |err| {
                                                DAGError::DagDriverError(err)
                                            })
                                    }),
                                status @ (SyncOutcome::NeedsSync(_) | SyncOutcome::EpochEnds) => {
                                    return Ok(status)
                                },
                                _ => unreachable!(),
                            }
                        },
                        DAGMessage::FetchRequest(request) => self
                            .fetch_receiver
                            .process(request)
                            .await
                            .map(|r| r.into())
                            .map_err(|err| {
                                err.downcast::<FetchRequestHandleError>()
                                    .map_or(DAGError::Unknown, DAGError::FetchRequestHandleError)
                            }),
                        _ => unreachable!("verification must catch this error"),
                    }
                },
                Err(err) => {
                    error!(error = ?err, "error verifying message");
                    Err(DAGError::MessageVerificationError)
                },
            }
        };

        debug!(
            "responding to process_rpc {:?}",
            response.as_ref().map(|r| r.name())
        );

        let response: DAGRpcResult = response
            .map_err(|e| DAGRpcError::new(self.epoch_state.epoch, e))
            .into();
        responder.respond(response)?;

        Ok(SyncOutcome::Synced(None))
    }
}
