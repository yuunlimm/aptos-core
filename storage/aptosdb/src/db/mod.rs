// Copyright © Aptos Foundation
// Parts of the project are originally copyright © Meta Platforms, Inc.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    backup::{backup_handler::BackupHandler, restore_utils},
    common::MAX_NUM_EPOCH_ENDING_LEDGER_INFO,
    errors::AptosDbError,
    event_store::EventStore,
    ledger_db::{LedgerDb, LedgerDbSchemaBatches},
    ledger_store::LedgerStore,
    metrics::{
        API_LATENCY_SECONDS, COMMITTED_TXNS, LATEST_TXN_VERSION, LEDGER_VERSION, NEXT_BLOCK_EPOCH,
        OTHER_TIMERS_SECONDS,
    },
    pruner::{LedgerPrunerManager, PrunerManager, StateKvPrunerManager, StateMerklePrunerManager},
    rocksdb_property_reporter::RocksdbPropertyReporter,
    schema::{
        block_by_version::BlockByVersionSchema,
        block_info::BlockInfoSchema,
        db_metadata::{DbMetadataKey, DbMetadataSchema, DbMetadataValue},
    },
    state_kv_db::StateKvDb,
    state_merkle_db::StateMerkleDb,
    state_store::StateStore,
    transaction_store::TransactionStore,
    utils::new_sharded_kv_schema_batch,
};
use anyhow::{anyhow, bail, ensure, Result};
use aptos_config::config::{
    PrunerConfig, RocksdbConfig, RocksdbConfigs, StorageDirPaths, NO_OP_STORAGE_PRUNER_CONFIG,
};
use aptos_crypto::HashValue;
use aptos_db_indexer::{db_v2::IndexerAsyncV2, Indexer};
use aptos_experimental_runtimes::thread_manager::{optimal_min_len, THREAD_MANAGER};
use aptos_logger::prelude::*;
use aptos_metrics_core::TimerHelper;
use aptos_schemadb::{ReadOptions, SchemaBatch};
use aptos_scratchpad::SparseMerkleTree;
use aptos_storage_interface::{
    block_info::{BlockInfo, BlockInfoV0},
    cached_state_view::ShardedStateCache,
    state_delta::StateDelta,
    state_view::DbStateView,
    DbReader, DbWriter, ExecutedTrees, Order, StateSnapshotReceiver, MAX_REQUEST_LIMIT,
};
use aptos_types::{
    account_address::AccountAddress,
    account_config::{new_block_event_key, NewBlockEvent},
    contract_event::{ContractEvent, EventWithVersion},
    epoch_change::EpochChangeProof,
    epoch_state::EpochState,
    event::EventKey,
    ledger_info::LedgerInfoWithSignatures,
    on_chain_config::{CurrentTimeMicroseconds, OnChainConfig},
    proof::{
        accumulator::InMemoryAccumulator, AccumulatorConsistencyProof, SparseMerkleProofExt,
        TransactionAccumulatorRangeProof, TransactionAccumulatorSummary,
        TransactionInfoListWithProof,
    },
    state_proof::StateProof,
    state_store::{
        state_key::StateKey,
        state_key_prefix::StateKeyPrefix,
        state_storage_usage::StateStorageUsage,
        state_value::{StateValue, StateValueChunkWithProof},
        table::{TableHandle, TableInfo},
        ShardedStateUpdates,
    },
    transaction::{
        AccountTransactionsWithProof, Transaction, TransactionInfo, TransactionListWithProof,
        TransactionOutput, TransactionOutputListWithProof, TransactionToCommit,
        TransactionWithProof, Version,
    },
    write_set::WriteSet,
};
use aptos_vm::data_cache::AsMoveResolver;
use dashmap::DashMap;
use move_resource_viewer::MoveValueAnnotator;
use rayon::prelude::*;
use std::{
    fmt::{Debug, Formatter},
    iter::Iterator,
    path::{Path, PathBuf},
    sync::Arc,
    time::Instant,
};

#[cfg(test)]
mod aptosdb_test;
#[cfg(any(test, feature = "fuzzing"))]
pub mod test_helper;

/// This holds a handle to the underlying DB responsible for physical storage and provides APIs for
/// access to the core Aptos data structures.
pub struct AptosDB {
    pub(crate) ledger_db: Arc<LedgerDb>,
    pub(crate) state_kv_db: Arc<StateKvDb>,
    pub(crate) event_store: Arc<EventStore>,
    pub(crate) ledger_store: Arc<LedgerStore>,
    pub(crate) state_store: Arc<StateStore>,
    pub(crate) transaction_store: Arc<TransactionStore>,
    ledger_pruner: LedgerPrunerManager,
    _rocksdb_property_reporter: RocksdbPropertyReporter,
    ledger_commit_lock: std::sync::Mutex<()>,
    indexer: Option<Indexer>,
    skip_index_and_usage: bool,
    indexer_async_v2: Option<IndexerAsyncV2>,
}

// DbReader implementations and private functions used by them.
include!("include/aptosdb_reader.rs");
// DbWriter implementations and private functions used by them.
include!("include/aptosdb_writer.rs");
// Other private methods.
include!("include/aptosdb_internal.rs");
// Testonly methods.
#[cfg(any(test, feature = "fuzzing"))]
include!("include/aptosdb_testonly.rs");

impl AptosDB {
    pub fn open(
        db_paths: StorageDirPaths,
        readonly: bool,
        pruner_config: PrunerConfig,
        rocksdb_configs: RocksdbConfigs,
        enable_indexer: bool,
        buffered_state_target_items: usize,
        max_num_nodes_per_lru_cache_shard: usize,
        enable_indexer_async_v2: bool,
    ) -> Result<Self> {
        Self::open_internal(
            &db_paths,
            readonly,
            pruner_config,
            rocksdb_configs,
            enable_indexer,
            buffered_state_target_items,
            max_num_nodes_per_lru_cache_shard,
            false,
            enable_indexer_async_v2,
        )
    }

    pub fn open_kv_only(
        db_paths: StorageDirPaths,
        readonly: bool,
        pruner_config: PrunerConfig,
        rocksdb_configs: RocksdbConfigs,
        enable_indexer: bool,
        buffered_state_target_items: usize,
        max_num_nodes_per_lru_cache_shard: usize,
        enable_indexer_async_v2: bool,
    ) -> Result<Self> {
        Self::open_internal(
            &db_paths,
            readonly,
            pruner_config,
            rocksdb_configs,
            enable_indexer,
            buffered_state_target_items,
            max_num_nodes_per_lru_cache_shard,
            true,
            enable_indexer_async_v2,
        )
    }

    pub fn open_dbs(
        db_paths: &StorageDirPaths,
        rocksdb_configs: RocksdbConfigs,
        readonly: bool,
        max_num_nodes_per_lru_cache_shard: usize,
    ) -> Result<(LedgerDb, StateMerkleDb, StateKvDb)> {
        let ledger_db = LedgerDb::new(db_paths.ledger_db_root_path(), rocksdb_configs, readonly)?;
        let state_kv_db = StateKvDb::new(
            db_paths,
            rocksdb_configs,
            readonly,
            ledger_db.metadata_db_arc(),
        )?;
        let state_merkle_db = StateMerkleDb::new(
            db_paths,
            rocksdb_configs,
            readonly,
            max_num_nodes_per_lru_cache_shard,
        )?;

        Ok((ledger_db, state_merkle_db, state_kv_db))
    }

    /// Gets an instance of `BackupHandler` for data backup purpose.
    pub fn get_backup_handler(&self) -> BackupHandler {
        BackupHandler::new(
            Arc::clone(&self.ledger_store),
            Arc::clone(&self.transaction_store),
            Arc::clone(&self.state_store),
            Arc::clone(&self.ledger_db),
        )
    }

    /// Creates new physical DB checkpoint in directory specified by `path`.
    pub fn create_checkpoint(
        db_path: impl AsRef<Path>,
        cp_path: impl AsRef<Path>,
        sharding: bool,
    ) -> Result<()> {
        let start = Instant::now();

        info!(sharding = sharding, "Creating checkpoint for AptosDB.");

        LedgerDb::create_checkpoint(db_path.as_ref(), cp_path.as_ref(), sharding)?;
        if sharding {
            StateKvDb::create_checkpoint(db_path.as_ref(), cp_path.as_ref())?;
        }
        StateMerkleDb::create_checkpoint(db_path.as_ref(), cp_path.as_ref(), sharding)?;

        info!(
            db_path = db_path.as_ref(),
            cp_path = cp_path.as_ref(),
            time_ms = %start.elapsed().as_millis(),
            "Made AptosDB checkpoint."
        );
        Ok(())
    }

    pub fn commit_genesis_ledger_info(&self, genesis_li: &LedgerInfoWithSignatures) -> Result<()> {
        let ledger_batch = SchemaBatch::new();
        let current_epoch = self
            .ledger_store
            .get_latest_ledger_info_option()
            .map_or(0, |li| li.ledger_info().next_block_epoch());
        ensure!(genesis_li.ledger_info().epoch() == current_epoch && current_epoch == 0);
        self.ledger_store
            .put_ledger_info(genesis_li, &ledger_batch)?;

        self.ledger_db.metadata_db().write_schemas(ledger_batch)
    }
}
