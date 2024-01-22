// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use crate::{
    compile_aptos_packages, dump_and_compile_from_package_metadata, is_aptos_package,
    CompilationCache, DataManager, ExecutionMode, IndexWriter, PackageInfo, TxnIndex,
    APTOS_COMMONS,
};
use anyhow::{format_err, Result};
use aptos_framework::natives::code::PackageMetadata;
use aptos_language_e2e_tests::data_store::FakeDataStore;
use aptos_rest_client::Client;
use aptos_types::{
    on_chain_config::{FeatureFlag, Features, OnChainConfig},
    state_store::{state_key::StateKey, state_value::StateValue},
    transaction::{
        signature_verified_transaction::SignatureVerifiedTransaction, Transaction,
        TransactionOutput, Version,
    },
    write_set::TOTAL_SUPPLY_STATE_KEY,
};
use aptos_validator_interface::{
    AptosValidatorInterface, DebuggerStateView, FilterCondition, RestDebuggerInterface,
};
use aptos_vm::{AptosVM, VMExecutor};
use move_core_types::account_address::AccountAddress;
use std::{
    collections::HashMap,
    ops::Deref,
    path::PathBuf,
    sync::{Arc, Mutex},
};

pub struct DataCollection {
    debugger: Arc<dyn AptosValidatorInterface + Send>,
    current_dir: PathBuf,
    batch_size: u64,
    dump_write_set: bool,
    filter_condition: FilterCondition,
    execution_only: bool,
    execution_mode: ExecutionMode,
}

impl DataCollection {
    pub fn new(
        debugger: Arc<dyn AptosValidatorInterface + Send>,
        current_dir: PathBuf,
        batch_size: u64,
        skip_failed_txns: bool,
        skip_publish_txns: bool,
        dump_write_set: bool,
        skip_source_code: bool,
        execution_only: bool,
        execution_mode: ExecutionMode,
    ) -> Self {
        Self {
            debugger,
            current_dir,
            batch_size,
            dump_write_set,
            filter_condition: FilterCondition {
                skip_failed_txns,
                skip_publish_txns,
                check_source_code: !skip_source_code,
            },
            execution_only,
            execution_mode,
        }
    }

    pub fn new_with_rest_client(
        rest_client: Client,
        current_dir: PathBuf,
        batch_size: u64,
        skip_failed_txns: bool,
        skip_publish_txns: bool,
        dump_write_set: bool,
        skip_source_code: bool,
        execution_only: bool,
        execution_mode: ExecutionMode,
    ) -> Result<Self> {
        Ok(Self::new(
            Arc::new(RestDebuggerInterface::new(rest_client)),
            current_dir,
            batch_size,
            skip_failed_txns,
            skip_publish_txns,
            dump_write_set,
            skip_source_code,
            execution_only,
            execution_mode,
        ))
    }

    fn execute_transactions_at_version_with_state_view(
        txns: Vec<Transaction>,
        debugger_stateview: &DebuggerStateView,
    ) -> Result<Vec<TransactionOutput>> {
        let sig_verified_txns: Vec<SignatureVerifiedTransaction> =
            txns.into_iter().map(|x| x.into()).collect::<Vec<_>>();
        // check whether total supply can be retrieved
        // used for debugging the aggregator panic issue, will be removed later
        // FIXME(#10412): remove the assert
        let val = debugger_stateview.get_state_value(TOTAL_SUPPLY_STATE_KEY.deref());
        assert!(val.is_ok() && val.unwrap().is_some());
        AptosVM::execute_block_no_limit(&sig_verified_txns, debugger_stateview)
            .map_err(|err| format_err!("Unexpected VM Error: {:?}", err))
    }

    fn dump_and_check_src(
        version: Version,
        address: AccountAddress,
        package_name: String,
        map: HashMap<(AccountAddress, String), PackageMetadata>,
        compilation_cache: &mut CompilationCache,
        execution_mode: Option<ExecutionMode>,
        current_dir: PathBuf,
    ) -> Option<PackageInfo> {
        let upgrade_number = if is_aptos_package(&package_name) {
            None
        } else {
            let package = map.get(&(address, package_name.clone())).unwrap();
            Some(package.upgrade_number)
        };

        let package_info = PackageInfo {
            address,
            package_name: package_name.clone(),
            upgrade_number,
        };

        if !is_aptos_package(&package_name)
            && !compilation_cache
                .compiled_package_map
                .contains_key(&package_info)
        {
            if compilation_cache.failed_packages.contains(&package_info) {
                return None;
            }
            let res = dump_and_compile_from_package_metadata(
                package_info.clone(),
                current_dir,
                &map,
                compilation_cache,
                execution_mode,
            );
            if res.is_err() {
                println!("compile package failed at:{}", version);
                return None;
            }
        }
        Some(package_info)
    }

    fn dump_txn_index(
        data_manager: &mut DataManager,
        txn_index: TxnIndex,
        data_state: &HashMap<StateKey, StateValue>,
        epoch_result_res: Result<Vec<TransactionOutput>>,
        dump_write_set: bool,
    ) {
        // dump TxnIndex
        data_manager.dump_txn_index(txn_index.version, &txn_index);
        // dump state data
        data_manager.dump_state_data(txn_index.version, data_state);
        // dump write set
        if dump_write_set {
            let output = epoch_result_res.unwrap();
            assert_eq!(output.len(), 1);
            let write_set = output[0].write_set();
            data_manager.dump_write_set(txn_index.version, write_set);
        }
    }

    pub async fn dump_data(&self, begin: Version, limit: u64) -> Result<()> {
        println!("begin dumping data");
        let compilation_cache = Arc::new(Mutex::new(CompilationCache::default()));
        let data_manager = Arc::new(Mutex::new(DataManager::new_with_dir_creation(
            &self.current_dir,
        )));
        let index_writer = Arc::new(Mutex::new(IndexWriter::new(&self.current_dir)));

        if self.execution_only {
            let aptos_commons_path = self.current_dir.join(APTOS_COMMONS);
            if self.execution_mode.is_v1_or_compare() {
                compile_aptos_packages(
                    &aptos_commons_path,
                    &mut compilation_cache.lock().unwrap().compiled_package_cache_v1,
                    false,
                )?;
            }
            if self.execution_mode.is_v2_or_compare() {
                compile_aptos_packages(
                    &aptos_commons_path,
                    &mut compilation_cache.lock().unwrap().compiled_package_cache_v2,
                    true,
                )?;
            }
        }

        let mut cur_version = begin;

        while cur_version < begin + limit {
            let batch = if cur_version + self.batch_size <= begin + limit {
                self.batch_size
            } else {
                begin + limit - cur_version
            };
            let res_txns = self
                .debugger
                .get_and_filter_committed_transactions(cur_version, batch, self.filter_condition)
                .await;
            // if error happens when collecting txns, log the version range
            if res_txns.is_err() {
                index_writer
                    .lock()
                    .unwrap()
                    .write_err(&format!("{}:{}", cur_version, batch));
            }
            let txns = res_txns.unwrap_or_default();
            if !txns.is_empty() {
                let mut txn_execution_ths = vec![];
                for (version, txn, source_code_data) in txns {
                    println!("get txn at version:{}", version);

                    let compilation_cache = compilation_cache.clone();
                    let current_dir = self.current_dir.clone();
                    let dump_write_set = self.dump_write_set;
                    let execution_only = self.execution_only;
                    let data_manager = data_manager.clone();
                    let index = index_writer.clone();
                    let execution_mode = self.execution_mode;

                    let state_view =
                        DebuggerStateView::new_with_data_reads(self.debugger.clone(), version);

                    let txn_execution_thread = tokio::task::spawn_blocking(move || {
                        let executor = crate::Execution::new(current_dir.clone(), execution_mode);
                        let epoch_result_res =
                            Self::execute_transactions_at_version_with_state_view(
                                vec![txn.clone()],
                                &state_view,
                            );
                        if let Err(err) = epoch_result_res {
                            println!(
                                "execution error during transaction at version:{} :{}",
                                version, err
                            );
                            return;
                        }

                        let mut version_idx = TxnIndex {
                            version,
                            txn,
                            package_info: PackageInfo::non_compilable_info(),
                        };

                        // handle source code
                        if let Some((address, package_name, map)) = source_code_data {
                            let execution_mode_opt = if execution_only {
                                Some(execution_mode)
                            } else {
                                None
                            };
                            let package_info_opt = Self::dump_and_check_src(
                                version,
                                address,
                                package_name,
                                map,
                                &mut compilation_cache.lock().unwrap(),
                                execution_mode_opt,
                                current_dir.clone(),
                            );
                            if package_info_opt.is_none() {
                                return;
                            }
                            version_idx.package_info = package_info_opt.unwrap();
                        }
                        if !execution_only {
                            // dump through data_manager
                            Self::dump_txn_index(
                                &mut data_manager.lock().unwrap(),
                                version_idx,
                                &state_view.get_state_keys().lock().unwrap(),
                                epoch_result_res,
                                dump_write_set,
                            );
                            // Log version
                            index.lock().unwrap().add_version(version);
                        } else {
                            use aptos_vm::data_cache::AsMoveResolver;
                            let state_store = FakeDataStore::new_with_state_value(
                                state_view
                                    .get_state_keys()
                                    .lock()
                                    .unwrap()
                                    .deref()
                                    .to_owned(),
                            );
                            let state_view = state_store.as_move_resolver();
                            let mut features =
                                Features::fetch_config(&state_view).unwrap_or_default();
                            if executor.bytecode_version == 6 {
                                features.enable(FeatureFlag::VM_BINARY_FORMAT_V6);
                            }
                            let cache_v1 = compilation_cache
                                .lock()
                                .unwrap()
                                .compiled_package_cache_v1
                                .clone();
                            let cache_v2 = compilation_cache
                                .lock()
                                .unwrap()
                                .compiled_package_cache_v2
                                .clone();
                            executor.execute_and_compare(
                                version,
                                &state_store,
                                &features,
                                &version_idx,
                                &cache_v1,
                                &cache_v2,
                            );
                        }
                    });
                    txn_execution_ths.push(txn_execution_thread);
                }
                futures::future::join_all(txn_execution_ths).await;
                // Dump version
                index_writer.lock().unwrap().dump_version();
            }
            cur_version += batch;
        }
        index_writer.lock().unwrap().flush_writer();
        Ok(())
    }
}
