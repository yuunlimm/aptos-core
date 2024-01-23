// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

impl DbWriter for AptosDB {
    /// `first_version` is the version of the first transaction in `txns_to_commit`.
    /// When `ledger_info_with_sigs` is provided, verify that the transaction accumulator root hash
    /// it carries is generated after the `txns_to_commit` are applied.
    /// Note that even if `txns_to_commit` is empty, `first_version` is checked to be
    /// `ledger_info_with_sigs.ledger_info.version + 1` if `ledger_info_with_sigs` is not `None`.
    fn save_transactions(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        base_state_version: Option<Version>,
        ledger_info_with_sigs: Option<&LedgerInfoWithSignatures>,
        sync_commit: bool,
        latest_in_memory_state: StateDelta,
        state_updates_until_last_checkpoint: Option<ShardedStateUpdates>,
        sharded_state_cache: Option<&ShardedStateCache>,
    ) -> Result<()> {
        gauged_api("save_transactions", || {
            // Executing and committing from more than one threads not allowed -- consensus and
            // state sync must hand over to each other after all pending execution and committing
            // complete.
            let _lock = self
                .ledger_commit_lock
                .try_lock()
                .expect("Concurrent committing detected.");

            latest_in_memory_state.current.log_generation("db_save");

            // For reconfig suffix.
            if ledger_info_with_sigs.is_none() && txns_to_commit.is_empty() {
                return Ok(());
            }

            self.save_transactions_validation(
                txns_to_commit,
                first_version,
                base_state_version,
                ledger_info_with_sigs,
                &latest_in_memory_state,
            )?;

            let new_root_hash = self.calculate_and_commit_ledger_and_state_kv(
                txns_to_commit,
                first_version,
                latest_in_memory_state.current.usage(),
                sharded_state_cache,
                self.skip_index_and_usage,
            )?;

            let _timer = OTHER_TIMERS_SECONDS.timer_with(&["save_transactions__others"]);
            {
                let mut buffered_state = self.state_store.buffered_state().lock();
                let last_version = first_version + txns_to_commit.len() as u64 - 1;

                self.commit_ledger_info(last_version, new_root_hash, ledger_info_with_sigs)?;

                if !txns_to_commit.is_empty() {
                    let _timer = OTHER_TIMERS_SECONDS.timer_with(&["buffered_state___update"]);
                    buffered_state.update(
                        state_updates_until_last_checkpoint,
                        latest_in_memory_state,
                        sync_commit || txns_to_commit.last().unwrap().is_reconfig(),
                    )?;
                }
            }

            self.post_commit(txns_to_commit, first_version, ledger_info_with_sigs)
        })
    }

    fn get_state_snapshot_receiver(
        &self,
        version: Version,
        expected_root_hash: HashValue,
    ) -> Result<Box<dyn StateSnapshotReceiver<StateKey, StateValue>>> {
        gauged_api("get_state_snapshot_receiver", || {
            self.state_store
                .get_snapshot_receiver(version, expected_root_hash)
        })
    }

    // TODO(bowu): populate the flag indicating the fast_sync is done.
    fn finalize_state_snapshot(
        &self,
        version: Version,
        output_with_proof: TransactionOutputListWithProof,
        ledger_infos: &[LedgerInfoWithSignatures],
    ) -> Result<()> {
        gauged_api("finalize_state_snapshot", || {
            // Ensure the output with proof only contains a single transaction output and info
            let num_transaction_outputs = output_with_proof.transactions_and_outputs.len();
            let num_transaction_infos = output_with_proof.proof.transaction_infos.len();
            ensure!(
                num_transaction_outputs == 1,
                "Number of transaction outputs should == 1, but got: {}",
                num_transaction_outputs
            );
            ensure!(
                num_transaction_infos == 1,
                "Number of transaction infos should == 1, but got: {}",
                num_transaction_infos
            );

            // TODO(joshlind): include confirm_or_save_frozen_subtrees in the change set
            // bundle below.

            // Update the merkle accumulator using the given proof
            let frozen_subtrees = output_with_proof
                .proof
                .ledger_info_to_transaction_infos_proof
                .left_siblings();
            restore_utils::confirm_or_save_frozen_subtrees(
                self.ledger_db.transaction_accumulator_db(),
                version,
                frozen_subtrees,
                None,
            )?;

            // Create a single change set for all further write operations
            let mut ledger_db_batch = LedgerDbSchemaBatches::new();
            let mut sharded_kv_batch = new_sharded_kv_schema_batch();
            let state_kv_metadata_batch = SchemaBatch::new();
            // Save the target transactions, outputs, infos and events
            let (transactions, outputs): (Vec<Transaction>, Vec<TransactionOutput>) =
                output_with_proof
                    .transactions_and_outputs
                    .into_iter()
                    .unzip();
            let events = outputs
                .clone()
                .into_iter()
                .map(|output| output.events().to_vec())
                .collect::<Vec<_>>();
            let wsets: Vec<WriteSet> = outputs
                .into_iter()
                .map(|output| output.write_set().clone())
                .collect();
            let transaction_infos = output_with_proof.proof.transaction_infos;
            // We should not save the key value since the value is already recovered for this version
            restore_utils::save_transactions(
                self.ledger_store.clone(),
                self.transaction_store.clone(),
                self.state_store.clone(),
                self.ledger_db.clone(),
                version,
                &transactions,
                &transaction_infos,
                &events,
                wsets,
                Option::Some((
                    &mut ledger_db_batch,
                    &mut sharded_kv_batch,
                    &state_kv_metadata_batch,
                )),
                false,
            )?;

            // Save the epoch ending ledger infos
            restore_utils::save_ledger_infos(
                self.ledger_db.metadata_db(),
                self.ledger_store.clone(),
                ledger_infos,
                Some(&mut ledger_db_batch.ledger_metadata_db_batches),
            )?;

            ledger_db_batch
                .ledger_metadata_db_batches
                .put::<DbMetadataSchema>(
                    &DbMetadataKey::LedgerCommitProgress,
                    &DbMetadataValue::Version(version),
                )?;
            ledger_db_batch
                .ledger_metadata_db_batches
                .put::<DbMetadataSchema>(
                    &DbMetadataKey::OverallCommitProgress,
                    &DbMetadataValue::Version(version),
                )?;

            // Apply the change set writes to the database (atomically) and update in-memory state
            //
            // state kv and SMT should use shared way of committing.
            self.ledger_db.write_schemas(ledger_db_batch)?;

            self.ledger_pruner.save_min_readable_version(version)?;
            self.state_store
                .state_merkle_pruner
                .save_min_readable_version(version)?;
            self.state_store
                .epoch_snapshot_pruner
                .save_min_readable_version(version)?;
            self.state_store
                .state_kv_pruner
                .save_min_readable_version(version)?;

            restore_utils::update_latest_ledger_info(self.ledger_store.clone(), ledger_infos)?;
            self.state_store.reset();

            Ok(())
        })
    }

    /// Open up dbwriter for table info indexing on indexer async v2 rocksdb
    fn index_table_info(
        &self,
        db_reader: Arc<dyn DbReader>,
        first_version: Version,
        write_sets: &[&WriteSet],
        end_early_if_pending_on_empty: bool,
    ) -> Result<()> {
        gauged_api("index_table_info", || {
            self.indexer_async_v2
                .as_ref()
                .map(|indexer| {
                    indexer.index_table_info(
                        db_reader,
                        first_version,
                        write_sets,
                        end_early_if_pending_on_empty,
                    )
                })
                .unwrap_or(Ok(()))
        })
    }

    fn cleanup_pending_on_items(&self) -> Result<()> {
        gauged_api("cleanup_pending_on_items", || {
            self.indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.cleanup_pending_on_items())
                .unwrap_or(Ok(()))
        })
    }

    fn update_next_version(&self, end_version: u64) -> Result<()> {
        gauged_api("update_next_version", || {
            self.indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.update_next_version(end_version))
                .unwrap_or(Ok(()))
        })
    }

    /// Update last restored timestamp when indexer async v2 db successfully restores
    /// db from gcs, this timestamp is used to determine if restore is too frequent and
    /// instead use next version to start syncing instead
    fn update_last_restored_timestamp(&self, restore_timestamp: u64) -> Result<()> {
        gauged_api("update_last_restored_timestamp", || {
            self.indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.update_last_restored_timestamp(restore_timestamp))
                .unwrap_or(Ok(()))
        })
    }

    fn create_checkpoint(&self, path: &PathBuf) -> Result<()> {
        gauged_api("create_checkpoint", || {
            self.indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.create_checkpoint(path))
                .unwrap_or(Ok(()))
        })
    }
}

impl AptosDB {
    fn save_transactions_validation(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        base_state_version: Option<Version>,
        ledger_info_with_sigs: Option<&LedgerInfoWithSignatures>,
        latest_in_memory_state: &StateDelta,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["save_transactions_validation"])
            .start_timer();
        let buffered_state = self.state_store.buffered_state().lock();
        ensure!(
            base_state_version == buffered_state.current_state().base_version,
            "base_state_version {:?} does not equal to the base_version {:?} in buffered state with current version {:?}",
            base_state_version,
            buffered_state.current_state().base_version,
            buffered_state.current_state().current_version,
        );

        // Ensure the incoming committing requests are always consecutive and the version in
        // buffered state is consistent with that in db.
        let next_version_in_buffered_state = buffered_state
            .current_state()
            .current_version
            .map(|version| version + 1)
            .unwrap_or(0);
        let num_transactions_in_db = self.get_latest_version().map_or(0, |v| v + 1);
        ensure!(num_transactions_in_db == first_version && num_transactions_in_db == next_version_in_buffered_state,
            "The first version {} passed in, the next version in buffered state {} and the next version in db {} are inconsistent.",
            first_version,
            next_version_in_buffered_state,
            num_transactions_in_db,
        );

        let num_txns = txns_to_commit.len() as u64;
        // ledger_info_with_sigs could be None if we are doing state synchronization. In this case
        // txns_to_commit should not be empty. Otherwise it is okay to commit empty blocks.
        ensure!(
            ledger_info_with_sigs.is_some() || num_txns > 0,
            "txns_to_commit is empty while ledger_info_with_sigs is None.",
        );

        let last_version = first_version + num_txns - 1;

        if let Some(x) = ledger_info_with_sigs {
            let claimed_last_version = x.ledger_info().version();
            ensure!(
                claimed_last_version  == last_version,
                "Transaction batch not applicable: first_version {}, num_txns {}, last_version_in_ledger_info {}",
                first_version,
                num_txns,
                claimed_last_version,
            );
        }

        ensure!(
            Some(last_version) == latest_in_memory_state.current_version,
            "the last_version {:?} to commit doesn't match the current_version {:?} in latest_in_memory_state",
            last_version,
            latest_in_memory_state.current_version.expect("Must exist"),
        );

        Ok(())
    }

    fn calculate_and_commit_ledger_and_state_kv(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        expected_state_db_usage: StateStorageUsage,
        sharded_state_cache: Option<&ShardedStateCache>,
        skip_index_and_usage: bool,
    ) -> Result<HashValue> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["save_transactions__work"])
            .start_timer();
        let mut new_root_hash = HashValue::zero();
        THREAD_MANAGER.get_non_exe_cpu_pool().scope(|s| {
            // TODO(grao): Write progress for each of the following databases, and handle the
            // inconsistency at the startup time.
            //
            // TODO(grao): Consider propagating the error instead of panic, if necessary.
            s.spawn(|_| {
                self.commit_events(txns_to_commit, first_version, skip_index_and_usage)
                    .unwrap()
            });
            s.spawn(|_| {
                self.commit_write_sets(txns_to_commit, first_version)
                    .unwrap()
            });
            s.spawn(|_| {
                self.ledger_db
                    .transaction_db()
                    .commit_transactions(txns_to_commit, first_version, skip_index_and_usage)
                    .unwrap()
            });
            s.spawn(|_| {
                self.commit_state_kv_and_ledger_metadata(
                    txns_to_commit,
                    first_version,
                    expected_state_db_usage,
                    sharded_state_cache,
                    skip_index_and_usage,
                )
                .unwrap()
            });
            s.spawn(|_| {
                self.commit_transaction_infos(txns_to_commit, first_version)
                    .unwrap()
            });
            s.spawn(|_| {
                new_root_hash = self
                    .commit_transaction_accumulator(txns_to_commit, first_version)
                    .unwrap()
            });
        });

        Ok(new_root_hash)
    }

    fn commit_state_kv_and_ledger_metadata(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        expected_state_db_usage: StateStorageUsage,
        sharded_state_cache: Option<&ShardedStateCache>,
        skip_index_and_usage: bool,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_state_kv_and_ledger_metadata"])
            .start_timer();
        let state_updates_vec = txns_to_commit
            .iter()
            .map(|txn_to_commit| txn_to_commit.state_updates())
            .collect::<Vec<_>>();

        let ledger_metadata_batch = SchemaBatch::new();
        let sharded_state_kv_batches = new_sharded_kv_schema_batch();
        let state_kv_metadata_batch = SchemaBatch::new();

        // TODO(grao): Make state_store take sharded state updates.
        self.state_store.put_value_sets(
            state_updates_vec,
            first_version,
            expected_state_db_usage,
            sharded_state_cache,
            &ledger_metadata_batch,
            &sharded_state_kv_batches,
            &state_kv_metadata_batch,
            // Always put in state value index for now.
            // TODO(grao): remove after APIs migrated off the DB to the indexer.
            self.state_store.state_kv_db.enabled_sharding(),
            skip_index_and_usage,
            txns_to_commit
                .iter()
                .rposition(|txn| txn.is_state_checkpoint()),
        )?;

        // Write block index if event index is skipped.
        if skip_index_and_usage {
            for (i, txn) in txns_to_commit.iter().enumerate() {
                for event in txn.events() {
                    if let Some(event_key) = event.event_key() {
                        if *event_key == new_block_event_key() {
                            let version = first_version + i as Version;
                            let new_block_event =
                                NewBlockEvent::try_from_bytes(event.event_data())?;
                            let block_height = new_block_event.height();
                            let id = new_block_event.hash()?;
                            let epoch = new_block_event.epoch();
                            let round = new_block_event.round();
                            let proposer = new_block_event.proposer();
                            let block_timestamp_usecs = new_block_event.proposed_time();
                            let block_info = BlockInfo::V0(BlockInfoV0::new(
                                id,
                                epoch,
                                round,
                                proposer,
                                block_timestamp_usecs,
                                version,
                            ));
                            ledger_metadata_batch
                                .put::<BlockInfoSchema>(&block_height, &block_info)?;
                            ledger_metadata_batch
                                .put::<BlockByVersionSchema>(&version, &block_height)?;
                        }
                    }
                }
            }
        }

        let last_version = first_version + txns_to_commit.len() as u64 - 1;
        ledger_metadata_batch
            .put::<DbMetadataSchema>(
                &DbMetadataKey::LedgerCommitProgress,
                &DbMetadataValue::Version(last_version),
            )
            .unwrap();

        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_state_kv_and_ledger_metadata___commit"])
            .start_timer();
        rayon::scope(|s| {
            s.spawn(|_| {
                self.ledger_db
                    .metadata_db()
                    .write_schemas(ledger_metadata_batch)
                    .unwrap();
            });
            s.spawn(|_| {
                self.state_kv_db
                    .commit(
                        last_version,
                        state_kv_metadata_batch,
                        sharded_state_kv_batches,
                    )
                    .unwrap();
            });
        });

        Ok(())
    }

    fn commit_events(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        skip_index: bool,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_events"])
            .start_timer();
        let batch = SchemaBatch::new();
        let num_txns = txns_to_commit.len();
        txns_to_commit
            .par_iter()
            .with_min_len(optimal_min_len(num_txns, 128))
            .enumerate()
            .try_for_each(|(i, txn_to_commit)| -> Result<()> {
                self.ledger_db.event_db().put_events(
                    first_version + i as u64,
                    txn_to_commit.events(),
                    skip_index,
                    &batch,
                )?;

                Ok(())
            })?;
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_events___commit"])
            .start_timer();
        self.ledger_db.event_db().write_schemas(batch)
    }

    fn commit_transaction_accumulator(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: u64,
    ) -> Result<HashValue> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_transaction_accumulator"])
            .start_timer();

        let batch = SchemaBatch::new();
        let root_hash =
            self.ledger_store
                .put_transaction_accumulator(first_version, txns_to_commit, &batch)?;

        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_transaction_accumulator___commit"])
            .start_timer();
        self.ledger_db
            .transaction_accumulator_db()
            .write_schemas(batch)?;

        Ok(root_hash)
    }

    fn commit_transaction_infos(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: u64,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_transaction_infos"])
            .start_timer();
        let batch = SchemaBatch::new();
        let num_txns = txns_to_commit.len();
        txns_to_commit
            .par_iter()
            .with_min_len(optimal_min_len(num_txns, 128))
            .enumerate()
            .try_for_each(|(i, txn_to_commit)| -> Result<()> {
                let version = first_version + i as u64;
                self.ledger_store.put_transaction_info(
                    version,
                    txn_to_commit.transaction_info(),
                    &batch,
                )?;

                Ok(())
            })?;

        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_transaction_infos___commit"])
            .start_timer();
        self.ledger_db.transaction_info_db().write_schemas(batch)
    }

    fn commit_write_sets(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_write_sets"])
            .start_timer();
        let batch = SchemaBatch::new();
        let num_txns = txns_to_commit.len();
        txns_to_commit
            .par_iter()
            .with_min_len(optimal_min_len(num_txns, 128))
            .enumerate()
            .try_for_each(|(i, txn_to_commit)| -> Result<()> {
                self.transaction_store.put_write_set(
                    first_version + i as u64,
                    txn_to_commit.write_set(),
                    &batch,
                )?;

                Ok(())
            })?;
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_write_sets___commit"])
            .start_timer();
        self.ledger_db.write_set_db().write_schemas(batch)
    }

    fn commit_ledger_info(
        &self,
        last_version: Version,
        new_root_hash: HashValue,
        ledger_info_with_sigs: Option<&LedgerInfoWithSignatures>,
    ) -> Result<()> {
        let _timer = OTHER_TIMERS_SECONDS
            .with_label_values(&["commit_ledger_info"])
            .start_timer();

        let ledger_batch = SchemaBatch::new();

        // If expected ledger info is provided, verify result root hash and save the ledger info.
        if let Some(x) = ledger_info_with_sigs {
            let expected_root_hash = x.ledger_info().transaction_accumulator_hash();
            ensure!(
                new_root_hash == expected_root_hash,
                "Root hash calculated doesn't match expected. {:?} vs {:?}",
                new_root_hash,
                expected_root_hash,
            );
            let current_epoch = self
                .ledger_store
                .get_latest_ledger_info_option()
                .map_or(0, |li| li.ledger_info().next_block_epoch());
            ensure!(
                x.ledger_info().epoch() == current_epoch,
                "Gap in epoch history. Trying to put in LedgerInfo in epoch: {}, current epoch: {}",
                x.ledger_info().epoch(),
                current_epoch,
            );

            self.ledger_store.put_ledger_info(x, &ledger_batch)?;
        }

        ledger_batch.put::<DbMetadataSchema>(
            &DbMetadataKey::OverallCommitProgress,
            &DbMetadataValue::Version(last_version),
        )?;
        self.ledger_db.metadata_db().write_schemas(ledger_batch)
    }

    fn post_commit(
        &self,
        txns_to_commit: &[TransactionToCommit],
        first_version: Version,
        ledger_info_with_sigs: Option<&LedgerInfoWithSignatures>,
    ) -> Result<()> {
        // If commit succeeds and there are at least one transaction written to the storage, we
        // will inform the pruner thread to work.
        let num_txns = txns_to_commit.len() as u64;
        if num_txns > 0 {
            let last_version = first_version + num_txns - 1;
            COMMITTED_TXNS.inc_by(num_txns);
            LATEST_TXN_VERSION.set(last_version as i64);
            // Activate the ledger pruner and state kv pruner.
            // Note the state merkle pruner is activated when state snapshots are persisted
            // in their async thread.
            self.ledger_pruner
                .maybe_set_pruner_target_db_version(last_version);
            self.state_store
                .state_kv_pruner
                .maybe_set_pruner_target_db_version(last_version);
        }

        // Note: this must happen after txns have been saved to db because types can be newly
        // created in this same chunk of transactions.
        if let Some(indexer) = &self.indexer {
            let _timer = OTHER_TIMERS_SECONDS
                .with_label_values(&["indexer_index"])
                .start_timer();
            let write_sets: Vec<_> = txns_to_commit.iter().map(|txn| txn.write_set()).collect();
            indexer.index(self.state_store.clone(), first_version, &write_sets)?;
        }

        // Once everything is successfully persisted, update the latest in-memory ledger info.
        if let Some(x) = ledger_info_with_sigs {
            self.ledger_store.set_latest_ledger_info(x.clone());

            LEDGER_VERSION.set(x.ledger_info().version() as i64);
            NEXT_BLOCK_EPOCH.set(x.ledger_info().next_block_epoch() as i64);
        }

        Ok(())
    }
}
