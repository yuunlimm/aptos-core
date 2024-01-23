// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

impl DbReader for AptosDB {
    fn get_epoch_ending_ledger_infos(
        &self,
        start_epoch: u64,
        end_epoch: u64,
    ) -> Result<EpochChangeProof> {
        gauged_api("get_epoch_ending_ledger_infos", || {
            let (ledger_info_with_sigs, more) =
                Self::get_epoch_ending_ledger_infos(self, start_epoch, end_epoch)?;
            Ok(EpochChangeProof::new(ledger_info_with_sigs, more))
        })
    }

    fn get_prefixed_state_value_iterator(
        &self,
        key_prefix: &StateKeyPrefix,
        cursor: Option<&StateKey>,
        version: Version,
    ) -> Result<Box<dyn Iterator<Item = Result<(StateKey, StateValue)>> + '_>> {
        gauged_api("get_prefixed_state_value_iterator", || {
            self.error_if_state_kv_pruned("StateValue", version)?;

            Ok(Box::new(
                self.state_store
                    .get_prefixed_state_value_iterator(key_prefix, cursor, version)?,
            )
                as Box<dyn Iterator<Item = Result<(StateKey, StateValue)>>>)
        })
    }

    fn get_latest_ledger_info_option(&self) -> Result<Option<LedgerInfoWithSignatures>> {
        gauged_api("get_latest_ledger_info_option", || {
            Ok(self.ledger_store.get_latest_ledger_info_option())
        })
    }

    fn get_latest_version(&self) -> Result<Version> {
        gauged_api("get_latest_version", || {
            self.ledger_store.get_latest_version()
        })
    }

    fn get_account_transaction(
        &self,
        address: AccountAddress,
        seq_num: u64,
        include_events: bool,
        ledger_version: Version,
    ) -> Result<Option<TransactionWithProof>> {
        gauged_api("get_account_transaction", || {
            self.transaction_store
                .get_account_transaction_version(address, seq_num, ledger_version)?
                .map(|txn_version| {
                    self.get_transaction_with_proof(txn_version, ledger_version, include_events)
                })
                .transpose()
        })
    }

    fn get_account_transactions(
        &self,
        address: AccountAddress,
        start_seq_num: u64,
        limit: u64,
        include_events: bool,
        ledger_version: Version,
    ) -> Result<AccountTransactionsWithProof> {
        gauged_api("get_account_transactions", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;

            let txns_with_proofs = self
                .transaction_store
                .get_account_transaction_version_iter(
                    address,
                    start_seq_num,
                    limit,
                    ledger_version,
                )?
                .map(|result| {
                    let (_seq_num, txn_version) = result?;
                    self.get_transaction_with_proof(txn_version, ledger_version, include_events)
                })
                .collect::<Result<Vec<_>>>()?;

            Ok(AccountTransactionsWithProof::new(txns_with_proofs))
        })
    }

    /// This API is best-effort in that it CANNOT provide absence proof.
    fn get_transaction_by_hash(
        &self,
        hash: HashValue,
        ledger_version: Version,
        fetch_events: bool,
    ) -> Result<Option<TransactionWithProof>> {
        gauged_api("get_transaction_by_hash", || {
            self.ledger_db
                .transaction_db()
                .get_transaction_version_by_hash(&hash, ledger_version)?
                .map(|v| self.get_transaction_with_proof(v, ledger_version, fetch_events))
                .transpose()
        })
    }

    /// Returns the transaction by version, delegates to `AptosDB::get_transaction_with_proof`.
    /// Returns an error if the provided version is not found.
    fn get_transaction_by_version(
        &self,
        version: Version,
        ledger_version: Version,
        fetch_events: bool,
    ) -> Result<TransactionWithProof> {
        gauged_api("get_transaction_by_version", || {
            self.get_transaction_with_proof(version, ledger_version, fetch_events)
        })
    }

    // ======================= State Synchronizer Internal APIs ===================================
    /// Returns batch of transactions for the purpose of synchronizing state to another node.
    ///
    /// If any version beyond ledger_version is requested, it is ignored.
    /// Returns an error if any version <= ledger_version is requested but not found.
    ///
    /// This is used by the State Synchronizer module internally.
    fn get_transactions(
        &self,
        start_version: Version,
        limit: u64,
        ledger_version: Version,
        fetch_events: bool,
    ) -> Result<TransactionListWithProof> {
        gauged_api("get_transactions", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;

            if start_version > ledger_version || limit == 0 {
                return Ok(TransactionListWithProof::new_empty());
            }
            self.error_if_ledger_pruned("Transaction", start_version)?;

            let limit = std::cmp::min(limit, ledger_version - start_version + 1);

            let txns = (start_version..start_version + limit)
                .map(|version| self.ledger_db.transaction_db().get_transaction(version))
                .collect::<Result<Vec<_>>>()?;
            let txn_infos = (start_version..start_version + limit)
                .map(|version| self.ledger_store.get_transaction_info(version))
                .collect::<Result<Vec<_>>>()?;
            let events = if fetch_events {
                Some(
                    (start_version..start_version + limit)
                        .map(|version| self.ledger_db.event_db().get_events_by_version(version))
                        .collect::<Result<Vec<_>>>()?,
                )
            } else {
                None
            };
            let proof = TransactionInfoListWithProof::new(
                self.ledger_store.get_transaction_range_proof(
                    Some(start_version),
                    limit,
                    ledger_version,
                )?,
                txn_infos,
            );

            Ok(TransactionListWithProof::new(
                txns,
                events,
                Some(start_version),
                proof,
            ))
        })
    }

    /// Get the first version that txn starts existent.
    fn get_first_txn_version(&self) -> Result<Option<Version>> {
        gauged_api("get_first_txn_version", || {
            Ok(Some(self.ledger_pruner.get_min_readable_version()))
        })
    }

    /// Get the first version that will likely not be pruned soon
    fn get_first_viable_txn_version(&self) -> Result<Version> {
        gauged_api("get_first_viable_txn_version", || {
            Ok(self.ledger_pruner.get_min_viable_version())
        })
    }

    /// Get the first version that write set starts existent.
    fn get_first_write_set_version(&self) -> Result<Option<Version>> {
        gauged_api("get_first_write_set_version", || {
            Ok(Some(self.ledger_pruner.get_min_readable_version()))
        })
    }

    /// Returns a batch of transactions for the purpose of synchronizing state to another node.
    ///
    /// If any version beyond ledger_version is requested, it is ignored.
    /// Returns an error if any version <= ledger_version is requested but not found.
    ///
    /// This is used by the State Synchronizer module internally.
    fn get_transaction_outputs(
        &self,
        start_version: Version,
        limit: u64,
        ledger_version: Version,
    ) -> Result<TransactionOutputListWithProof> {
        gauged_api("get_transactions_outputs", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;

            if start_version > ledger_version || limit == 0 {
                return Ok(TransactionOutputListWithProof::new_empty());
            }

            self.error_if_ledger_pruned("Transaction", start_version)?;

            let limit = std::cmp::min(limit, ledger_version - start_version + 1);

            let (txn_infos, txns_and_outputs) = (start_version..start_version + limit)
                .map(|version| {
                    let txn_info = self.ledger_store.get_transaction_info(version)?;
                    let events = self.ledger_db.event_db().get_events_by_version(version)?;
                    let write_set = self.transaction_store.get_write_set(version)?;
                    let txn = self.ledger_db.transaction_db().get_transaction(version)?;
                    let txn_output = TransactionOutput::new(
                        write_set,
                        events,
                        txn_info.gas_used(),
                        txn_info.status().clone().into(),
                    );
                    Ok((txn_info, (txn, txn_output)))
                })
                .collect::<Result<Vec<_>>>()?
                .into_iter()
                .unzip();
            let proof = TransactionInfoListWithProof::new(
                self.ledger_store.get_transaction_range_proof(
                    Some(start_version),
                    limit,
                    ledger_version,
                )?,
                txn_infos,
            );

            Ok(TransactionOutputListWithProof::new(
                txns_and_outputs,
                Some(start_version),
                proof,
            ))
        })
    }

    fn get_events(
        &self,
        event_key: &EventKey,
        start: u64,
        order: Order,
        limit: u64,
        ledger_version: Version,
    ) -> Result<Vec<EventWithVersion>> {
        gauged_api("get_events", || {
            self.get_events_by_event_key(event_key, start, order, limit, ledger_version)
        })
    }

    fn get_transaction_iterator(
        &self,
        start_version: Version,
        limit: u64,
    ) -> Result<Box<dyn Iterator<Item = Result<Transaction>> + '_>> {
        gauged_api("get_transaction_iterator", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;
            self.error_if_ledger_pruned("Transaction", start_version)?;

            let iter = self
                .ledger_db
                .transaction_db()
                .get_transaction_iter(start_version, limit as usize)?;
            Ok(Box::new(iter) as Box<dyn Iterator<Item = Result<Transaction>> + '_>)
        })
    }

    fn get_transaction_info_iterator(
        &self,
        start_version: Version,
        limit: u64,
    ) -> Result<Box<dyn Iterator<Item = Result<TransactionInfo>> + '_>> {
        gauged_api("get_transaction_info_iterator", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;
            self.error_if_ledger_pruned("Transaction", start_version)?;

            let iter = self
                .ledger_store
                .get_transaction_info_iter(start_version, limit as usize)?;
            Ok(Box::new(iter) as Box<dyn Iterator<Item = Result<TransactionInfo>> + '_>)
        })
    }

    fn get_events_iterator(
        &self,
        start_version: Version,
        limit: u64,
    ) -> Result<Box<dyn Iterator<Item = Result<Vec<ContractEvent>>> + '_>> {
        gauged_api("get_events_iterator", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;
            self.error_if_ledger_pruned("Transaction", start_version)?;

            let iter = self
                .ledger_db
                .event_db()
                .get_events_by_version_iter(start_version, limit as usize)?;
            Ok(Box::new(iter)
                as Box<
                    dyn Iterator<Item = Result<Vec<ContractEvent>>> + '_,
                >)
        })
    }

    fn get_write_set_iterator(
        &self,
        start_version: Version,
        limit: u64,
    ) -> Result<Box<dyn Iterator<Item = Result<WriteSet>> + '_>> {
        gauged_api("get_write_set_iterator", || {
            error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;
            self.error_if_ledger_pruned("Transaction", start_version)?;

            let iter = self
                .transaction_store
                .get_write_set_iter(start_version, limit as usize)?;
            Ok(Box::new(iter) as Box<dyn Iterator<Item = Result<WriteSet>> + '_>)
        })
    }

    fn get_transaction_accumulator_range_proof(
        &self,
        first_version: Version,
        limit: u64,
        ledger_version: Version,
    ) -> Result<TransactionAccumulatorRangeProof> {
        gauged_api("get_transaction_accumulator_range_proof", || {
            self.error_if_ledger_pruned("Transaction", first_version)?;

            self.ledger_store.get_transaction_range_proof(
                Some(first_version),
                limit,
                ledger_version,
            )
        })
    }

    /// Gets ledger info at specified version and ensures it's an epoch ending.
    fn get_epoch_ending_ledger_info(&self, version: u64) -> Result<LedgerInfoWithSignatures> {
        gauged_api("get_epoch_ending_ledger_info", || {
            self.ledger_store.get_epoch_ending_ledger_info(version)
        })
    }

    fn get_state_proof_with_ledger_info(
        &self,
        known_version: u64,
        ledger_info_with_sigs: LedgerInfoWithSignatures,
    ) -> Result<StateProof> {
        gauged_api("get_state_proof_with_ledger_info", || {
            let ledger_info = ledger_info_with_sigs.ledger_info();
            ensure!(
                known_version <= ledger_info.version(),
                "Client known_version {} larger than ledger version {}.",
                known_version,
                ledger_info.version(),
            );
            let known_epoch = self.ledger_store.get_epoch(known_version)?;
            let end_epoch = ledger_info.next_block_epoch();
            let epoch_change_proof = if known_epoch < end_epoch {
                let (ledger_infos_with_sigs, more) =
                    self.get_epoch_ending_ledger_infos(known_epoch, end_epoch)?;
                EpochChangeProof::new(ledger_infos_with_sigs, more)
            } else {
                EpochChangeProof::new(vec![], /* more = */ false)
            };

            Ok(StateProof::new(ledger_info_with_sigs, epoch_change_proof))
        })
    }

    fn get_state_proof(&self, known_version: u64) -> Result<StateProof> {
        gauged_api("get_state_proof", || {
            let ledger_info_with_sigs = self.ledger_store.get_latest_ledger_info()?;
            self.get_state_proof_with_ledger_info(known_version, ledger_info_with_sigs)
        })
    }

    fn get_state_value_by_version(
        &self,
        state_store_key: &StateKey,
        version: Version,
    ) -> Result<Option<StateValue>> {
        gauged_api("get_state_value_by_version", || {
            self.error_if_state_kv_pruned("StateValue", version)?;

            self.state_store
                .get_state_value_by_version(state_store_key, version)
        })
    }

    fn get_state_value_with_version_by_version(
        &self,
        state_key: &StateKey,
        version: Version,
    ) -> Result<Option<(Version, StateValue)>> {
        gauged_api("get_state_value_with_version_by_version", || {
            self.error_if_state_kv_pruned("StateValue", version)?;

            self.state_store
                .get_state_value_with_version_by_version(state_key, version)
        })
    }

    /// Returns the proof of the given state key and version.
    fn get_state_proof_by_version_ext(
        &self,
        state_key: &StateKey,
        version: Version,
    ) -> Result<SparseMerkleProofExt> {
        gauged_api("get_state_proof_by_version_ext", || {
            self.error_if_state_merkle_pruned("State merkle", version)?;

            self.state_store
                .get_state_proof_by_version_ext(state_key, version)
        })
    }

    fn get_state_value_with_proof_by_version_ext(
        &self,
        state_store_key: &StateKey,
        version: Version,
    ) -> Result<(Option<StateValue>, SparseMerkleProofExt)> {
        gauged_api("get_state_value_with_proof_by_version_ext", || {
            self.error_if_state_merkle_pruned("State merkle", version)?;

            self.state_store
                .get_state_value_with_proof_by_version_ext(state_store_key, version)
        })
    }

    fn get_latest_epoch_state(&self) -> Result<EpochState> {
        gauged_api("get_latest_epoch_state", || {
            let latest_ledger_info = self.ledger_store.get_latest_ledger_info()?;
            match latest_ledger_info.ledger_info().next_epoch_state() {
                Some(epoch_state) => Ok(epoch_state.clone()),
                None => self
                    .ledger_store
                    .get_epoch_state(latest_ledger_info.ledger_info().epoch()),
            }
        })
    }

    fn get_latest_executed_trees(&self) -> Result<ExecutedTrees> {
        gauged_api("get_latest_executed_trees", || {
            let buffered_state = self.state_store.buffered_state().lock();
            let num_txns = buffered_state
                .current_state()
                .current_version
                .map_or(0, |v| v + 1);

            let frozen_subtrees = self.ledger_store.get_frozen_subtree_hashes(num_txns)?;
            let transaction_accumulator =
                Arc::new(InMemoryAccumulator::new(frozen_subtrees, num_txns)?);
            let executed_trees = ExecutedTrees::new(
                buffered_state.current_state().clone(),
                transaction_accumulator,
            );
            Ok(executed_trees)
        })
    }

    fn get_buffered_state_base(&self) -> Result<SparseMerkleTree<StateValue>> {
        gauged_api("get_buffered_state_base", || {
            self.state_store.get_buffered_state_base()
        })
    }

    fn get_block_timestamp(&self, version: u64) -> Result<u64> {
        gauged_api("get_block_timestamp", || {
            self.error_if_ledger_pruned("NewBlockEvent", version)?;
            ensure!(version <= self.get_latest_version()?);

            match self.event_store.get_block_metadata(version) {
                Ok((_first_version, new_block_event)) => Ok(new_block_event.proposed_time()),
                Err(err) => {
                    // when event index is disabled, we won't be able to search the NewBlock event stream.
                    // TODO(grao): evaluate adding dedicated block_height_by_version index
                    warn!(
                        error = ?err,
                        "Failed to fetch block timestamp, falling back to on-chain config.",
                    );
                    let ts = self
                        .get_state_value_by_version(
                            &StateKey::access_path(CurrentTimeMicroseconds::access_path()?),
                            version,
                        )?
                        .ok_or_else(|| anyhow!("Timestamp not found at version {}", version))?;
                    Ok(bcs::from_bytes::<CurrentTimeMicroseconds>(ts.bytes())?.microseconds)
                },
            }
        })
    }

    fn get_next_block_event(&self, version: Version) -> Result<(Version, NewBlockEvent)> {
        gauged_api("get_next_block_event", || {
            self.error_if_ledger_pruned("NewBlockEvent", version)?;
            if let Some((block_version, _, _)) = self
                .event_store
                .lookup_event_at_or_after_version(&new_block_event_key(), version)?
            {
                self.event_store.get_block_metadata(block_version)
            } else {
                bail!(
                    "Failed to find a block event at or after version {}",
                    version
                )
            }
        })
    }

    // Returns latest `num_events` NewBlockEvents and their versions.
    // TODO(grao): Consider adding block_height as parameter.
    fn get_latest_block_events(&self, num_events: usize) -> Result<Vec<EventWithVersion>> {
        gauged_api("get_latest_block_events", || {
            if !self.skip_index_and_usage {
                return self.get_events(
                    &new_block_event_key(),
                    u64::max_value(),
                    Order::Descending,
                    num_events as u64,
                    self.get_latest_version().unwrap_or(0),
                );
            }

            let mut iter = self
                .ledger_db
                .metadata_db()
                .rev_iter::<BlockInfoSchema>(ReadOptions::default())?;
            iter.seek_to_last();

            let mut events = Vec::with_capacity(num_events);
            for item in iter.take(num_events) {
                let (block_height, block_info) = item?;
                let first_version = block_info.first_version();
                let event = self
                    .ledger_db
                    .event_db()
                    .get_events_by_version(first_version)?
                    .into_iter()
                    .find(|event| {
                        if let Some(key) = event.event_key() {
                            if *key == new_block_event_key() {
                                return true;
                            }
                        }
                        false
                    })
                    .ok_or_else(|| anyhow!("Event for block_height {block_height} at version {first_version} is not found."))?;
                events.push(EventWithVersion::new(first_version, event));
            }

            Ok(events)
        })
    }

    fn get_block_info_by_version(
        &self,
        version: Version,
    ) -> Result<(Version, Version, NewBlockEvent)> {
        gauged_api("get_block_info", || {
            self.error_if_ledger_pruned("NewBlockEvent", version)?;

            let latest_li = self.get_latest_ledger_info()?;
            let committed_version = latest_li.ledger_info().version();
            ensure!(
                version <= committed_version,
                "Requested version {} > committed version {}",
                version,
                committed_version
            );

            if !self.skip_index_and_usage {
                let (first_version, new_block_event) =
                    self.event_store.get_block_metadata(version)?;

                let last_version = self
                    .event_store
                    .lookup_event_after_version(&new_block_event_key(), version)?
                    .map_or(committed_version, |(v, _, _)| v - 1);

                return Ok((first_version, last_version, new_block_event));
            }

            let mut iter = self
                .ledger_db
                .metadata_db()
                .iter::<BlockByVersionSchema>(ReadOptions::default())?;

            iter.seek_for_prev(&version)?;
            let (_, block_height) = iter.next().transpose()?.ok_or(anyhow!(
                "Block is not found at version {version}, maybe pruned?"
            ))?;

            self.get_block_info_by_height(block_height)
        })
    }

    fn get_block_info_by_height(
        &self,
        block_height: u64,
    ) -> Result<(Version, Version, NewBlockEvent)> {
        gauged_api("get_block_info_by_height", || {
            let latest_li = self.get_latest_ledger_info()?;
            let committed_version = latest_li.ledger_info().version();

            if !self.skip_index_and_usage {
                let event_key = new_block_event_key();
                let (first_version, new_block_event) = self.event_store.get_event_by_key(
                    &event_key,
                    block_height,
                    committed_version,
                )?;
                let last_version = self
                    .event_store
                    .lookup_event_after_version(&event_key, first_version)?
                    .map_or(committed_version, |(v, _, _)| v - 1);
                return Ok((
                    first_version,
                    last_version,
                    bcs::from_bytes(new_block_event.event_data())?,
                ));
            };

            let first_version = self
                .get_block_info_internal(block_height)?
                .ok_or(anyhow!(
                    "Block is not found at height {block_height}, maybe pruned?"
                ))?
                .first_version();
            let last_version = self
                .get_block_info_internal(block_height + 1)?
                .map_or(committed_version, |block_info| {
                    block_info.first_version() - 1
                });

            // TODO(grao): Consider return BlockInfo instead of NewBlockEvent.
            let new_block_event = self
                .ledger_db
                .event_db()
                .get_events_by_version(first_version)?
                .into_iter()
                .find(|event| {
                    if let Some(key) = event.event_key() {
                        if *key == new_block_event_key() {
                            return true;
                        }
                    }
                    false
                })
            .ok_or_else(|| anyhow!("Event for block_height {block_height} at version {first_version} is not found."))?;

            Ok((
                first_version,
                last_version,
                bcs::from_bytes(new_block_event.event_data())?,
            ))
        })
    }

    fn get_last_version_before_timestamp(
        &self,
        timestamp: u64,
        ledger_version: Version,
    ) -> Result<Version> {
        gauged_api("get_last_version_before_timestamp", || {
            self.event_store
                .get_last_version_before_timestamp(timestamp, ledger_version)
        })
    }

    fn get_latest_state_checkpoint_version(&self) -> Result<Option<Version>> {
        gauged_api("get_latest_state_checkpoint_version", || {
            Ok(self
                .state_store
                .buffered_state()
                .lock()
                .current_checkpoint_version())
        })
    }

    fn get_state_snapshot_before(
        &self,
        next_version: Version,
    ) -> Result<Option<(Version, HashValue)>> {
        self.error_if_state_merkle_pruned("State merkle", next_version)?;
        gauged_api("get_state_snapshot_before", || {
            self.state_store.get_state_snapshot_before(next_version)
        })
    }

    fn get_accumulator_root_hash(&self, version: Version) -> Result<HashValue> {
        gauged_api("get_accumulator_root_hash", || {
            self.error_if_ledger_pruned("Transaction accumulator", version)?;
            self.ledger_store.get_root_hash(version)
        })
    }

    fn get_accumulator_consistency_proof(
        &self,
        client_known_version: Option<Version>,
        ledger_version: Version,
    ) -> Result<AccumulatorConsistencyProof> {
        gauged_api("get_accumulator_consistency_proof", || {
            self.error_if_ledger_pruned(
                "Transaction accumulator",
                client_known_version.unwrap_or(0),
            )?;
            self.ledger_store
                .get_consistency_proof(client_known_version, ledger_version)
        })
    }

    fn get_accumulator_summary(
        &self,
        ledger_version: Version,
    ) -> Result<TransactionAccumulatorSummary> {
        let num_txns = ledger_version + 1;
        let frozen_subtrees = self.ledger_store.get_frozen_subtree_hashes(num_txns)?;
        TransactionAccumulatorSummary::new(InMemoryAccumulator::new(frozen_subtrees, num_txns)?)
    }

    fn get_state_leaf_count(&self, version: Version) -> Result<usize> {
        gauged_api("get_state_leaf_count", || {
            self.error_if_state_merkle_pruned("State merkle", version)?;
            self.state_store.get_value_count(version)
        })
    }

    fn get_state_value_chunk_with_proof(
        &self,
        version: Version,
        first_index: usize,
        chunk_size: usize,
    ) -> Result<StateValueChunkWithProof> {
        gauged_api("get_state_value_chunk_with_proof", || {
            self.error_if_state_merkle_pruned("State merkle", version)?;
            self.state_store
                .get_value_chunk_with_proof(version, first_index, chunk_size)
        })
    }

    fn is_state_merkle_pruner_enabled(&self) -> Result<bool> {
        gauged_api("is_state_merkle_pruner_enabled", || {
            Ok(self
                .state_store
                .state_db
                .state_merkle_pruner
                .is_pruner_enabled())
        })
    }

    fn get_epoch_snapshot_prune_window(&self) -> Result<usize> {
        gauged_api("get_state_prune_window", || {
            Ok(self
                .state_store
                .state_db
                .epoch_snapshot_pruner
                .get_prune_window() as usize)
        })
    }

    fn is_ledger_pruner_enabled(&self) -> Result<bool> {
        gauged_api("is_ledger_pruner_enabled", || {
            Ok(self.ledger_pruner.is_pruner_enabled())
        })
    }

    fn get_ledger_prune_window(&self) -> Result<usize> {
        gauged_api("get_ledger_prune_window", || {
            Ok(self.ledger_pruner.get_prune_window() as usize)
        })
    }

    fn get_table_info(&self, handle: TableHandle) -> Result<TableInfo> {
        gauged_api("get_table_info", || {
            self.get_table_info_option(handle)?
                .ok_or_else(|| AptosDbError::NotFound(format!("TableInfo for {:?}", handle)).into())
        })
    }

    /// Returns whether the indexer DB has been enabled or not
    fn indexer_enabled(&self) -> bool {
        self.indexer.is_some()
    }

    /// Returns whether the indexer async v2 DB has been enabled or not
    fn indexer_async_v2_enabled(&self) -> bool {
        self.indexer_async_v2.is_some()
    }

    fn get_state_storage_usage(&self, version: Option<Version>) -> Result<StateStorageUsage> {
        gauged_api("get_state_storage_usage", || {
            if let Some(v) = version {
                self.error_if_ledger_pruned("state storage usage", v)?;
            }
            self.state_store.get_usage(version)
        })
    }

    /// Returns the next version for indexer async v2 to be processed
    /// It is mainly used by table info service to decide the start version
    fn get_indexer_async_v2_next_version(&self) -> Result<Version> {
        gauged_api("get_indexer_async_v2_next_version", || {
            Ok(self
                .indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.next_version())
                .unwrap_or(0))
        })
    }

    /// Returns the last db snapshot restored from gcs timestamp for indexer async v2
    /// It is mainly used by table info service to whether to start syncing from the next_version directly
    /// or to restore db snapshot from gcs
    fn get_indexer_async_v2_restore_timestamp(&self) -> Result<Version> {
        gauged_api("get_indexer_async_v2_restore_timestamp", || {
            Ok(self
                .indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.restore_timestamp())
                .unwrap_or(0))
        })
    }

    fn is_indexer_async_v2_pending_on_empty(&self) -> Result<bool> {
        gauged_api("is_indexer_async_v2_pending_on_empty", || {
            Ok(self
                .indexer_async_v2
                .as_ref()
                .map(|indexer| indexer.is_indexer_async_v2_pending_on_empty())
                .unwrap_or(false))
        })
    }
}

impl AptosDB {
    /// Returns ledger infos reflecting epoch bumps starting with the given epoch. If there are no
    /// more than `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results, this function returns all of them,
    /// otherwise the first `MAX_NUM_EPOCH_ENDING_LEDGER_INFO` results are returned and a flag
    /// (when true) will be used to indicate the fact that there is more.
    fn get_epoch_ending_ledger_infos(
        &self,
        start_epoch: u64,
        end_epoch: u64,
    ) -> Result<(Vec<LedgerInfoWithSignatures>, bool)> {
        self.get_epoch_ending_ledger_infos_impl(
            start_epoch,
            end_epoch,
            MAX_NUM_EPOCH_ENDING_LEDGER_INFO,
        )
    }

    fn get_epoch_ending_ledger_infos_impl(
        &self,
        start_epoch: u64,
        end_epoch: u64,
        limit: usize,
    ) -> Result<(Vec<LedgerInfoWithSignatures>, bool)> {
        ensure!(
            start_epoch <= end_epoch,
            "Bad epoch range [{}, {})",
            start_epoch,
            end_epoch,
        );
        // Note that the latest epoch can be the same with the current epoch (in most cases), or
        // current_epoch + 1 (when the latest ledger_info carries next validator set)

        let latest_epoch = self
            .ledger_store
            .get_latest_ledger_info()?
            .ledger_info()
            .next_block_epoch();
        ensure!(
            end_epoch <= latest_epoch,
            "Unable to provide epoch change ledger info for still open epoch. asked upper bound: {}, last sealed epoch: {}",
            end_epoch,
            latest_epoch - 1,  // okay to -1 because genesis LedgerInfo has .next_block_epoch() == 1
        );

        let (paging_epoch, more) = if end_epoch - start_epoch > limit as u64 {
            (start_epoch + limit as u64, true)
        } else {
            (end_epoch, false)
        };

        let lis = self
            .ledger_store
            .get_epoch_ending_ledger_info_iter(start_epoch, paging_epoch)?
            .collect::<Result<Vec<_>>>()?;

        ensure!(
            lis.len() == (paging_epoch - start_epoch) as usize,
            "DB corruption: missing epoch ending ledger info for epoch {}",
            lis.last()
                .map(|li| li.ledger_info().next_block_epoch() - 1)
                .unwrap_or(start_epoch),
        );
        Ok((lis, more))
    }

    /// Returns the transaction with proof for a given version, or error if the transaction is not
    /// found.
    fn get_transaction_with_proof(
        &self,
        version: Version,
        ledger_version: Version,
        fetch_events: bool,
    ) -> Result<TransactionWithProof> {
        self.error_if_ledger_pruned("Transaction", version)?;

        let proof = self
            .ledger_store
            .get_transaction_info_with_proof(version, ledger_version)?;
        let transaction = self.ledger_db.transaction_db().get_transaction(version)?;

        // If events were requested, also fetch those.
        let events = if fetch_events {
            Some(self.ledger_db.event_db().get_events_by_version(version)?)
        } else {
            None
        };

        Ok(TransactionWithProof {
            version,
            transaction,
            events,
            proof,
        })
    }

    fn get_events_by_event_key(
        &self,
        event_key: &EventKey,
        start_seq_num: u64,
        order: Order,
        limit: u64,
        ledger_version: Version,
    ) -> Result<Vec<EventWithVersion>> {
        error_if_too_many_requested(limit, MAX_REQUEST_LIMIT)?;
        let get_latest = order == Order::Descending && start_seq_num == u64::max_value();

        let cursor = if get_latest {
            // Caller wants the latest, figure out the latest seq_num.
            // In the case of no events on that path, use 0 and expect empty result below.
            self.event_store
                .get_latest_sequence_number(ledger_version, event_key)?
                .unwrap_or(0)
        } else {
            start_seq_num
        };

        // Convert requested range and order to a range in ascending order.
        let (first_seq, real_limit) = get_first_seq_num_and_limit(order, cursor, limit)?;

        // Query the index.
        let mut event_indices = self.event_store.lookup_events_by_key(
            event_key,
            first_seq,
            real_limit,
            ledger_version,
        )?;

        // When descending, it's possible that user is asking for something beyond the latest
        // sequence number, in which case we will consider it a bad request and return an empty
        // list.
        // For example, if the latest sequence number is 100, and the caller is asking for 110 to
        // 90, we will get 90 to 100 from the index lookup above. Seeing that the last item
        // is 100 instead of 110 tells us 110 is out of bound.
        if order == Order::Descending {
            if let Some((seq_num, _, _)) = event_indices.last() {
                if *seq_num < cursor {
                    event_indices = Vec::new();
                }
            }
        }

        let mut events_with_version = event_indices
            .into_iter()
            .map(|(seq, ver, idx)| {
                let event = self.event_store.get_event_by_version_and_index(ver, idx)?;
                let v0 = match &event {
                    ContractEvent::V1(event) => event,
                    ContractEvent::V2(_) => bail!("Unexpected module event"),
                };
                ensure!(
                    seq == v0.sequence_number(),
                    "Index broken, expected seq:{}, actual:{}",
                    seq,
                    v0.sequence_number()
                );
                Ok(EventWithVersion::new(ver, event))
            })
            .collect::<Result<Vec<_>>>()?;
        if order == Order::Descending {
            events_with_version.reverse();
        }

        Ok(events_with_version)
    }

    fn get_block_info_internal(&self, block_height: u64) -> Result<Option<BlockInfo>> {
        self.ledger_db
            .metadata_db()
            .get::<BlockInfoSchema>(&block_height)
    }

    fn get_table_info_option(&self, handle: TableHandle) -> Result<Option<TableInfo>> {
        if self.indexer_async_v2_enabled() {
            return self.get_table_info_from_indexer_async_v2(handle);
        }

        self.get_table_info_from_indexer(handle)
    }

    fn get_table_info_from_indexer_async_v2(
        &self,
        handle: TableHandle,
    ) -> Result<Option<TableInfo>> {
        match &self.indexer_async_v2 {
            Some(indexer_async_v2) => indexer_async_v2.get_table_info_with_retry(handle),
            None => bail!("Indexer Async V2 not enabled."),
        }
    }

    /// TODO(jill): deprecate Indexer once Indexer Async V2 is ready
    fn get_table_info_from_indexer(&self, handle: TableHandle) -> Result<Option<TableInfo>> {
        match &self.indexer {
            Some(indexer) => indexer.get_table_info(handle),
            None => bail!("Indexer not enabled."),
        }
    }
}
