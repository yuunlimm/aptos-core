// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use crate::{errors::*, task::ExecutorTask, view::LatestView};
use aptos_aggregator::types::{code_invariant_error, PanicError, PanicOr};
use aptos_logger::error;
use aptos_mvhashmap::types::ValueWithLayout;
use aptos_state_view::TStateView;
use aptos_types::{
    executable::Executable, transaction::BlockExecutableTransaction as Transaction,
    write_set::TransactionWrite,
};
use bytes::Bytes;
use move_core_types::value::MoveTypeLayout;
use rand::{thread_rng, Rng};
use std::{collections::BTreeMap, sync::Arc};

macro_rules! groups_to_finalize {
    ($outputs:expr, $($txn_idx:expr),*) => {{
	let group_write_ops = $outputs.resource_group_metadata_ops($($txn_idx),*);

        group_write_ops.into_iter()
            .map(|val| (val, false))
            .chain([()].into_iter().flat_map(|_| {
		// Lazily evaluated only after iterating over group_write_ops.
                $outputs.group_reads_needing_delayed_field_exchange($($txn_idx),*)
                    .into_iter()
                    .map(|val| (val, true))
            }))
    }};
}

pub(crate) use groups_to_finalize;

pub(crate) fn resource_group_error(err_msg: String) -> PanicOr<IntentionalFallbackToSequential> {
    error!("resource_group_error: {:?}", err_msg);
    PanicOr::Or(IntentionalFallbackToSequential::ResourceGroupError(err_msg))
}

pub(crate) fn map_finalized_group<T: Transaction, E: ExecutorTask<Txn = T>>(
    group_key: T::Key,
    finalized_group: anyhow::Result<Vec<(T::Tag, ValueWithLayout<T::Value>)>>,
    metadata_op: T::Value,
    is_read_needing_exchange: bool,
) -> Result<(T::Key, T::Value, Vec<(T::Tag, ValueWithLayout<T::Value>)>), E::Error> {
    let metadata_is_deletion = metadata_op.is_deletion();

    match finalized_group {
        Ok(finalized_group) => {
            if is_read_needing_exchange && metadata_is_deletion {
                // Value needed exchange but was not written / modified during the txn
                // execution: may not be empty.
                Err(Error::FallbackToSequential(resource_group_error(format!(
                    "Value only read and exchanged, but metadata op is Deletion",
                ))))
            } else if finalized_group.is_empty() != metadata_is_deletion {
                // finalize_group already applies the deletions.
                Err(Error::FallbackToSequential(resource_group_error(format!(
                    "Group is empty = {} but op is deletion = {} in parallel execution",
                    finalized_group.is_empty(),
                    metadata_is_deletion
                ))))
            } else {
                Ok((group_key, metadata_op, finalized_group))
            }
        },
        Err(e) => Err(Error::FallbackToSequential(resource_group_error(format!(
            "Error committing resource group {:?}",
            e
        )))),
    }
}

pub(crate) fn serialize_groups<T: Transaction>(
    finalized_groups: Vec<(T::Key, T::Value, Vec<(T::Tag, Arc<T::Value>)>)>,
) -> ::std::result::Result<Vec<(T::Key, T::Value)>, PanicOr<IntentionalFallbackToSequential>> {
    finalized_groups
        .into_iter()
        .map(|(group_key, mut metadata_op, finalized_group)| {
            let btree: BTreeMap<T::Tag, Bytes> = finalized_group
                .into_iter()
                // TODO[agg_v2](fix): Should anything be done using the layout here?
                .map(|(resource_tag, arc_v)| {
                    let bytes = arc_v
                        .extract_raw_bytes()
                        .expect("Deletions should already be applied");
                    (resource_tag, bytes)
                })
                .collect();

            // TODO[agg_v2](fix): Handle potential serialization failures.
            bcs::to_bytes(&btree)
                .map_err(|e| {
                    resource_group_error(format!("Unexpected resource group error {:?}", e))
                })
                .map(|group_bytes| {
                    metadata_op.set_bytes(group_bytes.into());
                    (group_key, metadata_op)
                })
        })
        .collect()
}

pub(crate) fn gen_id_start_value(sequential: bool) -> u32 {
    // IDs are ephemeral. Pick a random prefix, and different each time,
    // in case exchange is mistakenly not performed - to more easily catch it.
    // And in a bad case where it happens in prod, to and make sure incorrect
    // block doesn't get committed, but chain halts.
    // (take a different range from parallel execution, to even more easily differentiate)

    let offset = if sequential { 0 } else { 1000 };
    thread_rng().gen_range(1 + offset, 1000 + offset) * 1_000_000
}

pub(crate) fn map_id_to_values_in_group_writes<
    T: Transaction,
    S: TStateView<Key = T::Key> + Sync,
    X: Executable + 'static,
>(
    finalized_groups: Vec<(T::Key, T::Value, Vec<(T::Tag, ValueWithLayout<T::Value>)>)>,
    latest_view: &LatestView<T, S, X>,
) -> ::std::result::Result<Vec<(T::Key, T::Value, Vec<(T::Tag, Arc<T::Value>)>)>, PanicError> {
    let mut patched_finalized_groups = Vec::with_capacity(finalized_groups.len());
    for (group_key, group_metadata_op, resource_vec) in finalized_groups.into_iter() {
        let mut patched_resource_vec = Vec::with_capacity(resource_vec.len());
        for (tag, value_with_layout) in resource_vec.into_iter() {
            let value = match value_with_layout {
                ValueWithLayout::RawFromStorage(value) => value,
                ValueWithLayout::Exchanged(value, None) => value,
                ValueWithLayout::Exchanged(value, Some(layout)) => Arc::new(
                    replace_ids_with_values(&value, layout.as_ref(), latest_view)?,
                ),
            };
            patched_resource_vec.push((tag, value));
        }
        patched_finalized_groups.push((group_key, group_metadata_op, patched_resource_vec));
    }
    Ok(patched_finalized_groups)
}

// For each delayed field in resource write set, replace the identifiers with values.
pub(crate) fn map_id_to_values_in_write_set<
    T: Transaction,
    S: TStateView<Key = T::Key> + Sync,
    X: Executable + 'static,
>(
    resource_write_set: Vec<(T::Key, (T::Value, Option<Arc<MoveTypeLayout>>))>,
    latest_view: &LatestView<T, S, X>,
) -> BTreeMap<T::Key, T::Value> {
    let mut patched_resource_write_set = BTreeMap::new();

    for (key, (write_op, layout)) in resource_write_set.into_iter() {
        // layout is Some(_) if it contains a delayed field
        if let Some(layout) = layout {
            if !write_op.is_deletion() {
                match write_op.bytes() {
                    // TODO[agg_v2](fix): propagate error
                    None => unreachable!(),
                    Some(write_op_bytes) => {
                        let patched_bytes = match latest_view
                            .replace_identifiers_with_values(write_op_bytes, &layout)
                        {
                            Ok((bytes, _)) => bytes,
                            Err(_) => {
                                unreachable!("Failed to replace identifiers with values")
                            },
                        };
                        let mut patched_write_op = write_op;
                        patched_write_op.set_bytes(patched_bytes);
                        patched_resource_write_set.insert(key, patched_write_op);
                    },
                }
            }
        }
    }
    patched_resource_write_set
}

// Parse the input `value` and replace delayed field identifiers with corresponding values
// TODO: remove pub crate after refactoring.
pub(crate) fn replace_ids_with_values<
    T: Transaction,
    S: TStateView<Key = T::Key> + Sync,
    X: Executable + 'static,
>(
    value: &Arc<T::Value>,
    layout: &MoveTypeLayout,
    latest_view: &LatestView<T, S, X>,
) -> ::std::result::Result<T::Value, PanicError> {
    if let Some(mut value) = value.convert_read_to_modification() {
        if let Some(value_bytes) = value.bytes() {
            let (patched_bytes, _) = latest_view
                .replace_identifiers_with_values(value_bytes, layout)
                .unwrap();
            value.set_bytes(patched_bytes);
            Ok(value)
        } else {
            Err(code_invariant_error(format!(
                "Value to be exchanged doesn't have bytes: {:?}",
                value,
            )))
        }
    } else {
        Err(code_invariant_error(format!(
            "Value to be exchanged cannot be transformed to modification: {:?}",
            value,
        )))
    }
}
