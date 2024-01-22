// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use aptos_comparison_testing::{
    prepare_aptos_packages, DataCollection, Execution, ExecutionMode, APTOS_COMMONS,
};
use aptos_rest_client::Client;
use clap::{Parser, Subcommand};
use std::path::PathBuf;
use url::Url;

const BATCH_SIZE: u64 = 100;

#[derive(Subcommand)]
pub enum Cmd {
    /// Collect and dump the data
    Dump {
        /// Endpoint url to obtain the txn data,
        /// e.g. `https://api.mainnet.aptoslabs.com/v1` for mainnet.
        /// To avoid rate limiting, users need to apply for API key from `https://developers.aptoslabs.com/`
        /// and set the env variable X_API_KEY using the obtained key
        endpoint: String,
        /// Path to the dumped data
        output_path: Option<PathBuf>,
        /// Do not dump failed txns
        #[clap(long, default_value_t = false)]
        skip_failed_txns: bool,
        /// Do not dump publish txns
        #[clap(long, default_value_t = false)]
        skip_publish_txns: bool,
        /// Collect txns regardless whether the source code is available
        #[clap(long, default_value_t = false)]
        skip_source_code_check: bool,
        /// Dump the write set of txns
        #[clap(long, default_value_t = false)]
        dump_write_set: bool,
        /// Directly execute the txns without dumping the data
        #[clap(long, default_value_t = false)]
        execution_only: bool,
        /// Whether to execute against V1, V2 alone or both compilers for comparison
        /// Used when execution_only is true
        #[clap(long)]
        execution_mode: Option<ExecutionMode>,
    },
    /// Execution of txns
    Execute {
        /// Path to the data
        input_path: Option<PathBuf>,
        /// Whether to execute against V1, V2 alone or both compilers for comparison
        #[clap(long)]
        execution_mode: Option<ExecutionMode>,
    },
}

#[derive(Parser)]
pub struct Argument {
    #[clap(subcommand)]
    cmd: Cmd,

    /// Scan/execute from the txn of this version
    #[clap(long)]
    begin_version: u64,

    /// Number of txns to scan/execute
    #[clap(long)]
    limit: u64,
}

#[tokio::main]
async fn main() -> Result<()> {
    let args = Argument::parse();

    match args.cmd {
        Cmd::Dump {
            endpoint,
            output_path,
            skip_failed_txns,
            skip_publish_txns,
            skip_source_code_check: skip_source_code,
            dump_write_set,
            execution_only,
            execution_mode,
        } => {
            let batch_size = BATCH_SIZE;
            let output = if let Some(path) = output_path {
                path
            } else {
                PathBuf::from(".")
            };
            if !output.exists() {
                std::fs::create_dir_all(output.as_path()).unwrap();
            }
            if !skip_source_code {
                prepare_aptos_packages(output.join(APTOS_COMMONS)).await;
            }
            let data_collector = DataCollection::new_with_rest_client(
                Client::new(Url::parse(&endpoint)?),
                output.clone(),
                batch_size,
                skip_failed_txns,
                skip_publish_txns,
                dump_write_set,
                skip_source_code,
                execution_only,
                execution_mode.unwrap_or_default(),
            )?;
            data_collector
                .dump_data(args.begin_version, args.limit)
                .await?;
        },
        Cmd::Execute {
            input_path,
            execution_mode,
        } => {
            let input = if let Some(path) = input_path {
                path
            } else {
                PathBuf::from(".")
            };
            prepare_aptos_packages(input.join(APTOS_COMMONS)).await;
            let executor = Execution::new(input, execution_mode.unwrap_or_default());
            executor
                .execute_txns(args.begin_version, args.limit)
                .await?;
        },
    };
    Ok(())
}
