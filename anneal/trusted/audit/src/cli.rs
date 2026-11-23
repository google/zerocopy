// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Provides the standalone CLI entry point (`anneal-audit`) for auditing
//! Anneal's repository trust boundary (`trusted/` vs. `theory/` and
//! `correspondence/`) in CI.

use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Parser;
use clap::error::ErrorKind;

use crate::{Checker, Failure, Json};

#[derive(Parser)]
#[command(
    name = "anneal-audit",
    version,
    about = "Repository trusted-boundary and kernel environment auditor for Anneal"
)]
struct Cli {
    /// Path to the pinned `lean` binary (defaults to the installed Anneal
    /// toolchain's `lean`).
    #[arg(long)]
    lean: Option<PathBuf>,

    /// Path to the Anneal repository root (defaults to the workspace root).
    #[arg(long)]
    anneal_root: Option<PathBuf>,

    /// Emit the full JSON audit report instead of a human-readable summary.
    #[arg(long)]
    json: bool,

    /// Require Pass 2 (`vendor/lean-miri/`, `trusted/correspondence/`, and
    /// `correspondence/`) correspondence verification to be present and pass.
    #[arg(long)]
    require_correspondence: bool,

    /// Optional directory outside `--anneal-root` for caching verified
    /// `Miri.*` `.olean` artifacts across runs (overrides
    /// `ANNEAL_MIRI_CACHE_DIR`).
    #[arg(long)]
    miri_cache_dir: Option<PathBuf>,
}

pub fn main() -> ExitCode {
    // Paths are native OS values. Let clap validate each argument instead of
    // making an unrelated non-UTF-8 path panic before argument handling.
    match run(env::args_os().collect()) {
        Ok(code) => ExitCode::from(code),
        Err((code, msg)) => {
            eprintln!("{msg}");
            ExitCode::from(code)
        }
    }
}

fn failure_message(err: &Failure, checker: Option<&Checker>) -> (u8, String) {
    let began = checker.is_some_and(Checker::execution_began);
    (
        err.code as u8,
        format!(
            "Trusted check failed ({}): {}\nTarget execution began: {began}\nRetry only after resolving/reobserving the reported failure.",
            err.phase, err.message
        ),
    )
}

fn run(raw_args: Vec<OsString>) -> Result<u8, (u8, String)> {
    let cli = match Cli::try_parse_from(raw_args) {
        Ok(c) => c,
        Err(e) => {
            if matches!(e.kind(), ErrorKind::DisplayHelp | ErrorKind::DisplayVersion) {
                print!("{e}");
                return Ok(0);
            }
            return Err((2, e.to_string().trim_end().to_string()));
        }
    };

    let checkout = cli
        .anneal_root
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."));
    let mut checker = Checker::new(&checkout, cli.lean.as_deref()).map_err(|e| {
        (
            2,
            format!("Trusted check could not initialize staging directory: {e}"),
        )
    })?;
    if cli.require_correspondence {
        checker.set_require_correspondence(true);
    }
    if let Some(cache_dir) = cli.miri_cache_dir {
        checker.set_miri_cache_dir(Some(cache_dir));
    }

    match checker.run() {
        Ok(report) => {
            if cli.json {
                println!(
                    "{}",
                    serde_json::to_string_pretty(&report).expect("serialize audit report")
                );
                return Ok(0);
            }
            let guarantee = report.get("guarantee").and_then(Json::as_str).unwrap_or("");
            let k_decls = report
                .get("kernelDeclarations")
                .and_then(Json::as_i64)
                .unwrap_or(0);
            let replayed = report
                .get("replayedDeclarations")
                .and_then(Json::as_i64)
                .unwrap_or(0);
            let axioms = report
                .get("axioms")
                .and_then(|v| serde_json::to_string(v).ok())
                .unwrap_or_else(|| "[]".to_string());
            let tc = report.get("toolchain").and_then(Json::as_str).unwrap_or("");
            println!(
                "PASS: {guarantee}\n\
                 {} Trusted modules; {} Theory modules; \
                 {k_decls} Trusted kernel declarations; \
                 {replayed} total replayed declarations; \
                 axioms={axioms}\n\
                 {tc}",
                checker.modules().len(),
                checker.theory_modules().len()
            );
            if let Some(miri_mods) = report.get("miriClosureModules").and_then(Json::as_u64) {
                let miri_commit = report
                    .get("miriCommit")
                    .and_then(Json::as_str)
                    .unwrap_or("unknown");
                let miri_replayed = report
                    .get("miriReplayedDeclarations")
                    .and_then(Json::as_u64)
                    .unwrap_or(0);
                let miri_decls = report
                    .get("miriClosureReachableDeclarations")
                    .and_then(Json::as_u64)
                    .unwrap_or(0);
                println!(
                    "Vendor Miri: {miri_mods} verified closure modules \
                     ({miri_replayed} kernel-replayed declarations; \
                     {miri_decls} reachable cone declarations; \
                     commit {miri_commit})"
                );
            }
            if let Some(corr_decls) = report
                .get("correspondenceDeclarations")
                .and_then(Json::as_u64)
            {
                let corr_reachable = report
                    .get("correspondenceReachableDeclarations")
                    .and_then(Json::as_u64)
                    .unwrap_or(0);
                let corr_axioms = report
                    .get("correspondenceAxioms")
                    .and_then(|v| serde_json::to_string(v).ok())
                    .unwrap_or_else(|| "[]".to_string());
                println!(
                    "Correspondence: {corr_decls} replayed declarations; \
                     {corr_reachable} reachable declarations; \
                     axioms={corr_axioms}"
                );
            }
            Ok(0)
        }
        Err(err) => Err(failure_message(&err, Some(&checker))),
    }
}
