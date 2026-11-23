// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Run the pinned compiler or explicitly capture one configured compilation.
//! Typed capture does not verify a crate; the host must check the generated
//! subject against its authored specifications and exact root.

#![feature(normalize_lexically, rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod capture;
mod driver;
mod extract;
mod identity;
mod ir;
mod lean;
mod publication;

use std::collections::BTreeSet;
use std::env;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{ArgGroup, Parser};
use serde::Serialize;

#[derive(Debug, Parser)]
#[command(
    name = "anneal-rustc-capture capture",
    version,
    about = "Capture pinned Runtime(PostCleanup) MIR",
    group(ArgGroup::new("selection").required(true).args(["select", "scope"]))
)]
pub struct Args {
    #[arg(long)]
    crate_root: PathBuf,
    #[arg(long)]
    crate_name: String,
    #[arg(long, default_value = "2024", value_parser = ["2015", "2018", "2021", "2024"])]
    edition: String,
    #[arg(long)]
    target: String,
    /// Publish into a new directory with a UTF-8 resolved path.
    /// An existing destination is refused.
    #[arg(long)]
    out_dir: PathBuf,
    // Capture these callable roots without claiming coverage of other items.
    #[arg(long, action = clap::ArgAction::Append)]
    select: Vec<String>,
    // Require admission of every required item in the compiler census.
    #[arg(long, value_parser = ["crate"])]
    scope: Option<String>,
    #[arg(long, action = clap::ArgAction::Append)]
    cfg: Vec<String>,
    /// Override the sysroot resolved from the pinned compiler distribution.
    #[arg(long)]
    sysroot: Option<PathBuf>,
    /// Declare an allowed compiler input; repeat for every staged source file.
    /// An explicit allowlist prevents omitted declarations from authorizing
    /// ambient module or include-file reads.
    #[arg(long, required = true, action = clap::ArgAction::Append)]
    source_file: Vec<PathBuf>,
}

impl Args {
    pub(crate) fn resolved_scope(&self) -> Result<ir::Scope, Failure> {
        if self.scope.is_some() {
            return Ok(ir::Scope::Crate);
        }
        let roots: BTreeSet<String> = self.select.iter().cloned().collect();
        if roots.is_empty() {
            return Err(Failure::unsupported("empty selected scope"));
        }
        Ok(ir::Scope::SelectedUnit { roots })
    }
}

#[derive(Debug, Serialize)]
pub struct Failure {
    status: &'static str,
    diagnostics: Vec<String>,
    unsupported: Vec<ir::Unsupported>,
}

impl Failure {
    fn tool(message: impl Into<String>) -> Self {
        Self {
            status: "tool_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn io(error: std::io::Error) -> Self {
        Self::tool(error.to_string())
    }
    fn compiler(message: impl Into<String>) -> Self {
        Self {
            status: "compiler_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported(message: impl Into<String>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported_items(items: Vec<ir::Unsupported>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![format!(
                "{} required obligations are unsupported",
                items.len()
            )],
            unsupported: items,
        }
    }
}

fn run(mut args: Args) -> Result<serde_json::Value, Failure> {
    if args.target != "x86_64-unknown-linux-gnu" {
        return Err(Failure::unsupported(
            "the initial adapter supports only x86_64-unknown-linux-gnu",
        ));
    }
    // Declarations, selectors, and cfgs are sets. A declared alias selects its
    // canonical filename; it does not expose other ambient aliases to rustc.
    // The recording loader uses those names and their ancestor directories as
    // its source namespace, independently checking the exact bytes read.
    // Sorting keeps manifests stable; normalization alone proves no read.
    args.crate_root = args.crate_root.canonicalize().map_err(Failure::io)?;
    for path in &mut args.source_file {
        *path = path.canonicalize().map_err(Failure::io)?;
    }
    args.source_file.sort();
    args.source_file.dedup();
    args.cfg.sort();
    args.cfg.dedup();
    // Resolve explicit or packaged sysroot lexically (preserving virtual
    // symlink-forest layouts such as `<sysroot>/bin/rustc` beside
    // `<sysroot>/lib/rustlib`) and verify compiler identity and Linux driver
    // residency via open-FD `(st_dev, st_ino)` + SHA-256 before creating
    // publication directories or entering rustc's fatal-error handler.
    let raw_sysroot = match args.sysroot.take() {
        Some(sysroot) => sysroot,
        None => driver::resolve_packaged_sysroot().map_err(Failure::tool)?,
    };
    let sysroot = identity::normalize_logical_sysroot(&raw_sysroot)?;
    args.sysroot = Some(sysroot.clone());
    let verified = identity::verify_compiler(&sysroot, &args.target)?;
    // Keep compiler side effects outside the public artifact pair. The
    // publication owner cleans up staging on every error and unwind; only its
    // completed directory rename permits a captured status below.
    let publication = publication::Publication::new(&args.out_dir).map_err(Failure::io)?;
    args.out_dir = publication.compiler_dir();
    let manifest = capture::run(&args, &sysroot, &verified)?;
    let json =
        serde_json::to_vec_pretty(&manifest).map_err(|error| Failure::tool(error.to_string()))?;
    let lean = lean::render(&manifest.program);
    let destination = publication
        .publish(&json, lean.as_bytes())
        .map_err(Failure::io)?;
    let json_path = destination.join("capture.json");
    let lean_path = destination.join("Captured.lean");
    Ok(serde_json::json!({
        "status": "captured", "capture": json_path, "lean": lean_path,
        "selected_count": manifest.selected.len(),
        "census_count": manifest.census.len(),
        "source_count": manifest.source_files.len(),
    }))
}

fn run_capture(args: Vec<OsString>) -> ExitCode {
    let args = match Args::try_parse_from(
        std::iter::once(OsString::from("anneal-rustc-capture capture")).chain(args),
    ) {
        Ok(args) => args,
        Err(error)
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) =>
        {
            print!("{error}");
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            println!(
                "{}",
                serde_json::to_string(&Failure::tool(error.to_string()))
                    .expect("serializable failure")
            );
            return ExitCode::from(2);
        }
    };
    // A callback or adapter panic must become an explicit failed capture,
    // never an apparently successful receipt for an incomplete compiler run.
    // rustc's own ICE hook still supplies the detailed stderr diagnostic.
    let result = std::panic::catch_unwind(|| run(args)).unwrap_or_else(|_| {
        Err(Failure::tool(
            "capture or compiler panicked; see stderr diagnostics",
        ))
    });
    match result {
        Ok(success) => {
            println!("{success}");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!(
                "{}",
                serde_json::to_string(&failure).expect("serializable failure")
            );
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    let mut args: Vec<_> = env::args_os().skip(1).collect();
    if args.is_empty() || (args.len() == 1 && matches!(args[0].to_str(), Some("--help" | "-h"))) {
        println!(
            "Usage: anneal-rustc-capture [--] <rustc arguments>\n\
             \n\
             Run the pinned compiler and report a successful analysis callback on stderr.\n\
             Verification is not performed.\n\
             \n\
             Pass compiler options unchanged, including --sysroot for an unbundled\n\
             development binary. Installed binaries use the adjacent rust/ sysroot.\n\
             Use -- before compiler --help, --version, or an input named capture.\n\
             \n\
             Use anneal-rustc-capture capture --help for typed MIR capture."
        );
        return ExitCode::SUCCESS;
    }
    if args.len() == 1 && matches!(args[0].to_str(), Some("--version" | "-V")) {
        println!("anneal-rustc-capture {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    // Only the explicit command selects typed capture. Inspect it before
    // removing the raw compiler escape, so `-- capture` remains a rustc input.
    if args.first().is_some_and(|arg| arg == "capture") {
        args.remove(0);
        return run_capture(args);
    }
    if args.first().is_some_and(|arg| arg == "--") {
        args.remove(0);
    }
    driver::run(args)
}
