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
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

mod capture;
mod driver;
mod extract;
mod identity;
mod ir;
mod lean;
mod mono;
mod publication;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{ArgGroup, Parser, ValueEnum};
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliCrateType {
    Lib,
    Bin,
}

impl From<CliCrateType> for ir::CrateType {
    fn from(value: CliCrateType) -> Self {
        match value {
            CliCrateType::Lib => Self::Lib,
            CliCrateType::Bin => Self::Bin,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliPanicStrategy {
    Unwind,
    Abort,
}

impl From<CliPanicStrategy> for ir::PanicStrategy {
    fn from(value: CliPanicStrategy) -> Self {
        match value {
            CliPanicStrategy::Unwind => Self::Unwind,
            CliPanicStrategy::Abort => Self::Abort,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliStdlibCrate {
    Core,
}

impl From<CliStdlibCrate> for ir::StdlibCrate {
    fn from(value: CliStdlibCrate) -> Self {
        match value {
            CliStdlibCrate::Core => Self::Core,
        }
    }
}

#[derive(Debug, Parser)]
#[command(
    name = "anneal-rustc-capture capture",
    version,
    about = "Capture pinned Runtime(PostCleanup) MIR",
    group(ArgGroup::new("selection").required(true).multiple(true).args(["select", "instantiate", "scope"]))
)]
pub struct Args {
    #[arg(long)]
    crate_root: PathBuf,
    #[arg(long)]
    crate_name: String,
    #[arg(long, value_enum, default_value_t = CliCrateType::Lib)]
    crate_type: CliCrateType,
    #[arg(long, value_enum, default_value_t = CliPanicStrategy::Unwind)]
    panic: CliPanicStrategy,
    /// Enable runtime integer overflow checks (`-Coverflow-checks=yes`) during
    /// capture instead of `-Coverflow-checks=no`.
    #[arg(long)]
    overflow_checks: bool,
    #[arg(long, default_value = "2024", value_parser = ["2015", "2018", "2021", "2024"])]
    edition: String,
    #[arg(long)]
    target: String,
    /// Publish into a new directory with a UTF-8 resolved path.
    /// An existing destination is refused.
    #[arg(long)]
    out_dir: PathBuf,
    // Capture these callable roots without claiming coverage of other items.
    #[arg(long, action = clap::ArgAction::Append, conflicts_with = "scope")]
    select: Vec<String>,
    /// Capture concrete generic instantiations as JSON
    /// (`{"path":...,"args":[...]}`).
    #[arg(
        long,
        action = clap::ArgAction::Append,
        value_name = "JSON",
        conflicts_with = "scope",
        value_parser = parse_instantiation
    )]
    instantiate: Vec<ir::Instantiation>,
    // Require admission of every required item in the compiler census.
    #[arg(long, value_parser = ["crate"])]
    scope: Option<String>,
    #[arg(long, action = clap::ArgAction::Append)]
    cfg: Vec<String>,
    /// Declare a compile-time environment variable (`KEY=VALUE`) for `env!`
    /// and `option_env!`. Undeclared environment reads still fail closed.
    #[arg(
        long,
        action = clap::ArgAction::Append,
        value_name = "KEY=VALUE",
        value_parser = parse_env_binding
    )]
    env: Vec<(String, String)>,
    /// Override the sysroot resolved from the pinned compiler distribution.
    #[arg(long)]
    sysroot: Option<PathBuf>,
    /// Declare an allowed compiler input; repeat for every staged source file.
    /// An explicit allowlist prevents omitted declarations from authorizing
    /// ambient module or include-file reads.
    #[arg(long, required = true, action = clap::ArgAction::Append)]
    source_file: Vec<PathBuf>,
    /// Capture the named standard-library crate from its unmodified sources.
    /// This capability admits the crate's own language items and skips
    /// object emission. It requires a library crate whose `--crate-name`
    /// matches, selected roots, a compilation that loads no other crate, no
    /// `miri` cfg, and any crate-local `Ordering` language item to have the
    /// modeled shape. The capability is recorded in `capture.json`.
    #[arg(long, value_enum)]
    stdlib_crate: Option<CliStdlibCrate>,
}

fn parse_instantiation(raw: &str) -> Result<ir::Instantiation, String> {
    serde_json::from_str::<ir::Instantiation>(raw)
        .map_err(|e| format!("invalid --instantiate JSON {raw:?}: {e}"))
}

fn parse_env_binding(raw: &str) -> Result<(String, String), String> {
    let Some((key, value)) = raw.split_once('=') else {
        return Err(format!("expected KEY=VALUE environment binding, got {raw:?}"));
    };
    if key.is_empty() {
        return Err("environment variable name must not be empty".to_owned());
    }
    if key.contains('\0') || value.contains('\0') {
        return Err("environment binding must not contain NUL bytes".to_owned());
    }
    Ok((key.to_owned(), value.to_owned()))
}

impl Args {
    pub(crate) fn resolved_scope(&self) -> Result<ir::Scope, Failure> {
        if self.scope.is_some() {
            return Ok(ir::Scope::Crate);
        }
        let roots: BTreeSet<String> = self.select.iter().cloned().collect();
        let instantiations: BTreeSet<ir::Instantiation> =
            self.instantiate.iter().cloned().collect();
        if roots.is_empty() && instantiations.is_empty() {
            return Err(Failure::unsupported("empty selected scope"));
        }
        Ok(ir::Scope::SelectedUnit { roots, instantiations })
    }

    pub(crate) fn resolved_env(&self) -> Result<BTreeMap<String, String>, Failure> {
        let mut declared = BTreeMap::new();
        for (key, value) in &self.env {
            if declared.insert(key.clone(), value.clone()).is_some() {
                return Err(Failure::tool(format!(
                    "duplicate --env binding for {key}"
                )));
            }
        }
        Ok(declared)
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
    let declared_env = args.resolved_env()?;
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
    let manifest = capture::run(&args, &declared_env, &sysroot, &verified)?;
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

/// Entrypoint for the `anneal-rustc-capture` driver binary.
pub fn cli_main() -> ExitCode {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_env_binding_validates_syntax_and_nul_bytes() {
        assert_eq!(
            parse_env_binding("CARGO_PKG_VERSION=0.8.64").unwrap(),
            ("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())
        );
        assert_eq!(
            parse_env_binding("EMPTY=").unwrap(),
            ("EMPTY".to_owned(), String::new())
        );
        assert_eq!(
            parse_env_binding("NESTED=a=b=c").unwrap(),
            ("NESTED".to_owned(), "a=b=c".to_owned())
        );
        assert_eq!(
            parse_env_binding("AT=@literal").unwrap(),
            ("AT".to_owned(), "@literal".to_owned())
        );

        assert!(parse_env_binding("NO_EQUALS").is_err());
        assert!(parse_env_binding("=value").is_err());
        assert!(parse_env_binding("BAD\0KEY=value").is_err());
        assert!(parse_env_binding("KEY=bad\0value").is_err());
    }

    #[test]
    fn resolved_env_sorts_deterministically_and_rejects_duplicates() {
        let base = [
            "anneal-rustc-capture capture",
            "--crate-root=lib.rs",
            "--crate-name=demo",
            "--target=x86_64-unknown-linux-gnu",
            "--out-dir=out",
            "--select=f",
            "--source-file=lib.rs",
        ];

        let args = Args::try_parse_from(
            base.into_iter()
                .chain(["--env=Z_KEY=last", "--env=A_KEY=first"]),
        )
        .unwrap();
        let resolved = args.resolved_env().unwrap();
        let keys: Vec<&str> = resolved.keys().map(String::as_str).collect();
        assert_eq!(keys, vec!["A_KEY", "Z_KEY"]);
        assert_eq!(resolved["A_KEY"], "first");
        assert_eq!(resolved["Z_KEY"], "last");

        for dup in [
            ["--env=FOO=one", "--env=FOO=two"],
            ["--env=FOO=one", "--env=FOO=one"],
        ] {
            let args = Args::try_parse_from(base.into_iter().chain(dup)).unwrap();
            let err = args.resolved_env().unwrap_err();
            assert_eq!(err.status, "tool_failed");
            assert!(
                err.diagnostics[0].contains("duplicate --env binding for FOO"),
                "{err:?}"
            );
        }
    }
}
