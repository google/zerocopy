// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `cargo-anneal-obligations`: prints the per-function evidence ledger.

#![forbid(unsafe_code)]

use std::{
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
    process::ExitCode,
};

use anneal_obligations::{
    build, escape_controls, ratchet, spec_inputs, Baseline, Input, LabeledInput, Receipt, Request,
};
use anneal_spec_lower::{module_path, Source};
use serde_json::Value;

const USAGE: &str = "\
usage: cargo anneal-obligations [--format text|json] [--audit-assumptions]
                                [--ratchet BASELINE] [--crate NAME]
                                [--receipt FILE]... [--request FILE]...
                                [--spec-src-root DIR] [--spec FILE]...

Prints one evidence tier per function, weakest to strongest:
uncontracted, deferred, assumed, runtime_checked, checked_fuzz,
envelope_minted, proven_conditional, proven_closed. Nothing is re-verified;
validate receipts with `cargo anneal inspect` first.

  --receipt FILE     A Receipt Schema v3 JSON document from `cargo anneal
                     verify`. Its census lists the crate's functions, and a
                     verified receipt proves the functions it selects and the
                     instances it verifies through `scope.instantiations`,
                     each instance as its own item.
  --request FILE     A `request.json`; its selected-unit roots, and the
                     generic functions its `scope.instantiations` name, have
                     a stated specification.
  --spec FILE        A Rust file whose `anneal::spec` items have a stated
                     specification. With --spec-src-root DIR, FILE is relative
                     to DIR and its module path is derived from its location,
                     as for `anneal-spec-lower --src-root`.
  --crate NAME       Require every receipt and request to be for crate NAME.
  --format FORMAT    `text` (the default) or `json`.
  --audit-assumptions
                     Report proven_conditional items as assumed, so that no
                     proof whose receipt discloses conditions counts as proven.
  --ratchet BASELINE Exit 1 if any item in BASELINE (an earlier `--format json`
                     ledger) now has a lower tier or is missing, if a
                     conditional proof gained a condition, or if the number
                     of unproven items grew.

Exit status: 0 on success, 1 on a ratchet regression, 2 on usage, I/O, or
input errors.";

/// The largest input file read, which comfortably exceeds the largest
/// receipts for whole-crate captures.
const MAX_INPUT_BYTES: u64 = 512 * 1024 * 1024;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Format {
    Text,
    Json,
}

struct Args {
    format: Format,
    audit_assumptions: bool,
    ratchet: Option<PathBuf>,
    crate_name: Option<String>,
    receipts: Vec<PathBuf>,
    requests: Vec<PathBuf>,
    spec_src_root: Option<PathBuf>,
    specs: Vec<String>,
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // Cargo runs `cargo anneal-obligations ARGS` as
    // `cargo-anneal-obligations anneal-obligations ARGS`.
    if args.first().is_some_and(|a| a == "anneal-obligations") {
        args.remove(0);
    }
    match run(args) {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("cargo-anneal-obligations: {msg}");
            ExitCode::from(2)
        }
    }
}

fn parse_args(raw: Vec<String>) -> Result<Option<Args>, String> {
    let mut args = Args {
        format: Format::Text,
        audit_assumptions: false,
        ratchet: None,
        crate_name: None,
        receipts: Vec::new(),
        requests: Vec::new(),
        spec_src_root: None,
        specs: Vec::new(),
    };
    let mut raw = raw.into_iter();
    while let Some(a) = raw.next() {
        let mut value =
            |flag: &str| raw.next().ok_or_else(|| format!("{flag} needs a value\n\n{USAGE}"));
        match a.as_str() {
            "-h" | "--help" => return Ok(None),
            "--format" => {
                args.format = match value("--format")?.as_str() {
                    "text" => Format::Text,
                    "json" => Format::Json,
                    f => return Err(format!("unknown format `{}`\n\n{USAGE}", escape_controls(f))),
                }
            }
            "--audit-assumptions" => args.audit_assumptions = true,
            "--ratchet" if args.ratchet.is_some() => {
                return Err(format!("--ratchet may be given once\n\n{USAGE}"));
            }
            "--ratchet" => args.ratchet = Some(value("--ratchet")?.into()),
            "--crate" if args.crate_name.is_some() => {
                return Err(format!("--crate may be given once\n\n{USAGE}"));
            }
            "--crate" => args.crate_name = Some(value("--crate")?),
            "--receipt" => args.receipts.push(value("--receipt")?.into()),
            "--request" => args.requests.push(value("--request")?.into()),
            "--spec-src-root" if args.spec_src_root.is_some() => {
                return Err(format!("--spec-src-root may be given once\n\n{USAGE}"));
            }
            "--spec-src-root" => args.spec_src_root = Some(value("--spec-src-root")?.into()),
            "--spec" => args.specs.push(value("--spec")?),
            f => return Err(format!("unknown argument `{}`\n\n{USAGE}", escape_controls(f))),
        }
    }
    if args.receipts.is_empty() && args.requests.is_empty() && args.specs.is_empty() {
        return Err(format!("give at least one --receipt, --request, or --spec\n\n{USAGE}"));
    }
    if args.spec_src_root.is_some() && args.specs.is_empty() {
        return Err(format!("--spec-src-root needs at least one --spec\n\n{USAGE}"));
    }
    Ok(Some(args))
}

fn run(raw: Vec<String>) -> Result<ExitCode, String> {
    let Some(mut args) = parse_args(raw)? else {
        println!("{USAGE}");
        return Ok(ExitCode::SUCCESS);
    };
    for paths in [&mut args.receipts, &mut args.requests] {
        paths.sort();
        paths.dedup();
    }
    let mut inputs = Vec::new();
    for path in &args.receipts {
        let receipt = Receipt::from_json(&read_json(path)?)
            .map_err(|e| format!("{}: {e}", display_path(path)))?;
        inputs.push(LabeledInput { label: label(path), input: Input::Receipt(receipt) });
    }
    for path in &args.requests {
        let request = Request::from_json(&read_json(path)?)
            .map_err(|e| format!("{}: {e}", display_path(path)))?;
        inputs.push(LabeledInput { label: label(path), input: Input::Request(request) });
    }
    let mut specs = args.specs.clone();
    specs.sort();
    specs.dedup();
    let mut sources = Vec::new();
    for file in &specs {
        let path =
            args.spec_src_root.as_deref().map_or_else(|| PathBuf::from(file), |r| r.join(file));
        let text = read_text(&path)?;
        let module = if args.spec_src_root.is_some() { module_path(file) } else { Vec::new() };
        sources.push(Source { label: file.clone(), text, module });
    }
    if !sources.is_empty() {
        inputs.extend(spec_inputs(&sources)?);
    }

    let ledger = build(&inputs, args.crate_name.as_deref(), args.audit_assumptions)?;
    let rendered = match args.format {
        Format::Text => ledger.to_text(),
        Format::Json => {
            let mut text = serde_json::to_string_pretty(&ledger.to_json())
                .map_err(|e| format!("cannot render JSON: {e}"))?;
            text.push('\n');
            text
        }
    };
    io::stdout().write_all(rendered.as_bytes()).map_err(|e| format!("cannot write output: {e}"))?;

    let Some(path) = &args.ratchet else {
        return Ok(ExitCode::SUCCESS);
    };
    let baseline = Baseline::from_json(&read_json(path)?)
        .map_err(|e| format!("{}: {e}", display_path(path)))?;
    let findings =
        ratchet(&baseline, &ledger).map_err(|e| format!("{}: {e}", display_path(path)))?;
    if findings.is_empty() {
        return Ok(ExitCode::SUCCESS);
    }
    for finding in &findings {
        eprintln!("cargo-anneal-obligations: ratchet: {finding}");
    }
    eprintln!(
        "cargo-anneal-obligations: ratchet failed with {} finding(s) against {}",
        findings.len(),
        display_path(path)
    );
    Ok(ExitCode::from(1))
}

fn label(path: &Path) -> String {
    path.display().to_string()
}

fn display_path(path: &Path) -> String {
    escape_controls(&path.display().to_string())
}

fn read_text(path: &Path) -> Result<String, String> {
    let shown = display_path(path);
    let meta = fs::metadata(path).map_err(|e| format!("cannot read {shown}: {e}"))?;
    if meta.len() > MAX_INPUT_BYTES {
        return Err(format!("{shown} exceeds {MAX_INPUT_BYTES} bytes"));
    }
    fs::read_to_string(path).map_err(|e| format!("cannot read {shown}: {e}"))
}

fn read_json(path: &Path) -> Result<Value, String> {
    let shown = display_path(path);
    serde_json::from_str(&read_text(path)?)
        .map_err(|e| format!("{shown} is not valid JSON: {}", escape_controls(&e.to_string())))
}
