// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-spec-lower`: writes or checks lowered specification modules.

use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use anneal_spec_lower::{
    closure::parse_capture_json, list_targets, lower_with, module_path, Format, Options, Scope,
    Source,
};

const USAGE: &str = "\
usage: anneal-spec-lower [--src-root DIR] [SELECTION] [--format v1|v2-module]
                         [--crate-slug S] [--scope unit|crate]
                         [--capture-json FILE] (--out-dir DIR | --check DIR) FILE...
       anneal-spec-lower [--src-root DIR] --list-targets FILE...

Lowers the `anneal::spec` items and `anneal::external_spec!` blocks in FILE...
to one specification unit. Every item in FILE... is checked, selected or not.

  --src-root DIR    Resolve FILE relative to DIR and derive each file's module
                    path from its location (`a/b.rs` is `a::b`). Without it,
                    FILE paths are used as given and inline items belong to
                    the crate root.
  --target PATH     Lower only the item with `rust-path-v1` path PATH (no
                    scheme prefix). Repeatable. Selecting lowers only the
                    `#[anneal::pure]` helpers the selected items reach.
  --claim C         Lower only the items in claim C: those with
                    `claim = \"C\"`, or the one item whose derived singleton
                    claim is C. With --target, every target must be in C.
  --format v1       (Default.) Write Spec.lean (namespace `Spec`),
                    spec_span_map.json, and spec-closure.golden.
  --format v2-module
                    Write Specs/S/C.lean (namespace `Specs.S.C`), a Lean
                    module that records no Rust source positions, plus
                    spec-closure.golden. Needs --crate-slug S and --claim C.
  --crate-slug S    The crate component of the v2-module namespace.
  --scope unit|crate
                    Verification scope recorded in `MirEnvelopeSpec.gaps`
                    (defaults to `unit`).
  --capture-json FILE
                    Synthesize default UB-freedom entries for unannotated safe
                    callees in FILE and fail closed on unannotated `unsafe`
                    callees.
  --out-dir DIR     Write the output files under DIR.
  --check DIR       Exit 1 unless the output files under DIR already match
                    the lowering byte for byte.
  --list-targets    Print every item FILE... specify as a JSON array of
                    {\"target\", \"claim\", \"file\", \"kind\"} objects
                    sorted by target, where kind is \"inline\" or
                    \"external\". Clauses are not type-checked, and FILE...
                    may specify no items.

Exit status: 0 on success, 1 on specification errors or a failed --check,
2 on usage or I/O errors.";

enum Mode {
    Write(PathBuf),
    Check(PathBuf),
    List,
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("anneal-spec-lower: {msg}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode, String> {
    let mut args = std::env::args().skip(1);
    let mut src_root: Option<PathBuf> = None;
    let mut mode = None;
    let mut opts = Options::default();
    let mut format_given = false;
    let mut scope_given = false;
    let mut capture_json_path: Option<PathBuf> = None;
    let mut files = Vec::new();
    while let Some(a) = args.next() {
        let mut value =
            |flag: &str| args.next().ok_or_else(|| format!("{flag} needs a value\n\n{USAGE}"));
        match a.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                return Ok(ExitCode::SUCCESS);
            }
            "--src-root" => src_root = Some(value("--src-root")?.into()),
            "--out-dir" | "--check" | "--list-targets" if mode.is_some() => {
                return Err(format!(
                    "only one of --out-dir, --check, or --list-targets may be given\n\n{USAGE}"
                ));
            }
            "--out-dir" => mode = Some(Mode::Write(value("--out-dir")?.into())),
            "--check" => mode = Some(Mode::Check(value("--check")?.into())),
            "--list-targets" => mode = Some(Mode::List),
            "--target" => opts.targets.push(value("--target")?),
            "--claim" => opts.claim = Some(value("--claim")?),
            "--crate-slug" => opts.crate_slug = Some(value("--crate-slug")?),
            "--scope" => {
                scope_given = true;
                opts.scope = match value("--scope")?.as_str() {
                    "unit" => Scope::Unit,
                    "crate" => Scope::Crate,
                    s => return Err(format!("unknown scope `{s}`\n\n{USAGE}")),
                };
            }
            "--capture-json" => {
                capture_json_path = Some(value("--capture-json")?.into());
            }
            "--format" => {
                format_given = true;
                opts.format = match value("--format")?.as_str() {
                    "v1" => Format::V1,
                    "v2-module" => Format::V2Module,
                    f => return Err(format!("unknown format `{f}`\n\n{USAGE}")),
                }
            }
            f if f.starts_with('-') => return Err(format!("unknown option `{f}`\n\n{USAGE}")),
            f => files.push(f.to_string()),
        }
    }
    let mode = mode.ok_or_else(|| {
        format!("one of --out-dir, --check, or --list-targets is required\n\n{USAGE}")
    })?;
    if matches!(mode, Mode::List)
        && (!opts.targets.is_empty()
            || opts.claim.is_some()
            || opts.crate_slug.is_some()
            || format_given
            || scope_given
            || capture_json_path.is_some())
    {
        return Err(format!("--list-targets takes no selection or format options\n\n{USAGE}"));
    }
    if let Some(cap_path) = &capture_json_path {
        let cap_text = fs::read_to_string(cap_path)
            .map_err(|e| format!("cannot read {}: {e}", cap_path.display()))?;
        let parsed = parse_capture_json(&cap_text)
            .map_err(|e| format!("invalid {}: {e}", cap_path.display()))?;
        if scope_given && parsed.scope != opts.scope {
            return Err(format!(
                "--scope {:?} conflicts with capture JSON scope {:?}",
                opts.scope, parsed.scope
            ));
        }
        opts.scope = parsed.scope;
        opts.capture = Some(parsed);
    }
    opts.validate().map_err(|e| format!("{e}\n\n{USAGE}"))?;
    if files.is_empty() {
        return Err(format!("no input files\n\n{USAGE}"));
    }
    files.sort();
    let mut sources = Vec::new();
    for f in &files {
        let path = src_root.as_deref().map_or_else(|| PathBuf::from(f), |r| r.join(f));
        let text = fs::read_to_string(&path)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let module = if src_root.is_some() { module_path(f) } else { Vec::new() };
        sources.push(Source { label: f.clone(), text, module });
    }
    let fail = |errors: Vec<anneal_spec_lower::LowerError>| {
        for e in &errors {
            eprint!("{}", e.render(&sources));
        }
        eprintln!("anneal-spec-lower: {} error(s)", errors.len());
        Ok(ExitCode::from(1))
    };
    if matches!(mode, Mode::List) {
        let targets = match list_targets(&sources) {
            Ok(t) => t,
            Err(errors) => return fail(errors),
        };
        let json: Vec<_> = targets
            .iter()
            .map(|t| {
                serde_json::json!({
                    "target": t.target,
                    "claim": t.claim,
                    "file": sources[t.file].label,
                    "kind": if t.external { "external" } else { "inline" },
                })
            })
            .collect();
        let text = serde_json::to_string_pretty(&json).expect("target list serializes");
        println!("{text}");
        return Ok(ExitCode::SUCCESS);
    }
    let lowered = match lower_with(&sources, &opts) {
        Ok(l) => l,
        Err(errors) => return fail(errors),
    };
    match mode {
        Mode::Write(dir) => {
            for (name, bytes) in lowered.outputs() {
                let path = dir.join(name);
                if let Some(parent) = path.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
                }
                write(&path, bytes)?;
            }
            Ok(ExitCode::SUCCESS)
        }
        Mode::Check(dir) => {
            let mut stale = false;
            for (name, bytes) in lowered.outputs() {
                let path = dir.join(name);
                if fs::read_to_string(&path).ok().as_deref() != Some(bytes) {
                    eprintln!(
                        "anneal-spec-lower: {} is stale; regenerate it with --out-dir",
                        path.display()
                    );
                    stale = true;
                }
            }
            Ok(if stale { ExitCode::from(1) } else { ExitCode::SUCCESS })
        }
        Mode::List => unreachable!("handled above"),
    }
}

fn write(path: &Path, bytes: &str) -> Result<(), String> {
    fs::write(path, bytes).map_err(|e| format!("cannot write {}: {e}", path.display()))
}
