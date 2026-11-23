// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-spec-lower`: writes or checks `Spec.lean` and `spec_span_map.json`.

use std::{
    fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use anneal_spec_lower::{lower, module_path, Source};

const USAGE: &str = "\
usage: anneal-spec-lower [--src-root DIR] (--out-dir DIR | --check DIR) FILE...

Lowers the `anneal::spec` items and `anneal::external_spec!` blocks in FILE...
to one specification unit.

  --src-root DIR  Resolve FILE relative to DIR and derive each file's module
                  path from its location (`a/b.rs` is `a::b`). Without it,
                  FILE paths are used as given and inline items belong to the
                  crate root.
  --out-dir DIR   Write DIR/Spec.lean and DIR/spec_span_map.json.
  --check DIR     Exit 1 unless DIR/Spec.lean and DIR/spec_span_map.json
                  already match the lowering byte for byte.

Exit status: 0 on success, 1 on specification errors or a failed --check,
2 on usage or I/O errors.";

enum Mode {
    Write(PathBuf),
    Check(PathBuf),
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
            "--out-dir" => mode = Some(Mode::Write(value("--out-dir")?.into())),
            "--check" => mode = Some(Mode::Check(value("--check")?.into())),
            f if f.starts_with('-') => return Err(format!("unknown option `{f}`\n\n{USAGE}")),
            f => files.push(f.to_string()),
        }
    }
    let mode = mode.ok_or_else(|| format!("one of --out-dir or --check is required\n\n{USAGE}"))?;
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
    let lowered = match lower(&sources) {
        Ok(l) => l,
        Err(errors) => {
            for e in &errors {
                eprint!("{}", e.render(&sources));
            }
            eprintln!("anneal-spec-lower: {} error(s)", errors.len());
            return Ok(ExitCode::from(1));
        }
    };
    let outputs = [("Spec.lean", &lowered.spec_lean), ("spec_span_map.json", &lowered.span_map)];
    match mode {
        Mode::Write(dir) => {
            fs::create_dir_all(&dir)
                .map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
            for (name, bytes) in outputs {
                write(&dir.join(name), bytes)?;
            }
            Ok(ExitCode::SUCCESS)
        }
        Mode::Check(dir) => {
            let mut stale = false;
            for (name, bytes) in outputs {
                let path = dir.join(name);
                if fs::read_to_string(&path).ok().as_deref() != Some(bytes.as_str()) {
                    eprintln!(
                        "anneal-spec-lower: {} is stale; regenerate it with --out-dir",
                        path.display()
                    );
                    stale = true;
                }
            }
            Ok(if stale { ExitCode::from(1) } else { ExitCode::SUCCESS })
        }
    }
}

fn write(path: &Path, bytes: &str) -> Result<(), String> {
    fs::write(path, bytes).map_err(|e| format!("cannot write {}: {e}", path.display()))
}
