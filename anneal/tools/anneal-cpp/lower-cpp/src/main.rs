// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::process::ExitCode;

use anneal_lower_common::digest;
use anneal_lower_cpp::{lower_bundle_json_to_lean, EmitOptions};

const USAGE: &str =
    "usage: anneal-lower-cpp [--entry SYMBOL] [--namespace NS] [-o OUT.lean] BUNDLE.json

Lowers a RawCppBundle (schema v1) to a Lean file defining
`<NS>.program : Trusted.CppAst.CppProgram` (default NS: CapturedCpp).
Exit status: 0 on success, 1 on usage/IO errors, 2 if lowering is refused.";

fn main() -> ExitCode {
    let mut opts = EmitOptions::default();
    let mut input = None;
    let mut output = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut value = |name: &str| match args.next() {
            Some(v) => Ok(v),
            None => Err(format!("missing value for {name}")),
        };
        let r = match a.as_str() {
            "--entry" => value("--entry").map(|v| opts.lower.entry = Some(v)),
            "--namespace" => value("--namespace").map(|v| opts.namespace = v),
            "-o" | "--output" => value("-o").map(|v| output = Some(v)),
            "-h" | "--help" => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            _ if input.is_none() && !a.starts_with('-') => {
                input = Some(a);
                Ok(())
            }
            _ => Err(format!("unexpected argument `{a}`")),
        };
        if let Err(e) = r {
            eprintln!("anneal-lower-cpp: {e}\n{USAGE}");
            return ExitCode::from(1);
        }
    }
    let Some(input) = input else {
        eprintln!("{USAGE}");
        return ExitCode::from(1);
    };
    let text = match std::fs::read_to_string(&input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("anneal-lower-cpp: cannot read {input}: {e}");
            return ExitCode::from(1);
        }
    };
    let lean = match lower_bundle_json_to_lean(&text, &opts) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("anneal-lower-cpp: error: {e}");
            return ExitCode::from(2);
        }
    };
    match output {
        None => print!("{lean}"),
        Some(path) => {
            // Publish a `sha256sum`-compatible digest next to the output so
            // downstream consumers can pin the exact subject they verified.
            let file_name = std::path::Path::new(&path)
                .file_name()
                .map_or_else(|| path.clone(), |n| n.to_string_lossy().into_owned());
            let digest_path = format!("{path}.sha256");
            let digest = digest::sha256sum_line(lean.as_bytes(), &file_name);
            for (p, contents) in [(&path, lean.as_str()), (&digest_path, digest.as_str())] {
                if let Err(e) = std::fs::write(p, contents) {
                    eprintln!("anneal-lower-cpp: cannot write {p}: {e}");
                    return ExitCode::from(1);
                }
            }
        }
    }
    ExitCode::SUCCESS
}
