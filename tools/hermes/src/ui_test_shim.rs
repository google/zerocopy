use std::{env, path::PathBuf, process::exit};

use miette::Diagnostic as _;
use serde::Serialize;

use crate::{errors::HermesError, parse};

/// The entrypoint for running under the `ui_test` crate, which expects us to be
/// `rustc`. This is a bit of a hack, but it works.
pub fn run() {
    let args: Vec<String> = env::args().collect();

    // Spoof version if requested
    if args.contains(&"-vV".to_string()) || args.contains(&"--version".to_string()) {
        println!("rustc 1.93.0-nightly (hermes-shim)");
        println!("binary: rustc");
        println!("commit-hash: 0000000000000000000000000000000000000000");
        println!("commit-date: 2025-01-01");
        println!("host: x86_64-unknown-linux-gnu");
        println!("release: 1.93.0-nightly");
        exit(0);
    }

    // Find the file (ignoring rustc flags like --out-dir)
    let file_path = args
        .iter()
        .skip(1)
        .find(|arg| arg.ends_with(".rs") && !arg.starts_with("--"))
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            // If no file found, maybe it's just a flag check. Exit successfully
            // to appease ui_test.
            exit(0);
        });

    // Run logic with JSON emitter
    let mut has_errors = false;

    parse::read_file_and_visit_hermes_items(&file_path, |source, res| {
        if let Err(e) = res {
            has_errors = true;
            emit_rustc_json(&e, &source, file_path.to_str().unwrap());
        }
    })
    .unwrap();

    if has_errors {
        exit(1);
    }
}

#[derive(Serialize)]
struct RustcDiagnostic {
    message: String,
    level: String,
    spans: Vec<RustcSpan>,
    children: Vec<RustcDiagnostic>,
    rendered: String,
}

#[derive(Serialize)]
struct RustcSpan {
    file_name: String,
    byte_start: usize,
    byte_end: usize,
    line_start: usize,
    line_end: usize,
    column_start: usize,
    column_end: usize,
    is_primary: bool,
    text: Vec<RustcSpanLine>, // ui_test sometimes checks the snippet context
}

#[derive(Serialize)]
struct RustcSpanLine {
    text: String,
    highlight_start: usize,
    highlight_end: usize,
}

pub fn emit_rustc_json(e: &HermesError, source: &str, file: &str) {
    let msg = e.to_string();
    // Use miette's span to get byte offsets.
    let span = e.labels().and_then(|mut l| l.next());

    let mut spans = Vec::new();
    if let Some(labeled_span) = span {
        let offset = labeled_span.offset();
        let len = labeled_span.len();

        // Calculate lines/cols manually (miette makes this hard to extract
        // without a Report). This is isolated here now, so it's fine.
        let prefix = &source[..offset];
        let line_start = prefix.lines().count().max(1);
        let last_nl = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
        let column_start = (offset - last_nl) + 1;

        // Grab the line text for the snippet
        let line_end_idx = source[offset..].find('\n').map(|i| offset + i).unwrap_or(source.len());
        let line_text = source[last_nl..line_end_idx].to_string();

        spans.push(RustcSpan {
            file_name: file.to_string(),
            byte_start: offset,
            byte_end: offset + len,
            line_start,
            line_end: line_start, // Assuming single line for simplicity
            column_start,
            column_end: column_start + len,
            is_primary: true,
            text: vec![RustcSpanLine {
                text: line_text,
                highlight_start: column_start,
                highlight_end: column_start + len,
            }],
        });
    }

    let diag = RustcDiagnostic {
        message: msg.clone(),
        level: "error".to_string(),
        spans,
        children: vec![],
        rendered: format!("error: {}\n", msg),
    };

    eprintln!("{}", serde_json::to_string(&diag).unwrap());
}
