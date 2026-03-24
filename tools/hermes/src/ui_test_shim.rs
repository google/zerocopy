use std::{env, path::PathBuf, process::exit};

use miette::Diagnostic as _;
use serde::Serialize;

use crate::{errors::HermesError, parse};

/// The entrypoint for running under the `ui_test` crate.
///
/// `ui_test` expects us to behave like `rustc`:
/// - Accept flags (we mostly ignore them).
/// - Accept a single input file.
/// - Emit JSON diagnostics to stderr.
pub fn run() {
    let args: Vec<String> = env::args().collect();

    // Spoof version if requested
    if args.iter().any(|a| matches!(a.as_str(), "-vV" | "--version")) {
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

    // Ignore the returned source and module list; we only care about errors.
    let _ = parse::read_file_and_scan_compilation_unit(&file_path, false, |source, res| {
        if let Err(e) = res {
            has_errors = true;
            emit_rustc_json(&e, source, file_path.to_str().unwrap());
        }
    });

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
    text: Vec<RustcSpanLine>,
}

#[derive(Serialize)]
struct RustcSpanLine {
    text: String,
    highlight_start: usize,
    highlight_end: usize,
}

fn emit_rustc_json(e: &HermesError, source: &str, file: &str) {
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
        let line_idx = prefix.lines().count().max(1) - 1; // 0-indexed
        let line_start = line_idx + 1; // 1-indexed for rustc

        let line_start_offset = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
        let column_start = (offset - line_start_offset) + 1;

        // Extract the full line text for context
        let line_end_offset =
            source[offset..].find('\n').map(|i| offset + i).unwrap_or(source.len());
        let line_text = source[line_start_offset..line_end_offset].to_string();

        spans.push(RustcSpan {
            file_name: file.to_string(),
            byte_start: offset,
            byte_end: offset + len,
            line_start,
            line_end: line_start, // Assuming single-line span for simplicity
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
