// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Declarative corpora runners for `tests/corpora/{adversarial,scalar_specs}`.

use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
};

use anneal_testkit::{
    VerifyReceipt,
    corpora::{
        BlessPatch, CaseExpectationResult, CaseOutcome, DirectiveParser, FailureStage,
        FixtureCase, PrimaryExpectation, StageFailure, apply_bless_patches, evaluate_case,
    },
};

use crate::helpers::{
    corpora_dir, new_workspace, run_parallel, run_verify_strs, sorted_dir_entries,
};

const DUMMY_SPEC_LEAN: &str = "\
-- Copyright 2026 The Fuchsia Authors
-- Licensed under the Apache License v2.0 / MIT / BSD-3-Clause.

prelude
import Trusted.MirSemantics

namespace Spec

def specs : Trusted.MirSemantics.Specs := {}

end Spec
";

const DUMMY_PROOF_LEAN: &str = "\
-- Copyright 2026 The Fuchsia Authors
-- Licensed under the Apache License v2.0 / MIT / BSD-3-Clause.

prelude
import Expected

namespace Proof

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, trivial⟩
  intro _ _ found
  cases found

end Proof
";

fn bless_enabled() -> bool {
    std::env::var_os("ANNEAL_BLESS").as_deref() == Some(OsStr::new("1"))
}

fn keep_sandbox_enabled_from(raw: Option<&OsStr>) -> bool {
    raw.is_some_and(|v| v == "1")
}

fn finish_corpora_workspace<T>(
    staged: anneal_testkit::StagedWorkspace,
    result: T,
) -> T {
    let keep = keep_sandbox_enabled_from(std::env::var_os("ANNEAL_KEEP_SANDBOX").as_deref());
    let diag = std::env::var_os("ANNEAL_TEST_DIAGNOSTICS")
        .filter(|v| !v.is_empty())
        .map(PathBuf::from);
    staged
        .finish_with_options(Ok(result), keep, diag.as_deref())
        .expect("finish corpora workspace")
}

fn fixture_concurrency_from(
    args: &[String],
    jobs_env: Option<&str>,
    env_threads: Option<&str>,
    available: usize,
) -> Result<usize, String> {
    let mut cli_threads = None;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        if let Some(val) = arg.strip_prefix("--test-threads=") {
            if let Ok(n) = val.parse::<usize>()
                && n >= 1
            {
                cli_threads = Some(n);
            }
        } else if arg == "--test-threads"
            && let Some(val) = iter.next()
            && let Ok(n) = val.parse::<usize>()
            && n >= 1
        {
            cli_threads = Some(n);
        }
    }
    let env_threads = env_threads.and_then(|v| v.parse::<usize>().ok()).filter(|&n| n >= 1);
    let libtest_threads = cli_threads.or(env_threads).map(|n| n.clamp(1, 32));
    let jobs = match jobs_env {
        None => None,
        Some(raw) => {
            let parsed = raw
                .parse::<usize>()
                .ok()
                .filter(|n| (1..=32).contains(n))
                .ok_or_else(|| {
                    format!("ANNEAL_TEST_JOBS must be an integer in 1..=32, got {raw:?}")
                })?;
            Some(parsed)
        }
    };
    Ok(match (libtest_threads, jobs) {
        (Some(limit), Some(jobs)) => limit.min(jobs),
        (Some(limit), None) => limit,
        (None, Some(jobs)) => jobs,
        (None, None) => available.clamp(1, 3),
    })
}

fn fixture_concurrency() -> usize {
    let args: Vec<String> = std::env::args().collect();
    let jobs_env = match std::env::var_os("ANNEAL_TEST_JOBS") {
        None => None,
        Some(raw) => match raw.into_string() {
            Ok(s) => Some(s),
            Err(bad) => panic!("ANNEAL_TEST_JOBS must be valid UTF-8, got {bad:?}"),
        },
    };
    let env_threads = std::env::var("RUST_TEST_THREADS").ok();
    let available = thread::available_parallelism().map(std::num::NonZeroUsize::get).unwrap_or(2);
    fixture_concurrency_from(&args, jobs_env.as_deref(), env_threads.as_deref(), available)
        .unwrap_or_else(|err| panic!("{err}"))
}

fn is_root_proof_lean_file(file_name: &str) -> bool {
    let path = Path::new(file_name);
    if path.file_name() != Some(OsStr::new("Proof.lean")) {
        return false;
    }
    matches!(
        path.parent().and_then(|p| p.file_name()).and_then(|s| s.to_str()),
        None | Some("") | Some("target-src") | Some("in")
    )
}

fn is_root_spec_lean_file(file_name: &str) -> bool {
    let path = Path::new(file_name);
    if path.file_name() != Some(OsStr::new("Spec.lean")) {
        return false;
    }
    matches!(
        path.parent().and_then(|p| p.file_name()).and_then(|s| s.to_str()),
        None | Some("") | Some("target-src") | Some("in")
    )
}

/// Extracts `-- === scope: <name> ===` ... `-- === end-scope ===` 1-based
/// inclusive line ranges from a declarative `Proof.lean` file.
fn extract_proof_line_ranges(proof_lean: &str) -> Vec<(usize, usize, String)> {
    let mut ranges = Vec::new();
    let mut active: Option<(usize, String)> = None;
    for (idx, line) in proof_lean.lines().enumerate() {
        let line_no = idx + 1;
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("-- === scope:")
            && let Some(name) = rest.strip_suffix("===")
        {
            active = Some((line_no, name.trim().to_owned()));
        } else if trimmed == "-- === end-scope ==="
            && let Some((start, name)) = active.take()
        {
            ranges.push((start, line_no, name));
        }
    }
    ranges
}

/// Matches Lean JSON error diagnostics emitted on stdout back to the
/// originating root `Proof.lean` line scope, attributing errors outside root
/// `Proof.lean` (or unmapped lines) to `"crate"` scope.
fn parse_proof_failure(
    detail: &str,
    fn_ranges: &[(usize, usize, String)],
) -> (String, String) {
    for line in detail.lines() {
        let Ok(msg) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if msg["severity"].as_str() != Some("error") {
            continue;
        }
        let in_proof_lean = msg["fileName"].as_str().is_some_and(is_root_proof_lean_file);
        if !in_proof_lean {
            continue;
        }
        let diag = msg["data"].as_str().unwrap_or(detail).to_owned();
        if let Some(err_line) = msg["pos"]["line"].as_u64() {
            let err_line = err_line as usize;
            if let Some((_, _, fn_name)) =
                fn_ranges.iter().find(|(start, end, _)| err_line >= *start && err_line <= *end)
            {
                return (fn_name.clone(), diag);
            }
        }
        return ("crate".to_owned(), diag);
    }
    ("crate".to_owned(), detail.to_owned())
}

fn find_spec_lean_error(detail: &str) -> Option<String> {
    for line in detail.lines() {
        let Ok(msg) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if msg["severity"].as_str() == Some("error")
            && msg["fileName"].as_str().is_some_and(is_root_spec_lean_file)
        {
            return Some(msg["data"].as_str().unwrap_or(detail).to_owned());
        }
    }
    None
}

fn format_capture_failure(detail: &str) -> String {
    let Ok(json) = serde_json::from_str::<serde_json::Value>(detail) else {
        return detail.to_owned();
    };
    let mut lines = Vec::new();
    if let Some(items) = json["unsupported"].as_array() {
        for item in items {
            let path = item["path"].as_str().unwrap_or("");
            let reason = item["reason"].as_str().unwrap_or("");
            if !path.is_empty() && !reason.is_empty() {
                lines.push(format!("{path}: {reason}"));
            } else if !reason.is_empty() {
                lines.push(reason.to_owned());
            }
        }
    }
    if let Some(diags) = json["diagnostics"].as_array() {
        for diag in diags {
            if let Some(msg) = diag.as_str() {
                lines.push(msg.to_owned());
            }
        }
    }
    if lines.is_empty() {
        detail.to_owned()
    } else {
        lines.join("\n")
    }
}

fn translate_verify_run(
    run: &anneal_testkit::ExecutedRun<VerifyReceipt>,
    proof_ranges: &[(usize, usize, String)],
    artifacts_dir: Option<&Path>,
) -> CaseExpectationResult {
    let mir_lean = artifacts_dir
        .map(|d| d.join("capture/Captured.lean"))
        .filter(|p| p.is_file())
        .and_then(|p| fs::read_to_string(p).ok());

    match &run.output {
        VerifyReceipt::Verified(_) => CaseExpectationResult::Passed {
            mir_lean,
            output_text: String::from_utf8_lossy(&run.process.stdout).into_owned(),
        },
        VerifyReceipt::Failed(f) => {
            let failure = match f.phase.as_str() {
                "capture" => Some(StageFailure {
                    stage: FailureStage::Capture,
                    diagnostic: format_capture_failure(&f.detail),
                }),
                "preflight" => Some(StageFailure {
                    stage: FailureStage::Preflight,
                    diagnostic: f.detail.clone(),
                }),
                "audit" => {
                    if f.detail.starts_with("policy:") && f.detail.contains("in specification") {
                        Some(StageFailure {
                            stage: FailureStage::Preflight,
                            diagnostic: f.detail.clone(),
                        })
                    } else if let Some(spec_err) = find_spec_lean_error(&f.detail) {
                        Some(StageFailure {
                            stage: FailureStage::Spec,
                            diagnostic: spec_err,
                        })
                    } else {
                        let (scope, msg) = parse_proof_failure(&f.detail, proof_ranges);
                        let stage = if msg.starts_with("policy:") && msg.contains("audit") {
                            FailureStage::Audit
                        } else {
                            FailureStage::Proof { scope }
                        };
                        Some(StageFailure { stage, diagnostic: msg })
                    }
                }
                _ => Some(StageFailure {
                    stage: FailureStage::Audit,
                    diagnostic: f.detail.clone(),
                }),
            };
            CaseExpectationResult::Failed {
                message: format!("{}/{}: {}", f.status, f.phase, f.detail),
                failure,
                mir_lean,
            }
        }
    }
}

fn run_capture_case(case: &FixtureCase) -> CaseExpectationResult {
    let mut builder = new_workspace(&format!("cap-{}", case.name));
    builder
        .write_work_file(
            "Cargo.toml",
            b"[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .expect("write Cargo.toml");
    builder.write_work_file("src/lib.rs", case.source.as_bytes()).expect("write src/lib.rs");
    builder.write_work_file("Spec.lean", DUMMY_SPEC_LEAN.as_bytes()).expect("write Spec.lean");
    builder.write_work_file("Proof.lean", DUMMY_PROOF_LEAN.as_bytes()).expect("write Proof.lean");
    let staged = builder.stage().expect("stage capture workspace");

    let lib_path = staged.work_dir().join("src/lib.rs");
    let spec_arg = format!("Spec={}", staged.work_dir().join("Spec.lean").display());
    let proof_arg = format!("Proof={}", staged.work_dir().join("Proof.lean").display());
    let needs_art = !case.mir_contains.is_empty() || !case.mir_not_contains.is_empty();
    let art_dir = staged.work_dir().join("artifacts");

    let mut args = vec!["rustc".to_owned(), lib_path.display().to_string()];
    args.extend([
        "--crate-name".to_owned(),
        "fixture".to_owned(),
        "--spec-file".to_owned(),
        spec_arg,
        "--proof-file".to_owned(),
        proof_arg,
    ]);
    if needs_art {
        args.push("--artifacts".to_owned());
        args.push(art_dir.display().to_string());
    }
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    let run = run_verify_strs(&staged, &arg_refs);
    let result = translate_verify_run(&run, &[], needs_art.then_some(art_dir.as_path()));
    finish_corpora_workspace(staged, result)
}

fn run_scalar_spec_case(case_dir: &Path, case: &FixtureCase) -> CaseExpectationResult {
    let spec_src = fs::read_to_string(case_dir.join("Spec.lean"))
        .unwrap_or_else(|e| panic!("read {}/Spec.lean: {e}", case_dir.display()));
    let proof_src = fs::read_to_string(case_dir.join("Proof.lean"))
        .unwrap_or_else(|e| panic!("read {}/Proof.lean: {e}", case_dir.display()));
    let proof_ranges = extract_proof_line_ranges(&proof_src);

    let mut builder = new_workspace(&format!("spec-{}", case.name));
    builder.write_work_file("lib.rs", case.source.as_bytes()).expect("write lib.rs");
    builder.write_work_file("Spec.lean", spec_src.as_bytes()).expect("write Spec.lean");
    builder.write_work_file("Proof.lean", proof_src.as_bytes()).expect("write Proof.lean");
    let staged = builder.stage().expect("stage scalar spec workspace");

    let lib_path = staged.work_dir().join("lib.rs");
    let spec_arg = format!("Spec={}", staged.work_dir().join("Spec.lean").display());
    let proof_arg = format!("Proof={}", staged.work_dir().join("Proof.lean").display());
    let needs_art = !case.mir_contains.is_empty() || !case.mir_not_contains.is_empty();
    let art_dir = staged.work_dir().join("artifacts");

    let mut args = vec!["rustc".to_owned(), lib_path.display().to_string()];
    args.extend([
        "--crate-name".to_owned(),
        "fixture".to_owned(),
        "--spec-file".to_owned(),
        spec_arg,
        "--proof-file".to_owned(),
        proof_arg,
    ]);
    if needs_art {
        args.push("--artifacts".to_owned());
        args.push(art_dir.display().to_string());
    }
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    let run = run_verify_strs(&staged, &arg_refs);
    let result =
        translate_verify_run(&run, &proof_ranges, needs_art.then_some(art_dir.as_path()));
    finish_corpora_workspace(staged, result)
}

#[test]
fn verifies_adversarial_capture_corpus() {
    let capture_dir = corpora_dir().join("adversarial/capture");
    let files: Vec<_> = sorted_dir_entries(&capture_dir)
        .into_iter()
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .collect();
    assert!(!files.is_empty(), "expected capture corpus files under {}", capture_dir.display());

    let mut cases = Vec::new();
    for path in &files {
        let content = fs::read_to_string(path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        cases.extend(
            DirectiveParser::parse("adversarial/capture", path, &content)
                .unwrap_or_else(|e| panic!("parse {}: {e}", path.display())),
        );
    }

    let bless = bless_enabled();
    let results = run_parallel(cases.clone(), fixture_concurrency(), |c| run_capture_case(&c));
    let mut patches: Vec<BlessPatch> = Vec::new();
    let mut failures = Vec::new();
    for (case, res) in cases.iter().zip(results.iter()) {
        match evaluate_case(case, res, bless) {
            CaseOutcome::Passed => {}
            CaseOutcome::Blessed(patch) => patches.push(patch),
            CaseOutcome::Failed(err) => failures.push(format!("{}: {err}", case.name)),
        }
    }
    if bless && !patches.is_empty() {
        apply_bless_patches(&patches).expect("apply bless patches");
    }
    assert!(
        failures.is_empty(),
        "capture corpus failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn verifies_scalar_spec_corpus() {
    let specs_dir = corpora_dir().join("scalar_specs");
    let case_dirs: Vec<_> =
        sorted_dir_entries(&specs_dir).into_iter().filter(|p| p.is_dir()).collect();
    assert!(!case_dirs.is_empty(), "expected scalar spec directories under {}", specs_dir.display());

    let mut cases = Vec::new();
    for dir in &case_dirs {
        let lib_path = dir.join("lib.rs");
        let content = fs::read_to_string(&lib_path)
            .unwrap_or_else(|e| panic!("read {}: {e}", lib_path.display()));
        let mut parsed = DirectiveParser::parse("scalar_specs", &lib_path, &content)
            .unwrap_or_else(|e| panic!("parse {}: {e}", lib_path.display()));
        assert_eq!(
            parsed.len(),
            1,
            "expected exactly 1 case in {}",
            lib_path.display()
        );
        cases.push((dir.clone(), parsed.remove(0)));
    }

    let bless = bless_enabled();
    let results = run_parallel(cases.clone(), fixture_concurrency(), |(dir, c)| {
        run_scalar_spec_case(&dir, &c)
    });
    let mut patches: Vec<BlessPatch> = Vec::new();
    let mut failures = Vec::new();
    for ((_, case), res) in cases.iter().zip(results.iter()) {
        match evaluate_case(case, res, bless) {
            CaseOutcome::Passed => {}
            CaseOutcome::Blessed(patch) => patches.push(patch),
            CaseOutcome::Failed(err) => failures.push(format!("{}: {err}", case.name)),
        }
    }
    if bless && !patches.is_empty() {
        apply_bless_patches(&patches).expect("apply bless patches");
    }
    assert!(
        failures.is_empty(),
        "scalar spec corpus failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn rejects_malformed_fixture_directives() {
    let bad_inputs = [
        ("missing_expectation", "// === case: a ===\npub fn f() {}\n"),
        ("empty_fail_msg", "// === case: a ===\n//@ fail(capture): \"\"\npub fn f() {}\n"),
        (
            "unknown_stage",
            "// === case: a ===\n//@ fail(bogus): \"err\"\npub fn f() {}\n",
        ),
        (
            "duplicate_primary",
            "// === case: a ===\n//@ pass\n//@ fail(capture): \"err\"\npub fn f() {}\n",
        ),
        (
            "missing_issue",
            "// === case: a ===\n//@ known-bug(capture): \"err\"\npub fn f() {}\n",
        ),
    ];
    for (label, text) in bad_inputs {
        let err = DirectiveParser::parse("test", Path::new("bad.rs"), text)
            .expect_err(&format!("expected directive rejection for {label}"));
        let _ = err;
    }
}

#[test]
fn bless_updates_expectation_and_promotes_resolved_known_bug_without_flipping_polarity() {
    let dir = tempfile::tempdir().expect("tempdir");
    let file_path = dir.path().join("sample.rs");
    let content = "\
// === case: bug_fixed ===
//@ known_bug(#123, capture): \"old failure\"
pub fn f() {}
";
    fs::write(&file_path, content).unwrap();
    let cases = DirectiveParser::parse("test", &file_path, content).unwrap();
    let passed = CaseExpectationResult::Passed {
        mir_lean: None,
        output_text: String::new(),
    };
    let CaseOutcome::Blessed(patch) = evaluate_case(&cases[0], &passed, true) else {
        panic!("expected known-bug resolution to produce bless patch");
    };
    apply_bless_patches(&[patch]).unwrap();
    let updated = fs::read_to_string(&file_path).unwrap();
    assert!(updated.contains("//@ pass"), "expected promoted pass directive:\n{updated}");

    // Polarity lock: fail(...) must never be blessed into pass.
    let fail_content = "// === case: strict ===\n//@ fail(capture): \"x\"\npub fn f() {}\n";
    let fail_cases = DirectiveParser::parse("test", Path::new("strict.rs"), fail_content).unwrap();
    assert!(matches!(
        evaluate_case(&fail_cases[0], &passed, true),
        CaseOutcome::Failed(_)
    ));
}

#[test]
fn bless_does_not_promote_known_bug_with_failing_mir_assertion() {
    let content = "\
// === case: mir_check ===
//@ known_bug(#456, proof, f): \"err\"
//@ mir-contains: \"ExpectedToken\"
pub fn f() {}
";
    let cases = DirectiveParser::parse("test", Path::new("mir.rs"), content).unwrap();
    let passed_missing_mir = CaseExpectationResult::Passed {
        mir_lean: Some("def body_0 := ()".to_owned()),
        output_text: String::new(),
    };
    assert!(matches!(
        evaluate_case(&cases[0], &passed_missing_mir, true),
        CaseOutcome::Failed(_)
    ));
}

#[test]
fn single_case_fixture_preserves_leading_doc_comments() {
    let content = "\
// Copyright 2026 The Fuchsia Authors
//
//@ pass
//@ mir-contains: \"isize\"

/// Ordinary doc comment preserved.
#![no_std]
pub fn id(x: usize) -> usize { x }
";
    let cases = DirectiveParser::parse("scalar_specs", Path::new("doc_case.rs"), content).unwrap();
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0].name, "default");
    assert!(matches!(cases[0].expectation, PrimaryExpectation::Pass));
    assert!(cases[0].source.contains("/// Ordinary doc comment preserved."));
    assert!(cases[0].source.contains("#![no_std]"));
}

#[test]
fn parse_proof_failure_matches_diagnostic_file_before_line_attribution() {
    let fn_ranges = vec![(10usize, 30usize, "alpha".to_owned())];
    for other_file in [
        "/tmp/anneal-trusted-abc/target-src/Spec.lean",
        "/tmp/anneal-trusted-abc/target-src/Sub/Proof.lean",
    ] {
        let diag = serde_json::json!({
            "fileName": other_file,
            "severity": "error",
            "pos": { "line": 15, "column": 4 },
            "data": "other file error"
        });
        let (scope, _msg) = parse_proof_failure(&diag.to_string(), &fn_ranges);
        assert_eq!(scope, "crate", "expected crate scope for {other_file}");
    }

    let combined = format!(
        "{}\n{}",
        serde_json::json!({
            "fileName": "/tmp/anneal-trusted-abc/target-src/Spec.lean",
            "severity": "error",
            "pos": { "line": 15, "column": 4 },
            "data": "spec warning-or-error"
        }),
        serde_json::json!({
            "fileName": "/tmp/anneal-trusted-abc/target-src/Proof.lean",
            "severity": "error",
            "pos": { "line": 20, "column": 4 },
            "data": "proof type mismatch"
        })
    );
    let (scope, msg) = parse_proof_failure(&combined, &fn_ranges);
    assert_eq!(scope, "alpha");
    assert_eq!(msg, "proof type mismatch");
}

#[test]
fn fixture_concurrency_honors_jobs_cli_and_env() {
    let s = |xs: &[&str]| xs.iter().map(|v| (*v).to_owned()).collect::<Vec<_>>();
    // `ANNEAL_TEST_JOBS` caps concurrency downward without overriding an
    // explicit `--test-threads` or `RUST_TEST_THREADS` limit upward.
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=1"]), Some("4"), Some("2"), 16),
        Ok(1)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads", "2"]), Some("8"), Some("1"), 16),
        Ok(2)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=8"]), Some("2"), None, 16),
        Ok(2)
    );
    assert_eq!(fixture_concurrency_from(&s(&["bin", "--test-threads=64"]), None, None, 16), Ok(32));
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=64"]), Some("4"), None, 16),
        Ok(4)
    );
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), Some("4"), Some("1"), 16), Ok(1));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), Some("2"), Some("8"), 16), Ok(2));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, Some("8"), 16), Ok(8));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, Some("64"), 16), Ok(32));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), Some("8"), None, 16), Ok(8));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, Some("1"), 16), Ok(1));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, None, 16), Ok(3));
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, None, 1), Ok(1));
    for invalid in ["", "0", "33", "64", "abc"] {
        let err = fixture_concurrency_from(&s(&["bin"]), Some(invalid), Some("2"), 16)
            .expect_err(&format!("expected invalid ANNEAL_TEST_JOBS={invalid:?} to fail"));
        assert!(
            err.contains("ANNEAL_TEST_JOBS must be an integer in 1..=32"),
            "unexpected error for {invalid:?}: {err}"
        );
    }

    // `run_parallel` enforces the configured worker cap across items.
    let active = AtomicUsize::new(0);
    let peak = AtomicUsize::new(0);
    run_parallel((0..8).collect(), 2, |_| {
        let cur = active.fetch_add(1, Ordering::SeqCst) + 1;
        peak.fetch_max(cur, Ordering::SeqCst);
        thread::yield_now();
        active.fetch_sub(1, Ordering::SeqCst);
    });
    assert_eq!(active.load(Ordering::SeqCst), 0);
    assert!(peak.load(Ordering::SeqCst) <= 2, "run_parallel exceeded cap 2");
}

#[test]
fn keep_sandbox_honors_exact_one_value() {
    assert!(!keep_sandbox_enabled_from(None));
    for disabled in ["", "0", "false", "FALSE", "true", "yes", "2"] {
        assert!(
            !keep_sandbox_enabled_from(Some(OsStr::new(disabled))),
            "expected ANNEAL_KEEP_SANDBOX={disabled:?} not to retain sandbox"
        );
    }
    assert!(keep_sandbox_enabled_from(Some(OsStr::new("1"))));

    // Verify `StagedWorkspace::finish_with_options` deletes when `keep = false`
    // and retains on disk when `keep = true`.
    let dropped_staged = new_workspace("keep-false-").stage().unwrap();
    let dropped_root = dropped_staged.root_dir().to_path_buf();
    assert!(dropped_root.exists());
    dropped_staged.finish_with_options(Ok(()), false, None).unwrap();
    assert!(
        !dropped_root.exists(),
        "workspace must be removed when keep_sandbox = false: {}",
        dropped_root.display()
    );

    let kept_staged = new_workspace("keep-true-").stage().unwrap();
    let kept_root = kept_staged.root_dir().to_path_buf();
    kept_staged.finish_with_options(Ok(()), true, None).unwrap();
    let still_exists = kept_root.exists();
    let _ = fs::remove_dir_all(&kept_root);
    assert!(
        still_exists,
        "workspace must be retained on disk when keep_sandbox = true: {}",
        kept_root.display()
    );
}
