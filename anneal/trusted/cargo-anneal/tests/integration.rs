// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Declarative integration test suite and host-boundary security tests for
//! `cargo-anneal verify` over `Trusted.MirAst`, `Trusted.MirSemantics`, and
//! `Anneal.MirWp`.
//!
//! Fixture corpus files live under `tests/fixtures/*.rs` (top-level `.rs`
//! files). Each file contains one or more `// === case: <name> ===` sections
//! with `//@ ...` expectation directives:
//!
//! - `//@ pass`
//! - `//@ fail(capture): "<expected substring>"`
//! - `//@ fail(spec): "<expected substring>"`
//! - `//@ fail(proof, <fn_name_or_crate>): "<expected substring>"`
//! - `//@ known_bug(#<issue>, capture): "<expected substring>"`
//! - `//@ known_bug(#<issue>, spec): "<expected substring>"`
//! - `//@ known_bug(#<issue>, proof, <fn_name_or_crate>): "<expected>"`
//! - `//@ mir-contains: "<substring in Captured.lean>"`
//! - `//@ mir-not-contains: "<substring in Captured.lean>"`
//!
//! Stage semantics:
//! - `capture` asserts a rejection from `cargo-anneal` / `rustc-capture`
//!   during request, input, Cargo, or MIR capture.
//! - `spec` asserts a rejection from this harness's own `/// anneal:*`
//!   comment parser and `Spec.lean` synthesizer (surfaced only after real
//!   MIR capture succeeds); `cargo-anneal` itself never parses Rust doc
//!   comments.
//! - `proof` asserts a Lean compilation or audit rejection from
//!   `cargo-anneal` (`status=proof_failed`, `phase=audit`), attributed to a
//!   function name when a diagnostic lies in `Proof.lean`'s range for that
//!   function, or `crate` otherwise.
//!
//! Environment controls:
//! - `ANNEAL_TEST_FILTER=<substr>`: run only cases whose `<stem>::<case>`
//!   matches `<substr>`.
//! - `ANNEAL_TEST_JOBS=<n>`: strict integer (`1..=32`) process-wide cap on
//!   concurrent `cargo-anneal` verification invocations. Libtest's thread
//!   limit (`--test-threads`, else `RUST_TEST_THREADS`) is clamped to `1..=32`
//!   and, when both are set, combined via `min(libtest_threads, jobs)` so
//!   `ANNEAL_TEST_JOBS` never exceeds an explicit libtest thread limit. When
//!   neither is set, defaults to `min(available_parallelism, 3)`.
//! - `ANNEAL_BLESS=1`: update failed diagnostic substrings/scopes in place and
//!   promote resolved `known_bug` cases to `//@ pass`, without ever flipping
//!   pass/fail polarity.
//! - `ANNEAL_KEEP_SANDBOX=1`: retain temporary crate/proof/artifact sandboxes.

use serde_json::Value;
use std::collections::BTreeMap;
use std::env;
use std::ffi::OsStr;
use std::fmt::Write as _;
use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread;
use tempfile::TempDir;

// ---------------------------------------------------------------------------
// Tool discovery
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct Tools {
    cli: PathBuf,
    capture: PathBuf,
    lean: PathBuf,
    sysroot: PathBuf,
}

// Keep in sync with `Tools::discover` in `tests/mvp_e2e.rs`.
impl Tools {
    fn discover() -> Self {
        let install_root = override_path("ANNEAL_TEST_INSTALL_ROOT");
        // Prefer explicit `ANNEAL_CLI` / `ANNEAL_MVP_CLI` overrides, then the
        // freshly built test binary (`CARGO_BIN_EXE_cargo-anneal`). Never
        // read `ANNEAL_TEST_CARGO_ANNEAL` here so CI's installed-smoke
        // variable does not silently switch workspace tests off the build.
        let cli = first_override(&["ANNEAL_CLI", "ANNEAL_MVP_CLI"])
            .unwrap_or_else(|| PathBuf::from(env!("CARGO_BIN_EXE_cargo-anneal")));
        let cli = required_file(cli, "cargo-anneal", "ANNEAL_CLI");
        // Prefer explicit `ANNEAL_CAPTURE` / `ANNEAL_MVP_CAPTURE` overrides,
        // then the freshly built sibling beside `cli`, then an explicit
        // `ANNEAL_TEST_INSTALL_ROOT` bundle (never a user-global install).
        let capture = first_override(&["ANNEAL_CAPTURE", "ANNEAL_MVP_CAPTURE"])
            .or_else(|| {
                let sibling = cli.with_file_name("anneal-rustc-capture");
                sibling.is_file().then_some(sibling)
            })
            .or_else(|| {
                install_root
                    .as_ref()
                    .map(|root| root.join("bin/anneal-rustc-capture"))
            })
            .unwrap_or_else(|| cli.with_file_name("anneal-rustc-capture"));
        let capture = required_file(
            capture,
            "anneal-rustc-capture; build it before running this test",
            "ANNEAL_CAPTURE",
        );
        let lean = first_override(&["ANNEAL_LEAN", "ANNEAL_MVP_LEAN"])
            .or_else(|| install_root.as_ref().map(|root| root.join("lean/bin/lean")))
            .unwrap_or_else(cargo_anneal::default_lean_path);
        let lean = required_file(lean, "the pinned Lean executable", "ANNEAL_LEAN");
        let sysroot = first_override(&[
            "ANNEAL_SYSROOT",
            "ANNEAL_TEST_RUST_SYSROOT",
            "ANNEAL_MVP_SYSROOT",
        ])
        .or_else(|| install_root.as_ref().map(|root| root.join("rust")))
        .unwrap_or_else(|| {
            let output = Command::new("rustup")
                .args(["run", "nightly-2026-05-31", "rustc", "--print", "sysroot"])
                .output()
                .expect("install the pinned compiler or set ANNEAL_SYSROOT");
            assert!(
                output.status.success(),
                "cannot find the pinned compiler sysroot; set ANNEAL_SYSROOT:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            PathBuf::from(
                String::from_utf8(output.stdout)
                    .expect("rustc sysroot must be UTF-8")
                    .trim(),
            )
        });
        assert!(
            sysroot.join("lib").is_dir(),
            "missing compiler sysroot {}; set ANNEAL_SYSROOT",
            sysroot.display()
        );
        let sysroot = fs::canonicalize(sysroot).expect("resolve test sysroot path");
        Self {
            cli,
            capture,
            lean,
            sysroot,
        }
    }

    fn command(&self) -> Command {
        let mut command = Command::new(&self.cli);
        command
            .arg("verify")
            .arg("--capture")
            .arg(&self.capture)
            .arg("--lean")
            .arg(&self.lean)
            .arg("--sysroot")
            .arg(&self.sysroot);
        command
    }

    fn run_command(&self, mut command: Command) -> std::io::Result<Output> {
        let _permit = acquire_job_permit();
        command.output()
    }
}

fn override_path(var: &str) -> Option<PathBuf> {
    env::var_os(var)
        .filter(|v| !v.is_empty())
        .map(PathBuf::from)
}

fn first_override(names: &[&str]) -> Option<PathBuf> {
    names.iter().copied().find_map(override_path)
}

fn required_file(path: PathBuf, label: &str, var: &str) -> PathBuf {
    assert!(
        path.is_file(),
        "cannot find {label} at {}; set {var}",
        path.display()
    );
    fs::canonicalize(path).expect("resolve test tool path")
}

// ---------------------------------------------------------------------------
// Declarative fixture directive AST & fail-closed parser
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum FailureStage {
    Capture,
    Spec,
    Proof { scope: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StageFailure {
    stage: FailureStage,
    diagnostic: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PrimaryExpectation {
    Pass,
    Fail {
        stage: FailureStage,
        substring: String,
    },
    KnownBug {
        issue: u32,
        stage: FailureStage,
        substring: String,
    },
}

#[derive(Debug, Clone)]
struct FixtureCase {
    suite: String,
    name: String,
    file_path: PathBuf,
    primary_line_idx: usize,
    expectation: PrimaryExpectation,
    mir_contains: Vec<String>,
    mir_not_contains: Vec<String>,
    source: String,
}

impl FixtureCase {
    fn full_name(&self) -> String {
        format!("{}::{}", self.suite, self.name)
    }
}

fn parse_quoted_non_empty(raw: &str, ctx: &str) -> Result<String, String> {
    let trimmed = raw.trim();
    let val: String = serde_json::from_str(trimmed)
        .map_err(|_| format!("{ctx}: expected non-empty string literal, got {trimmed:?}"))?;
    if val.is_empty() {
        return Err(format!("{ctx}: expected non-empty string literal"));
    }
    Ok(val)
}

fn parse_stage_args(args: &[&str], ctx: &str) -> Result<FailureStage, String> {
    match args {
        ["capture"] => Ok(FailureStage::Capture),
        ["capture", ..] => Err(format!("{ctx}: `capture` stage does not take a scope")),
        ["spec"] => Ok(FailureStage::Spec),
        ["spec", ..] => Err(format!("{ctx}: `spec` stage does not take a scope")),
        ["proof"] => Err(format!(
            "{ctx}: `proof` stage requires a scope (`proof, <fn_or_crate>`)"
        )),
        ["proof", scope] => {
            let scope = scope.trim();
            if scope.is_empty() || !scope.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err(format!("{ctx}: invalid proof scope {scope:?}"));
            }
            Ok(FailureStage::Proof {
                scope: scope.to_owned(),
            })
        }
        _ => Err(format!("{ctx}: unrecognized stage specification {args:?}")),
    }
}

fn parse_fixture_file(
    suite: &str,
    file_path: &Path,
    content: &str,
) -> Result<Vec<FixtureCase>, String> {
    let lines: Vec<&str> = content.lines().collect();
    let mut sections: Vec<(String, usize, usize)> = Vec::new();
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("// === case:") {
            let name = rest
                .strip_suffix("===")
                .ok_or_else(|| {
                    format!(
                        "{}:{}: malformed `// === case: <name> ===` header",
                        file_path.display(),
                        idx + 1
                    )
                })?
                .trim();
            if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                return Err(format!(
                    "{}:{}: invalid case name {name:?}",
                    file_path.display(),
                    idx + 1
                ));
            }
            if let Some(last) = sections.last_mut() {
                last.2 = idx;
            }
            sections.push((name.to_owned(), idx + 1, lines.len()));
        }
    }
    if let Some((_, first_case_start, _)) = sections.first() {
        let first_header_idx = first_case_start.saturating_sub(1);
        for (idx, line) in lines[..first_header_idx].iter().enumerate() {
            if line.trim().starts_with("//@") {
                return Err(format!(
                    "{}:{}: `//@` directive appears before the first `// === case: ... ===` header",
                    file_path.display(),
                    idx + 1
                ));
            }
        }
    } else {
        sections.push(("default".to_owned(), 0, lines.len()));
    }

    let mut cases = Vec::with_capacity(sections.len());
    for (name, start, end) in sections {
        let mut primary: Option<(usize, PrimaryExpectation)> = None;
        let mut mir_contains = Vec::new();
        let mut mir_not_contains = Vec::new();
        let mut source_lines = Vec::new();

        for (offset, &line) in lines[start..end].iter().enumerate() {
            let line_idx = start + offset;
            let loc = format!(
                "{}:{}: ({suite}::{name})",
                file_path.display(),
                line_idx + 1
            );
            let trimmed = line.trim();
            if let Some(directive) = trimmed.strip_prefix("//@") {
                let directive = directive.trim();
                let parsed_primary = if directive == "pass" {
                    Some(PrimaryExpectation::Pass)
                } else if let Some(rest) = directive.strip_prefix("fail(") {
                    let (inside, after) = rest
                        .split_once("):")
                        .ok_or_else(|| format!("{loc}: malformed `fail(...)` directive"))?;
                    let parts: Vec<&str> = inside.split(',').map(str::trim).collect();
                    let stage = parse_stage_args(&parts, &loc)?;
                    let substring = parse_quoted_non_empty(after, &loc)?;
                    Some(PrimaryExpectation::Fail { stage, substring })
                } else if let Some(rest) = directive.strip_prefix("known_bug(") {
                    let (inside, after) = rest
                        .split_once("):")
                        .ok_or_else(|| format!("{loc}: malformed `known_bug(...)` directive"))?;
                    let parts: Vec<&str> = inside.split(',').map(str::trim).collect();
                    if parts.len() < 2 {
                        return Err(format!("{loc}: `known_bug` requires `(#<issue>, <stage>)`"));
                    }
                    let issue_raw = parts[0]
                        .strip_prefix('#')
                        .ok_or_else(|| format!("{loc}: invalid issue reference {:?}", parts[0]))?;
                    let issue: u32 = issue_raw
                        .parse()
                        .map_err(|_| format!("{loc}: invalid issue reference {:?}", parts[0]))?;
                    if issue == 0 {
                        return Err(format!("{loc}: invalid issue reference {:?}", parts[0]));
                    }
                    let stage = parse_stage_args(&parts[1..], &loc)?;
                    let substring = parse_quoted_non_empty(after, &loc)?;
                    Some(PrimaryExpectation::KnownBug {
                        issue,
                        stage,
                        substring,
                    })
                } else if let Some(after) = directive.strip_prefix("mir-contains:") {
                    mir_contains.push(parse_quoted_non_empty(after, &loc)?);
                    None
                } else if let Some(after) = directive.strip_prefix("mir-not-contains:") {
                    mir_not_contains.push(parse_quoted_non_empty(after, &loc)?);
                    None
                } else {
                    return Err(format!("{loc}: unknown directive `//@ {directive}`"));
                };

                if let Some(exp) = parsed_primary {
                    if primary.is_some() {
                        return Err(format!(
                            "{loc}: multiple primary expectation directives in one case"
                        ));
                    }
                    primary = Some((line_idx, exp));
                }
            } else {
                source_lines.push(line);
            }
        }

        let (primary_line_idx, expectation) = primary.ok_or_else(|| {
            format!(
                "{}:{}: ({suite}::{name}): missing primary expectation directive",
                file_path.display(),
                start + 1
            )
        })?;

        if matches!(
            expectation,
            PrimaryExpectation::Fail {
                stage: FailureStage::Capture,
                ..
            } | PrimaryExpectation::KnownBug {
                stage: FailureStage::Capture,
                ..
            }
        ) && (!mir_contains.is_empty() || !mir_not_contains.is_empty())
        {
            return Err(format!(
                "{}:{}: ({suite}::{name}): `mir-contains` / `mir-not-contains` cannot be used on `capture`-stage failures",
                file_path.display(),
                primary_line_idx + 1
            ));
        }

        let mut source = source_lines.join("\n");
        source.push('\n');
        cases.push(FixtureCase {
            suite: suite.to_owned(),
            name,
            file_path: file_path.to_path_buf(),
            primary_line_idx,
            expectation,
            mir_contains,
            mir_not_contains,
            source,
        });
    }
    Ok(cases)
}

// ---------------------------------------------------------------------------
// Bless support (polarity-safe)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
struct BlessPatch {
    file_path: PathBuf,
    line_idx: usize,
    replacement: String,
}

#[derive(Debug)]
enum CaseOutcome {
    Passed,
    Blessed(BlessPatch),
    Failed(String),
}

#[derive(Debug, Clone)]
struct VerifyReport {
    mir_lean: Option<String>,
    output_text: String,
}

#[derive(Debug, Clone)]
struct VerifyError {
    message: String,
    failure: Option<StageFailure>,
    mir_lean: Option<String>,
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

fn format_stage(stage: &FailureStage) -> String {
    match stage {
        FailureStage::Capture => "capture".to_owned(),
        FailureStage::Spec => "spec".to_owned(),
        FailureStage::Proof { scope } => format!("proof, {scope}"),
    }
}

fn first_clean_line(diag: &str) -> String {
    diag.lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("verification failed")
        .to_owned()
}

fn check_mir_assertions(case: &FixtureCase, mir_lean: Option<&str>) -> Result<(), String> {
    if case.mir_contains.is_empty() && case.mir_not_contains.is_empty() {
        return Ok(());
    }
    let Some(mir) = mir_lean else {
        return Err(
            "expected Captured.lean to be emitted for MIR assertions, but none was found"
                .to_owned(),
        );
    };
    for needle in &case.mir_contains {
        if !mir.contains(needle) {
            return Err(format!(
                "Captured.lean did not contain expected substring {needle:?}\n--- Captured.lean ---\n{mir}"
            ));
        }
    }
    for needle in &case.mir_not_contains {
        if mir.contains(needle) {
            return Err(format!(
                "Captured.lean unexpectedly contained forbidden substring {needle:?}\n--- Captured.lean ---\n{mir}"
            ));
        }
    }
    Ok(())
}

fn evaluate_case(
    case: &FixtureCase,
    result: &Result<VerifyReport, VerifyError>,
    bless: bool,
) -> CaseOutcome {
    match (&case.expectation, result) {
        (PrimaryExpectation::Pass, Ok(report)) => {
            if let Err(e) = check_mir_assertions(case, report.mir_lean.as_deref()) {
                CaseOutcome::Failed(e)
            } else {
                CaseOutcome::Passed
            }
        }
        (PrimaryExpectation::Pass, Err(err)) => {
            // Polarity-safe: never auto-flip `//@ pass` to `//@ fail(...)`.
            CaseOutcome::Failed(format!(
                "expected `//@ pass`, got failure:\n{}",
                err.message
            ))
        }
        (PrimaryExpectation::Fail { .. }, Ok(report)) => {
            // Polarity-safe: never auto-flip `//@ fail(...)` to `//@ pass`.
            CaseOutcome::Failed(format!(
                "expected failure, but verification succeeded:\n{}",
                report.output_text
            ))
        }
        (
            PrimaryExpectation::Fail {
                stage: exp_stage,
                substring,
            },
            Err(err),
        ) => {
            let Some(actual) = &err.failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured failure, got operational error:\n{}",
                    err.message
                ));
            };
            if let Err(e) = check_mir_assertions(case, err.mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless {
                let quoted = serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: format!("//@ fail({}): {quoted}", format_stage(&actual.stage)),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "failure mismatch:\n  expected stage: {:?} containing {:?}\n  actual stage:   {:?}\n  diagnostic:     {}",
                    exp_stage, substring, actual.stage, actual.diagnostic
                ))
            }
        }
        (PrimaryExpectation::KnownBug { issue, .. }, Ok(report)) => {
            if let Err(e) = check_mir_assertions(case, report.mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if bless {
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: "//@ pass".to_owned(),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "`known_bug(#{issue})` now passes! Re-run with `ANNEAL_BLESS=1` to promote it to `//@ pass`.\nReceipt:\n{}",
                    report.output_text
                ))
            }
        }
        (
            PrimaryExpectation::KnownBug {
                issue,
                stage: exp_stage,
                substring,
            },
            Err(err),
        ) => {
            let Some(actual) = &err.failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured known_bug failure, got operational error:\n{}",
                    err.message
                ));
            };
            if let Err(e) = check_mir_assertions(case, err.mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless {
                let quoted = serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
                CaseOutcome::Blessed(BlessPatch {
                    file_path: case.file_path.clone(),
                    line_idx: case.primary_line_idx,
                    replacement: format!(
                        "//@ known_bug(#{issue}, {}): {quoted}",
                        format_stage(&actual.stage)
                    ),
                })
            } else {
                CaseOutcome::Failed(format!(
                    "known_bug(#{issue}) mismatch:\n  expected stage: {:?} containing {:?}\n  actual stage:   {:?}\n  diagnostic:     {}",
                    exp_stage, substring, actual.stage, actual.diagnostic
                ))
            }
        }
    }
}

fn apply_bless_patches(patches: &[BlessPatch]) -> Result<(), String> {
    let mut by_file: BTreeMap<PathBuf, Vec<&BlessPatch>> = BTreeMap::new();
    for patch in patches {
        by_file
            .entry(patch.file_path.clone())
            .or_default()
            .push(patch);
    }
    for (path, file_patches) in by_file {
        let content = fs::read_to_string(&path)
            .map_err(|e| format!("failed to read {} for bless: {e}", path.display()))?;
        let mut lines: Vec<String> = content.lines().map(str::to_owned).collect();
        for patch in file_patches {
            if patch.line_idx >= lines.len() {
                return Err(format!(
                    "bless line index {} out of bounds for {}",
                    patch.line_idx,
                    path.display()
                ));
            }
            lines[patch.line_idx] = patch.replacement.clone();
        }
        let mut out = lines.join("\n");
        out.push('\n');
        fs::write(&path, out)
            .map_err(|e| format!("failed to write blessed {}: {e}", path.display()))?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Lightweight Rust spec parser & Lean Spec/Proof synthesizer
// ---------------------------------------------------------------------------

const LICENSE_HEADER: &str = "\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

";

const LEAN_CORE_HELPERS: &str = r#"noncomputable abbrev initial (b : Body) (args : List Val) : State :=
  mkState 0 0 (initLocalsLoop b args 0 b.locals)
noncomputable abbrev step (b : Body) (s : State) : StepResult State TerminalOut :=
  evalStep (bodyProg b) 0 s

theorem validArgs1 {args : List Val} {ty : MirTy}
    (h : checkArgsMatch args [ty] = true) :
    ∃ v, args = [v] ∧ checkVal v ty = true := by
  cases args with
  | nil => cases h
  | cons v rest =>
    unfold checkArgsMatch at h
    cases hv : checkVal v ty with
    | false => rw [hv] at h; cases h
    | true =>
      rw [hv] at h
      cases rest with
      | nil => exact ⟨v, rfl, hv⟩
      | cons _ _ => cases h

theorem validArgs2 {args : List Val} {t1 t2 : MirTy}
    (h : checkArgsMatch args [t1, t2] = true) :
    ∃ v1 v2, args = [v1, v2] ∧ checkVal v1 t1 = true ∧ checkVal v2 t2 = true := by
  cases args with
  | nil => cases h
  | cons v1 rest =>
    unfold checkArgsMatch at h
    cases hv1 : checkVal v1 t1 with
    | false => rw [hv1] at h; cases h
    | true =>
      rw [hv1] at h
      have h2 : checkArgsMatch rest [t2] = true := h
      let ⟨v2, heq, hv2⟩ := validArgs1 h2
      subst heq
      exact ⟨v1, v2, rfl, hv1, hv2⟩

theorem mirTy_int_inj {w1 w2 : IntWidth} {s1 s2 : Bool}
    (h : MirTy.beq (.int w1 s1) (.int w2 s2) = true) :
    w1 = w2 ∧ s1 = s2 := by
  cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem checkVal_scalar_inv {v : Val} {w : IntWidth} {s : Bool}
    (h : checkVal v (.int w s) = true) :
    ∃ bits : BitVec 128,
      v = .scalar ⟨w, s, bits⟩ ∧ (truncateBits w bits == bits) = true := by
  unfold checkVal Val.ty? at h
  cases v with
  | scalar sv =>
    cases sv with
    | mk sw ss bits =>
      cases hw : ScalarVal.wf ⟨sw, ss, bits⟩ with
      | false =>
        change (match (if ScalarVal.wf ⟨sw, ss, bits⟩ then some (MirTy.int sw ss) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
        rw [hw] at h; cases h
      | true =>
        change (match (if ScalarVal.wf ⟨sw, ss, bits⟩ then some (MirTy.int sw ss) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
        rw [hw] at h
        let ⟨h_w, h_s⟩ := mirTy_int_inj h
        subst h_w; subst h_s
        exact ⟨bits, rfl, hw⟩
  | ptr _ => cases h
  | bool _ => cases h
  | unit => cases h
  | tuple fields =>
    cases fields with
    | nil => cases h
    | cons f fs =>
      change (match (match Val.tys? (f :: fs) with | some tys => some (MirTy.tuple tys) | none => none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
      cases ht : Val.tys? (f :: fs) <;> rw [ht] at h <;> cases h
  | bytes _ => cases h
  | enumVal ety var =>
    change (match (if enumAdmitted ety && Nat.blt var ety.discriminants.length then some (MirTy.enum ety) else none) with | some vTy => vTy.beq (.int w s) | none => false) = true at h
    cases he : (enumAdmitted ety && Nat.blt var ety.discriminants.length) <;> rw [he] at h <;> cases h

theorem succ_add_eq (base : Nat) : ∀ k : Nat, base + (k + 1) = (base + 1) + k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (succ_add_eq base k)

theorem zero_add_eq : ∀ k : Nat, 0 + k = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (zero_add_eq k)

def CheckBodies (p : Program) (safety : String → List Val → Prop) :
    Nat → List Body → Prop
  | _, [] => True
  | base, b :: bs =>
    BodyVerified p base b (safety b.identity) ∧
    CheckBodies p safety (base + 1) bs

theorem all_bodies_of_checkBodies {p : Program}
    {safety : String → List Val → Prop} :
    ∀ (base : Nat) (bs : List Body),
      CheckBodies p safety base bs →
      ∀ (k : Nat) (selected : Body),
        Trusted.MirSemantics.getElem? bs k = some selected →
        BodyVerified p (base + k) selected (safety selected.identity)
  | _, [], _, _, _, found => by cases found
  | base, _ :: _, ⟨h_head, _⟩, 0, selected, found => by
    injection found with h_eq
    subst h_eq
    exact h_head
  | base, _ :: bs, ⟨_, h_tail⟩, k + 1, selected, found => by
    have ih := all_bodies_of_checkBodies (base + 1) bs h_tail k selected found
    rw [succ_add_eq base k]
    exact ih

theorem all_bodies_safe_of {p : Program}
    {safety : String → List Val → Prop}
    (h : CheckBodies p safety 0 p.bodies) :
    ∀ id selected,
      Trusted.MirSemantics.getElem? p.bodies id = some selected →
      BodyVerified p id selected (safety selected.identity) := by
  intro id selected found
  have h0 := all_bodies_of_checkBodies 0 p.bodies h id selected found
  rw [zero_add_eq id] at h0
  exact h0

theorem bodyVerified_of_exec1 {p : Program} {defId : DefId} {body : Body}
    {safetyPre : List Val → Prop} {ty : MirTy}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_adm : BodyStaticAdmitted p body = true)
    (h_param : (body.locals.drop 1).take body.argumentCount = [ty])
    (h_exec : ∀ v : Val, checkVal v ty = true →
      ∃ out, Executes body (initial body [v]) out)
    (h_callFree : bodyCallFree body = true := by rfl) :
    BodyVerified p defId body safetyPre := by
  refine bodyVerified_of_safe h_body h_adm (fun args h_valid _ => ?_) h_callFree
  have h_match : checkArgsMatch args [ty] = true := by
    unfold ValidEntryArgs at h_valid
    rw [h_param] at h_valid
    exact h_valid
  let ⟨v, h_eq, hv⟩ := validArgs1 h_match
  subst h_eq
  let ⟨_, hex⟩ := h_exec v hv
  exact executes_safe hex

theorem ensures_eq_of_exec1 {p : Program} {defId : DefId} {body : Body}
    {ty : MirTy}
    (h_body : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (h_param : (body.locals.drop 1).take body.argumentCount = [ty])
    (h_exec : ∀ v : Val, checkVal v ty = true →
      Executes body (initial body [v]) v)
    (h_callFree : bodyCallFree body = true := by rfl) :
    ∀ selected, Trusted.MirSemantics.getElem? p.bodies defId = some selected →
      ∀ args ret, ValidEntryArgs selected args →
        Behavior (entryProgForBody p defId) { args := args }
          (.returned ⟨ret, ⟨[]⟩⟩) →
        Trusted.MirSemantics.getElem? args 0 = some ret := by
  intro selected found args ret h_valid h_beh
  have h_same : selected = body := Option.some.inj (found.symm.trans h_body)
  subst h_same
  have h_ret : Returns selected args ret :=
    (returns_of_behavior found h_beh h_callFree).2
  have h_match : checkArgsMatch args [ty] = true := by
    unfold ValidEntryArgs at h_valid
    rw [h_param] at h_valid
    exact h_valid
  let ⟨v, h_eq, hv⟩ := validArgs1 h_match
  subst h_eq
  exact congrArg some (executes_unique (h_exec v hv) h_ret)
"#;

const LEAN_U32_HELPERS: &str = r#"theorem truncateBits_i32_idem (x : BitVec 128) :
    truncateBits .i32 (truncateBits .i32 x) = truncateBits .i32 x := by
  let b : BitVec 32 := bvExtractLsb 31 0 x
  have hb : (bvZeroExtend 128 b).toNat = b.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))
  have hb32 : BitVec.ofNat 32 (bvZeroExtend 128 b).toNat = b := by
    apply bitVec_eq_of_toNat_eq
    change Nat.mod (bvZeroExtend 128 b).toNat (Nat.pow 2 32) = b.toNat
    rw [hb]
    exact Nat.mod_eq_of_lt b.isLt
  change bvZeroExtend 128 (BitVec.ofNat 32 (bvZeroExtend 128 b).toNat) =
    bvZeroExtend 128 b
  rw [hb32]

theorem checkVal_u32_truncateBits (x : BitVec 128) :
    checkVal (.scalar ⟨.i32, false, truncateBits .i32 x⟩) (.int .i32 false) =
      true := by
  have h_eq :
      (truncateBits .i32 (truncateBits .i32 x) == truncateBits .i32 x) =
      true := by
    rw [truncateBits_i32_idem]
    exact beq_self_eq_true (truncateBits .i32 x)
  change (match (if (truncateBits .i32 (truncateBits .i32 x) == truncateBits .i32 x) then some (MirTy.int .i32 false) else none) with | some vTy => vTy.beq (.int .i32 false) | none => false) = true
  rw [h_eq]
  rfl

theorem evalBinOp_u32_add (b1 b2 : BitVec 128) :
    evalBinOp .add (.scalar ⟨.i32, false, b1⟩) (.scalar ⟨.i32, false, b2⟩) =
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, b1⟩ + decodeScalar ⟨.i32, false, b2⟩))⟩) := by
  unfold evalBinOp evalArithOp truncateScalar
  change (if _ && false then Except.error FaultKind.undefined else _) = _
  rw [Bool.and_false]
  rfl
"#;

const LEAN_ENUM_HELPERS: &str = r#"theorem natListBeq_eq {xs ys : List Nat} (h : natListBeq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      change (Nat.beq x y && natListBeq xs ys) = true at h
      have h1 : Nat.beq x y = true := by
        cases h_xy : Nat.beq x y
        · rw [h_xy] at h; cases h
        · rfl
      have h2 : natListBeq xs ys = true := by
        rw [h1] at h; exact h
      rw [Nat.eq_of_beq_eq_true h1, ih h2]

theorem intWidth_beq_eq {w1 w2 : IntWidth}
    (h : IntWidth.beq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | cases h

theorem enumTagRepr_beq_eq {r1 r2 : EnumTagRepr}
    (h : EnumTagRepr.beq r1 r2 = true) : r1 = r2 := by
  cases r1 with
  | zeroSized =>
    cases r2 with
    | zeroSized => rfl
    | scalar _ _ => cases h
  | scalar w1 s1 =>
    cases r2 with
    | zeroSized => cases h
    | scalar w2 s2 =>
      cases w1 <;> cases w2 <;> cases s1 <;> cases s2 <;> first | rfl | cases h

theorem enumTy_beq_eq {e1 e2 : EnumTy}
    (h : EnumTy.beq e1 e2 = true) : e1 = e2 := by
  cases e1 with
  | mk id1 dw1 ds1 tr1 discs1 =>
    cases e2 with
    | mk id2 dw2 ds2 tr2 discs2 =>
      unfold EnumTy.beq at h
      dsimp only at h
      cases h1 : Nat.beq id1 id2 <;>
        cases h2 : IntWidth.beq dw1 dw2 <;>
        cases h3 : (ds1 == ds2) <;>
        cases h4 : EnumTagRepr.beq tr1 tr2 <;>
        cases h5 : natListBeq discs1 discs2 <;>
        rw [h1, h2, h3, h4, h5] at h <;>
        try cases h
      rw [Nat.eq_of_beq_eq_true h1, intWidth_beq_eq h2, eq_of_beq h3,
        enumTagRepr_beq_eq h4, natListBeq_eq h5]

theorem checkVal_enum2_inv {ety : EnumTy}
    (h_ds : ety.discriminants = [0, 1]) {v : Val}
    (h : checkVal v (.enum ety) = true) :
    v = .enumVal ety 0 ∨ v = .enumVal ety 1 := by
  cases v with
  | enumVal ety' var =>
    change (match (if enumAdmitted ety' && Nat.blt var ety'.discriminants.length then some (MirTy.enum ety') else none) with | some vTy => vTy.beq (.enum ety) | none => false) = true at h
    cases h_adm : (enumAdmitted ety' && Nat.blt var ety'.discriminants.length) with
    | false => rw [h_adm] at h; cases h
    | true =>
      rw [h_adm] at h
      change EnumTy.beq ety' ety = true at h
      have h_eq := enumTy_beq_eq h
      subst h_eq
      rw [h_ds] at h_adm
      cases h_e : enumAdmitted ety' with
      | false => rw [h_e] at h_adm; cases h_adm
      | true =>
        rw [h_e] at h_adm
        cases var with
        | zero => exact .inl rfl
        | succ n =>
          cases n with
          | zero => exact .inr rfl
          | succ m => cases h_adm
  | scalar sv =>
    change (match (if sv.wf then some (MirTy.int sv.width sv.signed) else none) with | some vTy => vTy.beq (.enum ety) | none => false) = true at h
    cases h_wf : sv.wf <;> rw [h_wf] at h <;> cases h
  | tuple fields =>
    cases fields with
    | nil => cases h
    | cons f fs =>
      change (match (match Val.tys? (f :: fs) with | some tys => some (MirTy.tuple tys) | none => none) with | some vTy => vTy.beq (.enum ety) | none => false) = true at h
      cases ht : Val.tys? (f :: fs) <;> rw [ht] at h <;> cases h
  | ptr _ | bool _ | unit | bytes _ => cases h
"#;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RustIntTy {
    width_lean: &'static str,
    signed: bool,
}

impl RustIntTy {
    fn parse(ty: &str) -> Option<Self> {
        match ty {
            "u8" => Some(Self {
                width_lean: ".i8",
                signed: false,
            }),
            "i8" => Some(Self {
                width_lean: ".i8",
                signed: true,
            }),
            "u16" => Some(Self {
                width_lean: ".i16",
                signed: false,
            }),
            "i16" => Some(Self {
                width_lean: ".i16",
                signed: true,
            }),
            "u32" => Some(Self {
                width_lean: ".i32",
                signed: false,
            }),
            "i32" => Some(Self {
                width_lean: ".i32",
                signed: true,
            }),
            "u64" => Some(Self {
                width_lean: ".i64",
                signed: false,
            }),
            "i64" => Some(Self {
                width_lean: ".i64",
                signed: true,
            }),
            "usize" => Some(Self {
                width_lean: ".isize",
                signed: false,
            }),
            "isize" => Some(Self {
                width_lean: ".isize",
                signed: true,
            }),
            _ => None,
        }
    }

    fn mir_ty_lean(self) -> String {
        format!("(.int {} {})", self.width_lean, self.signed)
    }

    fn zero_val_lean(self) -> String {
        format!(
            ".scalar ⟨{}, {}, BitVec.ofNat 128 0⟩",
            self.width_lean, self.signed
        )
    }
}

#[derive(Debug, Clone)]
struct ParsedFn {
    name: String,
    is_unsafe: bool,
    params: Vec<(String, String)>,
    ret_ty: Option<String>,
    requires_nonzero: Option<(usize, RustIntTy)>,
    ensures_eq_param: Option<usize>,
    body_norm: String,
}

#[derive(Debug, Clone)]
struct SynthesizedPackage {
    spec_lean: String,
    proof_lean: String,
    fn_line_ranges: Vec<(usize, usize, String)>,
}

fn normalize_ws(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn consume_block_comment<'a>(rest: &'a str, depth: &mut usize) -> (&'a str, &'a str) {
    let bytes = rest.as_bytes();
    let mut pos = 0;
    while pos + 1 < bytes.len() {
        if bytes[pos] == b'/' && bytes[pos + 1] == b'*' {
            *depth += 1;
            pos += 2;
        } else if bytes[pos] == b'*' && bytes[pos + 1] == b'/' {
            *depth = depth.saturating_sub(1);
            pos += 2;
            if *depth == 0 {
                return (&rest[..pos], &rest[pos..]);
            }
        } else {
            pos += 1;
        }
    }
    (rest, "")
}

fn consume_attribute<'a>(
    rest: &'a str,
    depth: &mut usize,
    in_string: &mut bool,
) -> (&'a str, &'a str) {
    let start = if *depth == 0 {
        if rest.starts_with("#![") {
            2
        } else if rest.starts_with("#[") {
            1
        } else {
            0
        }
    } else {
        0
    };
    let mut escape = false;
    let mut skip_until = 0;
    for (rel_idx, ch) in rest[start..].char_indices() {
        let idx = start + rel_idx;
        if idx < skip_until {
            continue;
        }
        if *in_string {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                *in_string = false;
            }
            continue;
        }
        match ch {
            '"' => *in_string = true,
            '\'' => {
                // Skip single-character literals (`'['`, `']'`, `'"'`, `'\''`)
                // without misclassifying Rust lifetimes (`'a`).
                let mut tail = rest[idx + 1..].char_indices();
                match tail.next() {
                    Some((_, '\\')) => {
                        if tail.next().is_some()
                            && let Some((close_rel, '\'')) = tail.next()
                        {
                            skip_until = idx + 1 + close_rel + 1;
                        }
                    }
                    Some((_, c)) if c != '\'' => {
                        if let Some((close_rel, '\'')) = tail.next() {
                            skip_until = idx + 1 + close_rel + 1;
                        }
                    }
                    _ => {}
                }
            }
            '[' => *depth += 1,
            ']' => {
                *depth = depth.saturating_sub(1);
                if *depth == 0 {
                    let end = idx + ch.len_utf8();
                    return (&rest[..end], &rest[end..]);
                }
            }
            _ => {}
        }
    }
    (rest, "")
}

fn skip_rust_string(bytes: &[u8], start_quote: usize) -> usize {
    let mut i = start_quote + 1;
    let mut escape = false;
    while i < bytes.len() {
        let b = bytes[i];
        if escape {
            escape = false;
        } else if b == b'\\' {
            escape = true;
        } else if b == b'"' {
            return i + 1;
        }
        i += 1;
    }
    bytes.len()
}

fn try_skip_raw_string(bytes: &[u8], after_prefix: usize) -> Option<usize> {
    let mut hashes = 0usize;
    let mut i = after_prefix;
    while i < bytes.len() && bytes[i] == b'#' {
        hashes += 1;
        i += 1;
    }
    if i >= bytes.len() || bytes[i] != b'"' {
        return None;
    }
    i += 1;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            let mut matched = 0usize;
            while matched < hashes
                && i + 1 + matched < bytes.len()
                && bytes[i + 1 + matched] == b'#'
            {
                matched += 1;
            }
            if matched == hashes {
                return Some(i + 1 + hashes);
            }
        }
        i += 1;
    }
    Some(bytes.len())
}

fn skip_block_comment(bytes: &[u8], start_slash: usize) -> usize {
    let mut depth = 1usize;
    let mut i = start_slash + 2;
    while i + 1 < bytes.len() && depth > 0 {
        if bytes[i] == b'/' && bytes[i + 1] == b'*' {
            depth += 1;
            i += 2;
        } else if bytes[i] == b'*' && bytes[i + 1] == b'/' {
            depth -= 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    if depth > 0 { bytes.len() } else { i }
}

fn skip_line_comment(bytes: &[u8], start_slash: usize) -> usize {
    let mut i = start_slash + 2;
    while i < bytes.len() && bytes[i] != b'\n' {
        i += 1;
    }
    i
}

fn try_skip_char_literal(source: &str, start_quote: usize) -> Option<usize> {
    let tail = &source[start_quote + 1..];
    let mut chars = tail.char_indices();
    match chars.next()? {
        (_, '\\') => {
            // Skip `\\`, `\'`, `\xHH`, `\u{...}`, etc. up to closing `'` on
            // the same line.
            let _ = chars.next()?;
            for (rel, ch) in chars {
                if ch == '\'' {
                    return Some(start_quote + 1 + rel + 1);
                }
                if ch == '\n' {
                    return None;
                }
            }
            None
        }
        (_, '\'') | (_, '\n') => None,
        (_, _) => {
            let (close_rel, close_ch) = chars.next()?;
            if close_ch == '\'' {
                Some(start_quote + 1 + close_rel + 1)
            } else {
                None
            }
        }
    }
}

fn attribute_mentions_doc(attr: &str) -> bool {
    let bytes = attr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            i = skip_line_comment(bytes, i);
            continue;
        }
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i = skip_block_comment(bytes, i);
            continue;
        }
        if b == b'"' {
            i = skip_rust_string(bytes, i);
            continue;
        }
        if b == b'\'' {
            if let Some(next) = try_skip_char_literal(attr, i) {
                i = next;
                continue;
            }
            i += 1;
            continue;
        }
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let ident = &attr[start..i];
            if matches!(ident, "r" | "br" | "cr")
                && let Some(next) = try_skip_raw_string(bytes, i)
            {
                i = next;
                continue;
            }
            if ident == "r"
                && i + 1 < bytes.len()
                && bytes[i] == b'#'
                && (bytes[i + 1].is_ascii_alphabetic() || bytes[i + 1] == b'_')
            {
                let raw_start = i + 1;
                i = raw_start + 1;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                if &attr[raw_start..i] == "doc" {
                    return true;
                }
                continue;
            }
            if ident == "doc" {
                return true;
            }
            continue;
        }
        i += 1;
    }
    false
}

/// Scans all Rust attributes (`#[...]`, `#![...]`, including whitespace/comment
/// variants such as `# [ ... ]`) across `source` outside comments and literals,
/// failing closed on any `anneal:` substring or any `doc` attribute (which
/// could conceal an `anneal:` directive via string escapes, `concat!`,
/// `cfg_attr`, or `include_str!`).
fn scan_attributes_fail_closed(source: &str) -> Result<(), String> {
    let bytes = source.as_bytes();
    let skip_ws_comments = |mut k: usize| -> usize {
        loop {
            while k < bytes.len() && bytes[k].is_ascii_whitespace() {
                k += 1;
            }
            if k + 1 < bytes.len() && bytes[k] == b'/' && bytes[k + 1] == b'/' {
                k = skip_line_comment(bytes, k);
            } else if k + 1 < bytes.len() && bytes[k] == b'/' && bytes[k + 1] == b'*' {
                k = skip_block_comment(bytes, k);
            } else {
                return k;
            }
        }
    };
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'/' {
            i = skip_line_comment(bytes, i);
            continue;
        }
        if b == b'/' && i + 1 < bytes.len() && bytes[i + 1] == b'*' {
            i = skip_block_comment(bytes, i);
            continue;
        }
        if b == b'"' {
            i = skip_rust_string(bytes, i);
            continue;
        }
        if b == b'\'' {
            if let Some(next) = try_skip_char_literal(source, i) {
                i = next;
                continue;
            }
            i += 1;
            continue;
        }
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            i += 1;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let ident = &source[start..i];
            if matches!(ident, "r" | "br" | "cr")
                && let Some(next) = try_skip_raw_string(bytes, i)
            {
                i = next;
                continue;
            }
            if ident == "r"
                && i + 1 < bytes.len()
                && bytes[i] == b'#'
                && (bytes[i + 1].is_ascii_alphabetic() || bytes[i + 1] == b'_')
            {
                // Skip raw identifier `r#foo` so its `#` is not mistaken for
                // an attribute start.
                i += 2;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
            }
            continue;
        }
        if b == b'#' {
            let attr_start = i;
            let mut j = skip_ws_comments(i + 1);
            if j < bytes.len() && bytes[j] == b'!' {
                j = skip_ws_comments(j + 1);
            }
            if j < bytes.len() && bytes[j] == b'[' {
                let mut depth = 1usize;
                j += 1;
                while j < bytes.len() && depth > 0 {
                    let c = bytes[j];
                    if c == b'/' && j + 1 < bytes.len() && bytes[j + 1] == b'/' {
                        j = skip_line_comment(bytes, j);
                    } else if c == b'/' && j + 1 < bytes.len() && bytes[j + 1] == b'*' {
                        j = skip_block_comment(bytes, j);
                    } else if c == b'"' {
                        j = skip_rust_string(bytes, j);
                    } else if c == b'\'' {
                        if let Some(next) = try_skip_char_literal(source, j) {
                            j = next;
                        } else {
                            j += 1;
                        }
                    } else if c.is_ascii_alphabetic() || c == b'_' {
                        let id_start = j;
                        j += 1;
                        while j < bytes.len()
                            && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_')
                        {
                            j += 1;
                        }
                        let id = &source[id_start..j];
                        if matches!(id, "r" | "br" | "cr")
                            && let Some(next) = try_skip_raw_string(bytes, j)
                        {
                            j = next;
                        }
                    } else if c == b'[' {
                        depth += 1;
                        j += 1;
                    } else if c == b']' {
                        depth -= 1;
                        j += 1;
                    } else {
                        j += 1;
                    }
                }
                let attr_slice = &source[attr_start..j];
                if attr_slice.contains("anneal:") {
                    return Err(format!(
                        "unsupported attribute `anneal:` directive: `{}`",
                        attr_slice.trim()
                    ));
                }
                if attribute_mentions_doc(attr_slice) {
                    return Err(format!(
                        "unsupported `doc` attribute (use `///` doc comments for `anneal:` directives): `{}`",
                        attr_slice.trim()
                    ));
                }
                i = j;
                continue;
            }
        }
        i += 1;
    }
    Ok(())
}

fn parse_rust_functions(source: &str) -> Result<Vec<ParsedFn>, String> {
    scan_attributes_fail_closed(source)?;
    let mut fns = Vec::new();
    let mut pending_requires: Vec<String> = Vec::new();
    let mut pending_specs: Vec<String> = Vec::new();
    let mut brace_depth: i32 = 0;
    let mut block_comment_depth: usize = 0;
    let mut attr_depth: usize = 0;
    let mut attr_in_string = false;

    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let mut rest = lines[i].trim();
        // Strip leading block comments (`/* ... */`, `/** ... */`, `/*! ...`)
        // and attributes (`#[...]`, `#![...]`), failing closed if any carries
        // `anneal:`, and re-dispatch any remaining same-line item text so a
        // same-line `#[repr(u8)] pub enum` or `/** doc */ pub enum` cannot
        // silently pass pending directives to a later function.
        loop {
            rest = rest.trim_start();
            if block_comment_depth > 0 || rest.starts_with("/*") {
                let (consumed, after) = consume_block_comment(rest, &mut block_comment_depth);
                if consumed.contains("anneal:") {
                    return Err(format!(
                        "unsupported block-doc `anneal:` directive: `{}`",
                        consumed.trim()
                    ));
                }
                rest = after;
                if block_comment_depth > 0 {
                    break;
                }
                continue;
            }
            if attr_depth > 0 || rest.starts_with("#[") || rest.starts_with("#![") {
                let (consumed, after) =
                    consume_attribute(rest, &mut attr_depth, &mut attr_in_string);
                if consumed.contains("anneal:") {
                    return Err(format!(
                        "unsupported attribute `anneal:` directive: `{}`",
                        consumed.trim()
                    ));
                }
                rest = after;
                if attr_depth > 0 {
                    break;
                }
                continue;
            }
            break;
        }
        rest = rest.trim();
        if rest.is_empty() {
            i += 1;
            continue;
        }
        if let Some(inner_doc) = rest.strip_prefix("//!") {
            if inner_doc.contains("anneal:") {
                return Err(format!(
                    "unsupported inner-doc `anneal:` directive: `{}`",
                    inner_doc.trim()
                ));
            }
            i += 1;
            continue;
        }
        if brace_depth == 0 {
            if let Some(doc) = rest.strip_prefix("///") {
                let doc = doc.trim();
                if let Some(req) = doc.strip_prefix("anneal:requires ") {
                    let req = req.trim();
                    if req.is_empty() {
                        return Err("empty `anneal:requires` directive".to_owned());
                    }
                    if req.contains("anneal:") {
                        return Err(format!("unsupported `anneal:` doc directive `{doc}`"));
                    }
                    pending_requires.push(req.to_owned());
                } else if let Some(sp) = doc.strip_prefix("anneal:spec ") {
                    let sp = sp.trim();
                    if sp.is_empty() {
                        return Err("empty `anneal:spec` directive".to_owned());
                    }
                    if sp.contains("anneal:") {
                        return Err(format!("unsupported `anneal:` doc directive `{doc}`"));
                    }
                    pending_specs.push(sp.to_owned());
                } else if doc.contains("anneal:") {
                    return Err(format!("unsupported `anneal:` doc directive `{doc}`"));
                }
                i += 1;
                continue;
            }
            if rest.starts_with("//") {
                if rest.contains("anneal:") {
                    return Err(format!(
                        "unsupported unparsed `anneal:` directive: `{rest}`"
                    ));
                }
                i += 1;
                continue;
            }
            if is_top_level_fn_header(rest) {
                // Collect signature + body until matching `}` back at depth 0.
                let mut chunk = String::new();
                let mut depth = 0i32;
                let mut saw_open = false;
                let mut first_line = Some(rest);
                while i < lines.len() {
                    let l = first_line.take().unwrap_or(lines[i]);
                    let lt = l.trim();
                    // Fail closed on ANY `anneal:` occurrence on a function
                    // line or inside a function body (including mid-line
                    // `/** ... */`, mid-line `/// ...`, or nested docs).
                    if lt.contains("anneal:") {
                        return Err(format!("unsupported unparsed `anneal:` directive: `{lt}`"));
                    }
                    if !chunk.is_empty() {
                        chunk.push('\n');
                    }
                    chunk.push_str(l);
                    for ch in l.chars() {
                        if ch == '{' {
                            depth += 1;
                            saw_open = true;
                        } else if ch == '}' {
                            depth -= 1;
                        }
                    }
                    i += 1;
                    if saw_open && depth <= 0 {
                        break;
                    }
                }
                if saw_open {
                    let parsed = parse_one_fn(
                        &chunk,
                        &std::mem::take(&mut pending_requires),
                        &std::mem::take(&mut pending_specs),
                    )?;
                    fns.push(parsed);
                } else if !pending_requires.is_empty() || !pending_specs.is_empty() {
                    return Err("dangling `anneal:` directive on unclosed function item".to_owned());
                }
                continue;
            }
            // Non-fn item at top level (struct, enum, trait, impl, use, etc.):
            // fail closed if an `anneal:` directive was attached to it or
            // appears anywhere on the line.
            if !pending_requires.is_empty() || !pending_specs.is_empty() {
                return Err(format!(
                    "dangling `anneal:` directive attached to non-function item `{rest}`"
                ));
            }
            if rest.contains("anneal:") {
                return Err(format!(
                    "unsupported unparsed `anneal:` directive: `{rest}`"
                ));
            }
        } else if rest.contains("anneal:") {
            return Err(format!("unsupported nested `anneal:` directive: `{rest}`"));
        }
        for ch in rest.chars() {
            if ch == '{' {
                brace_depth += 1;
            } else if ch == '}' {
                brace_depth -= 1;
            }
        }
        i += 1;
    }
    if !pending_requires.is_empty() || !pending_specs.is_empty() {
        return Err("dangling `anneal:` directive not attached to a top-level function".to_owned());
    }
    Ok(fns)
}

fn is_top_level_fn_header(trimmed: &str) -> bool {
    ["pub unsafe fn ", "unsafe fn ", "pub fn ", "fn "]
        .iter()
        .any(|prefix| trimmed.starts_with(prefix))
}

fn parse_one_fn(fn_chunk: &str, requires: &[String], specs: &[String]) -> Result<ParsedFn, String> {
    let is_unsafe = fn_chunk.starts_with("pub unsafe fn ") || fn_chunk.starts_with("unsafe fn ");
    let after_fn = fn_chunk
        .split_once("fn ")
        .map(|(_, r)| r)
        .unwrap_or(fn_chunk);
    let open_paren = after_fn
        .find('(')
        .ok_or_else(|| format!("malformed fn header: {after_fn}"))?;
    let raw_name = after_fn[..open_paren].trim();
    let name = raw_name
        .split('<')
        .next()
        .unwrap_or(raw_name)
        .trim()
        .to_owned();
    let close_paren = after_fn[open_paren + 1..]
        .find(')')
        .map(|idx| open_paren + 1 + idx)
        .ok_or_else(|| format!("missing `)` in fn `{name}`"))?;
    let params_str = &after_fn[open_paren + 1..close_paren];
    let mut params = Vec::new();
    for p in params_str.split(',') {
        let p = p.trim();
        if p.is_empty() {
            continue;
        }
        if let Some((pname, pty)) = p.split_once(':') {
            let pname = pname.trim().trim_start_matches("mut ").trim().to_owned();
            let pty = pty.trim().to_owned();
            params.push((pname, pty));
        }
    }
    let open_brace = after_fn[close_paren + 1..]
        .find('{')
        .map(|idx| close_paren + 1 + idx)
        .unwrap_or(after_fn.len());
    let header_tail = after_fn[close_paren + 1..open_brace].trim();
    let ret_ty = header_tail
        .strip_prefix("->")
        .map(|r| r.split("where").next().unwrap_or(r).trim().to_owned())
        .filter(|r| !r.is_empty());
    let close_brace = after_fn.rfind('}').unwrap_or(after_fn.len());
    let body_raw = if open_brace < close_brace {
        &after_fn[open_brace + 1..close_brace]
    } else {
        ""
    };
    let body_norm = normalize_ws(body_raw);

    let mut requires_nonzero = None;
    for req in requires {
        if requires_nonzero.is_some() {
            return Err(format!(
                "multiple `anneal:requires` clauses on `{name}` are unsupported"
            ));
        }
        let Some((lhs, rhs)) = req.split_once("!=") else {
            return Err(format!(
                "unsupported `anneal:requires {req}` syntax on `{name}`"
            ));
        };
        let lhs = lhs.trim();
        let rhs = rhs.trim();
        let Some((param_idx, (_, pty))) = params.iter().enumerate().find(|(_, (pn, _))| pn == lhs)
        else {
            return Err(format!(
                "unknown identifier `{lhs}` in `anneal:requires {req}` on `{name}`"
            ));
        };
        if rhs != "0" {
            return Err(format!(
                "unsupported `anneal:requires {req}` literal `{rhs}` on `{name}` (expected `!= 0`)"
            ));
        }
        let Some(int_ty) = RustIntTy::parse(pty) else {
            return Err(format!(
                "unsupported parameter type `{pty}` in `anneal:requires {req}` on `{name}`"
            ));
        };
        requires_nonzero = Some((param_idx, int_ty));
    }

    let mut ensures_eq_param = None;
    for sp in specs {
        if ensures_eq_param.is_some() {
            return Err(format!(
                "multiple `anneal:spec` clauses on `{name}` are unsupported"
            ));
        }
        let inner = sp
            .strip_prefix("ensures(")
            .and_then(|s| s.strip_suffix(')'))
            .ok_or_else(|| format!("unsupported `anneal:spec {sp}` syntax on `{name}`"))?;
        if let Some((lhs, rhs)) = inner.split_once("==") {
            let lhs = lhs.trim();
            let rhs = rhs.trim();
            if lhs != "ret" {
                return Err(format!(
                    "expected `ret == <param>` in `anneal:spec {sp}` on `{name}`"
                ));
            }
            let Some((param_idx, _)) = params.iter().enumerate().find(|(_, (pn, _))| pn == rhs)
            else {
                return Err(format!(
                    "unknown identifier `{rhs}` in `anneal:spec {sp}` on `{name}`"
                ));
            };
            ensures_eq_param = Some(param_idx);
        } else {
            return Err(format!(
                "unsupported `anneal:spec {sp}` expression on `{name}`"
            ));
        }
    }

    Ok(ParsedFn {
        name,
        is_unsafe,
        params,
        ret_ty,
        requires_nonzero,
        ensures_eq_param,
        body_norm,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BodyPattern {
    DirectId(RustIntTy),
    MoveId(RustIntTy),
    ConstZero(RustIntTy),
    U32Add,
    ClampNonzero,
    CustomMirNonzero(RustIntTy),
    EnumTag,
    Unproved,
}

fn classify_body(f: &ParsedFn) -> BodyPattern {
    if f.params.len() == 1 {
        let (p, pty) = (&f.params[0].0, f.params[0].1.as_str());
        let ret_int = f.ret_ty.as_deref().and_then(RustIntTy::parse);
        if let Some(int_ty) = RustIntTy::parse(pty)
            && ret_int == Some(int_ty)
        {
            if f.body_norm == *p {
                return BodyPattern::DirectId(int_ty);
            }
            if f.body_norm == format!("let y = {p}; y") {
                return BodyPattern::MoveId(int_ty);
            }
            if f.body_norm == format!("let _ = {p}; 0") || f.body_norm == "0" {
                return BodyPattern::ConstZero(int_ty);
            }
            if int_ty == RustIntTy::parse("usize").unwrap()
                && f.body_norm == format!("if {p} == 0 {{ 1 }} else {{ {p} }}")
            {
                return BodyPattern::ClampNonzero;
            }
            if f.body_norm.contains("mir!") && f.body_norm.contains("Unreachable()") {
                return BodyPattern::CustomMirNonzero(int_ty);
            }
        }
        if pty == "Single"
            && let Some(out_ty) = ret_int
            && (f.body_norm == "0" || f.body_norm.ends_with("; 0"))
        {
            return BodyPattern::ConstZero(out_ty);
        }
    }
    if f.params.len() == 2 && f.params[0].1 == "u32" && f.params[1].1 == "u32" {
        let (p0, p1) = (&f.params[0].0, &f.params[1].0);
        if f.body_norm == format!("{p0} + {p1}") {
            return BodyPattern::U32Add;
        }
    }
    if f.params.len() == 1 && f.params[0].1 == "E" && f.body_norm.contains("E::A => 0") {
        return BodyPattern::EnumTag;
    }
    BodyPattern::Unproved
}

fn safe_pre_guard(f: &ParsedFn) -> Option<String> {
    match (f.is_unsafe, f.requires_nonzero) {
        (false, Some((req_idx, int_ty))) => Some(format!(
            "Trusted.MirSemantics.getElem? args {req_idx} ≠ some ({}) → ",
            int_ty.zero_val_lean()
        )),
        _ => None,
    }
}

fn ensures_clause_lean(program_expr: &str, idx: usize, f: &ParsedFn, ens_idx: usize) -> String {
    let pre_guard = safe_pre_guard(f).unwrap_or_default();
    format!(
        "∀ selected, Trusted.MirSemantics.getElem? {program_expr}.bodies {idx} = some selected → \
         ∀ args ret, ValidEntryArgs selected args → \
         {pre_guard}\
         Behavior (entryProgForBody {program_expr} {idx}) {{ args := args }} (.returned ⟨ret, ⟨[]⟩⟩) → \
         Trusted.MirSemantics.getElem? args {ens_idx} = some ret"
    )
}

fn synthesize_proof_package(source: &str) -> Result<SynthesizedPackage, String> {
    let fns = parse_rust_functions(source)?;

    // Build `Spec.lean` solely from function signatures and `anneal:*` doc
    // clauses (independent of `classify_body`). `BodyVerified` itself gates
    // `Specs.safety` by `selected.isUnsafe = true`.
    let mut safety_branches = Vec::new();
    let mut prop_clauses: Vec<(usize, String)> = Vec::new();
    for (idx, f) in fns.iter().enumerate() {
        if let Some((req_idx, int_ty)) = f.requires_nonzero {
            let zero_val = int_ty.zero_val_lean();
            safety_branches.push(format!(
                "(if stringBeq identity \"rust-path-v1::{}\" then \
                 Trusted.MirSemantics.getElem? args {req_idx} ≠ some ({zero_val}) else ",
                f.name
            ));
        }
        if let Some(ens_idx) = f.ensures_eq_param {
            let clause = format!("({})", ensures_clause_lean("p", idx, f, ens_idx));
            prop_clauses.push((idx, clause));
        }
    }

    // Default unmatched safety preconditions to `True` (matching
    // `Trusted.MirSemantics.Specs`) so an `unsafe fn` without a parsed
    // `requires` fails closed rather than turning `BodyVerified` vacuous.
    let safety_expr = if safety_branches.is_empty() {
        "fun _ _ => True".to_owned()
    } else {
        let mut s = String::from("fun identity args => ");
        for b in &safety_branches {
            s.push_str(b);
        }
        s.push_str("True");
        for _ in &safety_branches {
            s.push(')');
        }
        s
    };

    let property_expr = if prop_clauses.is_empty() {
        "fun _ => True".to_owned()
    } else {
        let joined = prop_clauses
            .iter()
            .map(|(_, c)| c.as_str())
            .collect::<Vec<_>>()
            .join(" ∧ ");
        format!("fun p => {joined}")
    };

    let spec_lean = format!(
        r#"{LICENSE_HEADER}prelude
import Trusted.MirSemantics

namespace Spec
open Trusted.MirAst Trusted.MirSemantics

def specs : Specs where
  safety := {safety_expr}
  property := {property_expr}

end Spec
"#
    );

    // Build `Proof.lean` and record 1-based line ranges per function so Lean
    // compiler rejections map cleanly to `FailureStage::Proof { scope }`.
    let mut proof_lines: Vec<String> = Vec::new();
    let push_block = |lines: &mut Vec<String>, text: &str| {
        for l in text.lines() {
            lines.push(l.to_owned());
        }
    };

    push_block(
        &mut proof_lines,
        &format!(
            r#"{LICENSE_HEADER}prelude
import Expected
import Anneal.MirWp

namespace Proof
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp"#
        ),
    );

    if fns.is_empty() {
        push_block(
            &mut proof_lines,
            r#"theorem all_bodies_safe : ∀ id selected, Trusted.MirSemantics.getElem? Captured.program.bodies id = some selected →
    BodyVerified Captured.program id selected (Spec.specs.safety selected.identity) := by
  intro id _ found
  cases id <;> cases found
theorem verify : Expected.claim :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe, True.intro⟩
end Proof"#,
        );
        let mut proof_lean = proof_lines.join("\n");
        proof_lean.push('\n');
        return Ok(SynthesizedPackage {
            spec_lean,
            proof_lean,
            fn_line_ranges: Vec::new(),
        });
    }

    let patterns: Vec<BodyPattern> = fns.iter().map(classify_body).collect();
    push_block(&mut proof_lines, LEAN_CORE_HELPERS);
    if patterns.contains(&BodyPattern::U32Add) {
        push_block(&mut proof_lines, LEAN_U32_HELPERS);
    }
    if patterns.contains(&BodyPattern::EnumTag) {
        push_block(&mut proof_lines, LEAN_ENUM_HELPERS);
    }

    let mut fn_line_ranges = Vec::new();
    for (i, (f, &pat)) in fns.iter().zip(&patterns).enumerate() {
        let start_line = proof_lines.len() + 1;
        let mut block = String::new();
        let has_pre_guard = safe_pre_guard(f).is_some();
        let guard_intro = if has_pre_guard { " h_ne" } else { "" };
        let _ = writeln!(block, "def body{i} : Body := Captured.program.bodies[{i}]");

        match pat {
            BodyPattern::DirectId(int_ty) => {
                let w = int_ty.width_lean;
                let s = int_ty.signed;
                let ty = int_ty.mir_ty_lean();
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_exec (v : Val) (hv : checkVal v {ty} = true) :
    Executes body{i} (initial body{i} [v]) v := by
  let ⟨bits, hb, _⟩ := checkVal_scalar_inv hv
  subst hb
  let v : Val := .scalar ⟨{w}, {s}, bits⟩
  let sv : SlotVal := .scalar ⟨{w}, {s}, bits⟩
  have s0 : step body{i} (initial body{i} [v]) = .step ⟨[⟨0, 0, 1, [.live sv, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv] ⟨0, []⟩ {ty} v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 1, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  exact .next s0 (.ret rfl)
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) :=
  bodyVerified_of_exec1 rfl rfl rfl (fun v hv => ⟨v, body{i}_exec v hv⟩)"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    if has_pre_guard {
                        let _ = writeln!(
                            block,
                            "theorem body{i}_ens : {ens_ty} :=\n  fun selected found args ret h_valid _ h_beh => ensures_eq_of_exec1 (p := Captured.program) (defId := {i}) (body := body{i}) rfl rfl body{i}_exec selected found args ret h_valid h_beh"
                        );
                    } else {
                        let _ = writeln!(
                            block,
                            "theorem body{i}_ens : {ens_ty} :=\n  ensures_eq_of_exec1 (p := Captured.program) (defId := {i}) (body := body{i}) rfl rfl body{i}_exec"
                        );
                    }
                }
            }
            BodyPattern::ConstZero(out_ty) => {
                let zero_val = out_ty.zero_val_lean();
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_runs (v : Val) :
    Runs body{i} 8 [v] ({zero_val}) := rfl
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  exact (run_initial_success (body{i}_runs v)).1"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  have same : body{i} = selected := Option.some.inj found
  subst selected
  have h_ret : Returns body{i} args ret := (returns_of_behavior found h_beh).2
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  have h_zero : ({zero_val}) = ret := run_result_unique (body{i}_runs v) h_ret
  exact congrArg some h_zero"#
                    );
                }
            }
            BodyPattern::Unproved => {
                // Intentionally emits an ill-typed `exact .ret rfl` proof stub
                // so `cargo-anneal verify` fails at the Lean proof-audit phase
                // for fixtures expecting `//@ fail(proof, <scope>)`.
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_exec (v : Val) :
    Executes body{i} (initial body{i} [v]) v := by
  exact .ret rfl
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  exact executes_safe (body{i}_exec v)"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  have same : body{i} = selected := Option.some.inj found
  subst selected
  have h_ret : Returns body{i} args ret := (returns_of_behavior found h_beh).2
  let ⟨v, h_eq, _⟩ := validArgs1 h_valid
  subst h_eq
  exact congrArg some (executes_unique (body{i}_exec v) h_ret)"#
                    );
                }
            }
            BodyPattern::MoveId(int_ty) => {
                let w = int_ty.width_lean;
                let s = int_ty.signed;
                let ty = int_ty.mir_ty_lean();
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_exec (v : Val) (hv : checkVal v {ty} = true) :
    Executes body{i} (initial body{i} [v]) v := by
  let ⟨bits, hb, _⟩ := checkVal_scalar_inv hv
  subst hb
  let v : Val := .scalar ⟨{w}, {s}, bits⟩
  let sv : SlotVal := .scalar ⟨{w}, {s}, bits⟩
  have s0 : step body{i} (initial body{i} [v]) = .step ⟨[⟨0, 0, 1, [.live .uninit, .live sv, .live .uninit], none⟩], ⟨[]⟩⟩ := rfl
  have s1 : step body{i} ⟨[⟨0, 0, 1, [.live .uninit, .live sv, .live .uninit], none⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 2, [.live .uninit, .live sv, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv, .live .uninit] ⟨2, []⟩ {ty} v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 2, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s2 : step body{i} ⟨[⟨0, 0, 2, [.live .uninit, .live sv, .live sv], none⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 3, [.live sv, .live sv, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv, .live sv] ⟨0, []⟩ {ty} v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 3, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s3 : step body{i} ⟨[⟨0, 0, 3, [.live sv, .live sv, .live sv], none⟩], ⟨[]⟩⟩ = .step ⟨[⟨0, 0, 4, [.live sv, .live sv, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s4 : step body{i} ⟨[⟨0, 0, 4, [.live sv, .live sv, .dead], none⟩], ⟨[]⟩⟩ = .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.ret s4))))
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) :=
  bodyVerified_of_exec1 rfl rfl rfl (fun v hv => ⟨v, body{i}_exec v hv⟩)"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    if has_pre_guard {
                        let _ = writeln!(
                            block,
                            "theorem body{i}_ens : {ens_ty} :=\n  fun selected found args ret h_valid _ h_beh => ensures_eq_of_exec1 (p := Captured.program) (defId := {i}) (body := body{i}) rfl rfl body{i}_exec selected found args ret h_valid h_beh"
                        );
                    } else {
                        let _ = writeln!(
                            block,
                            "theorem body{i}_ens : {ens_ty} :=\n  ensures_eq_of_exec1 (p := Captured.program) (defId := {i}) (body := body{i}) rfl rfl body{i}_exec"
                        );
                    }
                }
            }
            BodyPattern::U32Add => {
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_exec (bits1 bits2 : BitVec 128)
    (hv1 : checkVal (.scalar ⟨.i32, false, bits1⟩) (.int .i32 false) = true)
    (hv2 : checkVal (.scalar ⟨.i32, false, bits2⟩) (.int .i32 false) = true) :
    ∃ outVal, Executes body{i} (initial body{i} [.scalar ⟨.i32, false, bits1⟩, .scalar ⟨.i32, false, bits2⟩]) outVal := by
  let v1 : Val := .scalar ⟨.i32, false, bits1⟩
  let v2 : Val := .scalar ⟨.i32, false, bits2⟩
  let sv1 : SlotVal := .scalar ⟨.i32, false, bits1⟩
  let sv2 : SlotVal := .scalar ⟨.i32, false, bits2⟩
  let raw := bvOfInt 128 (decodeScalar ⟨.i32, false, bits1⟩ + decodeScalar ⟨.i32, false, bits2⟩)
  let outVal : Val := .scalar ⟨.i32, false, truncateBits .i32 raw⟩
  let sout : SlotVal := .scalar ⟨.i32, false, truncateBits .i32 raw⟩
  have hout : checkVal outVal (.int .i32 false) = true := checkVal_u32_truncateBits raw
  refine ⟨outVal, ?_⟩
  have s0 : step body{i} (initial body{i} [v1, v2]) = .step ⟨[⟨0, 0, 1, [.live .uninit, .live sv1, .live sv2, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s1 : step body{i} ⟨[⟨0, 0, 1, [.live .uninit, .live sv1, .live sv2, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 2, [.live .uninit, .live sv1, .live sv2, .live sv1, .dead], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv1, .live sv2, .live .uninit, .dead] ⟨3, []⟩ (.int .i32 false) v1 with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 2, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv1]; rfl
  have s2 : step body{i} ⟨[⟨0, 0, 2, [.live .uninit, .live sv1, .live sv2, .live sv1, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 3, [.live .uninit, .live sv1, .live sv2, .live sv1, .live .uninit], none⟩], ⟨[]⟩⟩ := rfl
  have s3 : step body{i} ⟨[⟨0, 0, 3, [.live .uninit, .live sv1, .live sv2, .live sv1, .live .uninit], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 4, [.live .uninit, .live sv1, .live sv2, .live sv1, .live sv2], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv1, .live sv2, .live sv1, .live .uninit] ⟨4, []⟩ (.int .i32 false) v2 with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 4, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv2]; rfl
  have s4 : step body{i} ⟨[⟨0, 0, 4, [.live .uninit, .live sv1, .live sv2, .live sv1, .live sv2], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 5, [.live sout, .live sv1, .live sv2, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ := by
    change (match (match evalBinOp .add v1 v2 with | .error k => Except.error k | .ok out => (Except.ok (out, [LocalSlot.live .uninit, LocalSlot.live sv1, LocalSlot.live sv2, LocalSlot.live .uninit, LocalSlot.live .uninit]) : Except FaultKind (Val × List LocalSlot))) with | .error k => @StepResult.fault State TerminalOut k | .ok (val, l1) => match writePlace l1 ⟨0, []⟩ (.int .i32 false) val with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 5, l', none⟩], ⟨[]⟩⟩) = _
    rw [evalBinOp_u32_add bits1 bits2]
    change (match writePlace [.live .uninit, .live sv1, .live sv2, .live .uninit, .live .uninit] ⟨0, []⟩ (.int .i32 false) outVal with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 5, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hout]; rfl
  have s5 : step body{i} ⟨[⟨0, 0, 5, [.live sout, .live sv1, .live sv2, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 6, [.live sout, .live sv1, .live sv2, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s6 : step body{i} ⟨[⟨0, 0, 6, [.live sout, .live sv1, .live sv2, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 7, [.live sout, .live sv1, .live sv2, .dead, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s7 : step body{i} ⟨[⟨0, 0, 7, [.live sout, .live sv1, .live sv2, .dead, .dead], none⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨outVal, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6 (.ret s7)))))))
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid _ => ?_)
  let ⟨v1, v2, h_eq, hv1, hv2⟩ := validArgs2 h_valid
  subst h_eq
  let ⟨bits1, hbits1, _⟩ := checkVal_scalar_inv hv1
  let ⟨bits2, hbits2, _⟩ := checkVal_scalar_inv hv2
  subst hbits1; subst hbits2
  let ⟨_, hexec⟩ := body{i}_exec bits1 bits2 hv1 hv2
  exact executes_safe hexec"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    // Intentionally emits an ill-typed `exact h_beh` stub so
                    // unsupported `ensures` obligations on `Add` fixtures fail
                    // at the Lean proof-audit phase.
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  exact h_beh"#
                    );
                }
            }
            BodyPattern::ClampNonzero => {
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_runs_zero :
    Runs body{i} 12 [.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩]
      (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
theorem body{i}_exec_nonzero (bits : BitVec 128)
    (hv : checkVal (.scalar ⟨.isize, false, bits⟩) (.int .isize false) = true)
    (hwf : (truncateBits .isize bits == bits) = true)
    (hne : (bits == BitVec.ofNat 128 0) = false) :
    Executes body{i} (initial body{i} [.scalar ⟨.isize, false, bits⟩]) (.scalar ⟨.isize, false, bits⟩) := by
  let v : Val := .scalar ⟨.isize, false, bits⟩
  let sv : SlotVal := .scalar ⟨.isize, false, bits⟩
  have heq_int : (decodeScalar ⟨.isize, false, bits⟩ == decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = false := by
    unfold decodeScalar
    change (Int.ofNat (truncateBits .isize bits).toNat == Int.ofNat 0) = false
    rw [eq_of_beq hwf]
    cases h0 : (Int.ofNat bits.toNat == Int.ofNat 0) with
    | false => rfl
    | true =>
      have hi : Int.ofNat bits.toNat = Int.ofNat 0 := eq_of_beq h0
      injection hi with hn
      have hb : bits = BitVec.ofNat 128 0 := bitVec_eq_of_toNat_eq hn
      rw [hb] at hne
      cases hne
  have s0 : step body{i} (initial body{i} [v]) = .step ⟨[⟨0, 0, 1, [.live .uninit, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s1 : step body{i} ⟨[⟨0, 0, 1, [.live .uninit, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 2, [.live .uninit, .live sv, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ := rfl
  have s2 : step body{i} ⟨[⟨0, 0, 2, [.live .uninit, .live sv, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 3, [.live .uninit, .live sv, .live .uninit, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv, .live .uninit, .live .uninit] ⟨3, []⟩ (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 3, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s3 : step body{i} ⟨[⟨0, 0, 3, [.live .uninit, .live sv, .live .uninit, .live sv], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 0, 4, [.live .uninit, .live sv, .live (.bool false), .live .uninit], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv, .live .uninit, .live .uninit] ⟨2, []⟩ .bool (.bool (decodeScalar ⟨.isize, false, bits⟩ == decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩)) with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 0, 4, l', none⟩], ⟨[]⟩⟩) = _
    rw [heq_int]; rfl
  have s4 : step body{i} ⟨[⟨0, 0, 4, [.live .uninit, .live sv, .live (.bool false), .live .uninit], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 0, [.live .uninit, .live sv, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ := rfl
  have s5 : step body{i} ⟨[⟨0, 2, 0, [.live .uninit, .live sv, .live .uninit, .live .uninit], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 1, [.live .uninit, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s6 : step body{i} ⟨[⟨0, 2, 1, [.live .uninit, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 2, [.live sv, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv, .live .uninit, .dead] ⟨0, []⟩ (.int .isize false) v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 2, 2, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s7 : step body{i} ⟨[⟨0, 2, 2, [.live sv, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 3, 0, [.live sv, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s8 : step body{i} ⟨[⟨0, 3, 0, [.live sv, .live sv, .live .uninit, .dead], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 3, 1, [.live sv, .live sv, .dead, .dead], none⟩], ⟨[]⟩⟩ := rfl
  have s9 : step body{i} ⟨[⟨0, 3, 1, [.live sv, .live sv, .dead, .dead], none⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.next s2 (.next s3 (.next s4 (.next s5 (.next s6 (.next s7 (.next s8 (.ret s9)))))))))
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
    exact (run_initial_success body{i}_runs_zero).1
  | false =>
    exact executes_safe (body{i}_exec_nonzero bits hv hwf hz)"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let zero_branch = if has_pre_guard {
                        "    exact False.elim (h_ne rfl)".to_owned()
                    } else {
                        format!(
                            "    have h_one : (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) = ret := run_result_unique body{i}_runs_zero h_ret\n    exact congrArg some h_one"
                        )
                    };
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  have same : body{i} = selected := Option.some.inj found
  subst selected
  have h_ret : Returns body{i} args ret := (returns_of_behavior found h_beh).2
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
{zero_branch}
  | false =>
    exact congrArg some (executes_unique (body{i}_exec_nonzero bits hv hwf hz) h_ret)"#
                    );
                }
            }
            BodyPattern::CustomMirNonzero(int_ty) => {
                let w = int_ty.width_lean;
                let s = int_ty.signed;
                let ty = int_ty.mir_ty_lean();
                let _ = writeln!(
                    block,
                    r#"theorem body{i}_exec_nonzero (bits : BitVec 128)
    (hv : checkVal (.scalar ⟨{w}, {s}, bits⟩) {ty} = true)
    (hwf : (truncateBits {w} bits == bits) = true)
    (hne : (bits == BitVec.ofNat 128 0) = false) :
    Executes body{i} (initial body{i} [.scalar ⟨{w}, {s}, bits⟩]) (.scalar ⟨{w}, {s}, bits⟩) := by
  let v : Val := .scalar ⟨{w}, {s}, bits⟩
  let sv : SlotVal := .scalar ⟨{w}, {s}, bits⟩
  have htr : (truncateBits {w} bits == truncateBits {w} (BitVec.ofNat 128 0)) = false := by
    rw [eq_of_beq hwf]
    exact hne
  have s0 : step body{i} (initial body{i} [v]) = .step ⟨[⟨0, 2, 0, [.live .uninit, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match (if (truncateBits {w} bits == truncateBits {w} (BitVec.ofNat 128 0)) then Except.ok 1 else Except.ok 2) with | .error k => @StepResult.fault State TerminalOut k | .ok tgt => jumpToBlock ⟨0, 0, 0, [.live .uninit, .live sv], none⟩ [] ⟨[]⟩ tgt) = _
    rw [htr]; rfl
  have s1 : step body{i} ⟨[⟨0, 2, 0, [.live .uninit, .live sv], none⟩], ⟨[]⟩⟩ =
      .step ⟨[⟨0, 2, 1, [.live sv, .live sv], none⟩], ⟨[]⟩⟩ := by
    change (match writePlace [.live .uninit, .live sv] ⟨0, []⟩ {ty} v with | .error k => @StepResult.fault State TerminalOut k | .ok l' => @StepResult.step State TerminalOut ⟨[⟨0, 2, 1, l', none⟩], ⟨[]⟩⟩) = _
    unfold writePlace; rw [hv]; rfl
  have s2 : step body{i} ⟨[⟨0, 2, 1, [.live sv, .live sv], none⟩], ⟨[]⟩⟩ =
      .done (.returned ⟨v, ⟨[]⟩⟩) := rfl
  exact .next s0 (.next s1 (.ret s2))
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid required => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
    exact False.elim (required rfl rfl)
  | false =>
    exact executes_safe (body{i}_exec_nonzero bits hv hwf hz)"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let zero_branch = if has_pre_guard {
                        "    exact False.elim (h_ne rfl)".to_owned()
                    } else {
                        format!(
                            r#"    let ⟨finish, h_reach, h_done⟩ := h_ret
    have s0 : step body{i} (initial body{i} [.scalar ⟨{w}, {s}, BitVec.ofNat 128 0⟩]) = .step ⟨[⟨0, 1, 0, [.live .uninit, .live (.scalar ⟨{w}, {s}, BitVec.ofNat 128 0⟩)], none⟩], ⟨[]⟩⟩ := rfl
    have s1 : step body{i} ⟨[⟨0, 1, 0, [.live .uninit, .live (.scalar ⟨{w}, {s}, BitVec.ofNat 128 0⟩)], none⟩], ⟨[]⟩⟩ = .fault .undefined := rfl
    cases reach_cases s0 h_reach with
    | inl h_eq => subst h_eq; cases s0.symm.trans h_done
    | inr h_tail =>
      have h_eq := reachable_after_fault s1 h_tail
      subst h_eq
      cases s1.symm.trans h_done"#
                        )
                    };
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  have same : body{i} = selected := Option.some.inj found
  subst selected
  have h_ret : Returns body{i} args ret := (returns_of_behavior found h_beh).2
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  let ⟨bits, hb, hwf⟩ := checkVal_scalar_inv hv
  subst hb
  cases hz : (bits == BitVec.ofNat 128 0) with
  | true =>
    have h0 : bits = BitVec.ofNat 128 0 := eq_of_beq hz
    subst h0
{zero_branch}
  | false =>
    exact congrArg some (executes_unique (body{i}_exec_nonzero bits hv hwf hz) h_ret)"#
                    );
                }
            }
            BodyPattern::EnumTag => {
                let _ = writeln!(
                    block,
                    r#"def body{i}_ety : EnumTy := match body{i}.locals with | _ :: .enum ety :: _ => ety | _ => {{ id := 0, discrWidth := .isize, discrSigned := true, tagRepr := .zeroSized, discriminants := [] }}
theorem body{i}_runs_0 :
    Runs body{i} 10 [.enumVal body{i}_ety 0]
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) := rfl
theorem body{i}_runs_1 :
    Runs body{i} 10 [.enumVal body{i}_ety 1]
      (.scalar ⟨.isize, false, BitVec.ofNat 128 1⟩) := rfl
theorem body{i}_safe : BodyVerified Captured.program {i} body{i} (Spec.specs.safety body{i}.identity) := by
  refine bodyVerified_of_safe rfl rfl (fun args h_valid _ => ?_)
  let ⟨v, h_eq, hv⟩ := validArgs1 h_valid
  subst h_eq
  cases checkVal_enum2_inv (ety := body{i}_ety) rfl hv with
  | inl h0 => subst h0; exact (run_initial_success body{i}_runs_0).1
  | inr h1 => subst h1; exact (run_initial_success body{i}_runs_1).1"#
                );
                if let Some(ens_idx) = f.ensures_eq_param {
                    // Intentionally emits an ill-typed `exact h_beh` stub so
                    // unsupported `ensures` obligations on `Enum2` fixtures
                    // fail at the Lean proof-audit phase.
                    let ens_ty = ensures_clause_lean("Captured.program", i, f, ens_idx);
                    let _ = writeln!(
                        block,
                        r#"theorem body{i}_ens : {ens_ty} := by
  intro selected found args ret h_valid{guard_intro} h_beh
  exact h_beh"#
                    );
                }
            }
        }

        push_block(&mut proof_lines, &block);
        let end_line = proof_lines.len();
        fn_line_ranges.push((start_line, end_line, f.name.clone()));
    }

    // Dispatch all body indices `0..fns.len()` via flat `CheckBodies` tuple.
    let mut safe_tuple = String::from("⟨");
    for i in 0..fns.len() {
        let _ = write!(safe_tuple, "body{i}_safe, ");
    }
    safe_tuple.push_str("True.intro⟩");
    push_block(
        &mut proof_lines,
        &format!(
            "theorem all_bodies_safe : ∀ id selected, Trusted.MirSemantics.getElem? Captured.program.bodies id = some selected → \
             BodyVerified Captured.program id selected (Spec.specs.safety selected.identity) :=\n  all_bodies_safe_of {safe_tuple}"
        ),
    );

    let prop_term = match prop_clauses.len() {
        0 => "True.intro".to_owned(),
        1 => format!("body{}_ens", prop_clauses[0].0),
        _ => {
            let inner = prop_clauses
                .iter()
                .map(|(idx, _)| format!("body{idx}_ens"))
                .collect::<Vec<_>>()
                .join(", ");
            format!("⟨{inner}⟩")
        }
    };
    push_block(
        &mut proof_lines,
        &format!(
            "theorem verify : Expected.claim :=\n  ⟨rfl, rfl, rfl, rfl, rfl, rfl, all_bodies_safe, {prop_term}⟩\nend Proof"
        ),
    );

    let mut proof_lean = proof_lines.join("\n");
    proof_lean.push('\n');
    Ok(SynthesizedPackage {
        spec_lean,
        proof_lean,
        fn_line_ranges,
    })
}

// ---------------------------------------------------------------------------
// End-to-end `cargo-anneal verify --manifest-path` execution & error mapping
// ---------------------------------------------------------------------------

fn keep_sandbox_enabled(val: Option<&OsStr>) -> bool {
    val.is_some_and(|v| v == "1")
}

struct SandboxCrate {
    _root: Option<TempDir>,
    root_path: PathBuf,
    crate_dir: PathBuf,
    proof_dir: PathBuf,
    artifacts_dir: PathBuf,
}

impl SandboxCrate {
    fn new(prefix: &str, rust_source: &str) -> Self {
        let keep = keep_sandbox_enabled(env::var_os("ANNEAL_KEEP_SANDBOX").as_deref());
        Self::new_with_keep(prefix, rust_source, keep)
    }

    fn new_with_keep(prefix: &str, rust_source: &str, keep: bool) -> Self {
        let temp = tempfile::Builder::new()
            .prefix(&format!("anneal-integ-{prefix}-"))
            .tempdir()
            .expect("create integration test sandbox");
        let root_path = temp.path().to_path_buf();
        let root = if keep {
            let _ = temp.keep();
            None
        } else {
            Some(temp)
        };
        let crate_dir = root_path.join("subject");
        let proof_dir = root_path.join("proof");
        let artifacts_dir = root_path.join("artifacts");
        fs::create_dir_all(crate_dir.join("src")).unwrap();
        fs::create_dir_all(&proof_dir).unwrap();
        fs::write(
            crate_dir.join("Cargo.toml"),
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(crate_dir.join("src/lib.rs"), rust_source).unwrap();
        Self {
            _root: root,
            root_path,
            crate_dir,
            proof_dir,
            artifacts_dir,
        }
    }
}

fn parse_capture_detail(detail: &str) -> String {
    if let Ok(env_json) = serde_json::from_str::<Value>(detail) {
        let mut parts = Vec::new();
        if let Some(arr) = env_json["unsupported"].as_array() {
            for item in arr {
                let path = item["path"].as_str().unwrap_or("<item>");
                let reason = item["reason"].as_str().unwrap_or("unsupported");
                parts.push(format!("{path}: {reason}"));
            }
        }
        if let Some(diags) = env_json["diagnostics"].as_array() {
            for d in diags {
                if let Some(s) = d.as_str() {
                    parts.push(s.to_owned());
                }
            }
        }
        if !parts.is_empty() {
            return parts.join("; ");
        }
    }
    detail.to_owned()
}

fn is_proof_lean_file(file_name: &str) -> bool {
    let path = Path::new(file_name);
    if path.file_name().and_then(|n| n.to_str()) != Some("Proof.lean") {
        return false;
    }
    match path.parent() {
        // Bare `"Proof.lean"` has an empty parent; staged Lean sources live
        // directly under `target-src/Proof.lean` (never a submodule such as
        // `target-src/Sub/Proof.lean`).
        None => true,
        Some(parent) if parent.as_os_str().is_empty() => true,
        Some(parent) => parent.file_name().and_then(|n| n.to_str()) == Some("target-src"),
    }
}

fn parse_proof_failure(detail: &str, fn_ranges: &[(usize, usize, String)]) -> (String, String) {
    let mut best_scope = "crate".to_owned();
    let mut messages = Vec::new();
    for line in detail.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        if let Ok(msg) = serde_json::from_str::<Value>(trimmed)
            && msg["severity"].as_str() == Some("error")
        {
            let in_proof_lean = msg["fileName"].as_str().is_some_and(is_proof_lean_file);
            if in_proof_lean && let Some(pos_line) = msg["pos"]["line"].as_u64() {
                let l = pos_line as usize;
                for (start, end, fn_name) in fn_ranges {
                    if l >= *start && l <= *end && best_scope == "crate" {
                        best_scope = fn_name.clone();
                    }
                }
            }
            if let Some(data) = msg["data"].as_str() {
                messages.push(data.to_owned());
            }
        }
    }
    let diag = if messages.is_empty() {
        detail.to_owned()
    } else {
        messages.join("\n")
    };
    (best_scope, diag)
}

fn placeholder_proof_package() -> (String, String) {
    let spec_lean = format!(
        "{LICENSE_HEADER}prelude\n\
         import Trusted.MirSemantics\n\
         \n\
         namespace Spec\n\
         open Trusted.MirAst Trusted.MirSemantics\n\
         \n\
         def specs : Specs where\n\
           safety := fun _ _ => True\n\
           property := fun _ => True\n\
         \n\
         end Spec\n"
    );
    let proof_lean = format!(
        "{LICENSE_HEADER}prelude\n\
         import Expected\n\
         \n\
         namespace Proof\n\
         theorem verify : Expected.claim := Unit.unit\n\
         end Proof\n"
    );
    (spec_lean, proof_lean)
}

fn verify_sandbox(
    tools: &Tools,
    sandbox: &SandboxCrate,
    rust_source: &str,
) -> Result<VerifyReport, VerifyError> {
    verify_sandbox_with_package(tools, sandbox, synthesize_proof_package(rust_source))
}

fn verify_sandbox_with_package(
    tools: &Tools,
    sandbox: &SandboxCrate,
    synth_result: Result<SynthesizedPackage, String>,
) -> Result<VerifyReport, VerifyError> {
    match &synth_result {
        Ok(s) => {
            fs::write(sandbox.proof_dir.join("Spec.lean"), &s.spec_lean).unwrap();
            fs::write(sandbox.proof_dir.join("Proof.lean"), &s.proof_lean).unwrap();
        }
        Err(_) => {
            let (placeholder_spec, placeholder_proof) = placeholder_proof_package();
            fs::write(sandbox.proof_dir.join("Spec.lean"), placeholder_spec).unwrap();
            fs::write(sandbox.proof_dir.join("Proof.lean"), placeholder_proof).unwrap();
        }
    }

    let mut command = tools.command();
    command
        .arg("--manifest-path")
        .arg(sandbox.crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(&sandbox.proof_dir)
        .arg("--artifacts")
        .arg(&sandbox.artifacts_dir);
    let output = tools.run_command(command).map_err(|e| VerifyError {
        message: format!("failed to spawn cargo-anneal: {e}"),
        failure: None,
        mir_lean: None,
    })?;

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let mir_lean = fs::read_to_string(sandbox.artifacts_dir.join("capture/Captured.lean")).ok();

    let receipt: Value = serde_json::from_str(&stdout).map_err(|e| VerifyError {
        message: format!("invalid JSON receipt ({e}):\nstdout:\n{stdout}\nstderr:\n{stderr}"),
        failure: None,
        mir_lean: mir_lean.clone(),
    })?;

    if output.status.success() {
        if let Err(spec_err) = synth_result {
            return Err(VerifyError {
                message: format!(
                    "harness invariant violated: cargo-anneal verify unexpectedly \
                     accepted placeholder Unit.unit proof during spec error \
                     ({spec_err}):\n{stdout}"
                ),
                failure: None,
                mir_lean,
            });
        }
        if receipt["schema_version"] != 2
            || receipt["taint_reasons"] != serde_json::json!([])
            || receipt.get("tainted").is_some()
            || receipt["status"] != "crate_verified"
            || receipt["audit"]["exactType"] != true
            || receipt["audit"]["replay"] != true
        {
            return Err(VerifyError {
                message: format!("unexpected verification receipt:\n{stdout}"),
                failure: None,
                mir_lean,
            });
        }
        let Some(mir_lean) = mir_lean else {
            return Err(VerifyError {
                message: format!(
                    "cargo-anneal verify succeeded without retaining capture/Captured.lean:\n{stdout}"
                ),
                failure: None,
                mir_lean: None,
            });
        };
        return Ok(VerifyReport {
            mir_lean: Some(mir_lean),
            output_text: stdout,
        });
    }

    let status = receipt["status"].as_str().unwrap_or("");
    let phase = receipt["phase"].as_str().unwrap_or("");
    let detail = receipt["detail"].as_str().unwrap_or(&stdout);

    match (status, phase) {
        ("unsupported" | "compiler_failed", "capture" | "cargo" | "inputs" | "request") => {
            let diagnostic = parse_capture_detail(detail);
            Err(VerifyError {
                message: format!("status={status} phase={phase}: {detail}"),
                failure: Some(StageFailure {
                    stage: FailureStage::Capture,
                    diagnostic,
                }),
                mir_lean,
            })
        }
        ("proof_failed", "audit") => match synth_result {
            Ok(synth) => {
                let (scope, diagnostic) = parse_proof_failure(detail, &synth.fn_line_ranges);
                Err(VerifyError {
                    message: format!("status={status} phase={phase}: {detail}"),
                    failure: Some(StageFailure {
                        stage: FailureStage::Proof { scope },
                        diagnostic,
                    }),
                    mir_lean,
                })
            }
            // Real capture succeeded and emitted `Captured.lean`, so now
            // surface the harness's spec-annotation rejection under the
            // dedicated `spec` stage.
            Err(spec_err) => Err(VerifyError {
                message: format!("spec: {spec_err}"),
                failure: Some(StageFailure {
                    stage: FailureStage::Spec,
                    diagnostic: spec_err,
                }),
                mir_lean,
            }),
        },
        _ => Err(VerifyError {
            message: format!("status={status} phase={phase}: {detail}"),
            failure: None,
            mir_lean,
        }),
    }
}

struct JobPool {
    available: Mutex<usize>,
    ready: Condvar,
}

struct JobPermit<'a>(&'a JobPool);

impl JobPool {
    fn new(limit: usize) -> Self {
        Self {
            available: Mutex::new(limit.max(1)),
            ready: Condvar::new(),
        }
    }

    fn acquire(&self) -> JobPermit<'_> {
        let mut available = self
            .available
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        while *available == 0 {
            available = self
                .ready
                .wait(available)
                .unwrap_or_else(|poisoned| poisoned.into_inner());
        }
        *available -= 1;
        JobPermit(self)
    }
}

impl Drop for JobPermit<'_> {
    fn drop(&mut self) {
        let mut available = self
            .0
            .available
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        *available += 1;
        self.0.ready.notify_one();
    }
}

fn acquire_job_permit() -> JobPermit<'static> {
    static POOL: OnceLock<JobPool> = OnceLock::new();
    POOL.get_or_init(|| JobPool::new(fixture_concurrency()))
        .acquire()
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
    let env_threads = env_threads
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n >= 1);
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
    let args: Vec<String> = env::args().collect();
    let jobs_env = match env::var_os("ANNEAL_TEST_JOBS") {
        None => None,
        Some(raw) => match raw.into_string() {
            Ok(s) => Some(s),
            Err(bad) => panic!("ANNEAL_TEST_JOBS must be valid UTF-8, got {bad:?}"),
        },
    };
    let env_threads = env::var("RUST_TEST_THREADS").ok();
    let available = thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(2);
    fixture_concurrency_from(
        &args,
        jobs_env.as_deref(),
        env_threads.as_deref(),
        available,
    )
    .unwrap_or_else(|err| panic!("{err}"))
}

fn dump_failure_bundle(case: &FixtureCase, detail: &str, mir_lean: Option<&str>) -> PathBuf {
    static FAILURE_DIR: OnceLock<PathBuf> = OnceLock::new();
    let root = FAILURE_DIR.get_or_init(|| {
        tempfile::Builder::new()
            .prefix("anneal-test-failures-")
            .tempdir()
            .expect("create process-unique failure bundle directory")
            .keep()
    });
    let dir = root.join(&case.suite).join(&case.name);
    let _ = fs::create_dir_all(&dir);
    let _ = fs::write(dir.join("lib.rs"), &case.source);
    let _ = fs::write(dir.join("failure.txt"), detail);
    if let Some(mir) = mir_lean {
        let _ = fs::write(dir.join("Captured.lean"), mir);
    }
    dir
}

// ---------------------------------------------------------------------------
// Declarative fixture corpus runner
// ---------------------------------------------------------------------------

#[test]
fn verifies_fixture_corpus() {
    let tools = Arc::new(Tools::discover());
    let fixtures_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut fixture_files = Vec::new();
    for entry in fs::read_dir(&fixtures_dir).expect("read tests/fixtures") {
        let entry = entry.unwrap();
        let path = entry.path();
        // Subdirectories (`scalar`, `spin`, `starnix`, `unsafe_identity`)
        // belong to `mvp_e2e.rs` and `ci/verify_starnix_e2e.py`.
        if path.is_file() && path.extension().is_some_and(|e| e == "rs") {
            fixture_files.push(path);
        }
    }
    fixture_files.sort();
    assert!(
        !fixture_files.is_empty(),
        "no declarative `.rs` fixtures found in {}",
        fixtures_dir.display()
    );

    let filter = env::var("ANNEAL_TEST_FILTER")
        .ok()
        .filter(|s| !s.is_empty());
    let bless = env::var("ANNEAL_BLESS").ok().as_deref() == Some("1");

    let mut all_cases = Vec::new();
    for path in &fixture_files {
        let suite = path.file_stem().unwrap().to_string_lossy().into_owned();
        let content = fs::read_to_string(path).unwrap();
        let mut parsed = parse_fixture_file(&suite, path, &content)
            .unwrap_or_else(|e| panic!("fixture parse error: {e}"));
        if let Some(f) = &filter {
            parsed.retain(|c| c.full_name().contains(f));
        }
        all_cases.extend(parsed);
    }
    assert!(
        !all_cases.is_empty(),
        "no fixture cases matched filter {filter:?}"
    );

    let concurrency = fixture_concurrency().min(all_cases.len().max(1));
    let queue = Arc::new(Mutex::new(all_cases.into_iter()));
    let patches = Arc::new(Mutex::new(Vec::new()));
    let failures = Arc::new(Mutex::new(Vec::new()));

    let mut handles = Vec::with_capacity(concurrency);
    for _ in 0..concurrency {
        let tools = Arc::clone(&tools);
        let queue = Arc::clone(&queue);
        let patches = Arc::clone(&patches);
        let failures = Arc::clone(&failures);
        handles.push(thread::spawn(move || {
            while let Some(case) = {
                let mut q = queue.lock().unwrap();
                q.next()
            } {
                let sandbox = SandboxCrate::new(&case.name, &case.source);
                let res = verify_sandbox(&tools, &sandbox, &case.source);
                let mir_ref = match &res {
                    Ok(r) => r.mir_lean.as_deref(),
                    Err(e) => e.mir_lean.as_deref(),
                };
                match evaluate_case(&case, &res, bless) {
                    CaseOutcome::Passed => {}
                    CaseOutcome::Blessed(patch) => {
                        patches.lock().unwrap().push(patch);
                    }
                    CaseOutcome::Failed(reason) => {
                        let dump = dump_failure_bundle(&case, &reason, mir_ref);
                        failures.lock().unwrap().push(format!(
                            "=== FAIL {} ({}:{}) ===\n{reason}\n(bundle saved at {})\n",
                            case.full_name(),
                            case.file_path.display(),
                            case.primary_line_idx + 1,
                            dump.display()
                        ));
                    }
                }
            }
        }));
    }
    for h in handles {
        h.join().expect("fixture worker thread panicked");
    }

    let patches = Arc::try_unwrap(patches).unwrap().into_inner().unwrap();
    if !patches.is_empty() {
        apply_bless_patches(&patches).expect("apply ANNEAL_BLESS patches");
    }

    let failures = Arc::try_unwrap(failures).unwrap().into_inner().unwrap();
    assert!(
        failures.is_empty(),
        "{} declarative fixture case(s) failed:\n\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Parser fail-closed & polarity-safe bless unit tests
// ---------------------------------------------------------------------------

#[test]
fn rejects_malformed_fixture_directives() {
    let dummy = Path::new("dummy.rs");
    for (label, bad_src, expected_err) in [
        (
            "unknown-directive",
            "//@ pass\n//@ unknown-flag: true\npub fn id(x: usize) -> usize { x }\n",
            "unknown directive",
        ),
        (
            "missing-primary",
            "//@ mir-contains: \"foo\"\npub fn id(x: usize) -> usize { x }\n",
            "missing primary expectation directive",
        ),
        (
            "duplicate-primary",
            "//@ pass\n//@ fail(capture): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "multiple primary expectation directives",
        ),
        (
            "proof-missing-scope",
            "//@ fail(proof): \"unproved\"\npub fn id(x: usize) -> usize { x }\n",
            "`proof` stage requires a scope",
        ),
        (
            "capture-with-scope",
            "//@ fail(capture, id): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "`capture` stage does not take a scope",
        ),
        (
            "spec-with-scope",
            "//@ fail(spec, id): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "`spec` stage does not take a scope",
        ),
        (
            "mir-contains-on-capture-fail",
            "//@ fail(capture): \"err\"\n//@ mir-contains: \"foo\"\npub fn id(x: usize) -> usize { x }\n",
            "cannot be used on `capture`-stage failures",
        ),
        (
            "known-bug-bad-issue",
            "//@ known_bug(123, proof, id): \"unproved\"\npub fn id(x: usize) -> usize { x }\n",
            "invalid issue reference",
        ),
        (
            "known-bug-zero-issue",
            "//@ known_bug(#0, capture): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "invalid issue reference",
        ),
        (
            "known-bug-missing-stage",
            "//@ known_bug(#123): \"err\"\npub fn id(x: usize) -> usize { x }\n",
            "`known_bug` requires `(#<issue>, <stage>)`",
        ),
        (
            "known-bug-capture-with-mir-not-contains",
            "//@ known_bug(#123, capture): \"err\"\n//@ mir-not-contains: \"foo\"\npub fn id(x: usize) -> usize { x }\n",
            "cannot be used on `capture`-stage failures",
        ),
        (
            "empty-mir-contains",
            "//@ pass\n//@ mir-contains: \"\"\npub fn id(x: usize) -> usize { x }\n",
            "expected non-empty string literal",
        ),
        (
            "empty-mir-not-contains",
            "//@ pass\n//@ mir-not-contains: \"\"\npub fn id(x: usize) -> usize { x }\n",
            "expected non-empty string literal",
        ),
    ] {
        let err = parse_fixture_file("dummy", dummy, bad_src)
            .expect_err(&format!("expected `{label}` to fail parsing"));
        assert!(
            err.contains(expected_err),
            "{label}: expected error containing {expected_err:?}, got: {err}"
        );
    }

    // `fail(spec)` parses cleanly and permits `mir-contains` since real capture
    // runs before reporting spec-parser errors.
    let spec_case = parse_fixture_file(
        "dummy",
        dummy,
        "//@ fail(spec): \"unknown identifier\"\n//@ mir-contains: \"def program\"\npub fn id(x: usize) -> usize { x }\n",
    )
    .expect("expected fail(spec) with mir-contains to parse");
    assert_eq!(spec_case.len(), 1);
    assert_eq!(
        spec_case[0].expectation,
        PrimaryExpectation::Fail {
            stage: FailureStage::Spec,
            substring: "unknown identifier".to_owned(),
        }
    );

    // `known_bug` parses cleanly across `capture`, `spec`, and `proof` stages.
    let kb_spec = parse_fixture_file(
        "dummy",
        dummy,
        "//@ known_bug(#123, spec): \"unsupported spec\"\n//@ mir-not-contains: \"unreachable\"\npub fn id(x: usize) -> usize { x }\n",
    )
    .expect("expected known_bug(spec) with mir-not-contains to parse");
    assert_eq!(kb_spec.len(), 1);
    assert_eq!(
        kb_spec[0].expectation,
        PrimaryExpectation::KnownBug {
            issue: 123,
            stage: FailureStage::Spec,
            substring: "unsupported spec".to_owned(),
        }
    );
}

#[test]
fn bless_updates_expectation_and_promotes_resolved_known_bug_without_flipping_polarity() {
    let tmp = tempfile::Builder::new()
        .prefix("anneal-bless-test-")
        .tempdir()
        .unwrap();
    let fixture_path = tmp.path().join("sample_bless.rs");
    let initial = "\
// === case: stale_proof_msg ===
//@ fail(proof, wrong_scope): \"outdated message\"
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: resolved_known_bug ===
//@ known_bug(#123, proof, id): \"unproved function body\"
pub fn id(x: usize) -> usize {
    x
}

// === case: broken_pass_never_auto_flipped ===
//@ pass
pub fn id(x: usize) -> usize {
    let _ = x;
    0
}

// === case: stale_known_bug_msg ===
//@ known_bug(#123, capture): \"old capture error\"
pub fn id(x: usize) -> usize {
    x
}
";
    fs::write(&fixture_path, initial).unwrap();
    let cases = parse_fixture_file("sample_bless", &fixture_path, initial).unwrap();
    assert_eq!(cases.len(), 4);

    let mut patches = Vec::new();
    let proof_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "status=proof_failed phase=audit: mismatch".to_owned(),
        failure: Some(StageFailure {
            stage: FailureStage::Proof {
                scope: "id".to_owned(),
            },
            diagnostic: "Type mismatch".to_owned(),
        }),
        mir_lean: Some("-- captured Captured.lean".to_owned()),
    });
    let capture_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "status=unsupported phase=capture: new capture error".to_owned(),
        failure: Some(StageFailure {
            stage: FailureStage::Capture,
            diagnostic: "new capture error".to_owned(),
        }),
        mir_lean: None,
    });
    let operational_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "status=tool_failed phase=audit: lean crashed".to_owned(),
        failure: None,
        mir_lean: None,
    });
    let pass_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: Some("-- captured Captured.lean".to_owned()),
        output_text: String::new(),
    });

    match evaluate_case(&cases[0], &proof_err, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!("expected Blessed for stale_proof_msg, got {other:?}"),
    }
    match evaluate_case(&cases[1], &pass_ok, false) {
        CaseOutcome::Failed(msg) => assert!(
            msg.contains("`known_bug(#123)` now passes!"),
            "expected resolved known_bug error when bless=false, got: {msg}"
        ),
        other => panic!("expected Failed for resolved_known_bug without bless, got {other:?}"),
    }
    match evaluate_case(&cases[1], &pass_ok, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!("expected Blessed for resolved_known_bug, got {other:?}"),
    }
    assert!(
        matches!(
            evaluate_case(&cases[2], &proof_err, true),
            CaseOutcome::Failed(_)
        ),
        "expected broken `//@ pass` case to fail even when bless=true"
    );
    // Matching `known_bug` passes; mismatching fails when bless=false, updates
    // in place preserving `#123` when bless=true, and operational errors never
    // bless.
    let matching_capture_err: Result<VerifyReport, VerifyError> = Err(VerifyError {
        message: "status=unsupported phase=capture: old capture error".to_owned(),
        failure: Some(StageFailure {
            stage: FailureStage::Capture,
            diagnostic: "old capture error".to_owned(),
        }),
        mir_lean: None,
    });
    assert!(
        matches!(
            evaluate_case(&cases[3], &matching_capture_err, false),
            CaseOutcome::Passed
        ),
        "expected matching known_bug failure to pass"
    );
    assert!(
        matches!(
            evaluate_case(&cases[3], &capture_err, false),
            CaseOutcome::Failed(ref msg) if msg.contains("known_bug(#123) mismatch")
        ),
        "expected mismatching known_bug failure to report mismatch when bless=false"
    );
    assert!(
        matches!(
            evaluate_case(&cases[3], &operational_err, true),
            CaseOutcome::Failed(_)
        ),
        "expected operational error on known_bug to fail even when bless=true"
    );
    match evaluate_case(&cases[3], &capture_err, true) {
        CaseOutcome::Blessed(p) => patches.push(p),
        other => panic!("expected Blessed for stale_known_bug_msg, got {other:?}"),
    }

    apply_bless_patches(&patches).unwrap();
    let updated = fs::read_to_string(&fixture_path).unwrap();
    assert!(
        updated.contains("//@ fail(proof, id): \"Type mismatch\""),
        "expected updated proof scope and message, got:\n{updated}"
    );
    assert!(
        updated.contains("// === case: resolved_known_bug ===\n//@ pass\n"),
        "expected resolved known_bug to promote to `//@ pass`, got:\n{updated}"
    );
    assert!(
        updated.contains("//@ known_bug(#123, capture): \"new capture error\""),
        "expected updated known_bug preserving issue #123, got:\n{updated}"
    );
}

// ---------------------------------------------------------------------------
// Host-boundary, staging, and environment-scrubbing tests
// ---------------------------------------------------------------------------

fn receipt_capture_sha256(output_text: &str) -> String {
    let receipt: Value = serde_json::from_str(output_text).expect("parse verified receipt JSON");
    let top = receipt["capture_sha256"]
        .as_str()
        .expect("verified receipt must include capture_sha256")
        .to_owned();
    let bound = receipt["audit"]["bindings"]["captureSha256"]
        .as_str()
        .expect("verified receipt audit bindings must include captureSha256");
    assert_eq!(
        top, bound,
        "receipt capture_sha256 must match audit.bindings.captureSha256"
    );
    assert!(
        cargo_anneal::is_sha256_hex(&top),
        "capture_sha256 must be a valid SHA-256 hex digest, got {top:?}"
    );
    top
}

fn retained_audit_capture_sha256(artifacts_dir: &Path) -> String {
    let raw = fs::read_to_string(artifacts_dir.join("audit-request.json"))
        .expect("read retained audit-request.json");
    let req: Value = serde_json::from_str(&raw).expect("parse retained audit-request.json");
    let sha = req["bindings"]["captureSha256"]
        .as_str()
        .expect("audit-request.json must include bindings.captureSha256")
        .to_owned();
    assert!(
        cargo_anneal::is_sha256_hex(&sha),
        "retained captureSha256 must be a valid SHA-256 hex digest, got {sha:?}"
    );
    let actual_capture_json = fs::read(artifacts_dir.join("capture/capture.json"))
        .expect("read retained capture/capture.json");
    assert_eq!(
        sha,
        cargo_anneal::sha256_bytes(&actual_capture_json),
        "audit-request captureSha256 must hash this run's fresh capture/capture.json"
    );
    sha
}

fn retained_captured_module_sha256(artifacts_dir: &Path) -> String {
    let raw = fs::read_to_string(artifacts_dir.join("audit-request.json"))
        .expect("read retained audit-request.json");
    let req: Value = serde_json::from_str(&raw).expect("parse retained audit-request.json");
    let sha = req["modules"]
        .as_array()
        .expect("audit-request.json modules array")
        .iter()
        .find(|m| m["module"].as_str() == Some("Captured"))
        .and_then(|m| m["expectedSha256"].as_str())
        .expect("audit-request.json must include Captured module expectedSha256")
        .to_owned();
    assert!(
        cargo_anneal::is_sha256_hex(&sha),
        "Captured expectedSha256 must be a valid SHA-256 hex digest, got {sha:?}"
    );
    sha
}

fn capture_json_semantic_fingerprint(artifacts_dir: &Path) -> Value {
    let raw = fs::read_to_string(artifacts_dir.join("capture/capture.json"))
        .expect("read retained capture/capture.json");
    let manifest: Value = serde_json::from_str(&raw).expect("parse retained capture/capture.json");
    // `capture.json` includes the random per-run stage path under
    // `source_files` and `configuration`; compare its path-independent program,
    // census, selected set, and source-file SHA-256 digests across runs.
    let source_hashes: Vec<String> = manifest["source_files"]
        .as_array()
        .expect("capture.json source_files array")
        .iter()
        .map(|s| {
            s["sha256"]
                .as_str()
                .expect("capture.json source_file sha256")
                .to_owned()
        })
        .collect();
    serde_json::json!({
        "program": manifest["program"],
        "census": manifest["census"],
        "selected": manifest["selected"],
        "source_hashes": source_hashes,
    })
}

fn compile_real_verifying_oleans(
    tools: &Tools,
    baseline_artifacts: &Path,
) -> (cargo_anneal::Checker, PathBuf) {
    let raw = fs::read_to_string(baseline_artifacts.join("audit-request.json"))
        .expect("read baseline audit-request.json");
    let mut req: cargo_anneal::TargetAuditRequest =
        serde_json::from_str(&raw).expect("deserialize baseline TargetAuditRequest");
    let expected_src = req
        .modules
        .iter()
        .find(|m| m.module == "Expected")
        .expect("baseline request must contain Expected module")
        .source
        .clone();
    // `Expected` is staged at `<work>/generated/Expected.lean`, so its
    // grandparent is `<work>`. Remap every module source to the retained copy.
    let orig_work = expected_src
        .parent()
        .and_then(Path::parent)
        .expect("Expected source path must have <work>/generated parent");
    for module in &mut req.modules {
        let rel = module
            .source
            .strip_prefix(orig_work)
            .expect("module source must live inside original stage");
        module.source = baseline_artifacts.join(rel);
    }

    let mut checker =
        cargo_anneal::Checker::new(&baseline_artifacts.join("anneal"), Some(&tools.lean))
            .expect("construct Checker over retained bundle");
    let audit = {
        let _permit = acquire_job_permit();
        checker
            .run_target(&req)
            .expect("compile genuine verifying .olean artifacts")
    };
    assert_eq!(audit["exactType"], true);
    assert_eq!(audit["replay"], true);

    let target_lib = checker.stage().join("target-lib");
    for stem in ["Captured", "Spec", "Expected", "Proof"] {
        let olean = target_lib.join(format!("{stem}.olean"));
        let meta = fs::metadata(&olean)
            .unwrap_or_else(|e| panic!("expected compiled {}: {e}", olean.display()));
        assert!(
            meta.len() > 0,
            "compiled {} must be non-empty",
            olean.display()
        );
    }
    (checker, target_lib)
}

fn copy_compiled_module_artifacts(src_dir: &Path, dst_dir: &Path, stems: &[&str]) -> Vec<String> {
    fs::create_dir_all(dst_dir).unwrap();
    let mut copied = Vec::new();
    for entry in fs::read_dir(src_dir).expect("read compiled target-lib") {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        }
        let name = entry.file_name().to_string_lossy().into_owned();
        if stems
            .iter()
            .any(|stem| name.starts_with(&format!("{stem}.")))
        {
            fs::copy(entry.path(), dst_dir.join(&name)).unwrap();
            copied.push(name);
        }
    }
    copied.sort();
    assert!(
        copied.iter().any(|n| n == "Proof.olean") && copied.iter().any(|n| n == "Captured.olean"),
        "expected Proof.olean and Captured.olean in copied artifacts, got {copied:?}"
    );
    copied
}

#[test]
fn ignores_tampered_or_spoofed_files_in_dot_anneal_and_proof_olean() {
    let tools = Tools::discover();
    let good_src = "/// anneal:spec ensures(ret == x)\n\
                    pub fn id(x: usize) -> usize {\n    x\n}\n";
    let bad_src = "/// anneal:spec ensures(ret == x)\n\
                   pub fn id(x: usize) -> usize {\n    let _ = x;\n    0\n}\n";
    let good_synth = synthesize_proof_package(good_src).unwrap();

    // Unspoofed verifying baseline: record its capture digest, real
    // `Captured.lean` / `capture.json` / `Expected.lean`, and compile genuine
    // kernel-valid `.olean` artifacts for the verifying package.
    let good_baseline = SandboxCrate::new("spoof-good-baseline", good_src);
    let good_base_report = verify_sandbox(&tools, &good_baseline, good_src)
        .expect("unspoofed good baseline must verify");
    let good_capture_sha256 = receipt_capture_sha256(&good_base_report.output_text);
    assert_eq!(
        retained_audit_capture_sha256(&good_baseline.artifacts_dir),
        good_capture_sha256
    );
    let good_captured_module_sha256 = retained_captured_module_sha256(&good_baseline.artifacts_dir);
    let good_fingerprint = capture_json_semantic_fingerprint(&good_baseline.artifacts_dir);
    let good_captured_lean =
        fs::read_to_string(good_baseline.artifacts_dir.join("capture/Captured.lean")).unwrap();
    let good_capture_json =
        fs::read_to_string(good_baseline.artifacts_dir.join("capture/capture.json")).unwrap();
    let good_expected_lean =
        fs::read_to_string(good_baseline.artifacts_dir.join("generated/Expected.lean")).unwrap();
    let (_checker, good_target_lib) =
        compile_real_verifying_oleans(&tools, &good_baseline.artifacts_dir);

    // Direction (a): verifying ("good") program with BREAKING spoofs placed in
    // `proof_dir/`, `proof_dir/.anneal/`, and `crate_dir/.anneal/`. If any of
    // these spoofs were honored, compilation or verification would fail.
    let good_spoofed = SandboxCrate::new("spoof-good-breaking", good_src);
    let breaking_captured = "prelude\nimport Trusted.MirAst\nnamespace Captured\n\
                             def program : Trusted.MirAst.Program := { bodies := [] }\n\
                             end Captured\n";
    let invalid_lean = "this is intentionally invalid Lean syntax !!!\n";
    let copied_names = copy_compiled_module_artifacts(
        &good_target_lib,
        &good_spoofed.proof_dir,
        &["Captured", "Spec", "Expected", "Proof"],
    );
    // Overwrite every adjacent compiled artifact in `proof_dir/` and
    // `proof_dir/.anneal/` with corrupt bytes.
    fs::create_dir_all(good_spoofed.proof_dir.join(".anneal")).unwrap();
    for name in &copied_names {
        fs::write(good_spoofed.proof_dir.join(name), b"corrupt olean bytes").unwrap();
        fs::write(
            good_spoofed.proof_dir.join(".anneal").join(name),
            b"corrupt olean bytes",
        )
        .unwrap();
    }
    fs::write(
        good_spoofed.proof_dir.join(".anneal/Captured.lean"),
        breaking_captured,
    )
    .unwrap();
    fs::write(
        good_spoofed.proof_dir.join(".anneal/Proof.lean"),
        invalid_lean,
    )
    .unwrap();
    fs::write(
        good_spoofed.proof_dir.join(".anneal/Spec.lean"),
        invalid_lean,
    )
    .unwrap();
    fs::write(
        good_spoofed.proof_dir.join(".anneal/capture.json"),
        b"{not json",
    )
    .unwrap();

    fs::create_dir_all(good_spoofed.crate_dir.join(".anneal")).unwrap();
    fs::write(
        good_spoofed.crate_dir.join(".anneal/Captured.lean"),
        breaking_captured,
    )
    .unwrap();
    fs::write(
        good_spoofed.crate_dir.join(".anneal/Proof.lean"),
        invalid_lean,
    )
    .unwrap();
    fs::write(
        good_spoofed.crate_dir.join(".anneal/capture.json"),
        b"{not json",
    )
    .unwrap();
    fs::write(
        good_spoofed.crate_dir.join(".anneal/poison.rs"),
        b"this is intentionally invalid Rust syntax !!!\n",
    )
    .unwrap();

    let good_spoof_report = verify_sandbox(&tools, &good_spoofed, good_src)
        .expect("verifying program must still succeed despite breaking spoofs");
    let good_spoof_capture_sha256 = receipt_capture_sha256(&good_spoof_report.output_text);
    assert_eq!(
        retained_audit_capture_sha256(&good_spoofed.artifacts_dir),
        good_spoof_capture_sha256,
        "good spoofed capture_sha256 must match its own freshly captured capture.json"
    );
    assert_ne!(
        good_spoof_capture_sha256,
        cargo_anneal::sha256_bytes(b"{not json"),
        "good spoofed capture_sha256 must not hash spoofed .anneal/capture.json"
    );
    let good_spoof_receipt: Value = serde_json::from_str(&good_spoof_report.output_text).unwrap();
    assert_eq!(
        good_spoof_receipt["audit"]["moduleIdentities"]["Captured"]["sourceSha256"].as_str(),
        Some(good_captured_module_sha256.as_str()),
        "good spoofed Captured.lean sourceSha256 must match unspoofed good baseline"
    );
    assert_eq!(
        retained_captured_module_sha256(&good_spoofed.artifacts_dir),
        good_captured_module_sha256,
        "good spoofed Captured expectedSha256 must match unspoofed good baseline"
    );
    assert_eq!(
        capture_json_semantic_fingerprint(&good_spoofed.artifacts_dir),
        good_fingerprint,
        "good spoofed capture.json content must match unspoofed good baseline"
    );
    assert_eq!(
        good_spoof_report.mir_lean.as_deref(),
        Some(good_captured_lean.as_str()),
        "good spoofed Captured.lean must match unspoofed good baseline"
    );

    // Unspoofed failing baseline using `good_synth` (the proof that genuinely
    // verifies `good_captured_lean`): proves `bad_src` fails at `Proof { id }`
    // with its own capture digest distinct from `good_capture_sha256`.
    let bad_baseline = SandboxCrate::new("spoof-bad-baseline", bad_src);
    let bad_base_err = verify_sandbox_with_package(
        &tools,
        &bad_baseline,
        Ok(SynthesizedPackage {
            spec_lean: good_synth.spec_lean.clone(),
            proof_lean: good_synth.proof_lean.clone(),
            fn_line_ranges: good_synth.fn_line_ranges.clone(),
        }),
    )
    .unwrap_err();
    assert_eq!(
        bad_base_err.failure.as_ref().map(|f| &f.stage),
        Some(&FailureStage::Proof {
            scope: "id".to_owned(),
        }),
        "unspoofed bad baseline must fail at Proof{{id}}, got: {bad_base_err}"
    );
    let bad_capture_sha256 = retained_audit_capture_sha256(&bad_baseline.artifacts_dir);
    let bad_captured_module_sha256 = retained_captured_module_sha256(&bad_baseline.artifacts_dir);
    let bad_fingerprint = capture_json_semantic_fingerprint(&bad_baseline.artifacts_dir);
    let bad_captured_lean =
        fs::read_to_string(bad_baseline.artifacts_dir.join("capture/Captured.lean")).unwrap();
    assert_ne!(
        bad_capture_sha256, good_capture_sha256,
        "bad and good programs must produce distinct capture_sha256 digests"
    );
    assert_ne!(
        bad_captured_module_sha256, good_captured_module_sha256,
        "bad and good programs must produce distinct Captured.lean digests"
    );
    assert_ne!(
        bad_fingerprint, good_fingerprint,
        "bad and good programs must produce distinct capture.json payloads"
    );
    assert_ne!(
        bad_captured_lean, good_captured_lean,
        "bad and good programs must produce distinct Captured.lean outputs"
    );

    // Direction (b): failing ("bad") program paired with `good_synth` AND
    // GENUINE ENABLING spoofs copied from the real verifying `good_baseline`
    // (`Captured.lean`, `capture.json`, `Expected.lean`, `Spec.lean`,
    // `Proof.lean`, and precompiled `{Captured,Spec,Expected,Proof}.olean`
    // artifacts in `proof_dir/`, `proof_dir/.anneal/`, and
    // `crate_dir/.anneal/`). Honoring either the spoofed `Captured.lean` or
    // the spoofed precompiled `.olean`s would falsely yield `crate_verified`.
    let bad_spoofed = SandboxCrate::new("spoof-bad-enabling", bad_src);
    let stems = ["Captured", "Spec", "Expected", "Proof"];
    copy_compiled_module_artifacts(&good_target_lib, &bad_spoofed.proof_dir, &stems);
    copy_compiled_module_artifacts(
        &good_target_lib,
        &bad_spoofed.proof_dir.join(".anneal"),
        &stems,
    );
    copy_compiled_module_artifacts(
        &good_target_lib,
        &bad_spoofed.crate_dir.join(".anneal"),
        &stems,
    );
    for dot_anneal in [
        bad_spoofed.proof_dir.join(".anneal"),
        bad_spoofed.crate_dir.join(".anneal"),
    ] {
        fs::write(dot_anneal.join("Captured.lean"), &good_captured_lean).unwrap();
        fs::write(dot_anneal.join("capture.json"), &good_capture_json).unwrap();
        fs::write(dot_anneal.join("Spec.lean"), &good_synth.spec_lean).unwrap();
        fs::write(dot_anneal.join("Proof.lean"), &good_synth.proof_lean).unwrap();
        fs::write(dot_anneal.join("Expected.lean"), &good_expected_lean).unwrap();
    }
    fs::write(bad_spoofed.crate_dir.join(".anneal/lib.rs"), good_src).unwrap();

    let bad_spoof_err = verify_sandbox_with_package(&tools, &bad_spoofed, Ok(good_synth))
        .expect_err("bad program must still be rejected despite genuine enabling spoofs");
    assert_eq!(
        bad_spoof_err.failure.as_ref().map(|f| &f.stage),
        Some(&FailureStage::Proof {
            scope: "id".to_owned(),
        }),
        "expected Proof{{id}} rejection despite genuine enabling spoofs, got: {bad_spoof_err}"
    );
    let bad_spoof_capture_sha256 = retained_audit_capture_sha256(&bad_spoofed.artifacts_dir);
    assert_ne!(
        bad_spoof_capture_sha256, good_capture_sha256,
        "bad spoofed capture_sha256 must not match the spoofed good capture.json"
    );
    assert_eq!(
        retained_captured_module_sha256(&bad_spoofed.artifacts_dir),
        bad_captured_module_sha256,
        "bad spoofed Captured.lean digest must match unspoofed bad baseline"
    );
    assert_eq!(
        capture_json_semantic_fingerprint(&bad_spoofed.artifacts_dir),
        bad_fingerprint,
        "bad spoofed capture.json content must match unspoofed bad baseline"
    );
    assert_eq!(
        bad_spoof_err.mir_lean.as_deref(),
        Some(bad_captured_lean.as_str()),
        "bad spoofed Captured.lean must match unspoofed bad baseline"
    );
}

#[test]
fn rejects_symlinked_sources_and_disallowed_manifest_targets() {
    let tools = Tools::discover();
    let ok_src = "pub fn id(x: usize) -> usize { x }\n";

    // 1. Symlinked `src/lib.rs` must not be staged via `--manifest-path`, and
    // must be rejected as `not a declared regular file` via `--request`.
    {
        let sandbox = SandboxCrate::new("symlink-lib", ok_src);
        let real_lib = sandbox.root_path.join("real_lib.rs");
        fs::rename(sandbox.crate_dir.join("src/lib.rs"), &real_lib).unwrap();
        symlink(&real_lib, sandbox.crate_dir.join("src/lib.rs")).unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("unsupported or empty compilation request"),
            "expected symlinked src/lib.rs manifest rejection, got: {err}"
        );

        let req_path = sandbox.root_path.join("request.json");
        let req = serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": sandbox.crate_dir,
                "crate_root": "src/lib.rs",
                "crate_name": "sample",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["src/lib.rs"],
            },
            "scope": { "kind": "crate" },
            "proof": {
                "source_root": sandbox.proof_dir,
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ]
            }
        });
        fs::write(&req_path, serde_json::to_vec_pretty(&req).unwrap()).unwrap();
        let mut cmd = tools.command();
        cmd.arg("--request").arg(&req_path);
        let out = tools.run_command(cmd).unwrap();
        assert!(!out.status.success());
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(
            stdout.contains("not a declared regular file"),
            "expected symlinked src/lib.rs request rejection, got:\n{stdout}"
        );
    }

    // 2. Symlinked `proof/Proof.lean` must not be staged (`WalkDir` does not
    // follow links, so `Proof` is omitted and rejected as
    // `unsupported`/`proof`).
    {
        let sandbox = SandboxCrate::new("symlink-proof", ok_src);
        let synth = synthesize_proof_package(ok_src).unwrap();
        fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
        let real_proof = sandbox.root_path.join("RealProof.lean");
        fs::write(&real_proof, &synth.proof_lean).unwrap();
        symlink(&real_proof, sandbox.proof_dir.join("Proof.lean")).unwrap();
        let mut cmd = tools.command();
        cmd.arg("--manifest-path")
            .arg(sandbox.crate_dir.join("Cargo.toml"))
            .arg("--proof-dir")
            .arg(&sandbox.proof_dir);
        let output = tools.run_command(cmd).unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            !output.status.success(),
            "expected symlinked Proof.lean to fail verification:\n{stdout}"
        );
        let receipt: Value = serde_json::from_str(&stdout)
            .unwrap_or_else(|e| panic!("expected JSON failure receipt ({e}):\n{stdout}"));
        assert_eq!(
            receipt["status"], "unsupported",
            "expected status=unsupported for symlinked Proof.lean:\n{stdout}"
        );
        assert_eq!(
            receipt["phase"], "proof",
            "expected phase=proof for symlinked Proof.lean:\n{stdout}"
        );
        assert_eq!(
            receipt["detail"], "specification and theorem must have their declared source roles",
            "expected declared source role rejection for symlinked Proof.lean:\n{stdout}"
        );
    }

    // 3. `build.rs` custom-build target must be rejected.
    {
        let sandbox = SandboxCrate::new("build-rs", ok_src);
        fs::write(sandbox.crate_dir.join("build.rs"), "fn main() {}\n").unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message.contains(
                "build scripts and procedural macros need an explicit configured compilation"
            ),
            "expected build.rs rejection, got: {err}"
        );
    }

    // 4. Binary-only crate (no library target) must be rejected.
    {
        let sandbox = SandboxCrate::new("bin-only", ok_src);
        fs::remove_file(sandbox.crate_dir.join("src/lib.rs")).unwrap();
        fs::write(sandbox.crate_dir.join("src/main.rs"), "fn main() {}\n").unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("Cargo shortcut requires a library target"),
            "expected binary-only rejection, got: {err}"
        );
    }

    // 5. Cargo `[features]` must be rejected.
    {
        let sandbox = SandboxCrate::new("cargo-features", ok_src);
        fs::write(
            sandbox.crate_dir.join("Cargo.toml"),
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[features]\nfoo = []\n",
        )
        .unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("Cargo features require an explicit configured compilation request"),
            "expected Cargo features rejection, got: {err}"
        );
    }

    // 6. Cargo `[dependencies]` must be rejected.
    {
        let sandbox = SandboxCrate::new("cargo-deps", ok_src);
        let dep_dir = sandbox.root_path.join("dep");
        fs::create_dir_all(dep_dir.join("src")).unwrap();
        fs::write(
            dep_dir.join("Cargo.toml"),
            "[package]\nname = \"dep\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        fs::write(dep_dir.join("src/lib.rs"), "").unwrap();
        fs::write(
            sandbox.crate_dir.join("Cargo.toml"),
            format!(
                "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\ndep = {{ path = {:?} }}\n",
                dep_dir.display().to_string()
            ),
        )
        .unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("Cargo shortcut requires a dependency-free library"),
            "expected Cargo dependencies rejection, got: {err}"
        );
    }

    // 7. Virtual workspace `Cargo.toml` must be rejected.
    {
        let sandbox = SandboxCrate::new("virtual-ws", ok_src);
        let ws_manifest = sandbox.root_path.join("Cargo.toml");
        fs::write(
            &ws_manifest,
            "[workspace]\nmembers = [\"subject\"]\nresolver = \"2\"\n",
        )
        .unwrap();
        let synth = synthesize_proof_package(ok_src).unwrap();
        fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
        fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();
        let mut cmd = tools.command();
        cmd.arg("--manifest-path")
            .arg(&ws_manifest)
            .arg("--proof-dir")
            .arg(&sandbox.proof_dir);
        let output = tools.run_command(cmd).unwrap();
        assert!(!output.status.success());
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("choose a package Cargo.toml, not a virtual workspace"),
            "expected virtual workspace rejection, got:\n{stdout}"
        );
    }
}

#[test]
fn rejects_compiler_overrides_in_source_root() {
    let tools = Tools::discover();
    let ok_src = "pub fn id(x: usize) -> usize { x }\n";
    for rel in [
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
    ] {
        let sandbox = SandboxCrate::new("compiler-override", ok_src);
        let override_path = sandbox.crate_dir.join(rel);
        if let Some(parent) = override_path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(
            &override_path,
            "[build]\nrustflags = [\"--cfg\", \"evil\"]\n",
        )
        .unwrap();
        let err = verify_sandbox(&tools, &sandbox, ok_src).unwrap_err();
        assert!(
            err.message
                .contains("compiler overrides need an explicit configured compilation"),
            "expected {rel} override rejection, got: {err}"
        );
    }
}

#[test]
fn verifies_under_hostile_environment_and_cargo_configs() {
    let tools = Tools::discover();
    let ok_src = "/// anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { x }\n";
    let sandbox = SandboxCrate::new("hostile-env", ok_src);
    let synth = synthesize_proof_package(ok_src).unwrap();
    fs::write(sandbox.proof_dir.join("Spec.lean"), &synth.spec_lean).unwrap();
    fs::write(sandbox.proof_dir.join("Proof.lean"), &synth.proof_lean).unwrap();

    let evil = tempfile::Builder::new()
        .prefix("anneal-evil-env-")
        .tempdir()
        .unwrap();
    let e = evil.path();
    let bad_cfg = "[build]\nrustc-wrapper = \"/bin/false\"\nrustflags = [\"--cfg\", \"evil\"]\n";
    fs::create_dir_all(e.join(".cargo")).unwrap();
    fs::write(e.join(".cargo/config.toml"), bad_cfg).unwrap();
    fs::create_dir_all(e.join("work")).unwrap();
    fs::create_dir_all(e.join("lib")).unwrap();
    for lib in ["libleanshared.so", "librustc_driver.so"] {
        fs::write(e.join("lib").join(lib), b"not an ELF shared library").unwrap();
    }

    let mut cmd = tools.command();
    cmd.arg("--manifest-path")
        .arg(sandbox.crate_dir.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(&sandbox.proof_dir)
        .current_dir(e.join("work"))
        .env("XDG_CACHE_HOME", e)
        .env("RUSTC", "/bin/false")
        .env("RUSTC_WRAPPER", "/bin/false")
        .env("RUSTFLAGS", "--cfg evil")
        .env("RUSTC_LOG", "debug")
        .env("LD_LIBRARY_PATH", e.join("lib"))
        .env("LEAN_PATH", e);
    let output = tools
        .run_command(cmd)
        .expect("invoke cargo-anneal under hostile environment");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "expected cargo-anneal verify to succeed under hostile env:\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let receipt: Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(receipt["schema_version"], 2);
    assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
    assert!(receipt.get("tainted").is_none());
    assert_eq!(receipt["status"], "crate_verified");
    assert_eq!(receipt["audit"]["exactType"], true);
    assert_eq!(receipt["audit"]["replay"], true);
}

#[test]
fn rejects_external_file_inclusion_via_path_attribute() {
    let tools = Tools::discover();
    let ext_dir = tempfile::Builder::new()
        .prefix("anneal-ext-src-")
        .tempdir()
        .unwrap();
    let ext_file = ext_dir.path().join("outside.rs");
    fs::write(&ext_file, "pub fn helper(x: usize) -> usize { x }\n").unwrap();

    let src = format!(
        "#[path = {:?}]\npub mod outside;\npub fn id(x: usize) -> usize {{ outside::helper(x) }}\n",
        ext_file.display().to_string()
    );
    let sandbox = SandboxCrate::new("path-attr-outside", &src);
    let err = verify_sandbox(&tools, &sandbox, &src).unwrap_err();
    assert!(
        err.message.contains("undeclared compiler read"),
        "expected undeclared compiler read rejection for #[path = ...], got: {err}"
    );
}

#[test]
fn single_case_fixture_preserves_leading_doc_comments() {
    let dummy = Path::new("single_case.rs");
    let raw = "\
// Copyright 2026 The Fuchsia Authors
//! Crate-level doc comment in header window.
/// anneal:spec ensures(ret == x)
//@ pass
pub fn id(x: usize) -> usize {
    x
}
";
    let pre_case_directive =
        "//@ pass\n// === case: first ===\n//@ pass\npub fn id(x: usize) -> usize { x }\n";
    let pre_case_err = parse_fixture_file("pre_case", dummy, pre_case_directive)
        .expect_err("`//@` directive before first case header must be rejected");
    assert!(
        pre_case_err.contains("before the first"),
        "unexpected pre-case directive error: {pre_case_err}"
    );

    let cases = parse_fixture_file("single_case", dummy, raw).unwrap();
    assert_eq!(cases.len(), 1);
    assert!(
        cases[0].source.contains("//! Crate-level doc comment"),
        "expected `//!` doc comment to be preserved, got:\n{}",
        cases[0].source
    );
    assert!(
        cases[0]
            .source
            .contains("/// anneal:spec ensures(ret == x)"),
        "expected `/// anneal:spec` doc comment to be preserved, got:\n{}",
        cases[0].source
    );
    let synth = synthesize_proof_package(&cases[0].source).unwrap();
    assert!(
        synth.spec_lean.contains("Behavior (entryProgForBody p 0)"),
        "expected Spec.lean to state Behavior contract without Returns:\n{}",
        synth.spec_lean
    );
    assert!(
        !synth.spec_lean.contains("Returns"),
        "Spec.lean must not reference proof-side `Returns`:\n{}",
        synth.spec_lean
    );

    // Non-directive `//` comments in the first eight lines of a single-case
    // fixture must be preserved so malformed annotations fail closed rather
    // than being silently stripped.
    let malformed_comment_raw = "\
//@ pass
// anneal:requires x != 0
pub unsafe fn id(x: usize) -> usize {
    x
}
";
    let malformed_cases =
        parse_fixture_file("single_case_bad_comment", dummy, malformed_comment_raw).unwrap();
    assert_eq!(malformed_cases.len(), 1);
    assert!(
        malformed_cases[0]
            .source
            .contains("// anneal:requires x != 0"),
        "expected leading `// anneal:` comment to be preserved, got:\n{}",
        malformed_cases[0].source
    );
    let err = synthesize_proof_package(&malformed_cases[0].source)
        .expect_err("malformed `// anneal:` comment in single-case fixture must fail closed");
    assert!(
        err.contains("unsupported unparsed `anneal:` directive"),
        "unexpected error for preserved `// anneal:` comment: {err}"
    );
}

#[test]
fn keep_sandbox_honors_exact_one_value() {
    assert!(!keep_sandbox_enabled(None));
    for disabled in ["", "0", "false", "FALSE", "true", "yes", "2"] {
        assert!(
            !keep_sandbox_enabled(Some(OsStr::new(disabled))),
            "expected ANNEAL_KEEP_SANDBOX={disabled:?} not to retain sandbox"
        );
    }
    assert!(keep_sandbox_enabled(Some(OsStr::new("1"))));

    let dropped_path = {
        let sandbox = SandboxCrate::new_with_keep(
            "keep-false",
            "pub fn id(x: usize) -> usize { x }\n",
            false,
        );
        assert!(sandbox.root_path.exists());
        sandbox.root_path.clone()
    };
    assert!(
        !dropped_path.exists(),
        "sandbox directory must be removed on drop when keep=false: {}",
        dropped_path.display()
    );

    let retained_path = {
        let sandbox =
            SandboxCrate::new_with_keep("keep-true", "pub fn id(x: usize) -> usize { x }\n", true);
        assert!(sandbox.root_path.exists());
        sandbox.root_path.clone()
    };
    let still_exists = retained_path.exists();
    let _ = fs::remove_dir_all(&retained_path);
    assert!(
        still_exists,
        "sandbox directory must be retained on drop when keep=true: {}",
        retained_path.display()
    );
}

#[test]
fn rejects_unsupported_and_duplicate_fn_spec_annotations() {
    for (label, bad_src, expected) in [
        (
            "nonzero-literal-1",
            "/// anneal:requires x != 1\npub fn id(x: usize) -> usize { x }\n",
            "unsupported `anneal:requires x != 1` literal `1`",
        ),
        (
            "requires-non-int-param",
            "pub enum E { A, B }\n/// anneal:requires e != 0\npub fn tag(e: E) -> usize { 0 }\n",
            "unsupported parameter type `E`",
        ),
        (
            "duplicate-requires",
            "/// anneal:requires x != 0\n/// anneal:requires x != 0\npub unsafe fn f(x: usize) -> usize { x }\n",
            "multiple `anneal:requires` clauses",
        ),
        (
            "duplicate-spec",
            "/// anneal:spec ensures(ret == x)\n/// anneal:spec ensures(ret == x)\npub fn f(x: usize) -> usize { x }\n",
            "multiple `anneal:spec` clauses",
        ),
        (
            "parenthesized-requires",
            "/// anneal:requires(x != 0)\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported `anneal:` doc directive",
        ),
        (
            "doc-attr-requires",
            "#[doc = \"anneal:requires x != 0\"]\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported attribute `anneal:` directive",
        ),
        (
            "inner-doc-requires",
            "//! anneal:requires x != 0\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported inner-doc `anneal:` directive",
        ),
        (
            "block-doc-requires",
            "/** anneal:requires x != 0 */\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported block-doc `anneal:` directive",
        ),
        (
            "unsupported-invariant",
            "/// anneal:invariant val != 0\npub struct S { val: usize }\n",
            "unsupported `anneal:` doc directive",
        ),
        (
            "dangling-requires-on-non-fn",
            "/// anneal:requires x != 0\npub struct S { val: usize }\n",
            "dangling `anneal:` directive",
        ),
        (
            "midline-block-doc-requires",
            "pub fn g(y: usize) -> usize { y } /** anneal:requires x != 0 */\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported unparsed `anneal:` directive",
        ),
        (
            "midline-line-doc-spec",
            "pub fn other(y: usize) -> usize { y } /// anneal:spec ensures(ret == x)\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported unparsed `anneal:` directive",
        ),
        (
            "regular-comment-anneal",
            "// anneal:requires x != 0\npub unsafe fn f(x: usize) -> usize { x }\n",
            "unsupported unparsed `anneal:` directive",
        ),
        (
            "same-line-attr-enum-dangling-requires",
            "/// anneal:requires x != 0\n#[repr(u8)] pub enum Tag { A, B }\npub unsafe fn nonzero_only(x: usize) -> usize { x }\n",
            "dangling `anneal:` directive",
        ),
        (
            "same-line-block-doc-enum-dangling-requires",
            "/// anneal:requires x != 0\n/** doc */ pub enum Tag { A, B }\npub unsafe fn nonzero_only(x: usize) -> usize { x }\n",
            "dangling `anneal:` directive",
        ),
        (
            "same-line-attr-type-dangling-requires",
            "/// anneal:requires x != 0\n#[allow(dead_code)] pub type Alias = usize;\npub unsafe fn nonzero_only(x: usize) -> usize { x }\n",
            "dangling `anneal:` directive",
        ),
        (
            "same-line-multi-attr-enum-dangling-requires",
            "/// anneal:requires x != 0\n#[allow(dead_code)] #[repr(u8)] pub enum Tag { A, B }\npub unsafe fn nonzero_only(x: usize) -> usize { x }\n",
            "dangling `anneal:` directive",
        ),
        (
            "escaped-doc-attr-unicode",
            "#[doc = \"anneal\\u{3a}spec ensures(ret == x)\"]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "escaped-doc-attr-hex",
            "#[doc = \"an\\x6eeal:spec ensures(ret == x)\"]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "concat-doc-attr",
            "#[doc = concat!(\"anneal\", \":\", \"spec ensures(ret == x)\")]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "cfg-attr-doc",
            "#[cfg_attr(all(), doc = \"anneal\\u{3a}spec ensures(ret == x)\")]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "spaced-inner-doc-attr",
            "# ! [ doc = \"anneal\\u{3a}spec ensures(ret == x)\" ]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "multiline-raw-ident-doc-attr",
            "#[\n    r#doc = \"anneal\\u{3a}spec ensures(ret == x)\"\n]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
        (
            "midline-escaped-doc-attr",
            "pub fn other(y: usize) -> usize { y } #[doc = \"anneal\\u{3a}spec ensures(ret == x)\"]\npub fn id(x: usize) -> usize { let _ = x; 0 }\n",
            "unsupported `doc` attribute",
        ),
    ] {
        let err = synthesize_proof_package(bad_src)
            .expect_err(&format!("expected `{label}` to fail spec parsing"));
        assert!(
            err.contains(expected),
            "{label}: expected error containing {expected:?}, got: {err}"
        );
    }

    // Non-`doc` attributes and string literals mentioning `doc` must not be
    // falsely rejected.
    let benign_attrs = "\
#[allow(missing_docs)]
#[allow(dead_code)]
/// anneal:spec ensures(ret == x)
pub fn id(x: usize) -> usize {
    let _ = \"#[doc = \\\"anneal\\\\u{3a}spec\\\"]\";
    x
}
";
    synthesize_proof_package(benign_attrs)
        .expect("non-doc attributes and string literals must parse cleanly");

    // Same-line attribute on a real top-level `unsafe fn` must still attach
    // `anneal:requires` and preserve `is_unsafe`.
    let same_line_attr_fn = "/// anneal:requires x != 0\n#[allow(dead_code)] pub unsafe fn nonzero_only(x: usize) -> usize { x }\n";
    let synth = synthesize_proof_package(same_line_attr_fn).unwrap();
    assert!(
        synth.spec_lean.contains("rust-path-v1::nonzero_only")
            && synth
                .spec_lean
                .contains(".scalar ⟨.isize, false, BitVec.ofNat 128 0⟩"),
        "expected same-line attributed unsafe fn to retain safety clause:\n{}",
        synth.spec_lean
    );

    // Verify `Spec.lean` emits `Specs.safety` independent of `classify_body`
    // and supports signed integer parameters (`i32`), defaulting unmatched
    // functions to `True` (never vacuous `False`).
    let unproved_unsafe =
        "/// anneal:requires x != 0\npub unsafe fn custom(x: i32) -> i32 { x.wrapping_add(1) }\n";
    let synth = synthesize_proof_package(unproved_unsafe).unwrap();
    assert!(
        synth.spec_lean.contains("rust-path-v1::custom")
            && synth
                .spec_lean
                .contains(".scalar ⟨.i32, true, BitVec.ofNat 128 0⟩")
            && synth.spec_lean.contains("else True)")
            && !synth.spec_lean.contains("False"),
        "expected signed i32 safety clause with non-vacuous True default:\n{}",
        synth.spec_lean
    );

    // An `unsafe fn` without any `requires` directive must emit `True` (not
    // vacuous `False`) for `Specs.safety`.
    let unsafe_no_req = "pub unsafe fn f(x: usize) -> usize { x }\n";
    let synth = synthesize_proof_package(unsafe_no_req).unwrap();
    assert!(
        synth.spec_lean.contains("safety := fun _ _ => True") && !synth.spec_lean.contains("False"),
        "expected non-vacuous `True` safety default for unsafe fn without requires:\n{}",
        synth.spec_lean
    );
}

#[test]
fn bless_does_not_promote_known_bug_with_failing_mir_assertion() {
    let dummy = Path::new("known_bug_mir.rs");
    let raw = "\
// === case: resolved_but_wrong_mir ===
//@ known_bug(#123, proof, id): \"unproved\"
//@ mir-contains: \"expected_token\"
pub fn id(x: usize) -> usize {
    x
}

// === case: pass_with_mir_not_contains ===
//@ pass
//@ mir-not-contains: \"forbidden_token\"
pub fn id(x: usize) -> usize {
    x
}

// === case: known_bug_with_mir_not_contains ===
//@ known_bug(#123, proof, id): \"unproved\"
//@ mir-not-contains: \"forbidden_token\"
pub fn id(x: usize) -> usize {
    x
}
";
    let cases = parse_fixture_file("known_bug_mir", dummy, raw).unwrap();
    assert_eq!(cases.len(), 3);
    let wrong_mir_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: Some("-- missing token".to_owned()),
        output_text: "{}".to_owned(),
    });
    match evaluate_case(&cases[0], &wrong_mir_ok, true) {
        CaseOutcome::Failed(reason) => {
            assert!(
                reason.contains("expected_token"),
                "expected MIR assertion failure, got: {reason}"
            );
        }
        other => panic!(
            "expected Failed when known_bug passes with violated MIR assertion, got {other:?}"
        ),
    }
    let matching_mir_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: Some("-- expected_token".to_owned()),
        output_text: "{}".to_owned(),
    });
    assert!(
        matches!(
            evaluate_case(&cases[0], &matching_mir_ok, true),
            CaseOutcome::Blessed(_)
        ),
        "expected Blessed once both verification and MIR assertions pass"
    );

    // Missing `Captured.lean` on a passing run must fail closed for
    // `mir-not-contains` rather than passing vacuously over `""`.
    let missing_mir_ok: Result<VerifyReport, VerifyError> = Ok(VerifyReport {
        mir_lean: None,
        output_text: "{}".to_owned(),
    });
    for (label, case, bless) in [
        ("pass-missing-mir", &cases[1], false),
        ("known-bug-missing-mir", &cases[2], true),
    ] {
        match evaluate_case(case, &missing_mir_ok, bless) {
            CaseOutcome::Failed(reason) => assert!(
                reason.contains("expected Captured.lean to be emitted"),
                "{label}: expected missing Captured.lean failure, got: {reason}"
            ),
            other => panic!("{label}: expected Failed when Captured.lean is absent, got {other:?}"),
        }
    }
}

#[test]
fn parse_proof_failure_matches_diagnostic_file_before_line_attribution() {
    let fn_ranges = vec![(10, 25, "id".to_owned()), (26, 40, "helper".to_owned())];

    // An error in `Spec.lean`, `Expected.lean`, `Captured.lean`, a nested
    // `Sub/Proof.lean`, or a diagnostic omitting `fileName` must never be
    // attributed to a `Proof.lean` function even when the line number overlaps.
    for other_file in [
        Some("/tmp/anneal-trusted-abc/target-src/Spec.lean"),
        Some("/tmp/anneal-trusted-abc/target-src/Expected.lean"),
        Some("/tmp/anneal-trusted-abc/target-src/Captured.lean"),
        Some("/tmp/anneal-trusted-abc/target-src/Sub/Proof.lean"),
        None,
    ] {
        let mut diag = serde_json::json!({
            "severity": "error",
            "pos": { "line": 15, "column": 1 },
            "data": "spec or other-file error"
        });
        if let Some(f) = other_file {
            diag["fileName"] = serde_json::json!(f);
        }
        let (scope, msg) = parse_proof_failure(&diag.to_string(), &fn_ranges);
        assert_eq!(
            scope, "crate",
            "expected crate scope for fileName={other_file:?}, got {scope:?}"
        );
        assert!(msg.contains("spec or other-file error"));
    }

    // A `Spec.lean` error on line 15 followed by a `Proof.lean` error on line
    // 30 attributes strictly to `helper` (from `Proof.lean`), not `id`.
    let combined = format!(
        "{}\n{}\n",
        serde_json::json!({
            "severity": "error",
            "fileName": "/tmp/anneal-trusted-abc/target-src/Spec.lean",
            "pos": { "line": 15, "column": 1 },
            "data": "spec error"
        }),
        serde_json::json!({
            "severity": "error",
            "fileName": "/tmp/anneal-trusted-abc/target-src/Proof.lean",
            "pos": { "line": 30, "column": 3 },
            "data": "proof error in helper"
        })
    );
    let (scope, msg) = parse_proof_failure(&combined, &fn_ranges);
    assert_eq!(scope, "helper");
    assert!(msg.contains("spec error") && msg.contains("proof error in helper"));
}

#[test]
fn fixture_concurrency_honors_jobs_cli_and_env() {
    let s = |xs: &[&str]| xs.iter().map(|v| (*v).to_owned()).collect::<Vec<_>>();
    // `ANNEAL_TEST_JOBS` caps concurrency downward but never overrides an
    // explicit `--test-threads` or `RUST_TEST_THREADS` limit upward.
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=1"]), Some("4"), Some("2"), 16),
        Ok(1)
    );
    assert_eq!(
        fixture_concurrency_from(
            &s(&["bin", "--test-threads", "2"]),
            Some("8"),
            Some("1"),
            16
        ),
        Ok(2)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=8"]), Some("2"), None, 16),
        Ok(2)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=64"]), None, None, 16),
        Ok(32)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin", "--test-threads=64"]), Some("4"), None, 16),
        Ok(4)
    );
    // `RUST_TEST_THREADS` uses the exact same `1..=32` clamp as
    // `--test-threads` and is never exceeded by `ANNEAL_TEST_JOBS`.
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), Some("4"), Some("1"), 16),
        Ok(1)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), Some("2"), Some("8"), 16),
        Ok(2)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), None, Some("8"), 16),
        Ok(8)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), None, Some("64"), 16),
        Ok(32)
    );
    // Without libtest thread overrides, `ANNEAL_TEST_JOBS` sets the cap
    // directly within `1..=32`, and omitting all controls clamps to `1..=3`.
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), Some("8"), None, 16),
        Ok(8)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), None, Some("1"), 16),
        Ok(1)
    );
    assert_eq!(
        fixture_concurrency_from(&s(&["bin"]), None, None, 16),
        Ok(3)
    );
    assert_eq!(fixture_concurrency_from(&s(&["bin"]), None, None, 1), Ok(1));
    // Invalid `ANNEAL_TEST_JOBS` values are strictly rejected instead of
    // silently falling back.
    for invalid in ["", "0", "33", "64", "abc"] {
        let err = fixture_concurrency_from(&s(&["bin"]), Some(invalid), Some("2"), 16).expect_err(
            &format!("expected invalid ANNEAL_TEST_JOBS={invalid:?} to fail"),
        );
        assert!(
            err.contains("ANNEAL_TEST_JOBS must be an integer in 1..=32"),
            "unexpected error for {invalid:?}: {err}"
        );
    }

    // Process-wide permit pool enforces the exact configured cap across
    // overlapping worker threads.
    let pool = Arc::new(JobPool::new(2));
    let active = Arc::new(Mutex::new((0usize, 0usize)));
    let mut handles = Vec::new();
    for _ in 0..4 {
        let pool = Arc::clone(&pool);
        let active = Arc::clone(&active);
        handles.push(thread::spawn(move || {
            for _ in 0..4 {
                let _permit = pool.acquire();
                {
                    let mut state = active.lock().unwrap();
                    state.0 += 1;
                    state.1 = state.1.max(state.0);
                }
                thread::yield_now();
                active.lock().unwrap().0 -= 1;
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    let (current, peak) = *active.lock().unwrap();
    assert_eq!(current, 0);
    assert!(peak <= 2, "permit pool exceeded cap 2: peak={peak}");
}

#[test]
fn synthesizer_attributes_ensures_to_fn_and_avoids_u32_add_shadowing() {
    let tools = Tools::discover();

    // 1. Multi-function crate placing `U32Add` at body indices 1 and 2 must
    // verify cleanly without parameter-vs-body identifier shadowing.
    let multi_u32 = "\
pub fn id0(x: usize) -> usize {
    x
}

pub fn add1(x: u32, y: u32) -> u32 {
    x + y
}

pub fn add2(x: u32, y: u32) -> u32 {
    x + y
}
";
    let sandbox_u32 = SandboxCrate::new("multi-u32-add", multi_u32);
    verify_sandbox(&tools, &sandbox_u32, multi_u32)
        .expect("U32Add at body indices 1 and 2 must verify cleanly");

    // 2. `ClampNonzero` with `ensures` and no `requires` must fail inside
    // `clamp_nonzero`'s own proof range, not `"crate"`.
    let clamp_no_req = "\
/// anneal:spec ensures(ret == x)
pub fn clamp_nonzero(x: usize) -> usize {
    if x == 0 {
        1
    } else {
        x
    }
}
";
    let sandbox_clamp = SandboxCrate::new("clamp-no-req", clamp_no_req);
    let err = verify_sandbox(&tools, &sandbox_clamp, clamp_no_req).unwrap_err();
    assert_eq!(
        err.failure.as_ref().map(|f| &f.stage),
        Some(&FailureStage::Proof {
            scope: "clamp_nonzero".to_owned()
        }),
        "expected scope `clamp_nonzero`, got: {err}"
    );

    // 3. `U32Add` with an unsupported `ensures` must attribute failure to
    // `add`, not `"crate"`.
    let add_with_ens = "\
/// anneal:spec ensures(ret == x)
pub fn add(x: u32, y: u32) -> u32 {
    x + y
}
";
    let sandbox_add = SandboxCrate::new("u32-add-ens", add_with_ens);
    let err = verify_sandbox(&tools, &sandbox_add, add_with_ens).unwrap_err();
    assert_eq!(
        err.failure.as_ref().map(|f| &f.stage),
        Some(&FailureStage::Proof {
            scope: "add".to_owned()
        }),
        "expected scope `add`, got: {err}"
    );

    // 4. `EnumTag` with `ensures` and `CustomMirNonzero` with `ensures` emit
    // `body0_ens` inside their function ranges.
    let enum_ens = "\
pub enum E {
    A,
    B,
}

/// anneal:spec ensures(ret == e)
pub fn tag(e: E) -> usize {
    match e {
        E::A => 0,
        E::B => 1,
    }
}
";
    let synth_enum = synthesize_proof_package(enum_ens).unwrap();
    assert!(
        synth_enum.proof_lean.contains("theorem body0_ens :"),
        "expected EnumTag ensures theorem inside fn range:\n{}",
        synth_enum.proof_lean
    );

    let custom_mir_ens = "\
#![no_std]
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;

/// anneal:requires x != 0
/// anneal:spec ensures(ret == x)
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]
pub unsafe fn nonzero_only(x: usize) -> usize {
    mir! {
        {
            match x {
                0 => bad,
                _ => ok,
            }
        }
        bad = {
            Unreachable()
        }
        ok = {
            RET = x;
            Return()
        }
    }
}
";
    let sandbox_cm = SandboxCrate::new("custom-mir-ens", custom_mir_ens);
    verify_sandbox(&tools, &sandbox_cm, custom_mir_ens)
        .expect("CustomMirNonzero with requires + ensures must verify cleanly");
}

#[test]
fn verify_sandbox_runs_real_capture_before_spec_synthesis_error() {
    let tools = Tools::discover();

    // 1. Valid MIR with invalid spec annotation must still invoke real
    // capture (`Captured.lean` is emitted) before reporting the spec error
    // under `FailureStage::Spec`.
    let bad_spec = "/// anneal:spec ensures(ret == y)\npub fn id(x: usize) -> usize { x }\n";
    let sandbox_spec = SandboxCrate::new("capture-first-spec", bad_spec);
    let err = verify_sandbox(&tools, &sandbox_spec, bad_spec).unwrap_err();
    let mir = err
        .mir_lean
        .as_deref()
        .expect("real capture must run and emit Captured.lean before spec error");
    assert!(
        mir.contains("def program : Trusted.MirAst.Program")
            && mir.contains("Trusted.MirAst.TerminatorKind.return_"),
        "expected Captured.lean to contain captured MIR body, got:\n{mir}"
    );
    let failure = err.failure.expect("expected structured spec failure");
    assert_eq!(failure.stage, FailureStage::Spec);
    assert!(
        failure.diagnostic.contains("unknown identifier `y`"),
        "expected spec diagnostic after capture succeeded, got: {}",
        failure.diagnostic
    );

    // 2. Unsupported MIR item with invalid spec annotation must report the
    // real capture rejection under `FailureStage::Capture` rather than masking
    // it with the spec error.
    let bad_mir_and_spec = "\
pub struct S { val: usize }
/// anneal:requires x != 1
pub unsafe fn f(x: usize) -> S { S { val: x } }
";
    let sandbox_mir = SandboxCrate::new("capture-first-mir", bad_mir_and_spec);
    let err = verify_sandbox(&tools, &sandbox_mir, bad_mir_and_spec).unwrap_err();
    let failure = err.failure.expect("expected structured capture failure");
    assert_eq!(failure.stage, FailureStage::Capture);
    assert!(
        failure
            .diagnostic
            .contains("whole-crate obligation is unsupported: Struct"),
        "expected real capture rejection before spec error, got: {}",
        failure.diagnostic
    );

    // 3. Unrecognized `anneal:` directive syntax on a capturable `unsafe fn`
    // fails closed under `FailureStage::Spec` instead of silently dropping the
    // precondition.
    let bad_syntax_unsafe =
        "/// anneal:requires(x != 0)\npub unsafe fn id(x: usize) -> usize { x }\n";
    let sandbox_syntax = SandboxCrate::new("capture-first-bad-directive", bad_syntax_unsafe);
    let err = verify_sandbox(&tools, &sandbox_syntax, bad_syntax_unsafe).unwrap_err();
    assert!(
        err.mir_lean.is_some(),
        "expected real capture to emit Captured.lean before spec error"
    );
    let failure = err.failure.expect("expected structured spec failure");
    assert_eq!(failure.stage, FailureStage::Spec);
    assert!(
        failure
            .diagnostic
            .contains("unsupported `anneal:` doc directive"),
        "expected unrecognized anneal: directive rejection, got: {}",
        failure.diagnostic
    );
}
