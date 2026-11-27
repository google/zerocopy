// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Stage-typed, polarity-locked `//@` expectation directive parser and bless
//! engine for declarative test corpora.
//!
//! Supported primary expectations (exactly one per `// === case: <name> ===`
//! section):
//! - `//@ pass`
//! - `//@ fail(capture): "<diagnostic_substring>"`
//! - `//@ fail(preflight): "<diagnostic_substring>"`
//! - `//@ fail(spec): "<diagnostic_substring>"`
//! - `//@ fail(proof, <fn_or_crate>): "<diagnostic_substring>"`
//! - `//@ fail(audit): "<diagnostic_substring>"`
//! - `//@ known_bug(#<issue>, <stage...>): "<diagnostic_substring>"`
//!
//! Optional per-case metadata:
//! - `//@ kills-guard: <guard_id>`
//! - `//@ mir-contains: "<substring>"`
//! - `//@ mir-not-contains: "<substring>"`
//!
//! **Polarity lock:** `ANNEAL_BLESS=1` may refresh diagnostic substrings within
//! a matching failing polarity or promote a newly passing `known_bug` to
//! `//@ pass`, and strictly refuses any `//@ pass <-> //@ fail(...)` flip.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::TestResult;

/// Pipeline stage at which a negative corpus case expects rejection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FailureStage {
    Capture,
    Preflight,
    Spec,
    Proof { scope: String },
    Audit,
}

/// Structured failure reported by executing a corpus case.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageFailure {
    pub stage: FailureStage,
    pub diagnostic: String,
}

/// Primary pass/fail/known-bug expectation parsed from `//@ ...`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrimaryExpectation {
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

impl PrimaryExpectation {
    fn polarity_kind(&self) -> PolarityKind {
        match self {
            Self::Pass => PolarityKind::Pass,
            Self::Fail { .. } => PolarityKind::Fail,
            Self::KnownBug { .. } => PolarityKind::KnownBug,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PolarityKind {
    Pass,
    Fail,
    KnownBug,
}

/// Parsed fixture case section from a corpus file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureCase {
    pub suite: String,
    pub name: String,
    pub file_path: PathBuf,
    pub primary_line_idx: usize,
    pub expectation: PrimaryExpectation,
    pub kills_guard: Option<String>,
    pub mir_contains: Vec<String>,
    pub mir_not_contains: Vec<String>,
    pub source: String,
}

impl FixtureCase {
    pub fn full_name(&self) -> String {
        format!("{}::{}", self.suite, self.name)
    }
}

/// Result of running a single corpus case before comparing against its
/// declared expectation.
#[derive(Clone, Debug)]
pub enum CaseExpectationResult {
    Passed {
        mir_lean: Option<String>,
        output_text: String,
    },
    Failed {
        message: String,
        failure: Option<StageFailure>,
        mir_lean: Option<String>,
    },
}

/// Targeted line patch generated under `ANNEAL_BLESS=1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlessPatch {
    pub file_path: PathBuf,
    pub line_idx: usize,
    pub replacement: String,
}

/// Evaluation outcome of a corpus case against its [`FixtureCase`] contract.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaseOutcome {
    Passed,
    Blessed(BlessPatch),
    Failed(String),
}

/// Entry point wrapper for parsing declarative `//@` corpus files.
pub struct DirectiveParser;

impl DirectiveParser {
    /// Parse `content` belonging to `suite` at `file_path`.
    pub fn parse(
        suite: &str,
        file_path: &Path,
        content: &str,
    ) -> TestResult<Vec<FixtureCase>> {
        parse_fixture_file(suite, file_path, content)
    }
}

/// Format a [`FailureStage`] for human diagnostics and blessed `//@` lines.
pub fn format_stage(stage: &FailureStage) -> String {
    match stage {
        FailureStage::Capture => "capture".to_owned(),
        FailureStage::Preflight => "preflight".to_owned(),
        FailureStage::Spec => "spec".to_owned(),
        FailureStage::Proof { scope } => format!("proof, {scope}"),
        FailureStage::Audit => "audit".to_owned(),
    }
}

/// Parse one declarative corpus file into zero-ambiguity [`FixtureCase`]
/// entries.
pub fn parse_fixture_file(
    suite: &str,
    file_path: &Path,
    content: &str,
) -> TestResult<Vec<FixtureCase>> {
    let lines: Vec<&str> = content.lines().collect();
    let mut sections: Vec<(String, usize, usize)> = Vec::new();
    let mut seen_names = BTreeSet::new();

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
            if name.is_empty()
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return Err(format!(
                    "{}:{}: invalid case name {name:?}",
                    file_path.display(),
                    idx + 1
                ));
            }
            if !seen_names.insert(name.to_owned()) {
                return Err(format!(
                    "{}:{}: duplicate case name {name:?}",
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
        let mut kills_guard: Option<String> = None;
        let mut mir_contains = Vec::new();
        let mut mir_not_contains = Vec::new();
        let mut source_lines = Vec::new();

        for (offset, &line) in lines[start..end].iter().enumerate() {
            let line_idx = start + offset;
            let loc = format!("{}:{}: ({suite}::{name})", file_path.display(), line_idx + 1);
            let trimmed = line.trim();
            if let Some(directive) = trimmed.strip_prefix("//@") {
                let directive = directive.trim();
                if let Some(after) = directive.strip_prefix("kills-guard:") {
                    if kills_guard.is_some() {
                        return Err(format!("{loc}: duplicate `kills-guard` directive"));
                    }
                    let guard_id = after.trim();
                    if guard_id.is_empty()
                        || !guard_id
                            .chars()
                            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '-' | '.'))
                    {
                        return Err(format!("{loc}: invalid guard id {guard_id:?}"));
                    }
                    kills_guard = Some(guard_id.to_owned());
                } else if let Some(after) = directive.strip_prefix("mir-contains:") {
                    mir_contains.push(parse_quoted_non_empty(after, &loc)?);
                } else if let Some(after) = directive.strip_prefix("mir-not-contains:") {
                    mir_not_contains.push(parse_quoted_non_empty(after, &loc)?);
                } else {
                    let exp = parse_primary_directive(directive, &loc)?;
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
            kills_guard,
            mir_contains,
            mir_not_contains,
            source,
        });
    }

    Ok(cases)
}

fn parse_primary_directive(directive: &str, loc: &str) -> TestResult<PrimaryExpectation> {
    if directive == "pass" {
        return Ok(PrimaryExpectation::Pass);
    }
    if let Some(rest) = directive.strip_prefix("fail(") {
        let (inside, after) = rest
            .split_once("):")
            .ok_or_else(|| format!("{loc}: malformed `fail(...)` directive"))?;
        let parts: Vec<&str> = inside.split(',').map(str::trim).collect();
        let stage = parse_stage_args(&parts, loc)?;
        let substring = parse_quoted_non_empty(after, loc)?;
        return Ok(PrimaryExpectation::Fail { stage, substring });
    }
    if let Some(rest) = directive.strip_prefix("known_bug(") {
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
        let stage = parse_stage_args(&parts[1..], loc)?;
        let substring = parse_quoted_non_empty(after, loc)?;
        return Ok(PrimaryExpectation::KnownBug {
            issue,
            stage,
            substring,
        });
    }
    Err(format!("{loc}: unknown directive `//@ {directive}`"))
}

fn parse_quoted_non_empty(raw: &str, ctx: &str) -> TestResult<String> {
    let trimmed = raw.trim();
    let val: String = serde_json::from_str(trimmed).map_err(|_| {
        format!("{ctx}: expected non-empty string literal, got {trimmed:?}")
    })?;
    if val.is_empty() {
        return Err(format!("{ctx}: expected non-empty string literal"));
    }
    Ok(val)
}

fn parse_stage_args(args: &[&str], ctx: &str) -> TestResult<FailureStage> {
    match args {
        ["capture"] => Ok(FailureStage::Capture),
        ["capture", ..] => Err(format!("{ctx}: `capture` stage does not take a scope")),
        ["preflight"] => Ok(FailureStage::Preflight),
        ["preflight", ..] => Err(format!("{ctx}: `preflight` stage does not take a scope")),
        ["spec"] => Ok(FailureStage::Spec),
        ["spec", ..] => Err(format!("{ctx}: `spec` stage does not take a scope")),
        ["audit"] => Ok(FailureStage::Audit),
        ["audit", ..] => Err(format!("{ctx}: `audit` stage does not take a scope")),
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

fn first_clean_line(diag: &str) -> String {
    diag.lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("verification failed")
        .to_owned()
}

/// Check `//@ mir-contains` and `//@ mir-not-contains` constraints.
pub fn check_mir_assertions(case: &FixtureCase, mir_lean: Option<&str>) -> TestResult {
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

/// Evaluate a [`CaseExpectationResult`] against `case` while enforcing the
/// strict polarity-lock invariant (`ANNEAL_BLESS=1` can never flip
/// `pass <-> fail`).
pub fn evaluate_case(
    case: &FixtureCase,
    result: &CaseExpectationResult,
    bless: bool,
) -> CaseOutcome {
    match (&case.expectation, result) {
        (PrimaryExpectation::Pass, CaseExpectationResult::Passed { mir_lean, .. }) => {
            if let Err(e) = check_mir_assertions(case, mir_lean.as_deref()) {
                CaseOutcome::Failed(e)
            } else {
                CaseOutcome::Passed
            }
        }
        (PrimaryExpectation::Pass, CaseExpectationResult::Failed { message, .. }) => {
            // Polarity-locked: never auto-flip `//@ pass` to `//@ fail(...)`.
            CaseOutcome::Failed(format!("expected `//@ pass`, got failure:\n{message}"))
        }
        (
            PrimaryExpectation::Fail { .. },
            CaseExpectationResult::Passed { output_text, .. },
        ) => {
            // Polarity-locked: never auto-flip `//@ fail(...)` to `//@ pass`.
            CaseOutcome::Failed(format!(
                "expected failure, but verification succeeded:\n{output_text}"
            ))
        }
        (
            PrimaryExpectation::Fail {
                stage: exp_stage,
                substring,
            },
            CaseExpectationResult::Failed {
                message,
                failure,
                mir_lean,
            },
        ) => {
            let Some(actual) = failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured failure, got operational error:\n{message}"
                ));
            };
            if let Err(e) = check_mir_assertions(case, mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless && &actual.stage == exp_stage {
                let quoted =
                    serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
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
        (
            PrimaryExpectation::KnownBug { issue, .. },
            CaseExpectationResult::Passed {
                mir_lean,
                output_text,
            },
        ) => {
            if let Err(e) = check_mir_assertions(case, mir_lean.as_deref()) {
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
                    "`known_bug(#{issue})` now passes! Re-run with `ANNEAL_BLESS=1` to promote it to `//@ pass`.\nReceipt:\n{output_text}"
                ))
            }
        }
        (
            PrimaryExpectation::KnownBug {
                issue,
                stage: exp_stage,
                substring,
            },
            CaseExpectationResult::Failed {
                message,
                failure,
                mir_lean,
            },
        ) => {
            let Some(actual) = failure else {
                return CaseOutcome::Failed(format!(
                    "expected structured known_bug failure, got operational error:\n{message}"
                ));
            };
            if let Err(e) = check_mir_assertions(case, mir_lean.as_deref()) {
                return CaseOutcome::Failed(e);
            }
            if &actual.stage == exp_stage && actual.diagnostic.contains(substring) {
                CaseOutcome::Passed
            } else if bless {
                let quoted =
                    serde_json::to_string(&first_clean_line(&actual.diagnostic)).unwrap();
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

/// Apply `patches` to fixture files on disk after enforcing defense-in-depth
/// polarity-lock validation on every modified directive line.
///
/// Validates all patches before writing any file: attempting to flip
/// `//@ pass` <-> `//@ fail(...)` returns an error without altering disk state.
pub fn apply_bless_patches(patches: &[BlessPatch]) -> TestResult {
    let mut by_file: BTreeMap<PathBuf, Vec<&BlessPatch>> = BTreeMap::new();
    for patch in patches {
        by_file
            .entry(patch.file_path.clone())
            .or_default()
            .push(patch);
    }

    let mut staged_writes: Vec<(PathBuf, String)> = Vec::with_capacity(by_file.len());
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
            let old_trimmed = lines[patch.line_idx].trim();
            let new_trimmed = patch.replacement.trim();
            let old_dir = old_trimmed.strip_prefix("//@").map(str::trim).ok_or_else(|| {
                format!(
                    "bless target {} line {} is not a `//@` directive",
                    path.display(),
                    patch.line_idx + 1
                )
            })?;
            let new_dir = new_trimmed.strip_prefix("//@").map(str::trim).ok_or_else(|| {
                format!(
                    "bless replacement {:?} is not a `//@` directive",
                    patch.replacement
                )
            })?;
            let loc = format!("{}:{}", path.display(), patch.line_idx + 1);
            let old_exp = parse_primary_directive(old_dir, &loc)?;
            let new_exp = parse_primary_directive(new_dir, &loc)?;
            match (&old_exp, &new_exp) {
                (
                    PrimaryExpectation::Fail { stage: old_stage, .. },
                    PrimaryExpectation::Fail { stage: new_stage, .. },
                ) if old_stage == new_stage => {}
                (
                    PrimaryExpectation::Fail { stage: old_stage, .. },
                    PrimaryExpectation::Fail { stage: new_stage, .. },
                ) => {
                    return Err(format!(
                        "{loc}: stage-lock refusal: ANNEAL_BLESS cannot shift fail({old_stage:?}) -> fail({new_stage:?})"
                    ));
                }
                (old, new) => match (old.polarity_kind(), new.polarity_kind()) {
                    (PolarityKind::KnownBug, PolarityKind::KnownBug)
                    | (PolarityKind::KnownBug, PolarityKind::Pass) => {}
                    (old_pol, new_pol) => {
                        return Err(format!(
                            "{loc}: polarity-lock refusal: ANNEAL_BLESS cannot flip {old_pol:?} -> {new_pol:?}"
                        ));
                    }
                },
            }
            lines[patch.line_idx] = patch.replacement.clone();
        }
        let mut out = lines.join("\n");
        out.push('\n');
        staged_writes.push((path, out));
    }

    for (path, out) in staged_writes {
        fs::write(&path, out)
            .map_err(|e| format!("failed to write blessed {}: {e}", path.display()))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
