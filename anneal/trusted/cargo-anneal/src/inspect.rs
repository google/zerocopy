// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Thin OS I/O shell for `cargo anneal inspect` wrapping the pure
//! [`crate::core::inspect`] verification, comparison, and rendering engine.

use std::{
    collections::BTreeSet,
    fs,
    io::{self, IsTerminal as _, Read as _, Write as _},
    path::{Path, PathBuf},
    process::ExitCode,
};

use clap::{Args, ValueEnum};

use crate::{
    core::{
        inspect::{
            diff::{ReceiptDiff, diff_receipts},
            profile::ArtifactAxis,
            render::{
                InspectFormat, InspectSection, RenderOptions, render_diff, render_inspection,
            },
            schema::{
                InspectParseError, PolicyRequirements, UnknownFieldsPolicy,
                parse_and_validate_receipt_with_max_bytes,
            },
            strict_json::{
                DEFAULT_MAX_RECEIPT_JSON_BYTES, MAX_CONFIGURABLE_RECEIPT_JSON_BYTES,
                validate_max_receipt_json_bytes,
            },
        },
        sanitize::SanitizedInline,
    },
    output::{ColorChoice, EnvSnapshot, resolve_stream_style},
    sys_util::SafeFs,
};

mod artifacts;
#[cfg(test)]
mod color_tests;
#[cfg(all(test, unix))]
mod tests;

#[cfg(all(test, unix))]
use self::artifacts::validate_artifact_dir_chain;
use self::artifacts::verify_retained_artifacts;

const MAX_ARTIFACT_FILE_BYTES: u64 = 128 * 1024 * 1024;
const MAX_LEDGER_BYTES: u64 = 16 * 1024 * 1024;

/// CLI-facing output format selector converted into pure [`InspectFormat`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum CliInspectFormat {
    #[default]
    Human,
    Ledger,
    Markdown,
    Json,
}

impl From<CliInspectFormat> for InspectFormat {
    fn from(value: CliInspectFormat) -> Self {
        match value {
            CliInspectFormat::Human => Self::Human,
            CliInspectFormat::Ledger => Self::Ledger,
            CliInspectFormat::Markdown => Self::Markdown,
            CliInspectFormat::Json => Self::Json,
        }
    }
}

/// CLI-facing unknown-field policy converted into pure [`UnknownFieldsPolicy`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum CliUnknownFieldsPolicy {
    #[default]
    Warn,
    Deny,
}

impl From<CliUnknownFieldsPolicy> for UnknownFieldsPolicy {
    fn from(value: CliUnknownFieldsPolicy) -> Self {
        match value {
            CliUnknownFieldsPolicy::Warn => Self::Warn,
            CliUnknownFieldsPolicy::Deny => Self::Deny,
        }
    }
}

/// CLI-facing report section filter converted into pure [`InspectSection`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum CliInspectSection {
    Summary,
    Assurance,
    Digests,
    Closures,
    Census,
    Warnings,
    Assumptions,
    Timing,
    UnknownFields,
}

impl From<CliInspectSection> for InspectSection {
    fn from(value: CliInspectSection) -> Self {
        match value {
            CliInspectSection::Summary => Self::Summary,
            CliInspectSection::Assurance => Self::Assurance,
            CliInspectSection::Digests => Self::Digests,
            CliInspectSection::Closures => Self::Closures,
            CliInspectSection::Census => Self::Census,
            CliInspectSection::Warnings => Self::Warnings,
            CliInspectSection::Assumptions => Self::Assumptions,
            CliInspectSection::Timing => Self::Timing,
            CliInspectSection::UnknownFields => Self::UnknownFields,
        }
    }
}

/// Offline verification receipt inspector (`cargo anneal inspect`).
#[derive(Args, Clone, Debug)]
pub struct InspectArgs {
    /// Path to Receipt Schema v3 JSON file, or `-` to read stdin.
    #[arg(value_name = "RECEIPT", required_unless_present = "diff")]
    pub receipt: Option<PathBuf>,
    /// Compare two Receipt Schema v3 JSON files (`<BASE> <HEAD>`).
    #[arg(long, num_args = 2, value_names = ["BASE", "HEAD"], conflicts_with = "receipt")]
    pub diff: Option<Vec<PathBuf>>,
    /// Output format (`human`, `ledger`, `markdown`, or `json`).
    #[arg(long, value_enum, default_value_t = CliInspectFormat::Human)]
    pub format: CliInspectFormat,
    /// Verify retained artifacts directory against recorded receipt digests.
    #[arg(long, value_name = "DIR", conflicts_with = "diff")]
    pub verify_artifacts: Option<PathBuf>,
    /// Require retained evidence files to be complete with zero missing paths.
    #[arg(long, requires = "verify_artifacts")]
    pub require_exact_artifacts: bool,
    /// Policy for unrecognized JSON fields (`warn` fails default validation
    /// with `exit 1` unless `--passive` is set; `deny` fails with `exit 2`).
    #[arg(long, value_enum, default_value_t = CliUnknownFieldsPolicy::Warn)]
    pub unknown_fields: CliUnknownFieldsPolicy,
    /// Fail (`exit 1`) if rendered deterministic ledger differs from `FILE`.
    #[arg(long, value_name = "FILE")]
    pub compare_ledger: Option<PathBuf>,
    /// Atomically write output to `FILE` instead of stdout.
    #[arg(long, value_name = "FILE")]
    pub output: Option<PathBuf>,
    /// Print full 64-character SHA-256 digests instead of 12-char prefixes.
    #[arg(long)]
    pub full_digests: bool,
    /// Restrict human output to specific sections.
    #[arg(long = "section", value_enum, conflicts_with = "diff")]
    pub section: Vec<CliInspectSection>,
    /// Passive viewer mode: disable terminal probes and ignore single-receipt
    /// status/taint gates as well as warn-mode unrecognized-field policy gates
    /// in both single-receipt and `--diff` modes (structural invariant
    /// violations, artifact mismatches, and `--compare-ledger` diffs still exit
    /// `1`).
    #[arg(
        long,
        conflicts_with_all = [
            "check",
            "require_untainted",
            "require_crate_scope",
            "require_containment",
            "require_kernel_replay",
            "allowed_axioms",
            "allowed_unstable_features",
            "forbid_incomplete_unstable_features",
            "require_exact_artifacts",
            "no_regressions",
            "require_unchanged_specs",
        ]
    )]
    pub passive: bool,
    /// Enforce passing, untainted, recognized verification checks (enabled by
    /// default; retained for compatibility; pass `--passive` to opt out).
    #[arg(long, conflicts_with = "diff")]
    pub check: bool,
    /// Exit `1` unless `taint_reasons` is empty.
    #[arg(long, conflicts_with = "diff")]
    pub require_untainted: bool,
    /// Exit `1` unless whole-crate verification scope was used.
    #[arg(long, conflicts_with = "diff")]
    pub require_crate_scope: bool,
    /// Exit `1` unless elaboration ran under OS sandbox containment.
    #[arg(long, conflicts_with = "diff")]
    pub require_containment: bool,
    /// Exit `1` unless at least `N` replay kernels passed.
    #[arg(long, value_name = "N", conflicts_with = "diff")]
    pub require_kernel_replay: Option<u64>,
    /// Comma-separated axiom names permitted in `audit.axioms`.
    #[arg(long, value_delimiter = ',', value_name = "AXIOM", conflicts_with = "diff")]
    pub allowed_axioms: Option<Vec<String>>,
    /// Comma-separated unstable features a tainted receipt may allow and
    /// observe. Admits the `unmodeled_unstable_features` taint and no other.
    #[arg(
        long,
        value_delimiter = ',',
        value_name = "FEATURE",
        value_parser = parse_feature_name_arg,
        conflicts_with_all = ["diff", "require_untainted"]
    )]
    pub allowed_unstable_features: Option<Vec<String>>,
    /// Exit `1` if the receipt enables any unstable feature that `rustc`
    /// marks incomplete.
    #[arg(long, conflicts_with = "diff")]
    pub forbid_incomplete_unstable_features: bool,
    /// Exit `1` on any Tier A assurance regression between `--diff` receipts.
    #[arg(long, requires = "diff")]
    pub no_regressions: bool,
    /// Treat specification changes in `--diff` as Tier A regressions and exit
    /// `1` when any Tier A regression is detected.
    #[arg(long, requires = "diff")]
    pub require_unchanged_specs: bool,
    /// Maximum receipt JSON size in bytes (`64 MiB` by default, up to `1 GiB`).
    #[arg(
        long,
        default_value_t = DEFAULT_MAX_RECEIPT_JSON_BYTES as u64,
        value_name = "BYTES",
        value_parser = parse_max_receipt_bytes_arg
    )]
    pub max_receipt_bytes: u64,
}

fn parse_max_receipt_bytes_arg(raw: &str) -> Result<u64, String> {
    let bytes: u64 = raw.parse().map_err(|_| {
        format!("invalid `--max-receipt-bytes` value {raw:?}: expected a positive integer")
    })?;
    validate_max_receipt_json_bytes(bytes)?;
    Ok(bytes)
}

fn parse_feature_name_arg(raw: &str) -> Result<String, String> {
    if crate::core::identifiers::is_feature_name(raw) {
        Ok(raw.to_owned())
    } else {
        Err(format!("invalid feature name {raw:?}: expected [a-z][a-z0-9_]*"))
    }
}

impl InspectArgs {
    /// Enforce CLI cross-argument invariants at parse time.
    pub fn validate(&self, mut command: clap::Command) -> Result<(), clap::Error> {
        if let Some(paths) = &self.diff
            && paths.len() == 2
            && paths[0] == Path::new("-")
            && paths[1] == Path::new("-")
        {
            return Err(command.error(
                clap::error::ErrorKind::ValueValidation,
                "cannot read both `--diff` inputs from stdin (`-`)",
            ));
        }
        Ok(())
    }
}

/// Execute `cargo anneal inspect`.
pub fn main(
    args: InspectArgs,
    color: crate::output::ColorChoice,
    quiet: bool,
    verbose: bool,
) -> ExitCode {
    match run(&args, color, quiet, verbose) {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {}", SanitizedInline(err.message()));
            ExitCode::from(err.exit_code() as u8)
        }
    }
}

fn run(
    args: &InspectArgs,
    color: crate::output::ColorChoice,
    quiet: bool,
    verbose: bool,
) -> Result<ExitCode, InspectParseError> {
    let max_receipt_bytes = validate_max_receipt_json_bytes(args.max_receipt_bytes)
        .map_err(InspectParseError::Operational)?;
    let render_opts = build_render_options(args, color, quiet, verbose);

    if let Some(diff_paths) = &args.diff {
        if diff_paths.len() != 2 {
            return Err(InspectParseError::Operational(
                "`--diff` requires exactly two receipt paths".into(),
            ));
        }
        let base_bytes = read_receipt_input(&diff_paths[0], max_receipt_bytes)?;
        let head_bytes = read_receipt_input(&diff_paths[1], max_receipt_bytes)?;
        let base = parse_and_validate_receipt_with_max_bytes(&base_bytes, max_receipt_bytes)?;
        let head = parse_and_validate_receipt_with_max_bytes(&head_bytes, max_receipt_bytes)?;
        let unknown_policy = UnknownFieldsPolicy::from(args.unknown_fields);
        if unknown_policy == UnknownFieldsPolicy::Warn {
            warn_unknown_fields("base receipt", &base.unrecognized_fields);
            warn_unknown_fields("head receipt", &head.unrecognized_fields);
        } else if !base.unrecognized_fields.is_empty() || !head.unrecognized_fields.is_empty() {
            let mut combined = base.unrecognized_fields.clone();
            combined.extend(head.unrecognized_fields.iter().cloned());
            combined.sort();
            combined.dedup();
            return Err(InspectParseError::Operational(format!(
                "unrecognized field(s) rejected by --unknown-fields=deny: {}",
                SanitizedInline(&combined.join(", "))
            )));
        }
        let diff: ReceiptDiff = diff_receipts(&base, &head, args.require_unchanged_specs);
        let output_text = render_diff(&diff, &render_opts);
        if let Some(expected_ledger) = &args.compare_ledger {
            let actual_ledger = render_diff(
                &diff,
                &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
            );
            compare_ledger_file(expected_ledger, &actual_ledger)?;
        }
        emit_output(args.output.as_deref(), &output_text)?;
        let has_invalid =
            !base.invariant_violations.is_empty() || !head.invariant_violations.is_empty();
        if has_invalid {
            eprintln!(
                "inspect diff failed: receipt envelope invariant violation(s) ({} base, {} head)",
                base.invariant_violations.len(),
                head.invariant_violations.len(),
            );
        }
        let unknown_warn_fail = unknown_policy == UnknownFieldsPolicy::Warn
            && !args.passive
            && (!base.unrecognized_fields.is_empty() || !head.unrecognized_fields.is_empty());
        if unknown_warn_fail {
            eprintln!(
                "inspect diff failed policy check: unrecognized receipt field(s) under --unknown-fields=warn (pass --passive to ignore)"
            );
        }
        if has_invalid
            || unknown_warn_fail
            || ((args.no_regressions || args.require_unchanged_specs) && diff.has_regressions)
        {
            return Ok(ExitCode::from(1));
        }
        return Ok(ExitCode::SUCCESS);
    }

    let path = args
        .receipt
        .as_deref()
        .ok_or_else(|| InspectParseError::Operational("missing receipt path argument".into()))?;
    let bytes = read_receipt_input(path, max_receipt_bytes)?;
    let mut env = parse_and_validate_receipt_with_max_bytes(&bytes, max_receipt_bytes)?;

    let unknown_policy = UnknownFieldsPolicy::from(args.unknown_fields);
    if unknown_policy == UnknownFieldsPolicy::Deny && !env.unrecognized_fields.is_empty() {
        return Err(InspectParseError::Operational(format!(
            "unrecognized field(s) rejected by --unknown-fields=deny: {}",
            SanitizedInline(&env.unrecognized_fields.join(", "))
        )));
    }
    if unknown_policy == UnknownFieldsPolicy::Warn {
        warn_unknown_fields("receipt", &env.unrecognized_fields);
    }

    let artifact_check = if let Some(dir) = &args.verify_artifacts {
        let summary = verify_retained_artifacts(
            dir,
            &env.receipt,
            &bytes,
            &env.receipt_sha256,
            args.require_exact_artifacts,
            max_receipt_bytes,
        )?;
        if summary.exact_match && summary.checked_files > 0 {
            env.profile.artifacts = ArtifactAxis::VerifiedLocal {
                path: summary.directory.clone(),
                checked_files: summary.checked_files,
            };
        }
        Some(summary)
    } else {
        None
    };

    let policy = PolicyRequirements {
        check: !args.passive,
        require_untainted: !args.passive || args.require_untainted,
        require_crate_scope: args.require_crate_scope,
        require_containment: args.require_containment,
        require_kernel_replay: args.require_kernel_replay,
        allowed_axioms: args.allowed_axioms.as_ref().map(|list| list.iter().cloned().collect()),
        allowed_unstable_features: args
            .allowed_unstable_features
            .as_ref()
            .map(|list| list.iter().cloned().collect()),
        forbid_incomplete_unstable_features: args.forbid_incomplete_unstable_features,
        unknown_fields: unknown_policy,
    };
    let mut policy_violations = env.evaluate_policy(&policy);
    if let Some(ref check) = artifact_check
        && !check.exact_match
    {
        policy_violations.extend(check.failures.clone());
    }

    if let Some(expected_ledger) = &args.compare_ledger {
        let actual_ledger = render_inspection(
            &env,
            artifact_check.as_ref(),
            &policy_violations,
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        compare_ledger_file(expected_ledger, &actual_ledger)?;
    }

    let rendered =
        render_inspection(&env, artifact_check.as_ref(), &policy_violations, &render_opts);
    emit_output(args.output.as_deref(), &rendered)?;

    if policy_violations.is_empty() { Ok(ExitCode::SUCCESS) } else { Ok(ExitCode::from(1)) }
}

fn resolve_inspect_use_color(
    passive: bool,
    has_output_file: bool,
    format: InspectFormat,
    color: ColorChoice,
    is_tty: impl FnOnce() -> bool,
    env: &EnvSnapshot,
) -> bool {
    if format != InspectFormat::Human {
        return false;
    }
    match color {
        ColorChoice::Always => true,
        ColorChoice::Never => false,
        ColorChoice::Auto => {
            if passive || has_output_file {
                return false;
            }
            resolve_stream_style(color, is_tty(), None, env).ansi_color
        }
    }
}

fn build_render_options(
    args: &InspectArgs,
    color: ColorChoice,
    quiet: bool,
    verbose: bool,
) -> RenderOptions {
    let format = InspectFormat::from(args.format);
    let env = EnvSnapshot::capture();
    let use_color = resolve_inspect_use_color(
        args.passive,
        args.output.is_some(),
        format,
        color,
        || io::stdout().is_terminal(),
        &env,
    );
    let sections = if args.section.is_empty() {
        None
    } else {
        Some(args.section.iter().copied().map(InspectSection::from).collect::<BTreeSet<_>>())
    };
    RenderOptions { format, use_color, full_digests: args.full_digests, quiet, verbose, sections }
}

fn warn_unknown_fields(label: &str, fields: &[String]) {
    if !fields.is_empty() {
        eprintln!(
            "WARNING: ignoring unrecognized field(s) in {label}: {}",
            SanitizedInline(&fields.join(", "))
        );
    }
}

fn read_receipt_input(path: &Path, max_bytes: usize) -> Result<Vec<u8>, InspectParseError> {
    if path == Path::new("-") {
        let mut buf = Vec::new();
        let limit = (max_bytes as u64).saturating_add(1);
        io::stdin()
            .lock()
            .take(limit)
            .read_to_end(&mut buf)
            .map_err(|e| InspectParseError::Operational(format!("cannot read stdin: {e}")))?;
        if buf.len() > max_bytes {
            let msg = if max_bytes < MAX_CONFIGURABLE_RECEIPT_JSON_BYTES {
                format!(
                    "stdin receipt exceeds {max_bytes}-byte limit (pass `--max-receipt-bytes` up \
                     to {MAX_CONFIGURABLE_RECEIPT_JSON_BYTES} to raise it)"
                )
            } else {
                format!("stdin receipt exceeds {max_bytes}-byte limit")
            };
            return Err(InspectParseError::Operational(msg));
        }
        return Ok(buf);
    }
    SafeFs::read_regular_nofollow_capped(path, max_bytes as u64, "inspect").map_err(|e| {
        if (e.message.contains("exceeds") || e.message.contains("exceeded"))
            && max_bytes < MAX_CONFIGURABLE_RECEIPT_JSON_BYTES
        {
            InspectParseError::Operational(format!(
                "{} (pass `--max-receipt-bytes` up to {MAX_CONFIGURABLE_RECEIPT_JSON_BYTES} to \
                 raise it)",
                e.message
            ))
        } else {
            InspectParseError::Operational(e.message)
        }
    })
}

fn compare_ledger_file(path: &Path, actual: &str) -> Result<(), InspectParseError> {
    let expected = SafeFs::read_regular_string_capped(path, MAX_LEDGER_BYTES, "inspect")
        .map_err(|e| InspectParseError::Operational(e.message))?;
    if expected != actual {
        return Err(InspectParseError::Policy(format!(
            "rendered ledger differs from expected ledger at {}",
            path.display()
        )));
    }
    Ok(())
}

fn emit_output(dest: Option<&Path>, text: &str) -> Result<(), InspectParseError> {
    match dest {
        None => {
            let mut stdout = io::stdout().lock();
            match stdout.write_all(text.as_bytes()).and_then(|()| stdout.flush()) {
                Ok(()) => Ok(()),
                Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Ok(()),
                Err(e) => Err(InspectParseError::Operational(format!("cannot write stdout: {e}"))),
            }
        }
        Some(path) => {
            if let Some(meta) = SafeFs::probe_symlink_metadata(path, "inspect")
                .map_err(|e| InspectParseError::Operational(e.message))?
                && (meta.file_type().is_symlink() || !meta.file_type().is_file())
            {
                return Err(InspectParseError::Operational(format!(
                    "refusing symlink or non-regular output destination: {}",
                    path.display()
                )));
            }
            let parent =
                path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
            let name = path.file_name().and_then(|n| n.to_str()).ok_or_else(|| {
                InspectParseError::Operational(format!("non-UTF-8 output path: {}", path.display()))
            })?;
            let (guard, mut file) = SafeFs::create_unique_temp(parent, name, "inspect")
                .map_err(|e| InspectParseError::Operational(e.message))?;
            file.write_all(text.as_bytes())
                .and_then(|()| file.flush())
                .map_err(|e| InspectParseError::Operational(format!("write temp output: {e}")))?;
            drop(file);
            fs::rename(guard.path(), path)
                .map_err(|e| InspectParseError::Operational(format!("rename output: {e}")))?;
            guard.disarm();
            Ok(())
        }
    }
}
