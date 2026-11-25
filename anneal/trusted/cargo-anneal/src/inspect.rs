// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Thin OS I/O shell for `cargo anneal inspect` wrapping the pure
//! [`crate::core::inspect`] verification, comparison, and rendering engine.

#[cfg(unix)]
use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
#[cfg(unix)]
use std::os::unix::ffi::OsStrExt as _;
use std::{
    collections::BTreeSet,
    env, fs,
    io::{self, IsTerminal as _, Read as _, Write as _},
    path::{Component, Path, PathBuf},
    process::ExitCode,
};

use clap::{Args, ValueEnum};

use crate::{
    core::{
        digest::sha256_bytes,
        inspect::{
            diff::{ReceiptDiff, diff_receipts},
            profile::ArtifactAxis,
            render::{
                ArtifactVerificationSummary, ColorChoice, InspectFormat, InspectSection,
                RenderOptions, render_diff, render_inspection,
            },
            schema::{
                InspectParseError, ParsedReceipt, PolicyRequirements, UnknownFieldsPolicy,
                parse_and_validate_receipt,
            },
            strict_json::{MAX_RECEIPT_JSON_BYTES, StrictJsonDom},
        },
        sanitize::SanitizedInline,
    },
    sys_util::SafeFs,
};

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

/// CLI-facing terminal color selector converted into pure [`ColorChoice`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum CliColorChoice {
    #[default]
    Auto,
    Always,
    Never,
}

impl From<CliColorChoice> for ColorChoice {
    fn from(value: CliColorChoice) -> Self {
        match value {
            CliColorChoice::Auto => Self::Auto,
            CliColorChoice::Always => Self::Always,
            CliColorChoice::Never => Self::Never,
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
    /// Control ANSI colors (`auto`, `always`, or `never`).
    #[arg(long, value_enum, default_value_t = CliColorChoice::Auto)]
    pub color: CliColorChoice,
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
    /// Show detailed selected bodies, closures, assumptions, and warnings.
    #[arg(short = 'v', long, conflicts_with = "quiet")]
    pub verbose: bool,
    /// Restrict human output to the primary summary status line and errors.
    #[arg(short = 'q', long, conflicts_with = "verbose")]
    pub quiet: bool,
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
    /// Exit `1` on any Tier A assurance regression between `--diff` receipts.
    #[arg(long, requires = "diff")]
    pub no_regressions: bool,
    /// Treat specification changes in `--diff` as Tier A regressions and exit
    /// `1` when any Tier A regression is detected.
    #[arg(long, requires = "diff")]
    pub require_unchanged_specs: bool,
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
pub fn main(args: InspectArgs) -> ExitCode {
    match run(&args) {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {}", SanitizedInline(err.message()));
            ExitCode::from(err.exit_code() as u8)
        }
    }
}

fn run(args: &InspectArgs) -> Result<ExitCode, InspectParseError> {
    let render_opts = build_render_options(args);

    if let Some(diff_paths) = &args.diff {
        if diff_paths.len() != 2 {
            return Err(InspectParseError::Operational(
                "`--diff` requires exactly two receipt paths".into(),
            ));
        }
        let base_bytes = read_receipt_input(&diff_paths[0])?;
        let head_bytes = read_receipt_input(&diff_paths[1])?;
        let base = parse_and_validate_receipt(&base_bytes)?;
        let head = parse_and_validate_receipt(&head_bytes)?;
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
    let bytes = read_receipt_input(path)?;
    let mut env = parse_and_validate_receipt(&bytes)?;

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

fn build_render_options(args: &InspectArgs) -> RenderOptions {
    let format = InspectFormat::from(args.format);
    let color = ColorChoice::from(args.color);
    let use_color = match color {
        ColorChoice::Always => true,
        ColorChoice::Never => false,
        ColorChoice::Auto => {
            !args.passive
                && args.output.is_none()
                && format == InspectFormat::Human
                && env::var_os("NO_COLOR").is_none_or(|v| v.is_empty())
                && io::stdout().is_terminal()
        }
    };
    let sections = if args.section.is_empty() {
        None
    } else {
        Some(args.section.iter().copied().map(InspectSection::from).collect::<BTreeSet<_>>())
    };
    RenderOptions {
        format,
        use_color,
        full_digests: args.full_digests,
        quiet: args.quiet,
        verbose: args.verbose,
        sections,
    }
}

fn warn_unknown_fields(label: &str, fields: &[String]) {
    if !fields.is_empty() {
        eprintln!(
            "WARNING: ignoring unrecognized field(s) in {label}: {}",
            SanitizedInline(&fields.join(", "))
        );
    }
}

fn read_receipt_input(path: &Path) -> Result<Vec<u8>, InspectParseError> {
    if path == Path::new("-") {
        let mut buf = Vec::new();
        let limit = (MAX_RECEIPT_JSON_BYTES as u64).saturating_add(1);
        io::stdin()
            .lock()
            .take(limit)
            .read_to_end(&mut buf)
            .map_err(|e| InspectParseError::Operational(format!("cannot read stdin: {e}")))?;
        if buf.len() > MAX_RECEIPT_JSON_BYTES {
            return Err(InspectParseError::Operational(format!(
                "stdin receipt exceeds {MAX_RECEIPT_JSON_BYTES}-byte limit"
            )));
        }
        return Ok(buf);
    }
    SafeFs::read_regular_nofollow_capped(path, MAX_RECEIPT_JSON_BYTES as u64, "inspect")
        .map_err(|e| InspectParseError::Operational(e.message))
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

fn is_safe_artifact_rel_path(rel: &str) -> bool {
    !rel.is_empty()
        && !rel.contains('\\')
        && Path::new(rel).components().all(|c| matches!(c, Component::Normal(_)))
}

#[cfg(unix)]
fn c_path_component(os: &std::ffi::OsStr, label: &str) -> Result<std::ffi::CString, String> {
    std::ffi::CString::new(os.as_bytes())
        .map_err(|_| format!("artifact path `{label}` contains interior NUL byte"))
}

#[cfg(unix)]
fn normalize_artifact_root(path: &Path) -> Result<std::borrow::Cow<'_, Path>, String> {
    use std::os::unix::ffi::OsStrExt;
    let bytes = path.as_os_str().as_bytes();
    // Trailing `/`, `/.`, or `/..` makes `lstat` and `open(..., O_NOFOLLOW)`
    // resolve a final symlink component; trim separators while preserving `/`
    // root and reject trailing `.` / `..` segments.
    let trimmed_len = bytes
        .iter()
        .rposition(|&b| b != b'/')
        .map_or(usize::from(!bytes.is_empty()), |idx| idx + 1);
    let trimmed = &bytes[..trimmed_len];
    let last_segment = trimmed.rsplit(|&b| b == b'/').next().unwrap_or(trimmed);
    if last_segment == b".." || (last_segment == b"." && trimmed != b".") {
        return Err(format!(
            "artifacts root must be a concrete non-dot directory path: {}",
            path.display()
        ));
    }
    if trimmed_len == bytes.len() {
        Ok(std::borrow::Cow::Borrowed(path))
    } else {
        Ok(std::borrow::Cow::Borrowed(Path::new(std::ffi::OsStr::from_bytes(trimmed))))
    }
}

#[cfg(not(unix))]
fn normalize_artifact_root(path: &Path) -> Result<std::borrow::Cow<'_, Path>, String> {
    let Some(raw) = path.to_str() else {
        return Ok(std::borrow::Cow::Borrowed(path));
    };
    let prefix_len = match path.components().next() {
        Some(Component::Prefix(p)) => p.as_os_str().to_str().map_or(0, str::len),
        _ => 0,
    };
    let (prefix, rest) = raw.split_at(prefix_len);
    let trimmed = rest.trim_end_matches(['/', '\\']);
    let last_segment = trimmed.rsplit(['/', '\\']).next().unwrap_or(trimmed);
    if last_segment == ".." || (last_segment == "." && !(prefix.is_empty() && trimmed == ".")) {
        return Err(format!(
            "artifacts root must be a concrete non-dot directory path: {}",
            path.display()
        ));
    }
    if trimmed.is_empty() {
        if rest.is_empty() {
            Ok(std::borrow::Cow::Borrowed(path))
        } else {
            Ok(std::borrow::Cow::Owned(PathBuf::from(format!("{prefix}{}", &rest[..1]))))
        }
    } else if trimmed.len() == rest.len() {
        Ok(std::borrow::Cow::Borrowed(path))
    } else {
        Ok(std::borrow::Cow::Borrowed(Path::new(&raw[..prefix_len + trimmed.len()])))
    }
}

#[cfg(unix)]
fn read_artifact_under_dir(dir: &Path, rel: &str) -> Result<Vec<u8>, String> {
    let dir = normalize_artifact_root(dir)?;
    let dir = dir.as_ref();
    if !is_safe_artifact_rel_path(rel) {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    let parts: Vec<&std::ffi::OsStr> = Path::new(rel)
        .components()
        .filter_map(|c| match c {
            Component::Normal(s) => Some(s),
            _ => None,
        })
        .collect();
    if parts.is_empty() {
        return Err(format!("empty artifact relative path `{rel}`"));
    }
    let c_root = c_path_component(dir.as_os_str(), &dir.display().to_string())?;
    // SAFETY: `c_root` is a valid NUL-terminated `CString` pointing to a live
    // buffer for the duration of the syscall.
    let root_fd = unsafe {
        libc::open(
            c_root.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if root_fd < 0 {
        let err = io::Error::last_os_error();
        return Err(format!("cannot open artifacts root {}: {err}", dir.display()));
    }
    // SAFETY: `root_fd >= 0` was just returned as a newly owned fd by `open`.
    let mut dir_fd = unsafe { OwnedFd::from_raw_fd(root_fd) };
    for parent_part in &parts[..parts.len() - 1] {
        let c_part = c_path_component(parent_part, rel)?;
        // SAFETY: `dir_fd` is an open directory fd and `c_part` is a valid
        // NUL-terminated `CString` alive for the syscall.
        let next_fd = unsafe {
            libc::openat(
                dir_fd.as_raw_fd(),
                c_part.as_ptr(),
                libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            )
        };
        if next_fd < 0 {
            let err = io::Error::last_os_error();
            return Err(format!(
                "artifact intermediate dir `{}` check failed in `{rel}`: {err}",
                Path::new(parent_part).display()
            ));
        }
        // SAFETY: `next_fd >= 0` was just returned as a newly owned fd by
        // `openat`.
        dir_fd = unsafe { OwnedFd::from_raw_fd(next_fd) };
    }
    let c_leaf = c_path_component(parts[parts.len() - 1], rel)?;
    // SAFETY: `dir_fd` is an open directory fd and `c_leaf` is a valid
    // NUL-terminated `CString` alive for the syscall.
    let leaf_fd = unsafe {
        libc::openat(
            dir_fd.as_raw_fd(),
            c_leaf.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC,
        )
    };
    if leaf_fd < 0 {
        let err = io::Error::last_os_error();
        return Err(format!("artifact `{rel}` check failed: {err}"));
    }
    // SAFETY: `leaf_fd >= 0` was just returned as a newly owned fd by `openat`.
    let file = fs::File::from(unsafe { OwnedFd::from_raw_fd(leaf_fd) });
    let meta = file.metadata().map_err(|e| format!("artifact `{rel}` stat failed: {e}"))?;
    if !meta.is_file() {
        return Err(format!("artifact `{rel}` must be a regular file"));
    }
    if meta.len() > MAX_ARTIFACT_FILE_BYTES {
        return Err(format!(
            "artifact `{rel}` exceeds {MAX_ARTIFACT_FILE_BYTES}-byte cap ({} bytes)",
            meta.len()
        ));
    }
    let mut buf = Vec::with_capacity(meta.len().min(64 * 1024) as usize);
    let limit = MAX_ARTIFACT_FILE_BYTES.saturating_add(1);
    file.take(limit)
        .read_to_end(&mut buf)
        .map_err(|e| format!("artifact `{rel}` read failed: {e}"))?;
    if (buf.len() as u64) > MAX_ARTIFACT_FILE_BYTES {
        return Err(format!("artifact `{rel}` exceeded {MAX_ARTIFACT_FILE_BYTES}-byte cap"));
    }
    Ok(buf)
}

/// Verify that `dir`, every intermediate component in `rel`, and the leaf file
/// are non-symlink filesystem entries of the expected kind.
#[cfg_attr(unix, allow(dead_code))]
fn validate_artifact_dir_chain(dir: &Path, rel: &str) -> Result<PathBuf, String> {
    let root_meta = SafeFs::probe_symlink_metadata(dir, "inspect")
        .map_err(|e| format!("artifacts directory check failed: {}", e.message))?
        .ok_or_else(|| format!("artifacts directory `{}` does not exist", dir.display()))?;
    if root_meta.file_type().is_symlink() || !root_meta.is_dir() {
        return Err(format!(
            "artifacts root `{}` must be a real directory (not a symlink)",
            dir.display()
        ));
    }
    let mut cur = dir.to_path_buf();
    let comps: Vec<&std::ffi::OsStr> = Path::new(rel)
        .components()
        .map(|c| match c {
            std::path::Component::Normal(s) => Ok(s),
            _ => Err(format!("unsafe artifact relative path `{rel}`")),
        })
        .collect::<Result<_, _>>()?;
    if comps.is_empty() {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    for (idx, comp) in comps.iter().enumerate() {
        cur.push(comp);
        let is_leaf = idx + 1 == comps.len();
        let meta = SafeFs::probe_symlink_metadata(&cur, "inspect")
            .map_err(|e| format!("artifact `{rel}` check failed: {}", e.message))?
            .ok_or_else(|| format!("missing artifact `{rel}`"))?;
        if meta.file_type().is_symlink() {
            return Err(format!("artifact `{rel}` traverses a symlink"));
        }
        if is_leaf {
            if !meta.is_file() {
                return Err(format!("artifact `{rel}` is not a regular file"));
            }
        } else if !meta.is_dir() {
            return Err(format!("artifact `{rel}` intermediate component is not a directory"));
        }
    }
    Ok(cur)
}

#[cfg(not(unix))]
fn read_artifact_under_dir(dir: &Path, rel: &str) -> Result<Vec<u8>, String> {
    let dir = normalize_artifact_root(dir)?;
    if !is_safe_artifact_rel_path(rel) {
        return Err(format!("unsafe artifact relative path `{rel}`"));
    }
    let target = validate_artifact_dir_chain(dir.as_ref(), rel)?;
    SafeFs::read_regular_nofollow_capped(&target, MAX_ARTIFACT_FILE_BYTES, "inspect")
        .map_err(|e| format!("artifact `{rel}` check failed: {}", e.message))
}

fn check_retained_result_json(
    dir: &Path,
    receipt_bytes: &[u8],
    receipt_sha256: &str,
    artifacts_field: Option<&str>,
    failures: &mut Vec<String>,
    checked_files: &mut usize,
) {
    let bytes = match read_artifact_under_dir(dir, "result.json") {
        Ok(b) => {
            *checked_files += 1;
            b
        }
        Err(msg) => {
            failures.push(msg);
            return;
        }
    };
    let actual_sha = sha256_bytes(&bytes);
    if actual_sha.eq_ignore_ascii_case(receipt_sha256) {
        return;
    }
    // `cargo anneal verify --artifacts <dir>` writes `result.json` in the
    // stage directory before retention, then sets `artifacts` on stdout.
    // Accept exact strict-JSON object equality once `artifacts` is stripped
    // from the inspected stdout receipt, provided retained `result.json` has
    // no `artifacts` override.
    if let Some(expected_artifacts) = artifacts_field
        && let Ok(mut receipt_val) = StrictJsonDom::parse(receipt_bytes)
        && let Ok(retained_val) = StrictJsonDom::parse(&bytes)
        && let (Some(receipt_obj), Some(retained_obj)) =
            (receipt_val.as_object_mut(), retained_val.as_object())
        && !retained_obj.contains_key("artifacts")
        && receipt_obj.get("artifacts").and_then(|v| v.as_str()) == Some(expected_artifacts)
    {
        receipt_obj.remove("artifacts");
        if *receipt_obj == *retained_obj {
            return;
        }
    }
    failures.push(format!(
        "artifact `result.json` SHA-256 mismatch: expected {receipt_sha256}, got {actual_sha}"
    ));
}

fn verify_retained_artifacts(
    dir: &Path,
    receipt: &ParsedReceipt,
    receipt_bytes: &[u8],
    receipt_sha256: &str,
    require_exact: bool,
) -> Result<ArtifactVerificationSummary, InspectParseError> {
    let dir = normalize_artifact_root(dir).map_err(InspectParseError::Operational)?;
    let dir = dir.as_ref();
    let dir_meta = fs::symlink_metadata(dir).map_err(|e| {
        InspectParseError::Operational(format!(
            "cannot inspect artifacts dir {}: {e}",
            dir.display()
        ))
    })?;
    if dir_meta.file_type().is_symlink() || !dir_meta.file_type().is_dir() {
        return Err(InspectParseError::Operational(format!(
            "artifacts root must be a regular non-symlink directory: {}",
            dir.display()
        )));
    }
    let mut failures = Vec::new();
    let mut checked_files = 0usize;

    let check_hash = |rel: &str, expected: &str, failures: &mut Vec<String>, count: &mut usize| {
        match read_artifact_under_dir(dir, rel) {
            Ok(bytes) => {
                *count += 1;
                let actual = sha256_bytes(&bytes);
                if !actual.eq_ignore_ascii_case(expected) {
                    failures.push(format!(
                        "artifact `{rel}` SHA-256 mismatch: expected {expected}, got {actual}"
                    ));
                }
            }
            Err(msg) => failures.push(msg),
        }
    };

    match receipt {
        ParsedReceipt::Failure(_) => {
            let result_path = dir.join("result.json");
            match SafeFs::probe_symlink_metadata(&result_path, "inspect") {
                Ok(Some(_)) => {
                    check_hash("result.json", receipt_sha256, &mut failures, &mut checked_files);
                }
                Ok(None) => {
                    if require_exact {
                        failures.push(
                            "missing retained result.json required by --require-exact-artifacts"
                                .into(),
                        );
                    }
                }
                Err(e) => {
                    failures.push(format!("retained result.json check failed: {}", e.message))
                }
            }
        }
        ParsedReceipt::Success(s) => {
            check_hash("request.json", &s.request_sha256, &mut failures, &mut checked_files);
            check_hash(
                "capture/capture.json",
                &s.capture_sha256,
                &mut failures,
                &mut checked_files,
            );
            for src in &s.sources {
                let rel = format!("rust/{}", src.relative_path);
                check_hash(&rel, &src.sha256, &mut failures, &mut checked_files);
            }
            if s.audit_sources.is_empty() {
                failures.push(
                    "receipt omits audit.sources required to verify retained Lean artifacts".into(),
                );
            } else {
                let mut has_model = false;
                let mut has_spec = false;
                let mut has_capture = false;
                let mut has_expected = false;
                let mut spec_count = 0usize;
                let mut on_disk_specs: Vec<(String, String)> = Vec::new();
                for entry in &s.audit_sources {
                    if entry.module.is_empty()
                        || !entry.module.split('.').all(|seg| {
                            !seg.is_empty()
                                && seg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                        })
                    {
                        failures.push(format!(
                            "audit.sources module `{}` is not a valid Lean module name",
                            entry.module
                        ));
                        continue;
                    }
                    let mod_path = entry.module.replace('.', "/");
                    let rel = match entry.role.as_str() {
                        "model" => {
                            has_model = true;
                            format!("anneal/trusted/lean/{mod_path}.lean")
                        }
                        "specification" => {
                            has_spec = true;
                            spec_count += 1;
                            format!("authored/{mod_path}.lean")
                        }
                        "capture" => {
                            has_capture = true;
                            format!("capture/{mod_path}.lean")
                        }
                        "expected" => {
                            has_expected = true;
                            format!("generated/{mod_path}.lean")
                        }
                        "proof" => {
                            if entry.module == "Anneal" || entry.module.starts_with("Anneal.") {
                                format!("anneal/theory/{mod_path}.lean")
                            } else {
                                format!("authored/{mod_path}.lean")
                            }
                        }
                        other => {
                            failures.push(format!(
                                "cannot map unknown audit.sources role `{other}` for `{}`",
                                entry.module
                            ));
                            continue;
                        }
                    };
                    match read_artifact_under_dir(dir, &rel) {
                        Ok(bytes) => {
                            checked_files += 1;
                            let actual = sha256_bytes(&bytes);
                            if !actual.eq_ignore_ascii_case(&entry.source_sha256) {
                                failures.push(format!(
                                    "artifact `{rel}` SHA-256 mismatch: expected {}, got {actual}",
                                    entry.source_sha256
                                ));
                            }
                            if entry.role == "specification" {
                                on_disk_specs.push((entry.module.clone(), actual));
                            }
                        }
                        Err(msg) => failures.push(msg),
                    }
                }
                if !has_model || !has_spec || !has_capture || !has_expected {
                    failures.push(
                        "audit.sources is missing required model/specification/capture/expected \
                         entries for artifact verification"
                            .into(),
                    );
                } else if on_disk_specs.len() == spec_count
                    && let Ok(encoded_specs) = serde_json::to_vec_pretty(&on_disk_specs)
                {
                    let actual_spec_manifest = sha256_bytes(&encoded_specs);
                    if !actual_spec_manifest.eq_ignore_ascii_case(&s.specification_manifest_sha256)
                    {
                        failures.push(format!(
                            "retained specification manifest SHA-256 mismatch: expected {}, \
                             got {actual_spec_manifest}",
                            s.specification_manifest_sha256
                        ));
                    }
                }
            }
            if require_exact {
                check_retained_result_json(
                    dir,
                    receipt_bytes,
                    receipt_sha256,
                    s.artifacts.as_deref(),
                    &mut failures,
                    &mut checked_files,
                );
            }
        }
    }

    Ok(ArtifactVerificationSummary {
        directory: dir.display().to_string(),
        exact_match: failures.is_empty(),
        checked_files,
        failures,
    })
}

#[cfg(all(test, unix))]
mod tests {
    use std::{fs, os::unix::fs::symlink};

    use super::validate_artifact_dir_chain;

    #[test]
    fn validate_artifact_dir_chain_rejects_root_intermediate_and_leaf_symlinks() {
        let tmp = tempfile::tempdir().unwrap();
        let real_root = tmp.path().join("real_art");
        let outside = tmp.path().join("outside");
        fs::create_dir_all(real_root.join("authored")).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(real_root.join("authored/Spec.lean"), b"-- ok\n").unwrap();
        fs::write(outside.join("Spec.lean"), b"-- outside\n").unwrap();

        assert!(validate_artifact_dir_chain(&real_root, "authored/Spec.lean").is_ok());

        // Symlinked root directory.
        let sym_root = tmp.path().join("sym_art");
        symlink(&real_root, &sym_root).unwrap();
        assert!(validate_artifact_dir_chain(&sym_root, "authored/Spec.lean").is_err());

        // Symlinked intermediate directory.
        let escaped_art = tmp.path().join("escaped_art");
        fs::create_dir_all(&escaped_art).unwrap();
        symlink(&outside, escaped_art.join("authored")).unwrap();
        assert!(validate_artifact_dir_chain(&escaped_art, "authored/Spec.lean").is_err());

        // Symlinked leaf file.
        symlink(outside.join("Spec.lean"), real_root.join("authored/Link.lean")).unwrap();
        assert!(validate_artifact_dir_chain(&real_root, "authored/Link.lean").is_err());
    }
}
