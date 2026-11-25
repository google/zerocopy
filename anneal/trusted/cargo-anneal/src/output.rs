// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Terminal capability resolution, type-enforced untrusted text sanitization,
//! `BrokenPipe`-safe stream writers, synchronous phase progress, and the
//! five-tier human verification card shared across `cargo-anneal` subcommands.
//!
//! Because `cargo-anneal` processes untrusted Rust sources, Lean modules, and
//! filesystem paths (`THREAT_MODEL.md` section 1), terminal rendering is an
//! anti-spoofing boundary:
//! 1. Untrusted strings reach human text formatters exclusively through
//!    [`SanitizedInline`] (single-line) and [`SanitizedBlock`] (`"  | "`
//!    column-0 guttered multi-line), neutralizing 7-bit/8-bit ANSI CSI/OSC
//!    sequences, carriage-return overwrites, Unicode bidirectional controls,
//!    and invisible format or tag codepoints.
//! 2. Unqualified `[OK]` and green SGR (`1;32`) styling appear exclusively on
//!    untainted, whole-crate (`scope.kind == "crate"`), zero-`spec_warnings`
//!    verifications under active elaborator containment.
//! 3. Machine JSON output (`--format json` and `--receipt-out`) bypasses ANSI
//!    styling unconditionally regardless of `--color=always` or environment
//!    variables.

use std::{
    env, fmt,
    io::{self, IsTerminal as _, Write},
    process::ExitCode,
    time::Instant,
};

use serde_json::Value;

/// Maximum structured failure items (`unsupported` entries or Lean diagnostics)
/// rendered inline before summarizing remaining items in non-`--verbose` mode.
pub const MAX_INLINE_FAILURE_ITEMS: usize = 5;

/// Maximum lines of a multi-line failure `detail` rendered inline in
/// non-`--verbose` human mode.
pub const MAX_DETAIL_LINES: usize = 20;

/// Maximum selected root or instantiation paths listed inline in
/// non-`--verbose` human mode.
pub const MAX_INLINE_SELECTED: usize = 8;

const RESET_SGR: &str = "\x1b[0m";
const DIM_SGR: &str = "\x1b[2m";
const BOLD_SGR: &str = "\x1b[1m";

/// User-requested ANSI color policy (`--color`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum ColorChoice {
    /// Emit ANSI SGR escapes on human streams only when the target stream is an
    /// interactive terminal (honoring `CARGO_TERM_COLOR`, non-empty `NO_COLOR`,
    /// `TERM=dumb`, and `CLICOLOR_FORCE` / `FORCE_COLOR`).
    #[default]
    Auto,
    /// Always emit ANSI SGR escapes on human-formatted streams (never in JSON).
    Always,
    /// Never emit ANSI SGR escapes.
    Never,
}

/// Primary `stdout` representation for `cargo anneal verify` (`--format`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, clap::ValueEnum)]
pub enum VerifyFormat {
    /// Render the five-tier human verification card on `stdout`.
    #[default]
    Human,
    /// Emit canonical Receipt Schema v3 JSON on `stdout`.
    Json,
    /// Emit the human card when `stdout` is a terminal and Receipt Schema v3
    /// JSON otherwise.
    Auto,
}

/// Concrete primary `stdout` format after resolving [`VerifyFormat::Auto`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResolvedVerifyFormat {
    Human,
    Json,
}

impl VerifyFormat {
    /// Resolve `self` against `stdout_is_tty`.
    pub const fn resolve(self, stdout_is_tty: bool) -> ResolvedVerifyFormat {
        match self {
            Self::Human => ResolvedVerifyFormat::Human,
            Self::Json => ResolvedVerifyFormat::Json,
            Self::Auto => {
                if stdout_is_tty {
                    ResolvedVerifyFormat::Human
                } else {
                    ResolvedVerifyFormat::Json
                }
            }
        }
    }
}

/// Immutable snapshot of terminal-related environment variables captured once
/// at process startup (or synthesized directly in unit tests).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EnvSnapshot {
    pub cargo_term_color: Option<String>,
    pub no_color: Option<String>,
    pub term: Option<String>,
    pub clicolor_force: Option<String>,
    pub force_color: Option<String>,
    pub columns: Option<String>,
    pub ci: bool,
    pub test_term_width: Option<u16>,
    pub test_redact_timing: bool,
}

impl EnvSnapshot {
    /// Capture terminal and CI environment variables from the current process.
    pub fn capture() -> Self {
        let get = |key: &str| env::var_os(key).map(|v| v.to_string_lossy().into_owned());
        let non_empty_non_zero = |key: &str| {
            env::var_os(key).is_some_and(|v| {
                let s = v.to_string_lossy();
                !s.is_empty() && s != "0" && !s.eq_ignore_ascii_case("false")
            })
        };
        let test_term_width = get("ANNEAL_TEST_TERM_WIDTH")
            .and_then(|raw| raw.parse::<u16>().ok())
            .filter(|w| (40..=500).contains(w));
        let test_redact_timing = non_empty_non_zero("ANNEAL_TEST_REDACT_TIMING");
        Self {
            cargo_term_color: get("CARGO_TERM_COLOR"),
            no_color: get("NO_COLOR"),
            term: get("TERM"),
            clicolor_force: get("CLICOLOR_FORCE"),
            force_color: get("FORCE_COLOR"),
            columns: get("COLUMNS"),
            ci: non_empty_non_zero("CI") || non_empty_non_zero("GITHUB_ACTIONS"),
            test_term_width,
            test_redact_timing,
        }
    }

    /// Return whether `TERM` is explicitly `"dumb"`.
    pub fn is_dumb_term(&self) -> bool {
        self.term.as_deref() == Some("dumb")
    }
}

/// Resolved capability descriptor for a single output stream (`stdout` or
/// `stderr`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StreamStyle {
    pub is_tty: bool,
    pub ansi_color: bool,
    pub width: usize,
}

fn is_force_color_enabled(raw: Option<&str>) -> bool {
    raw.is_some_and(|v| !v.is_empty() && v != "0")
}

/// Resolve [`StreamStyle`] for one stream independently of the other stream.
///
/// Precedence order:
/// 1. Explicit `--color` (`always` / `never`).
/// 2. `CARGO_TERM_COLOR` (`always` / `never`, ASCII case-insensitive).
/// 3. Non-empty `NO_COLOR` (`false`, overriding `CLICOLOR_FORCE` and
///    `FORCE_COLOR`; empty `NO_COLOR=""` is treated as unset per
///    `no-color.org`).
/// 4. `TERM=dumb` (`false`).
/// 5. Non-empty, non-`"0"` `CLICOLOR_FORCE` or `FORCE_COLOR` (`true`).
/// 6. Stream `is_tty` (strict terminal detection).
pub fn resolve_stream_style(
    flag: ColorChoice,
    is_tty: bool,
    fd_width: Option<usize>,
    env: &EnvSnapshot,
) -> StreamStyle {
    let ansi_color = match flag {
        ColorChoice::Never => false,
        ColorChoice::Always => true,
        ColorChoice::Auto => {
            if let Some(cargo_color) = env.cargo_term_color.as_deref() {
                if cargo_color.eq_ignore_ascii_case("never") {
                    false
                } else if cargo_color.eq_ignore_ascii_case("always") {
                    true
                } else {
                    resolve_auto_color_after_cargo(is_tty, env)
                }
            } else {
                resolve_auto_color_after_cargo(is_tty, env)
            }
        }
    };
    let width = if let Some(pinned) = env.test_term_width.filter(|w| (40..=500).contains(w)) {
        usize::from(pinned)
    } else if is_tty {
        fd_width
            .filter(|w| (40..=500).contains(w))
            .or_else(|| {
                env.columns
                    .as_deref()
                    .and_then(|s| s.parse::<usize>().ok())
                    .filter(|w| (40..=500).contains(w))
            })
            .unwrap_or(80)
    } else {
        80
    };
    StreamStyle { is_tty, ansi_color, width }
}

fn resolve_auto_color_after_cargo(is_tty: bool, env: &EnvSnapshot) -> bool {
    if env.no_color.as_deref().is_some_and(|v| !v.is_empty()) {
        return false;
    }
    if env.is_dumb_term() {
        return false;
    }
    if is_force_color_enabled(env.clicolor_force.as_deref())
        || is_force_color_enabled(env.force_color.as_deref())
    {
        return true;
    }
    is_tty
}

#[cfg(unix)]
fn query_fd_columns(fd: libc::c_int) -> Option<usize> {
    // SAFETY: `winsize` is a plain-old-data C struct zero-initialized before
    // `ioctl(fd, TIOCGWINSZ, &mut ws)` writes terminal dimensions for the
    // standard stream descriptor `STDOUT_FILENO` or `STDERR_FILENO`.
    unsafe {
        let mut ws: libc::winsize = std::mem::zeroed();
        if libc::ioctl(fd, libc::TIOCGWINSZ, &mut ws) == 0 && ws.ws_col > 0 {
            Some(usize::from(ws.ws_col))
        } else {
            None
        }
    }
}

#[cfg(not(unix))]
fn query_fd_columns(_fd: i32) -> Option<usize> {
    None
}

pub use crate::core::sanitize::is_dangerous_unicode;

fn push_escaped_block_char(out: &mut String, c: char) {
    match c {
        '\t' => out.push_str("    "),
        '\n' => out.push_str("\\n"),
        '\r' => out.push_str("\\r"),
        _ if is_dangerous_unicode(c) => {
            use fmt::Write as _;
            let _ = write!(out, "\\u{{{:04X}}}", c as u32);
        }
        _ => out.push(c),
    }
}

/// Single-line untrusted text wrapper guaranteeing zero raw control, escape,
/// newline, carriage-return, bidirectional, or invisible format codepoints.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SanitizedInline(String);

impl SanitizedInline {
    /// Sanitize an arbitrary untrusted string into a single-line safe token.
    pub fn new(raw: &str) -> Self {
        Self(crate::core::sanitize::sanitize_inline_string(raw))
    }

    /// Borrow the sanitized UTF-8 string slice.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Render as a GitHub Flavored Markdown inline code span, delegating to
    /// [`crate::core::sanitize`] so table-cell pipe delimiters (including odd
    /// backslash runs before `|`), empty inputs, and CommonMark §6.1 padding
    /// follow the single shared TCB sanitizer.
    pub fn to_gfm_code_span(&self, in_table_cell: bool) -> String {
        if in_table_cell {
            crate::core::sanitize::format_gfm_code_cell(&self.0)
        } else {
            crate::core::sanitize::format_gfm_code_span(&self.0)
        }
    }
}

impl fmt::Display for SanitizedInline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Multi-line untrusted text wrapper normalizing `\r\n` line breaks, escaping
/// lone `\r` and all control/bidirectional codepoints, and enforcing a fixed
/// `"  | "` column-0 gutter when rendered into human cards.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SanitizedBlock {
    lines: Vec<SanitizedInline>,
}

impl SanitizedBlock {
    /// Sanitize an arbitrary multi-line untrusted string.
    pub fn new(raw: &str) -> Self {
        if raw.is_empty() {
            return Self { lines: Vec::new() };
        }
        let normalized = raw.replace("\r\n", "\n");
        let trimmed = normalized.strip_suffix('\n').unwrap_or(&normalized);
        let lines = trimmed
            .split('\n')
            .map(|line| {
                let mut clean = String::with_capacity(line.len());
                for c in line.chars() {
                    push_escaped_block_char(&mut clean, c);
                }
                SanitizedInline(clean)
            })
            .collect();
        Self { lines }
    }

    /// Return the sanitized lines.
    pub fn lines(&self) -> &[SanitizedInline] {
        &self.lines
    }

    /// Return whether the block has zero lines.
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }

    /// Append `"  | "`-guttered lines to `out`, truncating at `max_lines` when
    /// `Some(limit)` is exceeded.
    pub fn write_guttered(&self, out: &mut String, max_lines: Option<usize>) {
        use fmt::Write as _;
        let total = self.lines.len();
        let limit = max_lines.unwrap_or(total);
        for line in self.lines.iter().take(limit) {
            let _ = writeln!(out, "  | {line}");
        }
        if total > limit {
            let omitted = total - limit;
            let _ = writeln!(out, "  | ... (+{omitted} more line(s); pass --verbose to show all)");
        }
    }

    /// Append sanitized lines (without column-0 gutter) to `out` for `stderr`
    /// compiler-diagnostic forwarding.
    pub fn write_plain_lines(&self, out: &mut String) {
        use fmt::Write as _;
        for line in &self.lines {
            let _ = writeln!(out, "{line}");
        }
    }
}

/// Five-tier mutually exclusive verification verdict badge.
///
/// Green styling (`SGR 1;32`) and `[OK]` are structurally restricted to
/// [`AssuranceBadge::Ok`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssuranceBadge {
    /// Verification or operational failure (`exit 1` or `exit 2`).
    Fail,
    /// Passed only under one or more `--allow-*` taint relaxations.
    Tainted,
    /// Untainted pass carrying advisory anti-vacuity `spec_warnings`.
    Warn,
    /// Untainted, zero-warning pass covering `SelectedUnit` scope only.
    Scoped,
    /// Untainted, zero-warning, whole-crate (`scope.kind == "crate"`) pass.
    Ok,
}

impl AssuranceBadge {
    /// Pure 7-bit ASCII bracketed badge token.
    pub const fn as_tag(self) -> &'static str {
        match self {
            Self::Fail => "[FAIL]",
            Self::Tainted => "[TAINTED]",
            Self::Warn => "[WARN]",
            Self::Scoped => "[SCOPED]",
            Self::Ok => "[OK]",
        }
    }

    /// ANSI SGR prefix applied strictly when `StreamStyle::ansi_color` is
    /// `true`.
    pub const fn sgr_prefix(self) -> &'static str {
        match self {
            Self::Fail => "\x1b[1;31m",
            Self::Tainted | Self::Warn => "\x1b[1;33m",
            Self::Scoped => "\x1b[1;36m",
            Self::Ok => "\x1b[1;32m",
        }
    }

    /// Format `self` with optional SGR styling and an immediate `SGR 0` reset.
    pub fn render_tag(self, ansi_color: bool) -> String {
        if ansi_color {
            format!("{}{}{}", self.sgr_prefix(), self.as_tag(), RESET_SGR)
        } else {
            self.as_tag().to_owned()
        }
    }
}

fn style_span(text: &str, sgr: &str, ansi_color: bool) -> String {
    if ansi_color { format!("{sgr}{text}{RESET_SGR}") } else { text.to_owned() }
}

/// Synchronous verification pipeline phases reported on `stderr`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyPhase {
    Stage,
    Capture { crate_name: SanitizedInline },
    Toolchain,
    SpecPreflight { module_count: usize },
    Elaborate { done: usize, total: usize, cached: usize },
    Audit,
}

impl VerifyPhase {
    fn step_index(&self) -> u8 {
        match self {
            Self::Stage => 1,
            Self::Capture { .. } => 2,
            Self::Toolchain => 3,
            Self::SpecPreflight { .. } => 4,
            Self::Elaborate { .. } => 5,
            Self::Audit => 6,
        }
    }

    /// Format the single-line ASCII progress label for this phase.
    pub fn label(&self) -> String {
        match self {
            Self::Stage => "[1/6] Staging inputs and resolving request".to_owned(),
            Self::Capture { crate_name } => {
                format!("[2/6] Capturing Rust MIR ({crate_name})")
            }
            Self::Toolchain => "[3/6] Admitting Lean toolchain and locks".to_owned(),
            Self::SpecPreflight { module_count } => {
                format!("[4/6] Checking specification preflight ({module_count} module(s))")
            }
            Self::Elaborate { done, total, cached } => {
                format!("[5/6] Elaborating Lean modules ({done}/{total}, {cached} cached)")
            }
            Self::Audit => "[6/6] Auditing kernel replay and input bindings".to_owned(),
        }
    }
}

/// Realization mode for `stderr` phase progress.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgressMode {
    /// Single-line `\r\x1b[2K` status updates on interactive non-CI terminals
    /// (never hides the cursor via `\x1b[?25l`).
    TransientTty,
    /// Newline-terminated milestone log lines (`--verbose` or `CI` human mode).
    LineLog,
    /// Zero progress bytes on `stderr` (`--format json`, `--quiet`, or piped
    /// non-CI `stderr`).
    Silent,
}

impl ProgressMode {
    /// Choose the `stderr` progress realization from resolved CLI and stream
    /// state.
    pub fn select(
        resolved_format: ResolvedVerifyFormat,
        quiet: bool,
        verbose: bool,
        stderr_style: StreamStyle,
        env: &EnvSnapshot,
    ) -> Self {
        if resolved_format == ResolvedVerifyFormat::Json || quiet {
            Self::Silent
        } else if verbose || env.ci {
            Self::LineLog
        } else if stderr_style.is_tty && !env.is_dumb_term() {
            Self::TransientTty
        } else {
            Self::Silent
        }
    }
}

fn truncate_to_char_width(s: &str, max_chars: usize) -> &str {
    if max_chars == 0 {
        return "";
    }
    match s.char_indices().nth(max_chars) {
        Some((byte_idx, _)) => &s[..byte_idx],
        None => s,
    }
}

/// Write all `bytes` to `writer`, classifying `BrokenPipe` separately from
/// operational write failures so callers never panic with exit `101`.
pub fn write_all_safe<W: Write>(writer: &mut W, bytes: &[u8]) -> io::Result<()> {
    writer.write_all(bytes)?;
    writer.flush()
}

/// Complete a subcommand by writing `primary_bytes` to `stdout_writer` (after
/// clearing any transient `stderr` progress line) while strictly preserving
/// non-zero `computed_exit` codes (`1` or `2`) on `BrokenPipe`.
pub fn finish_with_writers<Out: Write, Err: Write>(
    session: &mut OutputSession<Out, Err>,
    primary_bytes: &[u8],
    computed_exit: u8,
) -> ExitCode {
    session.clear_transient_stderr();
    match write_all_safe(&mut session.stdout, primary_bytes) {
        Ok(()) => ExitCode::from(computed_exit),
        Err(err) if err.kind() == io::ErrorKind::BrokenPipe => ExitCode::from(computed_exit),
        Err(err) => {
            let msg = SanitizedInline::new(&err.to_string());
            let _ = session.write_stderr_error(&format!("stdout write failed: {msg}"));
            ExitCode::from(2)
        }
    }
}

/// Owns `stdout` and `stderr` writers, resolved per-stream styles, and the
/// zero-thread phase progress state machine.
pub struct OutputSession<Out: Write = io::Stdout, Err: Write = io::Stderr> {
    pub stdout: Out,
    pub stderr: Err,
    pub stdout_style: StreamStyle,
    pub stderr_style: StreamStyle,
    pub quiet: bool,
    pub verbose: bool,
    pub progress_mode: ProgressMode,
    pub redact_timing: bool,
    transient_dirty: bool,
    active_line_phase: Option<(String, u8, Instant)>,
}

impl OutputSession<io::Stdout, io::Stderr> {
    /// Construct a live process `OutputSession` from global CLI flags and
    /// `VerifyFormat` (pass `VerifyFormat::Human` for non-`verify` commands).
    pub fn live(
        color: ColorChoice,
        quiet: bool,
        verbose: bool,
        verify_format: VerifyFormat,
    ) -> (Self, ResolvedVerifyFormat) {
        let env = EnvSnapshot::capture();
        let stdout = io::stdout();
        let stderr = io::stderr();
        let stdout_tty = stdout.is_terminal();
        let stderr_tty = stderr.is_terminal();
        #[cfg(unix)]
        let (stdout_w, stderr_w) = (
            if stdout_tty { query_fd_columns(libc::STDOUT_FILENO) } else { None },
            if stderr_tty { query_fd_columns(libc::STDERR_FILENO) } else { None },
        );
        #[cfg(not(unix))]
        let (stdout_w, stderr_w) = (query_fd_columns(1), query_fd_columns(2));

        let stdout_style = resolve_stream_style(color, stdout_tty, stdout_w, &env);
        let stderr_style = resolve_stream_style(color, stderr_tty, stderr_w, &env);
        let resolved_format = verify_format.resolve(stdout_tty);
        let progress_mode =
            ProgressMode::select(resolved_format, quiet, verbose, stderr_style, &env);
        (
            Self {
                stdout,
                stderr,
                stdout_style,
                stderr_style,
                quiet,
                verbose,
                progress_mode,
                redact_timing: env.test_redact_timing,
                transient_dirty: false,
                active_line_phase: None,
            },
            resolved_format,
        )
    }
}

impl<Out: Write, Err: Write> OutputSession<Out, Err> {
    /// Construct an `OutputSession` over custom writers (for deterministic
    /// unit and `BrokenPipe` tests).
    #[allow(clippy::too_many_arguments)]
    pub fn with_writers(
        stdout: Out,
        stderr: Err,
        stdout_style: StreamStyle,
        stderr_style: StreamStyle,
        quiet: bool,
        verbose: bool,
        progress_mode: ProgressMode,
        redact_timing: bool,
    ) -> Self {
        Self {
            stdout,
            stderr,
            stdout_style,
            stderr_style,
            quiet,
            verbose,
            progress_mode,
            redact_timing,
            transient_dirty: false,
            active_line_phase: None,
        }
    }

    /// Erase any active transient `\r\x1b[2K` progress status on `stderr` and
    /// flush any completed `LineLog` milestone before diagnostic or final
    /// `stdout` output.
    pub fn clear_transient_stderr(&mut self) {
        if self.transient_dirty {
            let _ = write_all_safe(&mut self.stderr, b"\r\x1b[2K");
            self.transient_dirty = false;
        }
    }

    fn flush_completed_line_phase(&mut self, next_step: Option<u8>) {
        if let Some((prev_label, prev_step, started)) = self.active_line_phase.take() {
            if next_step == Some(prev_step) {
                // Keep the original start timestamp across intra-phase updates
                // (such as `[5/6] Elaborating Lean modules (k/N)`), emitting a
                // single completion line when phase 5 finishes.
                self.active_line_phase = Some((prev_label, prev_step, started));
                return;
            }
            let line = if self.redact_timing {
                format!("{prev_label} ... ok\n")
            } else {
                format!("{prev_label} ... ok ({} ms)\n", started.elapsed().as_millis())
            };
            let _ = write_all_safe(&mut self.stderr, line.as_bytes());
        }
    }

    /// Report transition to or progress within `phase` on `stderr`.
    pub fn report_phase(&mut self, phase: VerifyPhase) {
        match self.progress_mode {
            ProgressMode::Silent => {}
            ProgressMode::TransientTty => {
                let label = phase.label();
                let max_cols = self.stderr_style.width.saturating_sub(1);
                let clipped = truncate_to_char_width(&label, max_cols);
                let rendered = if self.stderr_style.ansi_color {
                    format!("\r\x1b[2K{DIM_SGR}{clipped}{RESET_SGR}")
                } else {
                    format!("\r\x1b[2K{clipped}")
                };
                let _ = write_all_safe(&mut self.stderr, rendered.as_bytes());
                self.transient_dirty = true;
            }
            ProgressMode::LineLog => {
                let step = phase.step_index();
                let label = phase.label();
                if let Some((_, prev_step, started)) = self.active_line_phase.as_ref()
                    && *prev_step == step
                {
                    let started = *started;
                    self.active_line_phase = Some((label, step, started));
                    return;
                }
                self.flush_completed_line_phase(Some(step));
                self.active_line_phase = Some((label, step, Instant::now()));
            }
        }
    }

    /// Mark the active `LineLog` phase complete (on passing runs) and clear any
    /// transient status line.
    pub fn finish_phases(&mut self, succeeded: bool) {
        if succeeded && self.progress_mode == ProgressMode::LineLog {
            self.flush_completed_line_phase(None);
        } else {
            self.active_line_phase = None;
        }
        self.clear_transient_stderr();
    }

    /// Emit a mandatory taint warning banner to `stderr` (never suppressed by
    /// `--quiet`).
    pub fn write_taint_banner(&mut self, banner: &str) {
        self.clear_transient_stderr();
        let line = if self.stderr_style.ansi_color {
            format!("\x1b[1;33m{banner}{RESET_SGR}\n")
        } else {
            format!("{banner}\n")
        };
        let _ = write_all_safe(&mut self.stderr, line.as_bytes());
    }

    /// Emit a sanitized anti-vacuity specification warning on `stderr` unless
    /// `--quiet` is active.
    pub fn write_spec_warning(
        &mut self,
        code: &SanitizedInline,
        decl: &SanitizedInline,
        body: Option<&SanitizedInline>,
        msg: &SanitizedInline,
    ) {
        if self.quiet {
            return;
        }
        self.clear_transient_stderr();
        let text = match body {
            Some(b) => format!("WARNING [anti-vacuity: {code}] {decl} (body `{b}`): {msg}"),
            None => format!("WARNING [anti-vacuity: {code}] {decl}: {msg}"),
        };
        let line = if self.stderr_style.ansi_color {
            format!("\x1b[1;33m{text}{RESET_SGR}\n")
        } else {
            format!("{text}\n")
        };
        let _ = write_all_safe(&mut self.stderr, line.as_bytes());
    }

    /// Emit sanitized `rustc` diagnostics on `stderr` when capture fails.
    pub fn write_compiler_stderr(&mut self, raw_stderr: &[u8]) {
        if raw_stderr.is_empty() {
            return;
        }
        self.clear_transient_stderr();
        let lossy = String::from_utf8_lossy(raw_stderr);
        let block = SanitizedBlock::new(&lossy);
        let mut buf = String::new();
        block.write_plain_lines(&mut buf);
        let _ = write_all_safe(&mut self.stderr, buf.as_bytes());
    }

    /// Emit an operational or CLI error message on `stderr`.
    pub fn write_stderr_error(&mut self, message: &str) -> io::Result<()> {
        use fmt::Write as _;
        self.clear_transient_stderr();
        let block = SanitizedBlock::new(message);
        let prefix = style_span("error:", "\x1b[1;31m", self.stderr_style.ansi_color);
        let mut buf = String::new();
        if let Some((first, rest)) = block.lines().split_first() {
            let _ = writeln!(buf, "{prefix} {first}");
            for line in rest {
                let _ = writeln!(buf, "  | {line}");
            }
        } else {
            let _ = writeln!(buf, "{prefix}");
        }
        match write_all_safe(&mut self.stderr, buf.as_bytes()) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == io::ErrorKind::BrokenPipe => Ok(()),
            Err(err) => Err(err),
        }
    }

    /// Emit pre-formatted `clap` usage diagnostics on `stderr`, suppressing
    /// `BrokenPipe`.
    pub fn write_clap_error(&mut self, error: &clap::Error) {
        self.clear_transient_stderr();
        let rendered = error.to_string();
        let _ = write_all_safe(&mut self.stderr, rendered.as_bytes());
    }
}

/// Census coverage counts computed over `CaptureReceipt.selected` and
/// `CaptureReceipt.census`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CensusCoverage {
    /// Verified callable bodies in `Captured.program` (`selected.len()`).
    pub verified_bodies: usize,
    /// Required body-owning items in `census` with `selected == true`.
    pub selected_required_bodies: usize,
    /// Total required body-owning items in `census` (`has_body && required`).
    pub required_bodies: usize,
    /// Required body-owning items left unverified
    /// (`has_body && required && !selected`).
    pub unverified_required_bodies: usize,
    /// Non-body required items left unverified
    /// (`!has_body && required && !selected`, such as `static`, `const`,
    /// `global_asm!`, or `extern` blocks).
    pub unverified_required_owners: usize,
    /// Total unverified required crate items (`required && !selected`).
    pub unverified_required_total: usize,
    /// Sorted sanitized paths of verified bodies.
    pub selected_paths: Vec<SanitizedInline>,
}

impl CensusCoverage {
    /// Compute deterministic coverage statistics from a Receipt Schema v3 JSON
    /// object.
    pub fn from_receipt(receipt: &Value) -> Self {
        let mut selected_paths: Vec<SanitizedInline> = receipt["selected"]
            .as_array()
            .map(|arr| {
                arr.iter()
                    .filter_map(|item| item["path"].as_str().or_else(|| item.as_str()))
                    .map(SanitizedInline::new)
                    .collect()
            })
            .unwrap_or_default();
        selected_paths.sort();

        let verified_bodies = selected_paths.len();
        let mut selected_required_bodies = 0usize;
        let mut required_bodies = 0usize;
        let mut unverified_required_bodies = 0usize;
        let mut unverified_required_owners = 0usize;

        if let Some(census) = receipt["census"].as_array() {
            for item in census {
                let has_body = item["has_body"].as_bool().unwrap_or(false);
                let required = item["required"].as_bool().unwrap_or(false);
                let selected = item["selected"].as_bool().unwrap_or(false);
                if required {
                    if has_body {
                        required_bodies += 1;
                        if selected {
                            selected_required_bodies += 1;
                        } else {
                            unverified_required_bodies += 1;
                        }
                    } else if !selected {
                        unverified_required_owners += 1;
                    }
                }
            }
        }

        Self {
            verified_bodies,
            selected_required_bodies,
            required_bodies,
            unverified_required_bodies,
            unverified_required_owners,
            unverified_required_total: unverified_required_bodies + unverified_required_owners,
            selected_paths,
        }
    }
}

/// Routine Stage-0 TCB baseline assumptions that do not narrow the semantic
/// meaning of a verified result beyond the documented Stage-0 trust boundary.
///
/// Any assumption outside this exact set (including Profile v2's
/// entry-validity narrowing, experimental MIR semantics, unpinned Lean,
/// Tier 2 Landlock/seccomp shared-namespace caveats, or any future narrowing)
/// is surfaced verbatim as a non-maskable `! CAVEAT` row in both default and
/// `--quiet` human verdict cards rather than collapsed into a baseline count.
const BASELINE_STAGE0_ASSUMPTIONS: &[&str] = &[
    "faithful pinned compiler capture",
    "Lean kernel and admitted foundation",
    "intact compiler and verification environment",
];

/// Classify a passing Receipt Schema v3 object into its exact
/// [`AssuranceBadge`] tier (`Tainted`, `Warn`, `Scoped`, or `Ok`).
///
/// Fails closed to [`AssuranceBadge::Tainted`] on untrusted, truncated, or
/// malformed receipts: `[OK]` requires `schema_version == 3`, active
/// containment (`linux_bwrap` or `linux_landlock_seccomp`), an empty
/// `taint_reasons` array, absent/null/empty top-level `sorry_declarations`,
/// `audit.replay == true`, `audit.exactType == true`, an empty
/// `audit.sorryDeclarations` array, `audit.axioms` drawn strictly from
/// `{Classical.choice, Quot.sound, propext}`, an empty `spec_warnings` array,
/// a well-typed `assumptions` string array, a well-typed `census` array with
/// zero unverified required items, `status == "crate_verified"`, and
/// `scope.kind == "crate"`.
pub fn classify_success_badge(receipt: &Value) -> AssuranceBadge {
    const ALLOWED_AXIOMS: &[&str] = &["Classical.choice", "Quot.sound", "propext"];

    let Some(obj) = receipt.as_object() else {
        return AssuranceBadge::Tainted;
    };
    let schema_ok = obj.get("schema_version").and_then(Value::as_u64) == Some(3);
    let sandbox_contained = matches!(
        obj.get("elaboration_sandbox").and_then(Value::as_str),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    );
    let status = obj.get("status").and_then(Value::as_str);
    let status_clean = matches!(status, Some("crate_verified" | "selected_unit_verified"));
    let taint_reasons_clean = obj
        .get("taint_reasons")
        .and_then(Value::as_array)
        .is_some_and(|reasons| reasons.is_empty());
    let top_sorry_clean = match obj.get("sorry_declarations") {
        None | Some(Value::Null) => true,
        Some(Value::Array(decls)) => decls.is_empty(),
        Some(_) => false,
    };
    let audit_clean = obj.get("audit").and_then(Value::as_object).is_some_and(|audit| {
        let replay_ok = audit.get("replay").and_then(Value::as_bool) == Some(true);
        let exact_type_ok = audit.get("exactType").and_then(Value::as_bool) == Some(true);
        let sorry_decls_empty = audit
            .get("sorryDeclarations")
            .and_then(Value::as_array)
            .is_some_and(|decls| decls.is_empty());
        let axioms_ok = audit.get("axioms").and_then(Value::as_array).is_some_and(|axioms| {
            axioms.iter().all(|a| a.as_str().is_some_and(|name| ALLOWED_AXIOMS.contains(&name)))
        });
        replay_ok && exact_type_ok && sorry_decls_empty && axioms_ok
    });
    let assumptions_valid = obj
        .get("assumptions")
        .and_then(Value::as_array)
        .is_some_and(|entries| entries.iter().all(Value::is_string));
    let census_valid = obj.get("census").and_then(Value::as_array).is_some_and(|entries| {
        entries.iter().all(|entry| {
            entry.as_object().is_some_and(|item| {
                item.get("has_body").is_some_and(Value::is_boolean)
                    && item.get("selected").is_some_and(Value::is_boolean)
                    && item.get("required").is_some_and(Value::is_boolean)
            })
        })
    });
    let Some(warnings) = obj.get("spec_warnings").and_then(Value::as_array) else {
        return AssuranceBadge::Tainted;
    };

    if !schema_ok
        || !sandbox_contained
        || !status_clean
        || !taint_reasons_clean
        || !top_sorry_clean
        || !audit_clean
        || !assumptions_valid
        || !census_valid
    {
        return AssuranceBadge::Tainted;
    }
    if !warnings.is_empty() {
        return AssuranceBadge::Warn;
    }
    let cov = CensusCoverage::from_receipt(receipt);
    let is_crate_verified = status == Some("crate_verified")
        && obj.get("scope").and_then(|s| s.get("kind")).and_then(Value::as_str) == Some("crate")
        && cov.unverified_required_total == 0;
    if is_crate_verified { AssuranceBadge::Ok } else { AssuranceBadge::Scoped }
}

fn format_containment_label(sandbox: &str, ansi_color: bool) -> String {
    match sandbox {
        "linux_bwrap" => "linux_bwrap (ExecSeal Tier 1)".to_owned(),
        "linux_landlock_seccomp" => {
            "linux_landlock_seccomp (ExecSeal Tier 2: shared host mount/PID metadata visibility)"
                .to_owned()
        }
        "none" => {
            let msg = "NONE (UNSANDBOXED -- hostile Lean elaborator effects uncontained)";
            style_span(msg, "\x1b[1;33m", ansi_color)
        }
        other => SanitizedInline::new(other).to_string(),
    }
}

fn taint_flag_hint(reason: &str) -> &'static str {
    match reason {
        "sorry_in_proof" => "--allow-sorry-in-proof",
        "unpinned_lean" => "--allow-unpinned-lean",
        "unsandboxed_elaboration" => "--allow-unsandboxed-elaboration",
        _ => "--allow-*",
    }
}

/// Options controlling human card rendering on `stdout`.
#[derive(Clone, Copy, Debug)]
pub struct CardRenderOptions<'a> {
    pub ansi_color: bool,
    pub quiet: bool,
    pub verbose: bool,
    pub receipt_out_path: Option<&'a str>,
}

/// Render a passing Receipt Schema v3 JSON object as a deterministic five-tier
/// human verification card (`Tier 5 [OK]`, `Tier 4 [SCOPED]`, `Tier 3 [WARN]`,
/// or `Tier 2 [TAINTED]`).
pub fn render_success_card(receipt: &Value, opts: CardRenderOptions<'_>) -> String {
    use fmt::Write as _;

    let badge = classify_success_badge(receipt);
    let cov = CensusCoverage::from_receipt(receipt);
    let status = SanitizedInline::new(receipt["status"].as_str().unwrap_or("unknown"));
    let raw_assumptions: Vec<&str> = receipt["assumptions"]
        .as_array()
        .map(|arr| arr.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default();
    let mut baseline_assumptions: Vec<SanitizedInline> = Vec::new();
    let mut narrowing_assumptions: Vec<SanitizedInline> = Vec::new();
    for assumption in &raw_assumptions {
        if BASELINE_STAGE0_ASSUMPTIONS.contains(assumption) {
            baseline_assumptions.push(SanitizedInline::new(assumption));
        } else {
            narrowing_assumptions.push(SanitizedInline::new(assumption));
        }
    }
    let assumptions: Vec<SanitizedInline> =
        raw_assumptions.iter().map(|a| SanitizedInline::new(a)).collect();

    let experimental = receipt["experimental"].as_bool().unwrap_or(false);
    let is_profile_v2 = matches!(
        receipt["audit"]["canonicalRoot"].as_str(),
        Some("Trusted.MirSemantics.CrateTheoremV2" | "Trusted.MirSemantics.UnitTheoremV2")
    );
    let has_experimental_assumption =
        raw_assumptions.iter().any(|a| a.starts_with("experimental "));
    let exp_suffix = if badge == AssuranceBadge::Tainted {
        ""
    } else if experimental || is_profile_v2 || has_experimental_assumption {
        "  [STAGE 0 ALPHA -- EXPERIMENTAL]"
    } else if !narrowing_assumptions.is_empty() {
        "  [STAGE 0 ALPHA -- SCOPE ASSUMPTIONS APPLY]"
    } else {
        ""
    };

    let is_crate_scope = receipt["scope"]["kind"].as_str() == Some("crate");
    let warnings = receipt["spec_warnings"].as_array().cloned().unwrap_or_default();
    let taints: Vec<SanitizedInline> = receipt["taint_reasons"]
        .as_array()
        .map(|arr| arr.iter().filter_map(Value::as_str).map(SanitizedInline::new).collect())
        .unwrap_or_default();

    let badge_str = badge.render_tag(opts.ansi_color);
    let headline_rest = match badge {
        AssuranceBadge::Tainted => style_span(
            &format!("VERIFIED WITH TAINT -- DO NOT TRUST FOR ASSURANCE ({status})"),
            "\x1b[1;33m",
            opts.ansi_color,
        ),
        AssuranceBadge::Warn => {
            let scope_short = if is_crate_scope {
                format!(
                    "crate: {}/{} required crate bodies",
                    cov.selected_required_bodies, cov.required_bodies
                )
            } else {
                format!(
                    "selected: {}/{} required crate bodies; {} UNVERIFIED",
                    cov.selected_required_bodies,
                    cov.required_bodies,
                    cov.unverified_required_total
                )
            };
            style_span(
                &format!(
                    "VERIFIED WITH SPEC WARNINGS ({scope_short}; {} anti-vacuity warning(s)){exp_suffix}",
                    warnings.len()
                ),
                "\x1b[1;33m",
                opts.ansi_color,
            )
        }
        AssuranceBadge::Scoped => style_span(
            &format!(
                "VERIFIED (SELECTED UNIT ONLY -- {}/{} required crate bodies; {} required items UNVERIFIED){exp_suffix}",
                cov.selected_required_bodies, cov.required_bodies, cov.unverified_required_total
            ),
            BOLD_SGR,
            opts.ansi_color,
        ),
        AssuranceBadge::Ok => style_span(
            &format!(
                "CRATE VERIFIED ({}/{} required crate bodies){exp_suffix}",
                cov.selected_required_bodies, cov.required_bodies
            ),
            BOLD_SGR,
            opts.ansi_color,
        ),
        AssuranceBadge::Fail => unreachable!("success card never classifies as Fail"),
    };

    let mut out = String::new();
    let _ = writeln!(out, "{badge_str} {headline_rest}");

    // Mandatory caveats (`! TAINT` and `! WARNING`) are NEVER suppressed by
    // `--quiet`.
    for taint in &taints {
        let reason_str = taint.as_str();
        let flag = taint_flag_hint(reason_str);
        match reason_str {
            "sorry_in_proof" => {
                let sorry_decls: Vec<SanitizedInline> = receipt["sorry_declarations"]
                    .as_array()
                    .map(|arr| {
                        arr.iter().filter_map(Value::as_str).map(SanitizedInline::new).collect()
                    })
                    .unwrap_or_default();
                let _ = writeln!(
                    out,
                    "  ! TAINT    : {taint} ({flag}) -- {} unproven `sorry` declaration(s) in Proof{}",
                    sorry_decls.len(),
                    if sorry_decls.is_empty() { "" } else { ":" }
                );
                let cap = if opts.verbose { sorry_decls.len() } else { MAX_INLINE_FAILURE_ITEMS };
                for decl in sorry_decls.iter().take(cap) {
                    let _ = writeln!(out, "               - {decl}");
                }
                if sorry_decls.len() > cap {
                    let _ = writeln!(
                        out,
                        "               ... (+{} more; pass --verbose to list all)",
                        sorry_decls.len() - cap
                    );
                }
            }
            "unsandboxed_elaboration" => {
                let _ = writeln!(out, "  ! TAINT    : {taint} ({flag}) -- active sandbox `none`");
            }
            "unpinned_lean" => {
                let observed =
                    receipt["unpinned_lean"]["observed_version"].as_str().map(SanitizedInline::new);
                match observed {
                    Some(ver) => {
                        let _ = writeln!(
                            out,
                            "  ! TAINT    : {taint} ({flag}) -- unpinned Lean `{ver}`"
                        );
                    }
                    None => {
                        let _ = writeln!(
                            out,
                            "  ! TAINT    : {taint} ({flag}) -- Lean binary/foundation not locked"
                        );
                    }
                }
            }
            _ => {
                let _ = writeln!(out, "  ! TAINT    : {taint} ({flag})");
            }
        }
    }

    for warning in &warnings {
        let code = SanitizedInline::new(warning["code"].as_str().unwrap_or("unknown"));
        let decl = SanitizedInline::new(warning["declaration"].as_str().unwrap_or("<unknown>"));
        let msg = SanitizedInline::new(warning["message"].as_str().unwrap_or(""));
        match warning["body"].as_str().map(SanitizedInline::new) {
            Some(body) => {
                let _ = writeln!(
                    out,
                    "  ! WARNING  : [anti-vacuity: {code}] {decl} (body `{body}`): {msg}"
                );
            }
            None => {
                let _ = writeln!(out, "  ! WARNING  : [anti-vacuity: {code}] {decl}: {msg}");
            }
        }
    }

    for assumption in &narrowing_assumptions {
        let _ = writeln!(out, "  ! CAVEAT   : {assumption}");
    }

    if opts.quiet {
        if !is_crate_scope {
            let _ = writeln!(
                out,
                "  Selected   : {} callable body/bodies verified ({} required item(s) unverified)",
                cov.verified_bodies, cov.unverified_required_total
            );
        }
        if badge == AssuranceBadge::Tainted {
            let _ = writeln!(
                out,
                "  Notice     : Tainted receipt cannot establish soundness; re-run without `--allow-*` flags."
            );
        }
        return out;
    }

    // Subject row
    let crate_name =
        SanitizedInline::new(receipt["configuration"]["crate_name"].as_str().unwrap_or("<crate>"));
    let edition =
        SanitizedInline::new(receipt["configuration"]["edition"].as_str().unwrap_or("2024"));
    let target =
        SanitizedInline::new(receipt["configuration"]["target"].as_str().unwrap_or("<target>"));
    let cfgs: Vec<SanitizedInline> = receipt["configuration"]["cfg"]
        .as_array()
        .map(|arr| arr.iter().filter_map(Value::as_str).map(SanitizedInline::new).collect())
        .unwrap_or_default();
    if cfgs.is_empty() {
        let _ = writeln!(
            out,
            "  Subject    : crate `{crate_name}` (edition {edition}, target {target})"
        );
    } else {
        let joined: Vec<&str> = cfgs.iter().map(SanitizedInline::as_str).collect();
        let _ = writeln!(
            out,
            "  Subject    : crate `{crate_name}` (edition {edition}, target {target}, cfg: [{}])",
            joined.join(", ")
        );
    }

    // Selected-unit coverage row
    if !is_crate_scope {
        let body_word = if cov.verified_bodies == 1 { "body" } else { "bodies" };
        let _ = writeln!(
            out,
            "  Selected   : {} callable {body_word} verified ({} required bodies + {} required owners unverified):",
            cov.verified_bodies, cov.unverified_required_bodies, cov.unverified_required_owners
        );
        let cap = if opts.verbose { cov.selected_paths.len() } else { MAX_INLINE_SELECTED };
        for path in cov.selected_paths.iter().take(cap) {
            let _ = writeln!(out, "               - {path}");
        }
        if cov.selected_paths.len() > cap {
            let _ = writeln!(
                out,
                "               ... (+{} more; pass --verbose to list all)",
                cov.selected_paths.len() - cap
            );
        }
    }

    // Spec Bound & Theorem rows. `Checker::run_target_with_progress` populates
    // `audit.sources` with `TargetRole::Specification` serialized as
    // `"specification"`; fall back to unique modules in `specificationClosure`
    // if `audit.sources` is absent.
    let spec_decl =
        SanitizedInline::new(receipt["audit"]["specification"].as_str().unwrap_or("Spec.specs"));
    let spec_mod_count = receipt["audit"]["sources"]
        .as_array()
        .map(|arr| arr.iter().filter(|s| s["role"].as_str() == Some("specification")).count())
        .or_else(|| {
            receipt["audit"]["specificationClosure"].as_array().map(|arr| {
                arr.iter()
                    .filter_map(|entry| entry["module"].as_str())
                    .collect::<std::collections::BTreeSet<_>>()
                    .len()
            })
        })
        .unwrap_or(1);
    let spec_sha_raw = receipt["specification_manifest_sha256"].as_str().unwrap_or("");
    let spec_sha_display = if opts.verbose || spec_sha_raw.chars().count() <= 16 {
        SanitizedInline::new(spec_sha_raw).to_string()
    } else {
        format!("{}...", SanitizedInline::new(truncate_to_char_width(spec_sha_raw, 16)))
    };
    let _ = writeln!(
        out,
        "  Spec Bound : {spec_decl} ({spec_mod_count} spec module(s))  [sha256:{spec_sha_display}]"
    );

    let theorem_decl =
        SanitizedInline::new(receipt["audit"]["theorem"].as_str().unwrap_or("Proof.verify"));
    let canonical_root = SanitizedInline::new(
        receipt["audit"]["canonicalRoot"].as_str().unwrap_or("Trusted.MirSemantics.CrateTheorem"),
    );
    let _ = writeln!(out, "  Theorem    : {theorem_decl} : Expected.claim ({canonical_root})");

    // Containment row
    let sandbox_raw = receipt["elaboration_sandbox"].as_str().unwrap_or("unknown");
    let _ =
        writeln!(out, "  Containment: {}", format_containment_label(sandbox_raw, opts.ansi_color));

    // Axioms row
    let axioms: Vec<SanitizedInline> = receipt["audit"]["axioms"]
        .as_array()
        .map(|arr| arr.iter().filter_map(Value::as_str).map(SanitizedInline::new).collect())
        .unwrap_or_default();
    let uses_sorry_ax = axioms.iter().any(|a| a.as_str() == "sorryAx");
    let axiom_strs: Vec<&str> = axioms.iter().map(SanitizedInline::as_str).collect();
    let replayed = receipt["audit"]["replayedDeclarations"].as_u64().unwrap_or(0);
    let sorry_count = receipt["audit"]["sorryDeclarations"].as_array().map(Vec::len).unwrap_or(0);
    if uses_sorry_ax {
        let _ = writeln!(
            out,
            "  Axioms     : [{}]  <-- UNSOUND `sorryAx` ADMITTED BY TAINT FLAG",
            axiom_strs.join(", ")
        );
    } else {
        let _ = writeln!(
            out,
            "  Axioms     : [{}] ({replayed} replayed kernel declarations, {sorry_count} sorry)",
            axiom_strs.join(", ")
        );
    }

    // Assumptions & verbose provenance rows
    if opts.verbose {
        let _ = writeln!(out, "  Assumptions: {} Stage-0 TCB assumption(s):", assumptions.len());
        for assumption in &assumptions {
            let _ = writeln!(out, "               - {assumption}");
        }
        let deferred: Vec<SanitizedInline> = receipt["deferred"]
            .as_array()
            .map(|arr| arr.iter().filter_map(Value::as_str).map(SanitizedInline::new).collect())
            .unwrap_or_default();
        if !deferred.is_empty() {
            let def_strs: Vec<&str> = deferred.iter().map(SanitizedInline::as_str).collect();
            let _ = writeln!(out, "  Deferred   : {}", def_strs.join("; "));
        }
        for (label, key) in [
            ("Req Digest ", "request_sha256"),
            ("Cap Digest ", "capture_sha256"),
            ("Mdl Digest ", "model_manifest_sha256"),
        ] {
            if let Some(sha) = receipt[key].as_str() {
                let _ = writeln!(out, "  {label}: {}", SanitizedInline::new(sha));
            }
        }
        if let Some(timing) = receipt["timing_ms"].as_object() {
            let cap_ms = timing.get("capture").and_then(Value::as_u64).unwrap_or(0);
            let proof_ms = timing.get("proof_and_audit").and_then(Value::as_u64).unwrap_or(0);
            let total_ms = timing.get("total").and_then(Value::as_u64).unwrap_or(0);
            let _ = writeln!(
                out,
                "  Timing     : {cap_ms} ms capture, {proof_ms} ms proof+audit, {total_ms} ms total"
            );
        }
    } else if !baseline_assumptions.is_empty() && !narrowing_assumptions.is_empty() {
        let _ = writeln!(
            out,
            "  Assumptions: {} baseline Stage-0 TCB assumption(s) (pass --verbose to list); {} scope-bounding caveat(s) shown above",
            baseline_assumptions.len(),
            narrowing_assumptions.len()
        );
    } else if !baseline_assumptions.is_empty() {
        let _ = writeln!(
            out,
            "  Assumptions: {} baseline Stage-0 TCB assumption(s) (pass --verbose to list)",
            baseline_assumptions.len()
        );
    }

    if let Some(artifacts_path) = receipt["artifacts"].as_str() {
        let _ = writeln!(out, "  Artifacts  : {}", SanitizedInline::new(artifacts_path));
    }
    if let Some(receipt_path) = opts.receipt_out_path {
        let _ = writeln!(out, "  Receipt    : {}", SanitizedInline::new(receipt_path));
    }
    if badge == AssuranceBadge::Tainted {
        let _ = writeln!(
            out,
            "  Notice     : Tainted receipt cannot establish soundness; re-run without `--allow-*` flags."
        );
    }
    out
}

fn strip_staged_lean_prefix(raw_file: &str) -> &str {
    for marker in ["/ro/", "/in/", "/generated/", "/authored/"] {
        if let Some((_, suffix)) = raw_file.rsplit_once(marker)
            && !suffix.is_empty()
        {
            return suffix;
        }
    }
    raw_file
}

struct ParsedLeanDiag {
    header: SanitizedInline,
    body: SanitizedBlock,
}

struct ExtractedLeanDiags {
    diags: Vec<ParsedLeanDiag>,
    has_json_error: bool,
    non_json_lines: Vec<String>,
}

fn try_extract_lean_json_diagnostics(detail: &str) -> ExtractedLeanDiags {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    let mut others = Vec::new();
    let mut non_json_lines = Vec::new();
    for line in detail.lines() {
        let trimmed = line.trim();
        let parsed = if trimmed.starts_with('{') {
            serde_json::from_str::<Value>(trimmed).ok().and_then(|val| {
                let sev = val["severity"].as_str()?;
                let data = val["data"].as_str()?;
                let file = strip_staged_lean_prefix(val["fileName"].as_str().unwrap_or("<lean>"));
                let pos_line = val["pos"]["line"].as_u64();
                let pos_col = val["pos"]["column"].as_u64();
                let loc = match (pos_line, pos_col) {
                    (Some(l), Some(c)) => format!("{file}:{l}:{c}: {sev}:"),
                    (Some(l), None) => format!("{file}:{l}: {sev}:"),
                    _ => format!("{file}: {sev}:"),
                };
                Some((
                    sev.to_owned(),
                    ParsedLeanDiag {
                        header: SanitizedInline::new(&loc),
                        body: SanitizedBlock::new(data),
                    },
                ))
            })
        } else {
            None
        };
        if let Some((sev, diag)) = parsed {
            match sev.as_str() {
                "error" => errors.push(diag),
                "warning" => warnings.push(diag),
                _ => others.push(diag),
            }
        } else if !trimmed.is_empty() {
            non_json_lines.push(line.to_owned());
        }
    }
    let has_json_error = !errors.is_empty();
    errors.extend(warnings);
    errors.extend(others);
    ExtractedLeanDiags { diags: errors, has_json_error, non_json_lines }
}

/// Inputs describing a verification or operational failure for human card
/// rendering (`Tier 1: [FAIL]`).
pub struct FailureCardInput<'a> {
    pub taint_reasons: &'a [&'a str],
    pub elaboration_sandbox: Option<&'a str>,
    pub status: &'a str,
    pub phase: &'a str,
    pub detail: &'a str,
    pub hint: Option<&'a str>,
    pub artifacts: Option<&'a str>,
    pub exit_code: u8,
}

/// Render a failed verification run as a deterministic `Tier 1: [FAIL]` card.
pub fn render_failure_card(input: &FailureCardInput<'_>, opts: CardRenderOptions<'_>) -> String {
    use fmt::Write as _;

    let badge = AssuranceBadge::Fail.render_tag(opts.ansi_color);
    let status = SanitizedInline::new(input.status);
    let phase = SanitizedInline::new(input.phase);
    let taint_suffix = if input.taint_reasons.is_empty() {
        String::new()
    } else {
        let clean: Vec<String> =
            input.taint_reasons.iter().map(|t| SanitizedInline::new(t).to_string()).collect();
        format!("  [TAINTED RUN: {}]", clean.join(", "))
    };
    let headline = style_span(
        &format!(
            "VERIFICATION FAILED ({status} in phase `{phase}`, exit {}){taint_suffix}",
            input.exit_code
        ),
        "\x1b[1;31m",
        opts.ansi_color,
    );

    let mut out = String::new();
    let _ = writeln!(out, "{badge} {headline}");

    // Mandatory taint rows even on failure and even under `--quiet`.
    for raw_taint in input.taint_reasons {
        let taint = SanitizedInline::new(raw_taint);
        let flag = taint_flag_hint(raw_taint);
        let _ = writeln!(out, "  ! TAINT    : {taint} ({flag})");
    }

    if opts.quiet {
        return out;
    }

    let max_items = if opts.verbose { usize::MAX } else { MAX_INLINE_FAILURE_ITEMS };
    let max_lines = if opts.verbose { None } else { Some(MAX_DETAIL_LINES) };

    let mut rendered_structured = false;
    if input.phase == "capture"
        && let Ok(env_json) = serde_json::from_str::<Value>(input.detail)
        && env_json.is_object()
    {
        if let Some(unsupported) = env_json["unsupported"].as_array()
            && !unsupported.is_empty()
        {
            let _ = writeln!(
                out,
                "  Unsupported: {} required item(s) outside supported MIR profile:",
                unsupported.len()
            );
            for item in unsupported.iter().take(max_items) {
                let path = SanitizedInline::new(item["path"].as_str().unwrap_or("<item>"));
                let reason = SanitizedInline::new(item["reason"].as_str().unwrap_or("unsupported"));
                let _ = writeln!(out, "               - `{path}`: {reason}");
            }
            if unsupported.len() > max_items {
                let _ = writeln!(
                    out,
                    "               ... (+{} more; pass --verbose to show all)",
                    unsupported.len() - max_items
                );
            }
            rendered_structured = true;
        }
        if let Some(diags) = env_json["diagnostics"].as_array()
            && !diags.is_empty()
        {
            let _ = writeln!(out, "  Diagnostic : {} capture message(s):", diags.len());
            for diag in diags.iter().take(max_items) {
                if let Some(s) = diag.as_str() {
                    let _ = writeln!(out, "               - {}", SanitizedInline::new(s));
                }
            }
            if diags.len() > max_items {
                let _ = writeln!(
                    out,
                    "               ... (+{} more; pass --verbose to show all)",
                    diags.len() - max_items
                );
            }
            rendered_structured = true;
        }
        if !rendered_structured && input.status == "compiler_failed" {
            let _ = writeln!(
                out,
                "  Detail     : Rust compiler rejected crate during capture (see compiler diagnostics on stderr)"
            );
            rendered_structured = true;
        }
    }

    if !rendered_structured && input.phase == "audit" && input.status == "proof_failed" {
        let extracted = try_extract_lean_json_diagnostics(input.detail);
        if !extracted.diags.is_empty() {
            let render_non_json = |out: &mut String| {
                if !extracted.non_json_lines.is_empty() {
                    let joined = extracted.non_json_lines.join("\n");
                    let cleaned = if !opts.verbose {
                        joined.strip_prefix("audit: ").unwrap_or(&joined)
                    } else {
                        &joined
                    };
                    let block = SanitizedBlock::new(cleaned);
                    if block.lines().len() == 1 {
                        let _ = writeln!(out, "  Detail     : {}", block.lines()[0]);
                    } else {
                        let _ = writeln!(out, "  Detail     :");
                        block.write_guttered(out, max_lines);
                    }
                }
            };
            if !extracted.has_json_error {
                render_non_json(&mut out);
            }
            for diag in extracted.diags.iter().take(max_items) {
                let _ = writeln!(out, "  Diagnostic : {}", diag.header);
                diag.body.write_guttered(&mut out, max_lines);
            }
            if extracted.diags.len() > max_items {
                let _ = writeln!(
                    out,
                    "  ... (+{} more diagnostic(s); pass --verbose to show all)",
                    extracted.diags.len() - max_items
                );
            }
            if extracted.has_json_error {
                render_non_json(&mut out);
            }
            rendered_structured = true;
        }
    }

    if !rendered_structured && !input.detail.is_empty() {
        let cleaned_detail = if !opts.verbose && input.phase == "audit" {
            input.detail.strip_prefix("audit: ").unwrap_or(input.detail)
        } else {
            input.detail
        };
        let block = SanitizedBlock::new(cleaned_detail);
        if block.lines().len() == 1 {
            let _ = writeln!(out, "  Detail     : {}", block.lines()[0]);
        } else {
            let _ = writeln!(out, "  Detail     :");
            block.write_guttered(&mut out, max_lines);
        }
    }

    if let Some(sandbox) = input.elaboration_sandbox {
        let _ =
            writeln!(out, "  Containment: {}", format_containment_label(sandbox, opts.ansi_color));
    }
    if let Some(hint) = input.hint {
        let _ = writeln!(out, "  Hint       : {}", SanitizedInline::new(hint));
    }
    if let Some(artifacts_dir) = input.artifacts {
        let _ = writeln!(out, "  Artifacts  : {}", SanitizedInline::new(artifacts_dir));
    }
    if let Some(receipt_path) = opts.receipt_out_path {
        let _ = writeln!(out, "  Receipt    : {}", SanitizedInline::new(receipt_path));
    }
    out
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn resolve_stream_style_enforces_exact_precedence_and_strict_isatty() {
        let base_env = EnvSnapshot::default();

        // 1. Under `--color auto`, enable ANSI only on a TTY (`false` on
        //    pipes even when `CI=true`).
        assert!(resolve_stream_style(ColorChoice::Auto, true, Some(120), &base_env).ansi_color);
        assert!(!resolve_stream_style(ColorChoice::Auto, false, None, &base_env).ansi_color);
        let ci_env = EnvSnapshot { ci: true, ..base_env.clone() };
        assert!(!resolve_stream_style(ColorChoice::Auto, false, None, &ci_env).ansi_color);

        // 2. Independent stream evaluation: piped stdout (`false`) vs TTY
        //    stderr (`true`).
        let stdout_s = resolve_stream_style(ColorChoice::Auto, false, None, &base_env);
        let stderr_s = resolve_stream_style(ColorChoice::Auto, true, Some(100), &base_env);
        assert!(!stdout_s.ansi_color);
        assert_eq!(stdout_s.width, 80);
        assert!(stderr_s.ansi_color);
        assert_eq!(stderr_s.width, 100);

        // 3. Non-empty `NO_COLOR` overrides `CLICOLOR_FORCE` and `FORCE_COLOR`,
        //    whereas empty `NO_COLOR=""` is treated as unset.
        let no_color_set = EnvSnapshot {
            no_color: Some("1".to_owned()),
            clicolor_force: Some("1".to_owned()),
            force_color: Some("1".to_owned()),
            ..base_env.clone()
        };
        assert!(!resolve_stream_style(ColorChoice::Auto, true, None, &no_color_set).ansi_color);

        let no_color_empty = EnvSnapshot {
            no_color: Some(String::new()),
            clicolor_force: Some("1".to_owned()),
            ..base_env.clone()
        };
        assert!(resolve_stream_style(ColorChoice::Auto, false, None, &no_color_empty).ansi_color);

        // 4. `TERM=dumb` disables auto color even on a TTY and overrides
        //    `CLICOLOR_FORCE`.
        let dumb_env = EnvSnapshot {
            term: Some("dumb".to_owned()),
            clicolor_force: Some("1".to_owned()),
            ..base_env.clone()
        };
        assert!(!resolve_stream_style(ColorChoice::Auto, true, None, &dumb_env).ansi_color);

        // 5. `CARGO_TERM_COLOR` overrides `NO_COLOR`, and explicit `--color`
        //    overrides `CARGO_TERM_COLOR`.
        let cargo_always = EnvSnapshot {
            cargo_term_color: Some("ALWAYS".to_owned()),
            no_color: Some("1".to_owned()),
            ..base_env.clone()
        };
        assert!(resolve_stream_style(ColorChoice::Auto, false, None, &cargo_always).ansi_color);
        assert!(!resolve_stream_style(ColorChoice::Never, true, None, &cargo_always).ansi_color);

        let cargo_never = EnvSnapshot { cargo_term_color: Some("never".to_owned()), ..base_env };
        assert!(!resolve_stream_style(ColorChoice::Auto, true, None, &cargo_never).ansi_color);
        assert!(resolve_stream_style(ColorChoice::Always, false, None, &cargo_never).ansi_color);
    }

    #[test]
    fn sanitized_inline_and_block_neutralize_csi_c1_osc_cr_newline_and_bidi_spoofing() {
        let payload = concat!(
            "bad\x1b[2J\x1b[1;32m[OK]\x07",
            "\u{009b}32m",
            "\x1b]8;;https://example.com\x07link\x1b]8;;\x07",
            "\u{202e}forge\u{2066}iso\u{200b}\u{feff}\u{e0041}\u{070f}\u{180e}\u{206a}",
            "\r[OK] CRATE VERIFIED\n[OK] COL0"
        );
        let inline = SanitizedInline::new(payload);
        let s = inline.as_str();
        assert!(!s.contains('\x1b'), "{s}");
        assert!(!s.contains('\r'), "{s}");
        assert!(!s.contains('\n'), "{s}");
        assert!(!s.chars().any(is_dangerous_unicode), "{s}");
        assert!(s.contains("\\u{001B}[2J\\u{001B}[1;32m[OK]\\u{0007}"), "{s}");
        assert!(s.contains("\\u{009B}32m"), "{s}");
        assert!(
            s.contains(
                "\\u{202E}forge\\u{2066}iso\\u{200B}\\u{FEFF}\\u{E0041}\\u{070F}\\u{180E}\\u{206A}"
            ),
            "{s}"
        );
        assert!(s.contains("\\r[OK] CRATE VERIFIED\\n[OK] COL0"), "{s}");

        let block = SanitizedBlock::new("line 1\r[OK] SPOOF\r\n[OK] CRATE VERIFIED\n\tindented\n");
        let mut guttered = String::new();
        block.write_guttered(&mut guttered, None);
        for line in guttered.lines() {
            assert!(line.starts_with("  | "), "every line must carry col-0 gutter: {line:?}");
            assert!(!line.contains('\x1b') && !line.contains('\r'), "{line:?}");
        }
        assert!(guttered.contains("  | line 1\\r[OK] SPOOF\n"), "{guttered}");
        assert!(guttered.contains("  | [OK] CRATE VERIFIED\n"), "{guttered}");
        assert!(guttered.contains("  |     indented\n"), "{guttered}");

        // GFM inline code span escaping delegates to `core::sanitize`,
        // preventing odd-backslash pipe table breakouts and CommonMark §6.1
        // empty/all-space edge cases.
        let tricky = SanitizedInline::new("a``b|c");
        assert_eq!(tricky.to_gfm_code_span(true), "```a``b\\|c```");
        assert_eq!(
            SanitizedInline::new(r"a\|b").to_gfm_code_span(true),
            "<code>a&#92;&#124;b</code>"
        );
        assert_eq!(
            SanitizedInline::new(r"a\| [OK] |b").to_gfm_code_span(true),
            "<code>a&#92;&#124; &#91;OK&#93; &#124;b</code>"
        );
        assert_eq!(SanitizedInline::new("").to_gfm_code_span(true), "<code></code>");
        assert_eq!(SanitizedInline::new("").to_gfm_code_span(false), "<code></code>");
        assert_eq!(SanitizedInline::new("   ").to_gfm_code_span(true), "`   `");
        assert_eq!(SanitizedInline::new("   ").to_gfm_code_span(false), "`   `");
        assert_eq!(SanitizedInline::new(" foo ").to_gfm_code_span(true), "`  foo  `");
        assert_eq!(SanitizedInline::new(" foo ").to_gfm_code_span(false), "`  foo  `");
    }

    struct BrokenPipeWriter;
    impl Write for BrokenPipeWriter {
        fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "pipe closed"))
        }
        fn flush(&mut self) -> io::Result<()> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "pipe closed"))
        }
    }

    #[test]
    fn broken_pipe_never_panics_and_preserves_nonzero_exit_codes() {
        let style = StreamStyle { is_tty: false, ansi_color: false, width: 80 };
        for code in [0u8, 1, 2] {
            let mut session = OutputSession::with_writers(
                BrokenPipeWriter,
                Vec::<u8>::new(),
                style,
                style,
                false,
                false,
                ProgressMode::Silent,
                true,
            );
            let actual = finish_with_writers(&mut session, b"primary output\n", code);
            assert_eq!(actual, ExitCode::from(code));
            assert!(session.stderr.is_empty());
        }
    }

    #[test]
    fn transient_progress_erases_cleanly_before_diagnostics_and_primary_output() {
        let tty_style = StreamStyle { is_tty: true, ansi_color: false, width: 80 };
        let pipe_style = StreamStyle { is_tty: false, ansi_color: false, width: 80 };
        let mut session = OutputSession::with_writers(
            Vec::<u8>::new(),
            Vec::<u8>::new(),
            pipe_style,
            tty_style,
            false,
            false,
            ProgressMode::TransientTty,
            true,
        );
        session.report_phase(VerifyPhase::Stage);
        session.write_taint_banner("WARNING: TAINTED");
        session.report_phase(VerifyPhase::Audit);
        let code = finish_with_writers(&mut session, b"CARD\n", 0);
        assert_eq!(code, ExitCode::SUCCESS);
        let stderr_str = String::from_utf8(session.stderr).unwrap();
        // Never emits cursor-hide `\x1b[?25l`; clears before the taint banner
        // and again before `stdout` writes.
        assert!(!stderr_str.contains("\x1b[?25l"), "{stderr_str:?}");
        assert!(
            stderr_str.contains("\r\x1b[2KWARNING: TAINTED\n"),
            "transient line must clear before diagnostic: {stderr_str:?}"
        );
        assert!(
            stderr_str.ends_with("\r\x1b[2K"),
            "transient line must clear before final stdout: {stderr_str:?}"
        );
    }

    fn sample_success_receipt(scope: Value, taints: Value, warnings: Value) -> Value {
        let is_crate = scope["kind"].as_str() == Some("crate");
        let is_tainted = taints.as_array().is_some_and(|a| !a.is_empty());
        let status = match (is_crate, is_tainted) {
            (true, false) => "crate_verified",
            (false, false) => "selected_unit_verified",
            (true, true) => "tainted_crate_verified",
            (false, true) => "tainted_selected_unit_verified",
        };
        json!({
            "schema_version": 3,
            "status": status,
            "taint_reasons": taints,
            "elaboration_sandbox": if taints.as_array().is_some_and(|a| a.iter().any(|x| x == "unsandboxed_elaboration")) {
                "none"
            } else {
                "linux_bwrap"
            },
            "experimental": true,
            "request_sha256": "1111111111111111111111111111111111111111111111111111111111111111",
            "capture_sha256": "2222222222222222222222222222222222222222222222222222222222222222",
            "model_manifest_sha256": "3333333333333333333333333333333333333333333333333333333333333333",
            "specification_manifest_sha256": "8f3c2a19b4017e2d000000000000000000000000000000000000000000000000",
            "scope": scope,
            "selected": [{"def_id": 1, "path": "zero", "body_index": 0}],
            "census": [
                {"def_id": 1, "path": "zero", "kind": "Fn", "has_body": true, "selected": true, "required": true},
                {"def_id": 2, "path": "other", "kind": "Fn", "has_body": true, "selected": is_crate, "required": !is_crate}
            ],
            "configuration": {
                "crate_name": "scalar",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": []
            },
            "audit": {
                "theorem": "Proof.verify",
                "canonicalRoot": if is_crate { "Trusted.MirSemantics.CrateTheorem" } else { "Trusted.MirSemantics.UnitTheorem" },
                "specification": "Spec.specs",
                "replay": true,
                "exactType": true,
                "axioms": if is_tainted { json!(["propext", "sorryAx"]) } else { json!(["propext"]) },
                "sorryDeclarations": if is_tainted { json!(["Proof.hole"]) } else { json!([]) },
                "replayedDeclarations": 142,
                "sources": [{
                    "module": "Spec",
                    "role": "specification",
                    "sourceSha256": "4444444444444444444444444444444444444444444444444444444444444444",
                    "artifacts": []
                }]
            },
            "sorry_declarations": if is_tainted { json!(["Proof.hole"]) } else { Value::Null },
            "spec_warnings": warnings,
            "assumptions": [
                "faithful pinned compiler capture",
                "experimental pointer-free MIR semantics",
                "Lean kernel and admitted foundation",
                "intact compiler and verification environment"
            ],
            "deferred": ["complete review-surface reporting"]
        })
    }

    #[test]
    fn five_tier_verdict_hierarchy_restricts_ok_and_green_strictly_to_clean_whole_crate() {
        let color_opts = CardRenderOptions {
            ansi_color: true,
            quiet: false,
            verbose: false,
            receipt_out_path: Some("out/receipt.json"),
        };

        // Tier 5: [OK] (Clean whole-crate)
        let ok_rec = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        let ok_card = render_success_card(&ok_rec, color_opts);
        assert!(ok_card.contains("[OK]") && ok_card.contains("\x1b[1;32m"), "{ok_card}");
        assert!(ok_card.contains("Receipt    : out/receipt.json"), "{ok_card}");

        // Tier 4: [SCOPED] (Selected unit -> NEVER `[OK]` or SGR 32 green)
        let scoped_rec = sample_success_receipt(
            json!({"kind": "selected_unit", "roots": ["zero"]}),
            json!([]),
            json!([]),
        );
        let scoped_card = render_success_card(&scoped_rec, color_opts);
        assert!(scoped_card.contains("[SCOPED]"), "{scoped_card}");
        assert!(!scoped_card.contains("[OK]"), "{scoped_card}");
        assert!(!scoped_card.contains("\x1b[1;32m"), "{scoped_card}");
        assert!(
            scoped_card.contains("1/2 required crate bodies; 1 required items UNVERIFIED"),
            "{scoped_card}"
        );

        // Tier 3: [WARN] (Spec warnings -> NEVER `[OK]` and NEVER SGR 32 green)
        let warn_rec = sample_success_receipt(
            json!({"kind": "crate"}),
            json!([]),
            json!([{
                "code": "unsatisfiable_safety",
                "declaration": "Spec.specs",
                "body": "zero",
                "message": "safety is False"
            }]),
        );
        let warn_card = render_success_card(&warn_rec, color_opts);
        assert!(warn_card.contains("[WARN]"), "{warn_card}");
        assert!(
            warn_card.contains("! WARNING  : [anti-vacuity: unsatisfiable_safety]"),
            "{warn_card}"
        );
        assert!(!warn_card.contains("[OK]") && !warn_card.contains("\x1b[1;32m"), "{warn_card}");

        // Tier 2: [TAINTED] (`--quiet` still preserves taint headline and rows)
        let taint_rec = sample_success_receipt(
            json!({"kind": "crate"}),
            json!(["sorry_in_proof", "unsandboxed_elaboration"]),
            json!([]),
        );
        for quiet in [false, true] {
            let taint_card =
                render_success_card(&taint_rec, CardRenderOptions { quiet, ..color_opts });
            assert!(taint_card.contains("[TAINTED]"), "{taint_card}");
            assert!(taint_card.contains("DO NOT TRUST FOR ASSURANCE"), "{taint_card}");
            assert!(taint_card.contains("! TAINT    : sorry_in_proof"), "{taint_card}");
            assert!(taint_card.contains("! TAINT    : unsandboxed_elaboration"), "{taint_card}");
            assert!(
                !taint_card.contains("[OK]") && !taint_card.contains("\x1b[1;32m"),
                "{taint_card}"
            );
        }

        // Tier 1: [FAIL] (Parses structured capture envelope, Lean JSON, hints)
        let fail_detail = r#"{"status":"unsupported","unsupported":[{"def_id":1,"path":"take_ref","reason":"unsupported type: &'{erased} u64"}]}"#;
        let fail_hint = crate::diagnostics::hint_for_failure("unsupported", "capture", fail_detail);
        let fail_card = render_failure_card(
            &FailureCardInput {
                taint_reasons: &["unpinned_lean"],
                elaboration_sandbox: None,
                status: "unsupported",
                phase: "capture",
                detail: fail_detail,
                hint: fail_hint.as_deref(),
                artifacts: Some("/tmp/ev"),
                exit_code: 1,
            },
            color_opts,
        );
        assert!(fail_card.contains("[FAIL]"), "{fail_card}");
        assert!(fail_card.contains("[TAINTED RUN: unpinned_lean]"), "{fail_card}");
        assert!(
            fail_card.contains("- `take_ref`: unsupported type: &'{erased} u64"),
            "{fail_card}"
        );
        assert!(
            fail_card.contains("Hint       : Unsupported MIR in `take_ref`")
                && fail_card.contains("Profile v2 admits scalars"),
            "{fail_card}"
        );
        assert!(!fail_card.contains("[OK]") && !fail_card.contains("\x1b[1;32m"), "{fail_card}");
    }

    #[test]
    fn dangerous_unicode_covers_all_unicode_cf_format_ranges() {
        for ch in [
            '\u{0600}',
            '\u{0605}',
            '\u{06DD}',
            '\u{0890}',
            '\u{0891}',
            '\u{08E2}',
            '\u{115F}',
            '\u{1160}',
            '\u{3164}',
            '\u{FFA0}',
            '\u{110BD}',
            '\u{110CD}',
            '\u{13430}',
            '\u{1343F}',
            '\u{1BCA0}',
            '\u{1BCA3}',
            '\u{1D173}',
            '\u{1D17A}',
        ] {
            assert!(is_dangerous_unicode(ch), "expected Cf codepoint U+{:04X} escaped", ch as u32);
            let s = SanitizedInline::new(&format!("a{ch}b"));
            assert_eq!(s.as_str(), format!("a\\u{{{:04X}}}b", ch as u32));
        }
    }

    #[test]
    fn default_and_quiet_cards_disclose_profile_v2_and_non_baseline_assumptions() {
        let narrowing = "experimental Profile v2 MIR semantics: caller memory, \
            no aliasing model (Stacked or Tree Borrows); results say nothing \
            about calls that pass references to uninitialized, invalid, or \
            dangling memory";
        let mut v2_rec = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        v2_rec["experimental"] = json!(false);
        v2_rec["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheoremV2");
        v2_rec["assumptions"] = json!([
            "faithful pinned compiler capture",
            narrowing,
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment"
        ]);
        for quiet in [false, true] {
            let card = render_success_card(
                &v2_rec,
                CardRenderOptions {
                    ansi_color: false,
                    quiet,
                    verbose: false,
                    receipt_out_path: None,
                },
            );
            assert!(
                card.contains("[STAGE 0 ALPHA -- EXPERIMENTAL]"),
                "Profile v2 headline must flag experimental semantics (quiet={quiet}):\n{card}"
            );
            assert!(
                card.contains(&format!("! CAVEAT   : {narrowing}")),
                "Profile v2 narrowing must be visible without -v (quiet={quiet}):\n{card}"
            );
            assert!(!card.contains("standard Stage-0 TCB assumption(s)"), "{card}");
            if !quiet {
                assert!(
                    card.contains(
                        "Assumptions: 3 baseline Stage-0 TCB assumption(s) \
                         (pass --verbose to list); 1 scope-bounding caveat(s) shown above"
                    ),
                    "{card}"
                );
            }
        }

        // Clean baseline-only pointer-free receipt emits zero `! CAVEAT` rows.
        let mut baseline_rec =
            sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        baseline_rec["experimental"] = json!(false);
        baseline_rec["assumptions"] = json!([
            "faithful pinned compiler capture",
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment"
        ]);
        let baseline_card = render_success_card(
            &baseline_rec,
            CardRenderOptions {
                ansi_color: false,
                quiet: false,
                verbose: false,
                receipt_out_path: None,
            },
        );
        assert!(!baseline_card.contains("! CAVEAT"), "{baseline_card}");
        assert!(!baseline_card.contains("[STAGE 0 ALPHA"), "{baseline_card}");
        assert!(
            baseline_card.contains(
                "Assumptions: 3 baseline Stage-0 TCB assumption(s) (pass --verbose to list)"
            ),
            "{baseline_card}"
        );
    }

    #[test]
    fn lean_json_diagnostics_prioritize_errors_over_warnings_and_multi_spec_count() {
        let mut lines = Vec::new();
        for i in 1..=6 {
            lines.push(format!(
                r#"{{"severity":"warning","fileName":"/tmp/ro/Proof.lean","pos":{{"line":{i},"column":1}},"data":"unused variable w{i}"}}"#
            ));
        }
        lines.push(
            r#"{"severity":"error","fileName":"/tmp/ro/Proof.lean","pos":{"line":42,"column":4},"data":"type mismatch at goal"}"#
                .to_owned(),
        );
        let detail = lines.join("\n");
        let card = render_failure_card(
            &FailureCardInput {
                taint_reasons: &[],
                elaboration_sandbox: Some("linux_bwrap"),
                status: "proof_failed",
                phase: "audit",
                detail: &detail,
                hint: None,
                artifacts: None,
                exit_code: 1,
            },
            CardRenderOptions {
                ansi_color: false,
                quiet: false,
                verbose: false,
                receipt_out_path: None,
            },
        );
        assert!(card.contains("Proof.lean:42:4: error:"), "{card}");
        assert!(card.contains("type mismatch at goal"), "{card}");
        assert!(card.contains("(+2 more diagnostic(s)"), "{card}");

        let mut multi_spec = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        multi_spec["audit"]["sources"] = json!([
            {"module": "Spec", "role": "specification", "sourceSha256": "4".repeat(64), "artifacts": []},
            {"module": "SpecHelper", "role": "specification", "sourceSha256": "5".repeat(64), "artifacts": []},
            {"module": "Proof", "role": "proof", "sourceSha256": "6".repeat(64), "artifacts": []}
        ]);
        let multi_card = render_success_card(
            &multi_spec,
            CardRenderOptions {
                ansi_color: false,
                quiet: false,
                verbose: false,
                receipt_out_path: None,
            },
        );
        assert!(multi_card.contains("(2 spec module(s))"), "{multi_card}");
    }

    #[test]
    fn non_ascii_spec_sha_mixed_lean_detail_and_malformed_receipt_badge_are_safe() {
        let plain_opts = CardRenderOptions {
            ansi_color: false,
            quiet: false,
            verbose: false,
            receipt_out_path: None,
        };

        // Multi-byte UTF-8 digest does not panic when truncated to 16 chars.
        let mut utf8_rec = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        utf8_rec["specification_manifest_sha256"] = json!("aéééééééééééééééééé");
        let utf8_card = render_success_card(&utf8_rec, plain_opts);
        assert!(utf8_card.contains("[sha256:aééééééééééééééé...]"), "{utf8_card}");

        // Mixed Lean JSON warning + plain error line preserves non-JSON error
        // text in both default and `--verbose` modes.
        let hybrid_detail = concat!(
            r#"{"severity":"warning","fileName":"/tmp/ro/Proof.lean","pos":{"line":1,"column":1},"data":"unused var"}"#,
            "\n",
            "kernel rejected theorem type mismatch"
        );
        for verbose in [false, true] {
            let hybrid_card = render_failure_card(
                &FailureCardInput {
                    taint_reasons: &[],
                    elaboration_sandbox: Some("linux_bwrap"),
                    status: "proof_failed",
                    phase: "audit",
                    detail: hybrid_detail,
                    hint: None,
                    artifacts: None,
                    exit_code: 1,
                },
                CardRenderOptions { verbose, ..plain_opts },
            );
            assert!(
                hybrid_card.contains("kernel rejected theorem type mismatch"),
                "verbose={verbose}:\n{hybrid_card}"
            );
            assert!(hybrid_card.contains("Proof.lean:1:1: warning:"), "{hybrid_card}");
        }

        // External or malformed receipts fail closed instead of returning
        // `[OK]`.
        let mut no_sandbox = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        no_sandbox["elaboration_sandbox"] = json!("none");
        assert_eq!(classify_success_badge(&no_sandbox), AssuranceBadge::Tainted);

        let mut sorry_ax = sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        sorry_ax["audit"]["axioms"] = json!(["propext", "sorryAx"]);
        assert_eq!(classify_success_badge(&sorry_ax), AssuranceBadge::Tainted);

        // Truncated or structurally malformed receipts never fail open to
        // `[OK]`.
        let truncated = json!({
            "status": "crate_verified",
            "scope": {"kind": "crate"},
            "elaboration_sandbox": "linux_bwrap"
        });
        assert_eq!(classify_success_badge(&truncated), AssuranceBadge::Tainted);

        for mutate in [
            Box::new(|r: &mut Value| {
                r.as_object_mut().unwrap().remove("taint_reasons");
            }) as Box<dyn Fn(&mut Value)>,
            Box::new(|r: &mut Value| {
                r["taint_reasons"] = json!("sorry_in_proof");
            }),
            Box::new(|r: &mut Value| {
                r.as_object_mut().unwrap().remove("audit");
            }),
            Box::new(|r: &mut Value| {
                r["audit"]["replay"] = json!(false);
            }),
            Box::new(|r: &mut Value| {
                r["audit"]["exactType"] = json!(false);
            }),
            Box::new(|r: &mut Value| {
                r["audit"]["axioms"] = json!(["propext", "CustomUnapprovedAxiom"]);
            }),
            Box::new(|r: &mut Value| {
                r["audit"].as_object_mut().unwrap().remove("sorryDeclarations");
                r["sorry_declarations"] = json!(["Proof.hole"]);
            }),
            Box::new(|r: &mut Value| {
                r["sorry_declarations"] = json!(["Proof.hole"]);
            }),
            Box::new(|r: &mut Value| {
                r.as_object_mut().unwrap().remove("spec_warnings");
            }),
            Box::new(|r: &mut Value| {
                r.as_object_mut().unwrap().remove("assumptions");
            }),
            Box::new(|r: &mut Value| {
                r["assumptions"] = json!([42]);
            }),
            Box::new(|r: &mut Value| {
                r.as_object_mut().unwrap().remove("census");
            }),
            Box::new(|r: &mut Value| {
                r["census"] = json!([{"def_id": 1}]);
            }),
        ] {
            let mut malformed =
                sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
            mutate(&mut malformed);
            assert_eq!(
                classify_success_badge(&malformed),
                AssuranceBadge::Tainted,
                "malformed receipt must fail closed: {malformed}"
            );
        }

        let mut wrong_status =
            sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        wrong_status["status"] = json!("selected_unit_verified");
        assert_eq!(classify_success_badge(&wrong_status), AssuranceBadge::Scoped);

        // Crate-scoped receipt with an unselected required census item never
        // claims `[OK]` or `2/2`.
        let mut partial_crate =
            sample_success_receipt(json!({"kind": "crate"}), json!([]), json!([]));
        partial_crate["census"] = json!([
            {"def_id": 1, "path": "zero", "kind": "Fn", "has_body": true, "selected": true, "required": true},
            {"def_id": 2, "path": "other", "kind": "Fn", "has_body": true, "selected": false, "required": true}
        ]);
        assert_eq!(classify_success_badge(&partial_crate), AssuranceBadge::Scoped);
        let partial_card = render_success_card(&partial_crate, plain_opts);
        assert!(partial_card.contains("1/2 required crate bodies"), "{partial_card}");
        assert!(!partial_card.contains("[OK]"), "{partial_card}");
    }
}
