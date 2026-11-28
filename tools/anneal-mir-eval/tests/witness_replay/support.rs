// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Miri replay gate, toolchain detection, and witness rendering helpers
//! shared by the `witness_replay` tests.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use anneal_mir_eval::{
    AllocByte, CallerMemory, Counterexample, FaultDetail, IntTy, IntWidth, Outcome, StepTrace, Ty,
    Val, WitnessClass,
};

pub(super) const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
pub(super) const U32_TY: Ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
pub(super) const USIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });

static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(0);

pub(super) struct TempDir(PathBuf);

impl TempDir {
    pub(super) fn new(prefix: &str) -> Self {
        loop {
            let id = NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed);
            let dir = env::temp_dir().join(format!("{prefix}-{}-{id}", std::process::id()));
            match fs::create_dir(&dir) {
                Ok(()) => return Self(dir),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create temp dir {dir:?} for witness replay: {e}"),
            }
        }
    }

    pub(super) fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

/// Outcome of gating a single counterexample witness through Miri replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ReplayVerdict {
    /// Miri exited non-zero and emitted a genuine Miri UB diagnostic.
    ConfirmedMiriUb { diagnostic: String },
    /// Witness belongs to a documented conservative or unclassified
    /// `ModelOnlyUnreplayed` class; never silently promoted to confirmed UB.
    ModelOnlyUnreplayed { note: String },
    /// Miri replay failed (exit 0, compile error, ordinary panic, or
    /// unrecognized error).
    ReplayFailed { reason: String },
}

/// Strictly classify raw Miri process exit status and stderr.
///
/// Anti-bypass invariants:
/// - Exit code `0` is NEVER accepted as UB.
/// - `rustc` compilation errors (`error[E...]` / `could not compile`) are NEVER
///   accepted as UB.
/// - Ordinary Rust panics (`panicked at`) without an explicit Miri UB
///   diagnostic are NEVER accepted as UB.
/// - Only explicit Miri language UB (`error: Undefined Behavior:`) or Miri's
///   library UB precondition diagnostic (`unsafe precondition(s) violated:`
///   paired with `Undefined Behavior`) are accepted.
fn classify_miri_output(exit_code: Option<i32>, stderr: &str) -> Result<String, String> {
    if exit_code == Some(0) {
        return Err("Miri exited with status 0 (witness did not trigger UB)".into());
    }
    if stderr.contains("error[E") || stderr.contains("could not compile") {
        return Err(format!("replay harness failed to compile (not UB):\n{stderr}"));
    }
    if let Some(line) = stderr.lines().find(|l| l.contains("error: Undefined Behavior:")) {
        return Ok(line.trim().to_owned());
    }
    if stderr.contains("unsafe precondition(s) violated:") && stderr.contains("Undefined Behavior")
    {
        let line = stderr
            .lines()
            .find(|l| l.contains("unsafe precondition(s) violated:"))
            .unwrap_or("unsafe precondition(s) violated");
        return Ok(line.trim().to_owned());
    }
    if stderr.contains("panicked at") || stderr.contains("thread 'main' panicked") {
        return Err(format!("replay harness panicked without Miri UB diagnostic:\n{stderr}"));
    }
    Err(format!("Miri exited with {exit_code:?} without a recognized UB diagnostic:\n{stderr}"))
}

/// Gate a counterexample witness through the replay classification contract.
///
/// Unclassified (`None`) and `ModelOnlyUnreplayed` witnesses fail closed to
/// [`ReplayVerdict::ModelOnlyUnreplayed`] without ever claiming confirmed Miri
/// UB. Only [`WitnessClass::ReplayableMiriUb`] witnesses execute `run_miri`.
pub(super) fn gate_witness_replay<F>(ce: &Counterexample, run_miri: F) -> ReplayVerdict
where
    F: FnOnce() -> Result<(Option<i32>, String), String>,
{
    match ce.witness_class {
        Some(WitnessClass::ModelOnlyUnreplayed) => ReplayVerdict::ModelOnlyUnreplayed {
            note: ce
                .witness_note
                .clone()
                .unwrap_or_else(|| "conservative model-only UB class".into()),
        },
        None => ReplayVerdict::ModelOnlyUnreplayed {
            note: "unclassified witness defaults fail-closed to model_only_unreplayed".into(),
        },
        Some(WitnessClass::ReplayableMiriUb) => match run_miri() {
            Ok((code, stderr)) => match classify_miri_output(code, &stderr) {
                Ok(diagnostic) => ReplayVerdict::ConfirmedMiriUb { diagnostic },
                Err(reason) => ReplayVerdict::ReplayFailed { reason },
            },
            Err(reason) => ReplayVerdict::ReplayFailed { reason },
        },
    }
}

const DEFAULT_MIRI_TOOLCHAIN_CANDIDATES: &[&str] =
    &["nightly-2026-05-31", "nightly-2026-09-30", "nightly"];

/// Parse installed toolchain names from `rustup toolchain list` stdout,
/// stripping trailing annotations such as `(default)` or `(active, default)`.
pub(super) fn parse_installed_toolchains(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            if trimmed.is_empty() {
                return None;
            }
            // Strip parenthesized status annotations (` (default)`, etc.).
            let base = trimmed.split(" (").next().unwrap_or("").trim();
            // Skip status prose such as `no installed toolchains`.
            if base.is_empty() || base.contains(char::is_whitespace) {
                return None;
            }
            Some(base.to_owned())
        })
        .collect()
}

/// Query locally installed rustup toolchains without touching the network.
fn installed_rustup_toolchains() -> Option<Vec<String>> {
    let out = Command::new("rustup").args(["toolchain", "list"]).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(parse_installed_toolchains(&String::from_utf8_lossy(&out.stdout)))
}

/// Read the active host target triple from `rustc -vV` (offline).
fn rustc_host_triple() -> Option<String> {
    let out = Command::new("rustc").arg("-vV").output().ok()?;
    if !out.status.success() {
        return None;
    }
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host:").map(|rest| rest.trim().to_owned()))
        .filter(|h| !h.is_empty())
}

/// Whether `candidate` matches a toolchain already present in `installed`
/// (exact name or `<candidate>-<host_triple>`), so we never invoke a `cargo
/// +<tc>` rustup proxy that could attempt a network sync on an uninstalled
/// toolchain.
pub(super) fn is_toolchain_installed(
    installed: &[String],
    candidate: &str,
    host_triple: Option<&str>,
) -> bool {
    if installed.iter().any(|tc| tc == candidate) {
        return true;
    }
    if let Some(host) = host_triple {
        let with_host = format!("{candidate}-{host}");
        return installed.iter().any(|tc| tc == &with_host);
    }
    installed.iter().any(|tc| {
        tc.strip_prefix(candidate).and_then(|s| s.strip_prefix('-')).is_some_and(|rest| {
            // Avoid matching dated nightlies (`nightly-2026-05-31-...`) when
            // searching for unpinned `nightly`.
            !rest.bytes().next().is_some_and(|b| b.is_ascii_digit()) && rest.contains('-')
        })
    })
}

fn toolchain_has_runnable_miri(tc: &str) -> bool {
    // When rustup recognizes the toolchain's component list, require `miri`
    // locally before running `cargo +<tc> miri`. Custom linked toolchains may
    // fail `rustup component list`, in which case we still probe the already-
    // installed toolchain directly.
    if let Ok(comp) = Command::new("rustup")
        .args(["component", "list", "--installed", "--toolchain", tc])
        .output()
        && comp.status.success()
    {
        let stdout = String::from_utf8_lossy(&comp.stdout);
        let has_miri = stdout.lines().any(|l| {
            let name = l.trim();
            name == "miri" || name.starts_with("miri-")
        });
        if !has_miri {
            return false;
        }
    }
    let ver = Command::new("cargo")
        .args([&format!("+{tc}"), "miri", "--version"])
        .env("CARGO_NET_OFFLINE", "true")
        .output();
    if let Ok(o) = ver
        && o.status.success()
    {
        let sysroot = Command::new("cargo")
            .args([&format!("+{tc}"), "miri", "setup", "--print-sysroot"])
            .env("CARGO_NET_OFFLINE", "true")
            .output();
        if let Ok(s) = sysroot
            && s.status.success()
        {
            return true;
        }
    }
    false
}

/// Detect an installed and runnable `cargo +<toolchain> miri` toolchain
/// strictly among locally installed rustup toolchains (never invoking `cargo
/// +<tc>` for an uninstalled candidate).
///
/// When `explicit_override` (`ANNEAL_MIRI_TOOLCHAIN`) is `Some`, fails closed
/// (`Err`) if that exact toolchain is uninstalled or unusable instead of
/// falling back to another nightly.
pub(super) fn detect_miri_toolchain_in<F>(
    explicit_override: Option<&str>,
    installed_toolchains: Option<&[String]>,
    host_triple: Option<&str>,
    mut probe_miri: F,
) -> Result<Option<String>, String>
where
    F: FnMut(&str) -> bool,
{
    let Some(installed) = installed_toolchains else {
        if let Some(explicit) = explicit_override.map(str::trim).filter(|s| !s.is_empty()) {
            return Err(format!(
                "ANNEAL_MIRI_TOOLCHAIN='{explicit}' requested, but `rustup toolchain list` \
                 is unavailable"
            ));
        }
        return Ok(None);
    };
    if let Some(explicit) = explicit_override.map(str::trim).filter(|s| !s.is_empty()) {
        if is_toolchain_installed(installed, explicit, host_triple) && probe_miri(explicit) {
            return Ok(Some(explicit.to_owned()));
        }
        return Err(format!(
            "ANNEAL_MIRI_TOOLCHAIN='{explicit}' is not an installed runnable Miri toolchain \
             with an offline-ready sysroot"
        ));
    }
    for &tc in DEFAULT_MIRI_TOOLCHAIN_CANDIDATES {
        if is_toolchain_installed(installed, tc, host_triple) && probe_miri(tc) {
            return Ok(Some(tc.to_owned()));
        }
    }
    Ok(None)
}

pub(super) fn detect_miri_toolchain() -> Result<Option<String>, String> {
    let explicit = env::var("ANNEAL_MIRI_TOOLCHAIN").ok();
    let installed = installed_rustup_toolchains();
    let host = rustc_host_triple();
    detect_miri_toolchain_in(
        explicit.as_deref(),
        installed.as_deref(),
        host.as_deref(),
        toolchain_has_runnable_miri,
    )
}

/// Execute standalone Rust `source` under `cargo +<toolchain> miri run` inside
/// a temporary crate directory using an isolated `target_dir` and
/// `-Zmiri-symbolic-alignment-check`.
pub(super) fn run_miri_snippet(
    toolchain: &str,
    workspace_dir: &Path,
    target_dir: &Path,
    crate_name: &str,
    source: &str,
) -> Result<(Option<i32>, String), String> {
    let crate_dir = workspace_dir.join(crate_name);
    let src_dir = crate_dir.join("src");
    fs::create_dir(&crate_dir).map_err(|e| format!("create crate dir: {e}"))?;
    fs::create_dir(&src_dir).map_err(|e| format!("create src dir: {e}"))?;
    fs::write(
        crate_dir.join("Cargo.toml"),
        format!("[package]\nname = \"{crate_name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"),
    )
    .map_err(|e| format!("write Cargo.toml: {e}"))?;
    fs::write(src_dir.join("main.rs"), source).map_err(|e| format!("write main.rs: {e}"))?;

    let miriflags = match env::var("MIRIFLAGS") {
        Ok(existing) if !existing.trim().is_empty() => {
            if existing.contains("-Zmiri-symbolic-alignment-check") {
                existing
            } else {
                format!("{existing} -Zmiri-symbolic-alignment-check")
            }
        }
        _ => "-Zmiri-symbolic-alignment-check".into(),
    };

    let mut cmd = Command::new("cargo");
    cmd.args([
        &format!("+{toolchain}"),
        "miri",
        "run",
        "--offline",
        "--manifest-path",
        crate_dir.join("Cargo.toml").to_str().ok_or("non-utf8 manifest path")?,
    ]);
    cmd.env("CARGO_TARGET_DIR", target_dir);
    cmd.env("MIRIFLAGS", miriflags);
    let output = cmd.output().map_err(|e| format!("spawn cargo miri: {e}"))?;
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    Ok((output.status.code(), stderr))
}

pub(super) fn synthetic_ce(
    witness_class: Option<WitnessClass>,
    witness_note: Option<&str>,
) -> Counterexample {
    Counterexample {
        args: Vec::new(),
        caller_mem: CallerMemory::default(),
        witness_class,
        witness_note: witness_note.map(str::to_owned),
        fault_location: None,
        trace: StepTrace {
            body_id: 0,
            identity: "test::synthetic".into(),
            steps_executed: 1,
            fuel_limit: 16,
            outcome: Outcome::Fault(FaultDetail::undefined("synthetic")),
            events: Vec::new(),
            final_state: None,
        },
    }
}

pub(super) fn extract_slice_and_mid(ce: &Counterexample) -> (Vec<u8>, u64) {
    let (ptr, len) = match &ce.args[0] {
        Val::SlicePtr { ptr, len } => (ptr, *len),
        other => panic!("expected SlicePtr arg 0, got {other:?}"),
    };
    let mid = match &ce.args[1] {
        Val::Scalar(s) => s.bits as u64,
        other => panic!("expected usize arg 1, got {other:?}"),
    };
    let bytes = if len == 0 {
        Vec::new()
    } else {
        let alloc_id = ptr.alloc_id.expect("non-empty slice must have allocation provenance");
        let alloc = ce
            .caller_mem
            .allocations
            .iter()
            .find(|a| a.alloc_id == alloc_id)
            .expect("slice allocation must exist in caller_mem");
        let start = ptr.offset_bytes as usize;
        let end = start + (len as usize);
        alloc.bytes[start..end]
            .iter()
            .map(|b| match b {
                AllocByte::Init { byte, .. } => *byte,
                AllocByte::Uninit => panic!("valid &[u8] entry arg must have initialized bytes"),
            })
            .collect()
    };
    (bytes, mid)
}

pub(super) fn render_raw_u32_deref_harness(ce: &Counterexample) -> String {
    let Val::Ptr(pv) = &ce.args[0] else {
        panic!("expected Ptr arg 0, got {:?}", ce.args[0]);
    };
    match pv.alloc_id {
        None => {
            let addr = pv.offset_bytes;
            format!(
                "fn main() {{\n\
                     let p: *const u32 = {addr}_usize as *const u32;\n\
                     let _ = unsafe {{ *p }};\n\
                 }}\n"
            )
        }
        Some(aid) => {
            let alloc = ce
                .caller_mem
                .allocations
                .iter()
                .find(|a| a.alloc_id == aid)
                .expect("ptr alloc_id in caller_mem");
            if !alloc.live {
                "fn main() {\n\
                     let p: *const u32 = { let x: u32 = 0; &raw const x };\n\
                     let _ = unsafe { *p };\n\
                 }\n"
                .into()
            } else if alloc.bytes.iter().any(|b| matches!(b, AllocByte::Uninit)) {
                "fn main() {\n\
                     let x = core::mem::MaybeUninit::<u32>::uninit();\n\
                     let p: *const u32 = x.as_ptr();\n\
                     let _ = unsafe { *p };\n\
                 }\n"
                .into()
            } else {
                let len = alloc.bytes.len();
                let align_bytes = 1usize << alloc.align_log2;
                let off = pv.offset_bytes;
                format!(
                    "#[repr(C, align({align_bytes}))]\n\
                     struct AlignedBuf([u8; {len}]);\n\
                     fn main() {{\n\
                         let buf = AlignedBuf([0u8; {len}]);\n\
                         let p = buf.0.as_ptr().wrapping_add({off}) as *const u32;\n\
                         let _ = unsafe {{ *p }};\n\
                     }}\n"
                )
            }
        }
    }
}
