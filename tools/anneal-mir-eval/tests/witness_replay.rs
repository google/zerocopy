// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Anti-bypass Miri witness-replay gate and live differential verification
//! for `anneal-mir-eval` counterexamples.
//!
//! Every `FaultKind::Undefined` witness emitted by `anneal-mir-eval` is
//! classified into one of two disjoint classes:
//! - [`WitnessClass::ReplayableMiriUb`]: language or library UB that must
//!   reproduce as an explicit Miri UB diagnostic when replayed as standalone
//!   Rust under Miri (never passing on exit 0, compile errors, or ordinary
//!   panics).
//! - [`WitnessClass::ModelOnlyUnreplayed`]: conservative over-approximations
//!   in `Trusted.MirSemantics` (or entry-invariant violations) that are never
//!   silently treated as confirmed Miri UB.

#![forbid(unsafe_code)]

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use anneal_mir_eval::{
    AllocByte, Allocation, Block, Body, CallerMemory, CaptureInput, ConstLit, CoreCallOp,
    Counterexample, EvalConfig, FaultDetail, FaultKind, IntTy, IntWidth, Mutability, Operand,
    Outcome, PanicStrategy, Place, ProbeConfig, Program, ProjectionElem, PtrVal, Rvalue, Scope,
    Statement, StepTrace, SysrootNumKind, SysrootNumOp, TargetEndian, Terminator, Ty, UbClass,
    UnwindAction, Val, WitnessClass, eval_body_with_caller_mem, probe_body,
};

const U8_TY: Ty = Ty::Int(IntTy { width: IntWidth::I8, signed: false });
const U32_TY: Ty = Ty::Int(IntTy { width: IntWidth::I32, signed: false });
const USIZE_TY: Ty = Ty::Int(IntTy { width: IntWidth::Isize, signed: false });

static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(0);

struct TempDir(PathBuf);

impl TempDir {
    fn new(prefix: &str) -> Self {
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

    fn path(&self) -> &Path {
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
enum ReplayVerdict {
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
fn gate_witness_replay<F>(ce: &Counterexample, run_miri: F) -> ReplayVerdict
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
fn parse_installed_toolchains(stdout: &str) -> Vec<String> {
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
fn is_toolchain_installed(
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
fn detect_miri_toolchain_in<F>(
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

fn detect_miri_toolchain() -> Result<Option<String>, String> {
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
fn run_miri_snippet(
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

fn synthetic_ce(witness_class: Option<WitnessClass>, witness_note: Option<&str>) -> Counterexample {
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

#[test]
fn anti_bypass_gate_never_promotes_model_only_or_unclassified_witnesses() {
    // Unclassified `FaultDetail::undefined(...)` fails closed to
    // `ModelOnlyUnreplayed` (never silently classified as `ReplayableMiriUb`).
    let unclassified_fault = FaultDetail::undefined("legacy unclassified UB");
    assert_eq!(unclassified_fault.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
    assert!(unclassified_fault.model_only_note().is_some());

    // Non-UB faults (`Unsupported`) carry no UB witness class.
    assert_eq!(FaultDetail::unsupported("unsupported op").witness_class(), None);

    // Every `ModelOnlyUnreplayed` `UbClass` carries a non-empty explanation.
    let model_only_classes = [
        UbClass::ZeroOffsetDeadOrOobPtr,
        UbClass::ZstNullRawPtrDeref,
        UbClass::ZstProvenanceDeadOrOob,
        UbClass::ZstMutRefImmutableAlloc,
        UbClass::RefPointeeUninitOrInvalid,
        UbClass::MoveDeinitLocalRead,
        UbClass::CheckPtrAssertOnly,
        UbClass::ZstStackRefEscape,
        UbClass::SymbolicAllocAlignment,
        UbClass::DivergingCallReturned,
        UbClass::EntryInvalidRefArg,
        UbClass::SyntheticInvalidConstOrSwitch,
    ];
    for cls in model_only_classes {
        assert_eq!(cls.witness_class(), WitnessClass::ModelOnlyUnreplayed, "{cls:?}");
        assert!(
            cls.model_only_note().is_some_and(|n| !n.is_empty()),
            "missing model-only note for {cls:?}"
        );
    }

    // `gate_witness_replay` MUST return `ModelOnlyUnreplayed` without invoking
    // the Miri runner when the witness is `ModelOnlyUnreplayed` or `None`.
    let model_ce = synthetic_ce(
        Some(WitnessClass::ModelOnlyUnreplayed),
        Some("conservative zero-offset check"),
    );
    assert_eq!(
        gate_witness_replay(&model_ce, || panic!("runner must not execute for model-only class")),
        ReplayVerdict::ModelOnlyUnreplayed { note: "conservative zero-offset check".into() }
    );

    let none_ce = synthetic_ce(None, None);
    assert!(matches!(
        gate_witness_replay(&none_ce, || panic!("runner must not execute for unclassified class")),
        ReplayVerdict::ModelOnlyUnreplayed { .. }
    ));
}

#[test]
fn anti_bypass_gate_rejects_compile_errors_panics_and_zero_exit() {
    let replayable_ce = synthetic_ce(Some(WitnessClass::ReplayableMiriUb), None);

    // 1. Exit 0 MUST fail the gate (`ReplayFailed`), never confirm UB.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((Some(0), String::new()))),
        ReplayVerdict::ReplayFailed { .. }
    ));

    // 2. Compile error (`error[E0425]` or syntax `could not compile`) MUST fail
    //    the gate.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((
            Some(101),
            "error[E0425]: cannot find value `bogus`\nerror: could not compile `replay`".into(),
        ))),
        ReplayVerdict::ReplayFailed { .. }
    ));
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((
            Some(101),
            "error: expected item, found `}`\nerror: could not compile `replay`".into(),
        ))),
        ReplayVerdict::ReplayFailed { .. }
    ));

    // 3. Ordinary panic MUST fail the gate.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((
            Some(101),
            "thread 'main' panicked at src/main.rs:2:5:\nindex out of bounds".into(),
        ))),
        ReplayVerdict::ReplayFailed { .. }
    ));

    // 4. Unrecognized non-zero exit MUST fail the gate.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((Some(1), "unexpected crash".into()))),
        ReplayVerdict::ReplayFailed { .. }
    ));

    // 5. Genuine Miri language UB diagnostic confirms UB.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((
            Some(1),
            "error: Undefined Behavior: dereferencing pointer failed: null pointer".into(),
        ))),
        ReplayVerdict::ConfirmedMiriUb { .. }
    ));

    // 6. Genuine Miri library UB precondition diagnostic confirms UB.
    assert!(matches!(
        gate_witness_replay(&replayable_ce, || Ok((
            Some(1),
            "fatal runtime error: unsafe precondition(s) violated: slice::get_unchecked\n\
             This indicates a bug in the program. This Undefined Behavior check is optional."
                .into(),
        ))),
        ReplayVerdict::ConfirmedMiriUb { .. }
    ));
}

#[test]
fn miri_toolchain_detection_skips_uninstalled_toolchains_without_probing() {
    let host = Some("x86_64-unknown-linux-gnu");

    // 1. Stable-only environment (`rustup toolchain list` has no nightlies):
    //    auto-detection returns `Ok(None)` without ever probing `cargo +<tc>`.
    let stable_only = parse_installed_toolchains(
        "1.100.0-x86_64-unknown-linux-gnu (active, default)\n\
         1.56.0-x86_64-unknown-linux-gnu\n",
    );
    assert_eq!(
        detect_miri_toolchain_in(None, Some(&stable_only), host, |tc| {
            panic!("must not probe uninstalled toolchain '{tc}'")
        }),
        Ok(None)
    );

    // 2. Empty / `no installed toolchains` and missing `rustup`: auto returns
    //    `Ok(None)` without probing; explicit override fails closed.
    assert!(parse_installed_toolchains("no installed toolchains\n").is_empty());
    assert_eq!(
        detect_miri_toolchain_in(None, None, host, |tc| {
            panic!("must not probe when rustup is absent: '{tc}'")
        }),
        Ok(None)
    );
    assert!(
        detect_miri_toolchain_in(Some("nightly-2026-05-31"), None, host, |tc| {
            panic!("must not probe when rustup is absent: '{tc}'")
        })
        .is_err()
    );

    // 3. Dated nightly only (`nightly-2026-05-31-x86_64-unknown-linux-gnu`)
    //    must NOT falsely match unpinned `nightly` or another host triple.
    let dated_only = parse_installed_toolchains(
        "nightly-2026-05-31-x86_64-unknown-linux-gnu\n\
         nightly-2026-09-30-aarch64-apple-darwin\n",
    );
    assert!(is_toolchain_installed(&dated_only, "nightly-2026-05-31", host));
    assert!(is_toolchain_installed(
        &dated_only,
        "nightly-2026-05-31-x86_64-unknown-linux-gnu",
        host
    ));
    assert!(!is_toolchain_installed(&dated_only, "nightly", host));
    assert!(!is_toolchain_installed(&dated_only, "nightly-2026-09-30", host));
    // Fallback without host triple still rejects dated nightly for `nightly`.
    assert!(!is_toolchain_installed(&dated_only, "nightly", None));

    // 4. Only installed candidates are probed; explicit uninstalled override
    //    fails closed without invoking `probe_miri` or falling back.
    let default_nightly = parse_installed_toolchains(
        "stable-x86_64-unknown-linux-gnu\n\
         nightly-x86_64-unknown-linux-gnu (active, default)\n",
    );
    let mut probed = Vec::new();
    let found = detect_miri_toolchain_in(None, Some(&default_nightly), host, |tc| {
        probed.push(tc.to_owned());
        true
    });
    assert_eq!(found, Ok(Some("nightly".to_owned())));
    assert_eq!(probed, vec!["nightly".to_owned()]);

    assert!(
        detect_miri_toolchain_in(
            Some("nonexistent-miri-toolchain-0000"),
            Some(&default_nightly),
            host,
            |tc| panic!("must not probe uninstalled explicit override '{tc}'"),
        )
        .is_err()
    );
}

#[test]
fn miri_witness_replay_confirms_probe_ub_and_contrasts_model_only() {
    // Always extract all 5 probe/eval witnesses even if Miri is unavailable on
    // a minimal CI runner; only the live Miri subprocess execution requires a
    // Miri toolchain (or fails loudly when `ANNEAL_REQUIRE_MIRI_REPLAY=1`).

    // --- Witness 1: Verbatim `08_byte_slice_split_at_unchecked` ---
    const ZEROCOPY_08_JSON: &str =
        include_str!("fixtures/zerocopy_08_byte_slice_split_at_unchecked_capture.json");
    let CaptureInput::Manifest(zc08) = CaptureInput::from_json_str(ZEROCOPY_08_JSON).unwrap()
    else {
        panic!("expected schema-5 manifest");
    };
    let zc08_cfg = EvalConfig::for_program(
        &zc08.program,
        TargetEndian::from_manifest_str(&zc08.configuration.endian),
    )
    .unwrap();
    let zc08_report =
        probe_body(&zc08.program, 0, &ProbeConfig { max_cases: 48, fuel: 128, seed: 1 }, &zc08_cfg);
    let zc08_ce = zc08_report
        .first_replayable_undefined
        .as_ref()
        .expect("probe must find replayable UB witness for split_at_unchecked");
    assert_eq!(zc08_ce.witness_class, Some(WitnessClass::ReplayableMiriUb));
    assert_eq!(zc08_report.model_only_unreplayed_ub_count, 0);

    let (zc08_bytes, zc08_mid) = extract_slice_and_mid(zc08_ce);
    assert!(
        zc08_mid > zc08_bytes.len() as u64,
        "witness mid={zc08_mid} must exceed slice len={}",
        zc08_bytes.len()
    );

    // --- Witness 2: Profile v1 `SysrootCall(UncheckedAdd)` overflow ---
    let uadd_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 1,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 2,
            is_unsafe: true,
            identity: "rust-path-v1::replay::unchecked_add_u8".into(),
            local_tys: vec![U8_TY, U8_TY, U8_TY],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::SysrootCall {
                        op: SysrootNumOp {
                            kind: SysrootNumKind::UncheckedAdd,
                            ty: IntTy { width: IntWidth::I8, signed: false },
                        },
                        args: vec![
                            Operand::Copy { local: 1, projection: Vec::new() },
                            Operand::Copy { local: 2, projection: Vec::new() },
                        ],
                        dst_local: 0,
                        dst_projection: Vec::new(),
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
        }],
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    };
    let uadd_report = probe_body(
        &uadd_prog,
        0,
        &ProbeConfig { max_cases: 64, fuel: 32, seed: 1 },
        &EvalConfig::profile_v1(),
    );
    let uadd_ce = uadd_report
        .first_replayable_undefined
        .as_ref()
        .expect("probe must find replayable UB witness for unchecked_add");
    let (uadd_a, uadd_b) = match (&uadd_ce.args[0], &uadd_ce.args[1]) {
        (Val::Scalar(a), Val::Scalar(b)) => (a.bits as u8, b.bits as u8),
        other => panic!("unexpected unchecked_add witness args: {other:?}"),
    };
    assert!(uadd_a.checked_add(uadd_b).is_none(), "witness ({uadd_a}, {uadd_b}) must overflow u8");

    // --- Witness 3: Profile v2 `CoreCallOp::PtrAdd` out-of-bounds ---
    let const_u32_ptr = Ty::RawPtr { mutability: Mutability::Shared, pointee: Box::new(U32_TY) };
    let ptr_add_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "rust-path-v1::replay::ptr_add_oob".into(),
            local_tys: vec![const_u32_ptr.clone(), USIZE_TY, U32_TY, const_u32_ptr.clone()],
            blocks: vec![
                Block {
                    statements: vec![
                        Statement::StorageLive { local: 2 },
                        Statement::Assign {
                            local: 2,
                            projection: Vec::new(),
                            value: Rvalue::Use {
                                operand: Operand::Constant {
                                    ty: U32_TY,
                                    lit: ConstLit::Scalar { bits: 7 },
                                },
                                with_retag: false,
                            },
                        },
                        Statement::Assign {
                            local: 3,
                            projection: Vec::new(),
                            value: Rvalue::AddressOf {
                                mutability: Mutability::Shared,
                                place: Place { local: 2, projection: Vec::new() },
                            },
                        },
                    ],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::PtrAdd { mutability: Mutability::Shared, pointee: U32_TY },
                        args: vec![
                            Operand::Copy { local: 3, projection: Vec::new() },
                            Operand::Copy { local: 1, projection: Vec::new() },
                        ],
                        dst: Place { local: 0, projection: Vec::new() },
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
        }],
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    };
    let v2_cfg = EvalConfig::profile_v2(TargetEndian::Little);
    let ptr_add_report =
        probe_body(&ptr_add_prog, 0, &ProbeConfig { max_cases: 32, fuel: 32, seed: 1 }, &v2_cfg);
    let ptr_add_ce = ptr_add_report
        .first_replayable_undefined
        .as_ref()
        .expect("probe must find replayable UB witness for ptr_add");
    let ptr_add_count = match &ptr_add_ce.args[0] {
        Val::Scalar(s) => s.bits as u64,
        other => panic!("unexpected ptr_add count arg: {other:?}"),
    };
    assert!(ptr_add_count > 1, "expected OOB ptr_add count > 1, got {ptr_add_count}");

    // --- Witness 4: Profile v2 raw pointer dereference UB (`*const u32`) ---
    let deref_prog = Program {
        scope: Scope::Crate,
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "rust-path-v1::replay::deref_raw_u32".into(),
            local_tys: vec![U32_TY, const_u32_ptr.clone()],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 0,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::CopyPlace {
                            place: Place { local: 1, projection: vec![ProjectionElem::Deref] },
                        },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    };
    let deref_report =
        probe_body(&deref_prog, 0, &ProbeConfig { max_cases: 32, fuel: 32, seed: 1 }, &v2_cfg);
    let deref_ce = deref_report
        .first_replayable_undefined
        .as_ref()
        .expect("probe must find replayable UB witness for raw pointer deref");
    let deref_rust_src = render_raw_u32_deref_harness(deref_ce);

    // --- Witness 5: Conservative `ModelOnlyUnreplayed`
    //     (`ZeroOffsetDeadOrOobPtr`) ---
    let zero_off_prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["rust-path-v1::replay::zero_offset_dead".into()]
                .into_iter()
                .collect::<BTreeSet<_>>(),
            instantiations: BTreeSet::new(),
        },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: true,
            identity: "rust-path-v1::replay::zero_offset_dead".into(),
            local_tys: vec![const_u32_ptr.clone(), const_u32_ptr],
            blocks: vec![
                Block {
                    statements: vec![],
                    terminator: Terminator::CoreCall {
                        op: CoreCallOp::PtrAdd { mutability: Mutability::Shared, pointee: U32_TY },
                        args: vec![
                            Operand::Copy { local: 1, projection: Vec::new() },
                            Operand::Constant { ty: USIZE_TY, lit: ConstLit::Scalar { bits: 0 } },
                        ],
                        dst: Place { local: 0, projection: Vec::new() },
                        target: Some(1),
                        unwind: UnwindAction::Continue,
                    },
                    cleanup: false,
                },
                Block { statements: vec![], terminator: Terminator::Ret, cleanup: false },
            ],
        }],
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    };
    let dead_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Shared,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; 4],
            live: false,
        }],
    };
    let dead_ptr = Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 0, width: IntWidth::Isize });
    let zero_off_trace = eval_body_with_caller_mem(
        &zero_off_prog,
        0,
        std::slice::from_ref(&dead_ptr),
        dead_cm.clone(),
        32,
        &v2_cfg,
    );
    match &zero_off_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::ZeroOffsetDeadOrOobPtr));
            assert_eq!(f.witness_class(), Some(WitnessClass::ModelOnlyUnreplayed));
        }
        other => panic!("expected ZeroOffsetDeadOrOobPtr, got {other:?}"),
    }
    let zero_off_ce = Counterexample::from_trace(vec![dead_ptr], dead_cm, zero_off_trace);
    assert!(matches!(
        gate_witness_replay(&zero_off_ce, || panic!("model-only must not run replay gate")),
        ReplayVerdict::ModelOnlyUnreplayed { .. }
    ));

    // --- Live Miri Execution (mandatory if ANNEAL_REQUIRE_MIRI_REPLAY=1) ---
    let require_miri = env::var("ANNEAL_REQUIRE_MIRI_REPLAY")
        .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
    let detected = detect_miri_toolchain()
        .unwrap_or_else(|e| panic!("explicit Miri toolchain override failed: {e}"));
    let Some(toolchain) = detected else {
        assert!(
            !require_miri,
            "ANNEAL_REQUIRE_MIRI_REPLAY=1 is set, but no `cargo +<tc> miri` toolchain was found"
        );
        eprintln!(
            "[witness_replay] Miri toolchain not installed on host; \
             probe witness extraction and anti-bypass gate verified, live Miri replay skipped"
        );
        return;
    };

    let work_dir = TempDir::new("anneal-miri-replay");
    // Use an isolated per-run target directory inside `work_dir` so Cargo/Miri
    // never reuses stale invocation stubs from a deleted temp crate; Miri
    // still reuses its cached sysroot (`~/.cache/miri` or `MIRI_SYSROOT`).
    let target_dir = work_dir.path().join("target");

    // 1. Live replay of verbatim `zerocopy` `split_at_unchecked` OOB witness
    //    plus positive control.
    let zc08_ub_src = format!(
        "fn main() {{\n\
             let bytes: &[u8] = &{zc08_bytes:?};\n\
             let mid: usize = {zc08_mid}_usize;\n\
             unsafe {{\n\
                 let _ = (bytes.get_unchecked(..mid), bytes.get_unchecked(mid..));\n\
             }}\n\
         }}\n"
    );
    let v1 = gate_witness_replay(zc08_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "zc08_ub", &zc08_ub_src)
    });
    match &v1 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] zc08 split_at_unchecked -> {diagnostic}");
        }
        other => panic!("zerocopy split_at_unchecked witness failed Miri replay: {other:?}"),
    }
    let zc08_ok_src = format!(
        "fn main() {{\n\
             let bytes: &[u8] = &{zc08_bytes:?};\n\
             let mid: usize = 0;\n\
             unsafe {{\n\
                 let (h, t) = (bytes.get_unchecked(..mid), bytes.get_unchecked(mid..));\n\
                 assert_eq!(h.len() + t.len(), bytes.len());\n\
             }}\n\
         }}\n"
    );
    let (ok_code, ok_err) =
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "zc08_ok", &zc08_ok_src)
            .unwrap();
    assert_eq!(ok_code, Some(0), "positive control zc08_ok failed under Miri:\n{ok_err}");

    // 2. Live replay of Profile v1 `unchecked_add` overflow witness plus
    //    positive control.
    let uadd_ub_src = format!(
        "fn main() {{\n\
             let a: u8 = {uadd_a};\n\
             let b: u8 = {uadd_b};\n\
             let _ = unsafe {{ a.unchecked_add(b) }};\n\
         }}\n"
    );
    let v2 = gate_witness_replay(uadd_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "uadd_ub", &uadd_ub_src)
    });
    match &v2 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!(
                "[witness_replay:{toolchain}] unchecked_add({uadd_a}, {uadd_b}) -> {diagnostic}"
            );
        }
        other => panic!("unchecked_add witness failed Miri replay: {other:?}"),
    }
    let (uadd_ok_code, uadd_ok_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "uadd_ok",
        "fn main() { assert_eq!(unsafe { 1u8.unchecked_add(2) }, 3); }\n",
    )
    .unwrap();
    assert_eq!(uadd_ok_code, Some(0), "uadd_ok failed under Miri:\n{uadd_ok_err}");

    // 3. Live replay of Profile v2 `CoreCallOp::PtrAdd` OOB witness plus
    //    positive control.
    let ptr_add_ub_src = format!(
        "fn main() {{\n\
             let x: u32 = 7;\n\
             let p: *const u32 = &raw const x;\n\
             let _ = unsafe {{ p.add({ptr_add_count}_usize) }};\n\
         }}\n"
    );
    let v3 = gate_witness_replay(ptr_add_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "ptr_add_ub", &ptr_add_ub_src)
    });
    match &v3 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] ptr.add({ptr_add_count}) -> {diagnostic}");
        }
        other => panic!("ptr_add OOB witness failed Miri replay: {other:?}"),
    }
    let (pa_ok_code, pa_ok_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "ptr_add_ok",
        "fn main() { let x: u32 = 7; let p = &raw const x; let _ = unsafe { p.add(1) }; }\n",
    )
    .unwrap();
    assert_eq!(pa_ok_code, Some(0), "ptr_add_ok failed under Miri:\n{pa_ok_err}");

    // 4. Live replay of Profile v2 raw pointer dereference UB witness plus
    //    positive control.
    let v4 = gate_witness_replay(deref_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "deref_ub", &deref_rust_src)
    });
    match &v4 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] raw_ptr_deref -> {diagnostic}");
        }
        other => {
            panic!(
                "raw pointer deref witness failed Miri replay: {other:?}\nsource:\n{deref_rust_src}"
            )
        }
    }
    let (dr_ok_code, dr_ok_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "deref_ok",
        "fn main() { let x: u32 = 42; let p = &raw const x; assert_eq!(unsafe { *p }, 42); }\n",
    )
    .unwrap();
    assert_eq!(dr_ok_code, Some(0), "deref_ok failed under Miri:\n{dr_ok_err}");

    // 5. Empirical contrast under live Miri: zero-byte `p.add(0)` on a dead
    //    stack pointer exits 0 under Miri (NOT UB), confirming why
    //    `ZeroOffsetDeadOrOobPtr` is classified `ModelOnlyUnreplayed`.
    let (dead_zero_code, dead_zero_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "dead_zero_contrast",
        "fn main() {\n\
             let p: *const u32 = { let x: u32 = 0; &raw const x };\n\
             let _ = unsafe { p.add(0) };\n\
         }\n",
    )
    .unwrap();
    assert_eq!(
        dead_zero_code,
        Some(0),
        "expected dead_ptr.add(0) to exit 0 under Miri:\n{dead_zero_err}"
    );
    // 6. Live replay of concrete misaligned raw pointer deref (`alloc.align=4`,
    //    `offset=1` -> `UbClass::MisalignedMemoryAccess` -> `ConfirmedMiriUb`).
    let misalign_cm = CallerMemory {
        allocations: vec![Allocation {
            alloc_id: 2,
            align_log2: 2,
            mutability: Mutability::Shared,
            bytes: vec![AllocByte::Init { byte: 0, prov: None }; 8],
            live: true,
        }],
    };
    let misalign_ptr =
        Val::Ptr(PtrVal { alloc_id: Some(2), offset_bytes: 1, width: IntWidth::Isize });
    let misalign_trace = eval_body_with_caller_mem(
        &deref_prog,
        0,
        std::slice::from_ref(&misalign_ptr),
        misalign_cm.clone(),
        32,
        &v2_cfg,
    );
    match &misalign_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::MisalignedMemoryAccess));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected MisalignedMemoryAccess, got {other:?}"),
    }
    let misalign_ce = Counterexample::from_trace(vec![misalign_ptr], misalign_cm, misalign_trace);
    let misalign_src = render_raw_u32_deref_harness(&misalign_ce);
    let v6 = gate_witness_replay(&misalign_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "misalign_ub", &misalign_src)
    });
    match &v6 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] misaligned_u32_deref -> {diagnostic}");
        }
        other => panic!("misaligned raw u32 deref failed Miri replay: {other:?}"),
    }

    // 7. Live replay of overlapping `(u32, u32, u32)` (`BackendRepr::Memory`)
    //    `Assign` copy UB (`UbClass::OverlappingMemoryCopy` -> `ConfirmedMiriUb`
    //    with Miri `copy_nonoverlapping` diagnostic) plus padding-free
    //    `ScalarPair` `(u32, u32)` positive control (`exit 0`).
    let tup3_ty = Ty::Tuple { fields: vec![U32_TY, U32_TY, U32_TY] };
    let overlap_prog = Program {
        scope: Scope::SelectedUnit {
            roots: ["rust-path-v1::replay::overlap_assign_tup3".into()]
                .into_iter()
                .collect::<BTreeSet<_>>(),
            instantiations: BTreeSet::new(),
        },
        entry_def_id: 0,
        pointer_width_bits: 64,
        mir_profile_version: 2,
        overflow_checks: false,
        bodies: vec![Body {
            arg_count: 1,
            is_unsafe: false,
            identity: "rust-path-v1::replay::overlap_assign_tup3".into(),
            local_tys: vec![Ty::Unit, tup3_ty],
            blocks: vec![Block {
                statements: vec![Statement::Assign {
                    local: 1,
                    projection: Vec::new(),
                    value: Rvalue::Use {
                        operand: Operand::Copy { local: 1, projection: Vec::new() },
                        with_retag: false,
                    },
                }],
                terminator: Terminator::Ret,
                cleanup: false,
            }],
        }],
        panic: PanicStrategy::Unwind,
        has_local_panic_handler: true,
    };
    let overlap_args = vec![Val::Tuple(vec![Val::u32(1), Val::u32(2), Val::u32(3)])];
    let overlap_cm = CallerMemory::default();
    let overlap_trace =
        eval_body_with_caller_mem(&overlap_prog, 0, &overlap_args, overlap_cm.clone(), 16, &v2_cfg);
    match &overlap_trace.outcome {
        Outcome::Fault(f) => {
            assert_eq!(f.kind, FaultKind::Undefined);
            assert_eq!(f.ub_class, Some(UbClass::OverlappingMemoryCopy));
            assert_eq!(f.witness_class(), Some(WitnessClass::ReplayableMiriUb));
        }
        other => panic!("expected OverlappingMemoryCopy, got {other:?}"),
    }
    let overlap_ce = Counterexample::from_trace(overlap_args, overlap_cm, overlap_trace);
    let overlap_ub_src = "\
#![allow(internal_features)]\n\
#![feature(custom_mir, core_intrinsics)]\n\
use core::intrinsics::mir::*;\n\
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n\
fn self_copy_tup3(mut a: (u32, u32, u32)) {\n\
    mir! { { a = a; Return() } }\n\
}\n\
fn main() {\n\
    self_copy_tup3((1, 2, 3));\n\
}\n";
    let v7 = gate_witness_replay(&overlap_ce, || {
        run_miri_snippet(&toolchain, work_dir.path(), &target_dir, "overlap_ub", overlap_ub_src)
    });
    match &v7 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            assert!(
                diagnostic.contains("copy_nonoverlapping"),
                "expected copy_nonoverlapping diagnostic, got: {diagnostic}"
            );
            eprintln!("[witness_replay:{toolchain}] overlap_assign_tup3 -> {diagnostic}");
        }
        other => panic!("overlapping (u32, u32, u32) Assign witness failed Miri replay: {other:?}"),
    }
    let scalar_pair_ok_src = "\
#![allow(internal_features)]\n\
#![feature(custom_mir, core_intrinsics)]\n\
use core::intrinsics::mir::*;\n\
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n\
fn self_copy_tup2(mut a: (u32, u32)) {\n\
    mir! { { a = a; Return() } }\n\
}\n\
fn main() {\n\
    self_copy_tup2((1, 2));\n\
}\n";
    let (ov_ok_code, ov_ok_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "overlap_pair_ok",
        scalar_pair_ok_src,
    )
    .unwrap();
    assert_eq!(
        ov_ok_code,
        Some(0),
        "padding-free ScalarPair (u32, u32) self-Assign failed under Miri:\n{ov_ok_err}"
    );
    // Confirm live Miri ground truth: an immediate (non-address-taken) padded
    // `(u32, bool)` local produced by `Checked` exits 0 (`ModelOnlyUnreplayed`),
    // whereas an in-memory padded `(u32, bool)` (`*p = *p`) hits Miri's
    // `copy_nonoverlapping` UB (`ReplayableMiriUb`).
    let imm_padded_ok_src = "\
#![allow(internal_features)]\n\
#![feature(custom_mir, core_intrinsics)]\n\
use core::intrinsics::mir::*;\n\
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n\
fn self_copy_imm_padded(x: u32) {\n\
    mir! {\n\
        let a: (u32, bool);\n\
        {\n\
            a = Checked(x + 1_u32);\n\
            a = a;\n\
            Return()\n\
        }\n\
    }\n\
}\n\
fn main() {\n\
    self_copy_imm_padded(1);\n\
}\n";
    let (imm_pad_code, imm_pad_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "overlap_imm_padded_ok",
        imm_padded_ok_src,
    )
    .unwrap();
    assert_eq!(
        imm_pad_code,
        Some(0),
        "immediate padded (u32, bool) self-Assign should exit 0 under Miri:\n{imm_pad_err}"
    );
    let mem_padded_ub_src = "\
#![allow(internal_features)]\n\
#![feature(custom_mir, core_intrinsics)]\n\
use core::intrinsics::mir::*;\n\
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n\
fn self_copy_mem_padded(p: *mut (u32, bool)) {\n\
    mir! { { *p = *p; Return() } }\n\
}\n\
fn main() {\n\
    let mut a: (u32, bool) = (1, true);\n\
    self_copy_mem_padded(&raw mut a);\n\
}\n";
    let (mem_pad_code, mem_pad_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "overlap_mem_padded_ub",
        mem_padded_ub_src,
    )
    .unwrap();
    assert_ne!(
        mem_pad_code,
        Some(0),
        "in-memory padded (u32, bool) *p = *p should trigger Miri UB"
    );
    assert!(
        mem_pad_err.contains("copy_nonoverlapping"),
        "expected copy_nonoverlapping diagnostic on in-memory (u32, bool), got:\n{mem_pad_err}"
    );
    // Confirm live Miri ground truth: alignment-inflated `([u64; 0], u32, u32)`
    // has `BackendRepr::Memory` (even with zero padding bytes), so local
    // self-Assign `a = a` hits Miri's `copy_nonoverlapping` UB (`ReplayableMiriUb`).
    let align_inflated_ub_src = "\
#![allow(internal_features)]\n\
#![feature(custom_mir, core_intrinsics)]\n\
use core::intrinsics::mir::*;\n\
#[custom_mir(dialect = \"runtime\", phase = \"post-cleanup\")]\n\
fn self_copy_align_inflated(mut a: ([u64; 0], u32, u32)) {\n\
    mir! { { a = a; Return() } }\n\
}\n\
fn main() {\n\
    self_copy_align_inflated(([], 1, 2));\n\
}\n";
    let (ai_code, ai_err) = run_miri_snippet(
        &toolchain,
        work_dir.path(),
        &target_dir,
        "overlap_align_inflated_ub",
        align_inflated_ub_src,
    )
    .unwrap();
    assert_ne!(
        ai_code,
        Some(0),
        "alignment-inflated ([u64; 0], u32, u32) local a = a should trigger Miri UB"
    );
    assert!(
        ai_err.contains("copy_nonoverlapping"),
        "expected copy_nonoverlapping diagnostic on ([u64; 0], u32, u32), got:\n{ai_err}"
    );
}

fn extract_slice_and_mid(ce: &Counterexample) -> (Vec<u8>, u64) {
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

fn render_raw_u32_deref_harness(ce: &Counterexample) -> String {
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
