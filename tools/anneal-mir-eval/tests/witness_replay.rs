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

#[path = "witness_replay/live.rs"]
mod live;
#[path = "witness_replay/support.rs"]
mod support;

use std::{collections::BTreeSet, env};

use anneal_mir_eval::{
    AllocByte, Allocation, Block, Body, CallerMemory, CaptureInput, ConstLit, CoreCallOp,
    Counterexample, EvalConfig, FaultDetail, FaultKind, IntTy, IntWidth, Mutability, Operand,
    Outcome, PanicStrategy, Place, ProbeConfig, Program, ProjectionElem, PtrVal, Rvalue, Scope,
    Statement, SysrootNumKind, SysrootNumOp, TargetEndian, Terminator, Ty, UbClass, UnwindAction,
    Val, WitnessClass, eval_body_with_caller_mem, probe_body,
};
use support::{
    ReplayVerdict, TempDir, U8_TY, U32_TY, USIZE_TY, detect_miri_toolchain,
    detect_miri_toolchain_in, extract_slice_and_mid, gate_witness_replay, is_toolchain_installed,
    parse_installed_toolchains, render_raw_u32_deref_harness, synthetic_ce,
};

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
        UbClass::ConservativeOverlappingAssignCopy,
        UbClass::ZstOptionNonePayloadRead,
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

    live::replay_zc08(&toolchain, &work_dir, &target_dir, zc08_ce, &zc08_bytes, zc08_mid);
    live::replay_unchecked_add(&toolchain, &work_dir, &target_dir, uadd_ce, uadd_a, uadd_b);
    live::replay_ptr_add(&toolchain, &work_dir, &target_dir, ptr_add_ce, ptr_add_count);
    live::replay_raw_deref(&toolchain, &work_dir, &target_dir, deref_ce, &deref_rust_src);
    live::replay_dead_zero_contrast(&toolchain, &work_dir, &target_dir);
    live::replay_misaligned_deref(&toolchain, &work_dir, &target_dir, &deref_prog, &v2_cfg);
    live::replay_overlapping_assign(&toolchain, &work_dir, &target_dir, &v2_cfg);
}
