// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Unit tests and live end-to-end differential tests for `anneal-itree-diff`.

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::{collections::BTreeMap, env, fs, num::NonZeroU32, path::PathBuf, time::Duration};

use anneal_itree_diff::{
    CaseReport, DifferentialConfig, DifferentialEngine, DifferentialReport,
    apply_fuzz_shrink_outcome, check_case_expectation, check_case_expectation_with_mir_eval,
    checkout_boundary_root,
    corpus::curated_corpus,
    define_traced_enum, define_traced_struct, evaluate_metamorphic_duality, evaluate_mir_eval_leg,
    filter_corpus_cases,
    fuzzer::{FuzzStep, MutatorKind, generate_fuzz_batch},
    lean_trace_runner::{
        CaptureAttempt, CapturedArtifacts, LeanTraceMode, LeanTraceSession,
        MetamorphicDualityReceipt, build_capture_cargo_invocation_with_env,
        build_capture_invocation_with_env, build_lean_invocation_with_env,
        compute_capture_build_dir_tag, compute_lean_cache_key, compute_rustc_sysroot_digest,
        ensure_lean_and_driver_oleans, expected_base_olean_rel_paths, lean_str_lit,
        parse_lean_trace_output, parse_lean_trace_output_with_expected_args,
        resolve_cargo_binary_with_env_and_suffix, validate_cached_artifact_manifest,
        write_cached_artifact_manifest,
    },
    mir_eval_adapter::{
        MirEvalAdapter, MirEvalAvailability, build_mir_eval_invocation_with_env,
        parse_mir_eval_output, parse_mir_eval_output_with_expected_args,
    },
    miri_runner::{
        MiriAvailability, MiriProbeError, MiriRunner, MiriSysrootIdentity,
        build_miri_run_invocation_with_env, build_miri_setup_invocation_with_env,
        detect_authenticated_miri_ub_line, detect_miri_ub_line, miri_setup_search_dirs,
        parse_miri_run_output, parse_miri_run_output_authenticated,
        parse_miri_run_output_with_expected_args, query_miri_sysroot,
        query_miri_sysroot_with_timeout, resolve_cargo_miri_binary_with_path_and_suffix,
        resolve_miri_coordinates_with_env, resolve_miri_coordinates_with_env_and_suffix,
        validate_explicit_miri_sysroot,
    },
    normalize_configured_path,
    outcome::{
        AuthorityRunResult, CallerFrameLaw, CallerFrameSnapshot, ConservativeRefKind,
        DisclosedGapKind, DisclosedGapSpec, ExpectedConservativeSpec, ExpectedUbSpec, IntKind,
        MetamorphicStatus, SpineCompareMode, TerminalOutcome, TraceVal, TraceVerdict, UbFaultClass,
        classify_four_way, classify_four_way_with_ub_guard, classify_ub_fault_detail,
        compare_spines, compare_ub_fault_results, compute_boundary_mem_digest,
        normalize_unwind_reason, ub_fault_causes_compatible,
    },
    resolve_default_cache_root, resolve_default_cache_root_with_env,
    rustc_runner::{
        DYLIB_PATH_ENV_VAR, RustcDualResult, RustcRunner, build_rustc_compile_invocation_with_env,
        build_rustc_run_invocation_with_env, canonicalize_preserving_rustup_proxy_with_suffix,
        forward_platform_temp_and_profile_env_with_env, forward_standard_tool_env_with_env,
        join_dylib_path_with_existing, join_path_list_with_existing,
        parse_and_validate_host_target_triple, parse_rustc_run_output,
        parse_rustc_run_output_for_platform, parse_rustc_run_output_with_expected_args,
        query_rustc_host_target_with_timeout, query_rustc_sysroot,
        query_rustc_sysroot_with_timeout, resolve_explicit_or_path_exe_with_suffix,
        resolve_rustup_env_for_sysroot_with_env, run_supervised_retrying_busy,
        run_supervised_with_prefix, sysroots_equivalent, validate_host_target_matches_native_arch,
        validate_host_target_matches_platform,
    },
    should_skip_host_rustc,
    shrink::{
        ShrinkBudget, ShrinkFailureSignature, WitnessArtifact, shrink_fuzz_program,
        shrink_fuzz_program_with_budget, shrink_i32_non_monotonic, shrink_sequence_1_minimal,
        shrink_u32_non_monotonic,
    },
    shrink_and_build_witness_with, shrink_and_build_witness_with_budget,
    spec::{
        CaseCategory, ExpectedCaseClass, LeanProgramSpec, ReturnShape, TraceTestCase,
        parse_pre_entry_slots_stdout, parse_trace_json_stdout,
        parse_trace_json_stdout_with_expected_args, render_standalone_rust_harness,
    },
    trace_observer::{
        EnvAction, EnvSchedule, FromScheduleBytes, MaskedByte, ObservableEvent, ObservableSpine,
        PRE_ENTRY_JSON_PREFIX, ScheduleError, ShadowProvenanceTable, TraceRunDisposition,
        capture_masked_bytes, capture_padding_mask, capture_value_bytes, run_with_trace_recorder,
        value_as_raw_bytes,
    },
    traced_external_fn, validate_cache_root_outside_checkout, validate_cli_run_plan,
    validate_run_plan, validate_strict_multicall_probe, workspace_anneal_root,
};

define_traced_struct! {
    struct TestPaddedRecord {
        tag: u8,
        // 3 bytes implicit C padding at offsets 1..4
        value: u32,
        flag: bool,
        // 3 bytes trailing C padding at offsets 9..12
    }
}

define_traced_enum! {
    #[repr(u8)]
    enum TestOpCode {
        Alpha = 0,
        Beta = 2,
        Gamma = 7,
    }
}

traced_external_fn! {
    fn sample_traced_callee(x: u32, mode: TestOpCode) -> u32 {
        match mode {
            TestOpCode::Alpha => x.wrapping_add(1),
            TestOpCode::Beta => x.wrapping_mul(2),
            TestOpCode::Gamma => x ^ 0x55,
        }
    }
}

traced_external_fn! {
    fn sample_bool_callee(x: u32) -> bool {
        (x & 1) == 1
    }
}

traced_external_fn! {
    fn sample_panicking_callee(mode: u32) -> u32 {
        if mode == 0 {
            panic!("static body panic")
        } else {
            panic!("formatted body panic {mode}")
        }
    }
}

#[test]
fn padding_safe_offset_of_capture_and_poisoned_padding() {
    let rec = TestPaddedRecord { tag: 0xAB, value: 0x1122_3344, flag: true };
    let captured = capture_value_bytes(&rec);
    assert_eq!(captured.len(), core::mem::size_of::<TestPaddedRecord>());
    assert_eq!(captured.len(), 12);
    assert_eq!(captured[0], Some(0xAB));
    assert_eq!(&captured[4..8], &[Some(0x44), Some(0x33), Some(0x22), Some(0x11)]);
    assert_eq!(captured[8], Some(1));
    assert_eq!(&captured[1..4], &[None, None, None]);
    assert_eq!(&captured[9..12], &[None, None, None]);

    // Poisoned-padding test: construct two instances backed by raw aligned
    // buffers whose padding slots hold 0xAA vs 0x55, and verify `TraceCapture`
    // never reads or leaks the poisoned padding bytes (`Pad` vs `Init(0)`).
    #[repr(C, align(4))]
    struct AlignedBuf([u8; 12]);
    let mut raw_a = AlignedBuf([0xAAu8; 12]);
    let mut raw_b = AlignedBuf([0x55u8; 12]);
    for buf in [&mut raw_a.0, &mut raw_b.0] {
        buf[0] = 0x00; // tag = 0 (must stay Init(0), distinct from Pad!)
        buf[4..8].copy_from_slice(&0x1122_3344u32.to_le_bytes());
        buf[8] = 1;
    }
    let ptr_a = raw_a.0.as_ptr().cast::<TestPaddedRecord>();
    let ptr_b = raw_b.0.as_ptr().cast::<TestPaddedRecord>();
    let masked_a = unsafe { capture_masked_bytes(&*ptr_a) };
    let masked_b = unsafe { capture_masked_bytes(&*ptr_b) };
    assert_eq!(masked_a, masked_b);
    assert_eq!(masked_a[0], MaskedByte::Init(0));
    assert_eq!(masked_a[1], MaskedByte::Pad);
    assert_eq!(masked_a[2], MaskedByte::Pad);
    assert_eq!(masked_a[3], MaskedByte::Pad);
    assert_eq!(masked_a[9], MaskedByte::Pad);

    let mask = capture_padding_mask(&rec);
    assert_eq!(
        mask,
        vec![true, false, false, false, true, true, true, true, true, false, false, false]
    );

    let raw = value_as_raw_bytes(&rec);
    assert_eq!(raw, vec![0xAB, 0, 0, 0, 0x44, 0x33, 0x22, 0x11, 1, 0, 0, 0]);

    let mut noisy = raw.clone();
    noisy[1] = 0xFF;
    noisy[2] = 0xEE;
    noisy[3] = 0xDD;
    noisy[9] = 0xCC;
    let decoded = TestPaddedRecord::from_schedule_bytes(&noisy).expect("valid padded decode");
    assert_eq!(decoded, rec);

    let mut bad_bool = raw.clone();
    bad_bool[8] = 2;
    assert!(matches!(
        TestPaddedRecord::from_schedule_bytes(&bad_bool),
        Err(ScheduleError::InvalidBitPattern { .. })
    ));
    assert!(matches!(
        TestPaddedRecord::from_schedule_bytes(&raw[..8]),
        Err(ScheduleError::PayloadSizeMismatch { expected: 12, actual: 8, .. })
    ));
    assert!(matches!(
        bool::from_schedule_bytes(&[2]),
        Err(ScheduleError::InvalidBitPattern { .. })
    ));
    assert!(matches!(
        char::from_schedule_bytes(&0xD800u32.to_le_bytes()),
        Err(ScheduleError::InvalidBitPattern { .. })
    ));
    assert_eq!(char::from_schedule_bytes(&('Z' as u32).to_le_bytes()).unwrap(), 'Z');
    assert!(matches!(
        NonZeroU32::from_schedule_bytes(&0u32.to_le_bytes()),
        Err(ScheduleError::InvalidBitPattern { .. })
    ));
    assert_eq!(NonZeroU32::from_schedule_bytes(&42u32.to_le_bytes()).unwrap().get(), 42);
    assert_eq!(TestOpCode::from_schedule_bytes(&[2]).unwrap(), TestOpCode::Beta);
    assert!(matches!(
        TestOpCode::from_schedule_bytes(&[5]),
        Err(ScheduleError::InvalidBitPattern { .. })
    ));
}

#[test]
fn traced_external_fn_schedule_return_unwind_abort_and_invalid_bytes() {
    // 1. Default body + scheduled ReturnBytes.
    let mut sched = EnvSchedule::default();
    sched
        .push_callee("sample_traced_callee", EnvAction::ReturnBytes(999u32.to_le_bytes().to_vec()));
    let (res, rec) = run_with_trace_recorder(sched, || {
        let a = sample_traced_callee(10, TestOpCode::Alpha);
        let b = sample_traced_callee(10, TestOpCode::Beta);
        a + b
    });
    assert_eq!(res, TraceRunDisposition::Returned(1019));
    let calls = rec.spine.erased_call_spine();
    assert_eq!(calls.len(), 4);
    assert!(
        matches!(&calls[0], ObservableEvent::CallEnter { callee, .. } if callee == "sample_traced_callee")
    );
    assert!(matches!(&calls[1], ObservableEvent::CallReturn { ret_repr, .. } if ret_repr == "999"));
    assert!(matches!(&calls[3], ObservableEvent::CallReturn { ret_repr, .. } if ret_repr == "20"));

    // 2. Scheduled Unwind.
    let mut unwind_sched = EnvSchedule::default();
    unwind_sched
        .push_callee("sample_traced_callee", EnvAction::Unwind { message: "boom".to_string() });
    let (res_u, rec_u) =
        run_with_trace_recorder(unwind_sched, || sample_traced_callee(5, TestOpCode::Gamma));
    assert_eq!(res_u, TraceRunDisposition::Unwound { message: "boom".to_string() });
    assert!(rec_u.spine.events.iter().any(|e| matches!(
        e,
        ObservableEvent::CallUnwind { callee, reason } if callee == "sample_traced_callee" && reason == "boom"
    )));

    // 3. Scheduled Abort.
    let mut abort_sched = EnvSchedule::default();
    abort_sched
        .push_callee("sample_traced_callee", EnvAction::Abort { reason: "fatal_stop".to_string() });
    let (res_a, rec_a) =
        run_with_trace_recorder(abort_sched, || sample_traced_callee(5, TestOpCode::Alpha));
    assert!(
        matches!(res_a, TraceRunDisposition::ScheduledAbort(ref p) if p.reason == "fatal_stop")
    );
    assert!(rec_a.spine.events.iter().any(|e| matches!(
        e,
        ObservableEvent::CallUnwind { reason, .. } if reason == "abort:fatal_stop"
    )));

    // 4. Invalid scheduled ReturnBytes MUST surface as InvalidSchedule, NEVER
    //    masquerading as a normal callee Unwound!
    let mut bad_sched = EnvSchedule::default();
    bad_sched.push_callee("sample_bool_callee", EnvAction::ReturnBytes(vec![2u8]));
    let (res_bad, rec_bad) = run_with_trace_recorder(bad_sched, || sample_bool_callee(7));
    assert!(matches!(res_bad, TraceRunDisposition::InvalidSchedule(_)), "got {res_bad:?}");
    assert!(rec_bad.schedule_error.is_some());

    // 5. Fallback body panics (`&'static str` and `String`) MUST dereference
    //    `Box<dyn Any + Send>` (`&*__payload`) and preserve exact panic text in
    //    both `ObservableEvent::CallUnwind` and `TraceRunDisposition::Unwound`.
    let (res_p0, rec_p0) =
        run_with_trace_recorder(EnvSchedule::default(), || sample_panicking_callee(0));
    assert_eq!(res_p0, TraceRunDisposition::Unwound { message: "static body panic".to_string() });
    assert!(rec_p0.spine.events.iter().any(|e| matches!(
        e,
        ObservableEvent::CallUnwind { callee, reason }
            if callee == "sample_panicking_callee" && reason == "static body panic"
    )));

    let (res_p1, rec_p1) =
        run_with_trace_recorder(EnvSchedule::default(), || sample_panicking_callee(42));
    assert_eq!(
        res_p1,
        TraceRunDisposition::Unwound { message: "formatted body panic 42".to_string() }
    );
    assert!(rec_p1.spine.events.iter().any(|e| matches!(
        e,
        ObservableEvent::CallUnwind { callee, reason }
            if callee == "sample_panicking_callee" && reason == "formatted body panic 42"
    )));
}

#[test]
fn shadow_provenance_table_resolves_and_unregisters_via_raii_guard() {
    let mut table = ShadowProvenanceTable::new();
    let buf: [u32; 4] = [10, 20, 30, 40];
    let base = core::ptr::from_ref(&buf).addr();

    let alloc_id = {
        let guard = table.register_scoped_ref("stack_buf", &buf, false);
        let id = guard.alloc_id();
        let elem2 = guard.table().resolve_addr(base + 8, false).expect("interior offset");
        assert_eq!(elem2.alloc_id, id);
        assert_eq!(elem2.offset, 8);
        assert_eq!(elem2.tag, "stack_buf");

        assert!(guard.table().resolve_addr(base + 16, false).is_none());
        let end = guard.table().resolve_addr(base + 16, true).expect("one-past-end");
        assert_eq!(end.offset, 16);

        let ptr: *const u32 = core::ptr::from_ref(&buf[1]);
        let ptr_bytes = capture_value_bytes(&ptr);
        let decoded =
            guard.table().decode_pointer_bytes(&ptr_bytes, false).expect("decode pointer");
        assert_eq!(decoded.alloc_id, id);
        assert_eq!(decoded.offset, 4);
        id
    };

    // Dropping `ScopedAllocationGuard` unregisters `alloc_id` so popped stack
    // frames never leave stale provenance.
    assert!(table.resolve_addr(base + 8, false).is_none());
    assert!(!table.unregister_allocation(alloc_id));
}

#[test]
fn caller_frame_law_detects_local_alloc_and_padding_violations() {
    let before = CallerFrameSnapshot {
        locals: BTreeMap::from([
            ("_1".to_string(), vec![Some(1), None, None, None, Some(2)]),
            ("_dst".to_string(), vec![Some(0)]),
        ]),
        allocs: BTreeMap::from([(1u64, vec![Some(0xAA), None, Some(0xBB)])]),
    };

    let mut ok_after = before.clone();
    ok_after.locals.insert("_dst".to_string(), vec![Some(99)]);
    let law_ok = CallerFrameLaw::verify(&before, &ok_after, &["_dst"], &[]);
    assert!(law_ok.is_satisfied(), "{law_ok:?}");

    let mut bad_local = ok_after.clone();
    bad_local.locals.insert("_1".to_string(), vec![Some(9), None, None, None, Some(2)]);
    let law_local = CallerFrameLaw::verify(&before, &bad_local, &["_dst"], &[]);
    assert!(!law_local.caller_locals_preserved);
    assert!(!law_local.is_satisfied());

    let mut bad_pad = ok_after.clone();
    bad_pad.locals.insert("_1".to_string(), vec![Some(1), Some(0xEE), None, None, Some(2)]);
    let law_pad = CallerFrameLaw::verify(&before, &bad_pad, &["_dst"], &[]);
    assert!(!law_pad.padding_mask_respected);
    assert!(!law_pad.is_satisfied());

    let mut bad_alloc = ok_after;
    bad_alloc.allocs.insert(1u64, vec![Some(0xFF), None, Some(0xBB)]);
    let law_alloc = CallerFrameLaw::verify(&before, &bad_alloc, &["_dst"], &[]);
    assert!(!law_alloc.untouched_alloc_bytes_preserved);
    assert!(!law_alloc.is_satisfied());
}

#[test]
fn miri_ub_anchoring_exit_mapping_and_unique_json_framing() {
    // User panic text or guest plain-text `error: Undefined Behavior:` stderr
    // followed by `exit(1)` must NEVER trigger `FaultUb`.
    let user_panic_stderr = "thread 'main' panicked at harness.rs:12:\nuser message: undefined behavior in prose\nnote: run with `RUST_BACKTRACE=1`";
    assert_eq!(detect_miri_ub_line(user_panic_stderr), None);
    let spoofed_plain_ub = "error: Undefined Behavior: guest eprintln spoof\n";
    assert_eq!(detect_miri_ub_line(spoofed_plain_ub), None);
    let spoof_res = parse_miri_run_output("miri", Some(1), None, "", spoofed_plain_ub, 5);
    assert!(spoof_res.tool_error.is_some(), "plain-text UB spoof must fail closed");
    assert!(!matches!(spoof_res.outcome, TerminalOutcome::FaultUb { .. }));

    let auth_tok = "__anneal_miri_auth_aabbccddeeff001122334455__";
    let real_miri_ub_stderr = format!(
        concat!(
            r#"{{"$message_type":"diagnostic","message":"Undefined Behavior: overflowing shift by 32 in `unchecked_shl`","level":"error","spans":[{{"file_name":"{tok}/harness.rs"}}],"children":[{{"level":"help","message":"this indicates a bug in the program: it performed an invalid operation, and caused Undefined Behavior","spans":[]}}]}}"#,
            "\n",
            r#"{{"$message_type":"diagnostic","message":"aborting due to 1 previous error","level":"error","spans":[],"children":[]}}"#,
            "\n"
        ),
        tok = auth_tok
    );
    assert!(detect_authenticated_miri_ub_line(&real_miri_ub_stderr, Some(auth_tok)).is_some());
    assert!(
        detect_authenticated_miri_ub_line(
            &real_miri_ub_stderr,
            Some("__anneal_miri_auth_wrong_token__")
        )
        .is_none()
    );
    let miri_ub_res = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        "",
        &real_miri_ub_stderr,
        5,
        None,
        Some(auth_tok),
    );
    assert!(matches!(miri_ub_res.outcome, TerminalOutcome::FaultUb { .. }));
    assert!(miri_ub_res.tool_error.is_none());

    let wrong_tok_res = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        "",
        &real_miri_ub_stderr,
        5,
        None,
        Some("__anneal_miri_auth_wrong_token__"),
    );
    assert!(wrong_tok_res.tool_error.is_some());
    assert!(!matches!(wrong_tok_res.outcome, TerminalOutcome::FaultUb { .. }));

    // exit(101), SIGKILL(9), SIGSEGV(11), SIGBUS(7), and unmarked SIGABRT(6)
    // must map to ToolError, never Aborted or FaultUb.
    for (code, sig) in
        [(Some(101), None), (None, Some(9)), (None, Some(11)), (None, Some(7)), (None, Some(6))]
    {
        let r_host = parse_rustc_run_output("rustc-O0", code, sig, "", "crash", 1);
        assert!(r_host.tool_error.is_some(), "expected ToolError for ({code:?}, {sig:?})");
        let r_miri = parse_miri_run_output("miri", code, sig, "", user_panic_stderr, 1);
        assert!(r_miri.tool_error.is_some(), "expected Miri ToolError for ({code:?}, {sig:?})");
    }

    // SIGABRT(6) + unique ANNEAL_ITREE_PRE_ABORT: line maps to Aborted.
    let pre_abort_stdout = "ANNEAL_ITREE_PRE_ABORT:{\"outcome_kind\":\"aborted\",\"ret\":null,\"detail\":\"abort:halt\",\"boundary_slots\":[[48]],\"caller_locals_preserved\":true,\"untouched_alloc_bytes_preserved\":true,\"padding_mask_respected\":true,\"violations\":[],\"events\":[]}\n";
    let r_abort = parse_rustc_run_output("rustc-O0", None, Some(6), pre_abort_stdout, "", 2);
    assert!(r_abort.tool_error.is_none());
    assert!(matches!(r_abort.outcome, TerminalOutcome::Aborted { .. }));

    // 0 or >= 2 prefixed JSON lines must fail closed as framing errors.
    assert!(parse_trace_json_stdout("rustc-O0", "plain stdout\n", "", 1).is_err());
    let dup_trace = "ANNEAL_ITREE_TRACE_JSON:{\"outcome_kind\":\"unwound\",\"ret\":null}\nANNEAL_ITREE_TRACE_JSON:{\"outcome_kind\":\"unwound\",\"ret\":null}\n";
    assert!(parse_trace_json_stdout("rustc-O0", dup_trace, "", 1).is_err());

    let dup_lean = "ANNEAL_LEAN_ITREE_JSON:{\"outcome_kind\":\"unwound\"}\nANNEAL_LEAN_ITREE_JSON:{\"outcome_kind\":\"unwound\"}\n";
    assert!(parse_lean_trace_output("lean", dup_lean, "", 1).tool_error.is_some());

    // Symlinked or incomplete ANNEAL_ITREE_MIRI_SYSROOT rejected.
    let tmp = tempfile::tempdir().unwrap();
    let bad_sr = tmp.path().join("empty_sr");
    fs::create_dir_all(&bad_sr).unwrap();
    assert!(validate_explicit_miri_sysroot(&bad_sr).is_err());
    #[cfg(unix)]
    {
        let link_sr = tmp.path().join("symlink_sr");
        std::os::unix::fs::symlink(&bad_sr, &link_sr).unwrap();
        assert!(validate_explicit_miri_sysroot(&link_sr).is_err());
    }
}

#[test]
fn mismatch_taxonomy_classifies_all_verdict_variants_including_degraded_and_diverged() {
    let mk = |auth: &str, out: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome: out,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };

    let digest = compute_boundary_mem_digest(&[vec![Some(42), Some(0), Some(0), Some(0)]]);
    let ret42 = TerminalOutcome::Returned { ret: TraceVal::u32(42), mem_digest: digest.clone() };
    let ret99 = TerminalOutcome::Returned { ret: TraceVal::u32(99), mem_digest: digest };
    let ub = TerminalOutcome::FaultUb { detail: "ub".to_string() };
    let refused = TerminalOutcome::CaptureRefused { reason: "unsupported".to_string() };
    let div100 = TerminalOutcome::Diverged { fuel: 100 };

    // 1. Full 4-way agreement with Miri present -> Agree.
    let v_ok = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        Some(&mk("lean", ret42.clone())),
        None,
        SpineCompareMode::ObsErasedCallsOnly,
        None,
    );
    assert_eq!(v_ok, TraceVerdict::Agree);

    // 1b. Without Miri (`miri == None`), NEVER returns Agree -> DegradedNoMiri!
    let v_no_miri = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        None,
        Some(&mk("lean", ret42.clone())),
        None,
        SpineCompareMode::ObsErasedCallsOnly,
        None,
    );
    assert!(matches!(v_no_miri, TraceVerdict::DegradedNoMiri { .. }), "{v_no_miri:?}");

    // 1c. Without Lean (`lean == None`, `miri == Some`), NEVER returns Agree ->
    //     DegradedNoLean, while still catching O0 != O2 and rustc != Miri!
    let v_no_lean = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        None,
        None,
        SpineCompareMode::ObsErasedCallsOnly,
        None,
    );
    assert!(matches!(v_no_lean, TraceVerdict::DegradedNoLean { .. }), "{v_no_lean:?}");
    assert!(!v_no_lean.is_critical_failure());

    let v_no_lean_ub = classify_four_way(
        &AuthorityRunResult::skipped_for_ub("rustc-O0", "ub"),
        &AuthorityRunResult::skipped_for_ub("rustc-O2", "ub"),
        Some(&mk("miri", ub.clone())),
        None,
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(v_no_lean_ub, TraceVerdict::DegradedNoLean { .. }), "{v_no_lean_ub:?}");

    let v_no_miri_no_lean = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        None,
        None,
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_no_miri_no_lean, TraceVerdict::DegradedNoMiri { .. }),
        "{v_no_miri_no_lean:?}"
    );

    let v_no_lean_miri_mismatch = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret99.clone())),
        None,
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_no_lean_miri_mismatch, TraceVerdict::UnsoundAccept { .. }),
        "{v_no_lean_miri_mismatch:?}"
    );

    let v_no_lean_o0_o2_mismatch = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret99.clone()),
        Some(&mk("miri", ret42.clone())),
        None,
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_no_lean_o0_o2_mismatch, TraceVerdict::UnsoundAccept { .. }),
        "{v_no_lean_o0_o2_mismatch:?}"
    );

    // 2. P0 UnsoundAccept: Miri detects UB while Lean accepts (even when host
    //    rustc had tool_error).
    let v_p0_ub = classify_four_way(
        &AuthorityRunResult::tool_error("rustc-O0", "host crashed on UB"),
        &AuthorityRunResult::tool_error("rustc-O2", "host crashed on UB"),
        Some(&mk("miri", ub.clone())),
        Some(&mk("lean", ret42.clone())),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(v_p0_ub, TraceVerdict::UnsoundAccept { .. }), "{v_p0_ub:?}");

    // 2b. UB fault-cause parity: Miri and Lean both reporting `FaultUb` agree
    //     ONLY when their normalized UB causes match (`ScheduledReturnDecode`
    //     on the same callee, `UncheckedShiftOverflow`,
    //     `UnreachableOrNoUnwind`, etc.); unrelated earlier Miri UB paired
    //     with a different Lean UB cause fails closed as `UnsoundAccept`!
    assert_eq!(
        classify_ub_fault_detail(
            "callee `ext_oracle_bool` scheduled ReturnBytes invalid: invalid bool bit pattern 0x02"
        ),
        UbFaultClass::ScheduledReturnDecode
    );
    assert_eq!(
        classify_ub_fault_detail("invalid scheduled ReturnBytes for ext_oracle_bool"),
        UbFaultClass::ScheduledReturnDecode
    );
    assert!(ub_fault_causes_compatible(
        "callee `ext_oracle_bool` scheduled ReturnBytes invalid: invalid bool bit pattern 0x02",
        "invalid scheduled ReturnBytes for ext_oracle_bool",
    ));
    assert!(!ub_fault_causes_compatible(
        "callee `ext_a` scheduled ReturnBytes invalid: invalid bool bit pattern 0x02",
        "invalid scheduled ReturnBytes for ext_b",
    ));
    assert!(!ub_fault_causes_compatible(
        "error: Undefined Behavior: entering unreachable code",
        "invalid scheduled ReturnBytes for ext_oracle_bool",
    ));
    assert!(!ub_fault_causes_compatible(
        "error: Undefined Behavior: entering unreachable code",
        "Trusted.MirSemantics.FaultKind.undefined",
    ));
    let v_ub_match = classify_four_way(
        &AuthorityRunResult::tool_error("rustc-O0", "skipped"),
        &AuthorityRunResult::tool_error("rustc-O2", "skipped"),
        Some(&mk(
            "miri",
            TerminalOutcome::FaultUb {
                detail: "callee `ext_oracle_bool` scheduled ReturnBytes invalid: invalid bool"
                    .to_string(),
            },
        )),
        Some(&mk(
            "lean",
            TerminalOutcome::FaultUb {
                detail: "invalid scheduled ReturnBytes for ext_oracle_bool".to_string(),
            },
        )),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert_eq!(v_ub_match, TraceVerdict::Agree);

    let v_ub_cause_mismatch = classify_four_way(
        &AuthorityRunResult::tool_error("rustc-O0", "skipped"),
        &AuthorityRunResult::tool_error("rustc-O2", "skipped"),
        Some(&mk(
            "miri",
            TerminalOutcome::FaultUb {
                detail: "error: Undefined Behavior: entering unreachable code".to_string(),
            },
        )),
        Some(&mk(
            "lean",
            TerminalOutcome::FaultUb {
                detail: "invalid scheduled ReturnBytes for ext_oracle_bool".to_string(),
            },
        )),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_ub_cause_mismatch, TraceVerdict::UnsoundAccept { .. }),
        "expected UnsoundAccept on UB fault cause mismatch, got {v_ub_cause_mismatch:?}"
    );

    // 3. P0 UnsoundAccept: rustc O0 != O2 when Miri succeeds.
    let v_o0_o2 = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret99),
        Some(&mk("miri", ret42.clone())),
        Some(&mk("lean", ret42.clone())),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(v_o0_o2, TraceVerdict::UnsoundAccept { .. }), "{v_o0_o2:?}");

    // 4. ConservativeOverApprox on capture refusal and fuel exhaustion.
    let v_cons = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        Some(&mk("lean", refused.clone())),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(
        v_cons,
        TraceVerdict::ConservativeOverApprox {
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
            ..
        }
    ));
    assert!(!v_cons.is_critical_failure());

    let v_fuel = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        Some(&mk("lean", div100.clone())),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(
        v_fuel,
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
    ));

    let v_both_div = classify_four_way(
        &mk("rustc-O0", div100.clone()),
        &mk("rustc-O2", div100.clone()),
        Some(&mk("miri", div100.clone())),
        Some(&mk("lean", div100)),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert_eq!(v_both_div, TraceVerdict::Agree);

    // 4b. Undeclared Lean UB fault on an accepting Miri run fails closed.
    let v_false_ub = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        Some(&mk("lean", ub.clone())),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(v_false_ub.is_critical_failure());

    let unbridged_spec =
        DisclosedGapSpec::new(DisclosedGapKind::UnbridgedSemantics, "unbridged custom construct");
    let v_decl_ub = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42.clone())),
        Some(&mk(
            "lean",
            TerminalOutcome::FaultUb { detail: "unbridged custom construct".to_string() },
        )),
        None,
        SpineCompareMode::OutcomeOnly,
        Some(&unbridged_spec),
    );
    assert!(matches!(
        v_decl_ub,
        TraceVerdict::DisclosedGapArtifact { gap: DisclosedGapKind::UnbridgedSemantics, .. }
    ));
    assert!(!v_decl_ub.is_critical_failure());

    // 5. ToolError NEVER silently downgraded.
    let v_tool = classify_four_way(
        &mk("rustc-O0", ret42.clone()),
        &mk("rustc-O2", ret42.clone()),
        Some(&mk("miri", ret42)),
        Some(&AuthorityRunResult::tool_error("lean", "spawn failed")),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(matches!(v_tool, TraceVerdict::ToolError { .. }));
    assert!(v_tool.is_critical_failure());
}

#[test]
fn shrinker_pins_failure_signature_and_reaches_combined_fixed_point() {
    let seq = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    let pred = |s: &[i32]| {
        let p3 = s.iter().position(|&x| x == 3);
        let p7 = s.iter().position(|&x| x == 7);
        matches!((p3, p7), (Some(a), Some(b)) if a < b)
    };
    let out1 = shrink_sequence_1_minimal(&seq, pred);
    let out2 = shrink_sequence_1_minimal(&seq, pred);
    assert_eq!(out1, out2);
    assert_eq!(out1.minimized, vec![3, 7]);

    // Verify ShrinkFailureSignature rejects ToolError and separates missed_ub
    // from terminal_outcome_mismatch.
    let ub_leg = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: TerminalOutcome::FaultUb { detail: "ub".to_string() },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let ret_leg = AuthorityRunResult {
        authority: "lean".to_string(),
        outcome: TerminalOutcome::Returned {
            ret: TraceVal::u32(1),
            mem_digest: compute_boundary_mem_digest(&[]),
        },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let tool_err_leg = AuthorityRunResult::tool_error("lean", "timeout");
    let missed_ub_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &TraceVerdict::UnsoundAccept { detail: "miri detected UB while lean accepted".to_string() },
        Some(&ub_leg),
        Some(&ret_leg),
    )
    .unwrap();
    let val_mismatch_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &TraceVerdict::UnsoundAccept { detail: "terminal outcome mismatch".to_string() },
        Some(&ret_leg),
        Some(&ret_leg),
    )
    .unwrap();
    assert_ne!(missed_ub_sig, val_mismatch_sig);
    let twin_o0_o2_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &TraceVerdict::UnsoundAccept {
            detail: "metamorphic_duality: source-inlined twin rustc O0 vs O2 mismatch: None"
                .to_string(),
        },
        Some(&ret_leg),
        Some(&ret_leg),
    )
    .unwrap();
    assert_eq!(twin_o0_o2_sig.mismatch_category, "metamorphic_duality");
    assert_eq!(twin_o0_o2_sig.metamorphic_relations, vec!["inlined_rustc_o0_vs_o2"]);

    // Distinct metamorphic failure relations and distinct twin-leg outcome
    // summaries MUST produce distinct `ShrinkFailureSignature`s under
    // `from_case_report`, so shrinking never drifts between e.g.
    // `lean_called_vs_inlined` and `inlined_rustc_o0_vs_o2` or `returned` vs
    // `unwound` twin legs.
    let ok_dual = RustcDualResult {
        o0: ret_leg.clone(),
        o2: ret_leg.clone(),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let mut bad_twin_dual = ok_dual.clone();
    bad_twin_dual.parity_ok = false;
    bad_twin_dual.mismatch_detail = Some("O0 != O2".to_string());
    let mut ret_two_leg = ret_leg.clone();
    ret_two_leg.outcome = TerminalOutcome::Returned {
        ret: TraceVal::u32(2),
        mem_digest: compute_boundary_mem_digest(&[]),
    };
    let mut unwound_leg = ret_leg.clone();
    unwound_leg.outcome = TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[]) };

    let mk_meta_report = |receipt: MetamorphicDualityReceipt| CaseReport {
        case_id: "meta_sig".to_string(),
        category: CaseCategory::FuzzGenerated,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::UnsoundAccept { detail: receipt.detail.clone() },
        expectation_violation: None,
        rustc_dual: ok_dual.clone(),
        miri: Some(ret_leg.clone()),
        lean: Some(ret_leg.clone()),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: Some(receipt),
    };
    let rec_lean_twin = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&ret_leg),
        &ret_leg,
        &ok_dual,
        Some(&ret_leg),
        ret_two_leg,
    );
    let rec_rustc_twin = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&ret_leg),
        &ret_leg,
        &bad_twin_dual,
        Some(&ret_leg),
        ret_leg.clone(),
    );
    let rec_unwound_twin = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&ret_leg),
        &ret_leg,
        &ok_dual,
        Some(&ret_leg),
        unwound_leg,
    );
    let sig_lean_twin =
        ShrinkFailureSignature::from_case_report(&mk_meta_report(rec_lean_twin)).unwrap();
    let sig_rustc_twin =
        ShrinkFailureSignature::from_case_report(&mk_meta_report(rec_rustc_twin)).unwrap();
    let sig_unwound_twin =
        ShrinkFailureSignature::from_case_report(&mk_meta_report(rec_unwound_twin)).unwrap();
    assert_ne!(sig_lean_twin, sig_rustc_twin);
    assert_ne!(sig_lean_twin, sig_unwound_twin);

    // Also verify `validate_strict_multicall_probe` rejects `StrictVerbatim`
    // acceptance whenever `CompositionalITree` exercised a `.call` boundary.
    let mut called_primary = ret_leg.clone();
    called_primary.spine.events.push(ObservableEvent::CallEnter {
        callee: "ext_step".to_string(),
        arg_bytes: vec![],
        arg_reprs: vec![],
    });
    let refused_probe = AuthorityRunResult {
        authority: "lean-strict".to_string(),
        outcome: TerminalOutcome::CaptureRefused { reason: "unsupported call".to_string() },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let conservative_verdict = TraceVerdict::ConservativeOverApprox {
        reason: "unsupported call".to_string(),
        undeclared_ub_fault: false,
        ub_refutation_disallowed: false,
    };
    assert!(
        validate_strict_multicall_probe(&called_primary, &refused_probe, &conservative_verdict)
            .is_none()
    );
    assert!(matches!(
        validate_strict_multicall_probe(&called_primary, &ret_leg, &TraceVerdict::Agree),
        Some(TraceVerdict::UnsoundAccept { .. })
    ));
    assert!(validate_strict_multicall_probe(&ret_leg, &ret_leg, &TraceVerdict::Agree).is_none());
    assert!(
        ShrinkFailureSignature::from_verdict_and_legs(
            &TraceVerdict::ToolError { authority: "lean".to_string(), detail: "err".to_string() },
            Some(&ub_leg),
            Some(&tool_err_leg),
        )
        .is_none()
    );

    // Combined fixed-point check: when `input_x > 50`, two HelperCalls are
    // required; once Stage 2 lowers `input_x <= 50` (down to `10`), a second
    // outer iteration deletes the second HelperCall to reach true 1-min!
    let batch = generate_fuzz_batch(0x1234_5678, 6);
    let mut prog = batch[2].clone();
    prog.input_x = 500;
    prog.input_y = 300;
    prog.steps = vec![
        FuzzStep::HelperCall { callee_idx: 1, bias: 25 },
        FuzzStep::HelperCall { callee_idx: 2, bias: 30 },
        FuzzStep::BranchMix { then_imm: 11, else_imm: 19 },
    ];
    let coupled_pred = |p: &anneal_itree_diff::fuzzer::FuzzProgram| {
        let h1 = p.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { callee_idx: 1, .. }));
        let h2 = p.steps.iter().any(|s| matches!(s, FuzzStep::HelperCall { callee_idx: 2, .. }));
        if p.input_x > 50 { h1 && h2 } else { p.input_x >= 10 && h1 }
    };
    let budget_cut = shrink_fuzz_program_with_budget(
        &prog,
        ShrinkBudget { max_evals: 3, max_duration: Duration::from_secs(60) },
        coupled_pred,
    );
    assert!(budget_cut.succeeded);
    assert!(budget_cut.budget_exhausted);
    assert!(!budget_cut.is_one_minimal, "budget cutoff must not claim 1-minimality");
    assert_eq!(budget_cut.predicate_evaluations, 3);

    let shrunk = shrink_fuzz_program(&prog, coupled_pred);
    assert!(shrunk.succeeded && shrunk.is_one_minimal && !shrunk.budget_exhausted);
    assert_eq!(shrunk.minimized.steps.len(), 1, "expected second ddmin pass after input shrink");
    assert_eq!(shrunk.minimized.input_x, 10);
    assert_eq!(shrunk.minimized.input_y, 0);

    let tmp = tempfile::tempdir().unwrap();
    let witness_path = tmp.path().join("witness.json");
    let witness = WitnessArtifact::from_shrink(
        "synthetic_divergence",
        TraceVerdict::UnsoundAccept { detail: "minimized synthetic witness".to_string() },
        TraceVerdict::UnsoundAccept { detail: "original synthetic witness".to_string() },
        shrunk,
    );
    witness.write_json(&witness_path).unwrap();
    let reloaded: WitnessArtifact =
        serde_json::from_str(&fs::read_to_string(&witness_path).unwrap()).unwrap();
    assert_eq!(reloaded.case_id, "synthetic_divergence");
    assert_eq!(
        reloaded.verdict,
        TraceVerdict::UnsoundAccept { detail: "minimized synthetic witness".to_string() }
    );
    assert_eq!(
        reloaded.original_verdict,
        TraceVerdict::UnsoundAccept { detail: "original synthetic witness".to_string() }
    );
    assert_eq!(reloaded.shrink.minimized_steps, 1);
}

#[test]
fn fuzzer_determinism_and_all_five_mutators() {
    let b1 = generate_fuzz_batch(0xBEEF_CAFE, 12);
    let b2 = generate_fuzz_batch(0xBEEF_CAFE, 12);
    assert_eq!(b1, b2, "fuzzer must be strictly deterministic per seed");

    let mut seen = Vec::new();
    for p in &b1 {
        assert!(
            (1..=2).contains(&p.applied_mutators.len()),
            "expected 1..=2 applied mutators, got {:?}",
            p.applied_mutators
        );
        for m in &p.applied_mutators {
            if !seen.contains(m) {
                seen.push(*m);
            }
        }
    }
    for m in MutatorKind::ALL {
        assert!(seen.contains(&m), "missing mutator {m:?} in batch");
    }
}

#[cfg(unix)]
#[test]
fn mir_eval_adapter_mock_protocol_and_probe() {
    let unavail = MirEvalAdapter::probe_with_env(|_| None);
    assert!(matches!(unavail, MirEvalAvailability::Unavailable { .. }));

    let tmp = tempfile::tempdir().unwrap();
    let mock_bin = tmp.path().join("anneal-mir-eval");
    let fake_capture = tmp.path().join("capture.json");
    fs::write(&fake_capture, "{}").unwrap();

    let script = r#"#!/usr/bin/env bash
case "$*" in
  *"--body 0"*)
    printf '%s\n' '{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"scalar","value":{"width":"i32","signed":false,"bits":"42"}}}}}'
    exit 0
    ;;
  *"--body 1"*)
    printf '%s\n' '{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"shift overflow"}}}'
    exit 2
    ;;
  *"--body 2"*)
    printf '%s\n' '{"outcome":{"kind":"fault","value":{"kind":"unsupported","reason":"call terminator"}}}'
    exit 3
    ;;
  *"--body 3"*)
    printf '%s\n' '{"outcome":{"kind":"out_of_fuel"}}'
    exit 3
    ;;
  *"--body 4"*)
    printf '%s\n' '{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"bad exit"}}}'
    exit 0
    ;;
  *)
    printf '%s\n' '{"outcome":{"kind":"returned","value":{"kind":"unwound"}}}'
    exit 0
    ;;
esac
"#;
    fs::write(&mock_bin, script).unwrap();
    let mut perms = fs::metadata(&mock_bin).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&mock_bin, perms).unwrap();

    let avail = MirEvalAdapter::probe_with_env(|k| {
        if k == "ANNEAL_MIR_EVAL_BIN" { Some(mock_bin.as_os_str().to_os_string()) } else { None }
    });
    let MirEvalAvailability::Available(adapter) = avail else {
        panic!("expected mock MirEvalAdapter to be available");
    };

    let expected_post_ret42_digest =
        compute_boundary_mem_digest(&[vec![Some(0x10), Some(42), Some(0), Some(0), Some(0)]]);
    let r0 = adapter.eval_captured(&fake_capture, 0, 128, &[TraceVal::u32(7)]);
    assert!(r0.tool_error.is_none());
    assert!(r0.post_only_mem_digest, "value-only mir_eval output must flag post_only_mem_digest");
    assert_eq!(
        r0.outcome,
        TerminalOutcome::Returned {
            ret: TraceVal::Scalar { kind: IntKind::U32, bits: 42 },
            mem_digest: expected_post_ret42_digest,
        }
    );
    // Verify classify_four_way compares full-slot reference legs against
    // post-only mir_eval output without false mismatches.
    let full_ref_digest = compute_boundary_mem_digest(&[
        vec![Some(7), Some(0), Some(0), Some(0)],
        vec![Some(0x10), Some(42), Some(0), Some(0), Some(0)],
    ]);
    let full_ref_leg = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: TerminalOutcome::Returned { ret: TraceVal::u32(42), mem_digest: full_ref_digest },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    assert_eq!(
        classify_four_way(
            &full_ref_leg,
            &full_ref_leg,
            Some(&full_ref_leg),
            Some(&full_ref_leg),
            Some(&r0),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::Agree
    );

    let r1 = adapter.eval_captured(&fake_capture, 1, 128, &[]);
    assert!(matches!(r1.outcome, TerminalOutcome::FaultUb { .. }));

    let r2 = adapter.eval_captured(&fake_capture, 2, 128, &[]);
    assert!(matches!(r2.outcome, TerminalOutcome::CaptureRefused { .. }));

    let r3 = adapter.eval_captured(&fake_capture, 3, 128, &[]);
    assert_eq!(r3.outcome, TerminalOutcome::Diverged { fuel: 128 });

    let r4 = adapter.eval_captured(&fake_capture, 4, 128, &[]);
    assert!(r4.tool_error.is_some());

    let r5 = adapter.eval_captured(&fake_capture, 5, 128, &[]);
    assert!(matches!(r5.outcome, TerminalOutcome::Unwound { .. }));

    // Verify `Val::Ptr` normalizes to `OpaquePtr` (`1usize` when allocated or
    // non-zero integer address, `0usize` when null), `EnumVal` reads explicit
    // `ty.discriminants`, `Outcome::Aborted` requires exit code `4`, and
    // unmodeled `Val::Bytes` conservatively degrades to `CaptureRefused` rather
    // than `ToolError` (so `DisclosedGap` cases do not fail with `ToolError`
    // when `anneal-mir-eval` is on `PATH`).
    let ptr_non_null = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"ptr","value":{"alloc_id":0,"offset_bytes":0,"width":"isize"}}}}}"#,
        "",
        1,
    );
    assert!(ptr_non_null.tool_error.is_none(), "{ptr_non_null:?}");
    match &ptr_non_null.outcome {
        TerminalOutcome::Returned { ret, .. } => assert_eq!(ret, &TraceVal::usize_val(1)),
        other => panic!("expected Returned(1usize), got {other:?}"),
    }
    let ptr_null = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"ptr","value":{"alloc_id":null,"offset_bytes":0,"width":"isize"}}}}}"#,
        "",
        1,
    );
    match &ptr_null.outcome {
        TerminalOutcome::Returned { ret, .. } => assert_eq!(ret, &TraceVal::usize_val(0)),
        other => panic!("expected Returned(0usize), got {other:?}"),
    }

    let gap_spec = DisclosedGapSpec::new(
        DisclosedGapKind::CallerRawPtrAliasing,
        "does not model Rust's pointer aliasing rules",
    );
    let ref_ptr_digest = compute_boundary_mem_digest(&[
        vec![Some(7), Some(0), Some(0), Some(0)],
        vec![Some(0x10), Some(1), Some(0), Some(0), Some(0), Some(0), Some(0), Some(0), Some(0)],
    ]);
    let ref_ptr_leg = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: TerminalOutcome::Returned {
            ret: TraceVal::usize_val(1),
            mem_digest: ref_ptr_digest,
        },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let lean_gap_leg = AuthorityRunResult {
        authority: "lean-compositional-itree".to_string(),
        outcome: TerminalOutcome::CaptureRefused {
            reason: "body mixes reference and raw-pointer locals, which Profile v2 refuses because it does not model Rust's pointer aliasing rules".to_string(),
        },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            Some(&ref_ptr_leg),
            Some(&lean_gap_leg),
            Some(&ptr_non_null),
            SpineCompareMode::OutcomeOnly,
            Some(&gap_spec),
        ),
        TraceVerdict::DisclosedGapArtifact { gap: DisclosedGapKind::CallerRawPtrAliasing, .. }
    ));

    let enum_explicit = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"enum_val","value":{"ty":{"discriminants":["10","20"]},"variant":1}}}}}"#,
        "",
        1,
    );
    match &enum_explicit.outcome {
        TerminalOutcome::Returned {
            ret: TraceVal::Enum { variant_index, discriminant, .. },
            ..
        } => {
            assert_eq!((*variant_index, *discriminant), (1, 20));
        }
        other => panic!("expected Enum(1, 20), got {other:?}"),
    }

    let aborted_ok =
        parse_mir_eval_output(Some(4), r#"{"outcome":{"kind":"aborted","value":{}}}"#, "", 1);
    assert!(matches!(aborted_ok.outcome, TerminalOutcome::Aborted { .. }));
    let aborted_bad_exit =
        parse_mir_eval_output(Some(0), r#"{"outcome":{"kind":"aborted","value":{}}}"#, "", 1);
    assert!(aborted_bad_exit.tool_error.is_some());

    let bytes_skipped = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"bytes","value":[]}}}}"#,
        "",
        1,
    );
    assert!(bytes_skipped.tool_error.is_none());
    assert!(matches!(bytes_skipped.outcome, TerminalOutcome::CaptureRefused { .. }));

    // Explicit `boundary_slots` on nonterminal (`Fault` undefined/unsupported,
    // `OutOfFuel`) and skipped `Returned(Bytes)` outputs must match
    // `expected_entry_slots` (`Some(2)`), failing closed as `ToolError` when
    // malformed.
    for (code, payload) in [
        (
            2,
            r#"{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"shift overflow"}},"boundary_slots":[[1],[2]]}"#,
        ),
        (
            3,
            r#"{"outcome":{"kind":"fault","value":{"kind":"unsupported","reason":"call"}},"boundary_slots":[[1],[2]]}"#,
        ),
        (3, r#"{"outcome":{"kind":"out_of_fuel"},"boundary_slots":[[1],[2]]}"#),
        (
            0,
            r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"bytes","value":[]}}},"boundary_slots":[[1],[2],[16]]}"#,
        ),
    ] {
        let ok_nonterm =
            parse_mir_eval_output_with_expected_args(Some(code), payload, "", 64, 1, None, Some(2));
        assert!(ok_nonterm.tool_error.is_none(), "expected valid slots: {ok_nonterm:?}");
        let bad_nonterm =
            parse_mir_eval_output_with_expected_args(Some(code), payload, "", 64, 1, None, Some(1));
        assert!(
            bad_nonterm.tool_error.is_some(),
            "expected ToolError on entry-slot mismatch for {payload}: {bad_nonterm:?}"
        );
    }

    let unknown_kind_err = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"bogus","value":0}}}}"#,
        "",
        1,
    );
    assert!(unknown_kind_err.tool_error.is_some());

    // Capture manifest / schema skew exit-1 diagnostics from `anneal-mir-eval`
    // MUST classify as `ToolError`, never `CaptureRefused`.
    for err_msg in [
        "error: invalid capture manifest: missing field `program`",
        "error: unsupported capture schema_version 1 (expected 4)",
        "error: unsupported manifest configuration.endian 'big'",
    ] {
        let manifest_err = parse_mir_eval_output(Some(1), "", err_msg, 1);
        assert!(
            manifest_err.tool_error.is_some(),
            "expected ToolError for exit-1 manifest/schema error {err_msg:?}, got {manifest_err:?}"
        );
    }

    // Non-critical Lean verdicts (`ConservativeOverApprox` with
    // `undeclared_ub_fault: false`, or `DisclosedGapArtifact`) must NEVER mask
    // critical `mir_eval` `UnsoundAccept` or `undeclared_ub_fault: true` in
    // either Miri-enabled or `DegradedNoMiri` classification!
    let bad_ptr_wrong_val = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"ptr","value":{"alloc_id":null,"offset_bytes":0,"width":"isize"}}}}}"#,
        "",
        1,
    );
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            Some(&ref_ptr_leg),
            Some(&lean_gap_leg),
            Some(&bad_ptr_wrong_val),
            SpineCompareMode::OutcomeOnly,
            Some(&gap_spec),
        ),
        TraceVerdict::UnsoundAccept { .. }
    ));
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            None,
            Some(&lean_gap_leg),
            Some(&bad_ptr_wrong_val),
            SpineCompareMode::OutcomeOnly,
            Some(&gap_spec),
        ),
        TraceVerdict::UnsoundAccept { .. }
    ));

    let mir_eval_undecl_ub = parse_mir_eval_output(
        Some(2),
        r#"{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"spurious ub"}}}"#,
        "",
        1,
    );
    let lean_cons_leg = AuthorityRunResult {
        authority: "lean-compositional-itree".to_string(),
        outcome: TerminalOutcome::CaptureRefused { reason: "unsupported body".to_string() },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            Some(&ref_ptr_leg),
            Some(&lean_cons_leg),
            Some(&mir_eval_undecl_ub),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: true, .. }
    ));
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            None,
            Some(&lean_cons_leg),
            Some(&mir_eval_undecl_ub),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: true, .. }
    ));

    // When Miri and Lean both agree (`Returned`) while `anneal-mir-eval`
    // returns `CaptureRefused`, `Diverged`, or `DisclosedGap`,
    // `classify_four_way` MUST preserve the non-`Agree` evaluator verdict
    // rather than returning `Agree`.
    assert!(matches!(
        classify_four_way(
            &full_ref_leg,
            &full_ref_leg,
            Some(&full_ref_leg),
            Some(&full_ref_leg),
            Some(&r2),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
    ));
    assert!(matches!(
        classify_four_way(
            &full_ref_leg,
            &full_ref_leg,
            Some(&full_ref_leg),
            Some(&full_ref_leg),
            Some(&r3),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
    ));
    assert!(matches!(
        classify_four_way(
            &ref_ptr_leg,
            &ref_ptr_leg,
            Some(&ref_ptr_leg),
            Some(&ref_ptr_leg),
            Some(&lean_gap_leg),
            SpineCompareMode::OutcomeOnly,
            Some(&gap_spec),
        ),
        TraceVerdict::DisclosedGapArtifact { gap: DisclosedGapKind::CallerRawPtrAliasing, .. }
    ));
    assert!(matches!(
        classify_four_way(
            &full_ref_leg,
            &full_ref_leg,
            None,
            Some(&full_ref_leg),
            Some(&r2),
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
    ));

    // When `mir_eval` is explicitly configured (`Some(adapter)`),
    // non-`CapturedRust` cases (multi-call, synthetic AST, fuzz) and missing
    // captured bodies must NEVER silently omit `mir_eval` and claim `Agree`.
    let multicall_case = curated_corpus()
        .into_iter()
        .find(|c| {
            matches!(c.lean_program_spec, LeanProgramSpec::MultiCallWithCapturedCallees { .. })
        })
        .expect("corpus must contain a MultiCallWithCapturedCallees case");
    let me_multicall = evaluate_mir_eval_leg(Some(&adapter), None, &multicall_case)
        .expect("mir_eval must return CaptureRefused sentinel on multi-call");
    assert!(matches!(me_multicall.outcome, TerminalOutcome::CaptureRefused { .. }));
    let me_multicall_verdict = classify_four_way(
        &full_ref_leg,
        &full_ref_leg,
        Some(&full_ref_leg),
        Some(&full_ref_leg),
        Some(&me_multicall),
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(
            me_multicall_verdict,
            TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
        ),
        "got {me_multicall_verdict:?}"
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_case.lean_program_spec,
            &me_multicall_verdict,
            &RustcDualResult {
                o0: full_ref_leg.clone(),
                o2: full_ref_leg.clone(),
                parity_ok: true,
                skipped_for_ub: false,
                mismatch_detail: None,
            },
            Some(&full_ref_leg),
            Some(&full_ref_leg),
            Some(&me_multicall),
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_case.lean_program_spec,
            &TraceVerdict::Agree,
            &RustcDualResult {
                o0: full_ref_leg.clone(),
                o2: full_ref_leg.clone(),
                parity_ok: true,
                skipped_for_ub: false,
                mismatch_detail: None,
            },
            Some(&full_ref_leg),
            Some(&full_ref_leg),
            Some(&me_multicall),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "must reject false Agree when mir_eval conservatively refused"
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_case.lean_program_spec,
            &me_multicall_verdict,
            &RustcDualResult {
                o0: full_ref_leg.clone(),
                o2: full_ref_leg.clone(),
                parity_ok: true,
                skipped_for_ub: false,
                mismatch_detail: None,
            },
            Some(&full_ref_leg),
            Some(&lean_cons_leg),
            Some(&me_multicall),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "must still reject Lean CaptureRefused regression in CompositionalITree"
    );

    let fuzz_case = generate_fuzz_batch(0x1234, 1)[0].to_trace_test_case();
    let me_fuzz = evaluate_mir_eval_leg(Some(&adapter), None, &fuzz_case)
        .expect("mir_eval must return CaptureRefused sentinel on fuzz program");
    assert!(matches!(me_fuzz.outcome, TerminalOutcome::CaptureRefused { .. }));

    let mut captured_case = fuzz_case;
    captured_case.lean_program_spec = LeanProgramSpec::CapturedRust {
        crate_name: "cap_demo".to_string(),
        select_fn: "missing_fn".to_string(),
    };
    let fake_arts = CapturedArtifacts {
        capture_dir: tmp.path().to_path_buf(),
        capture_json: fake_capture,
        captured_lean: tmp.path().join("cap.lean"),
        olean_dir: tmp.path().to_path_buf(),
        body_ids_by_fn: BTreeMap::from([("other_fn".to_string(), 0)]),
    };
    let me_missing_fn = evaluate_mir_eval_leg(Some(&adapter), Some(&fake_arts), &captured_case)
        .expect("missing select_fn must produce ToolError rather than None");
    assert!(me_missing_fn.tool_error.is_some(), "expected ToolError, got {me_missing_fn:?}");
    let me_no_arts = evaluate_mir_eval_leg(Some(&adapter), None, &captured_case)
        .expect("missing capture artifacts must produce CaptureRefused rather than None");
    assert!(matches!(me_no_arts.outcome, TerminalOutcome::CaptureRefused { .. }));
}

/// Live negative test verifying that Lean `ITreeDriver` dynamically detects
/// caller-local / initialization-mask corruption across a call boundary and
/// `classify_four_way` flags it as `TraceVerdict::UnsoundAccept`.
#[test]
fn live_lean_driver_detects_caller_frame_corruption() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cache_root = resolve_default_cache_root(&anneal_root);
    let session = LeanTraceSession::prepare(&anneal_root, &cache_root).expect("prepare Lean");

    let probe = r#"import ITreeDriver
open Trusted.MirAst Trusted.MirSemantics ITreeDriver

def corruptTestProg : Program := {
  bodies := [
    {
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨2, []⟩ (some 1) .continue_ },
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨2, []⟩))],
          terminator := .return_ }
      ],
      identity := "caller"
    },
    {
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))],
          terminator := .return_ }
      ],
      identity := "callee"
    }
  ],
  entryDefId := 0,
  pointerWidthBits := 64,
  mirProfileVersion := 1,
  scope := .unit
}

#eval IO.println (ITreeDriver.runTraceCorruptCallerTest corruptTestProg 64 [.scalar ⟨.i32, false, BitVec.ofNat 128 9⟩])
"#;

    let res = session.run_raw_driver_probe(probe, "lean-corrupt-probe");
    assert!(res.tool_error.is_none(), "unexpected tool error: {res:?}");
    assert!(!res.caller_frame_law.caller_locals_preserved, "{:?}", res.caller_frame_law);
    assert!(!res.caller_frame_law.padding_mask_respected, "{:?}", res.caller_frame_law);
    assert!(!res.caller_frame_law.is_satisfied());

    let clean_ref = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: res.outcome.clone(),
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let verdict = classify_four_way(
        &clean_ref,
        &clean_ref,
        Some(&clean_ref),
        Some(&res),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(verdict, TraceVerdict::UnsoundAccept { .. }),
        "expected UnsoundAccept, got {verdict:?}"
    );
}

/// Live negative test verifying that standalone `anneal_rt` dynamically catches
/// BOTH caller-frame local mutation AND watched caller buffer mutation across a
/// call boundary under `rustc` (`-O0`/`-O2`) and `miri` (`-Zmiri-tree-borrows`
/// when available), flipping `CallerFrameCheck` and `CallerFrameLaw` to false.
#[test]
fn live_rust_and_miri_detect_caller_frame_and_watched_buffer_corruption() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cache_root = resolve_default_cache_root(&anneal_root);
    let pinned_sysroot =
        anneal_testkit::default_rust_sysroot().expect("resolve pinned rust sysroot");
    let rustc = RustcRunner::discover(Some(&pinned_sysroot)).expect("discover RustcRunner");
    let disable_miri = env::var("ANNEAL_ITREE_DISABLE_MIRI").ok().as_deref() == Some("1");
    let require_miri = env::var("ANNEAL_ITREE_REQUIRE_MIRI").ok().as_deref() == Some("1")
        || (!disable_miri
            && (env::var_os("ANNEAL_ITREE_MIRI_TOOLCHAIN").is_some()
                || env::var_os("ANNEAL_ITREE_MIRI_BIN").is_some()));
    let miri = match MiriRunner::probe(&cache_root, rustc.sysroot.as_deref()) {
        MiriAvailability::Available(m) => Some(m),
        MiriAvailability::InvalidConfig { reason } => {
            panic!("invalid Miri configuration in corruption test: {reason}");
        }
        MiriAvailability::Unavailable { reason } => {
            if require_miri {
                eprintln!("Miri required in corruption test but unavailable: {reason}");
            }
            None
        }
    };
    if require_miri {
        assert!(miri.is_some());
    }

    let corrupt_src = r#"
pub fn probe_corruption(mode: u32) -> u32 {
    let caller_frame = std::cell::UnsafeCell::new(std::hint::black_box(
        anneal_rt::RootCallerFrame {
            tag: 0x11,
            magic: 0x2233_4455,
            flag: true,
            counter: 0x9988_7766_5544_3322,
        },
    ));
    let watched_buf = std::cell::UnsafeCell::new(std::hint::black_box([
        0x10u8, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
    ]));
    let _guard = unsafe {
        anneal_rt::ScopedCallerWatchGuard::install(
            caller_frame.get().cast_const(),
            watched_buf.get().cast::<u8>().cast_const(),
            8,
        )
    };
    anneal_rt::handle_scheduled_call("corrupting_callee", Vec::new(), Vec::new(), || {
        if mode == 1 {
            unsafe {
                (*caller_frame.get()).magic ^= 1;
            }
        } else if mode == 2 {
            unsafe {
                (*watched_buf.get())[3] ^= 0xFF;
            }
        }
        7u32
    })
}
"#;

    let mk_case = |id: &str, mode_arg: &str| TraceTestCase {
        id: id.to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: String::new(),
        traced_rust_source: Some(corrupt_src.to_string()),
        entry_fn: "probe_corruption".to_string(),
        rust_arg_exprs: vec![mode_arg.to_string()],
        lean_args: Vec::new(),
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: String::new(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 64,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    };

    // Mode 1: mutating caller_frame.magic flips locals_preserved to false.
    let case_local = mk_case("neg_corrupt_local", "1u32");
    let r_local = rustc.run_dual(&case_local);
    assert!(r_local.o0.tool_error.is_none(), "{:?}", r_local.o0);
    assert!(!r_local.o0.caller_frame_law.caller_locals_preserved);
    assert!(r_local.o0.caller_frame_law.untouched_alloc_bytes_preserved);
    assert_eq!(
        r_local.o0.spine.caller_frame_checks(),
        vec![
            ("corrupting_callee:return".to_string(), false, true, false),
            ("root_exit".to_string(), true, true, true),
        ]
    );
    if let Some(m) = &miri {
        let m_local = m.run_case(&case_local);
        assert!(m_local.tool_error.is_none(), "Miri Tree Borrows must stay clean: {m_local:?}");
        assert!(!m_local.caller_frame_law.caller_locals_preserved);
        assert_eq!(m_local.spine.caller_frame_checks(), r_local.o0.spine.caller_frame_checks());
        let v = classify_four_way(
            &r_local.o0,
            &r_local.o2,
            Some(&m_local),
            None,
            None,
            SpineCompareMode::ObsErasedCallsOnly,
            None,
        );
        assert!(matches!(v, TraceVerdict::UnsoundAccept { .. }), "{v:?}");
    }

    // Mode 2: mutating watched_buf[3] flips allocs_preserved to false.
    let case_alloc = mk_case("neg_corrupt_alloc", "2u32");
    let r_alloc = rustc.run_dual(&case_alloc);
    assert!(r_alloc.o0.tool_error.is_none(), "{:?}", r_alloc.o0);
    assert!(r_alloc.o0.caller_frame_law.caller_locals_preserved);
    assert!(!r_alloc.o0.caller_frame_law.untouched_alloc_bytes_preserved);
    assert_eq!(
        r_alloc.o0.spine.caller_frame_checks(),
        vec![
            ("corrupting_callee:return".to_string(), true, false, false),
            ("root_exit".to_string(), true, true, true),
        ]
    );
    if let Some(m) = &miri {
        let m_alloc = m.run_case(&case_alloc);
        assert!(m_alloc.tool_error.is_none(), "Miri Tree Borrows must stay clean: {m_alloc:?}");
        assert!(!m_alloc.caller_frame_law.untouched_alloc_bytes_preserved);
        assert_eq!(m_alloc.spine.caller_frame_checks(), r_alloc.o0.spine.caller_frame_checks());
    }
}

fn assert_agree_or_mir_eval_refused(
    report: &CaseReport,
    mir_eval_enabled: bool,
    spine_mode: SpineCompareMode,
    context: &str,
) {
    if mir_eval_enabled {
        assert!(
            matches!(
                report.verdict,
                TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
            ),
            "expected ConservativeOverApprox when mir_eval is active on {context}, got {:?}",
            report.verdict
        );
        assert!(
            report
                .mir_eval
                .as_ref()
                .is_some_and(|me| matches!(me.outcome, TerminalOutcome::CaptureRefused { .. })),
            "expected mir_eval CaptureRefused on {context}, got {:?}",
            report.mir_eval
        );
        let without_mir_eval = classify_four_way_with_ub_guard(
            &report.rustc_dual.o0,
            &report.rustc_dual.o2,
            report.rustc_dual.skipped_for_ub,
            report.miri.as_ref(),
            report.lean.as_ref(),
            None,
            spine_mode,
            None,
        );
        assert_eq!(
            without_mir_eval,
            TraceVerdict::Agree,
            "expected 3-way Agree without mir_eval on {context}, got {without_mir_eval:?}"
        );
    } else {
        assert_eq!(
            report.verdict,
            TraceVerdict::Agree,
            "expected full Agree on {context}, got {:?}",
            report.verdict
        );
    }
}

/// Live test verifying degraded trimmed-archive (`workspace-tests`) behavior
/// when Miri is unavailable:
/// 1. `require_miri: true` fails closed at `DifferentialEngine::prepare`.
/// 2. With `enable_miri: false`, `Agree` is NEVER emitted (`agree == 0`),
///    `degraded_no_miri > 0`, `expected_ub` cases skip host `rustc` execution,
///    and `unsound_accept == 0` / `tool_error == 0`.
#[test]
fn live_degraded_no_miri_mode_never_emits_agree_and_skips_host_ub() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");

    let mut strict_cfg = DifferentialConfig::for_workspace(anneal_root.clone());
    strict_cfg.enable_miri = false;
    strict_cfg.require_miri = true;
    assert!(
        DifferentialEngine::prepare(strict_cfg).is_err(),
        "require_miri must fail closed when Miri is disabled/unavailable"
    );

    let mut deg_cfg = DifferentialConfig::for_workspace(anneal_root);
    deg_cfg.enable_miri = false;
    deg_cfg.require_miri = false;
    let engine = DifferentialEngine::prepare(deg_cfg).expect("prepare degraded engine");
    assert!(engine.miri.is_none());

    let corpus = curated_corpus();
    let rep = engine.run_cases(&corpus);
    assert_eq!(rep.counts.agree, 0, "Degraded mode without Miri MUST NEVER emit Agree!");
    if engine.mir_eval.is_some() {
        // Non-CapturedRust defined-behavior cases classify as
        // ConservativeOverApprox when anneal-mir-eval is active, leaving the
        // CapturedRust + expected-UB cases as DegradedNoMiri.
        assert!(rep.counts.degraded_no_miri >= 14, "counts={:?}", rep.counts);
        for (spec, c) in corpus.iter().zip(&rep.cases) {
            if !matches!(spec.lean_program_spec, LeanProgramSpec::CapturedRust { .. })
                && !spec.is_expected_ub()
            {
                assert!(
                    matches!(
                        c.verdict,
                        TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
                    ),
                    "expected ConservativeOverApprox on {} with mir_eval active, got {:?}",
                    c.case_id,
                    c.verdict
                );
                let without_mir_eval = classify_four_way_with_ub_guard(
                    &c.rustc_dual.o0,
                    &c.rustc_dual.o2,
                    c.rustc_dual.skipped_for_ub,
                    c.miri.as_ref(),
                    c.lean.as_ref(),
                    None,
                    spec.spine_mode,
                    spec.disclosed_gap.as_ref(),
                );
                assert!(
                    matches!(without_mir_eval, TraceVerdict::DegradedNoMiri { .. }),
                    "expected DegradedNoMiri without mir_eval on {}, got {without_mir_eval:?}",
                    c.case_id
                );
            }
        }
    } else {
        assert!(rep.counts.degraded_no_miri >= 23, "counts={:?}", rep.counts);
    }
    assert_eq!(rep.counts.unsound_accept, 0);
    assert_eq!(rep.counts.undeclared_ub_fault, 0);
    assert_eq!(rep.counts.tool_error, 0);
    assert_eq!(rep.counts.expectation_mismatches, 0);
    assert!(!rep.has_critical_failures());

    for c in &rep.cases {
        if c.expected_class == anneal_itree_diff::spec::ExpectedCaseClass::UndefinedBehavior {
            assert!(
                c.rustc_dual.skipped_for_ub,
                "expected host rustc to be skipped on UB case {} in no-Miri mode",
                c.case_id
            );
        }
    }
}

/// Live end-to-end differential test over the full 33-case 6-category corpus.
/// Runs full 4-way Miri verification whenever Miri is present in the active
/// sysroot or configured via `ANNEAL_ITREE_MIRI_*` (asserting `0`
/// `degraded_no_miri` when `ANNEAL_ITREE_REQUIRE_MIRI=1`), and runs cleanly in
/// `DegradedNoMiri` mode inside trimmed omnibus archives lacking `bin/miri`.
#[test]
fn live_four_way_curated_corpus_end_to_end() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cfg = DifferentialConfig::for_workspace(anneal_root);
    let disable_miri = env::var("ANNEAL_ITREE_DISABLE_MIRI").ok().as_deref() == Some("1");
    let require_miri = cfg.require_miri
        || (!disable_miri
            && (env::var_os("ANNEAL_ITREE_MIRI_TOOLCHAIN").is_some()
                || env::var_os("ANNEAL_ITREE_MIRI_BIN").is_some()));
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");
    if require_miri {
        assert!(
            engine.miri.is_some(),
            "expected Miri to be active, got status: {}",
            engine.miri_status
        );
    }

    let corpus = curated_corpus();
    assert_eq!(corpus.len(), 33);
    let report = engine.run_cases(&corpus);

    for c in &report.cases {
        assert!(
            !c.verdict.is_critical_failure(),
            "CRITICAL failure on case {}: {}\n  rustc_O0={:?}\n  rustc_O2={:?}\n  miri={:?}\n  lean={:?}\n  strict={:?}\n  metamorphic={:?}",
            c.case_id,
            c.verdict,
            c.rustc_dual.o0,
            c.rustc_dual.o2,
            c.miri,
            c.lean,
            c.lean_strict_probe,
            c.metamorphic,
        );
    }

    assert_eq!(report.counts.unsound_accept, 0);
    assert_eq!(report.counts.undeclared_ub_fault, 0);
    assert_eq!(report.counts.tool_error, 0);
    assert_eq!(report.counts.expectation_mismatches, 0);
    assert!(!report.has_critical_failures());

    for (spec, c) in corpus.iter().zip(&report.cases) {
        // Verify non-constant 64-char SHA-256 mem_digest on Returned outcomes.
        if let TerminalOutcome::Returned { mem_digest, .. } = &c.rustc_dual.o0.outcome {
            assert_eq!(mem_digest.len(), 64);
            assert_ne!(mem_digest, "empty");
        }

        if engine.miri.is_some() {
            assert_eq!(report.counts.degraded_no_miri, 0);
            match c.category {
                CaseCategory::ScalarBitwise | CaseCategory::BranchLoopCfg => {
                    assert_eq!(
                        c.verdict,
                        TraceVerdict::Agree,
                        "expected full Agree on {} ({:?}), got {:?}",
                        c.case_id,
                        c.category,
                        c.verdict
                    );
                }
                CaseCategory::MultiCallChain | CaseCategory::MetamorphicInliningDuality => {
                    assert_agree_or_mir_eval_refused(
                        c,
                        engine.mir_eval.is_some(),
                        spec.spine_mode,
                        &c.case_id,
                    );
                }
                _ => {}
            }
        } else {
            assert_eq!(report.counts.agree, 0);
        }

        if matches!(
            c.category,
            CaseCategory::MultiCallChain | CaseCategory::MetamorphicInliningDuality
        ) {
            let strict = c
                .lean_strict_probe
                .as_ref()
                .expect("expected strict verbatim conservative probe on multi-call case");
            if spec.requires_strict_refusal() {
                assert!(
                    matches!(strict.outcome, TerminalOutcome::CaptureRefused { .. }),
                    "expected strict verbatim Mode (a) to conservatively fault .unsupported on {}, got {:?}",
                    c.case_id,
                    strict.outcome
                );
            } else {
                let primary = c.lean.as_ref().expect("expected primary Lean result");
                assert!(
                    strict.outcome.semantically_eq(&primary.outcome),
                    "expected strict verbatim Mode (a) to match intra-crate call outcome on {}: {:?} vs {:?}",
                    c.case_id,
                    strict.outcome,
                    primary.outcome
                );
            }
        }

        if c.category == CaseCategory::BranchLoopCfg {
            let lean_res = c.lean.as_ref().expect("expected Lean result");
            assert!(
                !lean_res.spine.branch_tags().is_empty(),
                "expected non-empty switchInt BranchTag events on {}",
                c.case_id
            );
            assert_eq!(
                c.rustc_dual.o0.spine.branch_tags(),
                lean_res.spine.branch_tags(),
                "FullBranchesAndCalls BranchTag mismatch on {}",
                c.case_id
            );
        }
    }

    assert_eq!(report.counts.metamorphic_checked, 5);
    assert_eq!(report.counts.metamorphic_passed, 5);

    let find_pair = |id: &str| {
        corpus
            .iter()
            .zip(&report.cases)
            .find(|(spec, _)| spec.id == id)
            .unwrap_or_else(|| panic!("missing corpus case {id}"))
    };
    let find = |id: &str| find_pair(id).1;
    if engine.miri.is_some() {
        assert!(find("cat6_unreachable_ub").rustc_dual.skipped_for_ub);
        assert!(find("cat6_mir_unreachable_ub").rustc_dual.skipped_for_ub);
        assert!(find("cat6_shift_overflow_ub").rustc_dual.skipped_for_ub);
        assert!(matches!(
            find("cat6_unreachable_ub").verdict,
            TraceVerdict::ConservativeOverApprox {
                ub_refutation_disallowed: true,
                undeclared_ub_fault: false,
                ..
            }
        ));
        for id in [
            "cat6_mir_unreachable_ub",
            "cat6_shift_overflow_ub",
            "cat4_scheduled_abort_no_drop",
            "cat4_scheduled_return_bytes_override",
            "cat4_scheduled_invalid_bool_return_ub",
        ] {
            let (spec, rep) = find_pair(id);
            assert_agree_or_mir_eval_refused(rep, engine.mir_eval.is_some(), spec.spine_mode, id);
        }
    }
    assert!(matches!(
        find("cat6_div_by_zero_probe").verdict,
        TraceVerdict::ConservativeOverApprox {
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
            ..
        }
    ));
    assert!(matches!(
        find("cat6_oob_index_probe").verdict,
        TraceVerdict::ConservativeOverApprox {
            ub_refutation_disallowed: true,
            undeclared_ub_fault: false,
            ..
        }
    ));
    assert!(matches!(
        find("cat6_caller_raw_ptr_aliasing_gap").verdict,
        TraceVerdict::DisclosedGapArtifact { gap: DisclosedGapKind::CallerRawPtrAliasing, .. }
    ));
}

/// Live end-to-end differential fuzzing test executing 12 deterministically
/// generated multi-call programs (exercising all 5 mutators + full-authority
/// source-inlined metamorphic duality + caller-frame preservation).
#[test]
fn live_four_way_deterministic_fuzz_batch_end_to_end() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cfg = DifferentialConfig::for_workspace(anneal_root);
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");

    let report = engine.run_fuzz_campaign(0xA11E_2026, 12);
    assert_eq!(report.counts.total, 12);
    assert_eq!(report.counts.unsound_accept, 0);
    assert_eq!(report.counts.undeclared_ub_fault, 0);
    assert_eq!(report.counts.tool_error, 0);
    assert_eq!(report.counts.expectation_mismatches, 0);
    assert!(!report.has_critical_failures());

    if engine.mir_eval.is_some() {
        assert_eq!(report.counts.agree, 0);
        assert_eq!(report.counts.degraded_no_miri, 0);
        assert_eq!(report.counts.conservative_over_approx, 12);
        for c in &report.cases {
            assert!(
                c.mir_eval.as_ref().is_some_and(|me| {
                    matches!(me.outcome, TerminalOutcome::CaptureRefused { .. })
                }),
                "expected mir_eval CaptureRefused on {}, got {:?}",
                c.case_id,
                c.mir_eval
            );
            let without_mir_eval = classify_four_way_with_ub_guard(
                &c.rustc_dual.o0,
                &c.rustc_dual.o2,
                c.rustc_dual.skipped_for_ub,
                c.miri.as_ref(),
                c.lean.as_ref(),
                None,
                SpineCompareMode::ObsErasedCallsOnly,
                None,
            );
            if engine.miri.is_some() {
                assert_eq!(
                    without_mir_eval,
                    TraceVerdict::Agree,
                    "expected 3-way Agree without mir_eval on {}, got {without_mir_eval:?}",
                    c.case_id
                );
            } else {
                assert!(
                    matches!(without_mir_eval, TraceVerdict::DegradedNoMiri { .. }),
                    "expected DegradedNoMiri without mir_eval on {}, got {without_mir_eval:?}",
                    c.case_id
                );
            }
        }
    } else if engine.miri.is_some() {
        assert_eq!(report.counts.agree, 12);
        assert_eq!(report.counts.degraded_no_miri, 0);
    } else {
        assert_eq!(report.counts.agree, 0);
        assert_eq!(report.counts.degraded_no_miri, 12);
    }
    assert!(report.counts.metamorphic_checked >= 8);
    assert_eq!(report.counts.metamorphic_passed, report.counts.metamorphic_checked);
}

#[test]
fn non_monotonic_scalar_shrinker_finds_smaller_witness_across_false_midpoint() {
    // Non-monotonic point-set predicate: true at 10 and 100, false at 50 and
    // false on 0..=9.
    let point_pred = |v: u32| v == 10 || v == 100;
    assert!(!point_pred(50));
    assert!((0..10).all(|v| !point_pred(v)));
    assert_eq!(shrink_u32_non_monotonic(100, point_pred), 10);

    // Non-monotonic two-island predicate: true on 10..=18 and 82..=100, false
    // at 50 and on 0..=9.
    let island_pred = |v: u32| (10..=18).contains(&v) || (82..=100).contains(&v);
    assert!(!island_pred(50));
    assert_eq!(shrink_u32_non_monotonic(100, island_pred), 10);

    // Signed i32 non-monotonic narrowing: prefers +10 over -100 even when -50
    // and 0..=9 return false.
    let signed_pred = |v: i32| v == 10 || v == -10 || v == -100;
    assert!(!signed_pred(-50) && !signed_pred(50) && !signed_pred(0));
    assert_eq!(shrink_i32_non_monotonic(-100, signed_pred), 10);
    assert_eq!(shrink_i32_non_monotonic(-100, |v| v == -1 || v == -100), -1);

    // Full FuzzProgram shrinker starting from input_x = 100 where input_x == 50
    // returns false and 0..=9 return false.
    let mut prog = generate_fuzz_batch(0x2468_ACE0, 2)[0].clone();
    prog.input_x = 100;
    prog.input_y = 64;
    prog.steps =
        vec![FuzzStep::ArithImm { op: anneal_itree_diff::fuzzer::FuzzArithOp::Add, imm: 100 }];
    let res = shrink_fuzz_program(&prog, |p| {
        let imm_ok = p.steps.iter().any(|s| {
            matches!(
                s,
                FuzzStep::ArithImm { imm, .. } if *imm == 10 || *imm == 100
            )
        });
        (p.input_x == 10 || p.input_x == 100) && imm_ok
    });
    assert!(res.succeeded && res.is_one_minimal && !res.budget_exhausted);
    assert_eq!(res.minimized.input_x, 10);
    assert_eq!(res.minimized.input_y, 0);
    assert_eq!(
        res.minimized.steps,
        vec![FuzzStep::ArithImm { op: anneal_itree_diff::fuzzer::FuzzArithOp::Add, imm: 10 }]
    );
}

#[test]
fn metamorphic_conservative_lean_twins_count_as_skipped_never_passed() {
    let digest = compute_boundary_mem_digest(&[vec![Some(11), Some(0), Some(0), Some(0)]]);
    let mk_leg = |auth: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let ret11 = TerminalOutcome::Returned { ret: TraceVal::u32(11), mem_digest: digest };
    let rustc_ok = RustcDualResult {
        o0: mk_leg("rustc-O0", ret11.clone()),
        o2: mk_leg("rustc-O2", ret11.clone()),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };
    let miri_ok = mk_leg("miri", ret11.clone());
    let lean_ok = mk_leg("lean-compositional", ret11.clone());
    let lean_refused = mk_leg(
        "lean-strict",
        TerminalOutcome::CaptureRefused { reason: "unsupported construct".to_string() },
    );
    let lean_diverged = mk_leg("lean-strict", TerminalOutcome::Diverged { fuel: 64 });

    let rec_refused = evaluate_metamorphic_duality(
        &rustc_ok,
        Some(&miri_ok),
        &lean_ok,
        &rustc_ok,
        Some(&miri_ok),
        lean_refused,
    );
    assert!(
        matches!(rec_refused.status, MetamorphicStatus::SkippedConservative { .. }),
        "{rec_refused:?}"
    );
    assert!(!rec_refused.duality_holds);

    let rec_diverged = evaluate_metamorphic_duality(
        &rustc_ok,
        Some(&miri_ok),
        &lean_ok,
        &rustc_ok,
        Some(&miri_ok),
        lean_diverged,
    );
    assert!(
        matches!(rec_diverged.status, MetamorphicStatus::SkippedConservative { .. }),
        "{rec_diverged:?}"
    );
    assert!(!rec_diverged.duality_holds);

    let case_rep = CaseReport {
        case_id: "conservative_twin_case".to_string(),
        category: CaseCategory::MetamorphicInliningDuality,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::Agree,
        expectation_violation: None,
        rustc_dual: rustc_ok.clone(),
        miri: Some(miri_ok.clone()),
        lean: Some(lean_ok.clone()),
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: Some(rec_refused),
    };
    let report = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![case_rep],
        Vec::new(),
    );
    assert_eq!(report.counts.metamorphic_checked, 1);
    assert_eq!(report.counts.metamorphic_passed, 0);
    assert_eq!(report.counts.metamorphic_skipped, 1);
    assert!(!report.has_critical_failures());

    // Also verify DegradedNoLean aggregation in DifferentialReport.
    let no_lean_case = CaseReport {
        case_id: "degraded_no_lean_case".to_string(),
        category: CaseCategory::ScalarBitwise,
        expected_class: ExpectedCaseClass::Agree,
        verdict: TraceVerdict::DegradedNoLean { detail: "lean disabled".to_string() },
        expectation_violation: None,
        rustc_dual: rustc_ok,
        miri: Some(miri_ok),
        lean: None,
        lean_strict_probe: None,
        mir_eval: None,
        metamorphic: None,
    };
    let no_lean_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![no_lean_case],
        Vec::new(),
    );
    assert_eq!(no_lean_rep.counts.agree, 0);
    assert_eq!(no_lean_rep.counts.degraded_no_lean, 1);
    assert!(!no_lean_rep.has_critical_failures());
}

#[test]
fn trace_json_rejects_omitted_caller_frame_preservation_fields_as_tool_error() {
    let valid_rust = r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"allocs_preserved":true,"preserved":true}]}"#;
    assert!(
        parse_rustc_run_output("rustc-O0", Some(0), None, valid_rust, "", 1).tool_error.is_none()
    );

    let rust_missing_cases = [
        // Missing caller_locals_preserved
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Missing untouched_alloc_bytes_preserved
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Missing padding_mask_respected
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"violations":[],"events":[]}"#,
        // CallerFrameCheck missing locals_preserved
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","allocs_preserved":true,"preserved":true}]}"#,
        // CallerFrameCheck missing allocs_preserved
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"preserved":true}]}"#,
        // CallerFrameCheck missing preserved
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"allocs_preserved":true}]}"#,
    ];
    for line in rust_missing_cases {
        let host_res = parse_rustc_run_output("rustc-O0", Some(0), None, line, "", 1);
        assert!(host_res.tool_error.is_some(), "expected Rust ToolError for: {line}");
        let miri_res = parse_miri_run_output("miri", Some(0), None, line, "", 1);
        assert!(miri_res.tool_error.is_some(), "expected Miri ToolError for: {line}");
    }

    let valid_lean = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"allocs_preserved":true,"preserved":true}]}"#;
    assert!(parse_lean_trace_output("lean", valid_lean, "", 1).tool_error.is_none());

    let lean_missing_cases = [
        // Missing caller_locals_preserved
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Missing untouched_alloc_bytes_preserved
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Missing padding_mask_respected
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"violations":[],"events":[]}"#,
        // CallerFrameCheck missing locals_preserved
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","allocs_preserved":true,"preserved":true}]}"#,
        // CallerFrameCheck missing allocs_preserved
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"preserved":true}]}"#,
        // CallerFrameCheck missing preserved
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"caller_frame_check","point":"root_exit","locals_preserved":true,"allocs_preserved":true}]}"#,
    ];
    for line in lean_missing_cases {
        let lean_res = parse_lean_trace_output("lean", line, "", 1);
        assert!(lean_res.tool_error.is_some(), "expected Lean ToolError for: {line}");
    }
}

#[cfg(unix)]
#[test]
fn miri_sysroot_identity_tracks_binaries_and_rust_src_and_validates_stamp() {
    let tmp = tempfile::tempdir().unwrap();
    let sr = tmp.path().join("mock_sysroot");
    let bin_dir = sr.join("bin");
    let lib_dir = sr.join("lib");
    let rust_src = sr.join("lib/rustlib/src/rust");
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(&lib_dir).unwrap();
    fs::create_dir_all(rust_src.join("library/core/src/num")).unwrap();
    fs::create_dir_all(rust_src.join("library/alloc/src")).unwrap();
    fs::create_dir_all(rust_src.join("library/vendor/cfg-if")).unwrap();

    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    let rustc_bin = bin_dir.join("rustc");
    let miri_bin = bin_dir.join("miri");
    let cargo_bin = bin_dir.join("cargo");
    let cargo_miri_bin = bin_dir.join("cargo-miri");
    let host_driver_so = lib_dir.join("librustc_driver-mock.so");
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {mock_host}\\n'\n"
        ),
    );
    write_exec(&miri_bin, "#!/usr/bin/env bash\nprintf 'miri 0.1.0 (mock-a 2026-05-30)\\n'\n");
    write_exec(&cargo_bin, "#!/usr/bin/env bash\nprintf 'cargo 1.98.0\\n'\n");
    write_exec(&cargo_miri_bin, "#!/usr/bin/env bash\n# cargo-miri v1\nexit 0\n");
    fs::write(&host_driver_so, b"rustc-driver-v1").unwrap();

    let lock_path = rust_src.join("library/Cargo.lock");
    let core_toml = rust_src.join("library/core/Cargo.toml");
    let alloc_toml = rust_src.join("library/alloc/Cargo.toml");
    let core_num_mod = rust_src.join("library/core/src/num/mod.rs");
    fs::write(&lock_path, "version = 4\n# lock-a\n").unwrap();
    fs::write(&core_toml, "[package]\nname = \"core\"\nversion = \"0.0.0\"\n").unwrap();
    fs::write(&alloc_toml, "[package]\nname = \"alloc\"\nversion = \"0.0.0\"\n").unwrap();
    fs::write(rust_src.join("library/core/src/lib.rs"), "pub mod num;\n").unwrap();
    fs::write(&core_num_mod, "// core::num v1\npub const MAGIC: u32 = 1;\n").unwrap();
    fs::write(rust_src.join("library/vendor/cfg-if/.cargo-checksum.json"), "{\"files\":{}}\n")
        .unwrap();

    let id_base = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin))
        .expect("compute initial MiriSysrootIdentity");
    let stamp_path = tmp.path().join(".anneal-itree-miri-ready");
    id_base.write_ready_stamp(&stamp_path).unwrap();
    assert!(id_base.validate_ready_stamp(&stamp_path));

    // Legacy plain-text stamp must fail validation.
    let legacy_stamp = tmp.path().join(".legacy-ready");
    fs::write(&legacy_stamp, "nightly:0123456789abcdef\n").unwrap();
    assert!(!id_base.validate_ready_stamp(&legacy_stamp));

    // 1. Changing miri binary bytes (even with identical --version output)
    //    changes the composite key and invalidates the ready stamp!
    write_exec(
        &miri_bin,
        "#!/usr/bin/env bash\n# rebuilt miri binary bytes\nprintf 'miri 0.1.0 (mock-a 2026-05-30)\\n'\n",
    );
    let id_miri_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_base.miri_bin_sha256, id_miri_changed.miri_bin_sha256);
    assert_ne!(id_base.cache_dir_tag(), id_miri_changed.cache_dir_tag());
    assert!(!id_miri_changed.validate_ready_stamp(&stamp_path));

    // 2. Changing cargo-miri or cargo binary bytes changes the composite key
    //    and invalidates `.anneal-itree-miri-ready`!
    id_miri_changed.write_ready_stamp(&stamp_path).unwrap();
    write_exec(&cargo_miri_bin, "#!/usr/bin/env bash\n# cargo-miri v2\nexit 0\n");
    let id_cm_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_miri_changed.cargo_miri_bin_sha256, id_cm_changed.cargo_miri_bin_sha256);
    assert_ne!(id_miri_changed.composite_sha256, id_cm_changed.composite_sha256);
    assert!(!id_cm_changed.validate_ready_stamp(&stamp_path));

    id_cm_changed.write_ready_stamp(&stamp_path).unwrap();
    write_exec(&cargo_bin, "#!/usr/bin/env bash\nprintf 'cargo 1.98.0-rebuilt\\n'\n");
    let id_cargo_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_cm_changed.cargo_bin_sha256, id_cargo_changed.cargo_bin_sha256);
    assert_ne!(id_cm_changed.composite_sha256, id_cargo_changed.composite_sha256);
    assert!(!id_cargo_changed.validate_ready_stamp(&stamp_path));

    // 3. Mutating ONLY a nested `rust-src` implementation file
    //    (`library/core/src/num/mod.rs`) while keeping `Cargo.toml`,
    //    `Cargo.lock`, and `src/lib.rs` unchanged MUST change `rust_src_sha256`
    //    and invalidate `.anneal-itree-miri-ready`!
    id_cargo_changed.write_ready_stamp(&stamp_path).unwrap();
    fs::write(&core_num_mod, "// core::num v2\npub const MAGIC: u32 = 2;\n").unwrap();
    let id_nested_src_changed =
        MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_cargo_changed.rust_src_sha256, id_nested_src_changed.rust_src_sha256);
    assert_ne!(id_cargo_changed.cache_dir_tag(), id_nested_src_changed.cache_dir_tag());
    assert!(!id_nested_src_changed.validate_ready_stamp(&stamp_path));

    // 4. Mutating `bin/rustc` bytes (with identical `-vV` stdout) OR mutating
    //    host `lib/librustc_driver-mock.so` changes `MiriSysrootIdentity` and
    //    invalidates `.anneal-itree-miri-ready`!
    id_nested_src_changed.write_ready_stamp(&stamp_path).unwrap();
    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\n# rebuilt rustc binary bytes\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {mock_host}\\n'\n"
        ),
    );
    let id_rustc_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_nested_src_changed.rustc_bin_sha256, id_rustc_changed.rustc_bin_sha256);
    assert_ne!(id_nested_src_changed.cache_dir_tag(), id_rustc_changed.cache_dir_tag());
    assert!(!id_rustc_changed.validate_ready_stamp(&stamp_path));

    id_rustc_changed.write_ready_stamp(&stamp_path).unwrap();
    fs::write(&host_driver_so, b"rustc-driver-v2-patched").unwrap();
    let id_driver_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_rustc_changed.rustc_host_libs_sha256, id_driver_changed.rustc_host_libs_sha256);
    assert_ne!(id_rustc_changed.cache_dir_tag(), id_driver_changed.cache_dir_tag());
    assert!(!id_driver_changed.validate_ready_stamp(&stamp_path));

    // 5. Changing rust-src setup manifests/lockfiles invalidates the stamp.
    id_driver_changed.write_ready_stamp(&stamp_path).unwrap();
    fs::write(&lock_path, "version = 4\n# lock-b\n").unwrap();
    let id_lock_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_driver_changed.rust_src_sha256, id_lock_changed.rust_src_sha256);
    assert!(!id_lock_changed.validate_ready_stamp(&stamp_path));

    fs::write(&core_toml, "[package]\nname = \"core\"\nversion = \"0.0.1\"\n").unwrap();
    let id_core_changed = MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).unwrap();
    assert_ne!(id_lock_changed.rust_src_sha256, id_core_changed.rust_src_sha256);

    // 6. Symlink escaping canonical `rust-src` root must fail closed.
    let outside_file = tmp.path().join("outside_secret.rs");
    fs::write(&outside_file, "// outside\n").unwrap();
    let escape_link = rust_src.join("library/core/src/escaped.rs");
    std::os::unix::fs::symlink(&outside_file, &escape_link).unwrap();
    assert!(MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).is_err());
    fs::remove_file(&escape_link).unwrap();

    // 7. External `cargo_bin` and `miri_bin` sibling directories follow the
    //    exact setup search-directory precedence (`cargo_bin` dir -> `miri_bin`
    //    dir -> `<sysroot>/bin` -> `PATH`) used to locate and invoke
    //    `cargo-miri` during offline sysroot setup.
    let ext_cargo_dir = tmp.path().join("ext_cargo_bin");
    let ext_miri_dir = tmp.path().join("ext_miri_bin");
    fs::create_dir_all(&ext_cargo_dir).unwrap();
    fs::create_dir_all(&ext_miri_dir).unwrap();
    let ext_cargo = ext_cargo_dir.join("cargo");
    let ext_miri = ext_miri_dir.join("miri");
    let ext_cm_cargo = ext_cargo_dir.join("cargo-miri");
    let ext_cm_miri = ext_miri_dir.join("cargo-miri");
    write_exec(&ext_cargo, "#!/usr/bin/env bash\nprintf 'cargo ext\\n'\n");
    write_exec(&ext_miri, "#!/usr/bin/env bash\nprintf 'miri ext\\n'\n");
    write_exec(&ext_cm_miri, "#!/usr/bin/env bash\n# miri-sibling cargo-miri\nexit 0\n");
    let dirs = miri_setup_search_dirs(&sr, &ext_miri, Some(&ext_cargo), None);
    assert_eq!(dirs, vec![ext_cargo_dir.clone(), ext_miri_dir.clone(), bin_dir.clone()]);
    assert_eq!(
        resolve_cargo_miri_binary_with_path_and_suffix(&sr, &ext_miri, Some(&ext_cargo), None, ""),
        Some(fs::canonicalize(&ext_cm_miri).unwrap())
    );
    write_exec(&ext_cm_cargo, "#!/usr/bin/env bash\n# cargo-sibling cargo-miri\nexit 0\n");
    assert_eq!(
        resolve_cargo_miri_binary_with_path_and_suffix(&sr, &ext_miri, Some(&ext_cargo), None, ""),
        Some(fs::canonicalize(&ext_cm_cargo).unwrap())
    );
    let id_ext_a = MiriSysrootIdentity::compute(&sr, &ext_miri, Some(&ext_cargo)).unwrap();
    write_exec(&ext_cm_cargo, "#!/usr/bin/env bash\n# cargo-sibling cargo-miri v2\nexit 0\n");
    let id_ext_b = MiriSysrootIdentity::compute(&sr, &ext_miri, Some(&ext_cargo)).unwrap();
    assert_ne!(id_ext_a.cargo_miri_bin_sha256, id_ext_b.cargo_miri_bin_sha256);

    // 8. Missing required rust-src manifest fails closed.
    fs::remove_file(&alloc_toml).unwrap();
    assert!(MiriSysrootIdentity::compute(&sr, &miri_bin, Some(&cargo_bin)).is_err());
}

#[test]
fn disclosed_gap_requires_matching_boundary_marker_and_rejects_unrelated_ub() {
    let digest = compute_boundary_mem_digest(&[vec![Some(1), Some(0), Some(0), Some(0)]]);
    let mk = |auth: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let ok_ret = TerminalOutcome::Returned { ret: TraceVal::usize_val(1), mem_digest: digest };
    let ptr_gap = DisclosedGapSpec::new(
        DisclosedGapKind::CallerRawPtrAliasing,
        "unsupported type: *const u32",
    );

    // 1. Matching raw-pointer boundary capture refusal is admitted as
    //    DisclosedGapArtifact.
    let v_match = classify_four_way(
        &mk("rustc-O0", ok_ret.clone()),
        &mk("rustc-O2", ok_ret.clone()),
        Some(&mk("miri", ok_ret.clone())),
        Some(&mk(
            "lean",
            TerminalOutcome::CaptureRefused {
                reason: "1 required obligations are unsupported | unsupported=[{\"reason\":\"unsupported type: *const u32\"}]"
                    .to_string(),
            },
        )),
        None,
        SpineCompareMode::OutcomeOnly,
        Some(&ptr_gap),
    );
    assert!(matches!(
        v_match,
        TraceVerdict::DisclosedGapArtifact { gap: DisclosedGapKind::CallerRawPtrAliasing, .. }
    ));
    assert!(!v_match.is_critical_failure());

    // 2. Unrelated Lean `.undefined` faults on a case carrying
    //    `CallerRawPtrAliasing` MUST NOT be exempted as DisclosedGapArtifact
    //    and instead fail closed with `undeclared_ub_fault: true`!
    for unrelated_ub in [
        "arithmetic overflow",
        "division by zero",
        "uninitialized return",
        "unreachable executed",
        "Trusted.MirSemantics.FaultKind.undefined",
        "unsupported type: *const u32; arithmetic overflow",
    ] {
        let v_unrelated = classify_four_way(
            &mk("rustc-O0", ok_ret.clone()),
            &mk("rustc-O2", ok_ret.clone()),
            Some(&mk("miri", ok_ret.clone())),
            Some(&mk("lean", TerminalOutcome::FaultUb { detail: unrelated_ub.to_string() })),
            None,
            SpineCompareMode::OutcomeOnly,
            Some(&ptr_gap),
        );
        assert!(
            matches!(
                v_unrelated,
                TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: true, .. }
            ),
            "expected undeclared_ub_fault: true for {unrelated_ub:?}, got {v_unrelated:?}"
        );
        assert!(v_unrelated.is_critical_failure());
    }
}

#[cfg(unix)]
#[test]
fn rustc_runner_rejects_toolchain_sysroot_skew_and_missing_sysroot_compiler() {
    let tmp = tempfile::tempdir().unwrap();
    let lean_sr = tmp.path().join("lean_sysroot");
    let other_sr = tmp.path().join("other_sysroot");
    let missing_bin_sr = tmp.path().join("missing_bin_sysroot");
    let path_dir = tmp.path().join("path_bin");
    fs::create_dir_all(lean_sr.join("bin")).unwrap();
    fs::create_dir_all(lean_sr.join("lib")).unwrap();
    fs::create_dir_all(other_sr.join("bin")).unwrap();
    fs::create_dir_all(other_sr.join("lib")).unwrap();
    fs::create_dir_all(missing_bin_sr.join("lib")).unwrap();
    fs::create_dir_all(&path_dir).unwrap();

    let canon_lean_sr = fs::canonicalize(&lean_sr).unwrap();
    let canon_other_sr = fs::canonicalize(&other_sr).unwrap();

    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    let write_mock_rustc = |bin_path: &std::path::Path, reported_sr: &std::path::Path| {
        let script = format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nif [[ \"$*\" == *\"-vV\"* ]]; then\n  printf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {}\\n'\n  exit 0\nfi\nexit 1\n",
            reported_sr.display(),
            mock_host,
        );
        fs::write(bin_path, script).unwrap();
        let mut perms = fs::metadata(bin_path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(bin_path, perms).unwrap();
    };

    let lean_rustc = lean_sr.join("bin/rustc");
    let other_rustc = other_sr.join("bin/rustc");
    let wrapper_rustc = path_dir.join("rustc");
    write_mock_rustc(&lean_rustc, &canon_lean_sr);
    write_mock_rustc(&other_rustc, &canon_other_sr);
    write_mock_rustc(&wrapper_rustc, &canon_other_sr);

    assert_eq!(query_rustc_sysroot(&wrapper_rustc).unwrap(), canon_other_sr);

    // 1. Explicit ANNEAL_ITREE_RUSTC or RUSTC pointing at a mismatched sysroot
    //    must fail closed with a clear version-skew error.
    for key in ["ANNEAL_ITREE_RUSTC", "RUSTC"] {
        let skew_err = RustcRunner::discover_with_env(Some(&lean_sr), |k| {
            if k == key { Some(other_rustc.as_os_str().to_os_string()) } else { None }
        })
        .expect_err("mismatched explicit rustc must be rejected");
        assert!(skew_err.contains("toolchain version skew"), "got: {skew_err}");
    }

    // 2. Direct `<lean_sr>/bin/rustc` is accepted, while an external wrapper
    //    script claiming `canon_lean_sr` without being the pinned sysroot
    //    compiler MUST fail closed so capture and rustc cannot diverge.
    let ok_explicit = RustcRunner::discover_with_env(Some(&lean_sr), |k| {
        if k == "ANNEAL_ITREE_RUSTC" { Some(lean_rustc.as_os_str().to_os_string()) } else { None }
    })
    .expect("matching explicit sysroot rustc must succeed");
    assert_eq!(ok_explicit.sysroot.as_deref(), Some(canon_lean_sr.as_path()));

    let sneaky_wrapper = path_dir.join("sneaky-rustc-wrapper");
    write_mock_rustc(&sneaky_wrapper, &canon_lean_sr);
    for key in ["ANNEAL_ITREE_RUSTC", "RUSTC"] {
        let wrap_err = RustcRunner::discover_with_env(Some(&lean_sr), |k| {
            if k == key { Some(sneaky_wrapper.as_os_str().to_os_string()) } else { None }
        })
        .expect_err("external wrapper claiming Lean sysroot must fail closed");
        assert!(wrap_err.contains("toolchain compiler mismatch"), "got: {wrap_err}");
    }

    // 3. When `expected_sysroot` is provided without env overrides, missing
    //    `<sysroot>/bin/rustc` MUST fail closed rather than silently falling
    //    through to an unrelated compiler on `PATH`.
    let missing_err = RustcRunner::discover_with_env(Some(&missing_bin_sr), |k| {
        if k == "PATH" { Some(path_dir.as_os_str().to_os_string()) } else { None }
    })
    .expect_err("missing sysroot bin/rustc must not fall back to PATH");
    assert!(missing_err.contains("missing `bin/rustc`"), "got: {missing_err}");

    // 4. In `--no-lean` mode (`expected_sysroot == None`), PATH `rustc` queries
    //    `--print sysroot` so downstream authorities share its exact sysroot.
    let path_runner = RustcRunner::discover_with_env(None, |k| {
        if k == "PATH" { Some(path_dir.as_os_str().to_os_string()) } else { None }
    })
    .expect("PATH rustc discovery when expected_sysroot is None");
    assert_eq!(path_runner.sysroot.as_deref(), Some(canon_other_sr.as_path()));

    // 5. When `PATH` or `RUSTC` points at a `rustup` multicall proxy symlink
    //    (`rustc -> rustup`), `discover` pins `rustc_bin` directly to
    //    `<sysroot>/bin/rustc` so clean-env subprocesses never drift to a
    //    different default toolchain.
    let proxy_dir = tmp.path().join("rustup_proxy_bin");
    fs::create_dir_all(&proxy_dir).unwrap();
    let mock_rustup = proxy_dir.join("rustup");
    write_mock_rustc(&mock_rustup, &canon_other_sr);
    let proxy_rustc = proxy_dir.join("rustc");
    std::os::unix::fs::symlink(&mock_rustup, &proxy_rustc).unwrap();
    let proxy_runner = RustcRunner::discover_with_env(None, |k| {
        if k == "PATH" { Some(proxy_dir.as_os_str().to_os_string()) } else { None }
    })
    .expect("rustup proxy discovery");
    assert_eq!(proxy_runner.sysroot.as_deref(), Some(canon_other_sr.as_path()));
    assert_eq!(proxy_runner.rustc_bin, fs::canonicalize(&other_rustc).unwrap());

    // 6. Bare `RUSTC=rustc` or `ANNEAL_ITREE_RUSTC=rustc` overrides resolve
    //    through `PATH` rather than failing on the current directory.
    let bare_rustc_runner = RustcRunner::discover_with_env(None, |k| match k {
        "RUSTC" => Some(std::ffi::OsString::from("rustc")),
        "PATH" => Some(proxy_dir.as_os_str().to_os_string()),
        _ => None,
    })
    .expect("bare RUSTC=rustc resolved via PATH");
    assert_eq!(bare_rustc_runner.rustc_bin, fs::canonicalize(&other_rustc).unwrap());
    assert!(
        resolve_explicit_or_path_exe_with_suffix(
            std::ffi::OsStr::new("rustc"),
            Some(proxy_dir.as_os_str()),
            ""
        )
        .is_some()
    );

    // 7. Capture build target directory tag changes whenever the sysroot
    //    digest or Cargo binary digest changes in place, and dynamic-library
    //    path selection uses the platform loader variable.
    let tag_a = compute_capture_build_dir_tag("sysroot_sha_v1", "cargo_sha_v1");
    let tag_b = compute_capture_build_dir_tag("sysroot_sha_v2", "cargo_sha_v1");
    let tag_c = compute_capture_build_dir_tag("sysroot_sha_v1", "cargo_sha_v2");
    assert_ne!(tag_a, tag_b);
    assert_ne!(tag_a, tag_c);
    if cfg!(target_os = "macos") {
        assert_eq!(DYLIB_PATH_ENV_VAR, "DYLD_LIBRARY_PATH");
    } else {
        assert_eq!(DYLIB_PATH_ENV_VAR, "LD_LIBRARY_PATH");
    }
    let joined_dylib =
        join_dylib_path_with_existing(&canon_other_sr.join("lib"), Some(proxy_dir.as_os_str()));
    let split_dylib: Vec<_> = env::split_paths(&joined_dylib).collect();
    assert_eq!(split_dylib, vec![canon_other_sr.join("lib"), proxy_dir.clone()]);

    // Prepending `<rust_sysroot>/bin` to child `PATH` ensures Windows and
    // Unix subprocesses find selected compiler DLLs ahead of ambient PATH.
    let joined_child_path =
        join_path_list_with_existing(&canon_other_sr.join("bin"), Some(proxy_dir.as_os_str()))
            .expect("join child PATH");
    let split_child_path: Vec<_> = env::split_paths(&joined_child_path).collect();
    assert_eq!(split_child_path, vec![canon_other_sr.join("bin"), proxy_dir]);
    let joined_empty_existing =
        join_path_list_with_existing(&canon_other_sr.join("bin"), Some(std::ffi::OsStr::new("")))
            .expect("join child PATH with empty existing");
    assert_eq!(
        env::split_paths(&joined_empty_existing).collect::<Vec<_>>(),
        vec![canon_other_sr.join("bin")]
    );
}

#[test]
fn shrink_witness_recomputes_minimized_verdict_and_preserves_original_verdict() {
    let mut initial = generate_fuzz_batch(0x9988_7766, 2)[0].clone();
    initial.input_x = 100;
    initial.input_y = 50;
    initial.steps = vec![
        FuzzStep::ArithImm { op: anneal_itree_diff::fuzzer::FuzzArithOp::Add, imm: 7 },
        FuzzStep::BranchMix { then_imm: 3, else_imm: 5 },
    ];

    let mk_report = |prog: &anneal_itree_diff::fuzzer::FuzzProgram, verdict: TraceVerdict| {
        let digest =
            compute_boundary_mem_digest(&[vec![Some(0x10), Some(0), Some(0), Some(0), Some(0)]]);
        let leg_ref = AuthorityRunResult {
            authority: "miri".to_string(),
            outcome: TerminalOutcome::Returned {
                ret: TraceVal::u32(prog.input_x),
                mem_digest: digest.clone(),
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 1,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        };
        let leg_lean = AuthorityRunResult {
            authority: "lean".to_string(),
            outcome: TerminalOutcome::Returned {
                ret: TraceVal::u32(prog.input_x + 1),
                mem_digest: digest,
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 1,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        };
        CaseReport {
            case_id: format!("fuzz_s{}_i{}", prog.seed, prog.index),
            category: CaseCategory::FuzzGenerated,
            expected_class: ExpectedCaseClass::Agree,
            verdict,
            expectation_violation: None,
            rustc_dual: RustcDualResult {
                o0: leg_ref.clone(),
                o2: leg_ref.clone(),
                parity_ok: true,
                skipped_for_ub: false,
                mismatch_detail: None,
            },
            miri: Some(leg_ref),
            lean: Some(leg_lean),
            lean_strict_probe: None,
            mir_eval: None,
            metamorphic: None,
        }
    };

    let eval = |p: &anneal_itree_diff::fuzzer::FuzzProgram| {
        let v = TraceVerdict::UnsoundAccept {
            detail: format!(
                "terminal outcome mismatch: value {} != {} (steps={})",
                p.input_x,
                p.input_x + 1,
                p.steps.len()
            ),
        };
        mk_report(p, v)
    };

    let init_rep = eval(&initial);
    let target_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &init_rep.verdict,
        init_rep.miri.as_ref(),
        init_rep.lean.as_ref(),
    )
    .unwrap();

    let (witness, tool_err) = shrink_and_build_witness_with(
        &init_rep.case_id,
        &initial,
        &init_rep.verdict,
        &target_sig,
        eval,
    );
    assert!(tool_err.is_none());
    assert!(witness.shrink.minimized.steps.is_empty());
    assert_eq!(witness.shrink.minimized.input_x, 0);
    assert_eq!(witness.shrink.minimized.input_y, 0);
    assert_eq!(
        witness.original_verdict,
        TraceVerdict::UnsoundAccept {
            detail: "terminal outcome mismatch: value 100 != 101 (steps=2)".to_string(),
        }
    );
    assert_eq!(
        witness.verdict,
        TraceVerdict::UnsoundAccept {
            detail: "terminal outcome mismatch: value 0 != 1 (steps=0)".to_string(),
        }
    );

    let tmp = tempfile::tempdir().unwrap();
    let path = tmp.path().join("recomputed.witness.json");
    witness.write_json(&path).unwrap();
    let loaded: WitnessArtifact =
        serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    assert_eq!(loaded, witness);

    // Secondary witness errors must never overwrite a primary P0 UnsoundAccept.
    let mut p0 = TraceVerdict::UnsoundAccept { detail: "primary P0".to_string() };
    anneal_itree_diff::attach_secondary_tool_error(&mut p0, "witness-writer", "disk full");
    assert!(matches!(
        &p0,
        TraceVerdict::UnsoundAccept { detail }
            if detail.contains("primary P0") && detail.contains("disk full")
    ));

    // Also verify that if re-running the minimized candidate encounters a
    // transient ToolError, `shrink_and_build_witness_with` surfaces it.
    let calls_for_zero = std::cell::Cell::new(0usize);
    let (_, propagated) = shrink_and_build_witness_with(
        &init_rep.case_id,
        &initial,
        &init_rep.verdict,
        &target_sig,
        |p| {
            if p.steps.is_empty() && p.input_x == 0 && p.input_y == 0 {
                let seen = calls_for_zero.get();
                calls_for_zero.set(seen + 1);
                if seen >= 1 {
                    return mk_report(
                        p,
                        TraceVerdict::ToolError {
                            authority: "lean".to_string(),
                            detail: "transient timeout on witness re-run".to_string(),
                        },
                    );
                }
            }
            eval(p)
        },
    );
    assert!(matches!(propagated, Some(TraceVerdict::ToolError { .. })), "got {propagated:?}");

    // When `initial` fails to reproduce on `shrink_fuzz_program`'s very first
    // evaluation (returning `minimized == initial` with `succeeded = false`),
    // `shrink_and_build_witness_with` still re-evaluates `minimized`, marks
    // `witness.shrink.succeeded = false`, records the actual rechecked verdict
    // instead of copying `original_verdict`, and propagates `Some(ToolError)`.
    let (nonrepro_witness, nonrepro_err) = shrink_and_build_witness_with(
        &init_rep.case_id,
        &initial,
        &init_rep.verdict,
        &target_sig,
        |p| mk_report(p, TraceVerdict::Agree),
    );
    assert!(!nonrepro_witness.shrink.succeeded);
    assert!(!nonrepro_witness.shrink.is_one_minimal);
    assert_eq!(nonrepro_witness.verdict, TraceVerdict::Agree);
    assert!(
        matches!(nonrepro_err, Some(TraceVerdict::ToolError { .. })),
        "expected ToolError when initial failure fails to reproduce, got {nonrepro_err:?}"
    );

    // Budget cutoff before reaching a 1-minimal fixpoint MUST suppress witness
    // emission (`witnesses.is_empty()`, no `.witness.json` file written) while
    // surfacing the cutoff as a secondary `shrink-witness` notice on `report`.
    let (budget_witness, budget_err) = shrink_and_build_witness_with_budget(
        &init_rep.case_id,
        &initial,
        &init_rep.verdict,
        &target_sig,
        ShrinkBudget { max_evals: 2, max_duration: Duration::from_secs(60) },
        eval,
    );
    assert!(budget_witness.shrink.succeeded);
    assert!(budget_witness.shrink.budget_exhausted);
    assert!(!budget_witness.shrink.is_one_minimal);
    assert!(
        matches!(
            &budget_err,
            Some(TraceVerdict::ToolError { authority, detail })
                if authority == "shrink-witness"
                    && detail.contains("shrink budget exhausted before reaching 1-minimal")
        ),
        "expected shrink-witness budget-cutoff ToolError, got {budget_err:?}"
    );
    let mut budget_rep = init_rep.clone();
    let mut emitted_on_budget = Vec::new();
    let budget_dir = tmp.path().join("budget_witnesses");
    fs::create_dir_all(&budget_dir).unwrap();
    apply_fuzz_shrink_outcome(
        &mut budget_rep,
        Some(&budget_dir),
        &mut emitted_on_budget,
        budget_witness,
        budget_err,
    );
    assert!(
        emitted_on_budget.is_empty(),
        "budget-cut partial witness must not be emitted as 1-minimal"
    );
    assert!(!budget_dir.join(format!("{}.witness.json", budget_rep.case_id)).exists());
    assert!(
        matches!(
            &budget_rep.verdict,
            TraceVerdict::UnsoundAccept { detail }
                if detail.contains("shrink budget exhausted before reaching 1-minimal")
        ),
        "expected primary UnsoundAccept + cutoff notice, got {:?}",
        budget_rep.verdict
    );

    // Genuine 1-minimal shrink emits its JSON witness and pushes to
    // `witnesses`.
    let mut ok_rep = init_rep;
    let mut emitted_ok = Vec::new();
    let ok_dir = tmp.path().join("ok_witnesses");
    fs::create_dir_all(&ok_dir).unwrap();
    apply_fuzz_shrink_outcome(&mut ok_rep, Some(&ok_dir), &mut emitted_ok, witness, tool_err);
    assert_eq!(emitted_ok.len(), 1);
    assert!(ok_dir.join(format!("{}.witness.json", ok_rep.case_id)).is_file());
}

#[test]
fn boundary_slots_required_and_terminal_slot_tags_validated_across_parsers() {
    // 1. Valid baseline lines for returned (0x10 = 16), unwound (0x20 = 32),
    //    and aborted (0x30 = 48).
    let ok_rust_ret = r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","boundary_slots":[[16,42,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    assert!(
        parse_rustc_run_output("rustc-O0", Some(0), None, ok_rust_ret, "", 1).tool_error.is_none()
    );

    let ok_lean_ret = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"boundary_slots":[[16,42,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    assert!(parse_lean_trace_output("lean", ok_lean_ret, "", 1).tool_error.is_none());

    let ok_lean_abort = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"aborted","ret":null,"detail":"abort:x","fuel":8,"boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    assert!(parse_lean_trace_output("lean", ok_lean_abort, "", 1).tool_error.is_none());

    // 2. Omitting `boundary_slots`, passing `[]`, or passing wrong terminal
    //    tags must fail closed as ToolError in Rust/Miri.
    let bad_rust_lines = [
        // Missing boundary_slots field entirely
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"fault_ub","ret":null,"detail":"ub","caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        // Empty boundary_slots on returned / unwound / aborted
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            None,
            Some(6),
            r#"ANNEAL_ITREE_PRE_ABORT:{"outcome_kind":"aborted","ret":null,"detail":"abort:h","boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        // Mismatched terminal tags (`0x20` on returned, `0x10` on unwound, or
        // `0x01`/`0x10` on aborted)
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","boundary_slots":[[32]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","boundary_slots":[[16,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            None,
            Some(6),
            r#"ANNEAL_ITREE_PRE_ABORT:{"outcome_kind":"aborted","ret":null,"detail":"abort:h","boundary_slots":[[1]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            None,
            Some(6),
            r#"ANNEAL_ITREE_PRE_ABORT:{"outcome_kind":"aborted","ret":null,"detail":"abort:h","boundary_slots":[[16]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        // Tag-only `[16]` or wrong return bytes `[16,99,0,0,0]` for `u32(42)`
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","boundary_slots":[[16]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
        (
            Some(0),
            None,
            r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"42"},"detail":"","boundary_slots":[[16,99,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        ),
    ];
    for (exit_code, sig, line) in bad_rust_lines {
        let r = parse_rustc_run_output("rustc-O0", exit_code, sig, line, "", 1);
        assert!(r.tool_error.is_some(), "expected Rust ToolError for: {line}");
        let m = parse_miri_run_output("miri", exit_code, sig, line, "", 1);
        assert!(m.tool_error.is_some(), "expected Miri ToolError for: {line}");
    }

    // Omitting entry-argument slots when `expected_entry_slots = Some(2)` must
    // fail closed across Rust, Miri, and Lean parsers!
    assert!(
        parse_rustc_run_output_with_expected_args(
            "rustc-O0",
            Some(0),
            None,
            ok_rust_ret,
            "",
            1,
            Some(2),
        )
        .tool_error
        .is_some()
    );
    assert!(
        parse_miri_run_output_with_expected_args(
            "miri",
            Some(0),
            None,
            ok_rust_ret,
            "",
            1,
            Some(2)
        )
        .tool_error
        .is_some()
    );
    assert!(
        parse_lean_trace_output_with_expected_args("lean", ok_lean_ret, "", 1, Some(2))
            .tool_error
            .is_some()
    );

    // 3. Same checks on Lean and `anneal-mir-eval` parsers.
    let bad_lean_lines = [
        // Missing boundary_slots entirely
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"fault_unsupported","ret":null,"detail":"u","fuel":8,"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Empty boundary_slots on returned / unwound / aborted
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"aborted","ret":null,"detail":"a","fuel":8,"boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        // Mismatched terminal tags or truncated/wrong return payload bytes
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"boundary_slots":[[16]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"42"},"detail":"","fuel":8,"boundary_slots":[[16,7,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"unwound","ret":null,"detail":"p","fuel":8,"boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"aborted","ret":null,"detail":"a","fuel":8,"boundary_slots":[[1]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
    ];
    for line in bad_lean_lines {
        let l = parse_lean_trace_output("lean", line, "", 1);
        assert!(l.tool_error.is_some(), "expected Lean ToolError for: {line}");
    }

    let bad_mir_eval_slot = parse_mir_eval_output(
        Some(0),
        r#"{"outcome":{"kind":"returned","value":{"kind":"returned","ret":{"kind":"scalar","value":{"width":"i32","signed":false,"bits":"42"}}}},"boundary_slots":[[16]]}"#,
        "",
        1,
    );
    assert!(bad_mir_eval_slot.tool_error.is_some());

    // 4. Lean `"entry argument "` failures abort before pushing any entry
    //    argument boundary slots (`Some(0)`): `[]` is accepted even when the
    //    case has `2` arguments, whereas spurious non-empty `boundary_slots`
    //    must fail closed as `ToolError`.
    let entry_arg_empty_slots = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"fault_undefined","ret":null,"detail":"entry argument bit-validity failed","fuel":8,"boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    assert!(
        parse_lean_trace_output_with_expected_args("lean", entry_arg_empty_slots, "", 1, Some(2))
            .tool_error
            .is_none()
    );
    let entry_arg_spurious_slots = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"fault_undefined","ret":null,"detail":"entry argument bit-validity failed","fuel":8,"boundary_slots":[[1]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    assert!(
        parse_lean_trace_output_with_expected_args(
            "lean",
            entry_arg_spurious_slots,
            "",
            1,
            Some(2)
        )
        .tool_error
        .is_some()
    );
}

#[test]
fn corpus_filter_rejects_zero_matches_and_cli_exits_code_2() {
    let all = filter_corpus_cases(curated_corpus(), None).expect("unfiltered corpus");
    assert_eq!(all.len(), 33);

    let sub = filter_corpus_cases(curated_corpus(), Some("cat1_clamp")).expect("matching filter");
    assert_eq!(sub.len(), 1);
    assert_eq!(sub[0].id, "cat1_clamp_u32_range");

    let err = filter_corpus_cases(curated_corpus(), Some("__no_such_case_id__"))
        .expect_err("0-match filter must fail closed");
    assert!(err.contains("matched 0 cases"), "got: {err}");

    let bin = env!("CARGO_BIN_EXE_itree-diff");
    let out = std::process::Command::new(bin)
        .args(["--filter", "__no_such_case_id__", "--no-miri", "--no-lean"])
        .output()
        .expect("spawn itree-diff CLI");
    assert_eq!(
        out.status.code(),
        Some(2),
        "stdout={} stderr={}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("matched 0 cases"), "stderr={stderr}");

    // Passing `--filter` when corpus execution is disabled (`--fuzz 0` without
    // `--corpus`) must also exit with code 2 rather than ignoring `--filter`.
    let out_ignored = std::process::Command::new(bin)
        .args(["--fuzz", "0", "--filter", "cat1_clamp", "--no-miri", "--no-lean"])
        .output()
        .expect("spawn itree-diff CLI with --fuzz and --filter");
    assert_eq!(out_ignored.status.code(), Some(2));
    assert!(!out_ignored.stderr.is_empty());
}

#[test]
fn live_control_chars_escaped_and_round_tripped_across_rust_miri_and_lean() {
    let mut all_ctrls = String::from("ctrl:");
    for b in 0u8..=0x1Fu8 {
        all_ctrls.push(char::from(b));
    }
    all_ctrls.push_str("\"\\:end");

    let rendered_lit = lean_str_lit(&all_ctrls);
    assert!(
        rendered_lit.bytes().all(|b| b >= 0x20),
        "lean_str_lit must never emit raw ASCII control bytes: {rendered_lit:?}"
    );
    assert!(
        rendered_lit.contains("\\x00")
            && rendered_lit.contains("\\x08")
            && rendered_lit.contains("\\x0c")
            && rendered_lit.contains("\\x1b")
            && rendered_lit.contains("\\x1f")
    );

    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cfg = DifferentialConfig::for_workspace(anneal_root);
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");

    let mut case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_callee_panic_unwind_cleanup")
        .expect("locate cat4_callee_panic_unwind_cleanup");
    case.id = "ctrl_char_unwind_roundtrip".to_string();
    let mut sched = EnvSchedule::default();
    sched.push_callee("ext_may_panic_u32", EnvAction::Unwind { message: all_ctrls.clone() });
    case.env_schedule = sched;

    let rep = engine.run_case(&case);
    assert!(
        !rep.verdict.is_critical_failure(),
        "unexpected critical failure on control-char unwind: {:?}",
        rep
    );
    assert!(rep.expectation_violation.is_none(), "{:?}", rep.expectation_violation);

    let check_unwind_reason = |auth_res: &AuthorityRunResult| {
        assert!(auth_res.tool_error.is_none(), "{auth_res:?}");
        let found = auth_res.spine.events.iter().find_map(|ev| match ev {
            ObservableEvent::CallUnwind { reason, .. } => Some(reason.as_str()),
            _ => None,
        });
        assert_eq!(
            found,
            Some(all_ctrls.as_str()),
            "control-character round-trip mismatch in {}",
            auth_res.authority
        );
    };
    check_unwind_reason(&rep.rustc_dual.o0);
    check_unwind_reason(&rep.rustc_dual.o2);
    check_unwind_reason(rep.lean.as_ref().expect("Lean result"));
    if let Some(m) = &rep.miri {
        check_unwind_reason(m);
    }
}

#[test]
fn case_expectation_validator_catches_regressions_and_outcome_drift() {
    let ret_digest =
        compute_boundary_mem_digest(&[vec![Some(0x10), Some(7), Some(0), Some(0), Some(0)]]);
    let unw_digest = compute_boundary_mem_digest(&[vec![Some(0x20)]]);
    let abt_digest = compute_boundary_mem_digest(&[vec![Some(0x30)]]);

    let mk_leg = |auth: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let mk_rustc = |outcome: TerminalOutcome| RustcDualResult {
        o0: mk_leg("rustc-O0", outcome.clone()),
        o2: mk_leg("rustc-O2", outcome),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };

    let ret_out = TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: ret_digest };
    let unw_out = TerminalOutcome::Unwound { mem_digest: unw_digest };
    let abt_out = TerminalOutcome::Aborted { mem_digest: abt_digest };
    let ref_out = TerminalOutcome::CaptureRefused { reason: "unsupported".to_string() };
    let ub_out = TerminalOutcome::FaultUb {
        detail: "error: Undefined Behavior: overflowing shift by 32 in `unchecked_shl`".to_string(),
    };
    let shift_ub_spec = ExpectedUbSpec::new(
        UbFaultClass::UncheckedShiftOverflow,
        "unchecked_shl",
        Some("unchecked shift overflow"),
    );

    let captured_spec =
        LeanProgramSpec::CapturedRust { crate_name: "c".to_string(), select_fn: "f".to_string() };
    let multicall_spec = LeanProgramSpec::SyntheticMirAst {
        program_lean_expr: "{ bodies := [{ terminator := .call 1 [] ⟨0, []⟩ none (.cleanup 2) }] }"
            .to_string(),
        external_callees: vec!["ext_callee".to_string()],
    };
    let cons_verdict = TraceVerdict::ConservativeOverApprox {
        reason: "refused".to_string(),
        ub_refutation_disallowed: true,
        undeclared_ub_fault: false,
    };

    // 1. ExpectedCaseClass::Agree regressing to ConservativeOverApprox in
    //    CompositionalITree MUST fail expectation validation and fail
    //    `DifferentialReport::has_critical_failures()`.
    let regressed_violation = check_case_expectation(
        ExpectedCaseClass::Agree,
        None,
        None,
        CaseCategory::MultiCallChain,
        &multicall_spec,
        &cons_verdict,
        &mk_rustc(ret_out.clone()),
        Some(&mk_leg("miri", ret_out.clone())),
        Some(&mk_leg("lean", ref_out.clone())),
        LeanTraceMode::CompositionalITree,
    );
    assert!(regressed_violation.is_some());

    let regressed_rep = DifferentialReport::from_cases(
        "available",
        true,
        true,
        "unavailable",
        LeanTraceMode::CompositionalITree,
        vec![CaseReport {
            case_id: "regressed_agree_case".to_string(),
            category: CaseCategory::MultiCallChain,
            expected_class: ExpectedCaseClass::Agree,
            verdict: cons_verdict.clone(),
            expectation_violation: regressed_violation,
            rustc_dual: mk_rustc(ret_out.clone()),
            miri: Some(mk_leg("miri", ret_out.clone())),
            lean: Some(mk_leg("lean", ref_out.clone())),
            lean_strict_probe: None,
            mir_eval: None,
            metamorphic: None,
        }],
        Vec::new(),
    );
    assert_eq!(regressed_rep.counts.expectation_mismatches, 1);
    assert!(regressed_rep.has_critical_failures());

    // Multi-call conservative refusal IS allowed in StrictVerbatim, whereas a
    // single-body `CapturedRust` regression in StrictVerbatim is rejected!
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &cons_verdict,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out.clone())),
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::StrictVerbatim,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::ScalarBitwise,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out.clone())),
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::StrictVerbatim,
        )
        .is_some()
    );

    // 2. ExpectedCaseClass::Unwind or Abort silently agreeing on `Returned`
    //    must fail expectation validation and `has_critical_failures()`.
    for wrong_class in [ExpectedCaseClass::Unwind, ExpectedCaseClass::Abort] {
        let viol = check_case_expectation(
            wrong_class,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &TraceVerdict::Agree,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out.clone())),
            Some(&mk_leg("lean", ret_out.clone())),
            LeanTraceMode::CompositionalITree,
        );
        assert!(viol.is_some(), "expected violation when {wrong_class:?} returned normally");
        let bad_rep = DifferentialReport::from_cases(
            "available",
            true,
            true,
            "unavailable",
            LeanTraceMode::CompositionalITree,
            vec![CaseReport {
                case_id: format!("wrong_outcome_{wrong_class:?}"),
                category: CaseCategory::MultiCallChain,
                expected_class: wrong_class,
                verdict: TraceVerdict::Agree,
                expectation_violation: viol,
                rustc_dual: mk_rustc(ret_out.clone()),
                miri: Some(mk_leg("miri", ret_out.clone())),
                lean: Some(mk_leg("lean", ret_out.clone())),
                lean_strict_probe: None,
                mir_eval: None,
                metamorphic: None,
            }],
            Vec::new(),
        );
        assert_eq!(bad_rep.counts.expectation_mismatches, 1);
        assert!(bad_rep.has_critical_failures());
    }

    // 3. Valid DegradedNoMiri and DegradedNoLean runs satisfy expectations.
    let deg_no_miri = TraceVerdict::DegradedNoMiri { detail: "no miri".to_string() };
    let deg_no_lean = TraceVerdict::DegradedNoLean { detail: "no lean".to_string() };
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::ScalarBitwise,
            &captured_spec,
            &deg_no_miri,
            &mk_rustc(ret_out.clone()),
            None,
            Some(&mk_leg("lean", ret_out.clone())),
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Unwind,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &deg_no_lean,
            &mk_rustc(unw_out.clone()),
            Some(&mk_leg("miri", unw_out)),
            None,
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Abort,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &deg_no_miri,
            &mk_rustc(abt_out.clone()),
            None,
            Some(&mk_leg("lean", abt_out)),
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&shift_ub_spec),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_lean,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", ub_out.clone())),
            None,
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );

    // 4. ExpectedCaseClass::UndefinedBehavior rejects missing `expected_ub`,
    //    `Unclassified`/empty specs, simultaneous `--no-miri --no-lean`,
    //    unrelated Miri UB causes, and Lean diagnostics missing `lean_marker`.
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&shift_ub_spec),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_miri,
            &RustcDualResult::skipped_for_ub("ub"),
            None,
            None,
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            None,
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_lean,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", ub_out.clone())),
            None,
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&ExpectedUbSpec::new(UbFaultClass::Unclassified, "ub", None)),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_lean,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", ub_out)),
            None,
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );
    let sched_bool_ub_spec = ExpectedUbSpec::new(
        UbFaultClass::ScheduledReturnDecode,
        "callee `ext_oracle_bool` scheduled ReturnBytes invalid",
        Some("invalid scheduled ReturnBytes for ext_oracle_bool"),
    );
    let wrong_miri_ub = TerminalOutcome::FaultUb {
        detail: "error: Undefined Behavior: entering unreachable code".to_string(),
    };
    let expected_lean_ub = TerminalOutcome::FaultUb {
        detail: "invalid scheduled ReturnBytes for ext_oracle_bool".to_string(),
    };
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&sched_bool_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &TraceVerdict::Agree,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", wrong_miri_ub)),
            Some(&mk_leg("lean", expected_lean_ub)),
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );
    let ok_miri_sched_ub = TerminalOutcome::FaultUb {
        detail: "callee `ext_oracle_bool` scheduled ReturnBytes invalid: invalid bool".to_string(),
    };
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&sched_bool_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_spec,
            &cons_verdict,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", ok_miri_sched_ub.clone())),
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );

    // 5. `ExpectedCaseClass::DisclosedGap` requires an accepting reference
    //    outcome (`Returned` / `Unwound` / `Aborted` / `Diverged`): if Miri
    //    starts reporting `FaultUb`, expectation validation rejects it even
    //    when `verdict` is `DisclosedGapArtifact`.
    let gap_verdict = TraceVerdict::DisclosedGapArtifact {
        gap: DisclosedGapKind::CallerRawPtrAliasing,
        detail: "does not model Rust's pointer aliasing rules".to_string(),
    };
    let lean_gap_refused = TerminalOutcome::CaptureRefused {
        reason: "does not model Rust's pointer aliasing rules".to_string(),
    };
    assert!(
        check_case_expectation(
            ExpectedCaseClass::DisclosedGap,
            None,
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &gap_verdict,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out)),
            Some(&mk_leg("lean", lean_gap_refused.clone())),
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::DisclosedGap,
            None,
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &gap_verdict,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&mk_leg("miri", ok_miri_sched_ub)),
            Some(&mk_leg("lean", lean_gap_refused)),
            LeanTraceMode::CompositionalITree,
        )
        .is_some()
    );

    // 6. `ExpectedCaseClass::ConservativeOverApprox` and `DisclosedGap` MUST
    //    reject cases where Lean unexpectedly returned `Returned`, even if
    //    `anneal-mir-eval` produced `ConservativeOverApprox` or
    //    `DisclosedGapArtifact`.
    let mir_eval_cons = AuthorityRunResult {
        authority: "anneal-mir-eval".to_string(),
        outcome: TerminalOutcome::CaptureRefused {
            reason: "unsupported padded struct return".to_string(),
        },
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let mir_ret = mk_leg(
        "miri",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: "aa".repeat(32) },
    );
    let lean_regressed_ret = mk_leg(
        "lean",
        TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: "aa".repeat(32) },
    );
    let cons_padded_spec = ExpectedConservativeSpec::new(
        ConservativeRefKind::Returned,
        "unsupported type: PaddedHeader",
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&cons_padded_spec),
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_regressed_ret),
            Some(&mir_eval_cons),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "mir_eval CaptureRefused must not mask Lean Returned regression"
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::DisclosedGap,
            None,
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &gap_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_regressed_ret),
            Some(&mir_eval_cons),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "mir_eval DisclosedGapArtifact must not mask Lean Returned regression"
    );

    // 7. `ExpectedCaseClass::ConservativeOverApprox` MUST reject missing specs,
    //    empty markers, wrong reference outcomes, `Diverged` fuel exhaustion,
    //    and `CaptureRefused` with an unrelated diagnostic marker.
    let lean_padded_refused = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused { reason: "unsupported type: PaddedHeader".to_string() },
    );
    let lean_unrelated_refused = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused { reason: "unsupported type: Other".to_string() },
    );
    let lean_diverged = mk_leg("lean", TerminalOutcome::Diverged { fuel: 128 });
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&cons_padded_spec),
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_padded_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_none()
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            None,
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_padded_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "missing expected_conservative spec must fail"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&ExpectedConservativeSpec::new(ConservativeRefKind::Returned, "  ")),
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_padded_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "empty lean_marker in expected_conservative must fail"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&ExpectedConservativeSpec::new(
                ConservativeRefKind::Unwound,
                "unsupported type: PaddedHeader",
            )),
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_padded_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "wrong reference outcome kind must fail"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&cons_padded_spec),
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_unrelated_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "unrelated CaptureRefused marker must fail"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::ConservativeOverApprox,
            None,
            Some(&cons_padded_spec),
            CaseCategory::PaddedAggregatesAndEnums,
            &captured_spec,
            &cons_verdict,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&lean_diverged),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "Lean Diverged fuel exhaustion must not satisfy ConservativeOverApprox"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            Some(&cons_padded_spec),
            CaseCategory::ScalarBitwise,
            &captured_spec,
            &TraceVerdict::Agree,
            &mk_rustc(mir_ret.outcome.clone()),
            Some(&mir_ret),
            Some(&mir_ret),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "unexpected expected_conservative on Agree case must fail"
    );

    // 8. Expected-UB probes MUST bind conservative Lean `CaptureRefused`
    //    outcomes to an explicit `expected_ub.lean_refusal_marker` and MUST NOT
    //    certify via step-fuel exhaustion (`Diverged`).
    let unreach_ub_spec =
        ExpectedUbSpec::new(UbFaultClass::UnreachableOrNoUnwind, "entering unreachable code", None);
    let skipped_rustc = RustcDualResult::skipped_for_ub("ub");
    let v_ub_div = classify_four_way_with_ub_guard(
        &skipped_rustc.o0,
        &skipped_rustc.o2,
        true,
        None,
        Some(&lean_diverged),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_ub_div, TraceVerdict::UnsoundAccept { .. }),
        "Lean Diverged must not certify UB without Miri, got {v_ub_div:?}"
    );
    let miri_unreach_ub = mk_leg(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "error: Undefined Behavior: entering unreachable code".to_string(),
        },
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_spec),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &cons_verdict,
            &skipped_rustc,
            Some(&miri_unreach_ub),
            Some(&lean_diverged),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "marker-less UB expectation must reject Lean Diverged"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_spec),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_miri,
            &skipped_rustc,
            None,
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "UB expectation without lean_marker or lean_refusal_marker must reject CaptureRefused"
    );
    let unreach_ub_with_refusal =
        unreach_ub_spec.clone().with_lean_refusal_marker("unsafe unreachable");
    let lean_unreach_refused = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused { reason: "unsafe unreachable".to_string() },
    );
    let lean_unrelated_refused = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused { reason: "unrelated capture error".to_string() },
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_with_refusal),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_miri,
            &skipped_rustc,
            None,
            Some(&lean_unreach_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_none(),
        "matching expected_ub.lean_refusal_marker must accept CaptureRefused"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_with_refusal),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_miri,
            &skipped_rustc,
            None,
            Some(&lean_unrelated_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "unrelated CaptureRefused reason must fail lean_refusal_marker validation"
    );
    let conflicting_ub_spec = ExpectedUbSpec::new(
        UbFaultClass::UnreachableOrNoUnwind,
        "entering unreachable code",
        Some("entering unreachable code"),
    )
    .with_lean_refusal_marker("unsafe unreachable");
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&conflicting_ub_spec),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &deg_no_miri,
            &skipped_rustc,
            None,
            Some(&lean_unreach_refused),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "setting both lean_marker and lean_refusal_marker without strict-refusal duality must fail"
    );

    // 9. When `anneal-mir-eval` reports `FaultUb` on an expected-UB case, it
    //    MUST match a dedicated non-empty `expected_ub.mir_eval_marker` rather
    //    than only sharing a broad `UbFaultClass`.
    let unreach_ub_with_eval =
        unreach_ub_with_refusal.clone().with_mir_eval_marker("executed Unreachable terminator");
    let right_eval_ub = mk_leg(
        "anneal-mir-eval",
        TerminalOutcome::FaultUb { detail: "executed Unreachable terminator".to_string() },
    );
    let wrong_same_class_eval_ub = mk_leg(
        "anneal-mir-eval",
        TerminalOutcome::FaultUb { detail: "unwound into UnwindAction::Unreachable".to_string() },
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_with_eval),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &TraceVerdict::Agree,
            &skipped_rustc,
            Some(&miri_unreach_ub),
            Some(&lean_unreach_refused),
            Some(&right_eval_ub),
            LeanTraceMode::CompositionalITree,
        )
        .is_none(),
        "matching anneal-mir-eval UB diagnostic marker must pass"
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_with_eval),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &TraceVerdict::Agree,
            &skipped_rustc,
            Some(&miri_unreach_ub),
            Some(&lean_unreach_refused),
            Some(&wrong_same_class_eval_ub),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "wrong same-class anneal-mir-eval UB cause must fail expectation check"
    );
    assert!(
        check_case_expectation_with_mir_eval(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&unreach_ub_with_refusal),
            None,
            CaseCategory::NegativeUbAndOverApprox,
            &captured_spec,
            &TraceVerdict::Agree,
            &skipped_rustc,
            Some(&miri_unreach_ub),
            Some(&lean_unreach_refused),
            Some(&right_eval_ub),
            LeanTraceMode::CompositionalITree,
        )
        .is_some(),
        "missing mir_eval_marker on FaultUb must fail expectation check"
    );
}

#[test]
fn unconsumed_env_schedule_actions_rejected_in_process_and_live_authorities() {
    // 1. In-process `run_with_trace_recorder`: misspelled callee key and extra
    //    queued `ReturnBytes` both surface as `InvalidSchedule`
    //    (`ScheduleError::UnconsumedActions`).
    let mut typo_sched = EnvSchedule::default();
    typo_sched.push_callee("typo_callee", EnvAction::ReturnBytes(55u32.to_le_bytes().to_vec()));
    let (disp_typo, rec_typo) =
        run_with_trace_recorder(typo_sched, || sample_traced_callee(10, TestOpCode::Alpha));
    assert!(
        matches!(
            disp_typo,
            TraceRunDisposition::InvalidSchedule(ref p)
                if p.error == ScheduleError::UnconsumedActions { remaining: 1 }
        ),
        "got {disp_typo:?}"
    );
    assert_eq!(
        rec_typo.schedule_error,
        Some(("<unconsumed>".to_string(), ScheduleError::UnconsumedActions { remaining: 1 }))
    );

    let mut extra_sched = EnvSchedule::default();
    extra_sched
        .push_callee("sample_traced_callee", EnvAction::ReturnBytes(10u32.to_le_bytes().to_vec()));
    extra_sched
        .push_callee("sample_traced_callee", EnvAction::ReturnBytes(20u32.to_le_bytes().to_vec()));
    let (disp_extra, _) =
        run_with_trace_recorder(extra_sched, || sample_traced_callee(1, TestOpCode::Alpha));
    assert!(
        matches!(
            disp_extra,
            TraceRunDisposition::InvalidSchedule(ref p)
                if p.error == ScheduleError::UnconsumedActions { remaining: 1 }
        ),
        "got {disp_extra:?}"
    );

    // 2. Live 4-way engine: unconsumed schedule action on `returned`,
    //    `aborted`, and `StrictVerbatim` single-body runs must fail closed as
    //    `TraceVerdict::ToolError` across `rustc`, `miri` (when enabled), and
    //    Lean `ITreeDriver`.
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cfg = DifferentialConfig::for_workspace(anneal_root);
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");

    // 2a. Compositional multi-call `returned` path with misspelled callee key.
    let mut ret_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_call_once_and_postprocess")
        .expect("locate cat4_call_once_and_postprocess");
    ret_case.id = "neg_unconsumed_schedule_returned".to_string();
    ret_case
        .env_schedule
        .push_callee("typo_callee", EnvAction::ReturnBytes(123u32.to_le_bytes().to_vec()));

    let rep_ret = engine.run_case(&ret_case);
    assert!(matches!(rep_ret.verdict, TraceVerdict::ToolError { .. }), "{:?}", rep_ret.verdict);
    if let Some(m) = &rep_ret.miri {
        assert!(m.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")), "{m:?}");
        // Because provisioned Miri returned `tool_error` before certifying UB
        // absence, `engine.run_case` skips native host `rustc` fail-closed;
        // invoke `engine.rustc.run_dual` directly on this UB-free fixture to
        // verify `rustc -O0` and `-O2` unconsumed-schedule rejection too.
        assert!(rep_ret.rustc_dual.skipped_for_ub, "{:?}", rep_ret.rustc_dual);
        let direct_ret = engine.rustc.run_dual(&ret_case);
        assert!(
            direct_ret.o0.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            direct_ret.o0
        );
        assert!(
            direct_ret.o2.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            direct_ret.o2
        );
    } else {
        assert!(
            rep_ret.rustc_dual.o0.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            rep_ret.rustc_dual.o0
        );
        assert!(
            rep_ret.rustc_dual.o2.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            rep_ret.rustc_dual.o2
        );
    }
    assert!(
        rep_ret
            .lean
            .as_ref()
            .and_then(|l| l.tool_error.as_deref())
            .is_some_and(|e| e.contains("unconsumed")),
        "{:?}",
        rep_ret.lean
    );

    // 2b. Scheduled `aborted` path with an extra trailing action queued behind
    //     `Abort`.
    let mut abort_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_scheduled_abort_no_drop")
        .expect("locate cat4_scheduled_abort_no_drop");
    abort_case.id = "neg_unconsumed_schedule_aborted".to_string();
    abort_case
        .env_schedule
        .push_callee("ext_may_panic_u32", EnvAction::ReturnBytes(7u32.to_le_bytes().to_vec()));

    let rep_abort = engine.run_case(&abort_case);
    assert!(matches!(rep_abort.verdict, TraceVerdict::ToolError { .. }), "{:?}", rep_abort.verdict);
    if let Some(m) = &rep_abort.miri {
        assert!(m.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")), "{m:?}");
        assert!(rep_abort.rustc_dual.skipped_for_ub, "{:?}", rep_abort.rustc_dual);
        let direct_abort = engine.rustc.run_dual(&abort_case);
        assert!(
            direct_abort.o0.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            direct_abort.o0
        );
    } else {
        assert!(
            rep_abort.rustc_dual.o0.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
            "{:?}",
            rep_abort.rustc_dual.o0
        );
    }
    assert!(
        rep_abort
            .lean
            .as_ref()
            .and_then(|l| l.tool_error.as_deref())
            .is_some_and(|e| e.contains("unconsumed")),
        "{:?}",
        rep_abort.lean
    );

    // 2c. `StrictVerbatim` single-body Lean run with unconsumed global action
    //     on `returned`, `diverged` (`fuel = 1`), `fault_undefined`, and
    //     `fault_unsupported`, plus `fault_ub` with trailing unconsumed action.
    let mut strict_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat1_clamp_u32_range")
        .expect("locate cat1_clamp_u32_range");
    strict_case.id = "neg_unconsumed_schedule_strict".to_string();
    strict_case.env_schedule.push_global(EnvAction::ReturnBytes(1u32.to_le_bytes().to_vec()));
    let lean_sess = engine.lean.as_ref().expect("Lean session");
    let (strict_lean, _) = lean_sess.run_case(&strict_case, LeanTraceMode::StrictVerbatim);
    assert!(
        strict_lean.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
        "{strict_lean:?}"
    );

    let mut div_case = strict_case.clone();
    div_case.id = "neg_unconsumed_schedule_diverged".to_string();
    div_case.fuel = 1;
    let (div_lean, _) = lean_sess.run_case(&div_case, LeanTraceMode::CompositionalITree);
    assert!(
        div_lean.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
        "{div_lean:?}"
    );

    let mut ub_sched_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_scheduled_invalid_bool_return_ub")
        .expect("locate cat4_scheduled_invalid_bool_return_ub");
    ub_sched_case.id = "neg_unconsumed_schedule_fault_ub".to_string();
    ub_sched_case.env_schedule.push_callee("ext_oracle_bool", EnvAction::ReturnBytes(vec![1u8]));
    let rep_ub = engine.run_case(&ub_sched_case);
    assert!(matches!(rep_ub.verdict, TraceVerdict::ToolError { .. }), "{:?}", rep_ub.verdict);
    assert!(
        rep_ub
            .lean
            .as_ref()
            .and_then(|l| l.tool_error.as_deref())
            .is_some_and(|e| e.contains("unconsumed")),
        "{:?}",
        rep_ub.lean
    );
    if let Some(m) = &rep_ub.miri {
        assert!(m.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")), "{m:?}");
    }

    let mut bad_decode_extra = EnvSchedule::default();
    bad_decode_extra.push_callee("sample_bool_callee", EnvAction::ReturnBytes(vec![2u8]));
    bad_decode_extra.push_callee("sample_bool_callee", EnvAction::ReturnBytes(vec![1u8]));
    let (disp_ub_extra, _) = run_with_trace_recorder(bad_decode_extra, || sample_bool_callee(7));
    assert!(
        matches!(
            disp_ub_extra,
            TraceRunDisposition::InvalidSchedule(ref p)
                if p.error == ScheduleError::UnconsumedActions { remaining: 1 }
        ),
        "got {disp_ub_extra:?}"
    );
}

#[cfg(unix)]
#[test]
fn miri_runner_rejects_explicit_toolchain_skew_and_invalid_config() {
    let tmp = tempfile::tempdir().unwrap();
    let active_sr = tmp.path().join("active_sysroot");
    let other_sr = tmp.path().join("other_sysroot");
    let trimmed_sr = tmp.path().join("trimmed_omnibus_sysroot");
    let cache_dir = tmp.path().join("miri_cache");
    for sr in [&active_sr, &other_sr, &trimmed_sr] {
        fs::create_dir_all(sr.join("bin")).unwrap();
        fs::create_dir_all(sr.join("lib")).unwrap();
    }

    let canon_active = fs::canonicalize(&active_sr).unwrap();
    let canon_other = fs::canonicalize(&other_sr).unwrap();

    let write_mock_miri = |bin_path: &std::path::Path, reported_sr: &std::path::Path| {
        let script = format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nexit 1\n",
            reported_sr.display()
        );
        fs::write(bin_path, script).unwrap();
        let mut perms = fs::metadata(bin_path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(bin_path, perms).unwrap();
    };
    let write_mock_cargo = |bin_path: &std::path::Path| {
        fs::write(bin_path, "#!/usr/bin/env bash\nexit 0\n").unwrap();
        let mut perms = fs::metadata(bin_path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(bin_path, perms).unwrap();
    };

    let active_miri = active_sr.join("bin/miri");
    let active_cargo = active_sr.join("bin/cargo");
    let other_miri = other_sr.join("bin/miri");
    let other_cargo = other_sr.join("bin/cargo");
    write_mock_miri(&active_miri, &canon_active);
    write_mock_cargo(&active_cargo);
    write_mock_miri(&other_miri, &canon_other);
    write_mock_cargo(&other_cargo);

    assert_eq!(query_miri_sysroot(&active_miri).unwrap(), canon_active);
    assert_eq!(query_miri_sysroot(&other_miri).unwrap(), canon_other);

    // 1. Explicit ANNEAL_ITREE_MIRI_BIN pointing at `other_sr` must fail closed
    //    with InvalidConfig skew error!
    let skew_bin_err = resolve_miri_coordinates_with_env(Some(&active_sr), |k| {
        if k == "ANNEAL_ITREE_MIRI_BIN" {
            Some(other_miri.as_os_str().to_os_string())
        } else {
            None
        }
    })
    .expect_err("skewed ANNEAL_ITREE_MIRI_BIN must fail closed");
    assert!(skew_bin_err.is_invalid_config());
    assert!(skew_bin_err.reason().contains("Miri toolchain version skew"), "{skew_bin_err}");

    let probe_skew_bin = MiriRunner::probe_with_env(&cache_dir, Some(&active_sr), |k| {
        if k == "ANNEAL_ITREE_MIRI_BIN" {
            Some(other_miri.as_os_str().to_os_string())
        } else {
            None
        }
    });
    assert!(
        matches!(probe_skew_bin, MiriAvailability::InvalidConfig { .. }),
        "expected InvalidConfig, got {probe_skew_bin:?}"
    );

    // 2. Explicit ANNEAL_ITREE_MIRI_CARGO pointing at `other_sr` must fail
    //    closed as InvalidConfig skew both when `active_sr` has `bin/miri` AND
    //    when `trimmed_sr` lacks `bin/miri`!
    for exp_sr in [&active_sr, &trimmed_sr] {
        let skew_cargo_err = resolve_miri_coordinates_with_env(Some(exp_sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_CARGO" {
                Some(other_cargo.as_os_str().to_os_string())
            } else {
                None
            }
        })
        .expect_err("skewed ANNEAL_ITREE_MIRI_CARGO must fail closed");
        assert!(skew_cargo_err.is_invalid_config());
        assert!(
            skew_cargo_err.reason().contains("Miri toolchain version skew"),
            "{skew_cargo_err}"
        );
    }

    // 3. Matching explicit ANNEAL_ITREE_MIRI_BIN=<active_sr>/bin/miri succeeds!
    let (label_ok, sr_ok, miri_ok, cargo_ok) =
        resolve_miri_coordinates_with_env(Some(&active_sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_BIN" {
                Some(active_miri.as_os_str().to_os_string())
            } else {
                None
            }
        })
        .expect("matching explicit ANNEAL_ITREE_MIRI_BIN must succeed");
    assert_eq!(label_ok, "explicit-miri-bin");
    assert_eq!(sr_ok, canon_active);
    assert_eq!(miri_ok, fs::canonicalize(&active_miri).unwrap());
    assert_eq!(cargo_ok, Some(fs::canonicalize(&active_cargo).unwrap()));

    // 4. Invalid explicit ANNEAL_ITREE_MIRI_SYSROOT surfaces InvalidConfig
    //    (never Unavailable), whereas a trimmed sysroot without overrides
    //    surfaces Unavailable so `workspace-tests` runs in DegradedNoMiri mode.
    let bad_miri_sr = tmp.path().join("bad_miri_sysroot_dir");
    fs::create_dir_all(&bad_miri_sr).unwrap();
    let probe_bad_sr = MiriRunner::probe_with_env(&cache_dir, Some(&active_sr), |k| match k {
        "ANNEAL_ITREE_MIRI_BIN" => Some(active_miri.as_os_str().to_os_string()),
        "ANNEAL_ITREE_MIRI_SYSROOT" => Some(bad_miri_sr.as_os_str().to_os_string()),
        _ => None,
    });
    assert!(
        matches!(probe_bad_sr, MiriAvailability::InvalidConfig { .. }),
        "expected InvalidConfig for invalid ANNEAL_ITREE_MIRI_SYSROOT, got {probe_bad_sr:?}"
    );

    let probe_trimmed = MiriRunner::probe_with_env(&cache_dir, Some(&trimmed_sr), |_| None);
    assert!(
        matches!(probe_trimmed, MiriAvailability::Unavailable { .. }),
        "expected Unavailable on trimmed sysroot without overrides, got {probe_trimmed:?}"
    );
    assert!(matches!(
        resolve_miri_coordinates_with_env(Some(&trimmed_sr), |_| None),
        Err(MiriProbeError::Unavailable(_))
    ));
}

#[cfg(unix)]
#[test]
fn rustc_sysroot_digest_tracks_compiler_binary_and_host_and_target_libs() {
    let tmp = tempfile::tempdir().unwrap();
    let sr = tmp.path().join("mock_rust_sysroot");
    let bin_dir = sr.join("bin");
    let lib_dir = sr.join("lib");
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    let target_lib_dir = sr.join(format!("lib/rustlib/{mock_host}/lib"));
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(&lib_dir).unwrap();
    fs::create_dir_all(&target_lib_dir).unwrap();

    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    let rustc_bin = bin_dir.join("rustc");
    let driver_so = lib_dir.join("librustc_driver-mock.so");
    let llvm_so = lib_dir.join("libLLVM.so.22.1-rust-mock");
    let core_rlib = target_lib_dir.join("libcore-mock.rlib");

    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\n# build-a\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {mock_host}\\n'\n"
        ),
    );
    fs::write(&driver_so, b"driver-bytes-v1").unwrap();
    fs::write(&llvm_so, b"llvm-bytes-v1").unwrap();
    fs::write(&core_rlib, b"core-rlib-bytes-v1").unwrap();

    let d0 = compute_rustc_sysroot_digest(&sr).expect("initial sysroot digest");
    assert_eq!(d0.len(), 64);
    assert_eq!(compute_rustc_sysroot_digest(&sr).unwrap(), d0);

    // (a) Changing `bin/rustc` executable bytes with identical `-vV` stdout
    //     MUST change the sysroot digest.
    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\n# build-b-rebuilt-binary\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {mock_host}\\n'\n"
        ),
    );
    let d1 = compute_rustc_sysroot_digest(&sr).expect("digest after rustc binary rebuild");
    assert_ne!(d1, d0, "sysroot digest must change when bin/rustc bytes change");

    // (b) Changing `lib/librustc_driver-mock.so` (or versioned `libLLVM.so.*`)
    //     bytes MUST change the sysroot digest.
    fs::write(&driver_so, b"driver-bytes-v2-patched").unwrap();
    let d2 = compute_rustc_sysroot_digest(&sr).expect("digest after librustc_driver change");
    assert_ne!(d2, d1, "sysroot digest must change when librustc_driver.so bytes change");

    fs::write(&llvm_so, b"llvm-bytes-v2-patched").unwrap();
    let d2b = compute_rustc_sysroot_digest(&sr).expect("digest after libLLVM.so.* change");
    assert_ne!(d2b, d2, "sysroot digest must change when libLLVM.so.* bytes change");

    // (c) Changing `lib/rustlib/<host_target>/lib/libcore-mock.rlib`
    //     bytes MUST change the sysroot digest.
    fs::write(&core_rlib, b"core-rlib-bytes-v2-patched").unwrap();
    let d3 = compute_rustc_sysroot_digest(&sr).expect("digest after libcore.rlib change");
    assert_ne!(d3, d2b, "sysroot digest must change when target libcore.rlib bytes change");

    // Broken `bin/rustc` exiting non-zero must fail closed, while absent
    // `bin/rustc` records `"no-bin-rustc\0"` cleanly.
    write_exec(&rustc_bin, "#!/usr/bin/env bash\nexit 1\n");
    assert!(compute_rustc_sysroot_digest(&sr).is_err());

    fs::remove_file(&rustc_bin).unwrap();
    let d_no_rustc = compute_rustc_sysroot_digest(&sr).expect("sysroot without bin/rustc");
    assert_ne!(d_no_rustc, d3);
}

#[test]
fn validate_run_plan_and_cli_reject_zero_fuzz_and_empty_selections() {
    assert!(validate_run_plan(false, Some("cat1"), Some(4)).is_err());
    assert!(
        validate_run_plan(false, None, Some(0))
            .expect_err("`--fuzz 0` alone must fail")
            .contains("--fuzz count must be >= 1")
    );
    assert!(
        validate_run_plan(true, None, Some(0))
            .expect_err("`--corpus --fuzz 0` must also fail")
            .contains("--fuzz count must be >= 1")
    );
    assert!(
        validate_run_plan(false, None, None)
            .expect_err("empty selection must fail")
            .contains("no test cases selected")
    );
    assert!(validate_run_plan(true, None, None).is_ok());
    assert!(validate_run_plan(false, None, Some(1)).is_ok());
    assert!(validate_run_plan(true, Some("cat1"), Some(2)).is_ok());
    assert!(
        validate_cli_run_plan(true, None, None, true, false)
            .expect_err("`--shrink` without `--fuzz` must fail")
            .contains("--shrink requires a fuzz campaign")
    );
    assert!(
        validate_cli_run_plan(false, None, Some(2), false, true)
            .expect_err("`--witness-dir` without `--shrink` must fail")
            .contains("--witness-dir requires both --fuzz <N> and --shrink")
    );
    assert!(validate_cli_run_plan(false, None, Some(2), true, true).is_ok());

    let bin = env!("CARGO_BIN_EXE_itree-diff");
    for (cli_args, expected_substr) in [
        (&["--fuzz", "0", "--no-miri", "--no-lean"][..], "--fuzz count must be >= 1"),
        (&["--corpus", "--fuzz", "0", "--no-miri", "--no-lean"][..], "--fuzz count must be >= 1"),
        (&["--shrink", "--no-miri", "--no-lean"][..], "--shrink requires a fuzz campaign"),
        (
            &["--corpus", "--shrink", "--no-miri", "--no-lean"][..],
            "--shrink requires a fuzz campaign",
        ),
    ] {
        let out = std::process::Command::new(bin)
            .args(cli_args)
            .output()
            .expect("spawn itree-diff CLI with invalid run plan");
        assert_eq!(
            out.status.code(),
            Some(2),
            "expected exit code 2 for args {cli_args:?}: stdout={} stderr={}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(!stderr.trim().is_empty(), "expected non-empty stderr for {cli_args:?}");
        assert!(stderr.contains(expected_substr), "stderr={stderr}");
    }
}

#[test]
fn live_lean_cleanup_tracks_legitimate_retirements_and_rejects_corrupt_storage_dead() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let cache_root = resolve_default_cache_root(&anneal_root);
    let session = LeanTraceSession::prepare(&anneal_root, &cache_root).expect("prepare Lean");

    let run_dst_probe = |name: &str,
                         bb0_stmts: &str,
                         dst_local: u32,
                         bb2_stmts: &str,
                         callee_bb0: &str,
                         sched_lit: &str,
                         ext_lit: &str,
                         fuel: u32|
     -> AuthorityRunResult {
        let probe = format!(
            r#"import ITreeDriver
open Trusted.MirAst Trusted.MirSemantics ITreeDriver

def cleanupProbeProg : Program := {{
  bodies := [
    {{
      argumentCount := 2,
      locals := [
        .int .i32 false, -- 0: return
        .int .i32 false, -- 1: arg 1
        .int .i32 false, -- 2: arg 2
        .int .i32 false, -- 3: call dstLocal
        .int .i32 false, -- 4: caller live local
        .int .i32 false  -- 5: cleanup scratch local
      ],
      basicBlocks := [
        {{ statements := [{bb0_stmts}],
          terminator := .call 1 [.copy ⟨1, []⟩, .copy ⟨2, []⟩] ⟨{dst_local}, []⟩ (some 1) (.cleanup 2) }},
        {{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨3, []⟩))],
          terminator := .return_ }},
        {{ statements := [{bb2_stmts}],
          terminator := .unwindResume,
          cleanup := true }}
      ],
      identity := "caller"
    }},
    {{
      argumentCount := 2,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [{callee_bb0}],
      identity := "ext_unwind_callee"
    }}
  ],
  entryDefId := 0,
  pointerWidthBits := 64,
  mirProfileVersion := 1,
  scope := .unit
}}

#eval IO.println (ITreeDriver.runTraceChecked cleanupProbeProg TraceMode.compositionalITree {fuel}
  [Except.ok (.scalar ⟨.i32, false, BitVec.ofNat 128 11⟩),
   Except.ok (.scalar ⟨.i32, false, BitVec.ofNat 128 22⟩)]
  {sched_lit}
  {ext_lit})
"#
        );
        session.run_raw_driver_probe(&probe, name)
    };

    let ret_callee =
        "{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))], terminator := .return_ }";
    let run_cleanup_probe = |name: &str, bb0_stmts: &str, bb2_stmts: &str| -> AuthorityRunResult {
        run_dst_probe(
            name,
            bb0_stmts,
            3,
            bb2_stmts,
            ret_callee,
            "[(some \"ext_unwind_callee\", DriverEnvAction.unwind \"boom\")]",
            "[\"ext_unwind_callee\"]",
            64,
        )
    };

    // (a) Cleanup executing `.storageDead 1` (killing caller argument 1) MUST
    //     report `caller_locals_preserved = false` and `UnsoundAccept`!
    let res_kill_arg =
        run_cleanup_probe("lean-cleanup-kill-arg", ".storageLive 3", ".storageDead 1");
    assert!(res_kill_arg.tool_error.is_none(), "{res_kill_arg:?}");
    assert!(matches!(res_kill_arg.outcome, TerminalOutcome::Unwound { .. }));
    assert!(!res_kill_arg.caller_frame_law.caller_locals_preserved, "{:?}", res_kill_arg);
    assert!(!res_kill_arg.caller_frame_law.padding_mask_respected, "{:?}", res_kill_arg);
    assert!(res_kill_arg.spine.events.contains(&ObservableEvent::CallerFrameCheck {
        point: "ext_unwind_callee:unwind".to_string(),
        locals_preserved: false,
        allocs_preserved: true,
        preserved: false,
    }));

    let clean_unwind_ref = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: res_kill_arg.outcome.clone(),
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    assert!(matches!(
        classify_four_way(
            &clean_unwind_ref,
            &clean_unwind_ref,
            Some(&clean_unwind_ref),
            Some(&res_kill_arg),
            None,
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::UnsoundAccept { .. }
    ));

    // (b) Caller initializes live locals `3` and `4` (`4 != dstLocal`) before
    //     the unwinding call, and cleanup executes `.storageDead 4` -> MUST
    //     report `caller_locals_preserved = false` and `UnsoundAccept`!
    let init_live_3_and_4 = ".storageLive 3, .storageLive 4, .assign ⟨4, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 99)⟩))";
    let res_kill_live = run_cleanup_probe(
        "lean-cleanup-kill-live",
        init_live_3_and_4,
        ".storageDead 3, .storageDead 4",
    );
    assert!(res_kill_live.tool_error.is_none(), "{res_kill_live:?}");
    assert!(matches!(res_kill_live.outcome, TerminalOutcome::Unwound { .. }));
    assert!(!res_kill_live.caller_frame_law.caller_locals_preserved, "{:?}", res_kill_live);
    assert!(!res_kill_live.caller_frame_law.padding_mask_respected, "{:?}", res_kill_live);
    assert!(res_kill_live.spine.events.contains(&ObservableEvent::CallerFrameCheck {
        point: "ext_unwind_callee:unwind".to_string(),
        locals_preserved: false,
        allocs_preserved: true,
        preserved: false,
    }));
    assert!(matches!(
        classify_four_way(
            &clean_unwind_ref,
            &clean_unwind_ref,
            Some(&clean_unwind_ref),
            Some(&res_kill_live),
            None,
            SpineCompareMode::OutcomeOnly,
            None,
        ),
        TraceVerdict::UnsoundAccept { .. }
    ));

    // (c) Caller makes `dstLocal` (`3`) live before call, and cleanup
    //     legitimately transitions `3` from `.immediate none` to `.dead` and
    //     retires cleanup scratch `5` while keeping `4` intact -> satisfied!
    let scratch_cleanup = ".storageDead 3, .storageLive 5, .assign ⟨5, []⟩ (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 77)⟩)), .storageDead 5";
    let res_scratch_ok =
        run_cleanup_probe("lean-cleanup-scratch-ok", init_live_3_and_4, scratch_cleanup);
    assert!(res_scratch_ok.tool_error.is_none(), "{res_scratch_ok:?}");
    assert!(matches!(res_scratch_ok.outcome, TerminalOutcome::Unwound { .. }));
    assert!(
        res_scratch_ok.caller_frame_law.is_satisfied(),
        "{:?}",
        res_scratch_ok.caller_frame_law
    );
    assert!(res_scratch_ok.spine.events.contains(&ObservableEvent::CallerFrameCheck {
        point: "ext_unwind_callee:unwind".to_string(),
        locals_preserved: true,
        allocs_preserved: true,
        preserved: true,
    }));

    // (d)-(h) `.call` into `.dead` or OOB destination local fails at call entry
    // (never `Unwound`, `Aborted`, or `Diverged`).
    let assert_dead_callee = "{ statements := [], terminator := .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true .boundsCheck 0 .continue_ }";
    let res_dead_unsched = run_dst_probe(
        "lean-call-dead-dst-unsched",
        "",
        3,
        ".storageDead 3",
        assert_dead_callee,
        "[]",
        "[]",
        64,
    );
    assert!(
        matches!(
            &res_dead_unsched.outcome,
            TerminalOutcome::FaultUb { detail } if detail.contains("dead local write undefined")
        ),
        "expected dead local FaultUb before callee unwind, got {res_dead_unsched:?}"
    );
    let res_dead_unwind = run_dst_probe(
        "lean-call-dead-dst-unwind",
        "",
        3,
        ".storageDead 3",
        ret_callee,
        "[(some \"ext_unwind_callee\", DriverEnvAction.unwind \"boom\")]",
        "[\"ext_unwind_callee\"]",
        64,
    );
    assert!(
        !matches!(
            res_dead_unwind.outcome,
            TerminalOutcome::Unwound { .. } | TerminalOutcome::Returned { .. }
        ) && res_dead_unwind.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
        "dead-dst unwind schedule must fail closed before unwind, got {res_dead_unwind:?}"
    );
    let res_dead_abort = run_dst_probe(
        "lean-call-dead-dst-abort",
        "",
        3,
        ".storageDead 3",
        ret_callee,
        "[(some \"ext_unwind_callee\", DriverEnvAction.abort \"halt\")]",
        "[\"ext_unwind_callee\"]",
        64,
    );
    assert!(
        !matches!(
            res_dead_abort.outcome,
            TerminalOutcome::Aborted { .. } | TerminalOutcome::Returned { .. }
        ) && res_dead_abort.tool_error.as_deref().is_some_and(|e| e.contains("unconsumed")),
        "dead-dst abort schedule must fail closed before abort, got {res_dead_abort:?}"
    );
    let diverging_callee = "{ statements := [], terminator := .goto 0 }";
    let res_dead_diverge = run_dst_probe(
        "lean-call-dead-dst-diverge",
        "",
        3,
        ".storageDead 3",
        diverging_callee,
        "[]",
        "[]",
        8,
    );
    assert!(
        matches!(
            &res_dead_diverge.outcome,
            TerminalOutcome::FaultUb { detail } if detail.contains("dead local write undefined")
        ),
        "expected dead local FaultUb before intra-crate divergence, got {res_dead_diverge:?}"
    );
    let res_oob_dst = run_dst_probe(
        "lean-call-oob-dst",
        ".storageLive 3",
        99,
        ".storageDead 3",
        ret_callee,
        "[]",
        "[\"ext_unwind_callee\"]",
        64,
    );
    assert!(res_oob_dst.tool_error.is_none(), "{res_oob_dst:?}");
    assert!(
        matches!(
            &res_oob_dst.outcome,
            TerminalOutcome::CaptureRefused { reason }
                if reason.contains("call destination out of bounds")
        ),
        "expected OOB dst CaptureRefused, got {res_oob_dst:?}"
    );

    // (i) Unscheduled `lean_prog_unwind_cleanup` completes normal intra-crate
    //     call return (`1 + 17 + 1 = 19`) matching Rust on non-panicking args.
    let mut unsched_cleanup_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_callee_panic_unwind_cleanup")
        .expect("cat4_callee_panic_unwind_cleanup must exist");
    unsched_cleanup_case.env_schedule = Default::default();
    unsched_cleanup_case.rust_arg_exprs = vec!["1u32".to_string(), "17u32".to_string()];
    unsched_cleanup_case.lean_args = vec![TraceVal::u32(1), TraceVal::u32(17)];
    unsched_cleanup_case.expected_class = ExpectedCaseClass::Agree;
    let rustc_runner = RustcRunner::discover(Some(&session.rust_sysroot))
        .expect("discover rustc for unscheduled cleanup check");
    assert_eq!(rustc_runner.host_target, session.host_target);
    let rust_unsched = rustc_runner.run_dual(&unsched_cleanup_case);
    assert!(rust_unsched.parity_ok, "{rust_unsched:?}");
    let (res_unsched_cleanup, _) =
        session.run_case(&unsched_cleanup_case, LeanTraceMode::CompositionalITree);
    assert!(res_unsched_cleanup.tool_error.is_none(), "{res_unsched_cleanup:?}");
    assert!(
        matches!(
            &res_unsched_cleanup.outcome,
            TerminalOutcome::Returned { ret, .. } if ret == &TraceVal::u32(19)
        ),
        "expected unscheduled lean_prog_unwind_cleanup to return 19, got {res_unsched_cleanup:?}"
    );
    assert!(
        rust_unsched.o0.outcome.semantically_eq(&res_unsched_cleanup.outcome),
        "unscheduled cleanup Rust vs Lean mismatch: {:?} vs {:?}",
        rust_unsched.o0.outcome,
        res_unsched_cleanup.outcome
    );

    // (j) StrictVerbatim `strictLoop` retains the allocation snapshot taken at
    //     call entry and catches mid-callee mutations on non-root return even
    //     when the return step itself performs no allocation mutation.
    let strict_alloc_probe = r#"
import Trusted.MirAst
import Trusted.MirSemantics
import ITreeDriver
open Trusted.MirAst
open Trusted.MirSemantics

def strictAllocProg : Program := {
  bodies := [
    {
      argumentCount := 0,
      locals := [.int .i32 false, .int .i32 false],
      basicBlocks := [{ statements := [], terminator := .return_ }],
      identity := "strict_caller"
    },
    {
      argumentCount := 0,
      locals := [.int .i32 false],
      basicBlocks := [{ statements := [], terminator := .return_ }],
      identity := "strict_callee"
    }
  ],
  entryDefId := 0,
  pointerWidthBits := 64,
  mirProfileVersion := 1,
  scope := .unit
}

def strictBeforeAlloc : Allocation :=
  { allocId := 7, alignLog2 := 0, mutability := .mut, bytes := [.init 0x11 none], live := true }

def strictMutatedAlloc : Allocation :=
  { allocId := 7, alignLog2 := 0, mutability := .mut, bytes := [.init 0x22 none], live := true }

def strictCalleeFrame : FrameState := {
  defId := 1,
  blockIdx := 0,
  stmtIdx := 0,
  locals := [.immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 7⟩))],
  retDst? := some ⟨1, []⟩,
  retTarget? := some 0
}

def strictCallerFrame : FrameState := {
  defId := 0,
  blockIdx := 0,
  stmtIdx := 0,
  locals := [.immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 9⟩)), .immediate none]
}

def strictMidState : State := {
  frames := [strictCalleeFrame, strictCallerFrame],
  callerMem := ⟨[]⟩,
  mem := { nextAllocId := 8, allocations := [strictMutatedAlloc] }
}

def strictEntrySnap : ITreeDriver.StrictCallSnapshot := {
  calleeName := "strict_callee",
  preLocals := strictCallerFrame.locals,
  preMemAllocs := [strictBeforeAlloc]
}

#eval IO.println (ITreeDriver.strictLoop strictAllocProg [] 8 [] [] [strictEntrySnap] 8 strictMidState true true true [] [])
"#;
    let res_strict_alloc = session.run_raw_driver_probe(strict_alloc_probe, "lean-strict-alloc");
    assert!(res_strict_alloc.tool_error.is_none(), "{res_strict_alloc:?}");
    assert!(
        !res_strict_alloc.caller_frame_law.untouched_alloc_bytes_preserved,
        "{res_strict_alloc:?}"
    );
    assert!(
        res_strict_alloc.spine.events.contains(&ObservableEvent::CallerFrameCheck {
            point: "strict_callee:return".to_string(),
            locals_preserved: true,
            allocs_preserved: false,
            preserved: false,
        }),
        "expected failed strict_callee:return alloc check, got {:?}",
        res_strict_alloc.spine.events
    );

    // (k) `applyStrictUnwindChecks` emits chronological `CallUnwind` +
    //     `{callee}:unwind` `CallerFrameCheck` events from inner to outer frame
    //     and flags caller allocation drift on unwind.
    let strict_unwind_probe = r#"
import Trusted.MirAst
import Trusted.MirSemantics
import ITreeDriver
open Trusted.MirAst
open Trusted.MirSemantics

def fLeaf : FrameState := { defId := 2, blockIdx := 0, stmtIdx := 0, locals := [] }
def fMid : FrameState := { defId := 1, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }
def fRoot : FrameState := { defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }
def allocOk : Allocation :=
  { allocId := 3, alignLog2 := 0, mutability := .mut, bytes := [.init 0x44 none], live := true }
def allocDrifted : Allocation :=
  { allocId := 3, alignLog2 := 0, mutability := .mut, bytes := [.init 0x55 none], live := true }
def memNow : MemoryState := { nextAllocId := 4, allocations := [allocDrifted] }
def snaps : List ITreeDriver.StrictCallSnapshot := [
  { calleeName := "strict_inner", preLocals := fMid.locals, preMemAllocs := [allocDrifted] },
  { calleeName := "strict_outer", preLocals := fRoot.locals, preMemAllocs := [allocOk] }
]
def checkRes := ITreeDriver.applyStrictUnwindChecks memNow snaps [fMid, fRoot] true true true [] []

#eval IO.println (
  let (lOk, aOk, pOk, viols, evs) := checkRes
  let evsFinal := ITreeDriver.mkFrameCheckEvent "root_exit" (lOk && pOk) aOk :: evs
  ITreeDriver.finishUnwoundJson "unwound" 16 [] [] lOk aOk pOk viols evsFinal)
"#;
    let res_strict_unwind = session.run_raw_driver_probe(strict_unwind_probe, "lean-strict-unwind");
    assert!(res_strict_unwind.tool_error.is_none(), "{res_strict_unwind:?}");
    assert!(matches!(res_strict_unwind.outcome, TerminalOutcome::Unwound { .. }));
    assert!(!res_strict_unwind.caller_frame_law.untouched_alloc_bytes_preserved);
    assert_eq!(
        res_strict_unwind.spine.events,
        vec![
            ObservableEvent::CallUnwind {
                callee: "strict_inner".to_string(),
                reason: "unwound".to_string(),
            },
            ObservableEvent::CallerFrameCheck {
                point: "strict_inner:unwind".to_string(),
                locals_preserved: true,
                allocs_preserved: true,
                preserved: true,
            },
            ObservableEvent::CallUnwind {
                callee: "strict_outer".to_string(),
                reason: "unwound".to_string(),
            },
            ObservableEvent::CallerFrameCheck {
                point: "strict_outer:unwind".to_string(),
                locals_preserved: true,
                allocs_preserved: false,
                preserved: false,
            },
            ObservableEvent::CallerFrameCheck {
                point: "root_exit".to_string(),
                locals_preserved: true,
                allocs_preserved: false,
                preserved: false,
            },
        ]
    );
}

#[test]
fn full_branches_and_calls_compares_complete_call_events_and_lean_bytes() {
    let base_spine = ObservableSpine {
        events: vec![
            ObservableEvent::CallEnter {
                callee: "helper".to_string(),
                arg_bytes: vec![vec![Some(10), None, None, None, Some(20)]],
                arg_reprs: vec!["Padded{a=10,b=20}".to_string()],
            },
            ObservableEvent::CallReturn {
                callee: "helper".to_string(),
                ret_bytes: vec![Some(42), None, Some(0), Some(0)],
                ret_repr: "Ret(42)".to_string(),
            },
            ObservableEvent::CallerFrameCheck {
                point: "helper:return".to_string(),
                locals_preserved: true,
                allocs_preserved: true,
                preserved: true,
            },
            ObservableEvent::CallUnwind {
                callee: "panicker".to_string(),
                reason: "reason_alpha".to_string(),
            },
            ObservableEvent::BranchTag { block: 0, discr: "1".to_string(), target: 2 },
        ],
    };

    assert!(
        compare_spines(
            "ref",
            &base_spine,
            "cand",
            &base_spine,
            SpineCompareMode::FullBranchesAndCalls
        )
        .is_ok()
    );

    // (a) Divergence in `CallEnter.arg_bytes` (with identical `callee` and
    //     `arg_reprs`) MUST fail BOTH `FullBranchesAndCalls` and
    //     `ObsErasedCallsOnly`!
    let mut bad_arg_bytes = base_spine.clone();
    bad_arg_bytes.events[0] = ObservableEvent::CallEnter {
        callee: "helper".to_string(),
        arg_bytes: vec![vec![Some(10), Some(0xFF), None, None, Some(20)]],
        arg_reprs: vec!["Padded{a=10,b=20}".to_string()],
    };
    let err_arg = compare_spines(
        "ref",
        &base_spine,
        "cand",
        &bad_arg_bytes,
        SpineCompareMode::FullBranchesAndCalls,
    )
    .expect_err("FullBranchesAndCalls must reject CallEnter.arg_bytes mismatch");
    assert!(err_arg.contains("full call spine mismatch"), "{err_arg}");
    let err_arg_erased = compare_spines(
        "ref",
        &base_spine,
        "cand",
        &bad_arg_bytes,
        SpineCompareMode::ObsErasedCallsOnly,
    )
    .expect_err("ObsErasedCallsOnly must reject CallEnter.arg_bytes mismatch");
    assert!(err_arg_erased.contains("obs-erased observable spine mismatch"), "{err_arg_erased}");

    // (b) Divergence in `CallReturn.ret_bytes` (with identical `callee` and
    //     `ret_repr`) MUST fail BOTH `FullBranchesAndCalls` and
    //     `ObsErasedCallsOnly`!
    let mut bad_ret_bytes = base_spine.clone();
    bad_ret_bytes.events[1] = ObservableEvent::CallReturn {
        callee: "helper".to_string(),
        ret_bytes: vec![Some(42), Some(0), Some(0), Some(0)],
        ret_repr: "Ret(42)".to_string(),
    };
    let err_ret = compare_spines(
        "ref",
        &base_spine,
        "cand",
        &bad_ret_bytes,
        SpineCompareMode::FullBranchesAndCalls,
    )
    .expect_err("FullBranchesAndCalls must reject CallReturn.ret_bytes mismatch");
    assert!(err_ret.contains("full call spine mismatch"), "{err_ret}");
    let err_ret_erased = compare_spines(
        "ref",
        &base_spine,
        "cand",
        &bad_ret_bytes,
        SpineCompareMode::ObsErasedCallsOnly,
    )
    .expect_err("ObsErasedCallsOnly must reject CallReturn.ret_bytes mismatch");
    assert!(err_ret_erased.contains("obs-erased observable spine mismatch"), "{err_ret_erased}");

    // (c) Unrelated `CallUnwind.reason` (`"reason_alpha"` vs `"reason_beta"`)
    //     MUST fail both `FullBranchesAndCalls` and `ObsErasedCallsOnly`,
    //     whereas normalized MIR `.assert` unwind equivalents pass
    //     `ObsErasedCallsOnly` while failing `FullBranchesAndCalls`.
    let mut bad_unwind_reason = base_spine.clone();
    bad_unwind_reason.events[3] = ObservableEvent::CallUnwind {
        callee: "panicker".to_string(),
        reason: "reason_beta".to_string(),
    };
    let err_unw = compare_spines(
        "ref",
        &base_spine,
        "cand",
        &bad_unwind_reason,
        SpineCompareMode::FullBranchesAndCalls,
    )
    .expect_err("FullBranchesAndCalls must reject CallUnwind.reason mismatch");
    assert!(err_unw.contains("full call spine mismatch"), "{err_unw}");
    assert!(
        compare_spines(
            "ref",
            &base_spine,
            "cand",
            &bad_unwind_reason,
            SpineCompareMode::ObsErasedCallsOnly,
        )
        .is_err()
    );
    let mut rust_bounds_spine = base_spine.clone();
    rust_bounds_spine.events[3] = ObservableEvent::CallUnwind {
        callee: "panicker".to_string(),
        reason: "index out of bounds: the len is 2 but the index is 9".to_string(),
    };
    let mut lean_bounds_spine = base_spine.clone();
    lean_bounds_spine.events[3] = ObservableEvent::CallUnwind {
        callee: "panicker".to_string(),
        reason: "assert:bounds_check".to_string(),
    };
    assert!(
        compare_spines(
            "rustc",
            &rust_bounds_spine,
            "lean",
            &lean_bounds_spine,
            SpineCompareMode::ObsErasedCallsOnly,
        )
        .is_ok()
    );
    assert!(
        compare_spines(
            "rustc",
            &rust_bounds_spine,
            "lean",
            &lean_bounds_spine,
            SpineCompareMode::FullBranchesAndCalls,
        )
        .is_err()
    );

    // Lean JSON parser requires `arg_bytes` on `call_enter` and `ret_bytes` on
    // `call_return` (no silent empty default!).
    let valid_lean_calls = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"37"},"detail":"","fuel":8,"boundary_slots":[[16,37,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"call_enter","callee":"ext_transform_u32","arg_bytes":[[10,0,0,0]],"arg_reprs":["10"]},{"kind":"call_return","callee":"ext_transform_u32","ret_bytes":[37,0,0,0],"ret_repr":"37"}]}"#;
    let parsed_lean = parse_lean_trace_output("lean", valid_lean_calls, "", 1);
    assert!(parsed_lean.tool_error.is_none(), "{parsed_lean:?}");
    assert_eq!(
        parsed_lean.spine.erased_call_spine(),
        vec![
            ObservableEvent::CallEnter {
                callee: "ext_transform_u32".to_string(),
                arg_bytes: vec![vec![Some(10), Some(0), Some(0), Some(0)]],
                arg_reprs: vec!["10".to_string()],
            },
            ObservableEvent::CallReturn {
                callee: "ext_transform_u32".to_string(),
                ret_bytes: vec![Some(37), Some(0), Some(0), Some(0)],
                ret_repr: "37".to_string(),
            },
        ]
    );

    let missing_arg_bytes = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"37"},"detail":"","fuel":8,"boundary_slots":[[16,37,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"call_enter","callee":"ext_transform_u32","arg_reprs":["10"]}]}"#;
    assert!(parse_lean_trace_output("lean", missing_arg_bytes, "", 1).tool_error.is_some());

    let missing_ret_bytes = r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","width":"i32","signed":false,"bits":"37"},"detail":"","fuel":8,"boundary_slots":[[16,37,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[{"kind":"call_return","callee":"ext_transform_u32","ret_repr":"37"}]}"#;
    assert!(parse_lean_trace_output("lean", missing_ret_bytes, "", 1).tool_error.is_some());
}

#[cfg(unix)]
#[test]
fn explicit_miri_sysroot_requires_matching_ready_stamp_and_rejects_conflicting_overrides() {
    use std::{ffi::OsStr, os::unix::ffi::OsStrExt};

    let tmp = tempfile::tempdir().unwrap();
    let sr = tmp.path().join("active_sysroot");
    let cache_dir = tmp.path().join("miri_cache");
    let explicit_miri_sr = tmp.path().join("explicit_miri_target_sysroot");
    fs::create_dir_all(sr.join("bin")).unwrap();
    fs::create_dir_all(sr.join("lib")).unwrap();
    fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/core/src")).unwrap();
    fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/alloc/src")).unwrap();
    fs::create_dir_all(explicit_miri_sr.join("lib/rustlib")).unwrap();

    let canon_sr = fs::canonicalize(&sr).unwrap();
    let canon_explicit_miri_sr = fs::canonicalize(&explicit_miri_sr).unwrap();

    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    let rustc_bin = sr.join("bin/rustc");
    let miri_bin = sr.join("bin/miri");
    let cargo_bin = sr.join("bin/cargo");
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {}\\n'\n",
            canon_sr.display(),
            mock_host,
        ),
    );
    write_exec(
        &miri_bin,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'miri 0.1.0 (mock 2026-05-30)\\n'\n",
            canon_sr.display()
        ),
    );
    write_exec(&cargo_bin, "#!/usr/bin/env bash\nexit 0\n");
    fs::write(sr.join("lib/librustc_driver-mock.so"), b"driver-a").unwrap();

    let rust_src = sr.join("lib/rustlib/src/rust");
    fs::write(rust_src.join("library/Cargo.lock"), "version = 4\n").unwrap();
    fs::write(
        rust_src.join("library/core/Cargo.toml"),
        "[package]\nname = \"core\"\nversion = \"0.0.0\"\n",
    )
    .unwrap();
    fs::write(
        rust_src.join("library/alloc/Cargo.toml"),
        "[package]\nname = \"alloc\"\nversion = \"0.0.0\"\n",
    )
    .unwrap();
    let core_lib_rs = rust_src.join("library/core/src/lib.rs");
    fs::write(&core_lib_rs, "// core v1\n").unwrap();

    // (a) Valid `lib/rustlib` directory WITHOUT `.anneal-itree-miri-ready`
    //     MUST fail closed with `MiriAvailability::InvalidConfig`!
    let probe_missing_stamp = MiriRunner::probe_with_env(&cache_dir, Some(&sr), |k| {
        if k == "ANNEAL_ITREE_MIRI_SYSROOT" {
            Some(explicit_miri_sr.as_os_str().to_os_string())
        } else {
            None
        }
    });
    assert!(
        matches!(
            &probe_missing_stamp,
            MiriAvailability::InvalidConfig { reason }
                if reason.contains("failed MiriSysrootIdentity")
        ),
        "expected InvalidConfig for unstamped explicit sysroot, got {probe_missing_stamp:?}"
    );

    // (b) Explicit sysroot with `.anneal-itree-miri-ready` ONLY (missing
    //     `.anneal-itree-miri-artifacts.json`) fails closed (`InvalidConfig`);
    //     writing valid artifacts + manifest yields `Available`, then mutating
    //     `core/src/lib.rs` fails closed as `InvalidConfig`.
    let id_v1 = MiriSysrootIdentity::compute(&canon_sr, &miri_bin, Some(&cargo_bin)).unwrap();
    let ready_stamp = explicit_miri_sr.join(".anneal-itree-miri-ready");
    id_v1.write_ready_stamp(&ready_stamp).unwrap();

    let probe_explicit = || {
        MiriRunner::probe_with_env(&cache_dir, Some(&sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_SYSROOT" {
                Some(explicit_miri_sr.as_os_str().to_os_string())
            } else {
                None
            }
        })
    };
    let probe_missing_artifacts = probe_explicit();
    assert!(
        matches!(probe_missing_artifacts, MiriAvailability::InvalidConfig { .. }),
        "expected InvalidConfig when .anneal-itree-miri-artifacts.json missing, got {probe_missing_artifacts:?}"
    );

    let target_lib_dir = explicit_miri_sr.join("lib/rustlib").join(&mock_host).join("lib");
    fs::create_dir_all(&target_lib_dir).unwrap();
    fs::write(target_lib_dir.join("libcore-1.rlib"), b"mock-core-rlib").unwrap();
    fs::write(target_lib_dir.join("liballoc-1.rmeta"), b"mock-alloc-rmeta").unwrap();
    id_v1.write_built_artifacts_manifest(&explicit_miri_sr).unwrap();

    let probe_valid = probe_explicit();
    match probe_valid {
        MiriAvailability::Available(runner) => {
            assert_eq!(runner.miri_sysroot, canon_explicit_miri_sr);
        }
        other => panic!("expected Available when both stamps match identity, got {other:?}"),
    }

    fs::write(&core_lib_rs, "// core v2 mutated after sysroot build\n").unwrap();
    let probe_stale_stamp = probe_explicit();
    assert!(
        matches!(
            &probe_stale_stamp,
            MiriAvailability::InvalidConfig { reason }
                if reason.contains("failed MiriSysrootIdentity")
        ),
        "expected InvalidConfig for stale explicit sysroot stamp, got {probe_stale_stamp:?}"
    );

    // (c) Setting `ANNEAL_ITREE_MIRI_BIN` and `ANNEAL_ITREE_MIRI_TOOLCHAIN`
    //     together or passing non-UTF-8 `ANNEAL_ITREE_MIRI_TOOLCHAIN` fails
    //     closed with `InvalidConfig`!
    let conflict_err = resolve_miri_coordinates_with_env(Some(&sr), |k| match k {
        "ANNEAL_ITREE_MIRI_BIN" => Some(miri_bin.as_os_str().to_os_string()),
        "ANNEAL_ITREE_MIRI_TOOLCHAIN" => Some("nightly-2026-05-31".into()),
        _ => None,
    })
    .expect_err("simultaneous ANNEAL_ITREE_MIRI_BIN and ANNEAL_ITREE_MIRI_TOOLCHAIN must fail");
    assert!(conflict_err.is_invalid_config());

    let bad_utf8_tc = OsStr::from_bytes(b"nightly-\xff-invalid").to_os_string();
    let utf8_err = resolve_miri_coordinates_with_env(Some(&sr), |k| {
        if k == "ANNEAL_ITREE_MIRI_TOOLCHAIN" { Some(bad_utf8_tc.clone()) } else { None }
    })
    .expect_err("non-UTF-8 ANNEAL_ITREE_MIRI_TOOLCHAIN must fail closed");
    assert!(utf8_err.is_invalid_config());
    assert!(utf8_err.reason().contains("invalid UTF-8"), "{utf8_err}");
}

#[cfg(unix)]
#[test]
fn lean_cache_key_tracks_lean_binary_prefix_libs_and_stdlib_tree() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let tmp = tempfile::tempdir().unwrap();
    let lean_prefix = tmp.path().join("mock_lean_prefix");
    let bin_dir = lean_prefix.join("bin");
    let lib_dir = lean_prefix.join("lib");
    let stdlib_dir = lib_dir.join("lean");
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(stdlib_dir.join("Init")).unwrap();

    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    let lean_bin = bin_dir.join("lean");
    let prelude_olean = stdlib_dir.join("Init/Prelude.olean");
    let lean_shared_so = stdlib_dir.join("libleanshared.so");
    let top_llvm_so = lib_dir.join("libLLVM-mock.so");

    write_exec(
        &lean_bin,
        "#!/usr/bin/env bash\n# lean build-1\nprintf 'Lean (version 4.34.1, mock)\\n'\n",
    );
    fs::write(&prelude_olean, b"prelude-olean-bytes-v1").unwrap();
    fs::write(&lean_shared_so, b"leanshared-bytes-v1").unwrap();
    fs::write(&top_llvm_so, b"llvm-mock-bytes-v1").unwrap();

    let key0 =
        compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).expect("initial Lean key");
    assert_eq!(compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap(), key0);

    // (a) Replacing `bin/lean` bytes with identical `--version` changes key!
    write_exec(
        &lean_bin,
        "#!/usr/bin/env bash\n# lean build-2-rebuilt-in-place\nprintf 'Lean (version 4.34.1, mock)\\n'\n",
    );
    let key_bin = compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap();
    assert_ne!(key_bin, key0, "Lean cache key must change when bin/lean bytes change");

    // (b) Mutating `lib/lean/Init/Prelude.olean` bytes changes the key!
    fs::write(&prelude_olean, b"prelude-olean-bytes-v2-modified").unwrap();
    let key_prelude = compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap();
    assert_ne!(
        key_prelude, key_bin,
        "Lean cache key must change when Init/Prelude.olean bytes change"
    );

    // (c) Mutating `lib/lean/libleanshared.so` bytes changes the key!
    fs::write(&lean_shared_so, b"leanshared-bytes-v2-modified").unwrap();
    let key_shared = compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap();
    assert_ne!(
        key_shared, key_prelude,
        "Lean cache key must change when libleanshared.so bytes change"
    );

    // (d) Mutating `<lean_prefix>/lib/libLLVM-mock.so` changes the key!
    fs::write(&top_llvm_so, b"llvm-mock-bytes-v2-modified").unwrap();
    let key_llvm = compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap();
    assert_ne!(
        key_llvm, key_shared,
        "Lean cache key must change when top-level <lean_prefix>/lib shared libs change"
    );

    // (e) Escaping symlink inside `lib/lean` fails closed!
    let outside = tmp.path().join("outside.olean");
    fs::write(&outside, b"outside").unwrap();
    let bad_link = stdlib_dir.join("Init/Escaped.olean");
    std::os::unix::fs::symlink(&outside, &bad_link).unwrap();
    assert!(compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).is_err());
}

#[cfg(unix)]
#[test]
fn mir_eval_explicit_override_rejects_invalid_paths_and_engine_fails_closed() {
    let tmp = tempfile::tempdir().unwrap();
    let missing_path = tmp.path().join("does-not-exist-mir-eval");
    let dir_path = tmp.path().join("mir-eval-dir");
    fs::create_dir_all(&dir_path).unwrap();
    let non_exec_file = tmp.path().join("non-exec-mir-eval");
    fs::write(&non_exec_file, "#!/usr/bin/env bash\nexit 0\n").unwrap();
    let mut perms = fs::metadata(&non_exec_file).unwrap().permissions();
    perms.set_mode(0o644);
    fs::set_permissions(&non_exec_file, perms).unwrap();

    // Ambient absence (`ANNEAL_MIR_EVAL_BIN` unset, including a non-executable
    // file on `PATH`) stays `MirEvalAvailability::Unavailable`.
    let path_with_non_exec = tmp.path().join("non_exec_path_dir");
    fs::create_dir_all(&path_with_non_exec).unwrap();
    let path_cand = path_with_non_exec.join("anneal-mir-eval");
    fs::write(&path_cand, "not executable\n").unwrap();
    let mut cand_perms = fs::metadata(&path_cand).unwrap().permissions();
    cand_perms.set_mode(0o644);
    fs::set_permissions(&path_cand, cand_perms).unwrap();

    assert!(matches!(
        MirEvalAdapter::probe_with_env(|_| None),
        MirEvalAvailability::Unavailable { .. }
    ));
    assert!(matches!(
        MirEvalAdapter::probe_with_env(|k| {
            if k == "PATH" { Some(path_with_non_exec.as_os_str().to_os_string()) } else { None }
        }),
        MirEvalAvailability::Unavailable { .. }
    ));

    // Explicit `ANNEAL_MIR_EVAL_BIN` override with empty string, missing path,
    // directory, or non-executable file MUST return `InvalidConfig`!
    for bad_val in [
        std::ffi::OsString::new(),
        missing_path.as_os_str().to_os_string(),
        dir_path.as_os_str().to_os_string(),
        non_exec_file.as_os_str().to_os_string(),
    ] {
        let probed = MirEvalAdapter::probe_with_env(|k| {
            if k == "ANNEAL_MIR_EVAL_BIN" { Some(bad_val.clone()) } else { None }
        });
        assert!(
            matches!(probed, MirEvalAvailability::InvalidConfig { .. }),
            "expected InvalidConfig for ANNEAL_MIR_EVAL_BIN={bad_val:?}, got {probed:?}"
        );
    }

    // `DifferentialEngine::prepare_with_env` fails closed on invalid
    // `ANNEAL_MIR_EVAL_BIN` and succeeds when `ANNEAL_MIR_EVAL_BIN` is unset.
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_lean = false;
    cfg.enable_miri = false;
    cfg.require_miri = false;

    let err = match DifferentialEngine::prepare_with_env(cfg.clone(), |k| match k {
        "ANNEAL_MIR_EVAL_BIN" => Some(missing_path.as_os_str().to_os_string()),
        _ => env::var_os(k),
    }) {
        Ok(_) => {
            panic!("DifferentialEngine::prepare_with_env must fail on bad ANNEAL_MIR_EVAL_BIN")
        }
        Err(e) => e,
    };
    assert!(err.contains("invalid ANNEAL_MIR_EVAL_BIN configuration"), "got: {err}");

    let ok_engine = DifferentialEngine::prepare_with_env(cfg.clone(), |k| {
        if k == "ANNEAL_MIR_EVAL_BIN" { None } else { env::var_os(k) }
    })
    .expect("engine should initialize cleanly when ANNEAL_MIR_EVAL_BIN is unset");
    assert!(ok_engine.mir_eval.is_none());
    assert_eq!(ok_engine.mir_eval_status, "disabled (--no-lean)");

    // Valid explicit `ANNEAL_MIR_EVAL_BIN` paired with `enable_lean = false`
    // (`--no-lean`) MUST fail closed instead of silently skipping evaluation;
    // ambient `PATH` `anneal-mir-eval` under `--no-lean` reports `disabled`
    // (never `available`).
    let valid_dir = tmp.path().join("valid_mir_eval_bin_dir");
    fs::create_dir_all(&valid_dir).unwrap();
    let valid_exec = valid_dir.join("anneal-mir-eval");
    fs::write(&valid_exec, "#!/usr/bin/env bash\nexit 0\n").unwrap();
    let mut vperms = fs::metadata(&valid_exec).unwrap().permissions();
    vperms.set_mode(0o755);
    fs::set_permissions(&valid_exec, vperms).unwrap();

    let conflict_err = match DifferentialEngine::prepare_with_env(cfg.clone(), |k| match k {
        "ANNEAL_MIR_EVAL_BIN" => Some(valid_exec.as_os_str().to_os_string()),
        _ => env::var_os(k),
    }) {
        Ok(_) => panic!(
            "DifferentialEngine::prepare_with_env must reject explicit ANNEAL_MIR_EVAL_BIN under --no-lean"
        ),
        Err(e) => e,
    };
    assert!(
        conflict_err.contains("conflicting configuration: explicit ANNEAL_MIR_EVAL_BIN"),
        "got: {conflict_err}"
    );

    let joined_path = env::join_paths(std::iter::once(valid_dir.clone()).chain(
        env::var_os("PATH").into_iter().flat_map(|p| env::split_paths(&p).collect::<Vec<_>>()),
    ))
    .unwrap();
    let path_engine = DifferentialEngine::prepare_with_env(cfg, |k| match k {
        "ANNEAL_MIR_EVAL_BIN" => None,
        "PATH" => Some(joined_path.clone()),
        _ => env::var_os(k),
    })
    .expect("ambient PATH anneal-mir-eval should stay disabled under --no-lean");
    assert!(path_engine.mir_eval.is_none());
    assert_eq!(path_engine.mir_eval_status, "disabled (--no-lean)");

    // End-to-end CLI check via `DifferentialEngine::prepare`: setting invalid
    // `ANNEAL_MIR_EVAL_BIN` OR valid `ANNEAL_MIR_EVAL_BIN` with `--no-lean`
    // exits code 2 with configuration error on stderr.
    let bin = env!("CARGO_BIN_EXE_itree-diff");
    let out = std::process::Command::new(bin)
        .args(["--filter", "cat1_clamp", "--no-miri", "--no-lean"])
        .env_remove("ANNEAL_ITREE_REQUIRE_MIRI")
        .env("ANNEAL_MIR_EVAL_BIN", &missing_path)
        .output()
        .expect("spawn itree-diff CLI with invalid ANNEAL_MIR_EVAL_BIN");
    assert_eq!(out.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("invalid ANNEAL_MIR_EVAL_BIN configuration"), "stderr={stderr}");

    let out_conflict = std::process::Command::new(bin)
        .args(["--filter", "cat1_clamp", "--no-miri", "--no-lean"])
        .env_remove("ANNEAL_ITREE_REQUIRE_MIRI")
        .env("ANNEAL_MIR_EVAL_BIN", &valid_exec)
        .output()
        .expect("spawn itree-diff CLI with valid ANNEAL_MIR_EVAL_BIN + --no-lean");
    assert_eq!(out_conflict.status.code(), Some(2));
    let conflict_stderr = String::from_utf8_lossy(&out_conflict.stderr);
    assert!(
        conflict_stderr.contains("conflicting configuration: explicit ANNEAL_MIR_EVAL_BIN"),
        "stderr={conflict_stderr}"
    );
}

#[cfg(unix)]
#[test]
fn host_target_validation_accepts_64bit_le_and_rejects_32bit_be_or_cross_arch() {
    for good in [
        "x86_64-unknown-linux-gnu",
        "aarch64-unknown-linux-gnu",
        "aarch64-apple-darwin",
        "riscv64gc-unknown-linux-gnu",
        "loongarch64-unknown-linux-gnu",
        "powerpc64le-unknown-linux-gnu",
    ] {
        let vv = format!("rustc 1.98.0-nightly\nhost: {good}\n");
        assert_eq!(parse_and_validate_host_target_triple(&vv).unwrap(), good);
    }

    for bad in [
        "",
        "rustc 1.98.0-nightly\n",
        "rustc 1.98.0-nightly\nhost: i686-unknown-linux-gnu\n",
        "rustc 1.98.0-nightly\nhost: armv7-unknown-linux-gnueabihf\n",
        "rustc 1.98.0-nightly\nhost: aarch64_be-unknown-linux-gnu\n",
        "rustc 1.98.0-nightly\nhost: s390x-unknown-linux-gnu\n",
        "rustc 1.98.0-nightly\nhost: powerpc64-unknown-linux-gnu\n",
        "rustc 1.98.0-nightly\nhost: x86_64/evil\n",
    ] {
        assert!(
            parse_and_validate_host_target_triple(bad).is_err(),
            "expected invalid/unsupported host target for {bad:?}"
        );
    }

    let native_triple = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    assert!(
        validate_host_target_matches_platform(&native_triple, env::consts::ARCH, "linux").is_ok()
    );
    if env::consts::OS == "linux" {
        assert!(validate_host_target_matches_native_arch(&native_triple).is_ok());
    }
    let foreign_triple = if env::consts::ARCH == "x86_64" {
        "aarch64-unknown-linux-gnu"
    } else {
        "x86_64-unknown-linux-gnu"
    };
    let skew_err = validate_host_target_matches_native_arch(foreign_triple)
        .expect_err("cross-arch host target must be rejected for native RustcRunner execution");
    assert!(skew_err.contains("toolchain target architecture mismatch"), "got: {skew_err}");

    // Same-architecture foreign-OS triples MUST fail closed on native hosts!
    for same_arch_foreign_os in [
        format!("{}-pc-windows-msvc", env::consts::ARCH),
        format!("{}-apple-darwin", env::consts::ARCH),
        format!("{}-unknown-freebsd", env::consts::ARCH),
        format!("{}-unknown-none", env::consts::ARCH),
    ] {
        let os_err = validate_host_target_matches_platform(
            &same_arch_foreign_os,
            env::consts::ARCH,
            "linux",
        )
        .expect_err("same-arch foreign OS target must fail closed on linux");
        assert!(os_err.contains("toolchain target OS mismatch"), "got: {os_err}");
    }

    let tmp = tempfile::tempdir().unwrap();
    let foreign_sr = tmp.path().join("foreign_target_sr");
    fs::create_dir_all(foreign_sr.join("bin")).unwrap();
    fs::create_dir_all(foreign_sr.join("lib")).unwrap();
    let canon_foreign = fs::canonicalize(&foreign_sr).unwrap();
    let wrong_os_triple = if cfg!(windows) {
        format!("{}-unknown-linux-gnu", env::consts::ARCH)
    } else {
        format!("{}-pc-windows-msvc", env::consts::ARCH)
    };
    let foreign_rustc = foreign_sr.join("bin/rustc");
    fs::write(
        &foreign_rustc,
        format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then printf '%s\\n' '{}'; exit 0; fi\nprintf 'rustc 1.98.0-nightly\\nhost: {}\\n'\n",
            canon_foreign.display(),
            wrong_os_triple,
        ),
    )
    .unwrap();
    let mut perms = fs::metadata(&foreign_rustc).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&foreign_rustc, perms).unwrap();
    let disc_err = RustcRunner::discover_with_env(None, |k| {
        if k == "ANNEAL_ITREE_RUSTC" {
            Some(foreign_rustc.as_os_str().to_os_string())
        } else {
            None
        }
    })
    .expect_err("RustcRunner::discover must reject same-arch foreign-OS target");
    assert!(disc_err.contains("toolchain target OS mismatch"), "got: {disc_err}");
}

#[test]
fn metamorphic_duality_fails_on_original_authority_tool_error_or_preservation_violation() {
    let ok_out =
        TerminalOutcome::Returned { ret: TraceVal::u32(42), mem_digest: "deadbeef".to_string() };
    let mk_ok = |name: &str| AuthorityRunResult {
        authority: name.to_string(),
        outcome: ok_out.clone(),
        spine: Default::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let ok_dual = RustcDualResult {
        o0: mk_ok("rustc-O0"),
        o2: mk_ok("rustc-O2"),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };

    // Baseline passes when all original and twin authorities succeed and agree.
    let base_rec = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&mk_ok("miri")),
        &mk_ok("lean-called"),
        &ok_dual,
        Some(&mk_ok("miri-twin")),
        mk_ok("lean-inlined"),
    );
    assert_eq!(base_rec.status, MetamorphicStatus::Passed);
    assert!(base_rec.duality_holds);

    // 1. Original `rustc-O2` reporting a `tool_error` while `rustc-O0` and the
    //    inlined twin succeed MUST mark metamorphic status `Failed`.
    let mut bad_o2_dual = ok_dual.clone();
    bad_o2_dual.o2 = AuthorityRunResult::tool_error("rustc-O2", "compiler ICE at -O2");
    bad_o2_dual.parity_ok = false;
    bad_o2_dual.mismatch_detail = Some("tool error".to_string());
    let rec_o2_err = evaluate_metamorphic_duality(
        &bad_o2_dual,
        Some(&mk_ok("miri")),
        &mk_ok("lean-called"),
        &ok_dual,
        Some(&mk_ok("miri-twin")),
        mk_ok("lean-inlined"),
    );
    assert_eq!(rec_o2_err.status, MetamorphicStatus::Failed);
    assert!(!rec_o2_err.duality_holds);
    assert_eq!(rec_o2_err.tool_error.as_ref().map(|(a, _)| a.as_str()), Some("rustc-O2"));

    // 2. Original `miri` reporting a `tool_error` marks status `Failed`.
    let bad_miri = AuthorityRunResult::tool_error("miri", "miri ICE");
    let rec_miri_err = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&bad_miri),
        &mk_ok("lean-called"),
        &ok_dual,
        Some(&mk_ok("miri-twin")),
        mk_ok("lean-inlined"),
    );
    assert_eq!(rec_miri_err.status, MetamorphicStatus::Failed);
    assert!(!rec_miri_err.duality_holds);
    assert_eq!(rec_miri_err.tool_error.as_ref().map(|(a, _)| a.as_str()), Some("miri"));

    // 3. Original `CallerFrameLaw` violation on `called_miri` MUST mark
    //    metamorphic status `Failed`.
    let mut bad_miri_pres = mk_ok("miri");
    bad_miri_pres.caller_frame_law = CallerFrameLaw {
        caller_locals_preserved: false,
        untouched_alloc_bytes_preserved: true,
        padding_mask_respected: true,
        violations: vec!["corrupted caller frame".to_string()],
    };
    let rec_miri_pres = evaluate_metamorphic_duality(
        &ok_dual,
        Some(&bad_miri_pres),
        &mk_ok("lean-called"),
        &ok_dual,
        Some(&mk_ok("miri-twin")),
        mk_ok("lean-inlined"),
    );
    assert_eq!(rec_miri_pres.status, MetamorphicStatus::Failed);
    assert!(!rec_miri_pres.duality_holds);
    assert_eq!(rec_miri_pres.inlined_miri_matched, Some(false));

    // 4. `evaluate_metamorphic_duality` MUST enforce UB-cause compatibility
    //    between Miri and Lean on both legs rather than accepting arbitrary
    //    `FaultUb`.
    let mk_with = |name: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: name.to_string(),
        outcome,
        spine: Default::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let skipped_ub_dual = RustcDualResult::skipped_for_ub("ub");
    let shift_miri = mk_with(
        "miri",
        TerminalOutcome::FaultUb {
            detail: "error: Undefined Behavior: overflowing shift by 32".to_string(),
        },
    );
    let lean_wrong_ub = mk_with(
        "lean-inlined",
        TerminalOutcome::FaultUb { detail: "entering unreachable code".to_string() },
    );
    let lean_shift_ub = mk_with(
        "lean-inlined",
        TerminalOutcome::FaultUb { detail: "unchecked shift overflow".to_string() },
    );
    let lean_cons =
        mk_with("lean-called", TerminalOutcome::CaptureRefused { reason: "call".to_string() });

    let rec_ub_mismatch = evaluate_metamorphic_duality(
        &skipped_ub_dual,
        Some(&shift_miri),
        &lean_cons,
        &skipped_ub_dual,
        Some(&shift_miri),
        lean_wrong_ub,
    );
    assert_eq!(rec_ub_mismatch.status, MetamorphicStatus::Failed);
    assert!(!rec_ub_mismatch.duality_holds);
    assert!(
        rec_ub_mismatch.failed_relations.iter().any(|r| r == "inlined_miri_vs_lean_ub"),
        "{rec_ub_mismatch:?}"
    );

    let rec_ub_match = evaluate_metamorphic_duality(
        &skipped_ub_dual,
        Some(&shift_miri),
        &lean_shift_ub,
        &skipped_ub_dual,
        Some(&shift_miri),
        lean_shift_ub.clone(),
    );
    assert_eq!(rec_ub_match.status, MetamorphicStatus::Passed);
    assert!(rec_ub_match.duality_holds);

    // 5. On `skipped_for_ub` without Miri, accepting or `Diverged` Lean
    //    outcomes on `inlined_lean` MUST fail even when `called_lean` refused.
    for bad_outcome in [ok_out, TerminalOutcome::Diverged { fuel: 64 }] {
        let rec_no_miri_accept = evaluate_metamorphic_duality(
            &skipped_ub_dual,
            None,
            &lean_cons,
            &skipped_ub_dual,
            None,
            mk_with("lean-inlined", bad_outcome),
        );
        assert_eq!(rec_no_miri_accept.status, MetamorphicStatus::Failed);
        assert!(!rec_no_miri_accept.duality_holds);
        assert!(
            rec_no_miri_accept
                .failed_relations
                .iter()
                .any(|r| r == "inlined_skipped_ub_lean_accept"),
            "{rec_no_miri_accept:?}"
        );
    }

    let rec_no_miri_cons = evaluate_metamorphic_duality(
        &skipped_ub_dual,
        None,
        &lean_cons,
        &skipped_ub_dual,
        None,
        mk_with("lean-inlined", TerminalOutcome::CaptureRefused { reason: "ub".to_string() }),
    );
    assert!(
        matches!(rec_no_miri_cons.status, MetamorphicStatus::SkippedConservative { .. }),
        "{rec_no_miri_cons:?}"
    );
}

#[cfg(unix)]
#[test]
fn discovered_miri_in_active_sysroot_fails_closed_when_preparation_fails() {
    let tmp = tempfile::tempdir().unwrap();
    let sr = tmp.path().join("broken_miri_sysroot");
    let cache_dir = tmp.path().join("miri_cache");
    fs::create_dir_all(sr.join("bin")).unwrap();
    fs::create_dir_all(sr.join("lib")).unwrap();
    let canon_sr = fs::canonicalize(&sr).unwrap();
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);

    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    write_exec(
        &sr.join("bin/rustc"),
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'rustc 1.98.0-nightly (mock)\\nhost: {}\\n'\n",
            canon_sr.display(),
            mock_host,
        ),
    );
    write_exec(
        &sr.join("bin/miri"),
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'miri 0.1.0 (mock)\\n'\n",
            canon_sr.display(),
        ),
    );

    // `bin/miri` WAS discovered in `active_sysroot` without explicit overrides,
    // but `lib/rustlib/src/rust` (`rust-src`) is missing. `probe_with_env`
    // MUST return `InvalidConfig` (never `Unavailable`) so `prepare`
    // fails closed even when `require_miri == false`!
    let probed = MiriRunner::probe_with_env(&cache_dir, Some(&sr), |_| None);
    assert!(
        matches!(probed, MiriAvailability::InvalidConfig { .. }),
        "discovered Miri failing setup/identity must return InvalidConfig, got {probed:?}"
    );

    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.cache_root = cache_dir;
    cfg.enable_lean = false;
    cfg.enable_miri = true;
    cfg.require_miri = false;
    let rustc_override = sr.join("bin/rustc");
    let prep_err = match DifferentialEngine::prepare_with_env(cfg, |k| {
        if k == "ANNEAL_ITREE_RUSTC" {
            Some(rustc_override.as_os_str().to_os_string())
        } else {
            None
        }
    }) {
        Ok(_) => panic!("DifferentialEngine::prepare must fail closed when discovered Miri fails"),
        Err(e) => e,
    };
    assert!(prep_err.contains("invalid Miri configuration"), "got: {prep_err}");
}

#[test]
fn parse_miri_run_output_requires_nonzero_exit_for_ub_diagnostic() {
    let auth_tok = "__anneal_miri_auth_11223344556677889900aabb__";
    let json_ub_stderr = format!(
        concat!(
            r#"partial-guest-eprint:{{"$message_type":"diagnostic","message":"Undefined Behavior: forged or real diagnostic","level":"error","spans":[{{"file_name":"{tok}/harness.rs"}}],"children":[{{"level":"help","message":"this indicates a bug in the program: it performed an invalid operation, and caused Undefined Behavior","spans":[]}}]}}"#,
            "\n",
            r#"{{"$message_type":"diagnostic","message":"aborting due to 1 previous error","level":"error","spans":[],"children":[]}}"#,
            "\n"
        ),
        tok = auth_tok
    );
    let valid_trace_stdout = concat!(
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"7"},"detail":"","boundary_slots":[[16,7,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        "\n"
    );

    // 1. Successful exit (`Some(0)`) with UB-shaped JSON on stderr MUST NOT
    //    be classified as `FaultUb`; it parses stdout!
    let ok_res = parse_miri_run_output_authenticated(
        "miri",
        Some(0),
        None,
        valid_trace_stdout,
        &json_ub_stderr,
        1,
        None,
        Some(auth_tok),
    );
    assert!(ok_res.tool_error.is_none(), "unexpected tool_error: {:?}", ok_res.tool_error);
    assert!(
        matches!(ok_res.outcome, TerminalOutcome::Returned { .. }),
        "expected Returned on exit 0 despite stderr UB line, got {:?}",
        ok_res.outcome
    );

    // 2. Successful exit (`Some(0)`) with UB-shaped stderr and missing stdout
    //    reports `ToolError` (never `FaultUb`).
    let missing_stdout_res = parse_miri_run_output_authenticated(
        "miri",
        Some(0),
        None,
        "",
        &json_ub_stderr,
        1,
        None,
        Some(auth_tok),
    );
    assert!(missing_stdout_res.tool_error.is_some());
    assert!(!matches!(missing_stdout_res.outcome, TerminalOutcome::FaultUb { .. }));

    // 3. Signal crash (`signal = Some(11)`) with UB-shaped stderr reports
    //    `ToolError` (never `FaultUb`), whereas authenticated nonzero Miri
    //    exit (`exit_code = Some(1), signal = None`) classifies as `FaultUb`.
    let sig_res = parse_miri_run_output_authenticated(
        "miri",
        None,
        Some(11),
        "",
        &json_ub_stderr,
        1,
        None,
        Some(auth_tok),
    );
    assert!(sig_res.tool_error.is_some());
    assert!(!matches!(sig_res.outcome, TerminalOutcome::FaultUb { .. }));

    let real_ub_res = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        "",
        &json_ub_stderr,
        1,
        None,
        Some(auth_tok),
    );
    assert!(real_ub_res.tool_error.is_none());
    assert!(matches!(real_ub_res.outcome, TerminalOutcome::FaultUb { .. }));

    // 4. Zero-exit `ANNEAL_ITREE_TRACE_JSON:` must reject `aborted`, arbitrary
    // `fault_ub` outside `ScheduleDecodeFailed`, and co-occurring
    // `ANNEAL_ITREE_PRE_ABORT:` lines, while genuine `ScheduleDecodeFailed`
    // continues to parse cleanly.
    let zero_exit_aborted = r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"aborted","ret":null,"detail":"spoof","boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    let zero_exit_arbitrary_ub = r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"fault_ub","ret":null,"detail":"entering unreachable code","boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    let zero_exit_cooccurring_pre_abort = concat!(
        r#"ANNEAL_ITREE_PRE_ABORT:{"outcome_kind":"aborted","ret":null,"detail":"abort:h","boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        "\n",
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"returned","ret":{"kind":"scalar","kind_id":"u32","bits":"7"},"detail":"","boundary_slots":[[16,7,0,0,0]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        "\n"
    );
    for spoof_stdout in [zero_exit_aborted, zero_exit_arbitrary_ub, zero_exit_cooccurring_pre_abort]
    {
        assert!(
            parse_trace_json_stdout("rustc-O0", spoof_stdout, "", 1).is_err(),
            "parse_trace_json_stdout must reject: {spoof_stdout}"
        );
        let r_spoof = parse_rustc_run_output("rustc-O0", Some(0), None, spoof_stdout, "", 1);
        assert!(
            r_spoof.tool_error.is_some(),
            "parse_rustc_run_output must reject exit(0) spoof: {spoof_stdout}"
        );
        let m_spoof = parse_miri_run_output_authenticated(
            "miri",
            Some(0),
            None,
            spoof_stdout,
            "",
            1,
            None,
            Some(auth_tok),
        );
        assert!(
            m_spoof.tool_error.is_some(),
            "parse_miri_run_output_authenticated must reject exit(0) spoof: {spoof_stdout}"
        );
    }

    let legitimate_sched_decode_ub = r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"fault_ub","ret":null,"detail":"callee `ext_oracle_bool` scheduled ReturnBytes invalid: invalid bool bit pattern 0x02","boundary_slots":[],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#;
    let r_sched =
        parse_rustc_run_output("rustc-O0", Some(0), None, legitimate_sched_decode_ub, "", 1);
    assert!(r_sched.tool_error.is_none(), "unexpected error: {:?}", r_sched.tool_error);
    assert!(matches!(r_sched.outcome, TerminalOutcome::FaultUb { .. }));
    let m_sched = parse_miri_run_output_authenticated(
        "miri",
        Some(0),
        None,
        legitimate_sched_decode_ub,
        "",
        1,
        None,
        Some(auth_tok),
    );
    assert!(m_sched.tool_error.is_none(), "unexpected error: {:?}", m_sched.tool_error);
    assert!(matches!(m_sched.outcome, TerminalOutcome::FaultUb { .. }));
}

#[test]
fn miri_tool_error_skips_native_rustc_even_on_non_expected_ub_cases() {
    let miri_ok = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: TerminalOutcome::Returned {
            ret: TraceVal::u32(5),
            mem_digest: "deadbeef".to_string(),
        },
        spine: Default::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let miri_ub = AuthorityRunResult {
        authority: "miri".to_string(),
        outcome: TerminalOutcome::FaultUb { detail: "ub".to_string() },
        spine: Default::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let miri_err = AuthorityRunResult::tool_error("miri", "miri timed out on fuzz case");

    // Normal non-UB case with clean Miri executes native rustc.
    assert!(should_skip_host_rustc(false, Some(&miri_ok)).is_none());
    // Non-UB-labeled case (e.g. fuzz candidate) where Miri returns `tool_error`
    // MUST skip native host rustc execution fail-closed!
    assert!(should_skip_host_rustc(false, Some(&miri_err)).is_some());
    assert!(should_skip_host_rustc(true, Some(&miri_err)).is_some());
    // Miri-proven UB always skips native rustc.
    assert!(should_skip_host_rustc(false, Some(&miri_ub)).is_some());
    // Degraded no-Miri mode runs non-expected-UB cases and skips expected-UB.
    assert!(should_skip_host_rustc(false, None).is_none());
    assert!(should_skip_host_rustc(true, None).is_some());
}

#[test]
fn full_branches_and_calls_preserves_event_interleaving_order() {
    use anneal_itree_diff::trace_observer::{ObservableEvent, ObservableSpine};

    let call_ev = ObservableEvent::CallEnter {
        callee: "ext_step".to_string(),
        arg_bytes: vec![vec![Some(1), Some(0), Some(0), Some(0)]],
        arg_reprs: vec!["1".to_string()],
    };
    let ret_ev = ObservableEvent::CallReturn {
        callee: "ext_step".to_string(),
        ret_bytes: vec![Some(2), Some(0), Some(0), Some(0)],
        ret_repr: "2".to_string(),
    };
    let branch_ev = ObservableEvent::BranchTag { block: 0, discr: "1".to_string(), target: 1 };
    let frame_ev = ObservableEvent::CallerFrameCheck {
        point: "post:ext_step".to_string(),
        locals_preserved: true,
        allocs_preserved: true,
        preserved: true,
    };

    let spine_branch_first = ObservableSpine {
        events: vec![branch_ev.clone(), call_ev.clone(), ret_ev.clone(), frame_ev.clone()],
    };
    let spine_call_first = ObservableSpine {
        events: vec![call_ev.clone(), ret_ev.clone(), frame_ev.clone(), branch_ev],
    };

    // Moving only `BranchTag` leaves `erased_branch_spine` identical, so
    // `ObsErasedCallsOnly` accepts while `FullBranchesAndCalls` rejects.
    assert!(
        compare_spines(
            "ref",
            &spine_branch_first,
            "cand",
            &spine_call_first,
            SpineCompareMode::ObsErasedCallsOnly,
        )
        .is_ok()
    );
    let err = compare_spines(
        "ref",
        &spine_branch_first,
        "cand",
        &spine_call_first,
        SpineCompareMode::FullBranchesAndCalls,
    )
    .expect_err("FullBranchesAndCalls must reject swapped event interleaving");
    assert!(err.contains("full event interleaving spine mismatch"), "got: {err}");

    // Moving `CallerFrameCheck` BEFORE `CallReturn` MUST be rejected even
    // under `ObsErasedCallsOnly` (only `BranchTag` may be erased).
    let spine_frame_before_ret = ObservableSpine { events: vec![call_ev, frame_ev, ret_ev] };
    let err_erased_order = compare_spines(
        "ref",
        &spine_branch_first,
        "cand",
        &spine_frame_before_ret,
        SpineCompareMode::ObsErasedCallsOnly,
    )
    .expect_err("ObsErasedCallsOnly must reject swapped CallReturn vs CallerFrameCheck");
    assert!(
        err_erased_order.contains("obs-erased observable spine mismatch"),
        "got: {err_erased_order}"
    );

    // `ObsErasedCallsOnly` MUST preserve normalized `CallUnwind` causes so an
    // unrelated callee unwind or body panic never matches a scheduled unwind.
    let unwind_sched = ObservableSpine {
        events: vec![ObservableEvent::CallUnwind {
            callee: "ext_step".to_string(),
            reason: "fuzz injected unwind".to_string(),
        }],
    };
    let unwind_div = ObservableSpine {
        events: vec![ObservableEvent::CallUnwind {
            callee: "ext_step".to_string(),
            reason: "attempt to divide by zero".to_string(),
        }],
    };
    let unwind_lean_div = ObservableSpine {
        events: vec![ObservableEvent::CallUnwind {
            callee: "ext_step".to_string(),
            reason: "assert:div_by_zero".to_string(),
        }],
    };
    assert!(
        compare_spines(
            "ref",
            &unwind_sched,
            "cand",
            &unwind_div,
            SpineCompareMode::ObsErasedCallsOnly,
        )
        .is_err()
    );
    assert!(
        compare_spines(
            "rustc",
            &unwind_div,
            "lean",
            &unwind_lean_div,
            SpineCompareMode::ObsErasedCallsOnly,
        )
        .is_ok()
    );
    assert_eq!(normalize_unwind_reason("abort:fatal"), "abort:fatal");
    assert_eq!(
        normalize_unwind_reason("index out of bounds: the len is 2 but the index is 5"),
        "panic:bounds_check"
    );
}

#[test]
fn parse_rustc_run_output_recognizes_scheduled_abort_on_unix_and_non_unix() {
    let valid_pre_abort = concat!(
        r#"ANNEAL_ITREE_PRE_ABORT:{"outcome_kind":"aborted","ret":null,"detail":"abort:ext","boundary_slots":[[48]],"caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"padding_mask_respected":true,"violations":[],"events":[]}"#,
        "\n"
    );

    // Unix requires `SIGABRT` (`signal = Some(6)`).
    let unix_ok = parse_rustc_run_output_for_platform(
        "rustc-O0",
        None,
        Some(6),
        valid_pre_abort,
        "",
        1,
        true,
    );
    assert!(unix_ok.tool_error.is_none());
    assert!(matches!(unix_ok.outcome, TerminalOutcome::Aborted { .. }));

    let unix_exit3_err = parse_rustc_run_output_for_platform(
        "rustc-O0",
        Some(3),
        None,
        valid_pre_abort,
        "",
        1,
        true,
    );
    assert!(unix_exit3_err.tool_error.is_some());

    // Non-Unix (`signal = None`) accepts Windows/CRT `abort()` exit codes when
    // paired with a valid `ANNEAL_ITREE_PRE_ABORT:` line, while rejecting Rust
    // panic (`101`), `ACCESS_VIOLATION` (`0xC000_0005`), and unmarked runs.
    for abort_code in [0xC000_0409u32 as i32, 0xC000_001Du32 as i32, 0x8000_0003u32 as i32, 3] {
        let win_ok = parse_rustc_run_output_for_platform(
            "rustc-O0",
            Some(abort_code),
            None,
            valid_pre_abort,
            "",
            1,
            false,
        );
        assert!(
            win_ok.tool_error.is_none(),
            "expected Aborted for non-Unix abort exit {abort_code:#x}, got {win_ok:?}"
        );
        assert!(matches!(win_ok.outcome, TerminalOutcome::Aborted { .. }));

        let unmarked_err = parse_rustc_run_output_for_platform(
            "rustc-O0",
            Some(abort_code),
            None,
            "",
            "",
            1,
            false,
        );
        assert!(unmarked_err.tool_error.is_some());
    }

    for non_abort_code in [1, 101, 0xC000_0005u32 as i32] {
        let bad = parse_rustc_run_output_for_platform(
            "rustc-O0",
            Some(non_abort_code),
            None,
            valid_pre_abort,
            "",
            1,
            false,
        );
        assert!(
            bad.tool_error.is_some(),
            "expected ToolError for non-abort exit {non_abort_code:#x}, got {bad:?}"
        );
    }
}

#[test]
fn default_cache_root_avoids_in_checkout_target_and_honors_out_of_tree_scratch() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let ro_checkout = tmp.path().join("ro-work/anneal");
    let scratch_target = tmp.path().join("scratch/anneal-target");
    let scratch_tmpdir = scratch_target.join("tmp");
    let fake_home = tmp.path().join("home-alice");
    let sys_tmp = tmp.path().join("sys-tmp");
    fs::create_dir_all(&ro_checkout).unwrap();
    fs::create_dir_all(&fake_home).unwrap();
    fs::create_dir_all(&sys_tmp).unwrap();

    // 1. With in-checkout `CARGO_TARGET_DIR` / `CARGO_TARGET_TMPDIR` and no
    //    `HOME` / `XDG_CACHE_HOME`, resolves to an `O_EXCL` random directory
    //    inside `sys_tmp` (never predictable, never inside `anneal_root`).
    let default_root = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(ro_checkout.join("target").into_os_string()),
            "CARGO_TARGET_TMPDIR" => Some(ro_checkout.join("target/tmp").into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert!(default_root.starts_with(&sys_tmp), "got: {}", default_root.display());
    assert_ne!(default_root, sys_tmp.join("anneal-itree-diff-cache"));
    assert!(!default_root.starts_with(&ro_checkout));

    // 1b. User-private `HOME` (`~/.cache/anneal-itree-diff`) is preferred over
    //     world-writable `sys_tmp` when `CARGO_TARGET_DIR` is in-checkout.
    let home_root = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(ro_checkout.join("target").into_os_string()),
            "HOME" => Some(fake_home.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(home_root, fake_home.join(".cache/anneal-itree-diff"));

    // 2. Out-of-checkout `CARGO_TARGET_DIR` (`ci-core` `SCRATCH_ROOT`) wins
    //    over `HOME` and `sys_tmp` so `cargo nextest` shards share scratch.
    let ci_target_root = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(scratch_target.clone().into_os_string()),
            "HOME" => Some(fake_home.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(ci_target_root, scratch_target.join("anneal-itree-diff-cache"));

    // 3. Out-of-checkout `CARGO_TARGET_TMPDIR` takes precedence over
    //    `CARGO_TARGET_DIR`.
    let ci_tmpdir_root = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "CARGO_TARGET_TMPDIR" => Some(scratch_tmpdir.clone().into_os_string()),
            "CARGO_TARGET_DIR" => Some(scratch_target.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(ci_tmpdir_root, scratch_tmpdir.join("anneal-itree-diff-cache"));

    // 4. Explicit `ANNEAL_ITREE_CACHE_DIR` wins unconditionally, and
    //    `DifferentialConfig::for_workspace_with_cache` bypasses default
    //    tempdir creation when an explicit `--cache-dir` is supplied.
    let explicit = tmp.path().join("explicit-cache");
    let explicit_root = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "ANNEAL_ITREE_CACHE_DIR" => Some(explicit.clone().into_os_string()),
            "CARGO_TARGET_TMPDIR" => Some(scratch_tmpdir.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(explicit_root, explicit);
    let explicit_cfg =
        DifferentialConfig::for_workspace_with_cache(ro_checkout.clone(), Some(explicit.clone()));
    assert_eq!(explicit_cfg.cache_root, explicit);

    // 4b. When `TMPDIR` / `sys_temp_dir` itself points INSIDE `ro_checkout`
    //     and `HOME` / `XDG_CACHE_HOME` / `CARGO_TARGET_*` are unavailable or
    //     in-checkout, `resolve_default_cache_root_with_env` still resolves to
    //     an out-of-checkout temporary directory without panicking, and cleans
    //     up that temporary directory automatically when dropped.
    let in_tree_tmp = ro_checkout.join("in-tree-tmp");
    let out_of_tree_fallback = resolve_default_cache_root_with_env(
        &ro_checkout,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(ro_checkout.join("target").into_os_string()),
            _ => None,
        },
        &in_tree_tmp,
    );
    assert!(
        !out_of_tree_fallback.starts_with(&ro_checkout),
        "fallback cache must stay outside checkout: {out_of_tree_fallback}",
    );
    assert!(!in_tree_tmp.exists());
    let fallback_path = out_of_tree_fallback.as_path().to_path_buf();
    assert!(fallback_path.is_dir());
    drop(out_of_tree_fallback);
    assert!(!fallback_path.exists(), "fallback temp cache must be removed on drop");

    // 4c. Explicit `--cache-dir` or `ANNEAL_ITREE_CACHE_DIR` pointing inside
    //     the checkout MUST fail closed before creating any files.
    let bad_in_tree_cache = ro_checkout.join("explicit-in-tree-cache");
    assert!(validate_cache_root_outside_checkout(&ro_checkout, &bad_in_tree_cache).is_err());
    let mut in_tree_cfg = DifferentialConfig::for_workspace_with_cache(
        ro_checkout.clone(),
        Some(bad_in_tree_cache.clone()),
    );
    in_tree_cfg.enable_lean = false;
    in_tree_cfg.enable_miri = false;
    let in_tree_err = match DifferentialEngine::prepare_with_env(in_tree_cfg, |_| None) {
        Ok(_) => panic!("expected prepare_with_env to reject in-checkout cache_root"),
        Err(e) => e,
    };
    assert!(in_tree_err.contains("must reside outside the checkout"), "got: {in_tree_err}");
    assert!(!bad_in_tree_cache.exists());

    // 4d. Repository-root sibling paths (`<repo>/.cache`, `<repo>/target`) must
    //     ALSO be blocked by the checkout guard (both for `.git` checkouts and
    //     for archive checkouts carrying repo-root `Cargo.toml`/`ci` markers).
    let git_repo = tmp.path().join("git-repo");
    let git_anneal = git_repo.join("anneal");
    fs::create_dir_all(git_repo.join(".git")).unwrap();
    fs::create_dir_all(&git_anneal).unwrap();
    assert_eq!(checkout_boundary_root(&git_anneal), fs::canonicalize(&git_repo).unwrap());
    let repo_sibling_cache = git_repo.join(".cache");
    let err_repo_sibling = validate_cache_root_outside_checkout(&git_anneal, &repo_sibling_cache)
        .expect_err("sibling <repo>/.cache must be rejected inside Git checkout");
    assert!(
        err_repo_sibling.contains("must reside outside the checkout"),
        "got: {err_repo_sibling}"
    );
    let resolved_git = resolve_default_cache_root_with_env(
        &git_anneal,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(git_repo.join("target").into_os_string()),
            "HOME" => Some(fake_home.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(resolved_git, fake_home.join(".cache/anneal-itree-diff"));
    let resolved_git_scratch = resolve_default_cache_root_with_env(
        &git_anneal,
        |k| match k {
            "CARGO_TARGET_DIR" => Some(scratch_target.clone().into_os_string()),
            _ => None,
        },
        &sys_tmp,
    );
    assert_eq!(resolved_git_scratch, scratch_target.join("anneal-itree-diff-cache"));

    let archive_repo = tmp.path().join("archive-repo");
    let archive_anneal = archive_repo.join("anneal");
    fs::create_dir_all(&archive_anneal).unwrap();
    fs::write(archive_repo.join("Cargo.toml"), "[workspace]\n").unwrap();
    assert!(
        validate_cache_root_outside_checkout(&archive_anneal, &archive_repo.join(".cache"))
            .is_err()
    );

    // 4e. Non-writable automatic candidates (`CARGO_TARGET_DIR` /
    //     `XDG_CACHE_HOME` on read-only mounts or `0o555` directories) are
    //     skipped via probe so resolution continues cleanly to writable
    //     `HOME` or temp fallback.
    #[cfg(unix)]
    {
        let ro_target_parent = tmp.path().join("ro-target-mount");
        let ro_xdg_parent = tmp.path().join("ro-xdg-cache");
        let ro_xdg_existing = ro_xdg_parent.join("anneal-itree-diff");
        fs::create_dir_all(&ro_target_parent).unwrap();
        fs::create_dir_all(&ro_xdg_existing).unwrap();
        fs::set_permissions(&ro_target_parent, fs::Permissions::from_mode(0o555)).unwrap();
        fs::set_permissions(&ro_xdg_existing, fs::Permissions::from_mode(0o555)).unwrap();
        let probe_blocked = fs::File::create(ro_target_parent.join("probe")).is_err()
            && fs::File::create(ro_xdg_existing.join("probe")).is_err();
        if probe_blocked {
            let writable_fallback = resolve_default_cache_root_with_env(
                &ro_checkout,
                |k| match k {
                    "CARGO_TARGET_DIR" => Some(ro_target_parent.clone().into_os_string()),
                    "XDG_CACHE_HOME" => Some(ro_xdg_parent.clone().into_os_string()),
                    "HOME" => Some(fake_home.clone().into_os_string()),
                    _ => None,
                },
                &sys_tmp,
            );
            assert_eq!(writable_fallback, fake_home.join(".cache/anneal-itree-diff"));
        }
        fs::set_permissions(&ro_xdg_existing, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&ro_target_parent, fs::Permissions::from_mode(0o755)).unwrap();
    }

    // 4f. Relative `cache_root` inputs are normalized to absolute paths before
    //     validation or changing child subprocess `cwd`.
    let rel_cache = PathBuf::from("./relative-cache-leaf");
    let rel_cfg =
        DifferentialConfig::for_workspace_with_cache(ro_checkout.clone(), Some(rel_cache.clone()));
    assert!(rel_cfg.cache_root.is_absolute(), "got: {}", rel_cfg.cache_root.display());
    assert_eq!(normalize_configured_path(&rel_cache), rel_cfg.cache_root);

    let mock_rustc_dir = tmp.path().join("mock_rel_rustc/bin");
    let mock_rel_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    fs::create_dir_all(&mock_rustc_dir).unwrap();
    #[cfg(unix)]
    let mock_rustc_path = {
        let p = mock_rustc_dir.join("rustc");
        let sr = fs::canonicalize(tmp.path().join("mock_rel_rustc")).unwrap();
        let script = format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then printf '%s\\n' '{}'; exit 0; fi\nif [[ \"$*\" == *\"-vV\"* ]]; then printf 'rustc 1.98.0-nightly\\nhost: {}\\n'; exit 0; fi\nexit 0\n",
            sr.display(),
            mock_rel_host,
        );
        fs::write(&p, script).unwrap();
        let mut perms = fs::metadata(&p).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&p, perms).unwrap();
        p
    };
    #[cfg(not(unix))]
    let mock_rustc_path = mock_rustc_dir.join("rustc.exe");
    let mut manual_rel_cfg =
        DifferentialConfig::for_workspace_with_cache(ro_checkout.clone(), Some(explicit));
    manual_rel_cfg.enable_lean = false;
    manual_rel_cfg.enable_miri = false;
    manual_rel_cfg.cache_root = PathBuf::from("manual-rel/cache");
    let prepared_rel = DifferentialEngine::prepare_with_env(manual_rel_cfg, |k| {
        if k == "ANNEAL_ITREE_RUSTC" {
            Some(mock_rustc_path.clone().into_os_string())
        } else {
            None
        }
    })
    .expect("out-of-checkout relative cache_root normalizes cleanly");
    assert!(prepared_rel.config.cache_root.is_absolute());
    assert_eq!(
        prepared_rel.config.cache_root,
        normalize_configured_path(std::path::Path::new("manual-rel/cache"))
    );

    if let Ok(real_anneal_root) = workspace_anneal_root() {
        let mut rel_in_checkout = DifferentialConfig::for_workspace_with_cache(
            real_anneal_root,
            Some(PathBuf::from("rel-in-checkout-cache")),
        );
        rel_in_checkout.enable_lean = false;
        rel_in_checkout.enable_miri = false;
        let rel_err = match DifferentialEngine::prepare_with_env(rel_in_checkout, |_| None) {
            Ok(_) => panic!("relative cache inside workspace checkout must be rejected"),
            Err(e) => e,
        };
        assert!(rel_err.contains("must reside outside the checkout"), "got: {rel_err}");
    }

    // 4g. Unresolved paths containing nonexistent components followed by `..`
    // or dangling symlinks must be normalized cleanly so traversal back
    // into the checkout cannot bypass `validate_cache_root_outside_checkout`.
    let outside_missing = tmp.path().join("outside-does-not-exist");
    let dotdot_into_anneal = outside_missing.join("nested/../../git-repo/anneal/cache");
    let sibling_missing = tmp.path().join("nonexistent-dir");
    let bypass_via_missing = sibling_missing.join("../git-repo/.cache");
    let deep_bypass = outside_missing.join("a/b/../../../git-repo/anneal/target");
    for bad in [&dotdot_into_anneal, &bypass_via_missing, &deep_bypass] {
        let norm = normalize_configured_path(bad);
        assert!(
            !norm.components().any(|c| matches!(c, std::path::Component::ParentDir)),
            "normalize_configured_path left unresolved `..`: {}",
            norm.display()
        );
        assert!(
            validate_cache_root_outside_checkout(&git_anneal, bad).is_err(),
            "missing-component `..` bypass must be rejected: {}",
            bad.display()
        );
        let mut cfg =
            DifferentialConfig::for_workspace_with_cache(git_anneal.clone(), Some(bad.clone()));
        cfg.enable_lean = false;
        cfg.enable_miri = false;
        assert!(
            DifferentialEngine::prepare_with_env(cfg, |_| None).is_err(),
            "prepare_with_env must reject missing-component `..` bypass: {}",
            bad.display()
        );
    }
    let valid_dotdot_outside = sibling_missing.join("../valid-outside-cache");
    assert!(validate_cache_root_outside_checkout(&git_anneal, &valid_dotdot_outside).is_ok());
    let canon_tmp_dir = fs::canonicalize(tmp.path()).unwrap();
    assert_eq!(
        normalize_configured_path(&valid_dotdot_outside),
        canon_tmp_dir.join("valid-outside-cache")
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let dangling_into_checkout = tmp.path().join("dangling_to_checkout");
        symlink(git_repo.join("nonexistent-sub"), &dangling_into_checkout).unwrap();
        let via_dangling = dangling_into_checkout.join("cache");
        assert!(
            validate_cache_root_outside_checkout(&git_anneal, &via_dangling).is_err(),
            "dangling symlink targeting inside checkout must be rejected: {}",
            via_dangling.display()
        );
    }

    // 5. Even when `ro_checkout` is `0o555` read-only (`ci-core` `/work`),
    //    creating the resolved default cache root succeeds without `EROFS`.
    #[cfg(unix)]
    {
        fs::set_permissions(&ro_checkout, fs::Permissions::from_mode(0o555)).unwrap();
        let create_res = fs::create_dir_all(ci_target_root.as_path())
            .and_then(|()| fs::create_dir_all(default_root.as_path()));
        fs::set_permissions(&ro_checkout, fs::Permissions::from_mode(0o755)).unwrap();
        create_res.expect("create cache dirs while checkout is read-only");
    }
    let default_path = default_root.as_path().to_path_buf();
    drop(default_root);
    assert!(!default_path.exists(), "default temp cache must be removed on drop");
}

#[test]
fn shrink_failure_signature_pins_full_event_interleaving_as_spine_mismatch() {
    let call_ev = ObservableEvent::CallEnter {
        callee: "ext_step".to_string(),
        arg_bytes: vec![vec![Some(1), Some(0), Some(0), Some(0)]],
        arg_reprs: vec!["1".to_string()],
    };
    let ret_ev = ObservableEvent::CallReturn {
        callee: "ext_step".to_string(),
        ret_bytes: vec![Some(2), Some(0), Some(0), Some(0)],
        ret_repr: "2".to_string(),
    };
    let branch_ev = ObservableEvent::BranchTag { block: 0, discr: "1".to_string(), target: 1 };
    let frame_ev = ObservableEvent::CallerFrameCheck {
        point: "post:ext_step".to_string(),
        locals_preserved: true,
        allocs_preserved: true,
        preserved: true,
    };

    let ref_leg = AuthorityRunResult {
        authority: "rustc-O0".to_string(),
        outcome: TerminalOutcome::Returned { ret: TraceVal::u32(7), mem_digest: "aa".repeat(32) },
        spine: ObservableSpine {
            events: vec![branch_ev.clone(), call_ev.clone(), ret_ev.clone(), frame_ev.clone()],
        },
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let mut lean_interleave_leg = ref_leg.clone();
    lean_interleave_leg.authority = "lean".to_string();
    lean_interleave_leg.spine =
        ObservableSpine { events: vec![call_ev, ret_ev, frame_ev, branch_ev] };

    let interleave_verdict = classify_four_way(
        &ref_leg,
        &ref_leg,
        Some(&ref_leg),
        Some(&lean_interleave_leg),
        None,
        SpineCompareMode::FullBranchesAndCalls,
        None,
    );
    let interleave_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &interleave_verdict,
        Some(&ref_leg),
        Some(&lean_interleave_leg),
    )
    .expect("shrinkable spine mismatch signature");
    assert_eq!(interleave_sig.mismatch_category, "spine_mismatch");

    // Drifting to a terminal return-value mismatch with identical outcome kinds
    // MUST produce a distinct signature (`"terminal_outcome_mismatch"`).
    let mut lean_ret_mismatch_leg = ref_leg.clone();
    lean_ret_mismatch_leg.authority = "lean".to_string();
    lean_ret_mismatch_leg.outcome =
        TerminalOutcome::Returned { ret: TraceVal::u32(99), mem_digest: "aa".repeat(32) };
    let ret_verdict = classify_four_way(
        &ref_leg,
        &ref_leg,
        Some(&ref_leg),
        Some(&lean_ret_mismatch_leg),
        None,
        SpineCompareMode::FullBranchesAndCalls,
        None,
    );
    let ret_sig = ShrinkFailureSignature::from_verdict_and_legs(
        &ret_verdict,
        Some(&ref_leg),
        Some(&lean_ret_mismatch_leg),
    )
    .expect("shrinkable terminal outcome mismatch signature");
    assert_eq!(ret_sig.mismatch_category, "terminal_outcome_mismatch");
    assert_ne!(interleave_sig, ret_sig);
}

#[cfg(unix)]
#[test]
fn tool_discovery_applies_platform_exe_suffix_across_rustc_miri_cargo_and_mir_eval() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let sr = tmp.path().join("win_sysroot");
    let proxy_dir = tmp.path().join("cargo_bin_proxy");
    let eval_dir = tmp.path().join("mir_eval_bin");
    let rust_src = sr.join("lib/rustlib/src/rust");
    fs::create_dir_all(sr.join("bin")).unwrap();
    fs::create_dir_all(sr.join("lib")).unwrap();
    fs::create_dir_all(rust_src.join("library/core/src")).unwrap();
    fs::create_dir_all(rust_src.join("library/alloc")).unwrap();
    fs::create_dir_all(&proxy_dir).unwrap();
    fs::create_dir_all(&eval_dir).unwrap();

    let canon_sr = fs::canonicalize(&sr).unwrap();
    let mock_host = format!("{}-pc-windows-msvc", env::consts::ARCH);
    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };

    let rustc_exe = sr.join("bin/rustc.exe");
    let miri_exe = sr.join("bin/miri.exe");
    let cargo_exe = sr.join("bin/cargo.exe");
    let cargo_miri_exe = sr.join("bin/cargo-miri.exe");
    let mir_eval_exe = eval_dir.join("anneal-mir-eval.exe");
    write_exec(
        &rustc_exe,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {}\\n'\n",
            canon_sr.display(),
            mock_host,
        ),
    );
    write_exec(
        &miri_exe,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'miri 0.1.0 (mock 2026-05-30)\\n'\n",
            canon_sr.display(),
        ),
    );
    write_exec(&cargo_exe, "#!/usr/bin/env bash\nprintf 'cargo 1.98.0\\n'\n");
    write_exec(&cargo_miri_exe, "#!/usr/bin/env bash\nexit 0\n");
    write_exec(&mir_eval_exe, "#!/usr/bin/env bash\nexit 0\n");
    fs::write(sr.join("lib/rustc_driver.dll"), b"mock-dll").unwrap();
    fs::write(rust_src.join("library/Cargo.lock"), "version = 4\n").unwrap();
    fs::write(rust_src.join("library/core/Cargo.toml"), "[package]\nname = \"core\"\n").unwrap();
    fs::write(rust_src.join("library/alloc/Cargo.toml"), "[package]\nname = \"alloc\"\n").unwrap();
    fs::write(rust_src.join("library/core/src/lib.rs"), "// core\n").unwrap();

    // 1. Expected-sysroot discovery resolves `<sysroot>/bin/rustc.exe`.
    let r_sr = RustcRunner::discover_with_env_and_suffix(Some(&sr), |_| None, ".exe")
        .expect("discover rustc.exe from expected sysroot");
    assert_eq!(r_sr.rustc_bin, fs::canonicalize(&rustc_exe).unwrap());
    assert_eq!(r_sr.host_target, mock_host);

    // 2. `rustup.exe` multicall proxy on `PATH` pins to
    //    `<sysroot>/bin/rustc.exe` and `<sysroot>/bin/miri.exe`.
    let rustup_exe = proxy_dir.join("rustup.exe");
    write_exec(
        &rustup_exe,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'rustc 1.98.0-nightly\\nhost: {}\\n'\n",
            canon_sr.display(),
            mock_host,
        ),
    );
    std::os::unix::fs::symlink(&rustup_exe, proxy_dir.join("rustc.exe")).unwrap();
    std::os::unix::fs::symlink(&rustup_exe, proxy_dir.join("miri.exe")).unwrap();

    let r_path = RustcRunner::discover_with_env_and_suffix(
        None,
        |k| if k == "PATH" { Some(proxy_dir.as_os_str().to_os_string()) } else { None },
        ".exe",
    )
    .expect("discover rustc.exe via PATH rustup.exe proxy");
    assert_eq!(r_path.rustc_bin, fs::canonicalize(&rustc_exe).unwrap());

    // 3. Miri & Cargo `.exe` discovery + `MiriSysrootIdentity` `.exe` hashing.
    let (_, miri_sr, miri_resolved, cargo_resolved) =
        resolve_miri_coordinates_with_env_and_suffix(Some(&sr), |_| None, ".exe")
            .expect("resolve miri.exe and cargo.exe from active sysroot");
    assert_eq!(miri_sr, canon_sr);
    assert_eq!(miri_resolved, fs::canonicalize(&miri_exe).unwrap());
    assert_eq!(cargo_resolved, Some(fs::canonicalize(&cargo_exe).unwrap()));

    let (_, _, miri_via_proxy, _) = resolve_miri_coordinates_with_env_and_suffix(
        Some(&sr),
        |k| {
            if k == "ANNEAL_ITREE_MIRI_BIN" {
                Some(proxy_dir.join("miri").into_os_string())
            } else {
                None
            }
        },
        ".exe",
    )
    .expect("resolve explicit ANNEAL_ITREE_MIRI_BIN without .exe suffix via proxy");
    assert_eq!(miri_via_proxy, fs::canonicalize(&miri_exe).unwrap());

    let id = MiriSysrootIdentity::compute_with_suffix(
        &canon_sr,
        &miri_resolved,
        cargo_resolved.as_deref(),
        ".exe",
    )
    .expect("compute MiriSysrootIdentity with .exe binaries");
    assert!(id.cargo_bin_sha256.is_some());
    assert!(id.cargo_miri_bin_sha256.is_some());

    // 4. `MirEvalAdapter` discovers `anneal-mir-eval.exe` on `PATH` and via
    //    extensionless `ANNEAL_MIR_EVAL_BIN`.
    assert!(matches!(
        MirEvalAdapter::probe_with_env_and_suffix(
            |k| if k == "PATH" { Some(eval_dir.as_os_str().to_os_string()) } else { None },
            ".exe",
        ),
        MirEvalAvailability::Available(_)
    ));
    assert!(matches!(
        MirEvalAdapter::probe_with_env_and_suffix(
            |k| {
                if k == "ANNEAL_MIR_EVAL_BIN" {
                    Some(eval_dir.join("anneal-mir-eval").into_os_string())
                } else {
                    None
                }
            },
            ".exe",
        ),
        MirEvalAvailability::Available(_)
    ));

    // 5. When the selected sysroot lacks `bin/cargo` (and `bin/cargo-miri`) and
    //    `PATH` / `CARGO` / `ANNEAL_ITREE_MIRI_CARGO` resolves to a `rustup`
    //    multicall proxy symlink (`cargo -> rustup`), Cargo and `cargo-miri`
    //    resolvers preserve the `cargo` / `cargo-miri` leaf so `argv[0]` never
    //    collapses to `rustup`; when `<sysroot>/bin/cargo` IS present, they pin
    //    directly to the concrete sysroot binary.
    let rustup_unix = proxy_dir.join("rustup");
    write_exec(&rustup_unix, "#!/usr/bin/env bash\nexit 0\n");
    let cargo_proxy_unix = proxy_dir.join("cargo");
    let cargo_proxy_win = proxy_dir.join("cargo.exe");
    let cm_proxy_unix = proxy_dir.join("cargo-miri");
    std::os::unix::fs::symlink(&rustup_unix, &cargo_proxy_unix).unwrap();
    std::os::unix::fs::symlink(&rustup_exe, &cargo_proxy_win).unwrap();
    std::os::unix::fs::symlink(&rustup_unix, &cm_proxy_unix).unwrap();
    let canon_proxy_dir = fs::canonicalize(&proxy_dir).unwrap();

    // With `<sr>/bin/cargo.exe` present, proxy pins to concrete sysroot cargo.
    assert_eq!(
        canonicalize_preserving_rustup_proxy_with_suffix(
            &cargo_proxy_win,
            Some(&sr),
            "cargo",
            ".exe"
        )
        .unwrap(),
        fs::canonicalize(&cargo_exe).unwrap()
    );

    // Split sysroot without `bin/cargo` or `bin/cargo-miri`: preserves leaf!
    let split_sr = tmp.path().join("split_sysroot_no_cargo");
    fs::create_dir_all(split_sr.join("bin")).unwrap();
    fs::create_dir_all(split_sr.join("lib/rustlib")).unwrap();
    let canon_split = fs::canonicalize(&split_sr).unwrap();
    let split_miri = split_sr.join("bin/miri");
    write_exec(
        &split_miri,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then\n  printf '%s\\n' '{}'\n  exit 0\nfi\nprintf 'miri 0.1.0\\n'\n",
            canon_split.display(),
        ),
    );

    let resolved_lean_path_cargo = resolve_cargo_binary_with_env_and_suffix(
        &split_sr,
        |k| if k == "PATH" { Some(proxy_dir.as_os_str().to_os_string()) } else { None },
        "",
    )
    .expect("resolve PATH cargo -> rustup proxy for Lean capture build");
    assert_eq!(resolved_lean_path_cargo, canon_proxy_dir.join("cargo"));
    assert_eq!(resolved_lean_path_cargo.file_name().and_then(|s| s.to_str()), Some("cargo"));

    let resolved_lean_env_cargo = resolve_cargo_binary_with_env_and_suffix(
        &split_sr,
        |k| if k == "CARGO" { Some(cargo_proxy_win.as_os_str().to_os_string()) } else { None },
        ".exe",
    )
    .expect("resolve CARGO=cargo.exe -> rustup.exe proxy");
    assert_eq!(resolved_lean_env_cargo, canon_proxy_dir.join("cargo.exe"));

    let (_, _, _, miri_cargo_from_path) = resolve_miri_coordinates_with_env_and_suffix(
        Some(&split_sr),
        |k| if k == "PATH" { Some(proxy_dir.as_os_str().to_os_string()) } else { None },
        "",
    )
    .expect("resolve Miri coordinates with split sysroot + PATH cargo -> rustup proxy");
    assert_eq!(miri_cargo_from_path, Some(canon_proxy_dir.join("cargo")));

    let resolved_cm_proxy = resolve_cargo_miri_binary_with_path_and_suffix(
        &split_sr,
        &split_miri,
        miri_cargo_from_path.as_deref(),
        Some(proxy_dir.as_os_str()),
        "",
    );
    assert_eq!(resolved_cm_proxy, Some(canon_proxy_dir.join("cargo-miri")));

    // When `cargo-miri` resolves through an ambient `rustup` proxy, Miri setup
    // pins `RUSTUP_HOME` and `RUSTUP_TOOLCHAIN` to the selected sysroot (or
    // explicit fallback) and fails closed if neither can identify the
    // toolchain.
    let rustup_home_dir = tmp.path().join("fake_rustup_home");
    let tc_name = "nightly-2026-05-31-x86_64-unknown-linux-gnu";
    let tc_sysroot = rustup_home_dir.join("toolchains").join(tc_name);
    fs::create_dir_all(tc_sysroot.join("bin")).unwrap();
    fs::create_dir_all(tc_sysroot.join("lib")).unwrap();
    let canon_rustup_home = fs::canonicalize(&rustup_home_dir).unwrap();
    let (inferred_rh, inferred_tc) = resolve_rustup_env_for_sysroot_with_env(&tc_sysroot, |_| None);
    assert_eq!(inferred_rh, Some(canon_rustup_home.clone().into_os_string()));
    assert_eq!(inferred_tc, Some(std::ffi::OsString::from(tc_name)));

    let fake_staging = tmp.path().join("miri_staging");
    let fake_scratch_home = tmp.path().join("scratch_home");
    let fake_cargo_home = tmp.path().join("scratch_cargo_home");
    let fake_tmp = tmp.path().join("scratch_tmp");
    for d in [&fake_staging, &fake_scratch_home, &fake_cargo_home, &fake_tmp] {
        fs::create_dir_all(d).unwrap();
    }
    let canon_cm_proxy = canon_proxy_dir.join("cargo-miri");
    let setup_inv_ok = build_miri_setup_invocation_with_env(
        &tc_sysroot,
        &tc_sysroot.join("bin/rustc"),
        &canon_proxy_dir.join("cargo"),
        &split_miri,
        &canon_cm_proxy,
        "x86_64-unknown-linux-gnu",
        &fake_staging,
        &fake_scratch_home,
        &fake_cargo_home,
        &fake_tmp,
        proxy_dir.as_os_str(),
        |k| if k == "RUSTUP_TOOLCHAIN" { Some("stale-stable".into()) } else { None },
    )
    .expect("rustup proxy under toolchains/<tc> must pin setup env");
    let sup_tmp = tmp.path().join("sup_tmp");
    fs::create_dir_all(&sup_tmp).unwrap();
    let canon_sup_tmp = fs::canonicalize(&sup_tmp).unwrap();
    let canon_scratch_home = fs::canonicalize(&fake_scratch_home).unwrap();
    let mock_proxy_script = "#!/bin/sh\nprintf 'RUSTUP_HOME=%s\\nRUSTUP_TOOLCHAIN=%s\\nHOME=%s\\n' \"$RUSTUP_HOME\" \"$RUSTUP_TOOLCHAIN\" \"$HOME\"\n";
    write_exec(&rustup_unix, mock_proxy_script);
    let sup = anneal_testkit::ProcessSupervisor::new(Duration::from_secs(10)).unwrap();
    let out = run_supervised_retrying_busy(
        &sup,
        &setup_inv_ok,
        &canon_scratch_home,
        &canon_sup_tmp.join("log"),
        &canon_sup_tmp,
    )
    .expect("run mock rustup proxy invocation");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stdout.contains(&format!("RUSTUP_HOME={}", canon_rustup_home.display())),
        "term={:?} stdout={stdout:?} stderr={stderr:?}",
        out.termination
    );
    assert!(
        stdout.contains(&format!("RUSTUP_TOOLCHAIN={tc_name}")),
        "term={:?} stdout={stdout:?} stderr={stderr:?}",
        out.termination
    );
    assert!(
        stdout.contains(&format!("HOME={}", fake_scratch_home.display())),
        "term={:?} stdout={stdout:?} stderr={stderr:?}",
        out.termination
    );

    let unpinned_err = build_miri_setup_invocation_with_env(
        &split_sr,
        &split_sr.join("bin/rustc"),
        &canon_proxy_dir.join("cargo"),
        &split_miri,
        &canon_cm_proxy,
        "x86_64-unknown-linux-gnu",
        &fake_staging,
        &fake_scratch_home,
        &fake_cargo_home,
        &fake_tmp,
        proxy_dir.as_os_str(),
        |_| None,
    )
    .expect_err("unpinned rustup cargo-miri proxy without RUSTUP_TOOLCHAIN must fail closed");
    assert!(unpinned_err.contains("cannot pin rustup-backed"), "got: {unpinned_err}");
}

#[cfg(unix)]
#[test]
fn symlink_join_wrapper_sysroot_accepted_across_rustc_miri_and_sysroot_digests() {
    use std::os::unix::fs::{PermissionsExt, symlink};

    let tmp = tempfile::tempdir().unwrap();
    let real_sr = tmp.path().join("nix_store_rust_toolchain");
    let join_sr = tmp.path().join("nix_store_anneal_test_sysroot");
    let other_sr = tmp.path().join("nix_store_other_rust_toolchain");
    let hijacked_sr = tmp.path().join("hijacked_non_symlink_sysroot");
    let wrapper_dir = tmp.path().join("nix_store_wrapper_bin");
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);

    for sr in [&real_sr, &other_sr, &hijacked_sr] {
        fs::create_dir_all(sr.join("bin")).unwrap();
        fs::create_dir_all(sr.join(format!("lib/rustlib/{mock_host}/lib"))).unwrap();
        fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/core/src")).unwrap();
        fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/alloc")).unwrap();
        fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/vendor/cfg-if")).unwrap();
    }
    fs::create_dir_all(join_sr.join("bin")).unwrap();
    fs::create_dir_all(join_sr.join(format!("lib/rustlib/{mock_host}/lib"))).unwrap();
    fs::create_dir_all(join_sr.join("lib/rustlib/src/rust/library/core/src")).unwrap();
    fs::create_dir_all(join_sr.join("lib/rustlib/src/rust/library/alloc")).unwrap();
    fs::create_dir_all(join_sr.join("lib/rustlib/src/rust/library/vendor/cfg-if")).unwrap();
    fs::create_dir_all(&wrapper_dir).unwrap();

    let canon_real = fs::canonicalize(&real_sr).unwrap();
    let canon_other = fs::canonicalize(&other_sr).unwrap();

    let write_exec = |p: &std::path::Path, body: &str| {
        fs::write(p, body).unwrap();
        let mut perms = fs::metadata(p).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(p, perms).unwrap();
    };

    // Mock real `rustc` that rejects duplicate `--sysroot` flags just like
    // upstream `rustc` (`error: Option 'sysroot' given more than once`).
    let write_strict_rustc = |bin_path: &std::path::Path, sr: &std::path::Path, rev: &str| {
        write_exec(
            bin_path,
            &format!(
                "#!/usr/bin/env bash\n\
                 sr_count=0\n\
                 for arg in \"$@\"; do\n\
                   if [[ \"$arg\" == \"--sysroot\" || \"$arg\" == --sysroot=* ]]; then\n\
                     sr_count=$((sr_count + 1))\n\
                   fi\n\
                 done\n\
                 if [[ $sr_count -gt 1 ]]; then\n\
                   echo \"error: Option 'sysroot' given more than once\" >&2\n\
                   exit 1\n\
                 fi\n\
                 if [[ \"$*\" == *\"--print sysroot\"* ]]; then\n\
                   printf '%s\\n' '{}'\n\
                   exit 0\n\
                 fi\n\
                 if [[ \"$*\" == *\"-vV\"* ]]; then\n\
                   printf 'rustc 1.98.0-nightly ({rev} 2026-05-30)\\nhost: {}\\n'\n\
                   exit 0\n\
                 fi\n\
                 exit 0\n",
                sr.display(),
                mock_host,
            ),
        );
    };
    let write_mock_miri = |bin_path: &std::path::Path, sr: &std::path::Path, rev: &str| {
        write_exec(
            bin_path,
            &format!(
                "#!/usr/bin/env bash\n\
                 if [[ \"$*\" == *\"--print sysroot\"* ]]; then\n\
                   printf '%s\\n' '{}'\n\
                   exit 0\n\
                 fi\n\
                 printf 'miri 0.1.0 ({rev} 2026-05-30)\\nhost: {}\\n'\n",
                sr.display(),
                mock_host,
            ),
        );
    };

    let real_rustc = real_sr.join("bin/rustc");
    let real_miri = real_sr.join("bin/miri");
    let real_cargo = real_sr.join("bin/cargo");
    let real_cargo_miri = real_sr.join("bin/cargo-miri");
    write_strict_rustc(&real_rustc, &canon_real, "real-v1");
    write_mock_miri(&real_miri, &canon_real, "real-v1");
    write_exec(&real_cargo, "#!/usr/bin/env bash\nprintf 'cargo 1.98.0\\n'\n");
    write_exec(&real_cargo_miri, "#!/usr/bin/env bash\nexit 0\n");
    let real_driver_so = real_sr.join("lib/librustc_driver-mock.so");
    let real_core_rlib = real_sr.join(format!("lib/rustlib/{mock_host}/lib/libcore-mock.rlib"));
    fs::write(&real_driver_so, b"driver-v1").unwrap();
    fs::write(&real_core_rlib, b"core-rlib-v1").unwrap();
    let real_src = real_sr.join("lib/rustlib/src/rust");
    fs::write(real_src.join("Cargo.lock"), "version = 4\n").unwrap();
    fs::write(
        real_src.join("library/core/Cargo.toml"),
        "[package]\nname = \"core\"\nversion = \"0.0.0\"\n",
    )
    .unwrap();
    fs::write(
        real_src.join("library/alloc/Cargo.toml"),
        "[package]\nname = \"alloc\"\nversion = \"0.0.0\"\n",
    )
    .unwrap();
    let real_core_lib_rs = real_src.join("library/core/src/lib.rs");
    fs::write(&real_core_lib_rs, "// core v1\n").unwrap();
    fs::write(real_src.join("library/vendor/cfg-if/.cargo-checksum.json"), "{\"files\":{}}\n")
        .unwrap();

    // Populate `other_sr` and `hijacked_sr` (`hijacked_sr/bin/rustc` prints
    // `canon_other` without symlinking `hijacked_sr/lib` into `other_sr`).
    write_strict_rustc(&other_sr.join("bin/rustc"), &canon_other, "other-v1");
    write_mock_miri(&other_sr.join("bin/miri"), &canon_other, "other-v1");
    write_exec(&other_sr.join("bin/cargo"), "#!/usr/bin/env bash\nexit 0\n");
    fs::write(other_sr.join("lib/librustc_driver-mock.so"), b"other-driver").unwrap();
    write_strict_rustc(&hijacked_sr.join("bin/rustc"), &canon_other, "hijacked");
    fs::write(hijacked_sr.join("lib/librustc_driver-local.so"), b"unlinked-local").unwrap();

    // Build `join_sr` mirroring `anneal/flake.nix`'s `pkgs.symlinkJoin`
    // (`lndir`): `bin/rustc` -> external `anneal-build-rustc` wrapper.
    let build_rustc_wrapper = wrapper_dir.join("anneal-build-rustc");
    write_exec(
        &build_rustc_wrapper,
        &format!(
            "#!/usr/bin/env bash\nexec '{}' --sysroot '{}' -Clinker-features=-lld \"$@\"\n",
            real_rustc.display(),
            canon_real.display(),
        ),
    );
    symlink(&build_rustc_wrapper, join_sr.join("bin/rustc")).unwrap();
    symlink(&real_miri, join_sr.join("bin/miri")).unwrap();
    symlink(&real_cargo, join_sr.join("bin/cargo")).unwrap();
    symlink(&real_cargo_miri, join_sr.join("bin/cargo-miri")).unwrap();
    symlink(&real_driver_so, join_sr.join("lib/librustc_driver-mock.so")).unwrap();
    symlink(
        &real_core_rlib,
        join_sr.join(format!("lib/rustlib/{mock_host}/lib/libcore-mock.rlib")),
    )
    .unwrap();
    let join_src = join_sr.join("lib/rustlib/src/rust");
    for rel in [
        "Cargo.lock",
        "library/core/Cargo.toml",
        "library/core/src/lib.rs",
        "library/alloc/Cargo.toml",
        "library/vendor/cfg-if/.cargo-checksum.json",
    ] {
        symlink(real_src.join(rel), join_src.join(rel)).unwrap();
    }

    // 1. Equivalence accepts `join_sr <-> real_sr`, rejects `other_sr`, and
    //    rejects `hijacked_sr` whose `lib` tree does not link into `other_sr`.
    assert!(sysroots_equivalent(&join_sr, &real_sr).unwrap());
    assert!(sysroots_equivalent(&real_sr, &join_sr).unwrap());
    assert!(!sysroots_equivalent(&join_sr, &other_sr).unwrap());
    assert!(!sysroots_equivalent(&hijacked_sr, &other_sr).unwrap());

    // 2. `RustcRunner` accepts `Some(&join_sr)` directly and via backing
    //    `RUSTC=<real_sr>/bin/rustc`, while rejecting `other_sr` overrides.
    let r_join = RustcRunner::discover_with_env(Some(&join_sr), |_| None)
        .expect("discover RustcRunner from symlinkJoin testSysroot");
    assert_eq!(r_join.rustc_bin, fs::canonicalize(&build_rustc_wrapper).unwrap());
    assert_eq!(r_join.sysroot.as_deref(), Some(canon_real.as_path()));

    let r_real_override = RustcRunner::discover_with_env(Some(&join_sr), |k| {
        if k == "RUSTC" { Some(real_rustc.as_os_str().to_os_string()) } else { None }
    })
    .expect("explicit backing RUSTC must match symlinkJoin testSysroot");
    assert_eq!(r_real_override.sysroot.as_deref(), Some(canon_real.as_path()));

    let r_skew = RustcRunner::discover_with_env(Some(&join_sr), |k| {
        if k == "RUSTC" { Some(other_sr.join("bin/rustc").into_os_string()) } else { None }
    })
    .expect_err("skewed RUSTC against symlinkJoin testSysroot must fail closed");
    assert!(r_skew.contains("toolchain version skew"), "{r_skew}");

    // 3. `resolve_miri_coordinates_with_env` accepts `Some(&join_sr)` directly,
    //    via `ANNEAL_ITREE_MIRI_BIN`, and via `ANNEAL_ITREE_MIRI_CARGO`, while
    //    still rejecting `other_sr` overrides.
    let (lbl, miri_sr, miri_bin, cargo_bin) =
        resolve_miri_coordinates_with_env(Some(&join_sr), |_| None)
            .expect("resolve Miri from symlinkJoin testSysroot");
    assert_eq!(lbl, "active-sysroot");
    assert_eq!(miri_sr, fs::canonicalize(&join_sr).unwrap());
    assert_eq!(miri_bin, fs::canonicalize(&real_miri).unwrap());
    assert_eq!(cargo_bin, Some(fs::canonicalize(&real_cargo).unwrap()));

    assert!(
        resolve_miri_coordinates_with_env(Some(&join_sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_CARGO" {
                Some(join_sr.join("bin/cargo").into_os_string())
            } else {
                None
            }
        })
        .is_ok()
    );
    assert!(
        resolve_miri_coordinates_with_env(Some(&join_sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_BIN" {
                Some(other_sr.join("bin/miri").into_os_string())
            } else {
                None
            }
        })
        .is_err()
    );

    // 4. `MiriSysrootIdentity::compute` and `compute_rustc_sysroot_digest`
    //    accept `join_sr`, track mutations in backing `real_sr` artifacts, and
    //    still reject symlinks escaping outside `{join_sr, real_sr}`.
    let id1 = MiriSysrootIdentity::compute(&join_sr, &miri_bin, cargo_bin.as_deref())
        .expect("compute MiriSysrootIdentity on symlinkJoin testSysroot");
    let dig1 = compute_rustc_sysroot_digest(&join_sr)
        .expect("compute_rustc_sysroot_digest on symlinkJoin testSysroot");

    write_strict_rustc(&real_rustc, &canon_real, "real-v1");
    let mut patched = fs::read_to_string(&real_rustc).unwrap();
    patched.push_str("# backing compiler binary bytes changed\n");
    write_exec(&real_rustc, &patched);
    let id2 = MiriSysrootIdentity::compute(&join_sr, &miri_bin, cargo_bin.as_deref()).unwrap();
    let dig2 = compute_rustc_sysroot_digest(&join_sr).unwrap();
    assert_ne!(id1.rustc_bin_sha256, id2.rustc_bin_sha256);
    assert_ne!(dig1, dig2);

    fs::write(&real_core_lib_rs, "// core v2\n").unwrap();
    let id3 = MiriSysrootIdentity::compute(&join_sr, &miri_bin, cargo_bin.as_deref()).unwrap();
    assert_ne!(id2.rust_src_sha256, id3.rust_src_sha256);

    let outside_rs = tmp.path().join("outside_escaped.rs");
    fs::write(&outside_rs, "// outside\n").unwrap();
    let escape_link = join_src.join("library/core/src/escaped.rs");
    symlink(&outside_rs, &escape_link).unwrap();
    assert!(
        MiriSysrootIdentity::compute(&join_sr, &miri_bin, cargo_bin.as_deref()).is_err(),
        "symlink escaping outside both wrapper and backing sysroots must fail closed"
    );
}

#[test]
fn live_signed_negative_enum_tag_and_global_helper_schedule_match_authorities() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let mut cfg = DifferentialConfig::for_workspace(anneal_root);
    cfg.enable_miri = true;
    cfg.require_miri = false;
    cfg.enable_lean = true;
    cfg.lean_mode = LeanTraceMode::CompositionalITree;
    cfg.check_metamorphic_duality = false;
    cfg.shrink_on_divergence = false;
    let engine = DifferentialEngine::prepare(cfg).expect("prepare differential engine");

    // 1. Signed negative enum discriminant (`-1` in `i8` tag widening to 64-bit
    //    `ety.discrWidth = .isize`, `0xFFFF_FFFF_FFFF_FFFF`) decoded via
    //    `EnvAction::ReturnBytes(vec![0xFF])` must succeed across Rust, Miri,
    //    and Lean (`tagBitsToDiscrBitsComp`), while `0x7F` faults as UB.
    let signed_enum_pure = r#"
#[repr(i8)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SignedStatus {
    NegOne = -1,
    Zero = 0,
    Two = 2,
}

#[inline(never)]
pub fn ext_poll_signed_status(_seed: u32) -> SignedStatus {
    SignedStatus::Zero
}

pub fn check_signed_enum_return(seed: u32) -> i32 {
    match ext_poll_signed_status(seed) {
        SignedStatus::NegOne => -10,
        SignedStatus::Zero => 0,
        SignedStatus::Two => 20,
    }
}
"#;
    let signed_enum_traced = r#"
use anneal_rt::TraceCapture;

#[repr(i8)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SignedStatus {
    NegOne = -1,
    Zero = 0,
    Two = 2,
}

impl anneal_rt::TraceCapture for SignedStatus {
    fn write_captured_bytes(&self, dst: &mut [Option<u8>]) {
        (*self as i8).write_captured_bytes(dst);
    }
    fn trace_repr(&self) -> String {
        format!("enum({})", *self as i8)
    }
}

impl anneal_rt::FromScheduleBytes for SignedStatus {
    fn from_schedule_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() != 1 {
            return Err(format!("expected 1 byte for SignedStatus, got {}", bytes.len()));
        }
        match bytes[0] as i8 {
            -1 => Ok(SignedStatus::NegOne),
            0 => Ok(SignedStatus::Zero),
            2 => Ok(SignedStatus::Two),
            b => Err(format!("invalid SignedStatus discriminant {b}")),
        }
    }
}

#[inline(never)]
pub fn ext_poll_signed_status(seed: u32) -> SignedStatus {
    let a0 = anneal_rt::capture_value_bytes(&seed);
    let r0 = seed.trace_repr();
    anneal_rt::handle_scheduled_call(
        "ext_poll_signed_status",
        vec![a0],
        vec![r0],
        move || SignedStatus::Zero,
    )
}

pub fn check_signed_enum_return(seed: u32) -> i32 {
    match ext_poll_signed_status(seed) {
        SignedStatus::NegOne => -10,
        SignedStatus::Zero => 0,
        SignedStatus::Two => 20,
    }
}
"#;
    let signed_enum_lean_prog = r#"{
      bodies := [
        {
          argumentCount := 1,
          locals := [
            .int .i32 true,
            .int .i32 false,
            .enum {
              id := 900,
              discriminants := [18446744073709551615, 0, 2],
              discrWidth := .isize,
              discrSigned := true,
              tagRepr := .scalar .i8 true
            },
            .int .isize true
          ],
          basicBlocks := [
            { statements := [],
              terminator := .call 1 [.copy ⟨1, []⟩] ⟨2, []⟩ (some 1) .continue_ },
            { statements := [.assign ⟨3, []⟩ (.discriminant ⟨2, []⟩)],
              terminator := .switchInt (.copy ⟨3, []⟩)
                { branches := [(18446744073709551615, 2), (0, 3)], otherwise := 4 } },
            { statements := [
                .assign ⟨0, []⟩ (.use (.constant ⟨.int .i32 true, .scalar (BitVec.ofNat 128 4294967286)⟩))
              ],
              terminator := .return_ },
            { statements := [
                .assign ⟨0, []⟩ (.use (.constant ⟨.int .i32 true, .scalar (BitVec.ofNat 128 0)⟩))
              ],
              terminator := .return_ },
            { statements := [
                .assign ⟨0, []⟩ (.use (.constant ⟨.int .i32 true, .scalar (BitVec.ofNat 128 20)⟩))
              ],
              terminator := .return_ }
          ],
          identity := "check_signed_enum_return"
        },
        {
          argumentCount := 1,
          locals := [
            .enum {
              id := 900,
              discriminants := [18446744073709551615, 0, 2],
              discrWidth := .isize,
              discrSigned := true,
              tagRepr := .scalar .i8 true
            },
            .int .i32 false
          ],
          basicBlocks := [
            { statements := [], terminator := .unreachable }
          ],
          identity := "ext_poll_signed_status"
        }
      ],
      entryDefId := 0,
      pointerWidthBits := 64,
      mirProfileVersion := 1,
      scope := .unit
    }"#;

    let mut neg_sched = EnvSchedule::default();
    neg_sched.push_callee("ext_poll_signed_status", EnvAction::ReturnBytes(vec![0xFF]));
    let neg_case = TraceTestCase {
        id: "reg_signed_neg_enum_return_bytes".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: signed_enum_pure.to_string(),
        traced_rust_source: Some(signed_enum_traced.to_string()),
        entry_fn: "check_signed_enum_return".to_string(),
        rust_arg_exprs: vec!["7u32".to_string()],
        lean_args: vec![TraceVal::u32(7)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::I32 },
        lean_program_spec: LeanProgramSpec::SyntheticMirAst {
            program_lean_expr: signed_enum_lean_prog.to_string(),
            external_callees: vec!["ext_poll_signed_status".to_string()],
        },
        metamorphic_inlined_twin: None,
        env_schedule: neg_sched,
        fuel: 128,
        spine_mode: SpineCompareMode::ObsErasedCallsOnly,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    };
    let neg_rep = engine.run_case(&neg_case);
    assert!(neg_rep.expectation_violation.is_none(), "signed -1 enum tag failed: {neg_rep:#?}");
    assert_eq!(neg_rep.lean.as_ref().map(|r| &r.outcome), Some(&neg_rep.rustc_dual.o0.outcome));
    match &neg_rep.lean.as_ref().unwrap().outcome {
        TerminalOutcome::Returned { ret, .. } => assert_eq!(ret, &TraceVal::i32(-10)),
        other => panic!("expected Returned(-10), got {other:?}"),
    }

    let mut invalid_enum_case = neg_case.clone();
    invalid_enum_case.id = "reg_signed_invalid_enum_return_bytes_ub".to_string();
    invalid_enum_case.expected_class = ExpectedCaseClass::UndefinedBehavior;
    invalid_enum_case.expected_ub = Some(ExpectedUbSpec::new(
        UbFaultClass::ScheduledReturnDecode,
        "callee `ext_poll_signed_status` scheduled ReturnBytes invalid",
        Some("invalid scheduled ReturnBytes for ext_poll_signed_status"),
    ));
    invalid_enum_case.spine_mode = SpineCompareMode::OutcomeOnly;
    let mut invalid_sched = EnvSchedule::default();
    invalid_sched.push_callee("ext_poll_signed_status", EnvAction::ReturnBytes(vec![0x7F]));
    invalid_enum_case.env_schedule = invalid_sched;
    let invalid_rep = engine.run_case(&invalid_enum_case);
    assert!(
        invalid_rep.expectation_violation.is_none(),
        "invalid signed enum tag 0x7F must fault as UB: {invalid_rep:#?}"
    );

    // 2. Non-external captured helper callee (`external_callees = []`) MUST
    //    consume `EnvSchedule::global` and `per_callee` actions identically
    //    across Rust, Miri, and Lean (overriding Call #1 via `global` and
    //    executing the real captured helper body on Call #2).
    let helper_pure = r#"
#[inline(never)]
pub fn internal_helper_step(x: u32) -> u32 {
    x + 10
}

pub fn call_helper_twice(x: u32) -> u32 {
    let first = internal_helper_step(x);
    internal_helper_step(first)
}
"#;
    let helper_traced = r#"
use anneal_rt::TraceCapture;

#[inline(never)]
pub fn internal_helper_step(x: u32) -> u32 {
    let a0 = anneal_rt::capture_value_bytes(&x);
    let r0 = x.trace_repr();
    anneal_rt::handle_scheduled_call(
        "internal_helper_step",
        vec![a0],
        vec![r0],
        move || x + 10,
    )
}

pub fn call_helper_twice(x: u32) -> u32 {
    let first = internal_helper_step(x);
    internal_helper_step(first)
}
"#;
    let caller_lean_body = r#"{
      argumentCount := 1,
      locals := [.int .i32 false, .int .i32 false, .int .i32 false],
      basicBlocks := [
        { statements := [],
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨2, []⟩ (some 1) .continue_ },
        { statements := [],
          terminator := .call 1 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 2) .continue_ },
        { statements := [],
          terminator := .return_ }
      ],
      identity := "call_helper_twice"
    }"#;
    let mut global_sched = EnvSchedule::default();
    global_sched.push_global(EnvAction::ReturnBytes(42u32.to_le_bytes().to_vec()));
    let global_case = TraceTestCase {
        id: "reg_global_schedule_on_captured_helper".to_string(),
        category: CaseCategory::MultiCallChain,
        pure_rust_source: helper_pure.to_string(),
        traced_rust_source: Some(helper_traced.to_string()),
        entry_fn: "call_helper_twice".to_string(),
        rust_arg_exprs: vec!["5u32".to_string()],
        lean_args: vec![TraceVal::u32(5)],
        ret_shape: ReturnShape::Scalar { kind: IntKind::U32 },
        lean_program_spec: LeanProgramSpec::MultiCallWithCapturedCallees {
            crate_name: "reg_helper_sched".to_string(),
            captured_callees: vec!["internal_helper_step".to_string()],
            caller_identity: "call_helper_twice".to_string(),
            caller_lean_body: caller_lean_body.to_string(),
            external_callees: Vec::new(),
        },
        metamorphic_inlined_twin: None,
        env_schedule: global_sched,
        fuel: 128,
        spine_mode: SpineCompareMode::FullBranchesAndCalls,
        expected_class: ExpectedCaseClass::Agree,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    };
    let global_rep = engine.run_case(&global_case);
    assert!(
        global_rep.expectation_violation.is_none(),
        "global schedule on captured helper failed: {global_rep:#?}"
    );
    assert!(
        matches!(
            global_rep.lean_strict_probe.as_ref().map(|l| &l.outcome),
            Some(TerminalOutcome::CaptureRefused { .. })
        ),
        "StrictVerbatim must refuse scheduled call overrides: {:#?}",
        global_rep.lean_strict_probe
    );
    match &global_rep.lean.as_ref().unwrap().outcome {
        TerminalOutcome::Returned { ret, .. } => assert_eq!(ret, &TraceVal::u32(52)),
        other => panic!("expected Returned(52), got {other:?}"),
    }
}

#[test]
fn windows_temp_and_profile_env_preserved_across_all_supervised_invocations() {
    use std::ffi::OsStr;

    let win_temp = std::ffi::OsString::from(r"C:\Users\runner\AppData\Local\Temp");
    let win_tmp = std::ffi::OsString::from(r"C:\Users\runner\AppData\Local\TmpAlt");
    let win_profile = std::ffi::OsString::from(r"C:\Users\runner");
    let win_local = std::ffi::OsString::from(r"C:\Users\runner\AppData\Local");
    let win_roaming = std::ffi::OsString::from(r"C:\Users\runner\AppData\Roaming");
    let win_root = std::ffi::OsString::from(r"C:\Windows");
    let win_path = std::ffi::OsString::from(r"C:\rust\bin;C:\Windows\System32");
    let win_rustup = std::ffi::OsString::from(r"C:\Users\runner\.rustup");
    let win_cargo = std::ffi::OsString::from(r"C:\Users\runner\.cargo");

    // Simulate a standard Windows shell where `TMPDIR` and `HOME` are unset.
    let win_env = |key: &str| -> Option<std::ffi::OsString> {
        match key {
            "TEMP" => Some(win_temp.clone()),
            "TMP" => Some(win_tmp.clone()),
            "USERPROFILE" => Some(win_profile.clone()),
            "LOCALAPPDATA" => Some(win_local.clone()),
            "APPDATA" => Some(win_roaming.clone()),
            "SystemRoot" | "WINDIR" => Some(win_root.clone()),
            "PATH" => Some(win_path.clone()),
            "RUSTUP_HOME" => Some(win_rustup.clone()),
            "CARGO_HOME" => Some(win_cargo.clone()),
            _ => None,
        }
    };

    let tmp = tempfile::tempdir().unwrap();
    let scratch_fallback = tmp.path().join("scratch_fallback");
    let tool = tmp.path().join("tool");
    let src = tmp.path().join("src.rs");
    let bin = tmp.path().join("bin.exe");
    let sysroot = tmp.path().join("sysroot");
    let miri_sr = tmp.path().join("miri_sr");

    let assert_windows_env = |label: &str, inv: &anneal_testkit::Invocation| {
        assert_eq!(
            inv.environment.get(OsStr::new("TEMP")),
            Some(&win_temp),
            "{label}: missing TEMP"
        );
        assert_eq!(inv.environment.get(OsStr::new("TMP")), Some(&win_tmp), "{label}: missing TMP");
        assert_eq!(
            inv.environment.get(OsStr::new("TMPDIR")),
            Some(&win_temp),
            "{label}: TMPDIR should mirror non-empty Windows TEMP"
        );
        assert_eq!(
            inv.environment.get(OsStr::new("USERPROFILE")),
            Some(&win_profile),
            "{label}: missing USERPROFILE"
        );
        assert_eq!(
            inv.environment.get(OsStr::new("LOCALAPPDATA")),
            Some(&win_local),
            "{label}: missing LOCALAPPDATA"
        );
        assert_eq!(
            inv.environment.get(OsStr::new("APPDATA")),
            Some(&win_roaming),
            "{label}: missing APPDATA"
        );
        assert_eq!(
            inv.environment.get(OsStr::new("SystemRoot")),
            Some(&win_root),
            "{label}: missing SystemRoot"
        );
        assert_eq!(
            inv.environment.get(OsStr::new("WINDIR")),
            Some(&win_root),
            "{label}: missing WINDIR"
        );
    };

    let base_fwd = forward_platform_temp_and_profile_env_with_env(
        anneal_testkit::Invocation::new(&tool, &[]),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("base_fwd", &base_fwd);

    let std_fwd = forward_standard_tool_env_with_env(
        anneal_testkit::Invocation::new(&tool, &[]),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("std_fwd", &std_fwd);
    assert_eq!(std_fwd.environment.get(OsStr::new("PATH")), Some(&win_path));
    assert_eq!(std_fwd.environment.get(OsStr::new("RUSTUP_HOME")), Some(&win_rustup));
    assert_eq!(std_fwd.environment.get(OsStr::new("CARGO_HOME")), Some(&win_cargo));

    let rustc_compile = build_rustc_compile_invocation_with_env(
        &tool,
        "x86_64-pc-windows-msvc",
        2,
        &src,
        &bin,
        Some(&sysroot),
        Some(win_path.as_os_str()),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("rustc_compile", &rustc_compile);

    let rustc_run = build_rustc_run_invocation_with_env(
        &bin,
        Some(&sysroot),
        Some(win_path.as_os_str()),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("rustc_run", &rustc_run);

    let lean_inv =
        build_lean_invocation_with_env(&tool, "lean/path", &[], Some(&scratch_fallback), win_env);
    assert_windows_env("lean_inv", &lean_inv);
    assert_eq!(lean_inv.environment.get(OsStr::new("RUSTUP_HOME")), Some(&win_rustup));

    let cap_inv = build_capture_invocation_with_env(
        &tool,
        &src,
        "cap_crate",
        "x86_64-pc-windows-msvc",
        tmp.path(),
        &sysroot,
        OsStr::new("lib"),
        win_path.as_os_str(),
        &[],
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("cap_inv", &cap_inv);

    let cargo_cap_inv = build_capture_cargo_invocation_with_env(
        &tool,
        &tmp.path().join("Cargo.toml"),
        tmp.path(),
        &tool,
        &sysroot,
        OsStr::new("lib"),
        win_path.as_os_str(),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("cargo_cap_inv", &cargo_cap_inv);

    let miri_run_inv = build_miri_run_invocation_with_env(
        &tool,
        "x86_64-pc-windows-msvc",
        "/work=/src",
        &miri_sr,
        &src,
        OsStr::new("lib"),
        win_path.as_os_str(),
        Some(&scratch_fallback),
        win_env,
    );
    assert_windows_env("miri_run_inv", &miri_run_inv);

    let mir_eval_inv =
        build_mir_eval_invocation_with_env(&tool, &[], Some(&scratch_fallback), win_env);
    assert_windows_env("mir_eval_inv", &mir_eval_inv);
    assert_eq!(mir_eval_inv.environment.get(OsStr::new("PATH")), Some(&win_path));

    let scratch_home = tmp.path().join("miri_home");
    let scratch_cargo = tmp.path().join("miri_cargo");
    let scratch_miri_tmp = tmp.path().join("miri_tmp");
    let miri_setup_inv = build_miri_setup_invocation_with_env(
        &sysroot,
        &tool,
        &tool,
        &tool,
        &tool,
        "x86_64-pc-windows-msvc",
        &miri_sr,
        &scratch_home,
        &scratch_cargo,
        &scratch_miri_tmp,
        win_path.as_os_str(),
        win_env,
    )
    .expect("build_miri_setup_invocation_with_env");
    assert_eq!(
        miri_setup_inv.environment.get(OsStr::new("TEMP")),
        Some(&scratch_miri_tmp.as_os_str().to_os_string())
    );
    assert_eq!(
        miri_setup_inv.environment.get(OsStr::new("TMP")),
        Some(&scratch_miri_tmp.as_os_str().to_os_string())
    );
    assert_eq!(
        miri_setup_inv.environment.get(OsStr::new("USERPROFILE")),
        Some(&scratch_home.as_os_str().to_os_string())
    );
    assert_eq!(miri_setup_inv.environment.get(OsStr::new("SystemRoot")), Some(&win_root));

    // When all platform temp variables are unset/empty, `fallback_temp` must
    // populate `TMPDIR`, `TEMP`, and `TMP` cleanly.
    let empty_rustc = build_rustc_compile_invocation_with_env(
        &tool,
        "x86_64-pc-windows-msvc",
        0,
        &src,
        &bin,
        None,
        None,
        Some(&scratch_fallback),
        |_| None,
    );
    for key in ["TMPDIR", "TEMP", "TMP"] {
        assert_eq!(
            empty_rustc.environment.get(OsStr::new(key)),
            Some(&scratch_fallback.as_os_str().to_os_string()),
            "fallback must assign {key} when no host temp variable is set"
        );
    }

    // Also verify `run_supervised_with_prefix` assigns a writable scratch
    // tempdir automatically when an `Invocation` carries no temp variables.
    #[cfg(unix)]
    {
        let script = tmp.path().join("print_temp.sh");
        fs::write(
            &script,
            "#!/usr/bin/env bash\nprintf 'TMPDIR=%s\\nTEMP=%s\\nTMP=%s\\n' \"$TMPDIR\" \"$TEMP\" \"$TMP\"\n",
        )
        .unwrap();
        let mut perms = fs::metadata(&script).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&script, perms).unwrap();

        let bare_inv = anneal_testkit::Invocation::new(&script, &[])
            .env("PATH", env::var_os("PATH").unwrap_or_default());
        let out = run_supervised_with_prefix("anneal-itree-env-test-", &bare_inv, None, 10)
            .expect("run print_temp.sh under run_supervised_with_prefix");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let mut vals = Vec::new();
        for key in ["TMPDIR=", "TEMP=", "TMP="] {
            let val = stdout
                .lines()
                .find_map(|line| line.strip_prefix(key))
                .unwrap_or_else(|| panic!("missing {key} in {stdout:?}"));
            assert!(!val.is_empty(), "empty {key} in {stdout:?}");
            vals.push(val.to_string());
        }
        assert_eq!(vals[0], vals[1]);
        assert_eq!(vals[1], vals[2]);
    }
}

#[cfg(unix)]
#[test]
fn ready_stamped_lean_and_driver_cache_validation_and_rebuild() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let tmp = tempfile::tempdir().unwrap();
    let lean_prefix = tmp.path().join("mock_lean_prefix");
    let bin_dir = lean_prefix.join("bin");
    let stdlib_dir = lean_prefix.join("lib/lean");
    let cache_root = tmp.path().join("cache_root");
    let compile_log = tmp.path().join("lean_compile.log");
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(&stdlib_dir).unwrap();
    fs::create_dir_all(&cache_root).unwrap();
    fs::write(stdlib_dir.join("Init.olean"), b"mock-init-olean").unwrap();

    let lean_bin = bin_dir.join("lean");
    let mock_lean = format!(
        "#!/usr/bin/env bash\n\
         set -euo pipefail\n\
         if [[ \"$*\" == *\"--version\"* ]]; then\n\
           printf 'Lean (version 4.34.1, mock)\\n'\n\
           exit 0\n\
         fi\n\
         out_path=\"\"\n\
         prev=\"\"\n\
         for arg in \"$@\"; do\n\
           if [[ \"$prev\" == \"-o\" ]]; then\n\
             out_path=\"$arg\"\n\
           fi\n\
           prev=\"$arg\"\n\
         done\n\
         if [[ -n \"$out_path\" ]]; then\n\
           mkdir -p \"$(dirname \"$out_path\")\"\n\
           printf '%s\\n' \"$out_path\" >> '{}'\n\
           printf 'mock-olean:%s\\n' \"$out_path\" > \"$out_path\"\n\
         fi\n",
        compile_log.display(),
    );
    fs::write(&lean_bin, mock_lean).unwrap();
    let mut perms = fs::metadata(&lean_bin).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&lean_bin, perms).unwrap();

    // 1. Cold build populates base + driver .olean caches and manifests.
    let (paths1, driver_key) =
        ensure_lean_and_driver_oleans(&anneal_root, &lean_bin, &stdlib_dir, &cache_root)
            .expect("initial mock lean build");
    let driver_dir = &paths1[0];
    let base_dir = &paths1[1];
    let base_ready = base_dir.join(".anneal-itree-base-ready");
    let driver_ready = driver_dir.join(".anneal-itree-driver-ready");
    let base_key = compute_lean_cache_key(&anneal_root, &lean_bin, &stdlib_dir).unwrap();
    let expected_base = expected_base_olean_rel_paths();
    let expected_base_refs: Vec<&str> = expected_base.iter().map(String::as_str).collect();

    assert!(validate_cached_artifact_manifest(
        base_dir,
        &base_ready,
        &base_key,
        &expected_base_refs
    ));
    assert!(validate_cached_artifact_manifest(
        driver_dir,
        &driver_ready,
        &driver_key,
        &["ITreeDriver.olean"]
    ));

    let calls_1 = fs::read_to_string(&compile_log).unwrap().lines().count();
    assert_eq!(calls_1, expected_base.len() + 1);

    // 2. Warm hit skips compilation completely.
    fs::write(&compile_log, "").unwrap();
    let (paths2, key2) =
        ensure_lean_and_driver_oleans(&anneal_root, &lean_bin, &stdlib_dir, &cache_root)
            .expect("warm cache hit");
    assert_eq!(paths2, paths1);
    assert_eq!(key2, driver_key);
    assert_eq!(fs::read_to_string(&compile_log).unwrap(), "");

    // 3. Partial eviction: delete one middle base `.olean` while leaving
    // `.anneal-itree-base-ready` intact; cache validation must fail and
    // trigger a full base wipe + rebuild (without needlessly rebuilding
    // the still-valid driver cache).
    let victim_base = base_dir.join("Trusted/MirSemantics/Step.olean");
    fs::remove_file(&victim_base).unwrap();
    assert!(base_ready.is_file());
    assert!(!validate_cached_artifact_manifest(
        base_dir,
        &base_ready,
        &base_key,
        &expected_base_refs
    ));
    ensure_lean_and_driver_oleans(&anneal_root, &lean_bin, &stdlib_dir, &cache_root)
        .expect("rebuild after deleted base olean");
    assert!(victim_base.is_file());
    let calls_3 = fs::read_to_string(&compile_log).unwrap().lines().count();
    assert_eq!(calls_3, expected_base.len());

    // 4. Corrupt `ITreeDriver.olean` (0-byte truncation) while keeping
    // `.anneal-itree-driver-ready`: driver cache must wipe and rebuild cleanly.
    fs::write(&compile_log, "").unwrap();
    let driver_olean = driver_dir.join("ITreeDriver.olean");
    fs::write(&driver_olean, b"").unwrap();
    assert!(!validate_cached_artifact_manifest(
        driver_dir,
        &driver_ready,
        &driver_key,
        &["ITreeDriver.olean"]
    ));
    ensure_lean_and_driver_oleans(&anneal_root, &lean_bin, &stdlib_dir, &cache_root)
        .expect("rebuild after truncated driver olean");
    assert!(fs::metadata(&driver_olean).unwrap().len() > 0);
    assert_eq!(fs::read_to_string(&compile_log).unwrap().lines().count(), 1);

    // 5. Overwriting `.anneal-itree-base-ready` with legacy `"ok\n"` must
    // invalidate the cache and trigger a full base rebuild.
    fs::write(&compile_log, "").unwrap();
    fs::write(&base_ready, "ok\n").unwrap();
    assert!(!validate_cached_artifact_manifest(
        base_dir,
        &base_ready,
        &base_key,
        &expected_base_refs
    ));
    ensure_lean_and_driver_oleans(&anneal_root, &lean_bin, &stdlib_dir, &cache_root)
        .expect("rebuild after legacy ready stamp");
    assert_eq!(fs::read_to_string(&compile_log).unwrap().lines().count(), expected_base.len());

    // 6. Direct manifest integrity helper checks byte corruption.
    let probe_dir = tmp.path().join("manifest_probe");
    fs::create_dir_all(&probe_dir).unwrap();
    fs::write(probe_dir.join("A.olean"), b"alpha").unwrap();
    let probe_stamp = probe_dir.join(".ready");
    write_cached_artifact_manifest(&probe_dir, &probe_stamp, "k1", &["A.olean"]).unwrap();
    assert!(validate_cached_artifact_manifest(&probe_dir, &probe_stamp, "k1", &["A.olean"]));
    fs::write(probe_dir.join("A.olean"), b"zlphe").unwrap();
    assert!(!validate_cached_artifact_manifest(&probe_dir, &probe_stamp, "k1", &["A.olean"]));
}

#[cfg(unix)]
#[test]
fn ready_stamped_capture_cache_validation_and_recapture() {
    let anneal_root = workspace_anneal_root().expect("locate anneal workspace root");
    let tmp = tempfile::tempdir().unwrap();
    let cache_root = tmp.path().join("cap_cache_root");
    let bin_dir = tmp.path().join("bin");
    let rust_sr = tmp.path().join("rust_sysroot");
    let lean_prefix = tmp.path().join("lean_prefix");
    let stdlib_dir = lean_prefix.join("lib/lean");
    let cap_log = tmp.path().join("cap_calls.log");
    fs::create_dir_all(&cache_root).unwrap();
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(rust_sr.join("lib")).unwrap();
    fs::create_dir_all(&stdlib_dir).unwrap();
    fs::create_dir_all(lean_prefix.join("bin")).unwrap();

    let cap_bin = bin_dir.join("anneal-rustc-capture");
    let mock_cap = format!(
        "#!/usr/bin/env bash\n\
         set -euo pipefail\n\
         out_dir=\"\"\n\
         prev=\"\"\n\
         for arg in \"$@\"; do\n\
           if [[ \"$prev\" == \"--out-dir\" ]]; then\n\
             out_dir=\"$arg\"\n\
           fi\n\
           prev=\"$arg\"\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         printf '{{\"program\":{{\"bodies\":[{{\"identity\":\"mock_callee\"}}]}}}}\\n' > \"$out_dir/capture.json\"\n\
         printf -- '-- mock captured lean\\n' > \"$out_dir/Captured.lean\"\n\
         printf 'cap\\n' >> '{}'\n\
         printf '{{\"status\":\"captured\",\"capture\":\"%s\",\"lean\":\"%s\"}}\\n' \"$out_dir/capture.json\" \"$out_dir/Captured.lean\"\n",
        cap_log.display(),
    );
    fs::write(&cap_bin, mock_cap).unwrap();
    let mut cap_perms = fs::metadata(&cap_bin).unwrap().permissions();
    cap_perms.set_mode(0o755);
    fs::set_permissions(&cap_bin, cap_perms).unwrap();

    let lean_bin = lean_prefix.join("bin/lean");
    let mock_lean = "#!/usr/bin/env bash\n\
         set -euo pipefail\n\
         out_path=\"\"\n\
         prev=\"\"\n\
         for arg in \"$@\"; do\n\
           if [[ \"$prev\" == \"-o\" ]]; then\n\
             out_path=\"$arg\"\n\
           fi\n\
           prev=\"$arg\"\n\
         done\n\
         if [[ -n \"$out_path\" ]]; then\n\
           mkdir -p \"$(dirname \"$out_path\")\"\n\
           printf 'mock-captured-olean\\n' > \"$out_path\"\n\
         fi\n";
    fs::write(&lean_bin, mock_lean).unwrap();
    let mut lean_perms = fs::metadata(&lean_bin).unwrap().permissions();
    lean_perms.set_mode(0o755);
    fs::set_permissions(&lean_bin, lean_perms).unwrap();

    let session = LeanTraceSession {
        anneal_root,
        cache_root: cache_root.clone(),
        capture_bin: cap_bin,
        capture_bin_sha256: "cap_sha".to_string(),
        rust_sysroot: rust_sr,
        host_target: "x86_64-unknown-linux-gnu".to_string(),
        rustc_version_digest: "rustc_dig".to_string(),
        lean_bin,
        lean_driver_digest: "drv_dig".to_string(),
        olean_paths: vec![stdlib_dir],
        dylib_search_path: std::ffi::OsString::new(),
        child_path: env::var_os("PATH").unwrap_or_default(),
    };
    let work_dir = tmp.path().join("work");
    fs::create_dir_all(&work_dir).unwrap();
    let sel = vec!["mock_callee".to_string()];

    // 1. Cold capture builds capture outputs + Captured.olean + `.captured-ok`.
    let arts =
        match session.capture_rust_source(&work_dir, "krate", "pub fn mock_callee() {}", &sel) {
            CaptureAttempt::Captured(a) => a,
            other => panic!("expected Captured, got {other:?}"),
        };
    let cap_cache_dir = arts.capture_dir.parent().unwrap().to_path_buf();
    assert!(cap_cache_dir.join(".captured-ok").is_file());
    assert_eq!(fs::read_to_string(&cap_log).unwrap().lines().count(), 1);

    // 2. Warm capture cache hit invokes capture 0 times.
    match session.capture_rust_source(&work_dir, "krate", "pub fn mock_callee() {}", &sel) {
        CaptureAttempt::Captured(_) => {}
        other => panic!("expected warm Captured hit, got {other:?}"),
    }
    assert_eq!(fs::read_to_string(&cap_log).unwrap().lines().count(), 1);

    // 3. Truncating `Captured.olean` while keeping `.captured-ok` must wipe
    // and re-capture + re-compile cleanly.
    let cap_olean = arts.olean_dir.join("Captured.olean");
    fs::write(&cap_olean, b"").unwrap();
    let arts_rebuilt =
        match session.capture_rust_source(&work_dir, "krate", "pub fn mock_callee() {}", &sel) {
            CaptureAttempt::Captured(a) => a,
            other => panic!("expected re-Captured after corrupt olean, got {other:?}"),
        };
    assert!(fs::metadata(arts_rebuilt.olean_dir.join("Captured.olean")).unwrap().len() > 0);
    assert_eq!(fs::read_to_string(&cap_log).unwrap().lines().count(), 2);

    // 4. Legacy/torn or wrong-key `.captured-refused` must not short-circuit.
    fs::remove_file(cap_cache_dir.join(".captured-ok")).unwrap();
    fs::write(cap_cache_dir.join(".captured-refused"), "torn-non-json\n").unwrap();
    match session.capture_rust_source(&work_dir, "krate", "pub fn mock_callee() {}", &sel) {
        CaptureAttempt::Captured(_) => {}
        other => panic!("torn .captured-refused must trigger fresh capture, got {other:?}"),
    }
    assert_eq!(fs::read_to_string(&cap_log).unwrap().lines().count(), 3);

    // 5. Key-bound `.captured-refused` hits on matching refusal, rejects stale
    // key or empty reason.
    let unsup_cap = tmp.path().join("bin/anneal-rustc-capture-refuse");
    let unsup_log = tmp.path().join("refuse_calls.log");
    let mock_unsup = format!(
        "#!/usr/bin/env bash\n\
         printf 'refuse\\n' >> '{}'\n\
         printf '{{\"status\":\"unsupported\",\"reason\":\"unsupported MIR op\"}}\\n'\n\
         exit 1\n",
        unsup_log.display(),
    );
    fs::write(&unsup_cap, mock_unsup).unwrap();
    let mut unsup_perms = fs::metadata(&unsup_cap).unwrap().permissions();
    unsup_perms.set_mode(0o755);
    fs::set_permissions(&unsup_cap, unsup_perms).unwrap();
    let mut unsup_session = session;
    unsup_session.capture_bin = unsup_cap;
    match unsup_session.capture_rust_source(&work_dir, "krate", "pub fn mock_refuse() {}", &sel) {
        CaptureAttempt::Refused { reason } => assert!(reason.contains("unsupported MIR op")),
        other => panic!("expected Refused, got {other:?}"),
    }
    assert_eq!(fs::read_to_string(&unsup_log).unwrap().lines().count(), 1);
    match unsup_session.capture_rust_source(&work_dir, "krate", "pub fn mock_refuse() {}", &sel) {
        CaptureAttempt::Refused { reason } => assert!(reason.contains("unsupported MIR op")),
        other => panic!("expected cached Refused hit, got {other:?}"),
    }
    assert_eq!(fs::read_to_string(&unsup_log).unwrap().lines().count(), 1);
}

#[cfg(unix)]
#[test]
fn miri_built_sysroot_artifact_manifest_rejects_partial_eviction_and_corruption() {
    use std::os::unix::fs::symlink;

    let tmp = tempfile::tempdir().unwrap();
    let sr = tmp.path().join("active_sysroot");
    let cache_dir = tmp.path().join("miri_cache");
    let built_miri_sr = tmp.path().join("miri_built_sysroot");
    fs::create_dir_all(sr.join("bin")).unwrap();
    fs::create_dir_all(sr.join("lib")).unwrap();
    fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/core/src")).unwrap();
    fs::create_dir_all(sr.join("lib/rustlib/src/rust/library/alloc/src")).unwrap();
    let mock_host = format!("{}-unknown-linux-gnu", env::consts::ARCH);
    let target_lib_dir = built_miri_sr.join(format!("lib/rustlib/{mock_host}/lib"));
    fs::create_dir_all(&target_lib_dir).unwrap();

    let canon_sr = fs::canonicalize(&sr).unwrap();
    let write_exec = |path: &std::path::Path, body: &str| {
        fs::write(path, body).unwrap();
        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    };
    let rustc_bin = sr.join("bin/rustc");
    let miri_bin = sr.join("bin/miri");
    let cargo_bin = sr.join("bin/cargo");
    write_exec(
        &rustc_bin,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then printf '%s\\n' '{}'; exit 0; fi\nprintf 'rustc 1.98.0-nightly (mock 2026-05-30)\\nhost: {}\\n'\n",
            canon_sr.display(),
            mock_host,
        ),
    );
    write_exec(
        &miri_bin,
        &format!(
            "#!/usr/bin/env bash\nif [[ \"$*\" == *\"--print sysroot\"* ]]; then printf '%s\\n' '{}'; exit 0; fi\nprintf 'miri 0.1.0 (mock 2026-05-30)\\n'\n",
            canon_sr.display()
        ),
    );
    write_exec(&cargo_bin, "#!/usr/bin/env bash\nexit 0\n");
    fs::write(sr.join("lib/librustc_driver-mock.so"), b"driver-a").unwrap();
    let rust_src = sr.join("lib/rustlib/src/rust");
    fs::write(rust_src.join("library/Cargo.lock"), "version = 4\n").unwrap();
    fs::write(rust_src.join("library/core/Cargo.toml"), "[package]\nname = \"core\"\n").unwrap();
    fs::write(rust_src.join("library/alloc/Cargo.toml"), "[package]\nname = \"alloc\"\n").unwrap();
    fs::write(rust_src.join("library/core/src/lib.rs"), "// core\n").unwrap();

    let id = MiriSysrootIdentity::compute(&canon_sr, &miri_bin, Some(&cargo_bin)).unwrap();
    let ready_stamp = built_miri_sr.join(".anneal-itree-miri-ready");
    id.write_ready_stamp(&ready_stamp).unwrap();

    // Missing any compiled `.rlib`/`.rmeta` must fail artifact manifest
    // creation and validation.
    assert!(id.write_built_artifacts_manifest(&built_miri_sr).is_err());
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));

    let libcore_rlib = target_lib_dir.join("libcore-1.rlib");
    let liballoc_rmeta = target_lib_dir.join("liballoc-1.rmeta");
    fs::write(&libcore_rlib, b"rlib-core-v1").unwrap();
    fs::write(&liballoc_rmeta, b"rmeta-alloc-v1").unwrap();
    id.write_built_artifacts_manifest(&built_miri_sr).unwrap();
    assert!(id.validate_built_artifacts_manifest(&built_miri_sr));

    let probe = || {
        MiriRunner::probe_with_env(&cache_dir, Some(&sr), |k| {
            if k == "ANNEAL_ITREE_MIRI_SYSROOT" {
                Some(built_miri_sr.as_os_str().to_os_string())
            } else {
                None
            }
        })
    };
    assert!(matches!(probe(), MiriAvailability::Available(_)));

    // Corrupt byte in `.rlib` -> fails probe & validation.
    fs::write(&libcore_rlib, b"rlib-core-X1").unwrap();
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));
    assert!(matches!(probe(), MiriAvailability::InvalidConfig { .. }));

    // Restore valid, then truncate to 0 bytes -> fails.
    fs::write(&libcore_rlib, b"").unwrap();
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));

    // Delete `.rlib` -> fails.
    fs::remove_file(&libcore_rlib).unwrap();
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));

    // Symlink inside `lib/rustlib` -> fails closed.
    let outside = tmp.path().join("outside.rlib");
    fs::write(&outside, b"rlib-core-v1").unwrap();
    symlink(&outside, &libcore_rlib).unwrap();
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));
    assert!(matches!(probe(), MiriAvailability::InvalidConfig { .. }));

    // Delete `.anneal-itree-miri-artifacts.json` even with intact ready stamp
    // -> explicit `ANNEAL_ITREE_MIRI_SYSROOT` must fail closed!
    fs::remove_file(&libcore_rlib).unwrap();
    fs::write(&libcore_rlib, b"rlib-core-v1").unwrap();
    id.write_built_artifacts_manifest(&built_miri_sr).unwrap();
    assert!(matches!(probe(), MiriAvailability::Available(_)));
    fs::remove_file(built_miri_sr.join(".anneal-itree-miri-artifacts.json")).unwrap();
    assert!(!id.validate_built_artifacts_manifest(&built_miri_sr));
    assert!(matches!(probe(), MiriAvailability::InvalidConfig { .. }));
}

#[cfg(unix)]
#[test]
fn toolchain_discovery_probes_timeout_fail_closed() {
    let tmp = tempfile::tempdir().unwrap();
    let slow_script = tmp.path().join("slow-probe-wrapper");
    fs::write(&slow_script, "#!/usr/bin/env bash\nsleep 30\n").unwrap();
    let mut perms = fs::metadata(&slow_script).unwrap().permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&slow_script, perms).unwrap();

    let sysroot_err = query_rustc_sysroot_with_timeout(&slow_script, 1)
        .expect_err("hung rustc --print sysroot wrapper must time out");
    assert!(sysroot_err.contains("timed out"), "got: {sysroot_err}");

    let target_err = query_rustc_host_target_with_timeout(&slow_script, None, 1)
        .expect_err("hung rustc -vV wrapper must time out");
    assert!(target_err.contains("timed out"), "got: {target_err}");

    let miri_err = query_miri_sysroot_with_timeout(&slow_script, 1)
        .expect_err("hung miri --print sysroot wrapper must time out");
    assert!(miri_err.contains("timed out"), "got: {miri_err}");
}

#[test]
fn strict_verbatim_direct_mode_requires_refusal_on_multicall_specs() {
    let mk_leg = |auth: &str, outcome: TerminalOutcome| AuthorityRunResult {
        authority: auth.to_string(),
        outcome,
        spine: ObservableSpine::default(),
        caller_frame_law: CallerFrameLaw::all_satisfied(),
        tool_error: None,
        raw_diagnostics: String::new(),
        elapsed_ms: 1,
        post_only_mem_digest: false,
        entry_mem_digest: None,
    };
    let mk_rustc = |outcome: TerminalOutcome| RustcDualResult {
        o0: mk_leg("rustc-O0", outcome.clone()),
        o2: mk_leg("rustc-O2", outcome),
        parity_ok: true,
        skipped_for_ub: false,
        mismatch_detail: None,
    };

    let ret_out = TerminalOutcome::Returned {
        ret: TraceVal::u32(7),
        mem_digest: compute_boundary_mem_digest(&[vec![
            Some(0x10),
            Some(7),
            Some(0),
            Some(0),
            Some(0),
        ]]),
    };
    let unw_out =
        TerminalOutcome::Unwound { mem_digest: compute_boundary_mem_digest(&[vec![Some(0x20)]]) };
    let abt_out =
        TerminalOutcome::Aborted { mem_digest: compute_boundary_mem_digest(&[vec![Some(0x30)]]) };
    let ref_out = TerminalOutcome::CaptureRefused { reason: "unsupported call".to_string() };
    let div_out = TerminalOutcome::Diverged { fuel: 64 };
    let cons_verdict = TraceVerdict::ConservativeOverApprox {
        reason: "unsupported call".to_string(),
        ub_refutation_disallowed: true,
        undeclared_ub_fault: false,
    };
    let deg_no_miri = TraceVerdict::DegradedNoMiri { detail: "no miri".to_string() };

    let multicall_external = LeanProgramSpec::MultiCallWithCapturedCallees {
        crate_name: "cat4_helpers".to_string(),
        captured_callees: vec!["ext_transform_u32".to_string()],
        caller_identity: "caller".to_string(),
        caller_lean_body:
            "{ basicBlocks := [{ terminator := .call 1 [] ⟨0, []⟩ none .continue_ }] }".to_string(),
        external_callees: vec!["ext_transform_u32".to_string()],
    };
    let multicall_cleanup = LeanProgramSpec::MultiCallWithCapturedCallees {
        crate_name: "cat4_helpers".to_string(),
        captured_callees: vec!["ext_transform_u32".to_string()],
        caller_identity: "caller".to_string(),
        caller_lean_body:
            "{ basicBlocks := [{ terminator := .call 1 [] ⟨0, []⟩ none (.cleanup 1) }] }"
                .to_string(),
        external_callees: Vec::new(),
    };
    let multicall_intracall = LeanProgramSpec::MultiCallWithCapturedCallees {
        crate_name: "cat4_helpers".to_string(),
        captured_callees: vec!["ext_transform_u32".to_string()],
        caller_identity: "caller".to_string(),
        caller_lean_body:
            "{ basicBlocks := [{ terminator := .call 1 [] ⟨0, []⟩ none .continue_ }] }".to_string(),
        external_callees: Vec::new(),
    };
    let call_free_synthetic = LeanProgramSpec::SyntheticMirAst {
        program_lean_expr: "{ bodies := [{ basicBlocks := [{ terminator := .return_ }] }] }"
            .to_string(),
        external_callees: Vec::new(),
    };
    assert!(multicall_external.requires_strict_refusal());
    assert!(multicall_cleanup.requires_strict_refusal());
    assert!(!multicall_intracall.requires_strict_refusal());
    assert!(!call_free_synthetic.requires_strict_refusal());

    // Verify exact curated corpus strict-refusal expectations:
    // external-callee schedules and `.cleanup`/`.unwindResume` bodies require
    // StrictVerbatim refusal, while pure intra-crate calls and single-body
    // probes run directly under `evalMirStepBy`.
    for case in curated_corpus() {
        let should_refuse = matches!(
            case.id.as_str(),
            "cat4_callee_panic_unwind_cleanup"
                | "cat4_scheduled_return_bytes_override"
                | "cat4_scheduled_abort_no_drop"
                | "cat4_scheduled_invalid_bool_return_ub"
        );
        assert_eq!(
            case.lean_program_spec.requires_strict_refusal(),
            should_refuse,
            "unexpected strict refusal classification for corpus case {}",
            case.id
        );
        assert_eq!(
            case.requires_strict_refusal(),
            should_refuse,
            "unexpected case strict refusal classification for {}",
            case.id
        );
    }

    let mut sched_override_case = curated_corpus()
        .into_iter()
        .find(|c| c.id == "cat4_call_once_and_postprocess")
        .expect("cat4_call_once_and_postprocess must exist");
    assert!(!sched_override_case.requires_strict_refusal());
    sched_override_case.env_schedule.push_global(EnvAction::ReturnBytes(vec![7, 0, 0, 0]));
    assert!(sched_override_case.requires_strict_refusal());

    // Direct `--mode strict` runs on external/cleanup multi-call
    // Agree/Unwind/Abort cases MUST require CaptureRefused +
    // ConservativeOverApprox, rejecting silent Agree, DegradedNoMiri, Returned,
    // Unwound, Aborted, and Diverged outcomes.
    for (expected, ref_o) in [
        (ExpectedCaseClass::Agree, ret_out.clone()),
        (ExpectedCaseClass::Unwind, unw_out.clone()),
        (ExpectedCaseClass::Abort, abt_out.clone()),
    ] {
        assert!(
            check_case_expectation(
                expected,
                None,
                None,
                CaseCategory::MultiCallChain,
                &multicall_external,
                &cons_verdict,
                &mk_rustc(ref_o.clone()),
                Some(&mk_leg("miri", ref_o.clone())),
                Some(&mk_leg("lean", ref_out.clone())),
                LeanTraceMode::StrictVerbatim,
            )
            .is_none(),
            "StrictVerbatim CaptureRefused should pass for multi-call {expected:?}"
        );
        assert!(
            check_case_expectation(
                expected,
                None,
                None,
                CaseCategory::MultiCallChain,
                &multicall_external,
                &TraceVerdict::Agree,
                &mk_rustc(ref_o.clone()),
                Some(&mk_leg("miri", ref_o.clone())),
                Some(&mk_leg("lean", ref_o.clone())),
                LeanTraceMode::StrictVerbatim,
            )
            .is_some(),
            "StrictVerbatim executing multi-call {expected:?} to Agree must fail"
        );
        assert!(
            check_case_expectation(
                expected,
                None,
                None,
                CaseCategory::MultiCallChain,
                &multicall_external,
                &deg_no_miri,
                &mk_rustc(ref_o.clone()),
                None,
                Some(&mk_leg("lean", ref_o.clone())),
                LeanTraceMode::StrictVerbatim,
            )
            .is_some(),
            "StrictVerbatim without Miri executing multi-call {expected:?} must fail"
        );
        assert!(
            check_case_expectation(
                expected,
                None,
                None,
                CaseCategory::MultiCallChain,
                &multicall_external,
                &cons_verdict,
                &mk_rustc(ref_o.clone()),
                Some(&mk_leg("miri", ref_o.clone())),
                Some(&mk_leg("lean", div_out.clone())),
                LeanTraceMode::StrictVerbatim,
            )
            .is_some(),
            "StrictVerbatim Diverged on multi-call {expected:?} must fail"
        );
    }

    // Pure intra-crate call specs require matching execution in both
    // `StrictVerbatim` and `validate_strict_multicall_probe_for_spec`.
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_intracall,
            &cons_verdict,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out.clone())),
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::StrictVerbatim,
        )
        .is_some(),
        "pure intra-crate call in StrictVerbatim must reject spurious CaptureRefused"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::MultiCallChain,
            &multicall_intracall,
            &TraceVerdict::Agree,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out.clone())),
            Some(&mk_leg("lean", ret_out.clone())),
            LeanTraceMode::StrictVerbatim,
        )
        .is_none(),
        "pure intra-crate call in StrictVerbatim passes when matching Returned + Agree"
    );
    let mut called_primary = mk_leg("lean", ret_out.clone());
    called_primary.spine.events.push(
        anneal_itree_diff::trace_observer::ObservableEvent::CallEnter {
            callee: "ext_transform_u32".to_string(),
            arg_bytes: vec![],
            arg_reprs: vec![],
        },
    );
    assert!(
        anneal_itree_diff::validate_strict_multicall_probe_for_spec(
            &multicall_intracall,
            &called_primary,
            &mk_leg("lean", ret_out.clone()),
            &TraceVerdict::Agree,
        )
        .is_none()
    );
    assert!(
        anneal_itree_diff::validate_strict_multicall_probe_for_spec(
            &multicall_intracall,
            &called_primary,
            &mk_leg("lean", ref_out.clone()),
            &cons_verdict,
        )
        .is_some()
    );
    assert!(
        anneal_itree_diff::validate_strict_multicall_probe_for_spec(
            &multicall_external,
            &called_primary,
            &mk_leg("lean", ref_out.clone()),
            &cons_verdict,
        )
        .is_none()
    );

    // Call-free SyntheticMirAst (like single-body cat6 probes) still rejects
    // spurious CaptureRefused on Agree and permits FaultUb on UB probes.
    assert!(
        check_case_expectation(
            ExpectedCaseClass::Agree,
            None,
            None,
            CaseCategory::ScalarBitwise,
            &call_free_synthetic,
            &cons_verdict,
            &mk_rustc(ret_out.clone()),
            Some(&mk_leg("miri", ret_out)),
            Some(&mk_leg("lean", ref_out.clone())),
            LeanTraceMode::StrictVerbatim,
        )
        .is_some()
    );
    let sched_ub_spec = ExpectedUbSpec::new(
        UbFaultClass::ScheduledReturnDecode,
        "scheduled ReturnBytes invalid",
        Some("invalid scheduled ReturnBytes"),
    );
    let miri_sched_ub =
        mk_leg("miri", TerminalOutcome::FaultUb { detail: "scheduled ReturnBytes invalid".into() });
    let lean_sched_ub =
        mk_leg("lean", TerminalOutcome::FaultUb { detail: "invalid scheduled ReturnBytes".into() });
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&sched_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_external,
            &TraceVerdict::Agree,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&miri_sched_ub),
            Some(&lean_sched_ub),
            LeanTraceMode::StrictVerbatim,
        )
        .is_some(),
        "external multi-call UB probe in StrictVerbatim must fail if it does not refuse .call"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&sched_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_external,
            &cons_verdict,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&miri_sched_ub),
            Some(&mk_leg("lean", ref_out)),
            LeanTraceMode::StrictVerbatim,
        )
        .is_none(),
        "external multi-call UB probe in StrictVerbatim passes when it returns CaptureRefused"
    );
    let dual_sched_ub_spec = sched_ub_spec
        .clone()
        .with_lean_refusal_marker("external callee unsupported in StrictVerbatim: ext_oracle_bool");
    let expected_strict_refusal = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused {
            reason: "external callee unsupported in StrictVerbatim: ext_oracle_bool".to_string(),
        },
    );
    let unrelated_strict_refusal = mk_leg(
        "lean",
        TerminalOutcome::CaptureRefused { reason: "initStateBy unsupported".to_string() },
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&dual_sched_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_external,
            &cons_verdict,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&miri_sched_ub),
            Some(&expected_strict_refusal),
            LeanTraceMode::StrictVerbatim,
        )
        .is_none(),
        "strict multi-call UB probe with matching lean_refusal_marker passes"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&dual_sched_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_external,
            &cons_verdict,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&miri_sched_ub),
            Some(&unrelated_strict_refusal),
            LeanTraceMode::StrictVerbatim,
        )
        .is_some(),
        "strict multi-call UB probe must reject unrelated CaptureRefused when lean_refusal_marker is set"
    );
    assert!(
        check_case_expectation(
            ExpectedCaseClass::UndefinedBehavior,
            Some(&dual_sched_ub_spec),
            None,
            CaseCategory::MultiCallChain,
            &multicall_external,
            &TraceVerdict::Agree,
            &RustcDualResult::skipped_for_ub("ub"),
            Some(&miri_sched_ub),
            Some(&lean_sched_ub),
            LeanTraceMode::CompositionalITree,
        )
        .is_none(),
        "dual strict+compositional UB markers still pass CompositionalITree FaultUb"
    );
}

#[test]
fn fault_ub_enforces_entry_input_parity_and_pre_entry_authentication() {
    // 1. Standalone harness emits `emit_pre_entry_slots()` before subject call.
    let corpus = curated_corpus();
    let shift_case = corpus
        .iter()
        .find(|c| c.id == "cat6_shift_overflow_ub")
        .expect("cat6_shift_overflow_ub must exist");
    let harness = render_standalone_rust_harness(shift_case);
    let pre_idx = harness
        .find("anneal_rt::emit_pre_entry_slots();")
        .expect("harness must flush pre-entry slots before calling subject");
    let call_idx =
        harness.find("subject::shift_overflow_ub").expect("harness must invoke subject entry");
    assert!(pre_idx < call_idx, "pre-entry flush must precede subject entry invocation");

    // 2. Miri UB parser extracts and validates `ANNEAL_ITREE_PRE_ENTRY:` when
    //    `expected_entry_slots` is set and rejects missing/duplicate/skewed
    //    pre-entry framing.
    let auth_tok = "__anneal_miri_auth_shift_test__";
    let miri_ub_stderr = format!(
        concat!(
            r#"{{"$message_type":"diagnostic","message":"Undefined Behavior: overflowing shift by 33 in `unchecked_shl`","level":"error","spans":[{{"file_name":"{tok}/harness.rs"}}],"children":[{{"level":"help","message":"this indicates a bug in the program: it performed an invalid operation, and caused Undefined Behavior","spans":[]}}]}}"#,
            "\n",
            r#"{{"$message_type":"diagnostic","message":"aborting due to 1 previous error","level":"error","spans":[],"children":[]}}"#,
            "\n"
        ),
        tok = auth_tok
    );
    let pre_33 = format!("{PRE_ENTRY_JSON_PREFIX}{{\"boundary_slots\":[[1,0,0,0],[33,0,0,0]]}}\n");
    let miri_33 = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        &pre_33,
        &miri_ub_stderr,
        5,
        Some(2),
        Some(auth_tok),
    );
    assert!(miri_33.tool_error.is_none(), "unexpected error: {:?}", miri_33.tool_error);
    assert!(matches!(miri_33.outcome, TerminalOutcome::FaultUb { .. }));
    let expected_dig_33 = compute_boundary_mem_digest(&[
        vec![Some(1), Some(0), Some(0), Some(0)],
        vec![Some(33), Some(0), Some(0), Some(0)],
    ]);
    assert_eq!(miri_33.entry_mem_digest.as_deref(), Some(expected_dig_33.as_str()));

    let missing_pre = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        "",
        &miri_ub_stderr,
        5,
        Some(2),
        Some(auth_tok),
    );
    assert!(
        missing_pre.tool_error.is_some(),
        "missing PRE_ENTRY with expected_entry_slots must fail"
    );

    let dup_pre = format!("{pre_33}{pre_33}");
    let dup_res = parse_miri_run_output_authenticated(
        "miri",
        Some(1),
        None,
        &dup_pre,
        &miri_ub_stderr,
        5,
        Some(2),
        Some(auth_tok),
    );
    assert!(dup_res.tool_error.is_some(), "duplicate PRE_ENTRY must fail closed");

    let parsed_pre = parse_pre_entry_slots_stdout("miri", &pre_33, "", Some(2))
        .expect("valid pre-entry line")
        .expect("non-empty pre-entry slots");
    assert_eq!(parsed_pre.len(), 2);

    // 3. Lean UB parser preserves entry digest from `bSlots`, and mismatched
    //    inputs (shift 33 in Miri vs shift 32 in Lean) MUST fail as
    //    `UnsoundAccept` rather than `Agree`.
    let lean_ub_32_json = concat!(
        r#"ANNEAL_LEAN_ITREE_JSON:{"outcome_kind":"fault_undefined","ret":null,"#,
        r#""detail":"unchecked shift overflow: Trusted.MirSemantics.FaultKind.undefined","#,
        r#""fuel":128,"boundary_slots":[[1,0,0,0],[32,0,0,0]],"#,
        r#""caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"#,
        r#""padding_mask_respected":true,"violations":[],"events":[]}"#
    );
    let lean_32 =
        parse_lean_trace_output_with_expected_args("lean", lean_ub_32_json, "", 1, Some(2));
    assert!(lean_32.tool_error.is_none(), "{:?}", lean_32.tool_error);
    let skipped = RustcDualResult::skipped_for_ub("ub");
    let v_mismatch = classify_four_way_with_ub_guard(
        &skipped.o0,
        &skipped.o2,
        true,
        Some(&miri_33),
        Some(&lean_32),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert!(
        matches!(v_mismatch, TraceVerdict::UnsoundAccept { .. }),
        "shift 33 vs 32 FaultUb must fail as UnsoundAccept, got {v_mismatch:?}"
    );

    let lean_ub_33_json = lean_ub_32_json.replace("[32,0,0,0]", "[33,0,0,0]");
    let lean_33 =
        parse_lean_trace_output_with_expected_args("lean", &lean_ub_33_json, "", 1, Some(2));
    let v_match = classify_four_way_with_ub_guard(
        &skipped.o0,
        &skipped.o2,
        true,
        Some(&miri_33),
        Some(&lean_33),
        None,
        SpineCompareMode::OutcomeOnly,
        None,
    );
    assert_eq!(v_match, TraceVerdict::Agree);

    // 4. `ScheduleDecodeFailed` also verifies PRE_ENTRY against TRACE_JSON.
    let sched_ub_json = concat!(
        r#"ANNEAL_ITREE_TRACE_JSON:{"outcome_kind":"fault_ub","ret":null,"#,
        r#""detail":"callee `ext_oracle_bool` scheduled ReturnBytes invalid: bad bool","#,
        r#""boundary_slots":[[1,0,0,0],[33,0,0,0]],"#,
        r#""caller_locals_preserved":true,"untouched_alloc_bytes_preserved":true,"#,
        r#""padding_mask_respected":true,"violations":[],"events":[]}"#,
        "\n"
    );
    let mismatch_sched_stdout = format!(
        "{PRE_ENTRY_JSON_PREFIX}{{\"boundary_slots\":[[1,0,0,0],[32,0,0,0]]}}\n{sched_ub_json}"
    );
    assert!(
        parse_trace_json_stdout_with_expected_args("miri", &mismatch_sched_stdout, "", 1, Some(2))
            .is_err()
    );
    let ok_sched_stdout = format!("{pre_33}{sched_ub_json}");
    let sched_res =
        parse_trace_json_stdout_with_expected_args("miri", &ok_sched_stdout, "", 1, Some(2))
            .expect("matching PRE_ENTRY and TRACE_JSON slots");
    assert_eq!(sched_res.entry_mem_digest.as_deref(), Some(expected_dig_33.as_str()));

    // 5. Value-only `anneal-mir-eval` omitting `boundary_slots` uses
    //    `post_only_mem_digest`, while explicit slots must match Miri and
    //    and non-`post_only` asymmetric `None` entry digests fail closed.
    let me_omitted = parse_mir_eval_output_with_expected_args(
        Some(2),
        r#"{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"unchecked shift overflow"}}}"#,
        "",
        128,
        1,
        None,
        Some(2),
    );
    assert!(me_omitted.post_only_mem_digest);
    assert!(compare_ub_fault_results(&miri_33, &me_omitted).is_ok());

    let me_explicit_32 = parse_mir_eval_output_with_expected_args(
        Some(2),
        r#"{"outcome":{"kind":"fault","value":{"kind":"undefined","reason":"unchecked shift overflow"}},"boundary_slots":[[1,0,0,0],[32,0,0,0]]}"#,
        "",
        128,
        1,
        None,
        Some(2),
    );
    assert!(compare_ub_fault_results(&miri_33, &me_explicit_32).is_err());

    let mut unflagged_none = me_omitted.clone();
    unflagged_none.post_only_mem_digest = false;
    assert!(compare_ub_fault_results(&miri_33, &unflagged_none).is_err());
}

#[test]
fn overlapping_memory_copy_ub_fault_class_matches_miri_copy_nonoverlapping() {
    assert_eq!(
        classify_ub_fault_detail(
            "Undefined Behavior: `copy_nonoverlapping` called on overlapping ranges"
        ),
        UbFaultClass::PointerOrMemoryAccess
    );
    assert_eq!(
        classify_ub_fault_detail("overlapping memory copy in Assign Use"),
        UbFaultClass::PointerOrMemoryAccess
    );
}
