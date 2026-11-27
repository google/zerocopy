// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Live Profile v2 differential canaries: exercises real `anneal-rustc-capture`
//! Profile v2 Rust capture, Lean `Trusted.MirSemantics` kernel proofs, and Miri
//! (`-Zmiri-tree-borrows`) on features already supported on `origin/main`.

use std::{env, fs};

use anneal_itree_diff::{
    lean_trace_runner::{CaptureAttempt, LeanTraceSession, build_lean_invocation_with_env},
    miri_runner::{MiriAvailability, MiriRunner},
    outcome::{IntKind, SpineCompareMode, TerminalOutcome, TraceVal},
    resolve_default_cache_root,
    rustc_runner::run_supervised_with_prefix,
    spec::{CaseCategory, ExpectedCaseClass, LeanProgramSpec, ReturnShape, TraceTestCase},
    trace_observer::EnvSchedule,
    workspace_anneal_root,
};

const PURE_V2_SRC: &str = r#"#![no_std]
pub unsafe fn v2_ptr_add(p: *const u8, off: usize) -> u8 { unsafe { *p.add(off) } }
pub unsafe fn v2_sub(bytes: &[u8], i: usize, d: usize) -> usize {
    unsafe { bytes.get_unchecked(i.unchecked_sub(d)..) }.len()
}
pub fn v2_len(bytes: &[u8]) -> usize { bytes.len() }
pub unsafe fn v2_rw(p: *mut u8, val: u8) -> u8 { unsafe { *p = val; *p } }
pub fn v2_pair(pair: (u32, u8)) -> u32 { pair.0 + ((pair.1 as u32) << 8) }
"#;

const MIRI_WRAPPER_SRC: &str = r#"
pub unsafe fn miri_ptr_read(off: usize) -> u8 { unsafe { v2_ptr_add([10, 42, 22].as_ptr(), off) } }
pub unsafe fn miri_slice_sub(i: usize, d: usize) -> usize { unsafe { v2_sub(&[10, 42, 22], i, d) } }
pub fn miri_slice_len() -> usize { v2_len(&[10u8, 42u8, 22u8]) }
pub unsafe fn miri_write_read(m: u8, v: u8) -> u8 {
    static R: u8 = 0; let mut c = 0u8;
    let p = match m { 0 => &mut c as *mut u8, 1 => core::ptr::null_mut(), _ => (&R as *const u8).cast_mut() };
    unsafe { v2_rw(p, v) }
}
pub fn miri_padded_mix(hi: u32, lo: u8) -> u32 { v2_pair((hi, lo)) }
"#;

const FNS: [&str; 5] = ["v2_ptr_add", "v2_sub", "v2_len", "v2_rw", "v2_pair"];

fn v2_case(id: &str, entry: &str, args: &[&str], kind: IntKind, ub: bool) -> TraceTestCase {
    let miri_fns = ["miri_ptr_read", "miri_slice_sub", "miri_slice_len", "miri_write_read"];
    let i = miri_fns.iter().position(|e| *e == entry).unwrap_or(4);
    let cat = if ub { CaseCategory::NegativeUbAndOverApprox } else { CaseCategory::ScalarBitwise };
    let exp = if ub { ExpectedCaseClass::UndefinedBehavior } else { ExpectedCaseClass::Agree };
    let spec = LeanProgramSpec::CapturedRust {
        crate_name: "v2_canaries".into(),
        select_fn: FNS[i].into(),
    };
    TraceTestCase {
        id: id.into(),
        category: cat,
        pure_rust_source: PURE_V2_SRC.into(),
        traced_rust_source: Some(format!("{PURE_V2_SRC}\n{MIRI_WRAPPER_SRC}")),
        entry_fn: entry.into(),
        rust_arg_exprs: args.iter().map(|s| (*s).to_owned()).collect(),
        lean_args: Vec::new(),
        ret_shape: ReturnShape::Scalar { kind },
        lean_program_spec: spec,
        metamorphic_inlined_twin: None,
        env_schedule: EnvSchedule::default(),
        fuel: 64,
        spine_mode: SpineCompareMode::OutcomeOnly,
        expected_class: exp,
        expected_ub: None,
        expected_conservative: None,
        disclosed_gap: None,
    }
}

#[test]
fn live_profile_v2_lean_and_miri_differential_canaries() {
    let root = workspace_anneal_root().expect("locate anneal root");
    let cache = resolve_default_cache_root(&root);
    let session = LeanTraceSession::prepare(&root, &cache).expect("prepare Lean");
    let fns = FNS.map(str::to_owned);
    let cap_res = session.capture_rust_source(&cache, "v2_canaries", PURE_V2_SRC, &fns);
    let CaptureAttempt::Captured(arts) = cap_res else { panic!("capture: {cap_res:?}") };
    let raw = fs::read_to_string(&arts.capture_json).unwrap();
    let v: serde_json::Value = serde_json::from_str(&raw).unwrap();
    assert_eq!(v["program"]["mir_profile_version"], 2);
    let b = |k| arts.body_ids_by_fn[k];
    let (bp, bs, bl, bw, bt) = (b(FNS[0]), b(FNS[1]), b(FNS[2]), b(FNS[3]), b(FNS[4]));
    let lean_src = format!(
        r#"import Trusted
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Captured
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
set_option warningAsError true
def cmS : CallerMemory := {{ allocations := [{{ allocId := 1, alignLog2 := 0, mutability := .shared, live := true, bytes := [.init 10 none, .init 42 none, .init 22 none] }}] }}
def cmM : CallerMemory := {{ allocations := [{{ allocId := 1, alignLog2 := 0, mutability := .mut, live := true, bytes := [.init 0 none] }}] }}
def u8v (n : Nat) : Val := .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩
def usz (n : Nat) : Val := .scalar ⟨.isize, false, BitVec.ofNat 128 n⟩
def u32v (n : Nat) : Val := .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩
noncomputable def stepN (p : Program) : Nat → StepResult State TerminalOut → StepResult State TerminalOut
  | 0, r => r
  | n + 1, .step st => stepN p n (evalStepV2 p st)
  | _, r => r
private theorem beh_split (p : Program) (q : Query) (k m : Nat) (sMid : State) (ret : TerminalOut)
    (h1 : stepN p k (match initStateV2 p q with | .ok s => .step s | .error f => .fault f) = .step sMid)
    (h2 : execOutcomeStateV2 p (fun o => o = ret) (fun _ => False) m sMid) : BehaviorV2 p q ret := by
  refine (spec_and_behaviorV2_of_exec_eq (p := p) (q := q) (fuel := m + k) ?_).2.1
  unfold execProgV2
  cases hI : initStateV2 p q with
  | error f => rw [hI] at h1; cases k <;> cases h1
  | ok s0 =>
    rw [hI] at h1; clear hI
    induction k generalizing s0 with
    | zero => cases h1; exact h2
    | succ k ih =>
      change (match evalStepV2 p s0 with | .step st => execOutcomeStateV2 p _ _ (m + k) st | .done o => _ | .fault f => _)
      dsimp only [stepN] at h1
      cases hE : evalStepV2 p s0 with
      | step st => rw [hE] at h1; exact ih st h1
      | done _ | fault _ => rw [hE] at h1; cases k <;> cases h1
private theorem ub_of (p : Program) (q : Query) (s0 : State) (hI : initStateV2 p q = .ok s0)
    (hF : execOutcomeStateV2 p (fun _ => False) (fun k => k = .undefined) 32 s0) : ¬ WellFormedV2 p q := by
  let ⟨sE, r, hR, hT, hK⟩ := exists_terminal_of_execOutcomeStateV2 hF
  cases r with
  | step _ | done _ => cases hK
  | fault k => cases hK; exact fun h => h.2 .undefined (by unfold ReachesResultV2; rw [hI]; exact ⟨sE, hR, hT⟩)
noncomputable def s6p : State := ⟨[⟨{bp}, 1, 0, [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩)), .immediate (some (usz 1)), .immediate (some (.ptr ⟨some 1, UInt64.ofNat 1, .isize⟩)), .immediate none, .immediate none], none, none, none⟩], cmS, {{ entryMemoryWithCaller cmS with nextAllocId := 2 }}⟩
noncomputable def s8t : State := ⟨[⟨{bt}, 0, 8, [.immediate none, .immediate (some (.tuple [u32v 0x12340055, u8v 0x7f])), .immediate (some (u32v 0x12340055)), .immediate none, .immediate (some (u32v 0x7f)), .dead], none, none, none⟩], queryEmpty.callerMem, entryMemoryWithCaller queryEmpty.callerMem⟩
theorem ok_ptr : BehaviorV2 (entryProgForBody Captured.program {bp}) {{ args := [.ptr ⟨some 1, 0, .isize⟩, usz 1], callerMem := cmS }} (.returned ⟨u8v 42, cmS⟩) := beh_split _ _ 6 6 s6p _ rfl (by rfl)
theorem ok_sl : BehaviorV2 (entryProgForBody Captured.program {bl}) {{ args := [.slicePtr ⟨some 1, 0, .isize⟩ 3], callerMem := cmS }} (.returned ⟨usz 3, cmS⟩) := (spec_and_behaviorV2_of_exec_eq (p := entryProgForBody Captured.program {bl}) (q := {{ args := [.slicePtr ⟨some 1, 0, .isize⟩ 3], callerMem := cmS }}) (fuel := 16) rfl).2.1
theorem ok_wr : BehaviorV2 (entryProgForBody Captured.program {bw}) {{ args := [.ptr ⟨some 1, 0, .isize⟩, u8v 99], callerMem := cmM }} (.returned ⟨u8v 99, {{ allocations := [{{ allocId := 1, alignLog2 := 0, mutability := .mut, live := true, bytes := [.init 99 none] }}] }}⟩) := (spec_and_behaviorV2_of_exec_eq (p := entryProgForBody Captured.program {bw}) (q := {{ args := [.ptr ⟨some 1, 0, .isize⟩, u8v 99], callerMem := cmM }}) (fuel := 16) rfl).2.1
theorem ok_pair : BehaviorV2 (entryProgForBody Captured.program {bt}) {{ args := [.tuple [u32v 0x12340055, u8v 0x7f]] }} (.returned ⟨u32v 0x12347f55, queryEmpty.callerMem⟩) := beh_split _ _ 8 7 s8t _ rfl (by rfl)
theorem ub_ptr : ¬ WellFormedV2 (entryProgForBody Captured.program {bp}) {{ args := [.ptr ⟨some 1, 0, .isize⟩, usz 4], callerMem := cmS }} := ub_of _ _ _ rfl (by rfl)
theorem ub_sl : ¬ WellFormedV2 (entryProgForBody Captured.program {bs}) {{ args := [.slicePtr ⟨some 1, 0, .isize⟩ 3, usz 0, usz 1], callerMem := cmS }} := ub_of _ _ _ rfl (by rfl)
theorem ub_wr : ¬ WellFormedV2 (entryProgForBody Captured.program {bw}) {{ args := [.ptr ⟨none, 0, .isize⟩, u8v 99] }} := ub_of _ _ _ rfl (by rfl)
theorem ub_ro : ¬ WellFormedV2 (entryProgForBody Captured.program {bw}) {{ args := [.ptr ⟨some 1, 0, .isize⟩, u8v 99], callerMem := cmS }} := ub_of _ _ _ rfl (by rfl)
"#
    );
    let tmp = tempfile::tempdir().unwrap();
    let lean_file = tmp.path().join("CanaryChecks.lean");
    fs::write(&lean_file, lean_src).unwrap();
    let lp = session.lean_path_with(Some(&arts.olean_dir)).unwrap();
    let inv = build_lean_invocation_with_env(
        &session.lean_bin,
        &lp,
        &[lean_file.into_os_string()],
        Some(tmp.path()),
        |k| env::var_os(k),
    );
    let out = run_supervised_with_prefix("anneal-v2-canary-", &inv, Some(tmp.path()), 180).unwrap();
    let ok = matches!(out.termination, anneal_testkit::Termination::Exited(s) if s.success());
    let (so, se) = (String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert!(ok, "Lean ({}): {so}{se}", out.termination.describe());

    let has = |k| env::var_os(k).is_some_and(|v| !v.is_empty());
    let dis = env::var("ANNEAL_ITREE_DISABLE_MIRI").ok().as_deref() == Some("1");
    let req = env::var("ANNEAL_ITREE_REQUIRE_MIRI").ok().as_deref() == Some("1")
        || (!dis && (has("ANNEAL_ITREE_MIRI_TOOLCHAIN") || has("ANNEAL_ITREE_MIRI_BIN")));
    if !req && dis {
        eprintln!("SKIP profile_v2_canaries Miri checks: disabled");
        return;
    }
    let miri = match MiriRunner::probe(&cache, Some(&session.rust_sysroot)) {
        MiriAvailability::Available(m) => m,
        MiriAvailability::InvalidConfig { reason } => panic!("invalid Miri: {reason}"),
        MiriAvailability::Unavailable { reason } => {
            assert!(!req, "Miri required: {reason}");
            eprintln!("SKIP profile_v2_canaries Miri checks: {reason}");
            return;
        }
    };
    type Check<'a> = (&'a str, &'a str, &'a [&'a str], IntKind, Result<TraceVal, &'a str>);
    let p32 = Ok(TraceVal::u32(0x1234_7f55));
    let checks: [Check<'_>; 8] = [
        ("ptr_ok", "miri_ptr_read", &["1usize"], IntKind::U8, Ok(TraceVal::u8(42))),
        ("slice_len", "miri_slice_len", &[], IntKind::Usize, Ok(TraceVal::usize_val(3))),
        ("write_ok", "miri_write_read", &["0u8", "99u8"], IntKind::U8, Ok(TraceVal::u8(99))),
        ("pair_ok", "miri_padded_mix", &["0x12340055u32", "0x7fu8"], IntKind::U32, p32),
        ("ptr_oob", "miri_ptr_read", &["4usize"], IntKind::U8, Err("in-bounds pointer arithmetic")),
        ("slice_ub", "miri_slice_sub", &["0usize", "1usize"], IntKind::Usize, Err("overflow")),
        ("write_null", "miri_write_read", &["1u8", "99u8"], IntKind::U8, Err("null")),
        ("write_ro", "miri_write_read", &["2u8", "99u8"], IntKind::U8, Err("read-only")),
    ];
    for (id, entry, args, kind, exp) in checks {
        let r = miri.run_case(&v2_case(id, entry, args, kind, exp.is_err()));
        match (r.tool_error.as_ref(), &r.outcome, exp) {
            (None, TerminalOutcome::Returned { ret, .. }, Ok(e)) if ret.semantically_eq(&e) => {}
            (None, TerminalOutcome::FaultUb { detail }, Err(m))
                if detail.to_ascii_lowercase().contains(m) => {}
            _ => panic!("{id}: {r:?}"),
        }
    }
}
