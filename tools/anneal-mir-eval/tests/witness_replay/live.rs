// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Live Miri replays for
//! `miri_witness_replay_confirms_probe_ub_and_contrasts_model_only`: each
//! replays one witness (or a ground-truth contrast) with its positive
//! control.

use std::{collections::BTreeSet, path::Path};

use anneal_mir_eval::{
    AllocByte, Allocation, Block, Body, CallerMemory, Counterexample, EvalConfig, FaultKind,
    IntWidth, Mutability, Operand, Outcome, PanicStrategy, Program, PtrVal, Rvalue, Scope,
    Statement, Terminator, Ty, UbClass, Val, WitnessClass, eval_body_with_caller_mem,
};

use super::support::{
    ReplayVerdict, TempDir, U32_TY, gate_witness_replay, render_raw_u32_deref_harness,
    run_miri_snippet,
};

pub(super) fn replay_zc08(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    zc08_ce: &Counterexample,
    zc08_bytes: &[u8],
    zc08_mid: u64,
) {
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "zc08_ub", &zc08_ub_src)
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "zc08_ok", &zc08_ok_src).unwrap();
    assert_eq!(ok_code, Some(0), "positive control zc08_ok failed under Miri:\n{ok_err}");
}

pub(super) fn replay_unchecked_add(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    uadd_ce: &Counterexample,
    uadd_a: u8,
    uadd_b: u8,
) {
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "uadd_ub", &uadd_ub_src)
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
        toolchain,
        work_dir.path(),
        target_dir,
        "uadd_ok",
        "fn main() { assert_eq!(unsafe { 1u8.unchecked_add(2) }, 3); }\n",
    )
    .unwrap();
    assert_eq!(uadd_ok_code, Some(0), "uadd_ok failed under Miri:\n{uadd_ok_err}");
}

pub(super) fn replay_ptr_add(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    ptr_add_ce: &Counterexample,
    ptr_add_count: u64,
) {
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "ptr_add_ub", &ptr_add_ub_src)
    });
    match &v3 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] ptr.add({ptr_add_count}) -> {diagnostic}");
        }
        other => panic!("ptr_add OOB witness failed Miri replay: {other:?}"),
    }
    let (pa_ok_code, pa_ok_err) = run_miri_snippet(
        toolchain,
        work_dir.path(),
        target_dir,
        "ptr_add_ok",
        "fn main() { let x: u32 = 7; let p = &raw const x; let _ = unsafe { p.add(1) }; }\n",
    )
    .unwrap();
    assert_eq!(pa_ok_code, Some(0), "ptr_add_ok failed under Miri:\n{pa_ok_err}");
}

pub(super) fn replay_raw_deref(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    deref_ce: &Counterexample,
    deref_rust_src: &str,
) {
    // 4. Live replay of Profile v2 raw pointer dereference UB witness plus
    //    positive control.
    let v4 = gate_witness_replay(deref_ce, || {
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "deref_ub", deref_rust_src)
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
        toolchain,
        work_dir.path(),
        target_dir,
        "deref_ok",
        "fn main() { let x: u32 = 42; let p = &raw const x; assert_eq!(unsafe { *p }, 42); }\n",
    )
    .unwrap();
    assert_eq!(dr_ok_code, Some(0), "deref_ok failed under Miri:\n{dr_ok_err}");
}

pub(super) fn replay_dead_zero_contrast(toolchain: &str, work_dir: &TempDir, target_dir: &Path) {
    // 5. Empirical contrast under live Miri: zero-byte `p.add(0)` on a dead
    //    stack pointer exits 0 under Miri (NOT UB), confirming why
    //    `ZeroOffsetDeadOrOobPtr` is classified `ModelOnlyUnreplayed`.
    let (dead_zero_code, dead_zero_err) = run_miri_snippet(
        toolchain,
        work_dir.path(),
        target_dir,
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
}

pub(super) fn replay_misaligned_deref(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    deref_prog: &Program,
    v2_cfg: &EvalConfig,
) {
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
        deref_prog,
        0,
        std::slice::from_ref(&misalign_ptr),
        misalign_cm.clone(),
        32,
        v2_cfg,
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "misalign_ub", &misalign_src)
    });
    match &v6 {
        ReplayVerdict::ConfirmedMiriUb { diagnostic } => {
            eprintln!("[witness_replay:{toolchain}] misaligned_u32_deref -> {diagnostic}");
        }
        other => panic!("misaligned raw u32 deref failed Miri replay: {other:?}"),
    }
}

pub(super) fn replay_overlapping_assign(
    toolchain: &str,
    work_dir: &TempDir,
    target_dir: &Path,
    v2_cfg: &EvalConfig,
) {
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
        eval_body_with_caller_mem(&overlap_prog, 0, &overlap_args, overlap_cm.clone(), 16, v2_cfg);
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
        run_miri_snippet(toolchain, work_dir.path(), target_dir, "overlap_ub", overlap_ub_src)
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
        toolchain,
        work_dir.path(),
        target_dir,
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
        toolchain,
        work_dir.path(),
        target_dir,
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
        toolchain,
        work_dir.path(),
        target_dir,
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
        toolchain,
        work_dir.path(),
        target_dir,
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
