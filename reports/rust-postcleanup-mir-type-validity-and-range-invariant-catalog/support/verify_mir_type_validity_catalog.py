#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Generate mir_type_validity_rules.json and run the 24-case Rust 1.99.1 validity verification suite."""

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

VALIDITY_RULES = [
    {
        "rule_id": "VAL-01",
        "ty_kind": "TyKind::Bool",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Int(I8, false), valid_range: 0..=1 })",
        "gamma_valid_predicate": "0 <= v && v <= 1",
        "side_conditions": ["none"],
        "authority_kind": "Normative (Rust Reference behavior-considered-undefined.md) + Miri ValidityVisitor + layout.rs:414-420",
        "llvm_lowering_in_rustc_1_99_1": "i1 noundef (or i8 noundef range(i8 0, 2) in memory loads)",
    },
    {
        "rule_id": "VAL-02",
        "ty_kind": "TyKind::Char",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Int(I32, false), valid_range: 0..=0x10FFFF })",
        "gamma_valid_predicate": "(0 <= v && v <= 0xD7FF) || (0xE000 <= v && v <= 0x10FFFF)",
        "side_conditions": ["surrogate half range 0xD800..=0xDFFF is also excluded by Rust validity even though WrappingRange only stores single contiguous hull 0..=0x10FFFF"],
        "authority_kind": "Normative (Rust Reference) + Miri ValidityVisitor (checks surrogate gap) + layout.rs:421-427",
        "llvm_lowering_in_rustc_1_99_1": "i32 noundef range(i32 0, 1114112)",
    },
    {
        "rule_id": "VAL-03",
        "ty_kind": "TyKind::Int(iN) / TyKind::Uint(uN)",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Int(iN/uN, signed), valid_range: 0..=2^N-1 })",
        "gamma_valid_predicate": "is_initialized(v) && 0 <= v_unsigned && v_unsigned <= 2^N - 1",
        "side_conditions": ["every byte must be initialized (reading uninitialized bytes as integer is immediate UB)"],
        "authority_kind": "Normative (Rust Reference) + Miri ValidityVisitor + layout.rs:428-429",
        "llvm_lowering_in_rustc_1_99_1": "iN noundef",
    },
    {
        "rule_id": "VAL-04",
        "ty_kind": "TyKind::Adt(core::num::NonZero<uN>) / TyKind::Pat(uN, PatternKind::Range { start: 1, end: 2^N-1 })",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Int(N, false), valid_range: 1..=2^N-1 })",
        "gamma_valid_predicate": "1 <= v_unsigned && v_unsigned <= 2^N - 1",
        "side_conditions": ["In rustc 1.99.1, NonZero<T> is backed by ty::Pat(T, PatternKind::Range / Or) in layout.rs:244-411"],
        "authority_kind": "Normative (core::num::NonZero layout contract) + Miri + layout.rs:248-295",
        "llvm_lowering_in_rustc_1_99_1": "iN noundef range(iN 1, 0)",
    },
    {
        "rule_id": "VAL-05",
        "ty_kind": "TyKind::Pat(iN, PatternKind::Or([iN::MIN..=E, S..=iN::MAX])) & WrappingRange (S_unsigned > E_unsigned)",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Int(N, true), valid_range: WrappingRange { start: S_unsigned, end: E_unsigned } })",
        "gamma_valid_predicate": "if S_u <= E_u then (S_u <= v_u && v_u <= E_u) else (v_u >= S_u || v_u <= E_u)",
        "side_conditions": ["layout.rs:355-391 constructs wrapping unsigned WrappingRange (start > end) from signed or-patterns crossing 0 (such as NonZero<iN> or bounded signed niches)"],
        "authority_kind": "Implementation contract (layout.rs:312-401) + Miri ValidityVisitor (validity.rs:1007-1055)",
        "llvm_lowering_in_rustc_1_99_1": "iN noundef range(iN S_u, (E_u + 1) mod 2^N)",
    },
    {
        "rule_id": "VAL-06",
        "ty_kind": "TyKind::Never (!) and Uninhabited Enums (abi.is_uninhabited())",
        "backend_repr": "BackendRepr::Memory (size 0, abi.is_uninhabited() == true)",
        "gamma_valid_predicate": "False (reaching any program point with a live value of uninhabited type is immediate UB)",
        "side_conditions": ["abi.is_uninhabited() == true"],
        "authority_kind": "Normative (Rust Reference) + Miri + lint_and_remove_uninhabited.rs",
        "llvm_lowering_in_rustc_1_99_1": "unreachable terminator",
    },
    {
        "rule_id": "VAL-07",
        "ty_kind": "TyKind::Ref(_, T, Mutability) and Box<T> where T: Sized",
        "backend_repr": "BackendRepr::Scalar(Initialized { value: Pointer(AddrSpace(0)), valid_range: 1..=2^W-1 })",
        "gamma_valid_predicate": "addr(p) >= align(T) && addr(p) % align(T) == 0 && addr(p) + size(T) <= 2^W - 1 && size(T) <= isize::MAX && dereferenceable(p, size(T))",
        "side_conditions": ["align(T) = 2^k >= 1; for ZST (size(T) == 0), p must still be non-null and aligned to align(T) (e.g. align(u32) == 4 => addr(p) >= 4)"],
        "authority_kind": "Normative (Rust Reference) + Miri + rustc_ty_utils/src/abi.rs:512-555",
        "llvm_lowering_in_rustc_1_99_1": "ptr noundef nonnull align A dereferenceable(S) (plus noalias readonly/writable)",
    },
    {
        "rule_id": "VAL-08",
        "ty_kind": "TyKind::Ref(_, TyKind::Slice(T), _) and Box<[T]> where sizeof(T) >= 1",
        "backend_repr": "BackendRepr::ScalarPair { a: Pointer (1..=2^W-1), b: Int(usize, 0..=isize::MAX/sizeof(T)) }",
        "gamma_valid_predicate": "addr(ptr) >= align(T) && addr(ptr) % align(T) == 0 && len * sizeof(T) <= isize::MAX && addr(ptr) + len * sizeof(T) <= 2^W - 1",
        "side_conditions": [
            "CRITICAL ZST GUARD: sizeof(T) >= 1 is strictly required to deduce len <= isize::MAX! When sizeof(T) == 0 (&[()]), len * 0 == 0 <= isize::MAX holds for all len <= usize::MAX"
        ],
        "authority_kind": "Normative (Rust Reference + core::slice::from_raw_parts precondition) + Miri + rustc_codegen_llvm/src/abi.rs:559-580",
        "llvm_lowering_in_rustc_1_99_1": "range(i64 0, isize::MAX/sizeof(T) + 1) emitted ONLY on Direct ScalarPair parameters of &[T] (missed on &str, Box<[T]>, and memory loads of &[T] because layout.rs:504 leaves valid_range full)",
    },
    {
        "rule_id": "VAL-09",
        "ty_kind": "TyKind::Ref(_, TyKind::Slice(ZST), _) where sizeof(ZST) == 0",
        "backend_repr": "BackendRepr::ScalarPair { a: Pointer (1..=2^W-1), b: Int(usize, 0..=2^W-1) }",
        "gamma_valid_predicate": "addr(ptr) >= align(ZST) && addr(ptr) % align(ZST) == 0 && 0 <= len && len <= usize::MAX",
        "side_conditions": ["sizeof(ZST) == 0: len can legally equal usize::MAX (e.g. slice::from_raw_parts(NonNull::dangling().as_ptr(), usize::MAX))"],
        "authority_kind": "Normative + Miri + rustc_codegen_llvm/src/abi.rs:563 (elem_size != Size::ZERO guard)",
        "llvm_lowering_in_rustc_1_99_1": "ptr noundef nonnull align A, i64 noundef (no range attribute on len)",
    },
    {
        "rule_id": "VAL-10",
        "ty_kind": "TyKind::Ref(_, TyKind::Str, _) and Box<str>",
        "backend_repr": "BackendRepr::ScalarPair { a: Pointer (1..=2^W-1), b: Int(usize) }",
        "gamma_valid_predicate": "addr(ptr) >= 1 && len <= isize::MAX && addr(ptr) + len <= 2^W - 1 && valid_utf8(mem[ptr..ptr+len])",
        "side_conditions": ["sizeof(u8) == 1 >= 1, so &str always satisfies len <= isize::MAX"],
        "authority_kind": "Normative (Rust Reference) + Miri",
        "llvm_lowering_in_rustc_1_99_1": "MISSED IN RUSTC 1.99.1: abi.rs:561 checks `let ty::Slice(element_ty) = *pointee_ty.kind()`, which fails to match `ty::Str`, omitting `range(i64 0, -9223372036854775808)` on `&str` parameters!",
    },
    {
        "rule_id": "VAL-11",
        "ty_kind": "TyKind::RawPtr(TyKind::Slice(T), _) (*const [T] / *mut [T])",
        "backend_repr": "BackendRepr::ScalarPair { a: Pointer (0..=2^W-1), b: Int(usize, 0..=2^W-1) }",
        "gamma_valid_predicate": "is_initialized(ptr) && is_initialized(len) && 0 <= len && len <= usize::MAX",
        "side_conditions": [
            "Raw slice pointers created via ptr::slice_from_raw_parts(p, usize::MAX) are VALID values even when sizeof(T) >= 1 and p is null! Do NOT deduce len <= isize::MAX or ptr != 0 on *const [T] / *mut [T] unless dereferenced or reborrowed as &[T]"
        ],
        "authority_kind": "Normative (Rust Reference) + Miri",
        "llvm_lowering_in_rustc_1_99_1": "ptr noundef, i64 noundef",
    },
    {
        "rule_id": "VAL-12",
        "ty_kind": "TyKind::Ref(_, TyKind::Dynamic(..), _) (&dyn Trait / &mut dyn Trait)",
        "backend_repr": "BackendRepr::ScalarPair { a: Pointer (1..=2^W-1), b: Pointer (vtable, 1..=2^W-1) }",
        "gamma_valid_predicate": "addr(data_ptr) >= align(vtable) && addr(vtable_ptr) >= align(usize) && size(vtable) <= isize::MAX",
        "side_conditions": ["vtable entry 1 holds size_of_val <= isize::MAX; entry 2 holds align_of_val (power of two)"],
        "authority_kind": "Normative + Miri + layout.rs:507",
        "llvm_lowering_in_rustc_1_99_1": "ptr noundef nonnull, ptr noundef nonnull readonly align 8 dereferenceable(24)",
    },
    {
        "rule_id": "VAL-13",
        "ty_kind": "Enum with TagEncoding::Direct (Variants::Multiple)",
        "backend_repr": "BackendRepr::Scalar or ScalarPair or Memory with tag field at offset 0",
        "gamma_valid_predicate": "tag_val in valid_range(tag_scalar) && active_variant_fields_valid",
        "side_conditions": ["tag_scalar.valid_range bounds the min..=max discriminant bit-pattern"],
        "authority_kind": "Normative + Miri + layout.rs:340-405",
        "llvm_lowering_in_rustc_1_99_1": "range attribute on direct scalar tag; !range on Rvalue::Discriminant load",
    },
    {
        "rule_id": "VAL-14",
        "ty_kind": "Enum with TagEncoding::Niche (e.g. Option<&T>, Option<NonZeroU32>, Option<Result<NonZeroU32, bool>>)",
        "backend_repr": "BackendRepr::Scalar or ScalarPair sharing payload storage",
        "gamma_valid_predicate": "tag_or_niche_val in hull(valid_range(dataful_variant) U niche_values)",
        "side_conditions": ["When niche encoding fills all remaining values of a WrappingRange, scalar.is_always_valid(cx) becomes true; otherwise valid_range is the tight WrappingRange"],
        "authority_kind": "Normative + Miri + layout.rs:310-395",
        "llvm_lowering_in_rustc_1_99_1": "range attribute when !scalar.is_always_valid(cx)",
    },
    {
        "rule_id": "VAL-15",
        "ty_kind": "TyKind::Adt(MaybeUninit<T>) and Union types",
        "backend_repr": "Same BackendRepr size/align as T, but Scalar::Union (uninitialized bytes permitted)",
        "gamma_valid_predicate": "True (all initialized/uninitialized byte sequences of size_of::<T>() are valid; zero range/noundef assumptions)",
        "side_conditions": ["Never emit noundef, nonnull, or valid_range on MaybeUninit<T> or union fields"],
        "authority_kind": "Normative (Rust Reference) + Miri + layout.rs:295-308",
        "llvm_lowering_in_rustc_1_99_1": "no noundef, no range, no nonnull",
    },
    {
        "rule_id": "VAL-16",
        "ty_kind": "StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) & Unchecked BinOps",
        "backend_repr": "N/A (statement/rvalue operational obligation)",
        "gamma_valid_predicate": "eval_bool(op) == true; for AddUnchecked/SubUnchecked/MulUnchecked: no wrapping overflow; for ShlUnchecked/ShrUnchecked: shift < bit_width",
        "side_conditions": ["Immediate UB if violated on reachable execution path"],
        "authority_kind": "Normative (core::intrinsics::assume / unchecked_*) + Miri",
        "llvm_lowering_in_rustc_1_99_1": "@llvm.assume(i1 %op) and add/sub/mul nuw/nsw, shl/lshr/ashr",
    },
]

RUST_24_CASES_PROBE = r'''
#![allow(internal_features)]
#![feature(core_intrinsics, pattern_types, pattern_type_macro)]

use std::pat::pattern_type;
use std::mem::{MaybeUninit, size_of};
use std::num::{NonZeroI8, NonZeroU8, NonZeroU32, NonZeroUsize};
use std::ptr::{self, NonNull};

pub type BoundedPatU8 = pattern_type!(u8 is 10..=250);
pub type WrappingSignedPatI8 = pattern_type!(i8 is -128..=-10 | 10..=127);

#[derive(Copy, Clone)]
pub enum EmptyEnum {}

fn main() {
    let mut results = Vec::new();

    // Case 01: bool in 0..=1
    let b: bool = true;
    results.push(("case01_bool_range", (b as u8) <= 1));

    // Case 02: char valid Unicode scalar (0..=0xD7FF or 0xE000..=0x10FFFF)
    let c: char = '\u{10FFFF}';
    let cu = c as u32;
    results.push(("case02_char_range", cu <= 0x10FFFF && !(0xD800..=0xDFFF).contains(&cu)));

    // Case 03: NonZeroU32 in 1..=u32::MAX
    let nz = NonZeroU32::new(1).unwrap();
    results.push(("case03_nonzero_u32", nz.get() >= 1));

    // Case 04: Option<NonZeroU32> niche at 0 (size == 4)
    let opt_nz: Option<NonZeroU32> = None;
    results.push(("case04_option_nonzero_niche", size_of::<Option<NonZeroU32>>() == 4 && opt_nz.is_none()));

    // Case 05: TagEncoding::Niche requires at most ONE non-ZST dataful variant:
    // Option<Result<BoundedPatU8, ()>> has 1 dataful variant and 15 niches (size == 1),
    // whereas Result<BoundedPatU8, bool> has 2 non-ZST variants (1B each) so TagEncoding::Direct is used (size == 2)!
    results.push((
        "case05_nested_option_result_niche",
        size_of::<Option<Result<BoundedPatU8, ()>>>() == 1
            && size_of::<Result<BoundedPatU8, bool>>() == 2
            && size_of::<Result<NonZeroU32, bool>>() == 8,
    ));

    // Case 06: Wrapping valid_range via NonZeroI8 and pattern_type! Or-pattern (-128..=-10 | 10..=127)
    let nzi8 = NonZeroI8::new(-5).unwrap();
    results.push((
        "case06_wrapping_valid_range_or_pattern",
        nzi8.get() == -5
            && size_of::<Option<NonZeroI8>>() == 1
            && size_of::<Option<BoundedPatU8>>() == 1
            && size_of::<Option<WrappingSignedPatI8>>() == 1,
    ));

    // Case 07: &[u8] non-ZST slice length <= isize::MAX
    let s_u8: &[u8] = &[1, 2, 3, 4];
    results.push(("case07_slice_u8_len_le_isize_max", s_u8.len() <= (isize::MAX as usize)));

    // Case 08: &[u64] non-ZST slice length <= isize::MAX / 8
    let s_u64: &[u64] = &[10, 20];
    results.push(("case08_slice_u64_len_scaled_bound", s_u64.len() <= (isize::MAX as usize) / size_of::<u64>()));

    // Case 09: &[()] ZST slice with len == usize::MAX (> isize::MAX) is 100% SOUND!
    let zst_slice: &[()] = unsafe {
        std::slice::from_raw_parts(NonNull::<()>::dangling().as_ptr(), usize::MAX)
    };
    results.push(("case09_zst_slice_len_usize_max_sound", zst_slice.len() == usize::MAX));

    // Case 10: *const [u8] raw slice pointer with len == usize::MAX and null ptr is 100% SOUND until dereferenced!
    let raw_slice: *const [u8] = ptr::slice_from_raw_parts(ptr::null::<u8>(), usize::MAX);
    results.push(("case10_raw_slice_ptr_usize_max_sound", raw_slice.len() == usize::MAX));

    // Case 11: &str length <= isize::MAX
    let st: &str = "hello";
    results.push(("case11_str_len_le_isize_max", st.len() <= (isize::MAX as usize)));

    // Case 12: &u64 alignment >= 8 and non-null
    let val64: u64 = 42;
    let r64: &u64 = &val64;
    let addr = (r64 as *const u64).addr();
    results.push(("case12_ref_u64_aligned_nonnull", addr >= 8 && addr % 8 == 0));

    // Case 13: &[u32; 0] ZST array reference must still be aligned to align_of::<u32>() == 4
    let empty_arr: &[u32; 0] = &[];
    let addr_arr = (empty_arr as *const [u32; 0]).addr();
    results.push(("case13_zst_u32_array_ref_aligned_4", addr_arr >= 4 && addr_arr % 4 == 0));

    // Case 14: MaybeUninit<bool> suppresses niche (size_of::<Option<MaybeUninit<bool>>>() == 2)
    let mu: MaybeUninit<bool> = MaybeUninit::uninit();
    let _ = mu;
    results.push(("case14_maybe_uninit_bool_niche_suppressed", size_of::<Option<MaybeUninit<bool>>>() == 2));

    // Case 15: Box<[u16]> non-null, aligned 2, len <= isize::MAX / 2
    let bx: Box<[u16]> = Box::new([1, 2, 3]);
    results.push(("case15_box_slice_u16", bx.len() <= (isize::MAX as usize) / 2 && (bx.as_ptr().addr() % 2 == 0)));

    // Case 16: Option<&[u8]> niche in data pointer only (size == 16)
    results.push(("case16_option_slice_ref_size_16", size_of::<Option<&[u8]>>() == 16));

    // Case 17: core::intrinsics::assume(x < 100)
    let x = 42usize;
    unsafe { core::intrinsics::assume(x < 100); }
    results.push(("case17_intrinsic_assume", x < 100));

    // Case 18: unchecked_add / unchecked_sub / unchecked_shl
    let ua = unsafe { core::intrinsics::unchecked_add(10u32, 20u32) };
    let us = unsafe { core::intrinsics::unchecked_shl(1u32, 4u32) };
    results.push(("case18_unchecked_arith_and_shift", ua == 30 && us == 16));

    // Case 19: NonZeroU8 in Option<Result<NonZeroU8, ()>>
    results.push(("case19_option_result_nonzero_u8", size_of::<Option<Result<NonZeroU8, ()>>>() == 2));

    // Case 20: Enum direct discriminant tag range
    #[repr(u8)]
    enum DirTag { A = 10, B = 20, C = 30 }
    let dt = DirTag::B;
    let discr = dt as u8;
    results.push(("case20_enum_direct_tag_hull", (10..=30).contains(&discr)));

    // Case 21: Reference no-wrap address space: addr(ptr) + len * sizeof(T) <= usize::MAX
    let s_nowrap: &[u32] = &[1, 2, 3, 4];
    let p_addr = s_nowrap.as_ptr().addr();
    results.push(("case21_slice_addr_no_wrap", p_addr.checked_add(s_nowrap.len() * 4).is_some()));

    // Case 22: &dyn Trait vtable size/align validity
    trait Dummy { fn f(&self) -> u32; }
    impl Dummy for u32 { fn f(&self) -> u32 { *self } }
    let d: &dyn Dummy = &99u32;
    results.push(("case22_dyn_trait_valid", d.f() == 99 && size_of::<Option<&dyn Dummy>>() == 16));

    // Case 23: NonZeroUsize pointer-sized niche
    let nzu = NonZeroUsize::new(usize::MAX).unwrap();
    results.push(("case23_nonzero_usize_max", nzu.get() == usize::MAX && size_of::<Option<NonZeroUsize>>() == 8));

    // Case 24: Uninhabited EmptyEnum in Result<u64, EmptyEnum> collapses tag (size == 8)
    results.push(("case24_result_uninhabited_err_collapses_tag", size_of::<Result<u64, EmptyEnum>>() == 8));

    for (name, ok) in &results {
        assert!(*ok, "Failed validity case: {}", name);
    }
    println!("ALL_24_VALIDITY_CASES_PASSED ({})", results.len());
}
'''

LLVM_IR_GAP_PROBE = r'''
#![crate_type = "lib"]

#[no_mangle]
pub fn take_u8_slice(s: &[u8]) -> usize {
    s.len()
}

#[no_mangle]
pub fn take_u64_slice(s: &[u64]) -> usize {
    s.len()
}

#[no_mangle]
pub fn take_zst_slice(s: &[()]) -> usize {
    s.len()
}

#[no_mangle]
pub fn take_str(s: &str) -> usize {
    s.len()
}

#[no_mangle]
pub fn take_box_slice(s: Box<[u8]>) -> usize {
    s.len()
}

#[no_mangle]
pub fn take_raw_slice(s: *const [u8]) -> usize {
    s.len()
}

pub struct SliceHolder<'a> {
    pub inner: &'a [u8],
}

#[no_mangle]
pub fn load_slice_from_memory(h: &SliceHolder<'_>) -> usize {
    h.inner.len()
}
'''


def main() -> None:
    out_dir = Path(__file__).resolve().parent
    env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="n4_probe_", dir=str(tmp_base)))
    try:
        probe_rs = work / "probe24.rs"
        probe_rs.write_text(RUST_24_CASES_PROBE, encoding="utf-8")
        bin_path = work / "probe24"
        subprocess.run(
            ["rustc", "+1.99.1-x86_64-unknown-linux-gnu", "-Copt-level=3", str(probe_rs), "-o", str(bin_path)],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        run_out = subprocess.run([str(bin_path)], check=True, capture_output=True, text=True).stdout.strip()

        ir_rs = work / "ir_gap.rs"
        ir_rs.write_text(LLVM_IR_GAP_PROBE, encoding="utf-8")
        ll_path = work / "ir_gap.ll"
        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "-Copt-level=3",
                "--emit=llvm-ir",
                str(ir_rs),
                "-o",
                str(ll_path),
            ],
            env=env,
            check=True,
            capture_output=True,
            text=True,
        )
        ll_text = ll_path.read_text(encoding="utf-8")
        ll_lines = [line for line in ll_text.splitlines() if line.startswith("define ")]

        catalog = {
            "schema_version": "1.0",
            "rustc_version": "1.99.1",
            "rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
            "observed_at": "2026-11-14",
            "rules_count": len(VALIDITY_RULES),
            "validation_24_cases_output": run_out,
            "emitted_llvm_ir_signatures_rustc_1_99_1": ll_lines,
            "emitted_llvm_ir_full": ll_text,
            "rules": VALIDITY_RULES,
        }
        (out_dir / "mir_type_validity_rules.json").write_text(
            json.dumps(catalog, indent=2) + "\n", encoding="utf-8"
        )
        print(run_out)
        for sig in ll_lines:
            print(" ", sig)
        print("--- load_slice_from_memory body ---")
        in_load = False
        for line in ll_text.splitlines():
            if "define " in line and "@load_slice_from_memory" in line:
                in_load = True
            if in_load:
                print(" ", line)
                if line.strip() == "}":
                    break
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
