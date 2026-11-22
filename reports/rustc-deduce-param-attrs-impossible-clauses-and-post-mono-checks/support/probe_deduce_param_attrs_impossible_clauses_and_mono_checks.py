#!/usr/bin/env python3
"""Differential probe for three rustc mechanisms, run against a real `rustc`.

  A. `deduce_param_attrs`: which LLVM parameter attributes (`readonly`,
     `captures(none)`) rustc attaches to indirectly passed by-value parameters
     and to the indirect return place, both on local definitions and on
     cross-crate declarations whose facts travel through crate metadata.
  B. The MIR pass that replaces a body with a lone `unreachable` when the item
     has unsatisfiable `where` clauses (`ImpossibleClauses`; named
     `ImpossiblePredicates` in older toolchains).
  C. The post-monomorphization checks (`abi_check`, `move_check`).

Nothing in this file is a recorded result.  Every observation is produced by
invoking the compiler given by `--rustc` (or `$RUSTC`, or `rustc` on `PATH`) on
the Rust sources embedded below, inside a temporary directory that is removed
on exit.  The `PREDICTED_*` tables are *predictions* derived by reading the
rustc source at commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1; the probe
reports agreement or disagreement with them and never substitutes a prediction
for an observation.

Usage:
    python3 probe_deduce_param_attrs_impossible_clauses_and_mono_checks.py \
        --rustc /path/to/nightly/bin/rustc --out results.json \
        [--baseline recorded_baseline.json] [--dump-sources DIR] [--strict]

A nightly toolchain is required (unstable `-Z` flags and feature gates).
Only the Python standard library is used.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

SCHEMA = "deduce-param-attrs-probe/2"

# ---------------------------------------------------------------------------
# Embedded Rust sources
# ---------------------------------------------------------------------------

UP_SRC = r"""
//! Upstream crate: by-value parameters large enough to be passed by hidden
//! pointer (`PassMode::Indirect`) under the Rust ABI on x86-64.
#![allow(unused)]
use std::cell::Cell;
use std::hint::black_box;

/// 64 bytes, align 8, `Freeze`, no drop glue.
pub struct BigFreeze(pub [u64; 8]);
/// 64 bytes, align 8, NOT `Freeze` (`Cell` wraps `UnsafeCell`), no drop glue.
pub struct BigCell(pub [Cell<u64>; 8]);

/// 64 bytes, align 8, `Freeze`, `Copy`: used only by the forwarding witness.
#[derive(Clone, Copy)]
pub struct BigCopy(pub [u64; 8]);

// Only reads of the parameter.
#[inline(never)]
pub fn read_big_freeze(x: BigFreeze) -> u64 {
    x.0[0].wrapping_add(x.0[7])
}

// Only reads of a `Copy` parameter (callee of the forwarding witness).
#[inline(never)]
pub fn read_big_copy(x: BigCopy) -> u64 {
    x.0[0].wrapping_add(x.0[7])
}

// `&x` where the parameter type is `Freeze`.
#[inline(never)]
pub fn shared_borrow_big_freeze(x: BigFreeze) -> u64 {
    black_box(&x);
    x.0[0]
}

// `&x` where the parameter type is not `Freeze`.
#[inline(never)]
pub fn shared_borrow_big_cell(x: BigCell) -> u64 {
    black_box(&x);
    x.0[0].get()
}

// `&raw const x`.
#[inline(never)]
pub fn raw_const_borrow_big_freeze(x: BigFreeze) -> u64 {
    black_box(&raw const x);
    x.0[0]
}

// In-place store into the parameter at a data-dependent index (so no MIR pass
// can prove the store dead), with no borrow of the parameter.
#[inline(never)]
pub fn mutate_local_copy_big_freeze(mut x: BigFreeze) -> u64 {
    let i = (x.0[0] & 7) as usize;
    x.0[i] = 0xdead;
    x.0[0] ^ x.0[7]
}

// The parameter is only dropped, as a whole local.
#[inline(never)]
pub fn generic_drop_only<T>(_x: [T; 8], flag: u64) -> u64 {
    flag.wrapping_mul(3)
}

#[inline(never)]
pub fn sink_big_freeze(x: BigFreeze) -> u64 {
    x.0[1]
}

// The parameter is forwarded as a by-move call argument.
#[inline(never)]
pub fn forward_by_move_indirect(x: BigFreeze) -> u64 {
    sink_big_freeze(x)
}

// Two indirect parameters: the first is only read, the second is forwarded.
#[inline(never)]
pub fn mixed_read_then_forward(a: BigFreeze, b: BigFreeze) -> u64 {
    a.0[0].wrapping_add(sink_big_freeze(b))
}

// Two indirect parameters: the first is forwarded, the second is only read.
#[inline(never)]
pub fn mixed_forward_then_read(a: BigFreeze, b: BigFreeze) -> u64 {
    sink_big_freeze(a).wrapping_add(b.0[0])
}

// Indirect return place that is never written in MIR.
#[inline(never)]
pub fn ret_never_returns() -> [u8; 80] {
    loop {}
}

// Indirect return place written by a plain assignment.
#[inline(never)]
pub fn ret_not_captured(v: u8) -> [u8; 80] {
    [v; 80]
}

// Indirect return place used as the destination of a call.
#[inline(never)]
pub fn ret_captured(v: u8) -> [u8; 80] {
    black_box([v; 80])
}
"""

DOWN_SRC = r"""
//! Downstream crate: calls every upstream function so that the upstream
//! symbols appear as `declare` lines, and instantiates the generic one.
extern crate deduce_up;
use deduce_up::*;
use std::cell::Cell;

#[inline(never)]
pub fn call_read_big_freeze(v: u64) -> u64 {
    read_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_shared_borrow_big_freeze(v: u64) -> u64 {
    shared_borrow_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_shared_borrow_big_cell(v: u64) -> u64 {
    shared_borrow_big_cell(BigCell(std::array::from_fn(|_| Cell::new(v))))
}
#[inline(never)]
pub fn call_raw_const_borrow_big_freeze(v: u64) -> u64 {
    raw_const_borrow_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mutate_local_copy_big_freeze(v: u64) -> u64 {
    mutate_local_copy_big_freeze(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_forward_by_move_indirect(v: u64) -> u64 {
    forward_by_move_indirect(BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mixed_read_then_forward(v: u64) -> u64 {
    mixed_read_then_forward(BigFreeze([v; 8]), BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_mixed_forward_then_read(v: u64) -> u64 {
    mixed_forward_then_read(BigFreeze([v; 8]), BigFreeze([v; 8]))
}
#[inline(never)]
pub fn call_generic_drop_only_string(s: &str) -> u64 {
    generic_drop_only::<String>(std::array::from_fn(|_| String::from(s)), 5)
}
#[inline(never)]
pub fn call_generic_drop_only_u64(v: u64) -> u64 {
    generic_drop_only::<u64>([v; 8], 7)
}
// Forwarding witness: the argument is a by-value copy of `*src`.  rustc lowers
// it as `memcpy(tmp, src); call read_big_copy(tmp)`.  Whether LLVM may pass
// `src` itself depends on the attributes of `read_big_copy`'s declaration,
// which is all the downstream crate knows about that function.
#[inline(never)]
pub fn forwarding_witness(src: &BigCopy) -> u64 {
    read_big_copy(*src)
}
// Variant that also reads `*src` after the call.  Recorded without a
// prediction: the extra read lets an earlier LLVM pass split the copy.
#[inline(never)]
pub fn forwarding_witness_split(src: &BigCopy) -> u64 {
    read_big_copy(*src).wrapping_add(src.0[3])
}
#[inline(never)]
pub fn call_ret_never_returns() -> u8 {
    ret_never_returns()[0]
}
#[inline(never)]
pub fn call_ret_not_captured(v: u8) -> u8 {
    ret_not_captured(v)[3]
}
#[inline(never)]
pub fn call_ret_captured(v: u8) -> u8 {
    ret_captured(v)[3]
}
"""

# Hand-written MIR so that the call operand is `Copy(a)` in one function and
# `Move(a)` in the other, independent of what MIR building/optimization picks.
AUX_CUSTOM_MIR_SRC = r"""
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused)]
extern crate core;
use core::intrinsics::mir::*;

pub struct Big {
    pub blah: [u64; 8],
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_copy_arg(a: Big) {
    mir! {
        {
            Call(RET = custom_call_copy_arg(a), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}

#[inline(never)]
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub fn custom_call_move_arg(a: Big) {
    mir! {
        {
            Call(RET = custom_call_move_arg(Move(a)), ReturnTo(bb1), UnwindUnreachable())
        }
        bb1 = {
            Return()
        }
    }
}
"""

# Explicit tail call: both parameters are only *read* by the function's own
# statements, and the `become` passes fresh values.
AUX_TAIL_CALL_SRC = r"""
#![feature(explicit_tail_calls)]
#![allow(incomplete_features, unused)]

pub struct BigFreeze(pub [u64; 8]);

#[inline(never)]
pub fn tail_helper(a: BigFreeze, b: BigFreeze, n: u64) -> u64 {
    a.0[0] ^ b.0[0] ^ n
}

#[inline(never)]
pub fn tail_reads_then_becomes(a: BigFreeze, b: BigFreeze, n: u64) -> u64 {
    if n == 0 {
        return a.0[0] ^ b.0[0];
    }
    let s = a.0[1].wrapping_add(b.0[1]);
    become tail_helper(BigFreeze([s; 8]), BigFreeze([n; 8]), n - 1)
}
"""

# name -> (description, flags, source)
CASES = {
    # ---- the six cases shared with the recorded baseline ------------------
    "impossible_01_trivial_bounds_string_copy_erased_to_unreachable": (
        "global contradiction `String: Copy` under `trivial_bounds`",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""#![feature(trivial_bounds)]
pub fn impossible_string_copy(x: u32) -> u32
where
    String: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "impossible_02_generic_dyn_trait_sized_erased_to_unreachable": (
        "structurally impossible `dyn MyTrait<T>: Sized` mentioning a generic parameter",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""pub trait MyTrait<T> {}
pub fn impossible_dyn_sized<T>(x: u32) -> u32
where
    dyn MyTrait<T>: Sized,
{
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "mono_03_rust_abi_simd_vector_passes_indirect_ok": (
        "256-bit vector by value through the Rust ABI, no `avx` anywhere",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
#[inline(never)]
pub fn callee_takes_ymm_rust(v: Simd256) -> Simd256 {
    v
}
pub fn caller_without_avx(v: Simd256) -> Simd256 {
    callee_takes_ymm_rust(v)
}
""",
    ),
    "mono_03b_extern_c_avx2_simd_vector_by_value_rejected": (
        "256-bit vector by value to an `extern \"C\"` function that enables `avx2`; caller enables nothing",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
#[target_feature(enable = "avx2")]
pub unsafe extern "C" fn callee_takes_ymm_c(v: Simd256) -> Simd256 { v }

pub fn caller_without_avx(v: Simd256) -> Simd256 {
    unsafe { callee_takes_ymm_c(v) }
}
""",
    ),
    "mono_04_extern_c_unsized_slice_param_rejected_post_mono": (
        "unsized by-value parameter on a non-rustic ABI",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(unsized_fn_params)]
pub extern "C" fn c_abi_unsized_slice(_s: [u8]) {}
""",
    ),
    "mono_05_move_size_limit_lint_or_check": (
        "256-byte move with `-Z move-size-limit=64`, lint denied",
        ["--crate-type=lib", "--emit=obj", "-Z", "move-size-limit=64", "-D", "large-assignments"],
        r"""pub fn big_move(src: &[u8; 256]) -> [u8; 256] {
    let x = *src;
    x
}
""",
    ),
    # ---- controls added by this probe (not in the recorded baseline) ------
    "ctl_impossible_01b_no_where_clause_keeps_body": (
        "control for case 01: identical body, no where clause",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""pub fn possible_plain(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "ctl_impossible_02b_generic_param_clause_keeps_body": (
        "control: `T: Copy` is unsatisfiable for some `T` but not all",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""pub fn possible_for_some_t<T>(x: u32) -> u32
where
    T: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "ctl_impossible_02c_generic_str_sized_clause": (
        "structurally impossible `str: Sized`, written with a generic parameter in scope",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""#![feature(trivial_bounds)]
pub fn impossible_str_sized<T>(x: u32) -> u32
where
    str: Sized,
{
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "ctl_impossible_01d_erased_body_at_opt_level_0": (
        "case 01 at `-C opt-level=0`: is erasure independent of optimization?",
        ["--crate-type=lib", "-C", "opt-level=0", "--emit=mir"],
        r"""#![feature(trivial_bounds)]
pub fn impossible_string_copy(x: u32) -> u32
where
    String: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
""",
    ),
    "ctl_impossible_01e_calling_trivially_false_item_rejected": (
        "a call to the item of case 01: is any well-typed use possible?",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""#![feature(trivial_bounds)]
pub fn impossible_string_copy(x: u32) -> u32
where
    String: Copy,
{
    x.wrapping_mul(3).wrapping_add(1)
}
pub fn caller() -> u32 {
    impossible_string_copy(1)
}
""",
    ),
    "ctl_impossible_02e_calling_dyn_sized_item_rejected": (
        "a call to the item of case 02 at a concrete `T`",
        ["--crate-type=lib", "-C", "opt-level=1", "--emit=mir"],
        r"""pub trait MyTrait<T> {}
pub fn impossible_dyn_sized<T>(x: u32) -> u32
where
    dyn MyTrait<T>: Sized,
{
    x.wrapping_mul(3).wrapping_add(1)
}
pub fn caller() -> u32 {
    impossible_dyn_sized::<u8>(1)
}
""",
    ),
    "ctl_mono_03c_extern_c_caller_enables_avx_ok": (
        "control for 03b: the caller carries `#[target_feature(enable = \"avx\")]` (not `avx2`)",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
#[target_feature(enable = "avx2")]
pub unsafe extern "C" fn callee_takes_ymm_c(v: Simd256) -> Simd256 { v }

#[target_feature(enable = "avx")]
pub unsafe fn caller_with_avx(v: Simd256) -> Simd256 {
    unsafe { callee_takes_ymm_c(v) }
}
""",
    ),
    "ctl_mono_03d_extern_c_definition_without_avx_rejected": (
        "definition-site check: `extern \"C\"` definition taking a 256-bit vector, no `avx`",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
pub extern "C" fn definition_takes_ymm_c(v: Simd256) -> Simd256 { v }
""",
    ),
    "ctl_mono_03e_extern_c_128bit_vector_ok": (
        "control: a 128-bit vector through `extern \"C\"` needs only `sse`, baseline on x86-64",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd128([u64; 2]);
#[inline(never)]
pub extern "C" fn callee_takes_xmm_c(v: Simd128) -> Simd128 { v }

pub fn caller_baseline(v: Simd128) -> Simd128 {
    callee_takes_xmm_c(v)
}
""",
    ),
    "obs_mono_03f_foreign_declaration_with_simd_type": (
        "observation only: the vector type on a *foreign declaration* instead of a Rust definition",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(repr_simd)]
#[repr(simd)]
#[derive(Clone, Copy)]
pub struct Simd256([u64; 4]);
extern "C" {
    fn foreign_takes_ymm_c(v: Simd256) -> u64;
}
pub fn caller_without_avx(v: Simd256) -> u64 {
    unsafe { foreign_takes_ymm_c(v) }
}
""",
    ),
    "ctl_mono_04b_rust_abi_unsized_slice_param_ok": (
        "control for 04: the same unsized parameter on the Rust ABI",
        ["--crate-type=lib", "--emit=obj"],
        r"""#![feature(unsized_fn_params)]
pub fn rust_abi_unsized_slice(_s: [u8]) {}
""",
    ),
    "ctl_mono_05b_no_limit_flag_no_lint": (
        "control for 05: same source, no `-Z move-size-limit`",
        ["--crate-type=lib", "--emit=obj", "-D", "large-assignments"],
        r"""pub fn big_move(src: &[u8; 256]) -> [u8; 256] {
    let x = *src;
    x
}
""",
    ),
    "ctl_mono_05c_move_into_call_argument_opt0": (
        "a 256-byte value passed by move to a call, unoptimized MIR",
        ["--crate-type=lib", "--emit=obj,mir", "-C", "opt-level=0", "-Z", "move-size-limit=64", "-D", "large-assignments"],
        r"""pub struct Big(pub [u8; 256]);
#[inline(never)]
pub fn sink(b: Big) -> u8 {
    b.0[0]
}
pub fn pass_by_move(b: Big) -> u8 {
    sink(b)
}
""",
    ),
    "ctl_mono_05d_move_into_call_argument_opt2": (
        "the same source as 05c with `-C opt-level=2`",
        ["--crate-type=lib", "--emit=obj,mir", "-C", "opt-level=2", "-Z", "move-size-limit=64", "-D", "large-assignments"],
        r"""pub struct Big(pub [u8; 256]);
#[inline(never)]
pub fn sink(b: Big) -> u8 {
    b.0[0]
}
pub fn pass_by_move(b: Big) -> u8 {
    sink(b)
}
""",
    ),
}

# IR-level view of the vector pass modes (cases 03 and 03c), emitted as LLVM IR.
IR_CASES = {
    "ir_mono_03_rust_abi_simd256_signature": (
        ["--crate-type=lib", "-C", "opt-level=2", "-C", "no-prepopulate-passes", "--emit=llvm-ir"],
        "mono_03_rust_abi_simd_vector_passes_indirect_ok",
        ["callee_takes_ymm_rust"],
    ),
    "ir_mono_03c_extern_c_simd256_signature": (
        ["--crate-type=lib", "-C", "opt-level=2", "-C", "no-prepopulate-passes", "--emit=llvm-ir"],
        "ctl_mono_03c_extern_c_caller_enables_avx_ok",
        ["callee_takes_ymm_c"],
    ),
    "ir_mono_03e_extern_c_simd128_signature": (
        ["--crate-type=lib", "-C", "opt-level=2", "-C", "no-prepopulate-passes", "--emit=llvm-ir"],
        "ctl_mono_03e_extern_c_128bit_vector_ok",
        ["callee_takes_xmm_c"],
    ),
}

# ---------------------------------------------------------------------------
# Predictions derived from the rustc source at 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1.
# Per function: list of (param_index, readonly, captures) for pointer params
# of the *rustc-emitted* signature when deduction is active.
# ---------------------------------------------------------------------------

PREDICTED_ACTIVE = {
    "read_big_freeze": [(0, True, "none")],
    "read_big_copy": [(0, True, "none")],
    "shared_borrow_big_freeze": [(0, True, "address")],
    "shared_borrow_big_cell": [(0, False, "address")],
    "raw_const_borrow_big_freeze": [(0, False, "address")],
    "mutate_local_copy_big_freeze": [(0, False, "none")],
    "forward_by_move_indirect": [(0, False, "address")],
    "mixed_read_then_forward": [(0, True, "none"), (1, False, "address")],
    "mixed_forward_then_read": [(0, False, "address"), (1, True, "none")],
    "ret_never_returns": [(0, False, "none")],
    "ret_not_captured": [(0, False, "none")],
    "ret_captured": [(0, False, "address")],
}
# Deduction inactive (empty table): every indirect pointer keeps the defaults.
PREDICTED_INACTIVE = {
    name: [(idx, False, "address") for (idx, _ro, _cap) in rows]
    for name, rows in PREDICTED_ACTIVE.items()
}
# Generic instantiations (downstream `define`, only meaningful without LLVM's
# own attribute inference, i.e. under `-C no-prepopulate-passes`).
PREDICTED_GENERIC_ACTIVE = {
    "generic_drop_only::<u64>": [(0, True, "none")],
    "generic_drop_only::<String>": [(0, False, "address")],
}
PREDICTED_AUX_ACTIVE = {
    "custom_call_copy_arg": [(0, True, "none")],
    "custom_call_move_arg": [(0, False, "address")],
    "tail_reads_then_becomes": [(0, False, "address"), (1, False, "address")],
}

UPSTREAM_FUNCTIONS = list(PREDICTED_ACTIVE.keys()) + ["generic_drop_only", "sink_big_freeze"]

# name -> (upstream flags, downstream flags, upstream incremental?, downstream incremental?,
#          deduction active for upstream-defined functions as seen by downstream?,
#          deduction active for upstream's own local definitions?)
MATRIX = {
    "opt2_non_incr": (["-C", "opt-level=2"], ["-C", "opt-level=2"], False, False),
    "opt2_incremental": (["-C", "opt-level=2"], ["-C", "opt-level=2"], True, True),
    "opt2_up_incr_only": (["-C", "opt-level=2"], ["-C", "opt-level=2"], True, False),
    "opt2_down_incr_only": (["-C", "opt-level=2"], ["-C", "opt-level=2"], False, True),
    "opt2_non_incr_noprepop": (
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        False,
        False,
    ),
    "opt2_incremental_noprepop": (
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        True,
        True,
    ),
    "opt2_up_incr_only_noprepop": (
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        True,
        False,
    ),
    "opt2_down_incr_only_noprepop": (
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        False,
        True,
    ),
    "up_opt0_down_opt2_noprepop": (
        ["-C", "opt-level=0"],
        ["-C", "opt-level=2", "-C", "no-prepopulate-passes"],
        False,
        False,
    ),
}

COMMON = ["--edition=2021", "-C", "codegen-units=1", "-C", "symbol-mangling-version=v0"]

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def run(cmd, cwd):
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=600)
    return proc.returncode, proc.stdout, proc.stderr


EXTRA_REDACTIONS = []  # (absolute path prefix, placeholder), filled in by main()


def sanitize(text, roots):
    """Remove host-specific absolute paths from compiler output."""
    for root in roots:
        if root:
            text = text.replace(root, "<tmp>")
    for prefix, placeholder in EXTRA_REDACTIONS:
        if prefix:
            text = text.replace(prefix, placeholder)
    # Paths baked into the compiler binary by its own build (seen in panics).
    text = re.sub(r"/rustc(?:-dev)?/[0-9a-f]{40}/", "<rustc-src>/", text)
    return text


def split_top_level(text):
    parts, depth, cur = [], 0, []
    for ch in text:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    tail = "".join(cur).strip()
    if tail:
        parts.append(tail)
    return parts


def param_list(line, open_idx):
    """Return the text between the parenthesis at `open_idx` and its match."""
    depth = 0
    for i in range(open_idx, len(line)):
        if line[i] == "(":
            depth += 1
        elif line[i] == ")":
            depth -= 1
            if depth == 0:
                return line[open_idx + 1 : i]
    return line[open_idx + 1 :]


FLAG_WORDS = (
    "readonly",
    "readnone",
    "writeonly",
    "writable",
    "noalias",
    "nofree",
    "noundef",
    "nonnull",
    "nocapture",
    "dead_on_return",
    "dead_on_unwind",
)


def parse_param(text):
    tokens = text.split()
    info = {"type": tokens[0] if tokens else "", "text": text}
    if text.startswith("<") or text.startswith("{") or text.startswith("["):
        depth = 0
        for i, ch in enumerate(text):
            if ch in "<{[":
                depth += 1
            elif ch in ">}]":
                depth -= 1
                if depth == 0:
                    info["type"] = text[: i + 1]
                    break
    for word in FLAG_WORDS:
        info[word] = re.search(r"(?<![\w(])" + word + r"(?![\w(])", text) is not None
    cap = re.search(r"captures\(([^)]*)\)", text)
    if cap:
        info["captures"] = cap.group(1).strip()
    elif info["nocapture"]:
        info["captures"] = "none"
    else:
        info["captures"] = None
    info["sret"] = "sret(" in text
    deref = re.search(r"dereferenceable\((\d+)\)", text)
    info["dereferenceable"] = int(deref.group(1)) if deref else None
    return info


def parse_signature(line):
    m = re.match(r"^(define|declare)\b.*?@([A-Za-z0-9_.$]+)\(", line)
    if not m:
        return None
    params = [parse_param(p) for p in split_top_level(param_list(line, m.end() - 1))]
    return {"kind": m.group(1), "symbol": m.group(2), "params": params}


def pointer_rows(sig):
    """(index, readonly, captures) for every `ptr` parameter of a signature."""
    rows = []
    for idx, p in enumerate(sig["params"]):
        if p["type"] == "ptr":
            rows.append((idx, bool(p["readonly"]), p["captures"]))
    return rows


def find_signatures(ll_text, name):
    """All define/declare lines whose v0-mangled symbol contains `<len><name>`."""
    needle = f"{len(name)}{name}"
    out = []
    for line in ll_text.splitlines():
        if not (line.startswith("define ") or line.startswith("declare ")):
            continue
        sig = parse_signature(line)
        if sig is None:
            continue
        sym = sig["symbol"]
        pos = sym.find(needle)
        if pos < 0:
            continue
        # Reject matches where the length prefix is the tail of a longer number.
        if pos > 0 and sym[pos - 1].isdigit():
            continue
        sig["line"] = line
        out.append(sig)
    return out


def rows_json(rows):
    return [{"param": i, "readonly": ro, "captures": cap} for (i, ro, cap) in rows]


def compare_rows(observed, predicted):
    """Compare only the parameters named by the prediction."""
    obs = {i: (ro, cap) for (i, ro, cap) in observed}
    mismatches = []
    for (i, ro, cap) in predicted:
        if i not in obs:
            mismatches.append({"param": i, "predicted": [ro, cap], "observed": None})
        elif obs[i] != (ro, cap):
            mismatches.append({"param": i, "predicted": [ro, cap], "observed": list(obs[i])})
    return mismatches


def function_body(ll_text, name):
    """Text of the first `define` whose symbol contains `<len><name>`, through its `}`."""
    needle = f"{len(name)}{name}"
    lines = ll_text.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("define ") and needle in line:
            body = [line]
            for nxt in lines[i + 1 :]:
                body.append(nxt)
                if nxt == "}":
                    break
            return "\n".join(body)
    return None


def analyze_forwarding_witness(ll_text, name="forwarding_witness"):
    """How did the downstream crate lower `read_big_copy(*src)`?"""
    body = function_body(ll_text, name)
    if body is None:
        return None
    first = body.splitlines()[0]
    sig = parse_signature(first)
    # The incoming `&BigCopy` is the witness's only parameter; LLVM keeps its name.
    m = re.search(r"(%[\w.]+)\)\s*unnamed_addr", first)
    incoming = m.group(1) if m else None
    call_lines = [l.strip() for l in body.splitlines() if "13read_big_copy(" in l and "call" in l]
    passes_incoming = None
    if call_lines and incoming:
        args = param_list(call_lines[0], call_lines[0].index("13read_big_copy(") + len("13read_big_copy"))
        passes_incoming = args.strip().endswith(incoming)
    return {
        "incoming_pointer": incoming,
        "has_alloca": " alloca " in body,
        "memcpy_count": body.count("call void @llvm.memcpy"),
        "has_memcpy": "llvm.memcpy" in body,
        "call_lines": call_lines,
        "call_passes_incoming_pointer": passes_incoming,
        "param_count": len(sig["params"]) if sig else None,
    }


# ---------------------------------------------------------------------------
# Part A: cross-crate attribute matrix
# ---------------------------------------------------------------------------


def run_matrix_config(rustc, work, name, cfg, roots):
    up_flags, down_flags, up_incr, down_incr = cfg
    d = os.path.join(work, "matrix", name)
    os.makedirs(d)
    with open(os.path.join(d, "deduce_up.rs"), "w") as fh:
        fh.write(UP_SRC)
    with open(os.path.join(d, "deduce_down.rs"), "w") as fh:
        fh.write(DOWN_SRC)

    up_cmd = [rustc, *COMMON, "--crate-name=deduce_up", "--crate-type=rlib", *up_flags]
    if up_incr:
        up_cmd += ["-C", "incremental=" + os.path.join(d, "incr_up")]
    up_cmd += ["--emit=llvm-ir,link,mir", "--out-dir", d, "deduce_up.rs"]
    rc_up, _so, se_up = run(up_cmd, d)

    result = {
        "upstream_flags": up_flags + (["-C", "incremental=<dir>"] if up_incr else []),
        "downstream_flags": down_flags + (["-C", "incremental=<dir>"] if down_incr else []),
        "upstream_rc": rc_up,
        "upstream_stderr": sanitize(se_up, roots)[:4000],
    }
    if rc_up != 0:
        return result, None

    down_cmd = [rustc, *COMMON, "--crate-name=deduce_down", "--crate-type=lib", *down_flags]
    if down_incr:
        down_cmd += ["-C", "incremental=" + os.path.join(d, "incr_down")]
    down_cmd += [
        "--extern",
        "deduce_up=" + os.path.join(d, "libdeduce_up.rlib"),
        "--emit=llvm-ir",
        "--out-dir",
        d,
        "deduce_down.rs",
    ]
    rc_down, _so, se_down = run(down_cmd, d)
    result["downstream_rc"] = rc_down
    result["downstream_stderr"] = sanitize(se_down, roots)[:4000]
    if rc_down != 0:
        return result, None

    with open(os.path.join(d, "deduce_up.ll")) as fh:
        up_ll = fh.read()
    with open(os.path.join(d, "deduce_down.ll")) as fh:
        down_ll = fh.read()
    mir_path = os.path.join(d, "deduce_up.mir")
    mir_text = None
    if os.path.exists(mir_path):
        with open(mir_path) as fh:
            mir_text = sanitize(fh.read(), roots)

    functions = {}
    for fn in UPSTREAM_FUNCTIONS:
        entry = {"upstream_define": [], "downstream_declare": [], "downstream_define": []}
        for sig in find_signatures(up_ll, fn):
            if sig["kind"] == "define":
                entry["upstream_define"].append(
                    {"line": sig["line"], "pointer_params": rows_json(pointer_rows(sig))}
                )
        for sig in find_signatures(down_ll, fn):
            key = "downstream_declare" if sig["kind"] == "declare" else "downstream_define"
            entry[key].append(
                {"line": sig["line"], "pointer_params": rows_json(pointer_rows(sig))}
            )
        functions[fn] = entry
    result["functions"] = functions
    result["forwarding_witness"] = analyze_forwarding_witness(down_ll)
    split = analyze_forwarding_witness(down_ll, "forwarding_witness_split")
    if split is not None:
        split["observed_forwarded"] = (
            bool(split["call_passes_incoming_pointer"]) and not split["has_memcpy"]
        )
    result["forwarding_witness_split"] = split
    return result, mir_text


def evaluate_matrix(name, cfg, result):
    """Attach prediction checks.  Predictions only apply where LLVM's own
    attribute inference cannot interfere: `declare` lines always, `define`
    lines only under `-C no-prepopulate-passes`.

    Source model (three independent gates, all on session options):
      * producer: the `deduced_param_attrs` provider returns an empty table
        when the *defining* crate is unoptimized or incremental, and the
        metadata encoder then writes no table at all;
      * consumer: `TyCtxt::fn_abi_of_instance` asks for deduced attributes
        only when the *using* crate is optimized and not incremental."""
    up_flags, down_flags, up_incr, down_incr = cfg
    if "functions" not in result:
        return
    up_opt = "opt-level=0" not in up_flags
    down_opt = "opt-level=0" not in down_flags
    producer_active = up_opt and not up_incr
    consumer_active = down_opt and not down_incr
    # What the downstream crate sees for upstream-defined functions.
    cross_crate_active = producer_active and consumer_active
    # What the upstream crate emits on its own definitions (it is both
    # producer and consumer of its own facts).
    local_active = producer_active
    result["source_model"] = {
        "producer_active": producer_active,
        "consumer_active": consumer_active,
        "cross_crate_active": cross_crate_active,
        "local_active": local_active,
    }
    noprepop_up = "no-prepopulate-passes" in up_flags
    noprepop_down = "no-prepopulate-passes" in down_flags
    checks = []
    for fn, predicted_active in PREDICTED_ACTIVE.items():
        entry = result["functions"][fn]
        pred = predicted_active if cross_crate_active else PREDICTED_INACTIVE[fn]
        for item in entry["downstream_declare"]:
            rows = [(r["param"], r["readonly"], r["captures"]) for r in item["pointer_params"]]
            checks.append(
                {
                    "function": fn,
                    "site": "downstream_declare",
                    "deduction_predicted_active": cross_crate_active,
                    "mismatches": compare_rows(rows, pred),
                }
            )
        if not entry["downstream_declare"]:
            checks.append(
                {
                    "function": fn,
                    "site": "downstream_declare",
                    "deduction_predicted_active": cross_crate_active,
                    "mismatches": [{"error": "no declare line found"}],
                }
            )
        if noprepop_up and up_opt:
            pred_local = predicted_active if local_active else PREDICTED_INACTIVE[fn]
            for item in entry["upstream_define"]:
                rows = [(r["param"], r["readonly"], r["captures"]) for r in item["pointer_params"]]
                checks.append(
                    {
                        "function": fn,
                        "site": "upstream_define",
                        "deduction_predicted_active": local_active,
                        "mismatches": compare_rows(rows, pred_local),
                    }
                )
    if noprepop_down:
        # Generic instantiations are defined downstream from upstream metadata.
        entry = result["functions"]["generic_drop_only"]
        for item in entry["downstream_define"]:
            rows = [(r["param"], r["readonly"], r["captures"]) for r in item["pointer_params"]]
            line = item["line"]
            # v0 mangling: `y` is u64; the String instance names `alloc::string::String`.
            inst = "generic_drop_only::<String>" if "6String" in line else "generic_drop_only::<u64>"
            item["instance"] = inst
            pred = (
                PREDICTED_GENERIC_ACTIVE[inst]
                if cross_crate_active
                else [(0, False, "address")]
            )
            checks.append(
                {
                    "function": inst,
                    "site": "downstream_define",
                    "deduction_predicted_active": cross_crate_active,
                    "mismatches": compare_rows(rows, pred),
                }
            )
    # Forwarding needs the attributes on the declaration *and* LLVM's
    # optimization pipeline (absent under `-C no-prepopulate-passes`).
    fw = result.get("forwarding_witness")
    if fw is not None:
        expect_forwarded = cross_crate_active and not noprepop_down
        fw["predicted_forwarded"] = expect_forwarded
        observed = bool(fw["call_passes_incoming_pointer"]) and not fw["has_memcpy"]
        fw["observed_forwarded"] = observed
        checks.append(
            {
                "function": "forwarding_witness",
                "site": "downstream_body",
                "deduction_predicted_active": cross_crate_active,
                "mismatches": []
                if observed == expect_forwarded
                else [{"predicted_forwarded": expect_forwarded, "observed_forwarded": observed}],
            }
        )
    result["prediction_checks"] = checks
    result["prediction_mismatch_count"] = sum(1 for c in checks if c["mismatches"])


def run_aux(rustc, work, name, src, fns, roots):
    d = os.path.join(work, "aux", name)
    os.makedirs(d)
    with open(os.path.join(d, name + ".rs"), "w") as fh:
        fh.write(src)
    cmd = [
        rustc,
        *COMMON,
        "--crate-name=" + name,
        "--crate-type=lib",
        "-C",
        "opt-level=2",
        "-C",
        "no-prepopulate-passes",
        "--emit=llvm-ir,mir",
        "--out-dir",
        d,
        name + ".rs",
    ]
    rc, _so, se = run(cmd, d)
    result = {
        "flags": ["-C", "opt-level=2", "-C", "no-prepopulate-passes", "--emit=llvm-ir,mir"],
        "rc": rc,
        "stderr": sanitize(se, roots)[:4000],
        "functions": {},
        "prediction_checks": [],
    }
    mir_text = None
    if rc == 0:
        with open(os.path.join(d, name + ".ll")) as fh:
            ll = fh.read()
        mir_path = os.path.join(d, name + ".mir")
        if os.path.exists(mir_path):
            with open(mir_path) as fh:
                mir_text = sanitize(fh.read(), roots)
        for fn in fns:
            sigs = [s for s in find_signatures(ll, fn) if s["kind"] == "define"]
            result["functions"][fn] = [
                {"line": s["line"], "pointer_params": rows_json(pointer_rows(s))} for s in sigs
            ]
            for s in sigs:
                if fn in PREDICTED_AUX_ACTIVE:
                    result["prediction_checks"].append(
                        {
                            "function": fn,
                            "site": "define",
                            "mismatches": compare_rows(pointer_rows(s), PREDICTED_AUX_ACTIVE[fn]),
                        }
                    )
            if not sigs:
                result["prediction_checks"].append(
                    {"function": fn, "site": "define", "mismatches": [{"error": "no define line"}]}
                )
    result["prediction_mismatch_count"] = sum(
        1 for c in result["prediction_checks"] if c["mismatches"]
    )
    return result, mir_text


# ---------------------------------------------------------------------------
# Parts B and C: single-crate cases
# ---------------------------------------------------------------------------


def mir_function_bodies(mir_text):
    """Map `fn name` -> body text for a `--emit=mir` dump."""
    bodies = {}
    for m in re.finditer(r"^fn ([A-Za-z0-9_:<>]+)\(.*?^}", mir_text, re.S | re.M):
        bodies[m.group(1)] = m.group(0)
    return bodies


def is_lone_unreachable(body):
    blocks = re.findall(r"^\s*bb\d+(?: \(cleanup\))?: \{(.*?)^\s*\}", body, re.S | re.M)
    if len(blocks) != 1:
        return False
    stmts = [s.strip() for s in blocks[0].strip().splitlines() if s.strip()]
    return stmts == ["unreachable;"]


def run_case(rustc, work, name, roots):
    desc, flags, src = CASES[name]
    d = os.path.join(work, "cases", name)
    os.makedirs(d)
    path = os.path.join(d, "case.rs")
    with open(path, "w") as fh:
        fh.write(src)
    cmd = [rustc, "--edition=2021", *flags, "--crate-name=case", "--out-dir", d, "case.rs"]
    rc, _so, se = run(cmd, d)
    stderr = sanitize(se, roots).replace("case.rs", "<tmp>")
    result = {
        "description": desc,
        "flags": flags,
        "rc": rc,
        "error_codes": sorted(set(re.findall(r"error\[(E\d{4})\]", stderr))),
        "error_lines": [l for l in stderr.splitlines() if l.startswith("error")],
        "stderr": stderr[:6000],
    }
    if any(f.startswith("--emit=") and "mir" in f.split("=", 1)[1].split(",") for f in flags):
        mir_path = os.path.join(d, "case.mir")
        if os.path.exists(mir_path):
            with open(mir_path) as fh:
                mir = sanitize(fh.read(), roots)
            bodies = mir_function_bodies(mir)
            result["mir"] = mir[:4000]
            result["mir_functions"] = {
                fn: {"lone_unreachable": is_lone_unreachable(body)} for fn, body in bodies.items()
            }
            result["mir_has_unreachable"] = any(
                v["lone_unreachable"] for v in result["mir_functions"].values()
            )
        else:
            result["mir"] = None
            result["mir_has_unreachable"] = None
    return result


def run_ir_case(rustc, work, name, roots):
    flags, case_name, fns = IR_CASES[name]
    _desc, _flags, src = CASES[case_name]
    d = os.path.join(work, "ircases", name)
    os.makedirs(d)
    with open(os.path.join(d, "case.rs"), "w") as fh:
        fh.write(src)
    cmd = [rustc, *COMMON, *flags, "--crate-name=case", "--out-dir", d, "case.rs"]
    rc, _so, se = run(cmd, d)
    result = {"flags": flags, "source_case": case_name, "rc": rc, "signatures": {}}
    if rc != 0:
        result["stderr"] = sanitize(se, roots).replace("case.rs", "<tmp>")[:3000]
        return result
    with open(os.path.join(d, "case.ll")) as fh:
        ll = fh.read()
    for fn in fns:
        sigs = []
        for line in ll.splitlines():
            if (line.startswith("define ") or line.startswith("declare ")) and fn in line:
                sig = parse_signature(line)
                if sig:
                    sigs.append(
                        {
                            "line": line,
                            "param_types": [p["type"] for p in sig["params"]],
                            "has_sret": any(p["sret"] for p in sig["params"]),
                        }
                    )
        result["signatures"][fn] = sigs
    return result


# Expected outcomes of the single-crate cases, per the pinned-revision source.
PREDICTED_CASES = {
    "impossible_01_trivial_bounds_string_copy_erased_to_unreachable": {"rc": 0, "mir_has_unreachable": True},
    "impossible_02_generic_dyn_trait_sized_erased_to_unreachable": {"rc": 0, "mir_has_unreachable": True},
    "mono_03_rust_abi_simd_vector_passes_indirect_ok": {"rc": 0},
    "mono_03b_extern_c_avx2_simd_vector_by_value_rejected": {
        "rc": 1,
        "stderr_contains": "requires the `avx` target feature, which is not enabled in the caller",
    },
    "mono_04_extern_c_unsized_slice_param_rejected_post_mono": {"rc": 1, "stderr_contains": "unsized type `[u8]`"},
    "mono_05_move_size_limit_lint_or_check": {"rc": 1, "stderr_contains": "moving 256 bytes"},
    "ctl_impossible_01b_no_where_clause_keeps_body": {"rc": 0, "mir_has_unreachable": False},
    "ctl_impossible_02b_generic_param_clause_keeps_body": {"rc": 0, "mir_has_unreachable": False},
    "ctl_impossible_02c_generic_str_sized_clause": {"rc": 0, "mir_has_unreachable": True},
    "ctl_impossible_01d_erased_body_at_opt_level_0": {"rc": 0, "mir_has_unreachable": True},
    "ctl_impossible_01e_calling_trivially_false_item_rejected": {"rc": 1, "stderr_contains": "E0277"},
    "ctl_impossible_02e_calling_dyn_sized_item_rejected": {"rc": 1, "stderr_contains": "E0277"},
    "ctl_mono_03c_extern_c_caller_enables_avx_ok": {"rc": 0},
    "ctl_mono_03d_extern_c_definition_without_avx_rejected": {
        "rc": 1,
        "stderr_contains": "requires the `avx` target feature, which is not enabled",
    },
    "ctl_mono_03e_extern_c_128bit_vector_ok": {"rc": 0},
    "ctl_mono_04b_rust_abi_unsized_slice_param_ok": {"rc": 0},
    "ctl_mono_05b_no_limit_flag_no_lint": {"rc": 0},
    "ctl_mono_05c_move_into_call_argument_opt0": {"rc": 1, "stderr_contains": "moving 256 bytes"},
    "ctl_mono_05d_move_into_call_argument_opt2": {"rc": 0},
}


def evaluate_case(name, result):
    if name not in PREDICTED_CASES:
        # Recorded without an expectation: no source-derived prediction exists.
        result["observation_only"] = True
        result["prediction_mismatches"] = []
        return
    pred = PREDICTED_CASES[name]
    mismatches = []
    if result["rc"] != pred["rc"]:
        mismatches.append({"field": "rc", "predicted": pred["rc"], "observed": result["rc"]})
    if "mir_has_unreachable" in pred and result.get("mir_has_unreachable") != pred["mir_has_unreachable"]:
        mismatches.append(
            {
                "field": "mir_has_unreachable",
                "predicted": pred["mir_has_unreachable"],
                "observed": result.get("mir_has_unreachable"),
            }
        )
    if "stderr_contains" in pred and pred["stderr_contains"] not in result["stderr"]:
        mismatches.append(
            {"field": "stderr_contains", "predicted": pred["stderr_contains"], "observed": False}
        )
    result["prediction_mismatches"] = mismatches


# ---------------------------------------------------------------------------
# Comparison with a recorded baseline from another toolchain
# ---------------------------------------------------------------------------


def compare_with_baseline(results, baseline):
    """The baseline records raw `declare`/`define` lines per function for the
    configurations `opt2_non_incr` and `opt2_incremental`, and rc / MIR facts
    for six cases.  Only `declare` lines are compared for the matrix because
    `define` lines under the full LLVM pipeline also carry attributes inferred
    by LLVM itself."""
    out = {"baseline_rustc_version": baseline.get("rustc_version"), "matrix": [], "cases": []}
    base_matrix = baseline.get("deduce_param_attrs_llvm_ir", {})
    for cfg_name, fns in base_matrix.items():
        local_cfg = results["matrix"].get(cfg_name, {})
        for fn, lines in fns.items():
            base_rows = None
            for line in lines:
                if line.startswith("declare "):
                    sig = parse_signature(line)
                    if sig:
                        base_rows = pointer_rows(sig)
            local_rows = None
            entry = local_cfg.get("functions", {}).get(fn)
            if entry and entry["downstream_declare"]:
                local_rows = [
                    (r["param"], r["readonly"], r["captures"])
                    for r in entry["downstream_declare"][0]["pointer_params"]
                ]
            if base_rows is None:
                status = "baseline_has_no_declare_line"
            elif local_rows is None:
                status = "local_has_no_declare_line"
            else:
                status = "same" if base_rows == local_rows else "different"
            out["matrix"].append(
                {
                    "config": cfg_name,
                    "function": fn,
                    "baseline_declare_pointer_params": rows_json(base_rows) if base_rows else None,
                    "local_declare_pointer_params": rows_json(local_rows) if local_rows else None,
                    "status": status,
                }
            )
    for case_name, base in baseline.get("impossible_clauses_and_mono_checks", {}).items():
        local = results["cases"].get(case_name)
        item = {"case": case_name, "baseline_rc": base.get("rc")}
        if local is None:
            item["status"] = "local_missing"
        else:
            item["local_rc"] = local["rc"]
            same = base.get("rc") == local["rc"]
            if "mir_has_unreachable" in base:
                item["baseline_mir_has_unreachable"] = base["mir_has_unreachable"]
                item["local_mir_has_unreachable"] = local.get("mir_has_unreachable")
                same = same and base["mir_has_unreachable"] == local.get("mir_has_unreachable")
            item["status"] = "same" if same else "different"
        out["cases"].append(item)
    out["different_count"] = sum(
        1 for x in out["matrix"] + out["cases"] if x["status"] == "different"
    )
    return out


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", default=os.environ.get("RUSTC") or shutil.which("rustc"))
    ap.add_argument("--out", default=None, help="write the JSON result here (default: stdout)")
    ap.add_argument("--baseline", default=None, help="recorded result from another toolchain")
    ap.add_argument("--dump-sources", default=None, help="write the embedded Rust sources here")
    ap.add_argument("--dump-mir", default=None, help="write optimized-MIR specimens here")
    ap.add_argument("--strict", action="store_true", help="exit 1 on any prediction mismatch")
    args = ap.parse_args(argv)

    if args.dump_sources:
        os.makedirs(args.dump_sources, exist_ok=True)
        files = {
            "deduce_up.rs": UP_SRC,
            "deduce_down.rs": DOWN_SRC,
            "aux_custom_mir.rs": AUX_CUSTOM_MIR_SRC,
            "aux_tail_call.rs": AUX_TAIL_CALL_SRC,
        }
        for cname, (_d, _f, src) in CASES.items():
            files[cname + ".rs"] = src
        for fname, src in files.items():
            with open(os.path.join(args.dump_sources, fname), "w") as fh:
                fh.write(src.lstrip("\n"))

    if not args.rustc:
        print("no rustc found; pass --rustc", file=sys.stderr)
        return 2

    rc, vv, _se = run([args.rustc, "-vV"], None)
    if rc != 0:
        print("rustc -vV failed", file=sys.stderr)
        return 2
    # Never record where the toolchain or the user's home directory live.
    rc_sys, sysroot, _se = run([args.rustc, "--print", "sysroot"], None)
    if rc_sys == 0 and sysroot.strip():
        EXTRA_REDACTIONS.append((sysroot.strip(), "<sysroot>"))
        EXTRA_REDACTIONS.append((os.path.realpath(sysroot.strip()), "<sysroot>"))
    home = os.path.expanduser("~")
    if home and home != "/":
        EXTRA_REDACTIONS.append((home, "<home>"))

    results = {
        "schema": SCHEMA,
        "rustc_version": vv.strip(),
        "common_flags": COMMON,
        "matrix": {},
        "aux": {},
        "cases": {},
        "ir_cases": {},
    }
    mir_specimens = {}

    with tempfile.TemporaryDirectory(prefix="deduce_probe_") as work:
        roots = [work, os.path.realpath(work)]
        for name, cfg in MATRIX.items():
            res, mir = run_matrix_config(args.rustc, work, name, cfg, roots)
            evaluate_matrix(name, cfg, res)
            results["matrix"][name] = res
            if mir is not None and name in ("opt2_non_incr", "opt2_incremental"):
                mir_specimens[f"deduce_up.{name}.mir"] = mir
        for name, src, fns in (
            ("aux_custom_mir", AUX_CUSTOM_MIR_SRC, ["custom_call_copy_arg", "custom_call_move_arg"]),
            ("aux_tail_call", AUX_TAIL_CALL_SRC, ["tail_reads_then_becomes", "tail_helper"]),
        ):
            res, mir = run_aux(args.rustc, work, name, src, fns, roots)
            results["aux"][name] = res
            if mir is not None:
                mir_specimens[f"{name}.opt2.mir"] = mir
        for name in CASES:
            res = run_case(args.rustc, work, name, roots)
            evaluate_case(name, res)
            results["cases"][name] = res
        for name in IR_CASES:
            results["ir_cases"][name] = run_ir_case(args.rustc, work, name, roots)

    summary = {
        "matrix_prediction_mismatches": {
            n: r.get("prediction_mismatch_count") for n, r in results["matrix"].items()
        },
        "aux_prediction_mismatches": {
            n: r.get("prediction_mismatch_count") for n, r in results["aux"].items()
        },
        "case_prediction_mismatches": {
            n: len(r["prediction_mismatches"]) for n, r in results["cases"].items()
        },
        "build_failures": [
            n
            for n, r in results["matrix"].items()
            if r.get("upstream_rc") != 0 or r.get("downstream_rc") != 0
        ]
        + [n for n, r in results["aux"].items() if r.get("rc") != 0],
    }
    summary["total_prediction_mismatches"] = (
        sum(v or 0 for v in summary["matrix_prediction_mismatches"].values())
        + sum(v or 0 for v in summary["aux_prediction_mismatches"].values())
        + sum(summary["case_prediction_mismatches"].values())
    )
    results["summary"] = summary

    if args.baseline:
        with open(args.baseline) as fh:
            baseline = json.load(fh)
        results["baseline_comparison"] = compare_with_baseline(results, baseline)

    if args.dump_mir:
        os.makedirs(args.dump_mir, exist_ok=True)
        for fname, text in mir_specimens.items():
            with open(os.path.join(args.dump_mir, fname), "w") as fh:
                fh.write(text)

    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        with open(args.out, "w") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)

    print(
        "prediction mismatches: %d; build failures: %s"
        % (summary["total_prediction_mismatches"], summary["build_failures"] or "none"),
        file=sys.stderr,
    )
    if "baseline_comparison" in results:
        print(
            "baseline differences: %d" % results["baseline_comparison"]["different_count"],
            file=sys.stderr,
        )
    if args.strict and (summary["total_prediction_mismatches"] or summary["build_failures"]):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
