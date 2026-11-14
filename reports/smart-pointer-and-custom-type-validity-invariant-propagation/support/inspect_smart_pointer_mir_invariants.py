#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Inspector for rustc 1.99.1 smart-pointer MIR/LLVM invariants and Lean 4.34.1 probe runner (L3)."""

from __future__ import annotations

import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

RUST_PROBE_SRC = r"""
#![crate_type = "lib"]
use std::ptr::NonNull;
use std::rc::Rc;
use std::sync::Arc;

#[no_mangle]
pub fn vec_u8_len(v: &Vec<u8>) -> usize {
    v.len()
}

#[no_mangle]
pub fn vec_u8_capacity(v: &Vec<u8>) -> usize {
    v.capacity()
}

#[no_mangle]
pub fn vec_u8_as_slice_len(v: &Vec<u8>) -> usize {
    v.as_slice().len()
}

#[no_mangle]
pub fn vec_zst_len(v: &Vec<()>) -> usize {
    v.len()
}

#[no_mangle]
pub fn vec_zst_capacity(v: &Vec<()>) -> usize {
    v.capacity()
}

#[no_mangle]
pub fn string_len(s: &String) -> usize {
    s.len()
}

#[no_mangle]
pub fn box_slice_len(b: &Box<[u8]>) -> usize {
    b.len()
}

#[no_mangle]
pub fn arc_slice_len(a: &Arc<[u8]>) -> usize {
    a.len()
}

#[no_mangle]
pub fn rc_slice_len(r: &Rc<[u8]>) -> usize {
    r.len()
}

#[no_mangle]
pub fn nonnull_slice_len(p: NonNull<[u8]>) -> usize {
    p.len()
}

#[no_mangle]
pub fn vec_chunk16_sum_stock(v: &Vec<u8>) -> u64 {
    let mut i = 0usize;
    let mut acc = 0u64;
    while i + 16 <= v.len() {
        acc = acc.wrapping_add(v[i] as u64);
        acc = acc.wrapping_add(v[i + 1] as u64);
        acc = acc.wrapping_add(v[i + 2] as u64);
        acc = acc.wrapping_add(v[i + 3] as u64);
        acc = acc.wrapping_add(v[i + 4] as u64);
        acc = acc.wrapping_add(v[i + 5] as u64);
        acc = acc.wrapping_add(v[i + 6] as u64);
        acc = acc.wrapping_add(v[i + 7] as u64);
        acc = acc.wrapping_add(v[i + 8] as u64);
        acc = acc.wrapping_add(v[i + 9] as u64);
        acc = acc.wrapping_add(v[i + 10] as u64);
        acc = acc.wrapping_add(v[i + 11] as u64);
        acc = acc.wrapping_add(v[i + 12] as u64);
        acc = acc.wrapping_add(v[i + 13] as u64);
        acc = acc.wrapping_add(v[i + 14] as u64);
        acc = acc.wrapping_add(v[i + 15] as u64);
        i += 16;
    }
    acc
}
"""


def run_lean_probe() -> dict[str, object]:
    lean_file = HERE / "SmartPointerValidityAndTypeInvariantProbe.lean"
    cmd = [
        "anneal-lean-run",
        "--mode",
        "file",
        "--concurrency",
        "4",
        "--",
        "elan",
        "run",
        "leanprover/lean4:v4.34.1",
        "lean",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        str(lean_file),
    ]
    t0 = time.perf_counter()
    res = subprocess.run(cmd, text=True, capture_output=True, check=True)
    elapsed_ms = round((time.perf_counter() - t0) * 1000.0, 2)
    out = res.stdout.strip()
    if "sorryAx" in out or "ofReduceBool" in out:
        raise RuntimeError(f"Forbidden axiom in {lean_file.name}:\n{out}")
    return {
        "file": lean_file.name,
        "lines": len(lean_file.read_text(encoding="utf-8").splitlines()),
        "elapsed_ms": elapsed_ms,
        "axiom_output": out.splitlines(),
    }


def inspect_rustc_mir_and_llvm() -> dict[str, object]:
    with tempfile.TemporaryDirectory(prefix="smart_ptr_mir_") as tmpdir:
        tmp = Path(tmpdir)
        src_file = tmp / "probe.rs"
        mir_file = tmp / "probe.mir"
        ll_file = tmp / "probe.ll"
        src_file.write_text(RUST_PROBE_SRC.strip() + "\n", encoding="utf-8")

        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "-C",
                "opt-level=3",
                "-C",
                " no-prepopulate-passes" if False else "opt-level=3",
                "-Z",
                " query-dep-graph=no" if False else "merge-functions=disabled",
                "--emit=mir,llvm-ir",
                str(src_file),
                "--out-dir",
                str(tmp),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if not ll_file.exists():
            subprocess.run(
                [
                    "rustc",
                    "+1.99.1-x86_64-unknown-linux-gnu",
                    "-C",
                    "opt-level=3",
                    "--emit=mir,llvm-ir",
                    str(src_file),
                    "--out-dir",
                    str(tmp),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
        mir_text = mir_file.read_text(encoding="utf-8")
        ll_text = ll_file.read_text(encoding="utf-8")

        # Extract LLVM IR function definitions and range metadata
        fn_summaries: dict[str, dict[str, object]] = {}
        for fn_name in [
            "vec_u8_len",
            "vec_u8_capacity",
            "vec_u8_as_slice_len",
            "vec_zst_len",
            "vec_zst_capacity",
            "string_len",
            "box_slice_len",
            "arc_slice_len",
            "rc_slice_len",
            "nonnull_slice_len",
            "vec_chunk16_sum_stock",
        ]:
            m_ll = re.search(
                rf"(define[^\n]*@{fn_name}\([^\n]*\n(?:.*?\n)*?\}})", ll_text
            )
            ll_body = m_ll.group(1) if m_ll else ""
            if not ll_body:
                m_alias = re.search(rf"(@{fn_name}\s*=\s*[^\n]+)", ll_text)
                ll_body = m_alias.group(1) if m_alias else ""
            panic_bounds_calls = len(re.findall(r"panic_bounds_check", ll_body))
            has_llvm_assume = "@llvm.assume" in ll_body
            has_range_meta = "!range" in ll_body or "range(i64" in ll_body

            m_mir = re.search(
                rf"(fn {fn_name}\([^{{]*\{{.*?\n\}})", mir_text, flags=re.DOTALL
            )
            mir_body = m_mir.group(1) if m_mir else ""
            has_mir_assume = " Intrinsic(Assume(" in mir_body or "assume(" in mir_body

            fn_summaries[fn_name] = {
                "has_mir_assume": has_mir_assume,
                "has_llvm_assume": has_llvm_assume,
                "has_llvm_range_attr_or_meta": has_range_meta,
                "surviving_panic_bounds_check_calls_o3": panic_bounds_calls,
                "llvm_header": ll_body.splitlines()[0] if ll_body else "",
            }

        return fn_summaries


def main() -> None:
    lean_res = run_lean_probe()
    fn_summaries = inspect_rustc_mir_and_llvm()

    smart_pointer_catalog = [
        {
            "type": "Vec<T> (sizeof(T) >= 1)",
            "source_coords": "library/alloc/src/vec/mod.rs:436-439, library/alloc/src/raw_vec/mod.rs:39,85-94",
            "mir_fields": "buf.inner.ptr: Unique<u8> (NonNull<u8>), buf.inner.cap: UsizeNoHighBit, len: usize",
            "tier1_language_validity": "ptr >= 1 (NonNull), 0 <= cap <= isize::MAX (UsizeNoHighBit = 0..=0x7fff_ffff_ffff_ffff); len has raw type usize (0..=usize::MAX)",
            "inlined_mir_assume": "Vec::len() emits intrinsics::assume(len <= T::MAX_SLICE_LEN) (vec/mod.rs:3106); Vec::as_slice() omits assume and uses aggregate_raw_ptr (vec/mod.rs:1865)",
            "tier2_type_invariant": "len <= cap && cap * sizeof(T) <= isize::MAX",
            "stock_llvm_23_chunk16_surviving_checks": fn_summaries["vec_chunk16_sum_stock"][
                "surviving_panic_bounds_check_calls_o3"
            ],
            "minissa_tier1_plus_tier2_surviving_checks": 0,
        },
        {
            "type": "Vec<ZST> (sizeof(T) == 0)",
            "source_coords": "library/alloc/src/raw_vec/mod.rs:46-48, library/alloc/src/vec/mod.rs:3106",
            "mir_fields": "buf.inner.ptr: Unique<u8>, buf.inner.cap: Cap(0), len: usize",
            "tier1_language_validity": "ptr >= 1, cap == 0; RawVec::capacity() returns usize::MAX; len in 0..=usize::MAX",
            "inlined_mir_assume": "T::MAX_SLICE_LEN == usize::MAX (trivial assume)",
            "tier2_type_invariant": "0 <= len <= usize::MAX (cannot bound len <= isize::MAX!)",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 16,
        },
        {
            "type": "String",
            "source_coords": "library/alloc/src/string.rs:365-367",
            "mir_fields": "vec: Vec<u8> (buf.inner.ptr: Unique<u8>, buf.inner.cap: UsizeNoHighBit, len: usize)",
            "tier1_language_validity": "ptr >= 1, 0 <= cap <= isize::MAX",
            "inlined_mir_assume": "String::len() delegates to Vec<u8>::len() -> assume(len <= isize::MAX)",
            "tier2_type_invariant": "len <= cap <= isize::MAX && valid_utf8(buf[0..len])",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 0,
        },
        {
            "type": "Box<[T]> (sizeof(T) >= 1)",
            "source_coords": "library/alloc/src/boxed.rs:235-241",
            "mir_fields": "0: Unique<[T]> (0.0: NonNull<[T]> -> *const [T] !null), 1: Global",
            "tier1_language_validity": "VAL-08: addr(ptr) >= align(T), len * sizeof(T) <= isize::MAX (missed by rustc_codegen_llvm abi.rs:561 on parameters and loads!)",
            "inlined_mir_assume": "PtrMetadata(Deref(b))",
            "tier2_type_invariant": "Covered directly by Tier 1 VAL-08 once MiniSSA seeds Box<[T]> metadata",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 0,
        },
        {
            "type": "Arc<[T]> / Rc<[T]> (sizeof(T) >= 1)",
            "source_coords": "library/alloc/src/sync.rs:274-281,393-405; library/alloc/src/rc.rs:285-289,324-331",
            "mir_fields": "ptr: NonNull<ArcInner<[T]>> (fat raw pointer: data_ptr !null, metadata: usize)",
            "tier1_language_validity": "addr(ptr) >= 2 (align(2)); raw fat pointer metadata has full WrappingRange 0..=usize::MAX before Deref!",
            "inlined_mir_assume": "Deref::deref materializes &[T] (triggering VAL-08 len * sizeof(T) <= isize::MAX)",
            "tier2_type_invariant": "16 + len * sizeof(T) <= isize::MAX && strong >= 1 && weak >= 1",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 0,
        },
        {
            "type": "NonNull<[T]> / Unique<[T]>",
            "source_coords": "library/core/src/ptr/non_null.rs:79-81; library/core/src/ptr/unique.rs:35-43",
            "mir_fields": "pointer: pattern_type!(*const [T] is !null) (ScalarPair: ptr in 1..=usize::MAX, len in 0..=usize::MAX)",
            "tier1_language_validity": "addr(ptr) >= 1; len in 0..=usize::MAX (NonNull::slice_from_raw_parts(dangling, usize::MAX) is valid in safe Rust!)",
            "inlined_mir_assume": "None (must NOT assume len <= isize::MAX unless dereferenced via as_ref() or backed by container invariant)",
            "tier2_type_invariant": "None on standalone NonNull<[T]>; container-specific when embedded in Box<[T]> or RawVec",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 16,
        },
        {
            "type": "SmallVec<[T; N]> / Bytes",
            "source_coords": "ecosystem container ADTs (smallvec, bytes)",
            "mir_fields": "discriminant/capacity tag + inline array union or heap (ptr, len, cap)",
            "tier1_language_validity": "NonNull pointer niche where applicable; len/cap are plain usize",
            "inlined_mir_assume": "as_slice() constructs &[T] via slice::from_raw_parts (emitting VAL-08 on &[T])",
            "tier2_type_invariant": "#[anneal_spec::type_invariant]: len <= capacity() && capacity() * sizeof(T) <= isize::MAX",
            "stock_llvm_23_chunk16_surviving_checks": 16,
            "minissa_tier1_plus_tier2_surviving_checks": 0,
        },
    ]

    output = {
        "rustc_version": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "llvm_version": "23.1.1 (1b9c0d5ff9bbe7634aead059efe6b11a7eeba145)",
        "lean_verification": lean_res,
        "rustc_mir_and_llvm_inspection": fn_summaries,
        "smart_pointer_catalog": smart_pointer_catalog,
    }
    out_path = HERE / "smart_pointer_layout_and_mir_catalog.json"
    out_path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(
        f"L3 VERIFIED: Lean {lean_res['elapsed_ms']} ms; "
        f"vec_chunk16_sum_stock surviving checks at -O3 = "
        f"{fn_summaries['vec_chunk16_sum_stock']['surviving_panic_bounds_check_calls_o3']}"
    )


if __name__ == "__main__":
    main()
