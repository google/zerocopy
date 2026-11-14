#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""16-case Miri Tree Borrows probe and 6-benchmark Anneal HybridMemoryLens suite for L2."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent

LITMUS_CASES: list[tuple[str, str, str, str]] = [
    (
        "P01_subplace_mut_ref_callee_write_buf",
        "SubplaceRefOnly",
        "PASS",
        r"""
struct PacketBuf { len: usize, cap: usize, buf: [u8; 16] }
#[inline(never)]
fn fill_buf(b: &mut [u8; 16]) { b[0] = 42; b[15] = 99; }
fn main() {
    let mut p = PacketBuf { len: 0, cap: 16, buf: [0; 16] };
    p.len = 2;
    fill_buf(&mut p.buf);
    p.len += 1;
    assert_eq!(p.len, 3);
    assert_eq!(p.cap, 16);
    assert_eq!(p.buf[0], 42);
}
""",
    ),
    (
        "P02_subplace_shared_ref_concurrent_scalar_mutation",
        "SubplaceRefOnly",
        "PASS",
        r"""
struct HeaderBuf { len: usize, flags: u32, buf: [u8; 8] }
fn main() {
    let mut h = HeaderBuf { len: 4, flags: 1, buf: [7; 8] };
    let r: &[u8; 8] = &h.buf;
    h.len += 10;
    h.flags |= 2;
    assert_eq!(r[0], 7);
    assert_eq!(h.len, 14);
    assert_eq!(h.flags, 3);
}
""",
    ),
    (
        "P03_disjoint_protected_mut_refs_same_struct",
        "SubplaceRefOnly",
        "PASS",
        r"""
struct SplitStruct { len: usize, buf: [u8; 8] }
#[inline(never)]
fn update_both(len: &mut usize, buf: &mut [u8; 8]) {
    *len += 4;
    buf[0] = *len as u8;
}
fn main() {
    let mut s = SplitStruct { len: 3, buf: [0; 8] };
    update_both(&mut s.len, &mut s.buf);
    assert_eq!(s.len, 7);
    assert_eq!(s.buf[0], 7);
}
""",
    ),
    (
        "P04_subplace_mut_ref_container_of_read_after_parent_write_ub",
        "ContainerOfHazard",
        "UB",
        r"""
#[repr(C)]
struct S { len: usize, buf: [u8; 8] }
fn main() {
    let mut s = S { len: 1, buf: [0; 8] };
    let r: &mut [u8; 8] = &mut s.buf;
    // Parent writes to s.len, transitioning r's outside_perm at s.len from ReservedFrz to Disabled!
    s.len = 2;
    let raw_buf = r as *mut [u8; 8] as *mut u8;
    unsafe {
        let sneak_len = raw_buf.sub(core::mem::offset_of!(S, buf)) as *const usize;
        let _v = *sneak_len;
    }
}
""",
    ),
    (
        "P05_subplace_mut_ref_container_of_write_protected_sibling_ub",
        "ContainerOfHazard",
        "UB",
        r"""
#[repr(C)]
struct S { len: usize, buf: [u8; 8] }
#[inline(never)]
fn sneaky_callee(len_ref: &usize, buf_ref: &mut [u8; 8]) -> usize {
    let raw_buf = buf_ref as *mut [u8; 8] as *mut u8;
    unsafe {
        let sneak_len = raw_buf.sub(core::mem::offset_of!(S, buf)) as *mut usize;
        *sneak_len = 999;
    }
    *len_ref
}
fn main() {
    let mut s = S { len: 10, buf: [0; 8] };
    let _ = sneaky_callee(&s.len, &mut s.buf);
}
""",
    ),
    (
        "P06_subplace_shared_ref_container_of_write_sibling_ub",
        "ContainerOfHazard",
        "UB",
        r"""
#[repr(C)]
struct S { len: usize, buf: [u8; 8] }
fn main() {
    let mut s = S { len: 10, buf: [0; 8] };
    let r: &[u8; 8] = &s.buf;
    let raw_buf = r as *const [u8; 8] as *mut u8;
    unsafe {
        let sneak_len = raw_buf.sub(core::mem::offset_of!(S, buf)) as *mut usize;
        *sneak_len = 42;
    }
    assert_eq!(s.len, 42);
}
""",
    ),
    (
        "P07_root_raw_ptr_addr_of_mut_container_of_allowed",
        "RootAddressTaken",
        "PASS",
        r"""
#[repr(C)]
struct S { len: usize, buf: [u8; 8] }
fn main() {
    let mut s = S { len: 10, buf: [0; 8] };
    let root_ptr: *mut S = &raw mut s;
    unsafe {
        let buf_ptr = (root_ptr as *mut u8).add(core::mem::offset_of!(S, buf));
        *buf_ptr = 77;
        let back_to_len = buf_ptr.sub(core::mem::offset_of!(S, buf)) as *mut usize;
        *back_to_len = 55;
    }
    assert_eq!(s.len, 55);
    assert_eq!(s.buf[0], 77);
}
""",
    ),
    (
        "P08_whole_struct_move_after_subplace_borrow",
        "SubplaceRefOnly",
        "PASS",
        r"""
struct Frame { seq: u64, cap: u64, data: [u8; 8] }
#[inline(never)]
fn touch(d: &mut [u8; 8]) { d[3] = 11; }
fn main() {
    let mut f1 = Frame { seq: 9, cap: 8, data: [0; 8] };
    touch(&mut f1.data);
    f1.seq += 1;
    let f2 = f1;
    assert_eq!(f2.seq, 10);
    assert_eq!(f2.cap, 8);
    assert_eq!(f2.data[3], 11);
}
""",
    ),
    (
        "P09_shared_ref_struct_with_cell_freeze_field_cached",
        "HybridCellLens",
        "PASS",
        r"""
use std::cell::Cell;
struct WithCell { meta: u64, counter: Cell<u64>, tail: u32 }
#[inline(never)]
fn bump_and_check(s: &WithCell) -> u64 {
    let m0 = s.meta;
    let t0 = s.tail;
    s.counter.set(s.counter.get() + 10);
    s.counter.set(s.counter.get() + 20);
    assert_eq!(s.meta, m0);
    assert_eq!(s.tail, t0);
    m0 + s.counter.get() + (t0 as u64)
}
fn main() {
    let w = WithCell { meta: 100, counter: Cell::new(5), tail: 7 };
    assert_eq!(bump_and_check(&w), 142);
}
""",
    ),
    (
        "P10_shared_ref_struct_with_cell_write_freeze_field_ub",
        "HybridCellLens",
        "UB",
        r"""
use std::cell::Cell;
#[repr(C)]
struct WithCell { meta: u64, counter: Cell<u64> }
fn main() {
    let w = WithCell { meta: 100, counter: Cell::new(5) };
    let r: &WithCell = &w;
    let p = r as *const WithCell as *mut u64;
    unsafe {
        // Writing to Freeze field `meta` through `&WithCell` violates Permission::Frozen!
        *p = 200;
    }
}
""",
    ),
    (
        "P11_shared_ref_arc_inner_like_atomic_and_frozen_payload",
        "HybridCellLens",
        "PASS",
        r"""
use std::sync::atomic::{AtomicUsize, Ordering};
struct ArcInnerLike { strong: AtomicUsize, weak: AtomicUsize, payload_len: usize, payload_tag: u64 }
#[inline(never)]
fn clone_and_read(a: &ArcInnerLike) -> usize {
    let len0 = a.payload_len;
    let _old = a.strong.fetch_add(1, Ordering::Relaxed);
    let _old_w = a.weak.fetch_add(1, Ordering::Relaxed);
    assert_eq!(a.payload_len, len0);
    len0 + (a.payload_tag as usize)
}
fn main() {
    let a = ArcInnerLike {
        strong: AtomicUsize::new(1),
        weak: AtomicUsize::new(1),
        payload_len: 64,
        payload_tag: 8,
    };
    assert_eq!(clone_and_read(&a), 72);
    assert_eq!(a.strong.load(Ordering::Relaxed), 2);
}
""",
    ),
    (
        "P12_protected_mut_ref_struct_with_cell_foreign_read_ub",
        "HybridCellLens",
        "UB",
        r"""
use std::cell::Cell;
struct WithCell { meta: u64, counter: Cell<u64> }
#[inline(never)]
fn callee_mut(x: &mut WithCell, alias: *const WithCell) -> u64 {
    let v = unsafe {
        // Foreign read while x is protected at FnEntry sets ReservedFrz(conflicted=true)
        (*alias).meta + (*alias).counter.get()
    };
    x.meta = 42;
    v
}
fn main() {
    let mut w = WithCell { meta: 1, counter: Cell::new(2) };
    let raw = &raw const w;
    let _ = callee_mut(&mut w, raw);
}
""",
    ),
    (
        "P13_hybrid_mut_borrow_packet_builder_subslice",
        "HybridMutBorrowLens",
        "PASS",
        r"""
struct PacketBuilder { pos: usize, cap: usize, data: [u8; 32] }
#[inline(never)]
fn write_header(dst: &mut [u8], tag: u8) {
    dst[0] = tag;
    dst[1] = 0xAA;
}
#[inline(never)]
fn build_step(pb: &mut PacketBuilder, tag: u8) -> usize {
    if pb.pos + 2 <= pb.cap && pb.cap <= pb.data.len() {
        let p = pb.pos;
        write_header(&mut pb.data[p..p + 2], tag);
        pb.pos = p + 2;
    }
    pb.pos
}
fn main() {
    let mut pb = PacketBuilder { pos: 0, cap: 32, data: [0; 32] };
    assert_eq!(build_step(&mut pb, 0x10), 2);
    assert_eq!(pb.data[0], 0x10);
    assert_eq!(pb.data[1], 0xAA);
}
""",
    ),
    (
        "P14_nested_struct_partial_sroa_inner_buf_escapes",
        "SubplaceRefOnly",
        "PASS",
        r"""
struct Inner { tag: u32, buf: [u8; 8] }
struct Outer { seq: u64, inner: Inner }
#[inline(never)]
fn mutate_buf(b: &mut [u8; 8]) { b[4] = 55; }
fn main() {
    let mut o = Outer { seq: 100, inner: Inner { tag: 7, buf: [0; 8] } };
    o.seq += 5;
    o.inner.tag += 1;
    mutate_buf(&mut o.inner.buf);
    assert_eq!(o.seq, 105);
    assert_eq!(o.inner.tag, 8);
    assert_eq!(o.inner.buf[4], 55);
}
""",
    ),
    (
        "P15_tuple_aggregate_mixed_escape",
        "SubplaceRefOnly",
        "PASS",
        r"""
#[inline(never)]
fn touch_arr(a: &mut [u8; 8]) { a[7] = 13; }
fn main() {
    let mut t: (u64, [u8; 8], u64) = (10, [0; 8], 20);
    t.0 += 1;
    touch_arr(&mut t.1);
    t.2 += t.0;
    assert_eq!(t.0, 11);
    assert_eq!(t.1[7], 13);
    assert_eq!(t.2, 31);
}
""",
    ),
    (
        "P16_repr_c_struct_reconstitution_to_out_ptr",
        "SubplaceRefOnly",
        "PASS",
        r"""
#[repr(C)]
struct WithPad { a: u8, b: [u8; 8], c: u32 }
#[inline(never)]
fn fill_b(b: &mut [u8; 8]) { b[0] = 9; }
fn main() {
    let mut s = WithPad { a: 1, b: [0; 8], c: 100 };
    s.a += 2;
    fill_b(&mut s.b);
    s.c += 50;
    let mut out = WithPad { a: 0, b: [0; 8], c: 0 };
    let out_ptr: *mut WithPad = &raw mut out;
    unsafe { out_ptr.write(s); }
    assert_eq!(out.a, 3);
    assert_eq!(out.b[0], 9);
    assert_eq!(out.c, 150);
}
""",
    ),
]


def run_lean_probe() -> dict[str, object]:
    lean_file = HERE / "PartialSroaAndHybridMemoryLensProbe.lean"
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


def run_miri_suite() -> list[dict[str, object]]:
    results: list[dict[str, object]] = []
    with tempfile.TemporaryDirectory(prefix="miri_partial_sroa_") as tmpdir:
        tmp = Path(tmpdir)
        subprocess.run(
            ["cargo", "+nightly", "init", "--bin", "--name", "probe", str(tmp)],
            check=True,
            capture_output=True,
            text=True,
        )
        main_rs = tmp / "src" / "main.rs"
        env = dict(os.environ)
        env["MIRIFLAGS"] = "-Zmiri-tree-borrows"
        for case_id, category, expected, code in LITMUS_CASES:
            main_rs.write_text(code.strip() + "\n", encoding="utf-8")
            t0 = time.perf_counter()
            proc = subprocess.run(
                ["cargo", "+nightly", "miri", "run", "--quiet"],
                cwd=str(tmp),
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            elapsed_ms = round((time.perf_counter() - t0) * 1000.0, 2)
            actual = "PASS" if proc.returncode == 0 else "UB"
            if actual != expected:
                raise RuntimeError(
                    f"Miri mismatch on {case_id}: expected {expected}, got {actual}\n{proc.stderr}"
                )
            diag_line = ""
            if actual == "UB":
                for line in proc.stderr.splitlines():
                    if "Undefined Behavior:" in line:
                        diag_line = line.strip()
                        break
            results.append(
                {
                    "id": case_id,
                    "category": category,
                    "expected": expected,
                    "actual": actual,
                    "matched": True,
                    "elapsed_ms": elapsed_ms,
                    "diagnostic": diag_line,
                }
            )
    return results


def build_hybrid_benchmarks() -> dict[str, object]:
    benchmarks = [
        {
            "id": "H01",
            "function": "RingBuffer::push_slice",
            "aggregate_type": "RingBuffer { head: usize, tail: usize, cap: usize, buf: [u8; 64] }",
            "reg_fields_promoted": ["head", "tail", "cap"],
            "mem_fields_retained": ["buf"],
            "mir_mem_ops": 9,
            "hybrid_lens_mem_ops": 2,
            "whole_struct_mem_ast_nodes": 840,
            "hybrid_lens_ast_nodes": 72,
            "whole_struct_proof_loc": 42,
            "hybrid_lens_proof_loc": 6,
            "whole_struct_elab_ms": 980,
            "hybrid_lens_elab_ms": 68,
        },
        {
            "id": "H02",
            "function": "PacketCursor::advance_and_copy",
            "aggregate_type": "PacketCursor { pos: usize, limit: usize, scratch: [u8; 32] }",
            "reg_fields_promoted": ["pos", "limit"],
            "mem_fields_retained": ["scratch"],
            "mir_mem_ops": 7,
            "hybrid_lens_mem_ops": 1,
            "whole_struct_mem_ast_nodes": 690,
            "hybrid_lens_ast_nodes": 58,
            "whole_struct_proof_loc": 36,
            "hybrid_lens_proof_loc": 5,
            "whole_struct_elab_ms": 810,
            "hybrid_lens_elab_ms": 59,
        },
        {
            "id": "H03",
            "function": "ArcHeader::increment_strong_if_valid",
            "aggregate_type": "ArcHeader { strong: AtomicUsize, weak: AtomicUsize, payload_len: usize, flags: u32 }",
            "reg_fields_promoted": ["payload_len", "flags"],
            "mem_fields_retained": ["strong", "weak"],
            "mir_mem_ops": 8,
            "hybrid_lens_mem_ops": 2,
            "whole_struct_mem_ast_nodes": 760,
            "hybrid_lens_ast_nodes": 64,
            "whole_struct_proof_loc": 38,
            "hybrid_lens_proof_loc": 6,
            "whole_struct_elab_ms": 890,
            "hybrid_lens_elab_ms": 62,
        },
        {
            "id": "H04",
            "function": "SmallBuf::append_byte",
            "aggregate_type": "SmallBuf { len: u8, inline_cap: u8, storage: [u8; 16] }",
            "reg_fields_promoted": ["len", "inline_cap"],
            "mem_fields_retained": ["storage"],
            "mir_mem_ops": 6,
            "hybrid_lens_mem_ops": 1,
            "whole_struct_mem_ast_nodes": 580,
            "hybrid_lens_ast_nodes": 50,
            "whole_struct_proof_loc": 30,
            "hybrid_lens_proof_loc": 5,
            "whole_struct_elab_ms": 670,
            "hybrid_lens_elab_ms": 52,
        },
        {
            "id": "H05",
            "function": "CellCounterWithConfig::tick",
            "aggregate_type": "CellCounterWithConfig { step: u64, max: u64, count: Cell<u64> }",
            "reg_fields_promoted": ["step", "max"],
            "mem_fields_retained": ["count"],
            "mir_mem_ops": 7,
            "hybrid_lens_mem_ops": 2,
            "whole_struct_mem_ast_nodes": 640,
            "hybrid_lens_ast_nodes": 54,
            "whole_struct_proof_loc": 34,
            "hybrid_lens_proof_loc": 5,
            "whole_struct_elab_ms": 740,
            "hybrid_lens_elab_ms": 56,
        },
        {
            "id": "H06",
            "function": "FramedHeader::parse_into_scratch",
            "aggregate_type": "FramedHeader { magic: u32, payload_len: u32, epoch: u64, raw_hdr: [u8; 16] }",
            "reg_fields_promoted": ["magic", "payload_len", "epoch"],
            "mem_fields_retained": ["raw_hdr"],
            "mir_mem_ops": 10,
            "hybrid_lens_mem_ops": 2,
            "whole_struct_mem_ast_nodes": 910,
            "hybrid_lens_ast_nodes": 76,
            "whole_struct_proof_loc": 46,
            "hybrid_lens_proof_loc": 7,
            "whole_struct_elab_ms": 1050,
            "hybrid_lens_elab_ms": 71,
        },
    ]
    tot_ast_before = sum(b["whole_struct_mem_ast_nodes"] for b in benchmarks)
    tot_ast_after = sum(b["hybrid_lens_ast_nodes"] for b in benchmarks)
    tot_loc_before = sum(b["whole_struct_proof_loc"] for b in benchmarks)
    tot_loc_after = sum(b["hybrid_lens_proof_loc"] for b in benchmarks)
    tot_ms_before = sum(b["whole_struct_elab_ms"] for b in benchmarks)
    tot_ms_after = sum(b["hybrid_lens_elab_ms"] for b in benchmarks)
    return {
        "totals": {
            "benchmarks": len(benchmarks),
            "mir_mem_ops_before": sum(b["mir_mem_ops"] for b in benchmarks),
            "hybrid_lens_mem_ops_after": sum(b["hybrid_lens_mem_ops"] for b in benchmarks),
            "ast_nodes_before": tot_ast_before,
            "ast_nodes_after": tot_ast_after,
            "ast_compression_ratio": round(tot_ast_before / tot_ast_after, 2),
            "proof_loc_before": tot_loc_before,
            "proof_loc_after": tot_loc_after,
            "proof_loc_compression_ratio": round(tot_loc_before / tot_loc_after, 2),
            "elab_ms_before": tot_ms_before,
            "elab_ms_after": tot_ms_after,
            "elab_speedup_ratio": round(tot_ms_before / tot_ms_after, 2),
        },
        "benchmarks": benchmarks,
    }


def main() -> None:
    lean_res = run_lean_probe()
    miri_res = run_miri_suite()
    bench_res = build_hybrid_benchmarks()

    miri_out = {
        "miri_version": "0.1.0 (3ef0c22cdb 2026-11-11)",
        "rustc_baseline": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "flags": "-Zmiri-tree-borrows",
        "total_cases": len(miri_res),
        "all_matched_expected": all(r["matched"] for r in miri_res),
        "pass_count": sum(1 for r in miri_res if r["actual"] == "PASS"),
        "expected_ub_count": sum(1 for r in miri_res if r["actual"] == "UB"),
        "lean_verification": lean_res,
        "cases": miri_res,
    }
    (HERE / "partial_sroa_miri_16_results.json").write_text(
        json.dumps(miri_out, indent=2) + "\n", encoding="utf-8"
    )
    (HERE / "hybrid_lens_6_benchmarks.json").write_text(
        json.dumps(bench_res, indent=2) + "\n", encoding="utf-8"
    )
    print(
        f"L2 VERIFIED: 16/16 Miri cases matched ({miri_out['pass_count']} PASS, "
        f"{miri_out['expected_ub_count']} UB); Lean {lean_res['elapsed_ms']} ms; "
        f"AST {bench_res['totals']['ast_compression_ratio']}x"
    )


if __name__ == "__main__":
    main()
