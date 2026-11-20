#!/usr/bin/env python3
"""Empirical MIR census and -O0 vs -O3 execution benchmark for vrustc_certcheck_seed.rs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import statistics
import subprocess
import time
from collections import Counter
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
CRATE_RS = HERE / "vrustc_certcheck_seed.rs"
LEAN_FILE = HERE / "MirToMiniMachO0Seed.lean"
OUT_JSON = HERE / "certcheck_mir_census_and_bench.json"

WS_ROOT = HERE.parent.parent.parent.parent
BUILD_SCRATCH = WS_ROOT / "build_scratch" / "census_bench"


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while True:
            chunk = f.read(65536)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> tuple[int, str, str, float, int]:
    t0 = time.perf_counter()
    proc = subprocess.Popen(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    _, wait_status, rusage = os.wait4(proc.pid, 0)
    stdout_data = proc.stdout.read() if proc.stdout else ""
    stderr_data = proc.stderr.read() if proc.stderr else ""
    if proc.stdout:
        proc.stdout.close()
    if proc.stderr:
        proc.stderr.close()
    dt = time.perf_counter() - t0
    rc = os.waitstatus_to_exitcode(wait_status)
    return rc, stdout_data, stderr_data, dt, int(rusage.ru_maxrss)


def classify_function(fn_sig: str) -> str:
    if "<impl at " in fn_sig:
        if "idiomatic_safe" in fn_sig:
            return "idiomatic_safe"
        return "shared_derives"
    for name in (
        "slice_written_lanes_id",
        "mode_zeroed_lanes_id",
        "analyze_btl_slice",
        "check_btl_idiomatic",
        "check_regalloc_idiomatic",
        "verify_bundle_idiomatic",
        "CheckErr",
    ):
        if f"fn {name}" in fn_sig:
            return "idiomatic_safe"
    return "seed_core"


def classify_local_type(ty: str) -> str:
    t = ty.strip()
    if t in ("u8", "u16", "u32", "u64", "usize", "i8", "i16", "i32", "i64", "isize"):
        return "scalar_int_uint"
    if t == "bool":
        return "bool"
    if t == "()":
        return "unit"
    if t == "!":
        return "never"
    if t.startswith("&mut [") and ";" in t:
        return "ref_mut_array"
    if t.startswith("&[") and ";" in t:
        return "ref_shared_array"
    if t.startswith("&mut "):
        return "ref_mut_other"
    if t.startswith("&"):
        return "ref_shared_other"
    if t.startswith("[") and ";" in t:
        return "array_fixed"
    if t.startswith("(") and t.endswith(")"):
        return "tuple"
    if any(k in t for k in ("Result<", "Option<", "ControlFlow<", "RangeTo<", "Iter<", "Zip<", "TryFromIntError", "CheckErr")):
        return "std_or_result_adt"
    if t.startswith("{closure"):
        return "closure"
    return "user_struct_or_enum"


def analyze_mir_body_text(fn_sig: str, body_text: str) -> dict[str, Any]:
    lines = body_text.splitlines()
    blocks = 0
    locals_by_ty: Counter[str] = Counter()
    stmts: Counter[str] = Counter()
    rvals: Counter[str] = Counter()
    projs: Counter[str] = Counter()
    terms: Counter[str] = Counter()

    in_block = False
    for raw in lines:
        s = raw.strip()
        if not s or s.startswith("//") or s.startswith("debug ") or s.startswith("scope "):
            continue
        if s.startswith("let mut ") or s.startswith("let "):
            if ":" in s:
                ty = s.split(":", 1)[1].rstrip(";").strip()
                locals_by_ty[classify_local_type(ty)] += 1
            continue
        if re.match(r"^bb\d+(\s*\(cleanup\))?:\s*\{$", s):
            blocks += 1
            in_block = True
            continue
        if in_block and s == "}":
            in_block = False
            continue
        if not in_block:
            continue

        # Terminator or statement inside basic block
        if s.startswith("StorageLive("):
            stmts["StorageLive"] += 1
        elif s.startswith("StorageDead("):
            stmts["StorageDead"] += 1
        elif s == "nop;":
            stmts["Nop"] += 1
        elif s.startswith("discriminant("):
            stmts["SetDiscriminant"] += 1
        elif s.startswith("assert("):
            terms["Assert"] += 1
        elif s.startswith("switchInt("):
            terms["SwitchInt"] += 1
        elif s.startswith("goto ->"):
            terms["Goto"] += 1
        elif s == "return;":
            terms["Return"] += 1
        elif s == "unreachable;":
            terms["Unreachable"] += 1
        elif s == "resume;":
            terms["Resume"] += 1
        elif s.startswith("drop("):
            terms["Drop"] += 1
        elif "->" in s and (s.endswith(";") or "unwind" in s):
            terms["Call"] += 1
            projs["deref"] += s.count("(*_")
            projs["field"] += len(re.findall(r"\.\d+:", s))
            projs["downcast"] += len(re.findall(r"\([^()]*\s+as\s+(?!u\d+\b|i\d+\b|usize\b|isize\b|bool\b)[A-Za-z_][A-Za-z0-9_:]*\)", s))
        elif "=" in s:
            stmts["Assign"] += 1
            lhs, rhs = s.split("=", 1)
            lhs = lhs.strip()
            rhs = rhs.strip().rstrip(";")
            # Projections on LHS
            has_proj = False
            if "(*_" in lhs:
                projs["deref"] += 1
                has_proj = True
            if re.search(r"\.\d+", lhs):
                projs["field"] += 1
                has_proj = True
            if "[" in lhs and "constant " in lhs:
                projs["constant_index"] += 1
                has_proj = True
            elif "[" in lhs:
                projs["index"] += 1
                has_proj = True
            if re.search(r"\([^()]*\s+as\s+(?!u\d+\b|i\d+\b|usize\b|isize\b|bool\b)[A-Za-z_]", lhs):
                projs["downcast"] += 1
                has_proj = True
            if not has_proj:
                projs["unprojected_lhs"] += 1

            # Projections on RHS
            projs["deref"] += rhs.count("(*_")
            projs["field"] += len(re.findall(r"\.\d+:", rhs)) + len(re.findall(r"_\d+\.\d+", rhs))
            projs["downcast"] += len(re.findall(r"\([^()]*\s+as\s+(?!u\d+\b|i\d+\b|usize\b|isize\b|bool\b)[A-Za-z_][A-Za-z0-9_:]*\)", rhs))
            if "constant " in rhs and re.search(r"\[[^\]]+\]", rhs) and not rhs.startswith("["):
                projs["constant_index"] += 1
            elif re.search(r"\[_\d+\]", rhs):
                projs["index"] += 1

            # Rvalue kind (check Cast BEFORE Use_Copy/Use_Move since Cast prints `move _x as u8 (IntToInt)`)
            if re.search(r"\s+as\s+.+\([A-Za-z0-9_]+\)$", rhs):
                rvals["Cast"] += 1
            elif rhs.startswith("copy "):
                rvals["Use_Copy"] += 1
            elif rhs.startswith("move "):
                rvals["Use_Move"] += 1
            elif rhs.startswith("const "):
                rvals["Use_Constant"] += 1
            elif rhs.startswith("&mut ") or rhs.startswith("&"):
                rvals["Ref"] += 1
            elif rhs.startswith("PtrMetadata("):
                rvals["UnaryOp_PtrMetadata"] += 1
            elif rhs.startswith("Not(") or rhs.startswith("Neg("):
                rvals["UnaryOp_NotNeg"] += 1
            elif re.match(r"^(Add|Sub|Mul)WithOverflow\(", rhs):
                rvals["OverflowBinaryOp"] += 1
            elif re.match(r"^(Add|AddUnchecked|Sub|SubUnchecked|Mul|MulUnchecked|Div|Rem|BitAnd|BitOr|BitXor|Shl|ShlUnchecked|Shr|ShrUnchecked|Eq|Lt|Le|Ne|Ge|Gt)\(", rhs):
                rvals["BinaryOp"] += 1
            elif rhs.startswith("discriminant("):
                rvals["Discriminant"] += 1
            elif rhs.startswith("[") and ";" in rhs:
                rvals["Repeat"] += 1
            elif rhs.startswith("[") or rhs.startswith("(") or "::" in rhs or rhs.startswith("{"):
                rvals["Aggregate"] += 1
            else:
                rvals["Other"] += 1
        else:
            stmts["Other"] += 1

    # Check if body fits live Trusted/MirSemantics.lean v1 directly
    fits_trusted_v1 = (
        projs["deref"] == 0
        and projs["field"] == 0
        and projs["index"] == 0
        and projs["constant_index"] == 0
        and projs["downcast"] == 0
        and rvals["Ref"] == 0
        and rvals["Cast"] == 0
        and rvals["Aggregate"] == 0
        and rvals["Repeat"] == 0
        and rvals["UnaryOp_PtrMetadata"] == 0
        and rvals["OverflowBinaryOp"] == 0
        and terms["Assert"] == 0
        and terms["Call"] == 0
        and terms["Drop"] == 0
        and terms["Resume"] == 0
        and locals_by_ty["ref_mut_array"] == 0
        and locals_by_ty["ref_shared_array"] == 0
        and locals_by_ty["ref_mut_other"] == 0
        and locals_by_ty["ref_shared_other"] == 0
        and locals_by_ty["array_fixed"] == 0
        and locals_by_ty["std_or_result_adt"] == 0
        and locals_by_ty["user_struct_or_enum"] == 0
        and locals_by_ty["tuple"] == 0
        and locals_by_ty["closure"] == 0
    )

    # Check if body fits the CoreMirO0 extension (stack arrays + fixed stack refs +
    # field/index/deref + scalar casts + overflow/assert + internal calls, NO closures/downcasts/PtrMetadata/Drop/Resume)
    fits_core_mir_o0 = (
        projs["downcast"] == 0
        and rvals["UnaryOp_PtrMetadata"] == 0
        and terms["Drop"] == 0
        and terms["Resume"] == 0
        and locals_by_ty["std_or_result_adt"] == 0
        and locals_by_ty["closure"] == 0
    )

    return {
        "fn": fn_sig,
        "module_group": classify_function(fn_sig),
        "blocks": blocks,
        "locals_by_ty": dict(locals_by_ty),
        "stmts": dict(stmts),
        "rvals": dict(rvals),
        "projs": dict(projs),
        "terms": dict(terms),
        "fits_trusted_v1": fits_trusted_v1,
        "fits_core_mir_o0": fits_core_mir_o0,
    }


def parse_single_fn_dump_dir(mir_dir: Path) -> list[dict[str, Any]]:
    results = []
    for p in sorted(mir_dir.glob("*.3-2-000.runtime-post-cleanup.after.mir")):
        txt = p.read_text()
        m = re.search(r"^(fn .+?)\s*\{", txt, re.MULTILINE)
        if not m:
            continue
        fn_sig = m.group(1)
        results.append(analyze_mir_body_text(fn_sig, txt))
    return results


def aggregate_census(body_records: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[str, list[dict[str, Any]]] = {"all": body_records, "seed_core": [], "idiomatic_safe": [], "shared_derives": []}
    for r in body_records:
        groups[r["module_group"]].append(r)

    summary: dict[str, Any] = {}
    for gname, recs in groups.items():
        if not recs:
            summary[gname] = {"bodies": 0}
            continue
        bb_counts = [r["blocks"] for r in recs]
        loc_c: Counter[str] = Counter()
        st_c: Counter[str] = Counter()
        rv_c: Counter[str] = Counter()
        pr_c: Counter[str] = Counter()
        tm_c: Counter[str] = Counter()
        fit_v1 = 0
        fit_o0 = 0
        for r in recs:
            loc_c.update(r["locals_by_ty"])
            st_c.update(r["stmts"])
            rv_c.update(r["rvals"])
            pr_c.update(r["projs"])
            tm_c.update(r["terms"])
            if r["fits_trusted_v1"]:
                fit_v1 += 1
            if r["fits_core_mir_o0"]:
                fit_o0 += 1
        summary[gname] = {
            "bodies": len(recs),
            "basic_blocks_total": sum(bb_counts),
            "basic_blocks_median": statistics.median(bb_counts),
            "basic_blocks_max": max(bb_counts),
            "fits_trusted_v1_bodies": fit_v1,
            "fits_core_mir_o0_bodies": fit_o0,
            "locals_by_ty": dict(sorted(loc_c.items())),
            "stmts": dict(sorted(st_c.items())),
            "rvals": dict(sorted(rv_c.items())),
            "projs": dict(sorted(pr_c.items())),
            "terms": dict(sorted(tm_c.items())),
        }
    return summary


def hash_runtime_post_cleanup(mir_dir: Path) -> str:
    h = hashlib.sha256()
    files = sorted(mir_dir.glob("*.3-2-000.runtime-post-cleanup.after.mir"))
    for p in files:
        h.update(p.name.encode("utf-8"))
        h.update(b"\0")
        h.update(p.read_bytes())
        h.update(b"\0")
    return h.hexdigest()


BENCH_DRIVER_RS = r'''
use std::hint::black_box;
use std::time::Instant;
use vrustc_certcheck_seed::*;

fn empty_btl() -> BtlSuperblockCert {
    let z = BtlNode { op: 0, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    let fr = FarkasRow { ax: 0, ac: 0, bound: 0, lambda: 0 };
    BtlSuperblockCert {
        src_len: 0,
        tgt_len: 0,
        num_exits: 1,
        num_farkas: 0,
        tgt_check_op: 0,
        tgt_elim_guard: 0,
        src_nodes: [z; MAX_NODES],
        tgt_nodes: [z; MAX_NODES],
        src_exits: [0; MAX_EXITS],
        tgt_exits: [0; MAX_EXITS],
        farkas_rows: [fr; MAX_FARKAS],
        src_guard_removed_flag: 0,
    }
}

fn empty_ra() -> RegAllocCertPacket {
    let z = RaOp {
        kind: 0,
        dst_is_slot: 0,
        dst_idx: 0,
        src_is_slot: 0,
        src_idx: 0,
        slice: 0,
        write_mode: 0,
        vreg: 0,
        live_upper_mask: 0,
    };
    RegAllocCertPacket {
        num_ops: 0,
        ops: [z; MAX_RA_OPS],
        expected_final_reg0_vreg: 0,
        expected_final_reg0_lanes: 0,
        par_dst: [0; MAX_PAR_MOVES],
        par_src: [0; MAX_PAR_MOVES],
        par_len: 0,
        par_scratch: 0,
        par_slice: 0,
    }
}

fn pos_bundle_1() -> (BtlSuperblockCert, RegAllocCertPacket) {
    // x + x == x << 1 and aligned (slot1 | 1) or_disjoint -> add nuw, plus redundant freeze drop
    let mut b = empty_btl();
    b.src_len = 6;
    b.src_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: FLAG_NON_POISON_KNOWN, lhs: 0, rhs: 0, imm: 1 };
    b.src_nodes[1] = BtlNode { op: BtlOp::Freeze as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    b.src_nodes[2] = BtlNode { op: BtlOp::Add64 as u8, flags: 0, lhs: 1, rhs: 1, imm: 0 };
    b.src_nodes[3] = BtlNode { op: BtlOp::Const64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 1 };
    b.src_nodes[4] = BtlNode { op: BtlOp::Or64 as u8, flags: FLAG_DISJOINT, lhs: 0, rhs: 3, imm: 0 };
    b.src_nodes[5] = BtlNode { op: BtlOp::Add64 as u8, flags: 0, lhs: 2, rhs: 4, imm: 0 };
    b.src_exits[0] = 5;

    b.tgt_len = 6;
    b.tgt_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: FLAG_NON_POISON_KNOWN, lhs: 0, rhs: 0, imm: 1 };
    b.tgt_nodes[1] = BtlNode { op: BtlOp::Const64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 1 };
    b.tgt_nodes[2] = BtlNode { op: BtlOp::Shl64 as u8, flags: 0, lhs: 0, rhs: 1, imm: 0 };
    b.tgt_nodes[3] = BtlNode { op: BtlOp::Const64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 1 };
    b.tgt_nodes[4] = BtlNode { op: BtlOp::Add64 as u8, flags: FLAG_NUW, lhs: 0, rhs: 3, imm: 0 };
    b.tgt_nodes[5] = BtlNode { op: BtlOp::Add64 as u8, flags: 0, lhs: 2, rhs: 4, imm: 0 };
    b.tgt_exits[0] = 5;

    let mut r = empty_ra();
    r.num_ops = 7;
    r.ops[0] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 1, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Ymm256 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 10, live_upper_mask: 0 };
    r.ops[1] = RaOp { kind: RaOpKind::Spill as u8, dst_is_slot: 1, dst_idx: 0, src_is_slot: 0, src_idx: 1, slice: SubRegSlice::Ymm256 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 0, live_upper_mask: 0 };
    r.ops[2] = RaOp { kind: RaOpKind::Reload as u8, dst_is_slot: 0, dst_idx: 2, src_is_slot: 1, src_idx: 0, slice: SubRegSlice::Ymm256 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 0, live_upper_mask: 0 };
    r.ops[3] = RaOp { kind: RaOpKind::Move as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 2, slice: SubRegSlice::Xmm128 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 0, live_upper_mask: 0 };
    r.ops[4] = RaOp { kind: RaOpKind::VZeroUpper as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: 0, write_mode: 0, vreg: 0, live_upper_mask: 0 };
    r.ops[5] = RaOp { kind: RaOpKind::AbiCallOrRet as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: 0, write_mode: 0, vreg: 0, live_upper_mask: 0 };
    r.ops[6] = RaOp { kind: RaOpKind::Remat as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Full64 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 10, live_upper_mask: 0 };
    r.expected_final_reg0_vreg = 10;
    r.expected_final_reg0_lanes = LANE_ALL_64;
    (b, r)
}

fn pos_bundle_2() -> (BtlSuperblockCert, RegAllocCertPacket) {
    // Farkas-certified guard elimination: (1)*x + (0) <= 63 AND (-1)*x + (0) <= -64 -> 0 <= -1
    let mut b = empty_btl();
    b.src_len = 3;
    b.src_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: FLAG_NON_POISON_KNOWN, lhs: 0, rhs: 0, imm: 2 };
    b.src_nodes[1] = BtlNode { op: BtlOp::Const64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 64 };
    b.src_nodes[2] = BtlNode { op: BtlOp::Add64 as u8, flags: FLAG_NUW, lhs: 0, rhs: 1, imm: 0 };
    b.src_exits[0] = 2;
    b.tgt_len = 3;
    b.tgt_nodes = b.src_nodes;
    b.tgt_nodes[2].op = BtlOp::Or64 as u8;
    b.tgt_nodes[2].flags = FLAG_DISJOINT;
    b.tgt_exits[0] = 2;
    b.src_guard_removed_flag = 1;
    b.num_farkas = 2;
    b.farkas_rows[0] = FarkasRow { ax: 1, ac: 0, bound: 63, lambda: 1 };
    b.farkas_rows[1] = FarkasRow { ax: -1, ac: 0, bound: -64, lambda: 1 };

    let mut r = empty_ra();
    r.num_ops = 4;
    r.ops[0] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Full64 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 11, live_upper_mask: 0 };
    r.ops[1] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 1, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Full64 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 22, live_upper_mask: 0 };
    r.ops[2] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 2, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Full64 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 33, live_upper_mask: 0 };
    r.ops[3] = RaOp { kind: RaOpKind::ParMoveSwap as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: 0, write_mode: 0, vreg: 0, live_upper_mask: 0 };
    r.par_len = 3;
    r.par_dst[0] = 0; r.par_src[0] = 1;
    r.par_dst[1] = 1; r.par_src[1] = 2;
    r.par_dst[2] = 2; r.par_src[2] = 0;
    r.par_scratch = 4;
    r.par_slice = SubRegSlice::Full64 as u8;
    r.expected_final_reg0_vreg = 22;
    r.expected_final_reg0_lanes = LANE_ALL_64;
    (b, r)
}

fn pos_bundle_3() -> (BtlSuperblockCert, RegAllocCertPacket) {
    // Sub(x, x) -> 0 and SSE Xmm128 reload preserving live ymm_hi
    let mut b = empty_btl();
    b.src_len = 2;
    b.src_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: FLAG_NON_POISON_KNOWN, lhs: 0, rhs: 0, imm: 0 };
    b.src_nodes[1] = BtlNode { op: BtlOp::Sub64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    b.src_exits[0] = 1;
    b.tgt_len = 1;
    b.tgt_nodes[0] = BtlNode { op: BtlOp::Const64 as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    b.tgt_exits[0] = 0;

    let mut r = empty_ra();
    r.num_ops = 5;
    r.ops[0] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Ymm256 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 50, live_upper_mask: 0 };
    r.ops[1] = RaOp { kind: RaOpKind::SeedReg as u8, dst_is_slot: 0, dst_idx: 1, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Xmm128 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 51, live_upper_mask: 0 };
    r.ops[2] = RaOp { kind: RaOpKind::Spill as u8, dst_is_slot: 1, dst_idx: 0, src_is_slot: 0, src_idx: 1, slice: SubRegSlice::Xmm128 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 0, live_upper_mask: 0 };
    r.ops[3] = RaOp { kind: RaOpKind::Reload as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 1, src_idx: 0, slice: SubRegSlice::Xmm128 as u8, write_mode: WriteMode::PreserveUpper as u8, vreg: 0, live_upper_mask: LANE_YMM_HI };
    r.ops[4] = RaOp { kind: RaOpKind::VZeroUpper as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: 0, write_mode: 0, vreg: 0, live_upper_mask: 0 };
    r.expected_final_reg0_vreg = 51;
    r.expected_final_reg0_lanes = LANE_ALL_128;
    (b, r)
}

fn negative_cases() -> [(BtlSuperblockCert, RegAllocCertPacket, u32); 12] {
    let (p1b, p1r) = pos_bundle_1();
    let (p2b, p2r) = pos_bundle_2();
    let (p3b, p3r) = pos_bundle_3();

    // N1: overlapping `or disjoint`
    let mut n1b = p1b;
    n1b.tgt_nodes[0].imm = 0;
    n1b.tgt_nodes[4].op = BtlOp::Or64 as u8;
    n1b.tgt_nodes[4].flags = FLAG_DISJOINT;

    // N2: unproved `add nuw`
    let mut n2b = p1b;
    n2b.tgt_nodes[0].imm = 0;
    n2b.tgt_nodes[4].op = BtlOp::Add64 as u8;
    n2b.tgt_nodes[4].flags = FLAG_NUW;

    // N3: duplicated `freeze` on potentially-poison node
    let mut n3b = empty_btl();
    n3b.src_len = 3;
    n3b.src_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n3b.src_nodes[1] = BtlNode { op: BtlOp::Freeze as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n3b.src_nodes[2] = BtlNode { op: BtlOp::Xor64 as u8, flags: 0, lhs: 1, rhs: 1, imm: 0 };
    n3b.src_exits[0] = 2;
    n3b.tgt_len = 4;
    n3b.tgt_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n3b.tgt_nodes[1] = BtlNode { op: BtlOp::Freeze as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n3b.tgt_nodes[2] = BtlNode { op: BtlOp::Freeze as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n3b.tgt_nodes[3] = BtlNode { op: BtlOp::Xor64 as u8, flags: 0, lhs: 1, rhs: 2, imm: 0 };
    n3b.tgt_exits[0] = 3;

    // N4: Farkas sum_ax != 0
    let mut n4b = p2b;
    n4b.farkas_rows[0].lambda = 2;

    // N5: Farkas sum_bound == 0 (not <= -1)
    let mut n5b = p2b;
    n5b.farkas_rows[0].bound = 64;

    // N6: Target drops freeze on potentially-poison input
    let mut n6b = empty_btl();
    n6b.src_len = 2;
    n6b.src_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n6b.src_nodes[1] = BtlNode { op: BtlOp::Freeze as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n6b.src_exits[0] = 1;
    n6b.tgt_len = 1;
    n6b.tgt_nodes[0] = BtlNode { op: BtlOp::Input as u8, flags: 0, lhs: 0, rhs: 0, imm: 0 };
    n6b.tgt_exits[0] = 0;

    // N7: Exit mismatch
    let mut n7b = p1b;
    n7b.tgt_nodes[5].op = BtlOp::Sub64 as u8;

    // N8: Unseeded source after kill (regalloc2 bug check)
    let mut n8r = p1r;
    n8r.ops[2] = RaOp { kind: RaOpKind::Reload as u8, dst_is_slot: 0, dst_idx: 2, src_is_slot: 1, src_idx: 3, slice: SubRegSlice::Ymm256 as u8, write_mode: WriteMode::ZeroExtend256 as u8, vreg: 0, live_upper_mask: 0 };

    // N9: Lo32 ZeroExtend64 remat clobbering live hi32
    let mut n9r = empty_ra();
    n9r.num_ops = 1;
    n9r.ops[0] = RaOp { kind: RaOpKind::Remat as u8, dst_is_slot: 0, dst_idx: 0, src_is_slot: 0, src_idx: 0, slice: SubRegSlice::Lo32 as u8, write_mode: WriteMode::ZeroExtend64 as u8, vreg: 99, live_upper_mask: LANE_HI32 };

    // N10: VEX-128 reload clobbering live ymm_hi
    let mut n10r = p3r;
    n10r.ops[3].write_mode = WriteMode::ZeroExtend256 as u8;

    // N11: AbiCallOrRet with dirty YMM (missing vzeroupper)
    let mut n11r = p1r;
    n11r.ops[4] = RaOp { kind: RaOpKind::DirtyYmm as u8, dst_is_slot: 0, dst_idx: 3, src_is_slot: 0, src_idx: 0, slice: 0, write_mode: 0, vreg: 0, live_upper_mask: 0 };

    // N12: ParMoveSwap scratch clobber
    let mut n12r = p2r;
    n12r.par_scratch = 1;

    [
        (n1b, p1r, ERR_DISJOINT_OVERLAP),
        (n2b, p1r, ERR_NUW_UNPROVED),
        (n3b, p1r, ERR_FREEZE_DUPLICATED),
        (n4b, p2r, ERR_FARKAS_FAILED),
        (n5b, p2r, ERR_FARKAS_FAILED),
        (n6b, p1r, ERR_EXIT_MISMATCH),
        (n7b, p1r, ERR_EXIT_MISMATCH),
        (p1b, n8r, ERR_UNSEEDED_SRC),
        (p1b, n9r, ERR_CLOBBER_HI_LANE),
        (p3b, n10r, ERR_CLOBBER_HI_LANE),
        (p1b, n11r, ERR_DIRTY_YMM_AT_EXIT),
        (p2b, n12r, ERR_PARMOVE_CLOBBER),
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("verify");

    let p1 = pos_bundle_1();
    let p2 = pos_bundle_2();
    let p3 = pos_bundle_3();
    let negs = negative_cases();

    if mode == "once" {
        let s1 = seed_core::verify_bundle_seed(black_box(&p1.0), black_box(&p1.1));
        assert_eq!(s1.status, STATUS_OK);
        println!("ONCE_OK {}", s1.digest);
        return;
    }

    if mode == "verify" {
        for (idx, p) in [p1, p2, p3].iter().enumerate() {
            let s = seed_core::verify_bundle_seed(&p.0, &p.1);
            let i = idiomatic_safe::verify_bundle_idiomatic(&p.0, &p.1);
            assert_eq!(s.status, STATUS_OK, "pos {} seed failed", idx);
            assert_eq!(s.status, i.status, "pos {} status mismatch", idx);
            assert_eq!(s.checked_nodes, i.checked_nodes, "pos {} checked_nodes mismatch", idx);
            assert_eq!(s.checked_ra_ops, i.checked_ra_ops, "pos {} checked_ra_ops mismatch", idx);
            assert_eq!(s.digest, i.digest, "pos {} digest mismatch", idx);
        }
        for (idx, (b, r, exp)) in negs.iter().enumerate() {
            let s = seed_core::verify_bundle_seed(b, r);
            let i = idiomatic_safe::verify_bundle_idiomatic(b, r);
            assert_eq!(s.status, *exp, "neg {} unexpected seed rc {}", idx, s.status);
            assert_eq!(s.status, i.status, "neg {} status mismatch", idx);
            assert_eq!(s.checked_nodes, i.checked_nodes, "neg {} checked_nodes mismatch", idx);
            assert_eq!(s.checked_ra_ops, i.checked_ra_ops, "neg {} checked_ra_ops mismatch", idx);
            assert_eq!(s.digest, i.digest, "neg {} digest mismatch", idx);
        }
        println!("VERIFY_ALL_OK pos=3 neg=12");
        return;
    }

    let iters: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let mut acc_seed: u64 = 0;
    let t0 = Instant::now();
    for _ in 0..iters {
        let s1 = seed_core::verify_bundle_seed(black_box(&p1.0), black_box(&p1.1));
        let s2 = seed_core::verify_bundle_seed(black_box(&p2.0), black_box(&p2.1));
        let s3 = seed_core::verify_bundle_seed(black_box(&p3.0), black_box(&p3.1));
        acc_seed ^= s1.digest ^ s2.digest ^ s3.digest;
    }
    let dt_seed_ns = t0.elapsed().as_nanos() as u64;

    let mut acc_idio: u64 = 0;
    let t1 = Instant::now();
    for _ in 0..iters {
        let i1 = idiomatic_safe::verify_bundle_idiomatic(black_box(&p1.0), black_box(&p1.1));
        let i2 = idiomatic_safe::verify_bundle_idiomatic(black_box(&p2.0), black_box(&p2.1));
        let i3 = idiomatic_safe::verify_bundle_idiomatic(black_box(&p3.0), black_box(&p3.1));
        acc_idio ^= i1.digest ^ i2.digest ^ i3.digest;
    }
    let dt_idio_ns = t1.elapsed().as_nanos() as u64;
    assert_eq!(acc_seed, acc_idio);
    let total_steps = (p1.0.src_len + p1.0.tgt_len + p1.1.num_ops
        + p2.0.src_len + p2.0.tgt_len + p2.1.num_ops
        + p3.0.src_len + p3.0.tgt_len + p3.1.num_ops) * iters;
    println!(
        "{{\"iters\":{},\"bundles\":{},\"total_steps\":{},\"seed_ns\":{},\"idiomatic_ns\":{},\"digest\":{}}}",
        iters,
        iters * 3,
        total_steps,
        dt_seed_ns,
        dt_idio_ns,
        acc_seed
    );
}
'''


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-lean", action="store_true", help="Run rustc census and benchmarks only")
    args = parser.parse_args()

    if BUILD_SCRATCH.exists():
        shutil.rmtree(BUILD_SCRATCH)
    BUILD_SCRATCH.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    home = Path.home()
    env["PATH"] = f"{home / '.cargo/bin'}:{home / '.elan/bin'}:{home / '.local/bin'}:{env.get('PATH', '')}"

    rustc_ver = subprocess.run(["rustc", "--version", "-v"], env=env, capture_output=True, text=True, check=True).stdout.strip()
    lean_ver = subprocess.run([str(home / ".local/bin/anneal-lean-run"), "lean", "--version"], env=env, capture_output=True, text=True, check=True).stdout.strip()

    configs = [
        ("o0_abort", ["-C", "opt-level=0", "-C", "panic=abort"]),
        ("o3_abort", ["-C", "opt-level=3", "-C", "panic=abort"]),
        ("o0_unwind", ["-C", "opt-level=0", "-C", "panic=unwind"]),
        ("o3_unwind", ["-C", "opt-level=3", "-C", "panic=unwind"]),
    ]

    compile_results: dict[str, Any] = {}
    mir_censuses: dict[str, Any] = {}
    post_cleanup_hashes: dict[str, str] = {}
    opt_mir_hashes: dict[str, str] = {}

    for cname, flags in configs:
        cdir = BUILD_SCRATCH / cname
        mir_dir = cdir / "dump_mir"
        out_dir = cdir / "out"
        mir_dir.mkdir(parents=True, exist_ok=True)
        out_dir.mkdir(parents=True, exist_ok=True)

        cmd = [
            "rustc",
            "--edition=2024",
            "--crate-type=rlib",
            "--crate-name=vrustc_certcheck_seed",
            *flags,
            "-D",
            "warnings",
            "--emit=mir,llvm-ir,obj,link",
            "-Z",
            "dump-mir=runtime-post-cleanup",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--out-dir",
            str(out_dir),
            str(CRATE_RS),
        ]
        rc, out, err, dt, rss_kb = run_cmd(cmd, cwd=BUILD_SCRATCH, env=env)
        if rc != 0:
            raise RuntimeError(f"rustc failed for {cname}: {err}")

        obj_file = out_dir / "vrustc_certcheck_seed.o"
        rlib_file = out_dir / "libvrustc_certcheck_seed.rlib"
        opt_mir_file = out_dir / "vrustc_certcheck_seed.mir"
        ll_file = out_dir / "vrustc_certcheck_seed.ll"

        size_proc = subprocess.run(["size", str(obj_file)], capture_output=True, text=True, check=True)
        size_vals = size_proc.stdout.strip().splitlines()[-1].split()
        text_bytes = int(size_vals[0])
        data_bytes = int(size_vals[1])
        bss_bytes = int(size_vals[2])

        compile_results[cname] = {
            "rustc_wall_sec": round(dt, 4),
            "rustc_peak_rss_mb": round(rss_kb / 1024.0, 2),
            "obj_bytes": obj_file.stat().st_size,
            "rlib_bytes": rlib_file.stat().st_size,
            "ll_bytes": ll_file.stat().st_size,
            "opt_mir_bytes": opt_mir_file.stat().st_size,
            "text_bytes": text_bytes,
            "data_bytes": data_bytes,
            "bss_bytes": bss_bytes,
        }
        post_cleanup_hashes[cname] = hash_runtime_post_cleanup(mir_dir)
        opt_mir_hashes[cname] = sha256_file(opt_mir_file)

        if cname in ("o0_abort", "o0_unwind"):
            body_records = parse_single_fn_dump_dir(mir_dir)
            mir_censuses[f"{cname}_runtime_post_cleanup"] = aggregate_census(body_records)

    # Also measure symbol-level .text size breakdown inside o0_abort and o3_abort
    sym_sizes: dict[str, dict[str, int]] = {}
    for cname in ("o0_abort", "o3_abort"):
        obj_file = BUILD_SCRATCH / cname / "out" / "vrustc_certcheck_seed.o"
        nm_proc = subprocess.run(["nm", "--size-sort", "-C", str(obj_file)], capture_output=True, text=True, check=True)
        totals = {"seed_core": 0, "idiomatic_safe": 0, "other": 0}
        for line in nm_proc.stdout.splitlines():
            parts = line.split(None, 2)
            if len(parts) < 3 or parts[1] not in ("t", "T"):
                continue
            sz = int(parts[0], 16)
            sym = parts[2]
            if "seed_core::" in sym:
                totals["seed_core"] += sz
            elif "idiomatic_safe::" in sym:
                totals["idiomatic_safe"] += sz
            else:
                totals["other"] += sz
        sym_sizes[cname] = totals

    # Compile and execute real driver_o0 and driver_o3 binaries (identical source & flags except -C opt-level)
    driver_rs = BUILD_SCRATCH / "bench_driver.rs"
    driver_rs.write_text(BENCH_DRIVER_RS)
    bench_results: dict[str, Any] = {}
    for cname, opt_flag in (("driver_o0", "-Copt-level=0"), ("driver_o3", "-Copt-level=3")):
        rlib_cname = "o0_abort" if cname == "driver_o0" else "o3_abort"
        rlib_path = BUILD_SCRATCH / rlib_cname / "out" / "libvrustc_certcheck_seed.rlib"
        bin_path = BUILD_SCRATCH / cname
        rc, _, err, dt_c, rss_c = run_cmd(
            [
                "rustc",
                "--edition=2024",
                opt_flag,
                "-C",
                "panic=abort",
                "--extern",
                f"vrustc_certcheck_seed={rlib_path}",
                "-o",
                str(bin_path),
                str(driver_rs),
            ],
            cwd=BUILD_SCRATCH,
            env=env,
        )
        if rc != 0:
            raise RuntimeError(f"driver build failed {cname}: {err}")

        # Verify positive (3) and negative (12) equivalence
        rc_v, out_v, err_v, _, _ = run_cmd([str(bin_path), "verify"], cwd=BUILD_SCRATCH, env=env)
        if rc_v != 0 or "VERIFY_ALL_OK pos=3 neg=12" not in out_v:
            raise RuntimeError(f"verify failed {cname}: {out_v} {err_v}")

        # Cold-start process latency (15 trials)
        cold_ms = []
        for _ in range(15):
            t0 = time.perf_counter()
            p = subprocess.run([str(bin_path), "once"], capture_output=True, text=True, check=True)
            cold_ms.append((time.perf_counter() - t0) * 1000.0)
            assert "ONCE_OK" in p.stdout

        # Warm batch throughput (9 trials x 10,000 iters = 30,000 certs per trial)
        seed_ns_per_bundle = []
        idio_ns_per_bundle = []
        seed_steps_per_sec = []
        idio_steps_per_sec = []
        rss_vals = []
        for _ in range(9):
            rc_b, out_b, _, _, rss_b = run_cmd([str(bin_path), "bench", "10000"], cwd=BUILD_SCRATCH, env=env)
            assert rc_b == 0
            rec = json.loads(out_b.strip())
            seed_ns_per_bundle.append(rec["seed_ns"] / rec["bundles"])
            idio_ns_per_bundle.append(rec["idiomatic_ns"] / rec["bundles"])
            seed_steps_per_sec.append(rec["total_steps"] / (rec["seed_ns"] / 1e9))
            idio_steps_per_sec.append(rec["total_steps"] / (rec["idiomatic_ns"] / 1e9))
            rss_vals.append(rss_b / 1024.0)

        bench_results[cname] = {
            "bin_bytes": bin_path.stat().st_size,
            "driver_compile_sec": round(dt_c, 4),
            "verify_pos3_neg12_ok": True,
            "cold_start_median_ms": round(statistics.median(cold_ms), 3),
            "cold_start_min_ms": round(min(cold_ms), 3),
            "warm_peak_rss_mb": round(statistics.median(rss_vals), 2),
            "seed_core_ns_per_bundle_median": round(statistics.median(seed_ns_per_bundle), 2),
            "idiomatic_ns_per_bundle_median": round(statistics.median(idio_ns_per_bundle), 2),
            "seed_core_steps_per_sec_median": round(statistics.median(seed_steps_per_sec), 0),
            "idiomatic_steps_per_sec_median": round(statistics.median(idio_steps_per_sec), 0),
        }

    # Measure Lean v4.34.1 kernel checking of MirToMiniMachO0Seed.lean via anneal-lean-run
    if args.skip_lean:
        lean_out, lean_dt, lean_rss = "SKIPPED", 0.0, 0
    else:
        lean_cmd = [
            str(home / ".local/bin/anneal-lean-run"),
            "--mode",
            "file",
            "--",
            "lean",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            str(LEAN_FILE),
        ]
        lean_rc, lean_out, lean_err, lean_dt, lean_rss = run_cmd(lean_cmd, cwd=HERE, env=env)
        if lean_rc != 0:
            raise RuntimeError(f"Lean verification failed: {lean_out}\n{lean_err}")

    lean_text = LEAN_FILE.read_text()
    lean_theorems = len(re.findall(r"^\s*theorem\s+", lean_text, re.MULTILINE))
    lean_defs = len(re.findall(r"^\s*(?:def|inductive|structure)\s+", lean_text, re.MULTILINE))
    lean_lines = len(lean_text.splitlines())

    o0_seed_ns = bench_results["driver_o0"]["seed_core_ns_per_bundle_median"]
    o3_seed_ns = bench_results["driver_o3"]["seed_core_ns_per_bundle_median"]
    o0_idio_ns = bench_results["driver_o0"]["idiomatic_ns_per_bundle_median"]
    o3_idio_ns = bench_results["driver_o3"]["idiomatic_ns_per_bundle_median"]

    report = {
        "rustc_version": rustc_ver,
        "lean_version": lean_ver,
        "crate_source": CRATE_RS.name,
        "crate_sha256": sha256_file(CRATE_RS),
        "crate_loc": len(CRATE_RS.read_text().splitlines()),
        "lean_source": LEAN_FILE.name,
        "lean_sha256": sha256_file(LEAN_FILE),
        "lean_loc": lean_lines,
        "lean_theorems": lean_theorems,
        "lean_defs_types": lean_defs,
        "lean_kernel_check_sec": round(lean_dt, 3),
        "lean_kernel_peak_rss_mb": round(lean_rss / 1024.0, 2),
        "lean_kernel_axioms_stdout": lean_out.strip(),
        "post_cleanup_mir_sha256": post_cleanup_hashes,
        "post_cleanup_sha256_invariant_o0_vs_o3_abort": (
            post_cleanup_hashes["o0_abort"] == post_cleanup_hashes["o3_abort"]
        ),
        "opt_mir_sha256_diverges_o0_vs_o3_abort": (
            opt_mir_hashes["o0_abort"] != opt_mir_hashes["o3_abort"]
        ),
        "compile_metrics": compile_results,
        "symbol_text_bytes": sym_sizes,
        "mir_censuses": mir_censuses,
        "execution_benchmarks": bench_results,
        "o0_over_o3_ratios": {
            "seed_core_slowdown": round(o0_seed_ns / o3_seed_ns, 2),
            "idiomatic_slowdown": round(o0_idio_ns / o3_idio_ns, 2),
            "seed_core_vs_idiomatic_at_o0": round(o0_seed_ns / o0_idio_ns, 2),
            "seed_core_vs_idiomatic_at_o3": round(o3_seed_ns / o3_idio_ns, 2),
        },
    }
    OUT_JSON.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {OUT_JSON} (Lean={lean_dt:.2f}s, O0/O3 seed={report['o0_over_o3_ratios']['seed_core_slowdown']}x)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
