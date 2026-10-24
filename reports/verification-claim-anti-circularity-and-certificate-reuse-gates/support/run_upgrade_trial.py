#!/usr/bin/env python3
"""Study P3 / Milestone R6: Execution-based 4-toolchain upgrade oracle and bounded Charon 0.1.174 -> 0.1.210 study."""

import copy
import hashlib
import json
import os
import re
import resource
import subprocess
import time

BASE_DIR = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/compiler-upgrade-trial"
ART_DIR = os.path.join(BASE_DIR, "artifacts")
PORTABLE_DRIVER_SRC = os.path.join(BASE_DIR, "direct_mir_driver_portable.rs")

SUBJECTS = [
    (
        "cleanup_subject",
        "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/cleanup_subject.rs",
    ),
    (
        "place_mention_probe",
        "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/place_mention_probe.rs",
    ),
    (
        "zerocopy_layout_holdout",
        "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/zerocopy_layout_holdout.rs",
    ),
    (
        "loop_prefix_probe",
        "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/loop_prefix_probe.rs",
    ),
    (
        "dep_layout_core",
        "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/cargo-workspace-capture/workspace/dep_layout_core/src/lib.rs",
    ),
]

TOOLCHAINS = [
    {
        "id": "nightly_1_95_2026_02_06",
        "version": "1.95.0-nightly (efc9e1b50 2026-02-06)",
        "root": "/usr/local/google/home/joshlf/.anneal/toolchain/x86_64-unknown-linux-gnu-0191de6c9fa5/rust",
        "cfg_flags": [],
        "mir_use_arity": 1,
        "has_retag_stmt": True,
        "drop_glue_api": "Instance::resolve_drop_in_place",
        "derive_eq_helper_name": "assert_receiver_is_total_eq",
    },
    {
        "id": "nightly_1_96_2026_04_10",
        "version": "1.96.0-nightly (02c7f9bec 2026-04-10)",
        "root": "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu",
        "cfg_flags": [],
        "mir_use_arity": 1,
        "has_retag_stmt": True,
        "drop_glue_api": "Instance::resolve_drop_in_place",
        "derive_eq_helper_name": "assert_fields_are_eq",
    },
    {
        "id": "nightly_1_97_2026_04_11",
        "version": "1.97.0-nightly (bf4fbfb7a 2026-04-11)",
        "root": "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-04-12-x86_64-unknown-linux-gnu",
        "cfg_flags": [],
        "mir_use_arity": 1,
        "has_retag_stmt": True,
        "drop_glue_api": "Instance::resolve_drop_in_place",
        "derive_eq_helper_name": "assert_fields_are_eq",
    },
    {
        "id": "nightly_1_98_2026_05_30",
        "version": "1.98.0-nightly (f8a08b688 2026-05-30)",
        "root": "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61/rust",
        "cfg_flags": ["--cfg", "rustc_1_98"],
        "mir_use_arity": 2,
        "has_retag_stmt": False,
        "drop_glue_api": "Instance::resolve_drop_glue",
        "derive_eq_helper_name": "assert_fields_are_eq",
    },
]

CHARON_195_BIN = "/usr/local/google/home/joshlf/.anneal/toolchain/x86_64-unknown-linux-gnu-0191de6c9fa5/charon"
CHARON_195_DRIVER_BIN = "/usr/local/google/home/joshlf/.anneal/toolchain/x86_64-unknown-linux-gnu-0191de6c9fa5/charon-driver"
CHARON_198_BIN = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61/aeneas/bin/charon"
CHARON_198_DRIVER_BIN = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61/aeneas/bin/charon-driver"
CHARON_GIT_DB = "/usr/local/google/home/joshlf/.cargo/git/db/charon-e8f73e8d381056c2"

U32_MOD = 1 << 32
USIZE_MOD = 1 << 64
USIZE_MAX = USIZE_MOD - 1

DECLARED_INTRINSICS = {20, 21, 23, 25, 26, 27, 28, 29, 30, 31, 32, 37, 38, 39, 40, 41, 42}


def sha256_file(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_amir_v3_package(data: bytes) -> dict:
    """Full Boundary 1 + Boundary 2a + Boundary 2b .amir v3 wire parser (mirrors SubstantiveMirByteParser.lean)."""
    b = list(data)
    if any(x < 0 or x > 255 for x in b):
        return {"accepted": False, "reason": "non_physical_byte"}
    if len(b) < 10 or b[:4] != [0x41, 0x4D, 0x49, 0x52] or b[4] != 3:
        return {"accepted": False, "reason": "malformed_header"}
    def_phase = b[5]
    flags = b[6]
    fp_hi = b[7]
    fp_lo = b[8]
    body_count = b[9]
    if def_phase not in (1, 2, 3, 4) or flags not in (1, 3, 9, 11) or body_count == 0 or body_count > 64:
        return {"accepted": False, "reason": "invalid_header_flags_or_body_count"}

    pos = 10
    bodies = []
    for _ in range(body_count):
        if pos + 7 > len(b):
            return {"accepted": False, "reason": "truncated_body_header"}
        body_id, sym_id, orig_kind, phase_b, local_cnt, arg_cnt, blk_cnt = b[pos : pos + 7]
        pos += 7
        if local_cnt == 0 or local_cnt > 64 or arg_cnt >= local_cnt or blk_cnt == 0 or blk_cnt > 32:
            return {"accepted": False, "reason": "ill_formed_body_counts"}
        if pos + local_cnt > len(b):
            return {"accepted": False, "reason": "truncated_local_types"}
        local_types = b[pos : pos + local_cnt]
        pos += local_cnt
        if any(t < 1 or t > 23 for t in local_types):
            return {"accepted": False, "reason": "invalid_type_tag"}

        blocks = []
        for _ in range(blk_cnt):
            if pos + 2 > len(b):
                return {"accepted": False, "reason": "truncated_block_header"}
            is_cleanup, stmt_cnt = b[pos], b[pos + 1]
            pos += 2
            if is_cleanup not in (0, 1) or stmt_cnt > 64:
                return {"accepted": False, "reason": "invalid_block_header"}
            stmts = []
            for _ in range(stmt_cnt):
                if pos >= len(b):
                    return {"accepted": False, "reason": "truncated_stmt"}
                op = b[pos]
                pos += 1
                if op in (0x20, 0x21):
                    l_idx = b[pos]
                    pos += 1
                    if l_idx >= local_cnt:
                        return {"accepted": False, "reason": "local_out_of_bounds"}
                    stmts.append({"op": op, "kind": "StorageLive" if op == 0x20 else "StorageDead", "local": l_idx})
                elif op in (0x10, 0x11):
                    d_l, d_p, s0, s1 = b[pos : pos + 4]
                    pos += 4
                    if d_l >= local_cnt:
                        return {"accepted": False, "reason": "dst_out_of_bounds"}
                    stmts.append({
                        "op": op,
                        "kind": "AssignUseRetagYes" if op == 0x11 else "AssignUseNoRetag",
                        "dst": (d_l, d_p),
                        "src": (s0, s1),
                    })
                elif op in (0x12, 0x14):
                    d_l, d_p, s_l, s_p = b[pos : pos + 4]
                    pos += 4
                    stmts.append({"op": op, "kind": "CopyForDeref" if op == 0x12 else "Discriminant", "dst": (d_l, d_p), "src": (s_l, s_p)})
                elif op == 0x13:
                    d_l, d_p, rk, s_l, s_p = b[pos : pos + 5]
                    pos += 5
                    stmts.append({"op": op, "kind": "RefOrPtr", "dst": (d_l, d_p), "rk": rk, "src": (s_l, s_p)})
                elif op == 0x15:
                    d_l, d_p, bop, l0, l1, r0, r1 = b[pos : pos + 7]
                    pos += 7
                    stmts.append({"op": op, "kind": "BinOp", "dst": (d_l, d_p), "bop": bop, "lhs": (l0, l1), "rhs": (r0, r1)})
                elif op == 0x16:
                    d_l, d_p, uop, s0, s1 = b[pos : pos + 5]
                    pos += 5
                    stmts.append({"op": op, "kind": "UnOp", "dst": (d_l, d_p), "uop": uop, "src": (s0, s1)})
                elif op == 0x17:
                    d_l, d_p, k = b[pos : pos + 3]
                    pos += 3
                    stmts.append({"op": op, "kind": "Agg0", "dst": (d_l, d_p), "agg_kind": k})
                elif op == 0x18:
                    d_l, d_p, k, a0, a1 = b[pos : pos + 5]
                    pos += 5
                    stmts.append({"op": op, "kind": "Agg1", "dst": (d_l, d_p), "agg_kind": k, "f0": (a0, a1)})
                elif op == 0x19:
                    d_l, d_p, k, a0, a1, b0, b1 = b[pos : pos + 7]
                    pos += 7
                    stmts.append({"op": op, "kind": "Agg2", "dst": (d_l, d_p), "agg_kind": k, "f0": (a0, a1), "f1": (b0, b1)})
                elif op == 0x1A:
                    d_l, d_p, k, a0, a1, b0, b1, c0, c1 = b[pos : pos + 9]
                    pos += 9
                    stmts.append({"op": op, "kind": "Agg3", "dst": (d_l, d_p), "agg_kind": k, "f0": (a0, a1), "f1": (b0, b1), "f2": (c0, c1)})
                elif op == 0x22:
                    stmts.append({"op": op, "kind": "Nop"})
                elif op == 0x30:
                    s_l, s_p = b[pos : pos + 2]
                    pos += 2
                    stmts.append({"op": op, "kind": "PlaceMention", "src": (s_l, s_p)})
                elif op == 0x31:
                    rk, s_l, s_p = b[pos : pos + 3]
                    pos += 3
                    stmts.append({"op": op, "kind": "RetagStmt", "rk": rk, "src": (s_l, s_p)})
                else:
                    return {"accepted": False, "reason": f"unknown_stmt_opcode_{hex(op)}"}

            if pos >= len(b):
                return {"accepted": False, "reason": "truncated_term"}
            top = b[pos]
            pos += 1
            if top in (0x40, 0x41, 0x43):
                term = {"op": top, "kind": {0x40: "Return", 0x41: "UnwindResume", 0x43: "Unreachable"}[top]}
            elif top == 0x42:
                r = b[pos]
                pos += 1
                term = {"op": top, "kind": "UnwindTerminate", "reason": r}
            elif top == 0x44:
                t = b[pos]
                pos += 1
                if t >= blk_cnt:
                    return {"accepted": False, "reason": "goto_target_oob"}
                term = {"op": top, "kind": "Goto", "target": t}
            elif top == 0x45:
                d0, d1, v0, t0, oth = b[pos : pos + 5]
                pos += 5
                term = {"op": top, "kind": "SwitchInt1", "discr": (d0, d1), "val0": v0, "target0": t0, "otherwise": oth}
            elif top == 0x46:
                d0, d1, v0, t0, v1, t1, oth = b[pos : pos + 7]
                pos += 7
                term = {"op": top, "kind": "SwitchInt2", "discr": (d0, d1), "val0": v0, "target0": t0, "val1": v1, "target1": t1, "otherwise": oth}
            elif top == 0x47:
                p_l, p_p, g, t, uw = b[pos : pos + 5]
                pos += 5
                term = {"op": top, "kind": "Drop", "place": (p_l, p_p), "glue_sym": g, "target": t, "unwind": uw}
            elif top == 0x48:
                c0, c1, exp, t, uw = b[pos : pos + 5]
                pos += 5
                term = {"op": top, "kind": "Assert", "cond": (c0, c1), "expected": exp, "target": t, "unwind": uw}
            elif top in (0x49, 0x4A, 0x4B, 0x4C, 0x4D):
                arity = top - 0x49
                c, d_l, d_p, t_b, uw_b = b[pos : pos + 5]
                pos += 5
                args = []
                for _ in range(arity):
                    args.append((b[pos], b[pos + 1]))
                    pos += 2
                term = {"op": top, "kind": f"Call{arity}", "callee_sym": c, "dst": (d_l, d_p), "target": t_b, "unwind": uw_b, "args": args}
            else:
                return {"accepted": False, "reason": f"unknown_term_opcode_{hex(top)}"}

            blocks.append({"is_cleanup": bool(is_cleanup), "stmts": stmts, "term": term})

        bodies.append({
            "body_id": body_id,
            "sym_id": sym_id,
            "origin_kind": orig_kind,
            "phase": phase_b,
            "local_count": local_cnt,
            "arg_count": arg_cnt,
            "local_types": local_types,
            "blocks": blocks,
        })

    if pos != len(b):
        return {"accepted": False, "reason": f"trailing_bytes_{len(b) - pos}"}

    # Stage B2b: package admission closure (unique symIds + callee/drop-glue closure)
    sym_ids = [bd["sym_id"] for bd in bodies]
    if len(set(sym_ids)) != len(sym_ids):
        return {"accepted": False, "reason": "b2b_duplicate_sym_id"}
    present_syms = set(sym_ids)
    for bd in bodies:
        for blk in bd["blocks"]:
            tm = blk["term"]
            if tm["kind"] == "Drop":
                gs = tm["glue_sym"]
                if gs != 0 and gs not in present_syms:
                    return {"accepted": False, "reason": f"b2b_missing_drop_glue_{gs}"}
            elif tm["kind"].startswith("Call"):
                cs = tm["callee_sym"]
                if cs not in DECLARED_INTRINSICS and cs not in present_syms:
                    return {"accepted": False, "reason": f"b2b_missing_callee_{cs}"}

    return {
        "accepted": True,
        "version": 3,
        "fp16": [fp_hi, fp_lo],
        "body_count": body_count,
        "bodies": bodies,
    }


def run_legacy_structural_shape_check(subject_id: str, parsed_pkg: dict) -> dict:
    """Legacy structural shape checker from #61 (retained solely to contrast against decoded-AST execution in R6)."""
    if not parsed_pkg.get("accepted"):
        return {"legacy_shape_accepted": False, "reason": "boundary_1_2_rejected"}
    by_sym = {b["sym_id"]: b for b in parsed_pkg["bodies"]}
    if subject_id == "place_mention_probe":
        for sym in (6, 9, 10):
            if sym not in by_sym:
                return {"legacy_shape_accepted": False, "reason": f"missing_sym_{sym}"}
            blk0 = by_sym[sym]["blocks"][0]
            expected_src = (3, 0) if sym == 6 else (1, 4)
            if not any(s["kind"] == "PlaceMention" and s["src"] == expected_src for s in blk0["stmts"]):
                return {"legacy_shape_accepted": False, "reason": f"missing_place_mention_{sym}"}
        return {"legacy_shape_accepted": True}
    if subject_id == "cleanup_subject":
        for sym in (1, 2, 3, 4, 5, 6, 7, 8, 24):
            if sym not in by_sym:
                return {"legacy_shape_accepted": False, "reason": f"missing_sym_{sym}"}
        b4_drops = [blk["term"]["glue_sym"] for blk in by_sym[4]["blocks"] if blk["is_cleanup"] and blk["term"]["kind"] == "Drop"]
        b5_drops = [blk["term"]["glue_sym"] for blk in by_sym[5]["blocks"] if blk["is_cleanup"] and blk["term"]["kind"] == "Drop"]
        if b4_drops != [7, 7, 7, 7] or b5_drops != [7, 7]:
            return {"legacy_shape_accepted": False, "reason": "cleanup_drop_chain_mismatch"}
        return {"legacy_shape_accepted": True}
    if subject_id == "zerocopy_layout_holdout":
        for sym in (11, 12, 13, 14, 15, 16, 17, 18, 19, 44):
            if sym not in by_sym:
                return {"legacy_shape_accepted": False, "reason": f"missing_sym_{sym}"}
        if (
            len(by_sym[11]["blocks"]) != 11
            or len(by_sym[12]["blocks"]) != 23
            or len(by_sym[13]["blocks"]) != 25
            or len(by_sym[14]["blocks"]) != 14
        ):
            return {"legacy_shape_accepted": False, "reason": "block_count_mismatch"}
        return {"legacy_shape_accepted": True}
    if subject_id == "loop_prefix_probe":
        if 43 not in by_sym or len(by_sym[43]["blocks"]) != 9:
            return {"legacy_shape_accepted": False, "reason": "loop_block_count_mismatch"}
        return {"legacy_shape_accepted": True}
    if subject_id == "dep_layout_core":
        for sym in (52, 53, 54, 55):
            if sym not in by_sym:
                return {"legacy_shape_accepted": False, "reason": f"missing_sym_{sym}"}
        return {"legacy_shape_accepted": True}
    return {"legacy_shape_accepted": False, "reason": "unknown_subject"}


# ==============================================================================
# R6 Decoded-AST Small-Step Operational Interpreter (Mirrors SemanticVerticalSliceCore.lean)
# ==============================================================================

def unwrap_ref(v: tuple) -> tuple:
    return v[1] if v[0] == "ref_val" else v


def get_field_val(v: tuple, idx: int):
    u = unwrap_ref(v)
    if u[0] == "agg1":
        return u[2] if idx == 0 else None
    if u[0] == "agg2":
        return u[2] if idx == 0 else (u[3] if idx == 1 else None)
    if u[0] == "agg3":
        return u[2] if idx == 0 else (u[3] if idx == 1 else (u[4] if idx == 2 else None))
    return None


def set_field_val(v: tuple, idx: int, nv: tuple):
    if v[0] == "agg1":
        return ("agg1", v[1], nv) if idx == 0 else None
    if v[0] == "agg2":
        if idx == 0:
            return ("agg2", v[1], nv, v[3])
        if idx == 1:
            return ("agg2", v[1], v[2], nv)
        return None
    if v[0] == "agg3":
        if idx == 0:
            return ("agg3", v[1], nv, v[3], v[4])
        if idx == 1:
            return ("agg3", v[1], v[2], nv, v[4])
        if idx == 2:
            return ("agg3", v[1], v[2], v[3], nv)
        return None
    if v[0] == "ref_val":
        ninner = set_field_val(v[1], idx, nv)
        return ("ref_val", ninner) if ninner is not None else None
    return None


def read_place(locals_map: dict, heap: dict, place: tuple):
    l_idx, proj = place
    if l_idx not in locals_map:
        return ("stuck", "uninitialized_local")
    base = locals_map[l_idx]
    if proj == 0:
        return ("val", base)
    if proj in (1, 2, 3):
        fv = get_field_val(base, proj - 1)
        return ("val", fv) if fv is not None else ("stuck", "field_mismatch")
    if proj in (8, 9):
        fv = get_field_val(base, 0)
        return ("val", fv) if fv is not None else ("stuck", "downcast_mismatch")
    if proj == 4:
        if base[0] == "ext_ptr":
            return ("val", ("scalar", 0)) if base[1] else ("ub", "invalid_ptr_deref")
        if base[0] == "heap_ptr":
            slot = heap[base[1]]
            return ("val", ("agg2", 3, ("scalar", slot["step_count"]), ("scalar", slot["trace_acc"])))
        if base[0] == "ref_val":
            return ("val", base[1])
        return ("stuck", "deref_mismatch")
    if proj in (5, 6, 7):
        f_idx = proj - 5
        if base[0] == "heap_ptr":
            slot = heap[base[1]]
            if f_idx == 0:
                return ("val", ("scalar", slot["step_count"]))
            if f_idx == 1:
                return ("val", ("scalar", slot["trace_acc"]))
            return ("stuck", "heap_field_oob")
        fv = get_field_val(unwrap_ref(base), f_idx)
        return ("val", fv) if fv is not None else ("stuck", "deref_field_mismatch")
    return ("stuck", "unknown_proj")


def make_ref(locals_map: dict, heap: dict, place: tuple):
    l_idx, proj = place
    if l_idx not in locals_map:
        return ("stuck", "uninitialized_local")
    base = locals_map[l_idx]
    if proj == 4:
        if base[0] in ("heap_ptr", "ext_ptr", "ref_val"):
            return ("val", base)
        return ("stuck", "deref_ref_mismatch")
    r = read_place(locals_map, heap, place)
    if r[0] != "val":
        return r
    v = r[1]
    if v[0] in ("heap_ptr", "ext_ptr"):
        return ("val", v)
    return ("val", ("ref_val", v))


def write_place(locals_map: dict, heap: dict, place: tuple, nv: tuple) -> bool:
    l_idx, proj = place
    if proj == 0:
        locals_map[l_idx] = nv
        return True
    if proj in (1, 2, 3):
        if l_idx not in locals_map:
            return False
        nb = set_field_val(locals_map[l_idx], proj - 1, nv)
        if nb is None:
            return False
        locals_map[l_idx] = nb
        return True
    if proj in (5, 6):
        if l_idx not in locals_map:
            return False
        base = locals_map[l_idx]
        if base[0] == "heap_ptr" and nv[0] == "scalar":
            if proj == 5:
                heap[base[1]]["step_count"] = nv[1]
            else:
                heap[base[1]]["trace_acc"] = nv[1]
            return True
        return False
    return False


def eval_operand(locals_map: dict, heap: dict, op: tuple):
    b0, b1 = op
    if b0 < 64:
        return read_place(locals_map, heap, (b0, b1))
    if b0 < 128:
        return read_place(locals_map, heap, (b0 - 64, b1))
    if b0 in (128, 129, 130):
        return ("val", ("scalar", b1))
    if b0 == 131:
        if b1 in (0, 1):
            return ("val", ("agg0", 1))
        if b1 == 2:
            return ("val", ("scalar", 999))
    return ("stuck", "bad_const_operand")


def eval_binop(bop: int, lv: tuple, rv: tuple, dst_ty: int):
    if lv[0] != "scalar" or rv[0] != "scalar":
        return None
    a, b = lv[1], rv[1]
    modulus = U32_MOD if dst_ty in (3, 21) else USIZE_MOD
    if bop == 1:
        return ("scalar", 1 if a == b else 0)
    if bop == 2:
        return ("scalar", 1 if a != b else 0)
    if bop == 3:
        return ("scalar", 1 if a < b else 0)
    if bop == 4:
        return ("scalar", 1 if a <= b else 0)
    if bop == 5:
        return ("scalar", 1 if a > b else 0)
    if bop == 6:
        return ("scalar", 1 if a >= b else 0)
    if bop == 7:
        return ("scalar", (a + b) % modulus)
    if bop == 8:
        return ("scalar", (a - b) % modulus)
    if bop == 9:
        return ("scalar", (a * b) % modulus)
    if bop == 10:
        return None if b == 0 else ("scalar", a // b)
    if bop == 11:
        return None if b == 0 else ("scalar", a % b)
    if bop == 12:
        return ("scalar", a & b)
    if bop == 13:
        s = a + b
        return ("agg2", 4, ("scalar", s % modulus), ("scalar", 1 if s >= modulus else 0))
    if bop == 14:
        return ("agg2", 4, ("scalar", (a - b) % modulus), ("scalar", 1 if a < b else 0))
    if bop == 15:
        p = a * b
        return ("agg2", 4, ("scalar", p % modulus), ("scalar", 1 if p >= modulus else 0))
    return None


def run_decoded_ast_machine(by_sym: dict, entry_sym: int, init_locals: dict, max_steps: int = 400) -> dict:
    """Small-step decoded-AST operational machine matching SemanticVerticalSliceCore.lean."""
    heap = {
        0: {"step_count": 0, "trace_acc": 0},
        1: {"step_count": 0, "trace_acc": 0},
    }
    obs_events = []
    frames = [{
        "func_sym": entry_sym,
        "bb": 0,
        "locals": copy.deepcopy(init_locals),
        "ret_dest": None,
        "ret_target": None,
        "unwind_action": 252,
        "is_drop_glue": False,
    }]
    status = "running"

    def unwind_stack():
        nonlocal status
        while frames:
            caller = frames[-1]
            uw = caller["unwind_action"]
            if uw < 32:
                caller["bb"] = uw
                caller["unwind_action"] = 252
                return
            if uw == 252:
                frames.pop()
                continue
            status = ("aborted", uw)
            return
        status = ("unwound",)

    for _ in range(max_steps):
        if status != "running":
            break
        top = frames[-1]
        body = by_sym.get(top["func_sym"])
        if body is None:
            status = ("failed", f"missing_body_{top['func_sym']}")
            break
        if top["bb"] >= len(body["blocks"]):
            status = ("failed", "invalid_block_target")
            break
        blk = body["blocks"][top["bb"]]
        local_types = body["local_types"]

        stmt_err = None
        for s in blk["stmts"]:
            kind = s["kind"]
            if kind == "StorageLive" or kind == "Nop":
                continue
            if kind == "StorageDead":
                top["locals"].pop(s["local"], None)
                continue
            if kind in ("PlaceMention", "RetagStmt"):
                r = read_place(top["locals"], heap, s["src"])
                if r[0] != "val":
                    stmt_err = r
                    break
            elif kind in ("AssignUseNoRetag", "AssignUseRetagYes"):
                r = eval_operand(top["locals"], heap, s["src"])
                if r[0] != "val":
                    stmt_err = r
                    break
                if not write_place(top["locals"], heap, s["dst"], r[1]):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "CopyForDeref":
                r = read_place(top["locals"], heap, s["src"])
                if r[0] != "val":
                    stmt_err = r
                    break
                if not write_place(top["locals"], heap, s["dst"], r[1]):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "RefOrPtr":
                r = make_ref(top["locals"], heap, s["src"])
                if r[0] != "val":
                    stmt_err = r
                    break
                if not write_place(top["locals"], heap, s["dst"], r[1]):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "Discriminant":
                r = read_place(top["locals"], heap, s["src"])
                if r[0] != "val":
                    stmt_err = r
                    break
                v = r[1]
                if v == ("agg0", 2) or (v[0] == "agg1" and v[1] == 1):
                    dv = ("scalar", 0)
                elif v[0] == "agg1" and v[1] == 2:
                    dv = ("scalar", 1)
                else:
                    stmt_err = ("stuck", "discriminant_failed")
                    break
                if not write_place(top["locals"], heap, s["dst"], dv):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "BinOp":
                lr = eval_operand(top["locals"], heap, s["lhs"])
                rr = eval_operand(top["locals"], heap, s["rhs"])
                if lr[0] != "val":
                    stmt_err = lr
                    break
                if rr[0] != "val":
                    stmt_err = rr
                    break
                dst_ty = local_types[s["dst"][0]] if s["dst"][0] < len(local_types) else 4
                br = eval_binop(s["bop"], lr[1], rr[1], dst_ty)
                if br is None:
                    stmt_err = ("stuck", "binop_failed")
                    break
                if not write_place(top["locals"], heap, s["dst"], br):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "UnOp":
                sr = eval_operand(top["locals"], heap, s["src"])
                if sr[0] != "val" or sr[1][0] != "scalar":
                    stmt_err = ("stuck", "unop_failed")
                    break
                nv = 1 if sr[1][1] == 0 else 0
                if not write_place(top["locals"], heap, s["dst"], ("scalar", nv)):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "Agg0":
                if not write_place(top["locals"], heap, s["dst"], ("agg0", s["agg_kind"])):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "Agg1":
                fr = eval_operand(top["locals"], heap, s["f0"])
                if fr[0] != "val":
                    stmt_err = fr
                    break
                if not write_place(top["locals"], heap, s["dst"], ("agg1", s["agg_kind"], fr[1])):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "Agg2":
                r0 = eval_operand(top["locals"], heap, s["f0"])
                r1 = eval_operand(top["locals"], heap, s["f1"])
                if r0[0] != "val" or r1[0] != "val":
                    stmt_err = r0 if r0[0] != "val" else r1
                    break
                if not write_place(top["locals"], heap, s["dst"], ("agg2", s["agg_kind"], r0[1], r1[1])):
                    stmt_err = ("stuck", "write_failed")
                    break
            elif kind == "Agg3":
                r0 = eval_operand(top["locals"], heap, s["f0"])
                r1 = eval_operand(top["locals"], heap, s["f1"])
                r2 = eval_operand(top["locals"], heap, s["f2"])
                if r0[0] != "val" or r1[0] != "val" or r2[0] != "val":
                    stmt_err = ("stuck", "agg3_failed")
                    break
                if not write_place(top["locals"], heap, s["dst"], ("agg3", s["agg_kind"], r0[1], r1[1], r2[1])):
                    stmt_err = ("stuck", "write_failed")
                    break

        if stmt_err is not None:
            status = ("failed", "invalid_ptr_deref") if stmt_err[0] == "ub" else ("failed", stmt_err[1])
            break

        tm = blk["term"]
        tk = tm["kind"]
        if tk == "Goto":
            top["bb"] = tm["target"]
        elif tk == "SwitchInt1":
            dr = eval_operand(top["locals"], heap, tm["discr"])
            if dr[0] != "val" or dr[1][0] != "scalar":
                status = ("failed", "switch_non_scalar")
                break
            top["bb"] = tm["target0"] if dr[1][1] == tm["val0"] else tm["otherwise"]
        elif tk == "SwitchInt2":
            dr = eval_operand(top["locals"], heap, tm["discr"])
            if dr[0] != "val" or dr[1][0] != "scalar":
                status = ("failed", "switch_non_scalar")
                break
            top["bb"] = tm["target0"] if dr[1][1] == tm["val0"] else (tm["target1"] if dr[1][1] == tm["val1"] else tm["otherwise"])
        elif tk == "Return":
            ret_v = top["locals"].get(0, ("agg0", 1))
            if len(frames) == 1:
                status = ("returned", ret_v)
                break
            callee_frame = frames.pop()
            caller = frames[-1]
            if not callee_frame["is_drop_glue"] and callee_frame["ret_dest"] is not None:
                write_place(caller["locals"], heap, callee_frame["ret_dest"], ret_v)
            caller["bb"] = callee_frame["ret_target"]
            caller["unwind_action"] = 252
        elif tk == "UnwindResume":
            frames.pop()
            unwind_stack()
        elif tk == "UnwindTerminate":
            status = ("aborted", tm["reason"])
            break
        elif tk == "Unreachable":
            status = ("failed", "reached_unreachable")
            break
        elif tk == "Assert":
            cr = eval_operand(top["locals"], heap, tm["cond"])
            if cr[0] != "val" or cr[1][0] != "scalar":
                status = ("failed", "assert_non_scalar")
                break
            if cr[1][1] == tm["expected"]:
                top["bb"] = tm["target"]
            else:
                top["unwind_action"] = tm["unwind"]
                unwind_stack()
        elif tk == "Drop":
            gs = tm["glue_sym"]
            if gs == 0:
                top["bb"] = tm["target"]
            else:
                pr = make_ref(top["locals"], heap, tm["place"])
                if pr[0] != "val":
                    status = ("failed", pr[1])
                    break
                top["unwind_action"] = tm["unwind"]
                frames.append({
                    "func_sym": gs,
                    "bb": 0,
                    "locals": {0: ("agg0", 1), 1: pr[1]},
                    "ret_dest": (0, 0),
                    "ret_target": tm["target"],
                    "unwind_action": 252,
                    "is_drop_glue": True,
                })
        elif tk.startswith("Call"):
            arg_vals = []
            arg_err = None
            for a_op in tm["args"]:
                ar = eval_operand(top["locals"], heap, a_op)
                if ar[0] != "val":
                    arg_err = ar
                    break
                arg_vals.append(ar[1])
            if arg_err is not None:
                status = ("failed", "invalid_ptr_deref") if arg_err[0] == "ub" else ("failed", arg_err[1])
                break
            cs = tm["callee_sym"]
            if cs == 1 and len(arg_vals) == 2 and arg_vals[1][0] == "scalar":
                obs_events.append(arg_vals[1][1])
            if cs in by_sym:
                top["unwind_action"] = tm["unwind"]
                callee_locs = {0: ("agg0", 1)}
                for idx_a, av in enumerate(arg_vals):
                    callee_locs[idx_a + 1] = av
                frames.append({
                    "func_sym": cs,
                    "bb": 0,
                    "locals": callee_locs,
                    "ret_dest": tm["dst"],
                    "ret_target": tm["target"],
                    "unwind_action": 252,
                    "is_drop_glue": False,
                })
            elif cs in DECLARED_INTRINSICS:
                if cs == 20:
                    res_v = ("scalar", (arg_vals[0][1] + arg_vals[1][1]) % U32_MOD)
                elif cs == 40:
                    res_v = ("scalar", (arg_vals[0][1] + arg_vals[1][1]) % USIZE_MOD)
                elif cs == 21:
                    res_v = ("scalar", (arg_vals[0][1] * arg_vals[1][1]) % U32_MOD)
                elif cs == 41:
                    res_v = ("scalar", (arg_vals[0][1] * arg_vals[1][1]) % USIZE_MOD)
                elif cs == 23:
                    s = arg_vals[0][1] + arg_vals[1][1]
                    res_v = ("agg1", 1, ("scalar", s)) if s < USIZE_MOD else ("agg0", 2)
                elif cs == 42:
                    s = arg_vals[0][1] + arg_vals[1][1]
                    res_v = ("agg1", 1, ("scalar", s)) if s < U32_MOD else ("agg0", 2)
                elif cs == 25:
                    res_v = ("agg0", 1)
                elif cs == 26:
                    res_v = ("opaque_fmt_args", 999)
                elif cs == 27:
                    top["unwind_action"] = tm["unwind"]
                    unwind_stack()
                    continue
                elif cs == 28:
                    res_v = ("agg1", 1, arg_vals[0][2]) if (arg_vals[0][0] == "agg1" and arg_vals[0][1] == 1) else ("agg1", 2, arg_vals[1])
                elif cs == 29:
                    res_v = ("agg1", 1, arg_vals[0][2]) if arg_vals[0][1] == 1 else ("agg1", 2, arg_vals[0][2])
                elif cs == 30:
                    res_v = ("agg1", 2, arg_vals[0])
                elif cs == 31:
                    u = unwrap_ref(arg_vals[0])
                    res_v = ("scalar", 1 if (u[0] == "agg1" and u[1] == 1) else 0)
                elif cs in (38, 39):
                    res_v = ("scalar", 4)
                else:
                    status = ("failed", f"unhandled_intrinsic_{cs}")
                    break
                write_place(top["locals"], heap, tm["dst"], res_v)
                top["bb"] = tm["target"]
            else:
                status = ("failed", f"missing_body_{cs}")
                break

    return {
        "status": status,
        "heap": copy.deepcopy(heap),
        "obs_events": list(obs_events),
        "frames": frames,
    }


def eval_decoded_package_c0(subject_id: str, parsed_pkg: dict) -> dict:
    """Execute the decoded .amir v3 package on the frozen C0 test suite and compare against independent C0 expectations."""
    if not parsed_pkg.get("accepted"):
        return {"c0_oracle_accepted": False, "reason": f"boundary_1_2_rejected({parsed_pkg.get('reason')})"}
    by_sym = {b["sym_id"]: b for b in parsed_pkg["bodies"]}

    if subject_id == "cleanup_subject":
        cases = {}
        for mfe, tp in [(0, 0), (0, 1), (1, 0), (1, 1)]:
            r = run_decoded_ast_machine(
                by_sym,
                4,
                {0: ("agg0", 1), 1: ("scalar", mfe), 2: ("scalar", tp), 3: ("heap_ptr", 0), 4: ("heap_ptr", 1)},
            )
            cases[f"partial_init_{mfe}_{tp}"] = {
                "status": r["status"],
                "log1": (r["heap"][0]["step_count"], r["heap"][0]["trace_acc"]),
                "log2": (r["heap"][1]["step_count"], r["heap"][1]["trace_acc"]),
                "obs_events": r["obs_events"],
            }
        for tp in [0, 1]:
            r = run_decoded_ast_machine(
                by_sym,
                5,
                {0: ("agg0", 1), 1: ("scalar", tp), 2: ("heap_ptr", 0), 3: ("heap_ptr", 1)},
            )
            cases[f"partial_reinit_{tp}"] = {
                "status": r["status"],
                "log1": (r["heap"][0]["step_count"], r["heap"][0]["trace_acc"]),
                "log2": (r["heap"][1]["step_count"], r["heap"][1]["trace_acc"]),
                "obs_events": r["obs_events"],
            }
        expected = {
            "partial_init_0_0": {"status": ("returned", ("scalar", 105)), "log1": (1, 1), "log2": (1, 2), "obs_events": [1, 2]},
            "partial_init_0_1": {"status": ("unwound",), "log1": (1, 1), "log2": (1, 2), "obs_events": [1, 2]},
            "partial_init_1_0": {"status": ("returned", ("scalar", 105)), "log1": (2, 161), "log2": (1, 2), "obs_events": [10, 1, 2]},
            "partial_init_1_1": {"status": ("unwound",), "log1": (2, 161), "log2": (1, 2), "obs_events": [10, 1, 2]},
            "partial_reinit_0": {"status": ("returned", ("scalar", 107)), "log1": (2, 163), "log2": (1, 2), "obs_events": [10, 3, 2]},
            "partial_reinit_1": {"status": ("unwound",), "log1": (1, 10), "log2": (1, 2), "obs_events": [10, 2]},
        }
        mismatches = {k: {"actual": cases[k], "expected": expected[k]} for k in expected if cases.get(k) != expected[k]}
        return {
            "c0_oracle_accepted": len(mismatches) == 0,
            "reason": "ok" if not mismatches else f"executed_c0_cleanup_mismatch({list(mismatches.keys())})",
            "outcomes": cases,
            "mismatches": mismatches,
        }

    if subject_id == "place_mention_probe":
        outcomes = {}
        for sym, name in [(6, "ub_boundary_probe"), (9, "match_wildcard_probe"), (10, "assign_underscore_probe")]:
            for pv in [True, False]:
                locs = {0: ("agg0", 1), 1: ("ext_ptr", pv), 2: ("scalar", 1)} if sym != 10 else {0: ("agg0", 1), 1: ("ext_ptr", pv)}
                r = run_decoded_ast_machine(by_sym, sym, locs)
                outcomes[f"{name}_valid_{pv}"] = r["status"]
        expected = {
            "ub_boundary_probe_valid_True": ("returned", ("scalar", 0)),
            "ub_boundary_probe_valid_False": ("failed", "invalid_ptr_deref"),
            "match_wildcard_probe_valid_True": ("returned", ("scalar", 0)),
            "match_wildcard_probe_valid_False": ("failed", "invalid_ptr_deref"),
            "assign_underscore_probe_valid_True": ("returned", ("scalar", 0)),
            "assign_underscore_probe_valid_False": ("failed", "invalid_ptr_deref"),
        }
        mismatches = {k: {"actual": outcomes[k], "expected": expected[k]} for k in expected if outcomes.get(k) != expected[k]}
        return {
            "c0_oracle_accepted": len(mismatches) == 0,
            "reason": "ok" if not mismatches else f"executed_c0_place_mention_mismatch({list(mismatches.keys())})",
            "outcomes": outcomes,
            "mismatches": mismatches,
        }

    if subject_id == "zerocopy_layout_holdout":
        def run_align(sz, al):
            r = run_decoded_ast_machine(by_sym, 11, {0: ("agg0", 1), 1: ("scalar", sz), 2: ("scalar", al)})
            if r["status"][0] == "returned" and r["status"][1][0] == "agg1":
                return ("Ok", r["status"][1][2][1]) if r["status"][1][1] == 1 else ("Err", "SizeError")
            return ("Fault", r["status"])

        def run_extend(a1, s1, sl1, a2, s2, sl2):
            d1 = ("agg3", 1, ("scalar", a1), ("scalar", s1), ("scalar", 1 if sl1 else 0))
            d2 = ("agg3", 1, ("scalar", a2), ("scalar", s2), ("scalar", 1 if sl2 else 0))
            r = run_decoded_ast_machine(by_sym, 12, {0: ("agg0", 1), 1: d1, 2: d2})
            if r["status"][0] == "returned" and r["status"][1][0] == "agg1":
                if r["status"][1][1] == 1:
                    inner = r["status"][1][2]
                    dl = inner[2]
                    return ("Ok", (dl[2][1], dl[3][1], bool(dl[4][1])), inner[3][1])
                return ("Err", "SizeError")
            return ("Fault", r["status"])

        outcomes = {
            "align_to_6_0": run_align(6, 0),
            "align_to_8_4": run_align(8, 4),
            "align_to_6_4": run_align(6, 4),
            "align_to_13_4": run_align(13, 4),
            "align_to_usize_max_minus_1_4": run_align(USIZE_MAX - 1, 4),
            "extend_valid_slice": run_extend(4, 6, False, 4, 4, True),
            "extend_valid_sized": run_extend(4, 6, False, 8, 10, False),
            "extend_err_already_slice": run_extend(4, 8, True, 4, 4, False),
        }
        expected = {
            "align_to_6_0": ("Err", "SizeError"),
            "align_to_8_4": ("Ok", 8),
            "align_to_6_4": ("Ok", 8),
            "align_to_13_4": ("Ok", 16),
            "align_to_usize_max_minus_1_4": ("Err", "SizeError"),
            "extend_valid_slice": ("Ok", (4, 8, True), 8),
            "extend_valid_sized": ("Ok", (8, 18, False), 8),
            "extend_err_already_slice": ("Err", "SizeError"),
        }
        mismatches = {k: {"actual": outcomes[k], "expected": expected[k]} for k in expected if outcomes.get(k) != expected[k]}
        return {
            "c0_oracle_accepted": len(mismatches) == 0,
            "reason": "ok" if not mismatches else f"executed_c0_zerocopy_mismatch({list(mismatches.keys())})",
            "outcomes": outcomes,
            "mismatches": mismatches,
        }

    if subject_id == "loop_prefix_probe":
        r_bad = run_decoded_ast_machine(
            by_sym,
            43,
            {0: ("agg0", 1), 1: ("ext_ptr", False), 2: ("scalar", 1), 3: ("scalar", 8), 4: ("scalar", 0)},
            max_steps=10,
        )
        r_term = run_decoded_ast_machine(
            by_sym,
            43,
            {0: ("agg0", 1), 1: ("ext_ptr", False), 2: ("scalar", 0), 3: ("scalar", 8), 4: ("scalar", 4)},
            max_steps=60,
        )
        r_loop = run_decoded_ast_machine(
            by_sym,
            43,
            {0: ("agg0", 1), 1: ("ext_ptr", False), 2: ("scalar", 0), 3: ("scalar", 8), 4: ("scalar", 0)},
            max_steps=23,
        )
        outcomes = {
            "bad_prefix_invalid_ptr": r_bad["status"],
            "terminating_target8_step4": r_term["status"],
            "unbounded_step23_status": r_loop["status"],
            "unbounded_step23_bb": r_loop["frames"][-1]["bb"] if r_loop["frames"] else None,
        }
        expected = {
            "bad_prefix_invalid_ptr": ("failed", "invalid_ptr_deref"),
            "terminating_target8_step4": ("returned", ("scalar", 2)),
            "unbounded_step23_status": "running",
            "unbounded_step23_bb": 4,
        }
        mismatches = {k: {"actual": outcomes[k], "expected": expected[k]} for k in expected if outcomes.get(k) != expected[k]}
        return {
            "c0_oracle_accepted": len(mismatches) == 0,
            "reason": "ok" if not mismatches else f"executed_c0_loop_mismatch({list(mismatches.keys())})",
            "outcomes": outcomes,
            "mismatches": mismatches,
        }

    if subject_id == "dep_layout_core":
        r_10 = run_decoded_ast_machine(by_sym, 52, {0: ("agg0", 1), 1: ("scalar", 10)})
        r_24 = run_decoded_ast_machine(by_sym, 52, {0: ("agg0", 1), 1: ("scalar", 24)})
        outcomes = {
            "dep_inline_align_10": r_10["status"],
            "dep_inline_align_24": r_24["status"],
        }
        expected = {
            "dep_inline_align_10": ("returned", ("scalar", 14)),
            "dep_inline_align_24": ("returned", ("scalar", 28)),
        }
        mismatches = {k: {"actual": outcomes[k], "expected": expected[k]} for k in expected if outcomes.get(k) != expected[k]}
        return {
            "c0_oracle_accepted": len(mismatches) == 0,
            "reason": "ok" if not mismatches else f"executed_dep_layout_mismatch({list(mismatches.keys())})",
            "outcomes": outcomes,
            "mismatches": mismatches,
        }

    return {"c0_oracle_accepted": False, "reason": "unknown_subject"}


def diff_amir_v3_toolchains(parsed_97: dict, parsed_98: dict) -> dict:
    """Explain exact .amir v3 AST / opcode differences between 1.95..1.97 and 1.98."""
    retag_stmt_97 = 0
    use_no_retag_97 = 0
    use_yes_retag_97 = 0
    for b in parsed_97["bodies"]:
        for blk in b["blocks"]:
            for s in blk["stmts"]:
                if s["kind"] == "RetagStmt":
                    retag_stmt_97 += 1
                elif s["kind"] == "AssignUseNoRetag":
                    use_no_retag_97 += 1
                elif s["kind"] == "AssignUseRetagYes":
                    use_yes_retag_97 += 1

    retag_stmt_98 = 0
    use_no_retag_98 = 0
    use_yes_retag_98 = 0
    for b in parsed_98["bodies"]:
        for blk in b["blocks"]:
            for s in blk["stmts"]:
                if s["kind"] == "RetagStmt":
                    retag_stmt_98 += 1
                elif s["kind"] == "AssignUseNoRetag":
                    use_no_retag_98 += 1
                elif s["kind"] == "AssignUseRetagYes":
                    use_yes_retag_98 += 1

    return {
        "pre_1_98": {
            "retag_stmt_0x31_count": retag_stmt_97,
            "assign_use_no_retag_0x10_count": use_no_retag_97,
            "assign_use_retag_yes_0x11_count": use_yes_retag_97,
        },
        "rustc_1_98": {
            "retag_stmt_0x31_count": retag_stmt_98,
            "assign_use_no_retag_0x10_count": use_no_retag_98,
            "assign_use_retag_yes_0x11_count": use_yes_retag_98,
        },
        "explanation": (
            "In 1.95-1.97, Rvalue::Use(op) is 1-field (0x10 AssignUseNoRetag) and retags are "
            "standalone StatementKind::Retag(rk, place) statements (0x31 RetagStmt). In 1.98, "
            "StatementKind::Retag was removed and folded into Rvalue::Use(op, WithRetag::Yes) (0x11) "
            "vs WithRetag::No (0x10)."
        ),
    }


def run_charon_comparative_study() -> dict:
    """Bounded Charon 0.1.174 (1.95) vs 0.1.210 (1.98) configuration, source-diff, and rebuild study."""
    charon_study = {
        "charon_binaries": [
            {
                "version": "0.1.174",
                "pinned_toolchain": "nightly_1_95_2026_02_06 (efc9e1b50 2026-02-06)",
                "charon_bin": CHARON_195_BIN,
                "charon_sha256": sha256_file(CHARON_195_BIN),
                "charon_driver_bin": CHARON_195_DRIVER_BIN,
                "charon_driver_sha256": sha256_file(CHARON_195_DRIVER_BIN),
                "upstream_commit": "5096e36339dc62d885fb3b7bf6e1bd98000514e0",
            },
            {
                "version": "0.1.210",
                "pinned_toolchain": "nightly_1_98_2026_05_30 (f8a08b688 2026-05-30)",
                "charon_bin": CHARON_198_BIN,
                "charon_sha256": sha256_file(CHARON_198_BIN),
                "charon_driver_bin": CHARON_198_DRIVER_BIN,
                "charon_driver_sha256": sha256_file(CHARON_198_DRIVER_BIN),
                "upstream_commit": "1e08453924610c19d74c245a7308f17c1008e2db",
            },
        ],
        "shared_corpus_extractions": [],
    }

    configs = [
        ("default_ullbc", ["--ullbc", "--mir", "elaborated"]),
        (
            "precise_drops_preserve_ub_ullbc",
            [
                "--ullbc",
                "--mir",
                "elaborated",
                "--precise-drops",
                "--include",
                "core::mem::drop",
                "--include",
                "core::mem::forget",
                "--rustc-arg=-Zmir-preserve-ub",
            ],
        ),
        (
            "precise_drops_structured_llbc",
            [
                "--mir",
                "elaborated",
                "--precise-drops",
                "--include",
                "core::mem::drop",
                "--include",
                "core::mem::forget",
                "--rustc-arg=-Zmir-preserve-ub",
            ],
        ),
    ]

    for ch_ver, ch_bin, tc_root in [
        ("0.1.174", CHARON_195_BIN, TOOLCHAINS[0]["root"]),
        ("0.1.210", CHARON_198_BIN, TOOLCHAINS[3]["root"]),
    ]:
        env = os.environ.copy()
        env["PATH"] = f"{tc_root}/bin:" + env.get("PATH", "")
        env["LD_LIBRARY_PATH"] = f"{tc_root}/lib:{tc_root}/lib/rustlib/x86_64-unknown-linux-gnu/lib"
        for cfg_id, cfg_flags in configs:
            for s_id, s_path in SUBJECTS:
                out_file = os.path.join(ART_DIR, f"charon_{ch_ver}_{cfg_id}_{s_id}.json")
                cmd = (
                    [ch_bin, "rustc"]
                    + cfg_flags
                    + ["--dest-file", out_file, "--", "--crate-type=lib", "--edition=2021", s_path]
                )
                t0 = time.monotonic()
                proc = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=60)
                t1 = time.monotonic()
                data = json.load(open(out_file)) if os.path.exists(out_file) else {}
                funs = data.get("translated", {}).get("fun_decls", [])
                transparent_names = []
                opaque_names = []
                unwind_resume_blocks = 0
                place_mention_count = 0
                for fn in funs:
                    if not isinstance(fn, dict):
                        continue
                    name_str = "::".join(str(x) for x in fn.get("item_meta", {}).get("name", []))
                    body = fn.get("body")
                    if isinstance(body, dict) and "Unstructured" in body:
                        transparent_names.append(name_str)
                        for blk in body["Unstructured"].get("body", []):
                            if "UnwindResume" in json.dumps(blk.get("terminator", {})):
                                unwind_resume_blocks += 1
                            if "PlaceMention" in json.dumps(blk.get("statements", [])):
                                place_mention_count += 1
                    elif isinstance(body, dict) and "Structured" in body:
                        transparent_names.append(name_str)
                    else:
                        opaque_names.append(name_str)
                charon_study["shared_corpus_extractions"].append({
                    "charon_version": ch_ver,
                    "config_id": cfg_id,
                    "subject": s_id,
                    "exit_code": proc.returncode,
                    "elapsed_ms": int(round((t1 - t0) * 1000)),
                    "out_file_sha256": sha256_file(out_file) if os.path.exists(out_file) else None,
                    "fun_decl_count": len(funs),
                    "transparent_fun_count": len(transparent_names),
                    "opaque_fun_count": len(opaque_names),
                    "has_drop_in_place_bodies": any("drop_in_place" in n for n in transparent_names),
                    "has_core_mem_drop_body": any("mem" in n and "drop" in n and "drop_in_place" not in n for n in transparent_names),
                    "unwind_resume_block_count": unwind_resume_blocks,
                    "place_mention_block_count": place_mention_count,
                })

    # Inspect upstream commits in CHARON_GIT_DB between 5096e363 (0.1.174) and 1e084539 (0.1.210)
    commits = ["5096e363", "ce70ecf7", "3a01e036", "3e16db29", "1e084539"]
    commit_records = []
    for c in commits:
        proc = subprocess.run(
            ["git", f"--git-dir={CHARON_GIT_DB}", "show", "--shortstat", "--format=%H|%ai|%s", c],
            capture_output=True,
            text=True,
            check=True,
        )
        lines = [ln.strip() for ln in proc.stdout.strip().splitlines() if ln.strip()]
        hdr = lines[0].split("|", 2)
        stat = lines[-1] if len(lines) > 1 else ""
        proc_files = subprocess.run(
            ["git", f"--git-dir={CHARON_GIT_DB}", "show", "--name-only", "--format=", c],
            capture_output=True,
            text=True,
            check=True,
        )
        all_files = [f.strip() for f in proc_files.stdout.splitlines() if f.strip()]
        rs_files = [f for f in all_files if f.endswith(".rs") and not f.startswith("charon/tests/ui/")]
        commit_records.append({
            "commit": hdr[0],
            "date": hdr[1],
            "subject": hdr[2],
            "shortstat": stat,
            "total_files_changed": len(all_files),
            "non_ui_rust_source_files_changed": len(rs_files),
            "rust_source_files": rs_files,
        })

    # Inspect exact rustc_private diff in charon/src/bin/charon-driver/translate between 5096e363 and 1e084539
    diff_proc = subprocess.run(
        [
            "git",
            f"--git-dir={CHARON_GIT_DB}",
            "diff",
            "--stat",
            "5096e363..1e084539",
            "--",
            "charon/src/bin/charon-driver",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    charon_study["upstream_rustc_bump_commits"] = commit_records
    charon_study["charon_driver_diff_stat_0_1_174_to_0_1_210"] = diff_proc.stdout.strip().splitlines()

    # Bounded offline cargo build probe of charon at 1e084539
    wt_dir = "/tmp/charon_offline_probe_1e084539"
    os.makedirs(wt_dir, exist_ok=True)
    subprocess.run(
        ["git", f"--git-dir={CHARON_GIT_DB}", f"--work-tree={wt_dir}", "checkout", "-f", "1e084539"],
        capture_output=True,
        text=True,
        check=True,
    )
    tc98_root = TOOLCHAINS[3]["root"]
    cargo_bin = "/usr/local/google/home/joshlf/.cargo/bin/cargo"
    probe_env = os.environ.copy()
    probe_env["PATH"] = f"{tc98_root}/bin:" + probe_env.get("PATH", "")
    probe_env["LD_LIBRARY_PATH"] = (
        f"{tc98_root}/lib:{tc98_root}/lib/rustlib/x86_64-unknown-linux-gnu/lib:"
        + probe_env.get("LD_LIBRARY_PATH", "")
    )
    probe_env["RUSTC"] = os.path.join(tc98_root, "bin/rustc")
    t_probe0 = time.monotonic()
    probe_proc = subprocess.run(
        [cargo_bin, "check", "--offline", "--manifest-path", os.path.join(wt_dir, "charon/Cargo.toml")],
        env=probe_env,
        capture_output=True,
        text=True,
    )
    t_probe1 = time.monotonic()
    stderr_lines = [ln.strip() for ln in probe_proc.stderr.strip().splitlines() if ln.strip()]
    if probe_proc.returncode == 0:
        probe_status = "offline_cargo_check_succeeded_from_local_cargo_cache"
    elif any("librustc_driver" in ln for ln in stderr_lines):
        probe_status = "shared_library_loader_missing_ld_library_path"
    else:
        probe_status = "offline_cargo_check_failed_see_stderr"
    charon_study["offline_source_rebuild_probe"] = {
        "checkout_commit": "1e08453924610c19d74c245a7308f17c1008e2db",
        "command": "cargo check --offline --manifest-path charon/Cargo.toml (with LD_LIBRARY_PATH set for 1.98.0-nightly)",
        "exit_code": probe_proc.returncode,
        "elapsed_ms": int(round((t_probe1 - t_probe0) * 1000)),
        "stderr_tail_lines": stderr_lines[-6:],
        "observed_status": probe_status,
    }
    return charon_study


def main():
    os.makedirs(ART_DIR, exist_ok=True)
    os.makedirs("/tmp/p1_p3_build", exist_ok=True)
    toolchain_results = []
    parsed_by_tc_subj = {}

    for tc in TOOLCHAINS:
        tc_id = tc["id"]
        root = tc["root"]
        rustc_bin = os.path.join(root, "bin/rustc")
        lib_dir = os.path.join(root, "lib")
        host_lib_dir = os.path.join(root, "lib/rustlib/x86_64-unknown-linux-gnu/lib")

        env = os.environ.copy()
        env["LD_LIBRARY_PATH"] = f"{lib_dir}:{host_lib_dir}:" + env.get("LD_LIBRARY_PATH", "")

        driver_bin = f"/tmp/p1_p3_build/portable_mir_driver_{tc_id}"
        t0 = time.monotonic()
        compile_proc = subprocess.run(
            ["/usr/bin/time", "-v", rustc_bin, "--edition=2021", "-O"]
            + tc["cfg_flags"]
            + [PORTABLE_DRIVER_SRC, "-o", driver_bin],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        t1 = time.monotonic()
        if compile_proc.returncode != 0:
            raise RuntimeError(f"Failed to compile {tc_id}:\n{compile_proc.stderr}")
        m_comp = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", compile_proc.stderr)
        comp_rss = int(m_comp.group(1)) * 1024 if m_comp else 0

        subj_runs = []
        for s_id, s_path in SUBJECTS:
            out_json = os.path.join(ART_DIR, f"out_{tc_id}_{s_id}.json")
            out_bodies = os.path.join(ART_DIR, f"bodies_{tc_id}_{s_id}.json")
            out_amir = os.path.join(ART_DIR, f"{tc_id}_{s_id}.amir")

            extra_env = env.copy()
            if s_id == "dep_layout_core":
                with open("/tmp/p1_p3_build/generated_align.rs", "w") as gf:
                    gf.write("pub const GENERATED_ARCH_ALIGN: usize = 8;\n")
                extra_env["OUT_DIR"] = "/tmp/p1_p3_build"

            cmd = [
                driver_bin,
                "--crate-type=lib",
                "--edition=2021",
                "--sysroot",
                root,
                "-Z",
                "mir-preserve-ub",
                "-Z",
                "always-encode-mir=yes",
                "--emit=metadata",
                "-o",
                f"/tmp/p1_p3_build/lib_{tc_id}_{s_id}.rmeta",
                "--driver-run-mono-collector",
                "--driver-out-json",
                out_json,
                "--driver-dump-bodies",
                out_bodies,
                "--driver-emit-amir-v3",
                out_amir,
                s_path,
            ]
            rusage_before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            st0 = time.monotonic()
            s_proc = subprocess.run(
                ["/usr/bin/time", "-v"] + cmd,
                env=extra_env,
                capture_output=True,
                text=True,
                timeout=120,
            )
            st1 = time.monotonic()
            if s_proc.returncode != 0:
                raise RuntimeError(f"Capture failed on {tc_id} / {s_id}:\n{s_proc.stderr}\n{s_proc.stdout}")
            rusage_after = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
            m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", s_proc.stderr)
            rss_bytes = int(m.group(1)) * 1024 if m else int(rusage_after) * 1024

            with open(out_amir, "rb") as af:
                amir_bytes = af.read()
            parsed = parse_amir_v3_package(amir_bytes)
            parsed_by_tc_subj[(tc_id, s_id)] = parsed
            c0_res = eval_decoded_package_c0(s_id, parsed)
            legacy_shape = run_legacy_structural_shape_check(s_id, parsed)
            assert c0_res["c0_oracle_accepted"], f"C0 execution oracle failed for {tc_id}/{s_id}: {c0_res}"

            subj_runs.append({
                "subject": s_id,
                "exit_code": s_proc.returncode,
                "elapsed_ms": int(round((st1 - st0) * 1000)),
                "max_rss_bytes": rss_bytes,
                "rusage_children_ru_maxrss_bytes": int(rusage_after) * 1024,
                "rusage_before_kb": int(rusage_before),
                "rusage_after_kb": int(rusage_after),
                "out_json_sha256": sha256_file(out_json),
                "out_bodies_sha256": sha256_file(out_bodies),
                "out_amir_sha256": sha256_file(out_amir),
                "out_amir_size_bytes": len(amir_bytes),
                "amir_v3_fp16": parsed.get("fp16"),
                "amir_v3_body_count": parsed.get("body_count"),
                "boundary_1_2_accepted": parsed.get("accepted"),
                "legacy_structural_shape_check": legacy_shape,
                "c0_semantic_oracle": c0_res,
            })

        charon_env = os.environ.copy()
        charon_env["LD_LIBRARY_PATH"] = f"{lib_dir}:{host_lib_dir}"
        ch198_proc = subprocess.run([CHARON_198_DRIVER_BIN, "--version"], env=charon_env, capture_output=True, text=True)
        ch195_proc = subprocess.run([CHARON_195_DRIVER_BIN, "--version"], env=charon_env, capture_output=True, text=True)

        toolchain_results.append({
            "toolchain_id": tc_id,
            "version": tc["version"],
            "rustc_sha256": sha256_file(rustc_bin),
            "mir_use_arity": tc["mir_use_arity"],
            "has_retag_stmt": tc["has_retag_stmt"],
            "drop_glue_api": tc["drop_glue_api"],
            "derive_eq_helper_name": tc["derive_eq_helper_name"],
            "driver_compile_exit_code": compile_proc.returncode,
            "driver_compile_elapsed_ms": int(round((t1 - t0) * 1000)),
            "driver_compile_max_rss_bytes": comp_rss,
            "driver_binary_sha256": sha256_file(driver_bin),
            "prebuilt_charon_0_1_174_probe": {
                "exit_code": ch195_proc.returncode,
                "compatible_without_rebuild": ch195_proc.returncode == 0,
                "stderr_summary": ch195_proc.stderr.strip().splitlines()[0] if ch195_proc.stderr.strip() else "",
            },
            "prebuilt_charon_0_1_210_probe": {
                "exit_code": ch198_proc.returncode,
                "compatible_without_rebuild": ch198_proc.returncode == 0,
                "stderr_summary": ch198_proc.stderr.strip().splitlines()[0] if ch198_proc.stderr.strip() else "",
            },
            "subject_runs": subj_runs,
        })
        print(
            f"Completed toolchain {tc_id}: compile_exit={compile_proc.returncode}, "
            f"charon_195_exit={ch195_proc.returncode}, charon_198_exit={ch198_proc.returncode}"
        )

    cross_toolchain_comparison = {}
    for s_id, _ in SUBJECTS:
        p95 = parsed_by_tc_subj[("nightly_1_95_2026_02_06", s_id)]
        p96 = parsed_by_tc_subj[("nightly_1_96_2026_04_10", s_id)]
        p97 = parsed_by_tc_subj[("nightly_1_97_2026_04_11", s_id)]
        p98 = parsed_by_tc_subj[("nightly_1_98_2026_05_30", s_id)]
        c95 = eval_decoded_package_c0(s_id, p95)["outcomes"]
        c96 = eval_decoded_package_c0(s_id, p96)["outcomes"]
        c97 = eval_decoded_package_c0(s_id, p97)["outcomes"]
        c98 = eval_decoded_package_c0(s_id, p98)["outcomes"]
        assert c95 == c96 == c97 == c98, f"Cross-toolchain C0 mismatch on {s_id}"
        cross_toolchain_comparison[s_id] = {
            "1_95_to_1_97_byte_identical": (p95["fp16"] == p96["fp16"] == p97["fp16"]),
            "1_97_to_1_98_opcode_diff": diff_amir_v3_toolchains(p97, p98),
            "all_4_toolchains_c0_semantically_equivalent": (c95 == c96 == c97 == c98),
            "c0_outcomes": {str(k): str(v) for k, v in c98.items()},
        }

    # Run 4 Semantic-Drift Negative Controls on 1.98 driver (2 structural + 2 structure-preserving constant/branch drifts)
    tc98_root = TOOLCHAINS[3]["root"]
    tc98_env = os.environ.copy()
    tc98_env["LD_LIBRARY_PATH"] = f"{tc98_root}/lib:{tc98_root}/lib/rustlib/x86_64-unknown-linux-gnu/lib"
    drv98 = "/tmp/p1_p3_build/portable_mir_driver_nightly_1_98_2026_05_30"

    drift_controls = []
    for ctrl_id, drift_flag, s_id, s_path, expect_legacy_pass in [
        ("drift_control_strip_place_mention", "strip_place_mention", "place_mention_probe", SUBJECTS[1][1], False),
        ("drift_control_strip_cleanup_drop", "strip_cleanup_drop", "cleanup_subject", SUBJECTS[0][1], False),
        ("drift_control_alter_reinit_constant", "alter_reinit_constant", "cleanup_subject", SUBJECTS[0][1], True),
        ("drift_control_swap_extend_slice_branch", "swap_extend_slice_branch", "zerocopy_layout_holdout", SUBJECTS[2][1], True),
    ]:
        out_json = os.path.join(ART_DIR, f"out_{ctrl_id}.json")
        out_amir = os.path.join(ART_DIR, f"{ctrl_id}.amir")
        cmd = [
            drv98,
            "--crate-type=lib",
            "--edition=2021",
            "--sysroot",
            tc98_root,
            "-Z",
            "mir-preserve-ub",
            "-Z",
            "always-encode-mir=yes",
            "--emit=metadata",
            "-o",
            f"/tmp/p1_p3_build/lib_{ctrl_id}.rmeta",
            "--driver-run-mono-collector",
            "--driver-simulate-drift",
            drift_flag,
            "--driver-out-json",
            out_json,
            "--driver-emit-amir-v3",
            out_amir,
            s_path,
        ]
        proc = subprocess.run(cmd, env=tc98_env, capture_output=True, text=True, check=True)
        with open(out_amir, "rb") as af:
            amir_bytes = af.read()
        parsed = parse_amir_v3_package(amir_bytes)
        legacy_res = run_legacy_structural_shape_check(s_id, parsed)
        c0_res = eval_decoded_package_c0(s_id, parsed)
        assert parsed.get("accepted") is True
        assert legacy_res.get("legacy_shape_accepted") is expect_legacy_pass
        assert c0_res.get("c0_oracle_accepted") is False
        drift_controls.append({
            "control_id": ctrl_id,
            "subject": s_id,
            "simulate_drift_mode": drift_flag,
            "exit_code": proc.returncode,
            "out_amir_sha256": sha256_file(out_amir),
            "out_amir_size_bytes": len(amir_bytes),
            "amir_v3_fp16": parsed.get("fp16"),
            "boundary_1_2_accepted": parsed.get("accepted"),
            "legacy_structural_shape_accepted": legacy_res.get("legacy_shape_accepted"),
            "c0_oracle_accepted": c0_res.get("c0_oracle_accepted"),
            "c0_rejection_reason": c0_res.get("reason"),
            "c0_mismatches": {str(k): str(v) for k, v in c0_res.get("mismatches", {}).items()},
        })
        print(
            f"Drift control {ctrl_id}: exit={proc.returncode}, "
            f"b1_2={parsed.get('accepted')}, legacy_shape={legacy_res.get('legacy_shape_accepted')}, "
            f"c0_accepted={c0_res.get('c0_oracle_accepted')} ({c0_res.get('reason')})"
        )

    charon_study = run_charon_comparative_study()

    ledger = {
        "wire_format": "AMIR_v3",
        "portable_driver_source": PORTABLE_DRIVER_SRC,
        "portable_driver_sha256": sha256_file(PORTABLE_DRIVER_SRC),
        "portable_driver_adaptation_cost": {
            "conditional_cfg_blocks": 5,
            "conditional_loc": 36,
            "api_differences_handled": [
                "1.95 -> 1.96: #[derive(Eq)] helper method renamed from assert_receiver_is_total_eq to assert_fields_are_eq",
                "1.97 -> 1.98: StatementKind::Retag(rk, place) (0x31) removed and folded into Rvalue::Use(op, WithRetag) (0x10/0x11)",
                "1.97 -> 1.98: Instance::resolve_drop_in_place renamed to Instance::resolve_drop_glue",
            ],
        },
        "charon_0_1_174_to_0_1_210_comparative_study": charon_study,
        "toolchain_trials": toolchain_results,
        "cross_toolchain_amir_v3_and_c0_comparison": cross_toolchain_comparison,
        "semantic_drift_negative_controls": drift_controls,
    }

    out_ledger = os.path.join(BASE_DIR, "upgrade-trial-ledger.json")
    with open(out_ledger, "w") as f:
        json.dump(ledger, f, indent=2)
        f.write("\n")
    print("Wrote", out_ledger, "sha256:", sha256_file(out_ledger))


if __name__ == "__main__":
    main()
