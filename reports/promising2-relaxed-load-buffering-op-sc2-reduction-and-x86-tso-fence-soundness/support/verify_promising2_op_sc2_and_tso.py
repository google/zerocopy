#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

""" standalone reproducible verification suite for:
1. Multi-architecture (`aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
   `riscv64gc-unknown-linux-gnu`, `x86_64-unknown-linux-gnu`) `#![no_core]`
   atomic codegen under Anneal's pinned `rustc 1.98.0-nightly (f8a08b688c)`
   (`-O --emit=asm`), testing load-buffering (`lb_rlx`, `lb_false_dep`,
   `lb_branch_hoist`, `lb_cond_overwrite`, `lb_rlx_fetch_add`, `lb_data_dep`,
   `lb_ctrl_dep`, `lb_frel_acq`) and `crossbeam-epoch`'s `x86` `SeqCst` swap +
   `compiler_fence(SeqCst)` + `Acquire` load vs. `fence(SeqCst)`.
2. Executable state-space & non-vacuity verification of Operational Promising
   2.0 combined with `Op-SC2'` (`PS2-OpSC2'`) and `TargetMemModel`
   (`portable_cpp20` vs. `x86_tso`), including positive/negative ablation
   controls for `capMem` RMW-steal protection and `fence(Release)` promise
   draining.
3. Full 5-gate `TrustedBoundary.lean` verification (`preflight`, `-t0`
   `-DwarningAsError=true` compile, `audit` fresh kernel replay,
   `CheckEnvConstants` zero `_unsafe_rec`/zero `sorry`, and `#print axioms`)
   over `Anneal/PromisingReductionProof.lean`.
"""

from __future__ import annotations

import fractions
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

ANNEAL_ROOT_ENV = os.environ.get("ANNEAL_ROOT", "")
ZEROCOPY_REPO = Path(os.environ.get("ZEROCOPY_REPO", "."))
ZEROCOPY_REV = os.environ.get(
    "ZEROCOPY_REV", "ae3c943b7b1004d839ddb8d0dad65eacba158d58"
)
LEAN_PREFIX = Path(
    os.environ.get(
        "LEAN_PREFIX",
        str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"),
    )
)
LEAN_BIN = LEAN_PREFIX / "bin" / "lean"
PROOF_SRC = Path(__file__).resolve().parent / "Anneal" / "PromisingReductionProof.lean"

OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]
ALL_PARTS = OLEAN_PARTS + IR_PARTS
CLEAN_ENV = {"PATH": "/usr/bin:/bin"}

NOCORE_ATOMICS_RS = r"""#![feature(
    no_core,
    lang_items,
    intrinsics,
    rustc_attrs,
    auto_traits,
    adt_const_params
)]
#![allow(internal_features, incomplete_features)]
#![no_core]
#![crate_type = "lib"]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "const_param_ty"] pub trait ConstParamTy_ {}
#[lang = "structural_peq"] pub trait StructuralPartialEq {}

impl Copy for u32 {}
impl Copy for usize {}
impl<T: ?Sized> Copy for *mut T {}
impl<T: ?Sized> Copy for *const T {}

pub enum AtomicOrdering {
    Relaxed,
    Release,
    Acquire,
    AcqRel,
    SeqCst,
}
impl Copy for AtomicOrdering {}
impl ConstParamTy_ for AtomicOrdering {}
impl StructuralPartialEq for AtomicOrdering {}

#[rustc_intrinsic]
pub unsafe fn atomic_load<T: Copy, const ORD: AtomicOrdering>(src: *const T) -> T;
#[rustc_intrinsic]
pub unsafe fn atomic_store<T: Copy, const ORD: AtomicOrdering>(dst: *mut T, val: T);
#[rustc_intrinsic]
pub unsafe fn atomic_xadd<T: Copy, U: Copy, const ORD: AtomicOrdering>(dst: *mut T, src: U) -> T;
#[rustc_intrinsic]
pub unsafe fn atomic_xchg<T: Copy, const ORD: AtomicOrdering>(dst: *mut T, src: T) -> T;
#[rustc_intrinsic]
pub unsafe fn atomic_fence<const ORD: AtomicOrdering>();
#[rustc_intrinsic]
pub unsafe fn atomic_singlethreadfence<const ORD: AtomicOrdering>();
#[rustc_intrinsic]
pub fn wrapping_sub<T: Copy>(a: T, b: T) -> T;
#[rustc_intrinsic]
pub fn wrapping_add<T: Copy>(a: T, b: T) -> T;

#[no_mangle]
pub unsafe fn lb_rlx(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1);
    r
}

#[no_mangle]
pub unsafe fn lb_false_dep(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    let z = wrapping_sub(r, r);
    atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, wrapping_add(1, z));
    r
}

#[no_mangle]
pub unsafe fn lb_branch_hoist(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    match r {
        1 => atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1),
        _ => atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1),
    }
    r
}

#[no_mangle]
pub unsafe fn lb_cond_overwrite(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    match r {
        0 => {
            atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1);
            atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 2);
        }
        _ => {
            atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 2);
        }
    }
    r
}

#[no_mangle]
pub unsafe fn lb_rlx_fetch_add(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    let _ = atomic_xadd::<u32, u32, { AtomicOrdering::Relaxed }>(y, 1);
    r
}

#[no_mangle]
pub unsafe fn lb_data_dep(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, r);
    r
}

#[no_mangle]
pub unsafe fn lb_ctrl_dep(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Relaxed }>(x);
    match r {
        1 => atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1),
        _ => {}
    }
    r
}

#[no_mangle]
pub unsafe fn lb_frel_acq(x: *const u32, y: *mut u32) -> u32 {
    let r = atomic_load::<u32, { AtomicOrdering::Acquire }>(x);
    atomic_fence::<{ AtomicOrdering::Release }>();
    atomic_store::<u32, { AtomicOrdering::Relaxed }>(y, 1);
    r
}

#[no_mangle]
pub unsafe fn crossbeam_x86_pattern(x: *mut usize, y: *const usize) -> usize {
    let _ = atomic_xchg::<usize, { AtomicOrdering::SeqCst }>(x, 1);
    atomic_singlethreadfence::<{ AtomicOrdering::SeqCst }>();
    atomic_load::<usize, { AtomicOrdering::Acquire }>(y)
}

#[no_mangle]
pub unsafe fn portable_fence_sc_pattern(x: *mut usize, y: *const usize) -> usize {
    let _ = atomic_xchg::<usize, { AtomicOrdering::SeqCst }>(x, 1);
    atomic_fence::<{ AtomicOrdering::SeqCst }>();
    atomic_load::<usize, { AtomicOrdering::Acquire }>(y)
}
"""

THEOREMS = [
    "Anneal.PromisingReductionProof.promiseFree_forbids_lb_rlx_1_1",
    "Anneal.PromisingReductionProof.ps2_allows_lb_rlx_1_1",
    "Anneal.PromisingReductionProof.ps2_allows_lb_cond_overwrite_1_2",
    "Anneal.PromisingReductionProof.ps2_cap_blocks_stealable_rmw_promise",
    "Anneal.PromisingReductionProof.ps2_threadStep_preserves_valInv",
    "Anneal.PromisingReductionProof.ps2_pure_relaxed_invariant_preserved",
    "Anneal.PromisingReductionProof.ps2_forbids_oota_lb_data_dep",
    "Anneal.PromisingReductionProof.ps2_forbids_lb_frel_acq_1_1",
    "Anneal.PromisingReductionProof.releaseOnly_exact_bisimulation",
    "Anneal.PromisingReductionProof.portableCpp20_allows_xchg_cfence_acq_0_0",
    "Anneal.PromisingReductionProof.x86Tso_forbids_xchg_cfence_acq_0_0",
    "Anneal.PromisingReductionProof.tso_xchg_forbids_0_0_and_portable_allows_0_0",
]


def sha256_path(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def find_pinned_anneal_rustc() -> Path:
    if "PINNED_RUSTC" in os.environ:
        return Path(os.environ["PINNED_RUSTC"])
    cache = Path.home() / ".cache/anneal/toolchain"
    for cand in sorted(cache.glob("*/rust/bin/rustc")):
        try:
            ver = subprocess.check_output([str(cand), "--version", "--verbose"], text=True)
            if "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1" in ver:
                return cand
        except Exception:
            continue
    raise RuntimeError("Pinned Anneal rustc (f8a08b688c) not found in ~/.cache/anneal/toolchain")


def extract_asm_functions(asm_text: str) -> dict[str, list[str]]:
    funcs: dict[str, list[str]] = {}
    aliases: list[tuple[str, str]] = []
    cur_name: str | None = None
    cur_insns: list[str] = []
    for raw in asm_text.splitlines():
        line = raw.strip()
        if not line or line.startswith("//") or line.startswith("#") or line.startswith(";"):
            continue
        m_set = re.match(r"^\.set\s+_?([A-Za-z0-9_]+),\s*_?([A-Za-z0-9_]+)$", line)
        if m_set:
            aliases.append((m_set.group(1), m_set.group(2)))
            continue
        m_eq = re.match(r"^_?([A-Za-z0-9_]+)\s*=\s*_?([A-Za-z0-9_]+)$", line)
        if m_eq:
            aliases.append((m_eq.group(1), m_eq.group(2)))
            continue
        m_lbl = re.match(r"^_?([A-Za-z0-9_]+):$", line)
        if m_lbl and m_lbl.group(1).startswith("LBB"):
            continue
        if m_lbl and not m_lbl.group(1).startswith("L") and not m_lbl.group(1).startswith("."):
            if cur_name is not None:
                funcs[cur_name] = cur_insns
            cur_name = m_lbl.group(1)
            cur_insns = []
            continue
        if line.startswith("."):
            if line.startswith(".cfi_endproc") or line.startswith(".subsections_via_symbols"):
                if cur_name is not None:
                    funcs[cur_name] = cur_insns
                    cur_name = None
                    cur_insns = []
            continue
        if cur_name is not None:
            cur_insns.append(re.sub(r"\s+", " ", line))
    if cur_name is not None:
        funcs[cur_name] = cur_insns
    for alias, target in aliases:
        if target in funcs and alias not in funcs:
            funcs[alias] = list(funcs[target])
    return funcs


def probe_multiarch_rustc_asm() -> dict[str, object]:
    rustc = find_pinned_anneal_rustc()
    env = dict(os.environ)
    lib_dir = str(rustc.parent.parent / "lib")
    env["LD_LIBRARY_PATH"] = f"{lib_dir}:{env.get('LD_LIBRARY_PATH', '')}"
    targets = [
        "aarch64-unknown-linux-gnu",
        "aarch64-apple-darwin",
        "riscv64gc-unknown-linux-gnu",
        "x86_64-unknown-linux-gnu",
    ]
    out: dict[str, object] = {
        "rustc_version": subprocess.check_output(
            [str(rustc), "--version", "--verbose"], env=env, text=True
        ).strip(),
        "targets": {},
    }
    with tempfile.TemporaryDirectory() as tmp_s:
        tmp = Path(tmp_s)
        src = tmp / "nocore_atomics.rs"
        src.write_text(NOCORE_ATOMICS_RS)
        for tgt in targets:
            asm_path = tmp / f"{tgt}.s"
            subprocess.run(
                [
                    str(rustc),
                    "-Copt-level=3",
                    "--target",
                    tgt,
                    "--emit=asm",
                    str(src),
                    "-o",
                    str(asm_path),
                ],
                env=env,
                check=True,
            )
            asm_text = asm_path.read_text()
            funcs = extract_asm_functions(asm_text)
            out["targets"][tgt] = {
                "asm_sha256": hashlib.sha256(asm_text.encode()).hexdigest(),
                "functions": funcs,
            }

    # Assertions verifying key hardware/compiler facts + non-vacuity contrasts!
    a64_linux = out["targets"]["aarch64-unknown-linux-gnu"]["functions"]
    a64_apple = out["targets"]["aarch64-apple-darwin"]["functions"]
    rv64 = out["targets"]["riscv64gc-unknown-linux-gnu"]["functions"]
    x64 = out["targets"]["x86_64-unknown-linux-gnu"]["functions"]

    # 1. Identical-code-folding / dependency erasure: lb_rlx == lb_false_dep == lb_branch_hoist
    for arch_name, fn_map in [
        ("aarch64-linux", a64_linux),
        ("aarch64-apple", a64_apple),
        ("riscv64gc", rv64),
        ("x86_64", x64),
    ]:
        assert fn_map["lb_rlx"] == fn_map["lb_false_dep"] == fn_map["lb_branch_hoist"], (
            f"Expected identical emitted code on {arch_name}: {fn_map}"
        )
        # Non-vacuity contrast: lb_data_dep and lb_ctrl_dep MUST NOT collapse to lb_rlx!
        assert fn_map["lb_data_dep"] != fn_map["lb_rlx"], f"Data dep collapsed on {arch_name}"
        assert fn_map["lb_ctrl_dep"] != fn_map["lb_rlx"], f"Ctrl dep collapsed on {arch_name}"
        # LLVM 20 preserves all 3 atomic stores across the conditional arms of lb_cond_overwrite
        # (while PS 2.0 admits (1, 2) both via R->W reordering in the r != 0 arm and if a
        # future optimizer performs atomic dead-store elimination):
        store_insns = [
            i
            for i in fn_map["lb_cond_overwrite"]
            if i.startswith("str ") or i.startswith("sw ") or i.startswith("movl $")
        ]
        assert len(store_insns) == 3, f"Expected 3 stores on {arch_name}: {fn_map['lb_cond_overwrite']}"

    # 2. Check aarch64-apple-darwin `crossbeam_x86_pattern` (`swpal` + `ldapr`, NO `dmb ish`)
    # vs. `portable_fence_sc_pattern` (`swpal` + `dmb ish` + `ldapr`)!
    apple_cb = " ; ".join(a64_apple["crossbeam_x86_pattern"])
    apple_sc = " ; ".join(a64_apple["portable_fence_sc_pattern"])
    assert "swpal" in apple_cb and "ldapr" in apple_cb and "dmb ish" not in apple_cb, apple_cb
    assert "swpal" in apple_sc and "dmb ish" in apple_sc and "ldapr" in apple_sc, apple_sc

    # 3. Check x86_64 `crossbeam_x86_pattern` (`xchgq` + `movq`, zero `mfence` needed on TSO)
    x64_cb = " ; ".join(x64["crossbeam_x86_pattern"])
    assert "xchgq" in x64_cb and "movq" in x64_cb, x64_cb

    return out


# ============================================================================
# Executable Operational Promising 2.0 + Op-SC2' + TargetMemModel Explorer
# ============================================================================


@dataclass(frozen=True)
class ExMsg:
    loc: str
    from_ts: Fraction
    to_ts: Fraction
    val: int
    msg_view: tuple[tuple[str, Fraction], ...]
    promised_by: int | None
    is_cap: bool = False


def view_dict(t: tuple[tuple[str, Fraction], ...]) -> dict[str, Fraction]:
    return dict(t)


def view_tuple(d: dict[str, Fraction]) -> tuple[tuple[str, Fraction], ...]:
    return tuple(sorted((k, v) for k, v in d.items() if v > 0))


def view_get(t: tuple[tuple[str, Fraction], ...], loc: str) -> Fraction:
    for k, v in t:
        if k == loc:
            return v
    return Fraction(0)


def view_bump(t: tuple[tuple[str, Fraction], ...], loc: str, ts: Fraction) -> tuple[tuple[str, Fraction], ...]:
    d = view_dict(t)
    if ts > d.get(loc, Fraction(0)):
        d[loc] = ts
    return view_tuple(d)


def view_join(
    a: tuple[tuple[str, Fraction], ...], b: tuple[tuple[str, Fraction], ...]
) -> tuple[tuple[str, Fraction], ...]:
    d = view_dict(a)
    for k, v in b:
        if v > d.get(k, Fraction(0)):
            d[k] = v
    return view_tuple(d)


def intervals_disjoint(a1: Fraction, b1: Fraction, a2: Fraction, b2: Fraction) -> bool:
    return b1 <= a2 or b2 <= a1


def candidate_slots(
    mem: tuple[ExMsg, ...], loc: str, min_from: Fraction, allow_split: bool = True
) -> list[tuple[Fraction, Fraction]]:
    loc_msgs = sorted(
        [m for m in mem if m.loc == loc and not (m.from_ts == 0 and m.to_ts == 0)],
        key=lambda m: (m.from_ts, m.to_ts),
    )
    slots: list[tuple[Fraction, Fraction]] = []
    # Check gaps before/between existing messages
    prev_end = Fraction(0)
    for m in loc_msgs:
        if allow_split and m.from_ts > prev_end:
            lo = max(prev_end, min_from)
            if lo < m.from_ts:
                # Choose interior sub-interval leaving space on both sides!
                span = m.from_ts - lo
                s_from = lo + span * Fraction(1, 3)
                s_to = lo + span * Fraction(2, 3)
                slots.append((s_from, s_to))
        prev_end = max(prev_end, m.to_ts)
    # Top append slot (leaving open gap `(prev_end, prev_end + 1)` so RMW slots aren't closed
    # and future splits remain possible!)
    top_from = max(prev_end + Fraction(1), min_from + Fraction(1))
    slots.append((top_from, top_from + Fraction(1)))
    return slots


def cap_memory(mem: tuple[ExMsg, ...], locs: tuple[str, ...]) -> tuple[ExMsg, ...]:
    caps: list[ExMsg] = []
    for loc in locs:
        max_to = max((m.to_ts for m in mem if m.loc == loc), default=Fraction(0))
        caps.append(
            ExMsg(
                loc=loc,
                from_ts=max_to,
                to_ts=max_to + Fraction(1),
                val=0,
                msg_view=(),
                promised_by=None,
                is_cap=True,
            )
        )
    return mem + tuple(caps)


@dataclass(frozen=True)
class ThreadSt:
    pc: int
    regs: tuple[tuple[str, int], ...]
    cur: tuple[tuple[str, Fraction], ...] = ()
    acq: tuple[tuple[str, Fraction], ...] = ()
    rel: tuple[tuple[str, Fraction], ...] = ()


def reg_get(regs: tuple[tuple[str, int], ...], name: str) -> int:
    for k, v in regs:
        if k == name:
            return v
    return 0


def reg_set(regs: tuple[tuple[str, int], ...], name: str, val: int) -> tuple[tuple[str, int], ...]:
    d = dict(regs)
    d[name] = val
    return tuple(sorted(d.items()))


def eval_expr(expr, regs: tuple[tuple[str, int], ...]) -> int:
    if isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        return reg_get(regs, expr)
    op = expr[0]
    if op == "zero_dep":
        v = eval_expr(expr[1], regs)
        return (v - v) + expr[2]
    raise ValueError(f"Unknown expr: {expr}")


def thread_has_promise(tid: int, mem: tuple[ExMsg, ...]) -> bool:
    return any(m.promised_by == tid for m in mem)


def single_step_physical(
    tid: int,
    prog: list[tuple],
    st: ThreadSt,
    mem: tuple[ExMsg, ...],
    s_sc: tuple[tuple[str, Fraction], ...],
    model: str,
    drain_on_release_fence: bool = True,
    check_rel_on_fulfill: bool = True,
) -> list[tuple[ThreadSt, tuple[ExMsg, ...], tuple[tuple[str, Fraction], ...]]]:
    if st.pc >= len(prog):
        return []
    ins = prog[st.pc]
    kind = ins[0]
    results = []

    if kind == "load":
        _, reg, loc, ord_ = ins
        min_ts = view_get(st.cur, loc)
        if ord_ == "SeqCst" and model == "portable_cpp20":
            min_ts = max(min_ts, view_get(s_sc, loc))
        for m in mem:
            if m.loc != loc or m.is_cap or m.promised_by == tid or m.to_ts < min_ts:
                continue
            cur1 = view_bump(st.cur, loc, m.to_ts)
            if ord_ in ("Acquire", "AcqRel", "SeqCst"):
                cur2 = view_join(cur1, m.msg_view)
            else:
                cur2 = cur1
            acq2 = view_join(view_bump(st.acq, loc, m.to_ts), m.msg_view)
            results.append(
                (
                    ThreadSt(st.pc + 1, reg_set(st.regs, reg, m.val), cur2, acq2, st.rel),
                    mem,
                    s_sc,
                )
            )

    elif kind == "store":
        _, loc, expr, ord_ = ins
        val = eval_expr(expr, st.regs)
        min_ts = view_get(st.cur, loc)
        # 1. Fresh store
        for from_ts, to_ts in candidate_slots(mem, loc, min_ts):
            cur2 = view_bump(st.cur, loc, to_ts)
            acq2 = view_bump(st.acq, loc, to_ts)
            exp = cur2 if ord_ in ("Release", "AcqRel", "SeqCst") else view_bump(st.rel, loc, to_ts)
            s_sc2 = view_bump(s_sc, loc, to_ts) if ord_ == "SeqCst" else s_sc
            if model == "x86_tso" and ord_ == "SeqCst":
                s_sc2 = view_join(s_sc2, cur2)
                cur2 = view_join(cur2, s_sc2)
                acq2 = cur2
            m = ExMsg(loc, from_ts, to_ts, val, exp, None, False)
            results.append((ThreadSt(st.pc + 1, st.regs, cur2, acq2, st.rel), mem + (m,), s_sc2))
        # 2. Fulfill own Relaxed promise
        if ord_ == "Relaxed":
            for idx, m in enumerate(mem):
                if (
                    m.promised_by == tid
                    and m.loc == loc
                    and m.val == val
                    and not m.is_cap
                    and min_ts <= m.from_ts
                    and (not check_rel_on_fulfill or m.msg_view == view_bump(st.rel, loc, m.to_ts))
                ):
                    cur2 = view_bump(st.cur, loc, m.to_ts)
                    acq2 = view_bump(st.acq, loc, m.to_ts)
                    fulfilled = ExMsg(m.loc, m.from_ts, m.to_ts, m.val, m.msg_view, None, False)
                    mem2 = mem[:idx] + (fulfilled,) + mem[idx + 1 :]
                    results.append((ThreadSt(st.pc + 1, st.regs, cur2, acq2, st.rel), mem2, s_sc))

    elif kind == "rmw_add" or kind == "rmw_xchg":
        _, reg, loc, expr, ord_ = ins
        arg_val = eval_expr(expr, st.regs)
        min_ts = view_get(st.cur, loc)
        for m in mem:
            if m.loc != loc or m.is_cap or m.promised_by == tid or m.to_ts < min_ts:
                continue
            # Check RMW adjacency: find tight `(m.to_ts, to_ts]` disjoint from all other msgs!
            other = [x for x in mem if x.loc == loc and not (x.from_ts == 0 and x.to_ts == 0)]
            next_starts = [x.from_ts for x in other if x.from_ts >= m.to_ts]
            if any(x.from_ts == m.to_ts for x in other):
                continue  # Adjacent RMW slot already occupied (or capped by PS 2.0 cap!)
            to_ts = (
                m.to_ts + (min(next_starts) - m.to_ts) * Fraction(1, 2)
                if next_starts
                else m.to_ts + Fraction(1, 2)
            )
            new_val = (m.val + arg_val) if kind == "rmw_add" else arg_val
            # 2a. Fresh RMW execution
            cur_r = (
                view_join(view_bump(st.cur, loc, m.to_ts), m.msg_view)
                if ord_ in ("Acquire", "AcqRel", "SeqCst")
                else view_bump(st.cur, loc, m.to_ts)
            )
            cur2 = view_bump(cur_r, loc, to_ts)
            acq2 = view_bump(view_join(view_bump(st.acq, loc, m.to_ts), m.msg_view), loc, to_ts)
            exp = (
                view_join(cur2, m.msg_view)
                if ord_ in ("Release", "AcqRel", "SeqCst")
                else view_join(view_bump(st.rel, loc, to_ts), m.msg_view)
            )
            s_sc2 = view_bump(s_sc, loc, to_ts) if ord_ == "SeqCst" else s_sc
            if model == "x86_tso":
                # Every atomic RMW (`lock xadd` / `xchg`) on x86_64 drains TSO store buffer!
                s_sc2 = view_join(s_sc2, cur2)
                cur2 = view_join(cur2, s_sc2)
                acq2 = cur2
                exp = cur2
            new_m = ExMsg(loc, m.to_ts, to_ts, new_val, exp, None, False)
            results.append(
                (
                    ThreadSt(st.pc + 1, reg_set(st.regs, reg, m.val), cur2, acq2, st.rel),
                    mem + (new_m,),
                    s_sc2,
                )
            )
        # 2b. Fulfill promised Relaxed RMW (`ord_ in ("Relaxed", "Acquire")`)
        if ord_ in ("Relaxed", "Acquire"):
            for idx, pm in enumerate(mem):
                if pm.promised_by != tid or pm.loc != loc or pm.is_cap:
                    continue
                for base_m in mem:
                    if (
                        base_m.loc != loc
                        or base_m.is_cap
                        or base_m.promised_by == tid
                        or base_m.to_ts != pm.from_ts
                        or base_m.to_ts < min_ts
                    ):
                        continue
                    expected_val = (base_m.val + arg_val) if kind == "rmw_add" else arg_val
                    exp = view_join(view_bump(st.rel, loc, pm.to_ts), base_m.msg_view)
                    if pm.val == expected_val and pm.msg_view == exp:
                        cur_r = (
                            view_join(view_bump(st.cur, loc, base_m.to_ts), base_m.msg_view)
                            if ord_ == "Acquire"
                            else view_bump(st.cur, loc, base_m.to_ts)
                        )
                        cur2 = view_bump(cur_r, loc, pm.to_ts)
                        acq2 = view_bump(
                            view_join(view_bump(st.acq, loc, base_m.to_ts), base_m.msg_view),
                            loc,
                            pm.to_ts,
                        )
                        fulfilled = ExMsg(
                            pm.loc, pm.from_ts, pm.to_ts, pm.val, pm.msg_view, None, False
                        )
                        mem2 = mem[:idx] + (fulfilled,) + mem[idx + 1 :]
                        results.append(
                            (
                                ThreadSt(
                                    st.pc + 1, reg_set(st.regs, reg, base_m.val), cur2, acq2, st.rel
                                ),
                                mem2,
                                s_sc,
                            )
                        )

    elif kind == "fence":
        _, ord_ = ins
        if drain_on_release_fence and ord_ in ("Release", "AcqRel", "SeqCst"):
            if thread_has_promise(tid, mem):
                return []
        cur2 = st.acq if ord_ in ("Acquire", "AcqRel", "SeqCst") else st.cur
        rel2 = cur2 if ord_ in ("Release", "AcqRel", "SeqCst") else st.rel
        s_sc2 = s_sc
        if ord_ == "SeqCst":
            joined = view_join(s_sc, cur2)
            cur2 = joined
            rel2 = joined
            s_sc2 = joined
        results.append((ThreadSt(st.pc + 1, st.regs, cur2, max_v(st.acq, cur2), rel2), mem, s_sc2))

    elif kind == "cfence_sc":
        results.append((ThreadSt(st.pc + 1, st.regs, st.cur, st.acq, st.rel), mem, s_sc))

    elif kind == "br_eq":
        _, reg, target_val, jump_pc = ins
        next_pc = jump_pc if reg_get(st.regs, reg) == target_val else st.pc + 1
        results.append((ThreadSt(next_pc, st.regs, st.cur, st.acq, st.rel), mem, s_sc))

    elif kind == "jmp":
        _, jump_pc = ins
        results.append((ThreadSt(jump_pc, st.regs, st.cur, st.acq, st.rel), mem, s_sc))

    return results


def max_v(a, b):
    return view_join(a, b)


def can_certify(
    tid: int,
    prog: list[tuple],
    st: ThreadSt,
    mem: tuple[ExMsg, ...],
    s_sc: tuple[tuple[str, Fraction], ...],
    locs: tuple[str, ...],
    model: str,
    use_cap: bool = True,
    drain_on_release_fence: bool = True,
    check_rel_on_fulfill: bool = True,
) -> bool:
    if not thread_has_promise(tid, mem):
        return True
    start_mem = cap_memory(mem, locs) if use_cap else mem
    queue = [(st, start_mem, s_sc, 0)]
    seen = {(st, start_mem, s_sc)}
    while queue:
        cur_st, cur_mem, cur_sc, depth = queue.pop()
        if not thread_has_promise(tid, cur_mem):
            return True
        if depth >= 8:
            continue
        for nxt_st, nxt_mem, nxt_sc in single_step_physical(
            tid,
            prog,
            cur_st,
            cur_mem,
            cur_sc,
            model,
            drain_on_release_fence,
            check_rel_on_fulfill,
        ):
            if not thread_has_promise(tid, nxt_mem):
                return True
            key = (nxt_st, nxt_mem, nxt_sc)
            if key not in seen:
                seen.add(key)
                queue.append((nxt_st, nxt_mem, nxt_sc, depth + 1))
    return False


def explore_litmus(
    progs: list[list[tuple]],
    locs: tuple[str, ...],
    possible_promise_vals: tuple[int, ...] = (1,),
    allow_promises: bool = True,
    model: str = "portable_cpp20",
    use_cap: bool = True,
    drain_on_release_fence: bool = True,
    allow_rmw_promise: bool = False,
    check_rel_on_fulfill: bool = True,
) -> tuple[set[tuple[tuple[str, int], ...]], bool]:
    init_mem = tuple(ExMsg(loc, Fraction(0), Fraction(0), 0, (), None, False) for loc in locs)
    init_threads = tuple(ThreadSt(0, ()) for _ in progs)
    start = (init_threads, init_mem, ())
    queue = [start]
    seen = {start}
    outcomes: set[tuple[tuple[str, int], ...]] = set()
    saw_stuck_promise = False

    while queue:
        threads, mem, s_sc = queue.pop()
        all_halted = all(threads[i].pc >= len(progs[i]) for i in range(len(progs)))
        if all_halted:
            if any(m.promised_by is not None for m in mem):
                saw_stuck_promise = True
            else:
                flat_regs: list[tuple[str, int]] = []
                for i, tst in enumerate(threads):
                    for k, v in tst.regs:
                        flat_regs.append((f"T{i}.{k}", v))
                outcomes.add(tuple(sorted(flat_regs)))
            continue

        for tid, prog in enumerate(progs):
            tst = threads[tid]
            if tst.pc >= len(prog):
                continue
            tid_succ = 0
            # Physical step
            for nst, nmem, nsc in single_step_physical(
                tid, prog, tst, mem, s_sc, model, drain_on_release_fence, check_rel_on_fulfill
            ):
                if can_certify(
                    tid,
                    prog,
                    nst,
                    nmem,
                    nsc,
                    locs,
                    model,
                    use_cap,
                    drain_on_release_fence,
                    check_rel_on_fulfill,
                ):
                    tid_succ += 1
                    nxt = (threads[:tid] + (nst,) + threads[tid + 1 :], nmem, nsc)
                    if nxt not in seen:
                        seen.add(nxt)
                        queue.append(nxt)
            if thread_has_promise(tid, mem) and tid_succ == 0:
                saw_stuck_promise = True

            # Promise step (cap max 1 outstanding promise per thread for bounded litmus tests)
            if allow_promises and model == "portable_cpp20" and not thread_has_promise(tid, mem):
                for loc in locs:
                    min_ts = view_get(tst.cur, loc)
                    # Standard non-RMW Relaxed store promise
                    for from_ts, to_ts in candidate_slots(mem, loc, min_ts, allow_split=False):
                        exp = view_bump(tst.rel, loc, to_ts)
                        for pval in possible_promise_vals:
                            pm = ExMsg(loc, from_ts, to_ts, pval, exp, tid, False)
                            nmem = mem + (pm,)
                            if can_certify(
                                tid,
                                prog,
                                tst,
                                nmem,
                                s_sc,
                                locs,
                                model,
                                use_cap,
                                drain_on_release_fence,
                                check_rel_on_fulfill,
                            ):
                                nxt = (threads, nmem, s_sc)
                                if nxt not in seen:
                                    seen.add(nxt)
                                    queue.append(nxt)
                    # Adjacent RMW Relaxed promise (`fetch_add(Relaxed)`)
                    if allow_rmw_promise:
                        for base_m in mem:
                            if (
                                base_m.loc != loc
                                or base_m.is_cap
                                or base_m.promised_by == tid
                                or base_m.to_ts < min_ts
                            ):
                                continue
                            other = [
                                x
                                for x in mem
                                if x.loc == loc and not (x.from_ts == 0 and x.to_ts == 0)
                            ]
                            if any(x.from_ts == base_m.to_ts for x in other):
                                continue
                            to_ts = base_m.to_ts + Fraction(1, 2)
                            exp = view_join(view_bump(tst.rel, loc, to_ts), base_m.msg_view)
                            for pval in possible_promise_vals:
                                pm = ExMsg(loc, base_m.to_ts, to_ts, pval, exp, tid, False)
                                nmem = mem + (pm,)
                                if can_certify(
                                    tid,
                                    prog,
                                    tst,
                                    nmem,
                                    s_sc,
                                    locs,
                                    model,
                                    use_cap,
                                    drain_on_release_fence,
                                    check_rel_on_fulfill,
                                ):
                                    nxt = (threads, nmem, s_sc)
                                    if nxt not in seen:
                                        seen.add(nxt)
                                        queue.append(nxt)

    return outcomes, saw_stuck_promise


def run_ps2_litmus_suite() -> dict[str, object]:
    results: dict[str, object] = {}

    lb_rlx = [
        [("load", "r0", "x", "Relaxed"), ("store", "y", 1, "Relaxed")],
        [("load", "r1", "y", "Relaxed"), ("store", "x", 1, "Relaxed")],
    ]
    pf_lb, _ = explore_litmus(lb_rlx, ("x", "y"), allow_promises=False)
    ps2_lb, stuck_lb = explore_litmus(lb_rlx, ("x", "y"), allow_promises=True)
    assert (("T0.r0", 1), ("T1.r1", 1)) not in pf_lb
    assert (("T0.r0", 1), ("T1.r1", 1)) in ps2_lb and not stuck_lb
    results["LB+rlx"] = {
        "promise_free_allows_1_1": False,
        "ps2_allows_1_1": True,
        "ps2_outcomes": [dict(o) for o in sorted(ps2_lb)],
    }

    lb_false_dep = [
        [("load", "r0", "x", "Relaxed"), ("store", "y", ("zero_dep", "r0", 1), "Relaxed")],
        [("load", "r1", "y", "Relaxed"), ("store", "x", ("zero_dep", "r1", 1), "Relaxed")],
    ]
    ps2_fdep, _ = explore_litmus(lb_false_dep, ("x", "y"))
    assert (("T0.r0", 1), ("T1.r1", 1)) in ps2_fdep
    results["LB+false_dep"] = {"ps2_allows_1_1": True}

    lb_branch_hoist = [
        [
            ("load", "r0", "x", "Relaxed"),
            ("br_eq", "r0", 1, 4),
            ("store", "y", 1, "Relaxed"),
            ("jmp", 5),
            ("store", "y", 1, "Relaxed"),
        ],
        [("load", "r1", "y", "Relaxed"), ("store", "x", 1, "Relaxed")],
    ]
    ps2_bh, _ = explore_litmus(lb_branch_hoist, ("x", "y"))
    assert (("T0.r0", 1), ("T1.r1", 1)) in ps2_bh
    results["LB+branch_hoist"] = {"ps2_allows_1_1": True}

    lb_cond_ov = [
        [
            ("load", "r0", "x", "Relaxed"),
            ("br_eq", "r0", 0, 3),
            ("jmp", 4),
            ("store", "y", 1, "Relaxed"),
            ("store", "y", 2, "Relaxed"),
        ],
        [
            ("load", "r1", "y", "Relaxed"),
            ("br_eq", "r1", 2, 3),
            ("jmp", 4),
            ("store", "x", 1, "Relaxed"),
        ],
    ]
    ps2_cov, stuck_cov = explore_litmus(lb_cond_ov, ("x", "y"), possible_promise_vals=(1, 2))
    assert (("T0.r0", 1), ("T1.r1", 2)) in ps2_cov and not stuck_cov
    results["LB+cond_overwrite"] = {"ps2_allows_1_2": True}

    lb_rlx_rmw = [
        [("load", "r0", "x", "Relaxed"), ("rmw_add", "old", "y", 1, "Relaxed")],
        [("load", "r1", "y", "Relaxed"), ("store", "x", 1, "Relaxed")],
    ]
    ps2_rmw, stuck_rmw = explore_litmus(
        lb_rlx_rmw, ("x", "y"), allow_rmw_promise=True
    )
    assert any(dict(o)["T0.r0"] == 1 and dict(o)["T1.r1"] == 1 for o in ps2_rmw) and not stuck_rmw
    results["LB+rlx_fetch_add"] = {"ps2_allows_1_1": True}

    lb_data_dep = [
        [("load", "r0", "x", "Relaxed"), ("store", "y", "r0", "Relaxed")],
        [("load", "r1", "y", "Relaxed"), ("store", "x", "r1", "Relaxed")],
    ]
    ps2_ddep, _ = explore_litmus(lb_data_dep, ("x", "y"), possible_promise_vals=(0, 1))
    assert ps2_ddep == {(("T0.r0", 0), ("T1.r1", 0))}, ps2_ddep
    results["LB+data_dep_OOTA"] = {"ps2_allows_1_1": False, "outcomes": [dict(o) for o in ps2_ddep]}

    lb_ctrl_dep = [
        [
            ("load", "r0", "x", "Relaxed"),
            ("br_eq", "r0", 1, 3),
            ("jmp", 4),
            ("store", "y", 1, "Relaxed"),
        ],
        [
            ("load", "r1", "y", "Relaxed"),
            ("br_eq", "r1", 1, 3),
            ("jmp", 4),
            ("store", "x", 1, "Relaxed"),
        ],
    ]
    ps2_cdep, _ = explore_litmus(lb_ctrl_dep, ("x", "y"))
    assert ps2_cdep == {(("T0.r0", 0), ("T1.r1", 0))}, ps2_cdep
    results["LB+ctrl_dep"] = {"ps2_allows_1_1": False}

    lb_rel_acq = [
        [("load", "r0", "x", "Acquire"), ("store", "y", 1, "Release")],
        [("load", "r1", "y", "Acquire"), ("store", "x", 1, "Release")],
    ]
    ps2_ra, _ = explore_litmus(lb_rel_acq, ("x", "y"))
    assert (("T0.r0", 1), ("T1.r1", 1)) not in ps2_ra
    results["LB+rel+acq"] = {"ps2_allows_1_1": False}

    # Release-fence LB + non-vacuity ablation!
    lb_frel_acq = [
        [("load", "r0", "x", "Acquire"), ("fence", "Release"), ("store", "y", 1, "Relaxed")],
        [("load", "r1", "y", "Acquire"), ("fence", "Release"), ("store", "x", 1, "Relaxed")],
    ]
    ps2_frel, _ = explore_litmus(
        lb_frel_acq, ("x", "y"), drain_on_release_fence=True, check_rel_on_fulfill=True
    )
    buggy_frel, _ = explore_litmus(
        lb_frel_acq, ("x", "y"), drain_on_release_fence=False, check_rel_on_fulfill=False
    )
    assert (("T0.r0", 1), ("T1.r1", 1)) not in ps2_frel
    assert (("T0.r0", 1), ("T1.r1", 1)) in buggy_frel  # Non-vacuity control!
    results["LB+frel+acq"] = {
        "ps2_allows_1_1": False,
        "ablation_no_fence_drain_and_no_rel_view_falsely_allows_1_1": True,
    }

    # PS 2.0 `capMem` RMW-steal non-vacuity control!
    rmw_steal = [
        [
            ("rmw_xchg", "r0", "z", 1, "Relaxed"),
            ("br_eq", "r0", 0, 3),
            ("jmp", 4),
            ("store", "y", 1, "Relaxed"),
        ],
        [("load", "r1", "y", "Relaxed"), ("rmw_xchg", "r2", "z", 2, "Relaxed")],
    ]
    _, stuck_capped = explore_litmus(rmw_steal, ("y", "z"), use_cap=True)
    _, stuck_uncapped = explore_litmus(rmw_steal, ("y", "z"), use_cap=False)
    assert stuck_capped is False
    assert stuck_uncapped is True  # Uncapped PS 1.0-style RMW certification gets stuck!
    results["PS2_capMem_rmw_steal_control"] = {
        "capped_stuck_promise": stuck_capped,
        "uncapped_ablation_stuck_promise": stuck_uncapped,
    }

    # Crossbeam x86 pattern: portable_cpp20 vs x86_tso!
    cb_pattern = [
        [
            ("rmw_xchg", "old0", "x", 1, "SeqCst"),
            ("cfence_sc",),
            ("load", "r0", "y", "Acquire"),
        ],
        [
            ("rmw_xchg", "old1", "y", 1, "SeqCst"),
            ("cfence_sc",),
            ("load", "r1", "x", "Acquire"),
        ],
    ]
    cb_portable, _ = explore_litmus(cb_pattern, ("x", "y"), model="portable_cpp20")
    cb_tso, _ = explore_litmus(cb_pattern, ("x", "y"), model="x86_tso")
    allows_00_portable = any(
        dict(o)["T0.r0"] == 0 and dict(o)["T1.r1"] == 0 for o in cb_portable
    )
    allows_00_tso = any(dict(o)["T0.r0"] == 0 and dict(o)["T1.r1"] == 0 for o in cb_tso)
    assert allows_00_portable is True
    assert allows_00_tso is False
    results["crossbeam_xchg_cfence_acq"] = {
        "portable_cpp20_allows_0_0": allows_00_portable,
        "x86_tso_allows_0_0": allows_00_tso,
    }

    return results


def to_wire(avail: dict[str, str]) -> list[list[str]]:
    o = [avail[k] for k in OLEAN_PARTS if k in avail]
    i = [avail[k] for k in IR_PARTS if k in avail]
    return [o, i]


def verify_lean_5_gates() -> dict[str, object]:
    with tempfile.TemporaryDirectory() as tmp_s:
        tmp = Path(tmp_s)
        if ANNEAL_ROOT_ENV:
            anneal_root = Path(ANNEAL_ROOT_ENV)
        else:
            ext = tmp / "zc_extract"
            ext.mkdir(parents=True, exist_ok=True)
            archive_bytes = subprocess.check_output(
                ["git", "-C", str(ZEROCOPY_REPO), "archive", ZEROCOPY_REV, "anneal"]
            )
            subprocess.run(["tar", "-x", "-C", str(ext)], input=archive_bytes, check=True)
            anneal_root = ext / "anneal"
        return _verify_lean_5_gates_in_tmp(tmp, anneal_root)


def _verify_lean_5_gates_in_tmp(tmp: Path, ANNEAL_ROOT: Path) -> dict[str, object]:
    lock_data = json.loads((ANNEAL_ROOT / "trusted/lean/foundation-lock.json").read_text())
    inspector_orig = ANNEAL_ROOT / "trusted/audit/TrustedBoundary.lean"
    lean_sha = sha256_path(LEAN_BIN)
    lean_ver = subprocess.check_output(
        [str(LEAN_BIN), "--version"], env=CLEAN_ENV, text=True
    ).strip()
    assert lock_data["distributions"].get(lean_ver) == lean_sha

    artifacts: dict[str, list[list[str]]] = {}
    for fmod, rec in sorted(lock_data["modules"].items()):
        rel_mod = fmod.replace(".", "/")
        avail: dict[str, str] = {}
        for part in ALL_PARTS:
            expected = rec["parts"][part]
            installed = LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}"
            if expected is not None:
                assert installed.exists() and sha256_path(installed) == expected
                avail[part] = str(installed)
        artifacts[fmod] = to_wire(avail)

    foundation_mods = sorted(lock_data["modules"].keys())
    graph = dict(lock_data["graph"])
    axioms = lock_data["axioms"]

    trusted_mods = [
        ("Trusted", ANNEAL_ROOT / "trusted/lean/Trusted.lean"),
        ("Trusted.MirAst.Types", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Types.lean"),
        ("Trusted.MirAst.Places", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Places.lean"),
        ("Trusted.MirAst.Rvalues", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Rvalues.lean"),
        ("Trusted.MirAst.Statements", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Statements.lean"),
        ("Trusted.MirAst.Terminators", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Terminators.lean"),
        ("Trusted.MirAst.Body", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst/Body.lean"),
        ("Trusted.MirAst", ANNEAL_ROOT / "trusted/lean/Trusted/MirAst.lean"),
        ("Trusted.MirModel", ANNEAL_ROOT / "trusted/lean/Trusted/MirModel.lean"),
        ("Trusted.MirSemantics.Enum", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Enum.lean"),
        ("Trusted.MirSemantics.Bytes", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Bytes.lean"),
        ("Trusted.MirSemantics.Layout", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Layout.lean"),
        ("Trusted.MirSemantics.Memory", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Memory.lean"),
        ("Trusted.MirSemantics.State", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/State.lean"),
        ("Trusted.MirSemantics.Ops", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Ops.lean"),
        ("Trusted.MirSemantics.Step", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Step.lean"),
        ("Trusted.MirSemantics.Boundary", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/Boundary.lean"),
        ("Trusted.MirSemantics.CanaryFixtures", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean"),
        ("Trusted.MirSemantics", ANNEAL_ROOT / "trusted/lean/Trusted/MirSemantics.lean"),
    ]
    theory_mods = [
        ("Anneal.NatBitwise", ANNEAL_ROOT / "theory/Anneal/NatBitwise.lean"),
        ("Anneal.MirWp.Core", ANNEAL_ROOT / "theory/Anneal/MirWp/Core.lean"),
        ("Anneal.MirWp.Scalars", ANNEAL_ROOT / "theory/Anneal/MirWp/Scalars.lean"),
        ("Anneal.MirWp.Reflection", ANNEAL_ROOT / "theory/Anneal/MirWp/Reflection.lean"),
        ("Anneal.MirWp.Execution", ANNEAL_ROOT / "theory/Anneal/MirWp/Execution.lean"),
        ("Anneal.MirWp.Canaries", ANNEAL_ROOT / "theory/Anneal/MirWp/Canaries.lean"),
        ("Anneal.MirWp", ANNEAL_ROOT / "theory/Anneal/MirWp.lean"),
        ("Anneal.Core.SepPCM", ANNEAL_ROOT / "theory/Anneal/Core/SepPCM.lean"),
        ("Anneal.PromisingReductionProof", PROOF_SRC),
    ]
    all_mods = trusted_mods + theory_mods

    if True:
        inspector = tmp / "TrustedBoundary.lean"
        shutil.copy2(inspector_orig, inspector)

        staged = []
        src_map = {}
        for m, p in all_mods:
            dst = tmp / "src" / (m.replace(".", "/") + ".lean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(p, dst)
            staged.append([m, str(dst)])
            src_map[m] = dst

        # Gate 1: Preflight
        pf_req = tmp / "pf_req.json"
        pf_res = tmp / "pf_res.json"
        pf_req.write_text(
            json.dumps(
                {
                    "mode": "preflight",
                    "sysroot": str(LEAN_PREFIX),
                    "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
                    "foundation": foundation_mods,
                    "graph": graph,
                    "axioms": axioms,
                    "sources": staged,
                }
            )
        )
        subprocess.run(
            [str(LEAN_BIN), "-j1", "-M2048", "--run", str(inspector), str(pf_req), str(pf_res)],
            cwd=tmp,
            env=CLEAN_ENV,
            check=True,
        )
        pf_data = json.loads(pf_res.read_text())
        assert pf_data["ok"] is True, pf_data

        imports_by_mod = {}
        module_tiers = []
        for hdr in pf_data["result"]["headers"]:
            m = hdr["module"]
            imports_by_mod[m] = hdr["imports"]
            if m.startswith("Trusted"):
                module_tiers.append([m, hdr["trustTier"]])
            else:
                assert hdr.get("trustTier") is None

        staged_names = {m for m, _ in all_mods}
        topo_order: list[str] = []
        done: set[str] = set()

        def visit_mod(m: str) -> None:
            if m in done or m not in staged_names:
                return
            for imp in imports_by_mod[m]:
                visit_mod(imp["module"])
            done.add(m)
            topo_order.append(m)

        for m, _ in all_mods:
            visit_mod(m)

        # Gate 2: Compile (-t0 -DwarningAsError=true)
        out_lib = tmp / "lib"
        for m in topo_order:
            setup_p = tmp / f"{m}.setup.json"
            setup_p.write_text(
                json.dumps(
                    {
                        "name": m,
                        "isModule": False,
                        "imports": imports_by_mod[m],
                        "importArts": artifacts,
                        "dynlibs": [],
                        "plugins": [],
                        "options": {},
                    }
                )
            )
            olean_out = out_lib / f"{m.replace('.', '/')}.olean"
            olean_out.parent.mkdir(parents=True, exist_ok=True)
            res = subprocess.run(
                [
                    str(LEAN_BIN),
                    "-j1",
                    "-M2048",
                    "-t0",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-DwarningAsError=true",
                    "--setup",
                    str(setup_p),
                    "-o",
                    str(olean_out),
                    str(src_map[m]),
                ],
                cwd=tmp,
                env=CLEAN_ENV,
                capture_output=True,
                text=True,
            )
            if res.returncode != 0 or res.stdout != "" or res.stderr != "":
                raise RuntimeError(
                    f"Compile failed on {m}: rc={res.returncode}\nout={res.stdout}\nerr={res.stderr}"
                )
            avail_m = {}
            stem = str(olean_out)[: -len("olean")]
            for part in ALL_PARTS:
                cand = Path(f"{stem}{part}")
                if cand.exists():
                    avail_m[part] = str(cand)
            artifacts[m] = to_wire(avail_m)
            graph[m] = imports_by_mod[m]

        # Gate 3: Audit (fresh kernel replay)
        aud_req = tmp / "aud_req.json"
        aud_res = tmp / "aud_res.json"
        aud_req.write_text(
            json.dumps(
                {
                    "mode": "audit",
                    "sysroot": str(LEAN_PREFIX),
                    "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
                    "foundation": foundation_mods,
                    "graph": graph,
                    "axioms": axioms,
                    "trusted": [m for m, _ in trusted_mods],
                    "theory": [m for m, _ in theory_mods],
                    "moduleTiers": module_tiers,
                    "requireMirWp": True,
                }
            )
        )
        subprocess.run(
            [str(LEAN_BIN), "-j1", "-M2048", "--run", str(inspector), str(aud_req), str(aud_res)],
            cwd=tmp,
            env=CLEAN_ENV,
            check=True,
        )
        aud_data = json.loads(aud_res.read_text())
        assert aud_data["ok"] is True and aud_data["result"]["replay"] is True

        # Gate 4: CheckEnvConstants (`unsafeRec=0, hasSorry=0`)
        chk_src = tmp / "CheckEnvConstants.lean"
        chk_src.write_text(
            """import Lean.Environment
import Lean.Util.Sorry

open Lean

def constantHasSorry (ci : ConstantInfo) : Bool :=
  ci.type.hasSorry ||
    (ci.value? (allowOpaque := true)).any Expr.hasSorry ||
    match ci with
    | .recInfo v => v.rules.any (·.rhs.hasSorry)
    | _ => false

def main (args : List String) : IO UInt32 := do
  let [reqPath] := args
    | IO.eprintln "expected request json"; return 2
  let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile reqPath)
  let sysroot ← IO.ofExcept <| j.getObjValAs? String "sysroot"
  initSearchPath sysroot
  let entries ← IO.ofExcept <|
    j.getObjValAs? (Array (String × Array (Array String))) "artifacts"
  let arts : NameMap ImportArtifacts :=
    entries.foldl (init := {}) fun acc (n, parts) =>
      acc.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  let rootsRaw ← IO.ofExcept <| j.getObjValAs? (Array String) "roots"
  let repoModsRaw ← IO.ofExcept <| j.getObjValAs? (Array String) "repoModules"
  let repoModSet : NameSet := .ofList (repoModsRaw.toList.map String.toName)
  let env ← importModules (rootsRaw.map fun n => { module := n.toName }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false)
    (level := .private) (arts := arts)
  let mut totalConsts := 0
  let mut totalExtra := 0
  let mut nUnsafe := 0
  let mut nPartial := 0
  let mut nUnsafeRec := 0
  let mut nAxiom := 0
  let mut nOpaque := 0
  let mut nSorry := 0
  for m in env.header.modules, data in env.header.moduleData do
    if repoModSet.contains m.module then
      totalConsts := totalConsts + data.constants.size
      totalExtra := totalExtra + data.extraConstNames.size
      for ci in data.constants do
        if ci.isUnsafe then nUnsafe := nUnsafe + 1
        if ci.isPartial then nPartial := nPartial + 1
        if (ci.name.toString.splitOn "_unsafe_rec").length > 1 then nUnsafeRec := nUnsafeRec + 1
        if ci.isAxiom then nAxiom := nAxiom + 1
        if ci matches .opaqueInfo _ then nOpaque := nOpaque + 1
        if constantHasSorry ci then nSorry := nSorry + 1
      for en in data.extraConstNames do
        if (en.toString.splitOn "_unsafe_rec").length > 1 then nUnsafeRec := nUnsafeRec + 1
  IO.println s!"ENV_CHECK_SUMMARY: total={totalConsts} extra={totalExtra} isUnsafe={nUnsafe} isPartial={nPartial} unsafeRec={nUnsafeRec} isAxiom={nAxiom} isOpaque={nOpaque} hasSorry={nSorry}"
  return if nUnsafe == 0 && nPartial == 0 && nUnsafeRec == 0 && nAxiom == 0 && nOpaque == 0 && nSorry == 0 then 0 else 1
"""
        )
        chk_req = tmp / "chk_req.json"
        chk_req.write_text(
            json.dumps(
                {
                    "sysroot": str(LEAN_PREFIX),
                    "artifacts": [[k, v] for k, v in sorted(artifacts.items())],
                    "roots": foundation_mods + [m for m, _ in all_mods],
                    "repoModules": ["Anneal.PromisingReductionProof"],
                }
            )
        )
        res_chk = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "--run",
                str(chk_src),
                str(chk_req),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
            check=True,
        )
        assert "unsafeRec=0 isAxiom=0 isOpaque=0 hasSorry=0" in res_chk.stdout, res_chk.stdout

        # Gate 5: `#print axioms`
        ax_lines = ["prelude", "import Anneal.PromisingReductionProof", ""] + [
            f"#print axioms {t}" for t in THEOREMS
        ]
        ax_src = tmp / "Ax.lean"
        ax_src.write_text("\n".join(ax_lines) + "\n")
        ax_setup = tmp / "Ax.setup.json"
        ax_setup.write_text(
            json.dumps(
                {
                    "name": "Ax",
                    "isModule": False,
                    "imports": [
                        {
                            "module": "Anneal.PromisingReductionProof",
                            "importAll": False,
                            "isExported": True,
                            "isMeta": False,
                        }
                    ],
                    "importArts": artifacts,
                    "dynlibs": [],
                    "plugins": [],
                    "options": {},
                }
            )
        )
        res_ax = subprocess.run(
            [
                str(LEAN_BIN),
                "-j1",
                "-M2048",
                "-t0",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "--setup",
                str(ax_setup),
                str(ax_src),
            ],
            cwd=tmp,
            env=CLEAN_ENV,
            capture_output=True,
            text=True,
            check=True,
        )
        for line in res_ax.stdout.splitlines():
            assert "sorryAx" not in line and "ofReduceBool" not in line, line

        return {
            "proof_lines": len(PROOF_SRC.read_text().splitlines()),
            "proof_sha256": sha256_path(PROOF_SRC),
            "preflight_ok": True,
            "audit_ok": aud_data["ok"],
            "replay": aud_data["result"]["replay"],
            "replayed_declarations": aud_data["result"]["replayedDeclarations"],
            "compiler_only_names": aud_data["result"]["compilerOnlyNames"],
            "env_constants_check": res_ax.returncode == 0 and res_chk.stdout.strip(),
            "axioms_output": res_ax.stdout.strip(),
        }


def main() -> int:
    asm_out = probe_multiarch_rustc_asm()
    litmus_out = run_ps2_litmus_suite()
    lean_out = verify_lean_5_gates()
    summary = {
        "multiarch_asm": asm_out,
        "ps2_litmus": litmus_out,
        "lean_5_gates": lean_out,
    }
    receipt_path = Path(__file__).resolve().parent / "verify_promising2_receipt.json"
    receipt_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "ALL_CHECKS_PASSED",
                "proof_lines": lean_out["proof_lines"],
                "proof_sha256": lean_out["proof_sha256"],
                "replayed_declarations": lean_out["replayed_declarations"],
                "env_constants_check": lean_out["env_constants_check"],
                "axioms": lean_out["axioms_output"].splitlines(),
                "litmus_keys": sorted(litmus_out.keys()),
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
