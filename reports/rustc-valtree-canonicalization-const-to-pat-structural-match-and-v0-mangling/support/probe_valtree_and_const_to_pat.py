#!/usr/bin/env python3
"""Empirical probe for rustc ValTree canonicalization, const_to_pat structural
matching, Miri padding uninitialization, array-pattern stack overflow, and v0
const-generic symbol mangling.

Usage:
    python3 probe_valtree_and_const_to_pat.py [--output <json_path>]

Requirements:
    - Nightly rustc (tested on rustc 1.98.0-nightly and 1.102.0-nightly)
    - cargo + miri component (for Miri padding-uninit checks)
    - nm or llvm-nm (for v0 symbol extraction)
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


def _find_tool(name: str, extra_dirs: list[Path] | None = None) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    for d in extra_dirs or []:
        cand = d / name
        if cand.is_file() and os.access(cand, os.X_OK):
            return str(cand)
    return None


def _toolchain_paths() -> tuple[str, str, str | None, str | None]:
    env_extra: list[Path] = []
    home = Path.home()
    cargo_bin = home / ".cargo" / "bin"
    if cargo_bin.is_dir():
        env_extra.append(cargo_bin)

    rustc = _find_tool("rustc", env_extra)
    cargo = _find_tool("cargo", env_extra)
    if not rustc or not cargo:
        raise RuntimeError("rustc and cargo must be installed and on PATH (or ~/.cargo/bin)")

    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    sysroot_p = Path(sysroot)
    llvm_bins = list(sysroot_p.glob("lib/rustlib/*/bin"))
    nm_bin = _find_tool("llvm-nm", llvm_bins) or _find_tool("nm")
    miri_bin = _find_tool("cargo-miri", [sysroot_p / "bin", *env_extra])
    return rustc, cargo, nm_bin, miri_bin


def _scrub(text: str, tmp_root: str) -> str:
    """Remove ephemeral temp-directory paths and home paths from diagnostic text."""
    out = text.replace(tmp_root, "<TMPDIR>")
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    return out


def _run_rustc(
    rustc: str,
    src_path: Path,
    out_path: Path,
    extra_args: list[str] | None = None,
    timeout: int = 60,
    env_override: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    cmd = [rustc, "--edition=2024", str(src_path), "-o", str(out_path)]
    if extra_args:
        cmd.extend(extra_args)
    env = os.environ.copy()
    if env_override:
        env.update(env_override)
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)


def _compile_and_run(
    rustc: str,
    tmp_dir: Path,
    name: str,
    code: str,
    extra_args: list[str] | None = None,
    timeout: int = 60,
    env_override: dict[str, str] | None = None,
) -> dict[str, Any]:
    src = tmp_dir / f"{name}.rs"
    exe = tmp_dir / f"{name}.bin"
    src.write_text(code, encoding="utf-8")
    t0 = time.monotonic()
    print(f"[probe] {name} ...", flush=True)
    try:
        comp = _run_rustc(
            rustc, src, exe, extra_args=extra_args, timeout=timeout, env_override=env_override
        )
    except subprocess.TimeoutExpired:
        print(f"[probe] {name} -> TIMEOUT", flush=True)
        return {"compile_rc": None, "timed_out": True}
    dt_ms = round((time.monotonic() - t0) * 1000.0, 2)
    print(f"[probe] {name} -> rc={comp.returncode} ({dt_ms} ms)", flush=True)

    tmp_s = str(tmp_dir)
    res: dict[str, Any] = {
        "compile_rc": comp.returncode,
        "compile_elapsed_ms": dt_ms,
        "stderr_head": _scrub(comp.stderr, tmp_s)[:1800],
    }
    if comp.returncode == 0 and exe.is_file():
        run = subprocess.run([str(exe)], capture_output=True, text=True, timeout=30)
        res["run_rc"] = run.returncode
        res["stdout"] = _scrub(run.stdout.strip(), tmp_s)
        res["run_stderr"] = _scrub(run.stderr.strip(), tmp_s)[:1000]
    return res


def _run_miri_case(
    cargo: str,
    rustc: str,
    tmp_dir: Path,
    name: str,
    main_rs: str,
) -> dict[str, Any]:
    proj = tmp_dir / f"miri_{name}"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        f'[package]\nname = "miri_{name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(main_rs, encoding="utf-8")

    env = os.environ.copy()
    rustc_dir = str(Path(rustc).parent)
    env["PATH"] = f"{rustc_dir}:{env.get('PATH', '')}"
    env["CARGO_TARGET_DIR"] = str(tmp_dir / "miri_target")
    env["MIRIFLAGS"] = "-Zmiri-disable-isolation"

    t0 = time.monotonic()
    print(f"[miri] {name} ...", flush=True)
    proc = subprocess.run(
        [cargo, "miri", "run", "--quiet", "--offline"],
        cwd=str(proj),
        capture_output=True,
        text=True,
        timeout=180,
        env=env,
    )
    dt_ms = round((time.monotonic() - t0) * 1000.0, 2)
    print(f"[miri] {name} -> rc={proc.returncode} ({dt_ms} ms)", flush=True)
    tmp_s = str(tmp_dir)
    return {
        "rc": proc.returncode,
        "elapsed_ms": dt_ms,
        "stdout": _scrub(proc.stdout.strip(), tmp_s)[:1000],
        "stderr_head": _scrub(proc.stderr.strip(), tmp_s)[:1800],
    }


def run_probes() -> dict[str, Any]:
    rustc, cargo, nm_bin, miri_bin = _toolchain_paths()
    rustc_ver = subprocess.check_output([rustc, "--version", "--verbose"], text=True).strip()
    miri_ver = None
    if miri_bin:
        try:
            env = os.environ.copy()
            env["PATH"] = f"{Path(rustc).parent}:{env.get('PATH', '')}"
            miri_ver = subprocess.check_output(
                [cargo, "miri", "--version"], text=True, env=env
            ).strip()
        except Exception:
            miri_ver = None

    results: dict[str, Any] = {
        "timestamp_utc": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": rustc_ver,
        "miri_version": miri_ver,
        "part_a_valtree_canonicalization": {},
        "part_b_const_to_pat_and_structural_eq": {},
        "part_c_v0_const_generic_mangling": {},
    }

    with tempfile.TemporaryDirectory(prefix="valtree_probe_") as td:
        tmp = Path(td)
        pa = results["part_a_valtree_canonicalization"]
        pb = results["part_b_const_to_pat_and_structural_eq"]
        pc = results["part_c_v0_const_generic_mangling"]

        # ------------------------------------------------------------------
        # PART A: ValTree canonicalization, padding/ref erasure, limits, DAG
        # ------------------------------------------------------------------

        # A1: Padding erasure unifies distinct padding bit-patterns into one TypeId
        pa["padding_erasure_unification"] = _compile_and_run(
            rustc,
            tmp,
            "a1_pad_unify",
            r"""
#![feature(adt_const_params)]
use core::any::TypeId;
use core::marker::ConstParamTy;

#[repr(C)]
#[derive(PartialEq, Eq, ConstParamTy)]
struct Padded { a: u8, b: u32 }

const PAD_ZERO: Padded = unsafe { core::mem::transmute([1u8, 0, 0, 0, 2, 0, 0, 0]) };
const PAD_DEAD: Padded = unsafe { core::mem::transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) };

struct Tag<const P: Padded>;

fn val_of<const P: Padded>() -> u32 { (P.a as u32) * 100 + P.b }

fn main() {
    let same = TypeId::of::<Tag<PAD_ZERO>>() == TypeId::of::<Tag<PAD_DEAD>>();
    println!("SAME_TID={} V0={} V1={}", same, val_of::<PAD_ZERO>(), val_of::<PAD_DEAD>());
}
""",
        )

        # A1b/A1c/A1d/A1e: Miri padding byte initialization checks
        if miri_bin:
            pa["miri_padding_direct_literal_const"] = _run_miri_case(
                cargo,
                rustc,
                tmp,
                "pad_direct_lit",
                r"""
#[repr(C)]
struct Padded { a: u8, b: u32 }

const P: Padded = Padded { a: 1, b: 2 };

fn main() {
    let p = P;
    let bytes: [u8; 8] = unsafe { core::mem::transmute(p) };
    println!("{:?}", bytes);
}
""",
            )
            pa["miri_padding_direct_transmuted_const"] = _run_miri_case(
                cargo,
                rustc,
                tmp,
                "pad_direct_xmut",
                r"""
#[repr(C)]
struct Padded { a: u8, b: u32 }

const PAD_DEAD: Padded = unsafe { core::mem::transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) };

fn main() {
    let p = PAD_DEAD;
    let bytes: [u8; 8] = unsafe { core::mem::transmute(p) };
    println!("DIRECT_XMUT_BYTES={:02X?}", bytes);
}
""",
            )
            pa["miri_padding_valtree_const_param_from_literal"] = _run_miri_case(
                cargo,
                rustc,
                tmp,
                "pad_vt_lit",
                r"""
#![feature(adt_const_params)]
use core::marker::ConstParamTy;

#[repr(C)]
#[derive(PartialEq, Eq, ConstParamTy)]
struct Padded { a: u8, b: u32 }

const P_LIT: Padded = Padded { a: 1, b: 2 };

fn inspect<const P: Padded>() -> [u8; 8] {
    unsafe { core::mem::transmute(P) }
}

fn main() {
    let bytes = inspect::<P_LIT>();
    println!("{:?}", bytes);
}
""",
            )
            pa["miri_padding_valtree_const_param_from_transmuted"] = _run_miri_case(
                cargo,
                rustc,
                tmp,
                "pad_vt_xmut",
                r"""
#![feature(adt_const_params)]
use core::marker::ConstParamTy;

#[repr(C)]
#[derive(PartialEq, Eq, ConstParamTy)]
struct Padded { a: u8, b: u32 }

const PAD_DEAD: Padded = unsafe { core::mem::transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) };

fn inspect<const P: Padded>() -> [u8; 8] {
    unsafe { core::mem::transmute(P) }
}

fn main() {
    let bytes = inspect::<PAD_DEAD>();
    println!("{:?}", bytes);
}
""",
            )

        # A2: Reference identity / address erasure in ValTree
        pa["ref_identity_erasure"] = _compile_and_run(
            rustc,
            tmp,
            "a2_ref_erase",
            r"""
#![feature(adt_const_params, unsized_const_params)]
use core::any::TypeId;

const A: u8 = 7;
const B: u8 = 7;
const R1: &'static u8 = &A;
const R2: &'static u8 = &B;

struct RefTag<const R: &'static u8>;

const S1: &'static str = "hi";
const S2_BYTES: [u8; 2] = *b"hi";
const S2: &'static str = unsafe { core::str::from_utf8_unchecked(&S2_BYTES) };
struct StrTag<const S: &'static str>;

fn main() {
    let ref_same = TypeId::of::<RefTag<R1>>() == TypeId::of::<RefTag<R2>>();
    let str_same = TypeId::of::<StrTag<S1>>() == TypeId::of::<StrTag<S2>>();
    println!("REF_SAME_TID={} STR_SAME_TID={}", ref_same, str_same);
}
""",
        )

        # A3: Array match size sweep vs VALTREE_MAX_NODES = 100_000
        sweep: dict[str, Any] = {}
        segv_backtrace_head = ""
        for n in [1000, 4000, 10000, 15000, 20000, 50000, 99999, 100000, 100001]:
            code = f"""
const BIG: [u8; {n}] = [0u8; {n}];
#[inline(never)]
pub fn check(x: [u8; {n}]) -> bool {{ matches!(x, BIG) }}
fn main() {{ println!("{{}}", check([0u8; {n}])); }}
"""
            env_ov = {"RUST_BACKTRACE": "1"} if n == 20000 else None
            r = _compile_and_run(rustc, tmp, f"a3_sweep_{n}", code, timeout=90, env_override=env_ov)
            err_lines = [ln for ln in r.get("stderr_head", "").splitlines() if ln.strip()]
            sweep[str(n)] = {
                "compile_rc": r.get("compile_rc"),
                "timed_out": r.get("timed_out", False),
                "err_line0": err_lines[0] if err_lines else "",
            }
            if n == 20000 and r.get("compile_rc", 0) != 0:
                segv_backtrace_head = r.get("stderr_head", "")
        pa["valtree_array_match_size_sweep"] = sweep
        pa["valtree_array_match_20000_backtrace_head"] = segv_backtrace_head

        # A3b: Const generic array boundary at 99_999, 100_000, 100_001
        for n in [99999, 100000, 100001]:
            pa[f"valtree_const_generic_arr_{n}"] = _compile_and_run(
                rustc,
                tmp,
                f"a3_cg_{n}",
                f"""
#![feature(adt_const_params)]
const BIG: [u8; {n}] = [0u8; {n}];
struct ArrTag<const A: [u8; {n}]>;
fn main() {{ let _ = ArrTag::<BIG>; println!("CG_OK={n}"); }}
""",
                timeout=90,
            )

        # A3c: Binary DAG depth 18 (2^18 = 262,144 logical leaves) in const generic
        dag_defs = [
            "#![feature(adt_const_params, unsized_const_params)]",
            "use core::marker::ConstParamTy;",
            "#[derive(PartialEq, Eq, ConstParamTy)]",
            "enum Node { Leaf(u8), Pair(&'static Node, &'static Node) }",
            "const N0: Node = Node::Leaf(1);",
        ]
        for d in range(1, 19):
            dag_defs.append(f"const N{d}: Node = Node::Pair(&N{d-1}, &N{d-1});")
        dag_cg_code = "\n".join(
            dag_defs
            + [
                "struct DagTag<const N: &'static Node>;",
                'fn main() { let _ = DagTag::<{ &N18 }>; println!("DAG_CG_2POW18_DEPTH=18"); }',
            ]
        )
        pa["valtree_dag_cg_2pow18"] = _compile_and_run(rustc, tmp, "a3_dag_cg", dag_cg_code, timeout=90)

        # A3d: Const block in pattern rejected
        dag_pat_block_code = "\n".join(
            dag_defs[:15]
            + [
                "fn check(x: &Node) -> bool { matches!(x, const { &N10 }) }",
                "fn main() { let _ = check(&N10); }",
            ]
        )
        pa["valtree_dag_pat_const_block_d10"] = _compile_and_run(
            rustc, tmp, "a3_dag_pat_block", dag_pat_block_code
        )

        # A3e: Named const DAG depth 10 (1024 leaves) in pattern
        dag_pat_named_code = "\n".join(
            dag_defs[:15]
            + [
                "const ROOT10: &'static Node = &N10;",
                "fn check(x: &Node) -> bool { matches!(x, ROOT10) }",
                'fn main() { println!("DAG_PAT_NAMED_D10={}", check(&N10)); }',
            ]
        )
        pa["valtree_dag_pat_named_d10"] = _compile_and_run(
            rustc, tmp, "a3_dag_pat_named", dag_pat_named_code
        )

        # A3f: Cyclic const item (E0391 query cycle) vs cyclic static reference (ValTree traversal)
        pa["valtree_cyclic_const_item"] = _compile_and_run(
            rustc,
            tmp,
            "a3_cycle_const",
            r"""
#[derive(PartialEq, Eq)]
struct Cyc(Option<&'static Cyc>);
const C: Cyc = Cyc(Some(&C));
fn main() { let _ = matches!(C, C); }
""",
        )
        pa["valtree_cyclic_static_ref"] = _compile_and_run(
            rustc,
            tmp,
            "a3_cycle_static",
            r"""
#[derive(PartialEq)]
struct Thing(&'static Thing);
static X: Thing = Thing(&X);
const Y: &Thing = &X;
fn main() {
    if let Y = Y {}
}
""",
        )

        # A4: FnDef ZST accepted in ValTree vs rejected in const_to_pat
        pa["fndef_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "a4_fndef",
            r"""
fn f() {}
#[derive(PartialEq)]
struct Hold<F>(F);
fn test_fndef<F: Copy + PartialEq>(x: F) {
    let _ = x;
}
const fn mk_hold() -> Hold<fn()> { Hold(f) }
fn main() {
    const C: () = ();
    let _ = matches!((), C);
    let _ = mk_hold();
    let _ = test_fndef(f);
}
""",
        )
        pa["fndef_ty_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "a4_fndef_direct",
            r"""
#![feature(type_alias_impl_trait)]
fn helper() {}
type F = impl Copy + PartialEq;
#[define_opaque(F)]
const CF: F = helper;
fn main() {
    let _ = matches!(CF, CF);
}
""",
        )

        # ------------------------------------------------------------------
        # PART B: const_to_pat, StructuralPartialEq, floats, ptrs, unions, gates
        # ------------------------------------------------------------------

        # B1a: Active-variant-only StructuralPartialEq (Wrap::Empty with manual PartialEq payload)
        pb["active_variant_empty_skips_nonstructural_payload"] = _compile_and_run(
            rustc,
            tmp,
            "b1_empty",
            r"""
struct Manual(u8);
impl PartialEq for Manual { fn eq(&self, _: &Self) -> bool { false } }
#[derive(PartialEq)]
enum Wrap<T> { Empty, Full(T) }

const C_EMPTY: Wrap<Manual> = Wrap::Empty;
fn main() {
    let m = matches!(Wrap::<Manual>::Empty, C_EMPTY);
    let eq = Wrap::<Manual>::Empty == C_EMPTY;
    println!("ACTIVE_VARIANT_EMPTY_MATCHES={} EQ={}", m, eq);
}
""",
        )

        # B1b: Wrap::Empty with payload that has NO PartialEq impl at all (caught by alias_to_pat L216)
        pb["active_variant_empty_without_any_partialeq_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b1_empty_nopeq",
            r"""
struct NoPeq(u8);
#[derive(PartialEq)]
enum Wrap<T> { Empty, Full(T) }

const C_EMPTY: Wrap<NoPeq> = Wrap::Empty;
fn main() {
    let _ = matches!(Wrap::<NoPeq>::Empty, C_EMPTY);
}
""",
        )

        # B1c: Wrap::Full(Manual(1)) rejected because active variant recurses into Manual
        pb["active_variant_full_rejects_nonstructural_payload"] = _compile_and_run(
            rustc,
            tmp,
            "b1_full",
            r"""
struct Manual(u8);
impl PartialEq for Manual { fn eq(&self, _: &Self) -> bool { false } }
#[derive(PartialEq)]
enum Wrap<T> { Empty, Full(T) }

const C_FULL: Wrap<Manual> = Wrap::Full(Manual(1));
fn main() { let _ = matches!(Wrap::Full(Manual(1)), C_FULL); }
""",
        )

        # B2a: Direct manual PartialEq rejected
        pb["manual_partialeq_direct_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b2_manual",
            r"""
struct Manual(u8);
impl PartialEq for Manual { fn eq(&self, other: &Self) -> bool { self.0 == other.0 } }
const M: Manual = Manual(5);
fn main() { let _ = matches!(Manual(5), M); }
""",
        )

        # B2b: Non-const PartialEq allowed in const fn match
        pb["const_fn_non_const_partialeq_allowed"] = _compile_and_run(
            rustc,
            tmp,
            "b2_const_fn",
            r"""
#[derive(PartialEq, Eq)]
struct Key(u16, bool);
const TARGET: Key = Key(42, true);
const fn is_target(k: Key) -> bool {
    match k {
        TARGET => true,
        _ => false,
    }
}
const R_T: bool = is_target(Key(42, true));
const R_F: bool = is_target(Key(42, false));
fn main() { println!("CONST_FN_MATCH T={} F={}", R_T, R_F); }
""",
        )

        # B3a: Float -0.0 == +0.0 pattern matching + MIR dump
        b3_src = tmp / "b3_float_zero.rs"
        b3_mir = tmp / "b3_float_zero.mir"
        b3_code = r"""
const POS_ZERO: f64 = 0.0;
const NEG_ZERO: f64 = -0.0;

#[inline(never)]
pub fn match_pos_zero(x: f64) -> bool {
    matches!(x, POS_ZERO)
}

#[inline(never)]
pub fn match_neg_zero(x: f64) -> bool {
    matches!(x, NEG_ZERO)
}

fn main() {
    println!(
        "NEG0_MATCHES_POS0={} POS0_MATCHES_NEG0={} NAN_MATCHES_0={}",
        match_pos_zero(-0.0),
        match_neg_zero(0.0),
        match_pos_zero(f64::NAN),
    );
}
"""
        b3_res = _compile_and_run(rustc, tmp, "b3_float_zero", b3_code)
        b3_src.write_text(b3_code, encoding="utf-8")
        mir_proc = _run_rustc(rustc, b3_src, b3_mir, extra_args=["--emit=mir"])
        if mir_proc.returncode == 0 and b3_mir.is_file():
            mir_text = b3_mir.read_text(encoding="utf-8")
            b3_res["mir_len"] = len(mir_text)
            # Extract match_pos_zero and match_neg_zero blocks
            idx = mir_text.find("fn match_pos_zero")
            end = mir_text.find("fn main")
            b3_res["mir_snippet"] = mir_text[idx:end].strip() if idx != -1 and end != -1 else mir_text[:1500]
        pb["float_pos_neg_zero_match"] = b3_res

        # B3b: Float NaN rejected (RFC 3535) — both quiet NaN and signaling/payload NaN
        pb["float_nan_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b3_nan",
            r"""
const MY_NAN: f64 = f64::NAN;
fn main() { let _ = matches!(0.0_f64, MY_NAN); }
""",
        )
        pb["float_payload_nan_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b3_snan",
            r"""
const PAYLOAD_NAN: f64 = f64::from_bits(0x7ff0_0000_0000_0001);
fn main() { let _ = matches!(0.0_f64, PAYLOAD_NAN); }
""",
        )

        # B3c: Float forbidden as const param type (E0741)
        pb["float_const_param_ty_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b3_flt_param",
            r"""
struct FTag<const F: f64>;
fn main() { let _ = FTag::<0.0>; }
""",
        )

        # B4a: Thin raw pointer without provenance allowed in pattern
        pb["raw_ptr_without_provenance_allowed"] = _compile_and_run(
            rustc,
            tmp,
            "b4_intptr",
            r"""
const INT_PTR: *const u8 = core::ptr::without_provenance(0x1000);
fn main() {
    let p_ok: *const u8 = core::ptr::without_provenance(0x1000);
    let p_no: *const u8 = core::ptr::without_provenance(0x2000);
    println!("INT_PTR_MATCH={} MISMATCH={}", matches!(p_ok, INT_PTR), matches!(p_no, INT_PTR));
}
""",
        )

        # B4b: Raw pointer WITH provenance rejected
        pb["raw_ptr_with_provenance_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b4_provptr",
            r"""
static X: u8 = 0;
const PROV_PTR: *const u8 = &X as *const u8;
fn main() { let _ = matches!(&X as *const u8, PROV_PTR); }
""",
        )

        # B4c: Wide raw pointer WITHOUT provenance rejected (ScalarPair)
        pb["wide_raw_ptr_without_provenance_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b4_wideptr",
            r"""
const WIDE_INT_PTR: *const [u8] =
    core::ptr::slice_from_raw_parts(core::ptr::without_provenance(0x1000), 4);
fn main() {
    let p = core::ptr::slice_from_raw_parts(core::ptr::without_provenance::<u8>(0x1000), 4);
    let _ = matches!(p, WIDE_INT_PTR);
}
""",
        )

        # B4d: Function pointer rejected
        pb["fn_ptr_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b4_fnptr",
            r"""
fn helper() {}
const FP: fn() = helper;
fn main() { let _ = matches!(helper as fn(), FP); }
""",
        )

        # B4e: Union rejected
        pb["union_pattern_rejected"] = _compile_and_run(
            rustc,
            tmp,
            "b4_union",
            r"""
#[derive(Copy, Clone)]
union U { a: u8, b: u8 }
impl PartialEq for U { fn eq(&self, other: &Self) -> bool { unsafe { self.a == other.a } } }
const CU: U = U { a: 1 };
fn main() { let _ = matches!(U { a: 1 }, CU); }
""",
        )

        # B5: Padded struct pattern ignores padding bytes
        pb["padded_struct_pattern_ignores_padding"] = _compile_and_run(
            rustc,
            tmp,
            "b5_pad_pat",
            r"""
#[repr(C)]
#[derive(PartialEq, Eq)]
struct Padded { a: u8, b: u32 }

const PAD_ZERO: Padded = unsafe { core::mem::transmute([1u8, 0, 0, 0, 2, 0, 0, 0]) };
fn main() {
    let x: Padded = unsafe { core::mem::transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) };
    println!("PAD_PAT_MATCH={}", matches!(x, PAD_ZERO));
}
""",
        )

        # B6a/b/c: min_adt_const_params vs adt_const_params (#[non_exhaustive] + field visibility)
        pb["non_exhaustive_const_param_without_adt_feature"] = _compile_and_run(
            rustc,
            tmp,
            "b6_min_nonexh",
            r"""
#![feature(min_adt_const_params)]
use core::marker::ConstParamTy;

#[non_exhaustive]
#[derive(PartialEq, Eq, ConstParamTy)]
struct NonExh { x: u8 }

fn main() { let _ = NonExh { x: 1 }; }
""",
        )
        pb["non_exhaustive_const_param_with_adt_feature"] = _compile_and_run(
            rustc,
            tmp,
            "b6_full_nonexh",
            r"""
#![feature(adt_const_params)]
use core::marker::ConstParamTy;

#[non_exhaustive]
#[derive(PartialEq, Eq, ConstParamTy)]
struct NonExh { x: u8 }

struct Tag<const N: NonExh>;
fn main() { let _ = Tag::<{ NonExh { x: 1 } }>; println!("NONEXH_WITH_FEATURE_OK"); }
""",
        )
        pb["private_field_const_param_without_adt_feature"] = _compile_and_run(
            rustc,
            tmp,
            "b6_min_priv",
            r"""
#![feature(min_adt_const_params)]
use core::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct PrivField { x: u8 }

fn main() { let _ = PrivField { x: 1 }; }
""",
        )
        pb["private_field_const_param_with_adt_feature"] = _compile_and_run(
            rustc,
            tmp,
            "b6_full_priv",
            r"""
#![feature(adt_const_params)]
use core::marker::ConstParamTy;

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct PrivField { x: u8 }

struct Tag<const P: PrivField>;
fn main() { let _ = Tag::<{ PrivField { x: 1 } }>; println!("PRIV_WITH_FEATURE_OK"); }
""",
        )

        # ------------------------------------------------------------------
        # PART C: v0 Symbol Mangling of ValTree Const Generics
        # ------------------------------------------------------------------
        c_src = tmp / "c_mangle.rs"
        c_obj = tmp / "c_mangle.o"
        c_src.write_text(
            r"""
#![crate_type = "lib"]
#![crate_name = "c_mangle"]
#![feature(adt_const_params, unsized_const_params)]

use core::marker::ConstParamTy;

#[repr(C)]
#[derive(PartialEq, Eq, ConstParamTy)]
pub struct Padded { pub a: u8, pub b: u32 }

#[derive(PartialEq, Eq, ConstParamTy)]
pub struct TupleStruct(pub u8, pub bool);

#[derive(PartialEq, Eq, ConstParamTy)]
pub enum Choice {
    Unit,
    Tup(u16),
    Named { tag: i8 },
}

pub const PAD_ZERO: Padded = unsafe { core::mem::transmute([1u8, 0, 0, 0, 2, 0, 0, 0]) };
pub const PAD_DEAD: Padded = unsafe { core::mem::transmute([1u8, 0xDE, 0xAD, 0xBE, 2, 0, 0, 0]) };

pub const R1_VAL: u8 = 7;
pub const R2_VAL: u8 = 7;
pub const R1: &'static u8 = &R1_VAL;
pub const R2: &'static u8 = &R2_VAL;

#[inline(never)]
pub fn mangle_i32<const N: i32>() -> i32 { N }

#[inline(never)]
pub fn mangle_str<const S: &'static str>() -> usize { S.len() }

#[inline(never)]
pub fn mangle_arr<const A: [u8; 3]>() -> u8 { A[0] }

#[inline(never)]
pub fn mangle_ref<const R: &'static u8>() -> u8 { *R }

#[inline(never)]
pub fn mangle_pad<const P: Padded>() -> u32 { P.b }

#[inline(never)]
pub fn mangle_tup<const T: TupleStruct>() -> u8 { T.0 }

#[inline(never)]
pub fn mangle_enum<const C: Choice>() -> u8 {
    match C {
        Choice::Unit => 0,
        Choice::Tup(_) => 1,
        Choice::Named { .. } => 2,
    }
}

#[inline(never)]
pub fn mangle_dup_backref<const P1: Padded, const P2: Padded>() -> u32 {
    P1.b + P2.b
}

pub fn instantiate_all() -> usize {
    let mut acc = 0usize;
    acc += mangle_i32::<42>() as usize;
    acc += mangle_i32::<-42>() as usize;
    acc += mangle_str::<"hi">();
    acc += mangle_arr::<{ [1, 2, 3] }>() as usize;
    acc += mangle_ref::<R1>() as usize;
    acc += mangle_ref::<R2>() as usize;
    acc += mangle_pad::<PAD_ZERO>() as usize;
    acc += mangle_pad::<PAD_DEAD>() as usize;
    acc += mangle_tup::<{ TupleStruct(9, true) }>() as usize;
    acc += mangle_enum::<{ Choice::Unit }>() as usize;
    acc += mangle_enum::<{ Choice::Tup(0x201) }>() as usize;
    acc += mangle_enum::<{ Choice::Named { tag: -3 } }>() as usize;
    acc += mangle_dup_backref::<PAD_ZERO, PAD_DEAD>() as usize;
    acc
}
""",
            encoding="utf-8",
        )
        c_proc = _run_rustc(
            rustc,
            c_src,
            c_obj,
            extra_args=[
                "--emit=obj",
                "-C",
                "symbol-mangling-version=v0",
                "-C",
                "opt-level=0",
            ],
        )
        pc["compile_rc"] = c_proc.returncode
        if c_proc.returncode == 0 and nm_bin and c_obj.is_file():
            nm_out = subprocess.check_output([nm_bin, "--defined-only", "-g", str(c_obj)], text=True)
            syms: list[str] = []
            for line in nm_out.splitlines():
                parts = line.split()
                if len(parts) >= 3 and "mangle_" in parts[2]:
                    syms.append(parts[2])
            syms.sort()
            pc["defined_symbols"] = syms
            pc["mangle_pad_symbol_count"] = sum(1 for s in syms if "10mangle_pad" in s)
            pc["mangle_ref_symbol_count"] = sum(1 for s in syms if "10mangle_ref" in s)
            pc["mangle_dup_backref_symbols"] = [s for s in syms if "18mangle_dup_backref" in s]
        else:
            pc["stderr_head"] = _scrub(c_proc.stderr, str(tmp))[:1800]

    return results


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_valtree_and_const_to_pat_results.json",
        help="Output JSON path",
    )
    args = ap.parse_args()
    data = run_probes()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(f"Wrote {args.output} ({args.output.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
