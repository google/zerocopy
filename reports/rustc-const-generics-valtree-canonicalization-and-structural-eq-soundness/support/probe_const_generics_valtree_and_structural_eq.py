#!/usr/bin/env python3
"""Differential rustc, MIR, LLVM v0 symbol, and Miri probe for const generics,
ValTree canonicalization, generic_const_exprs syntactic unification, and
ConstParamTy / StructuralPartialEq admission rules.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def sanitize(text: str, tmp_root: Path) -> str:
    text = text.replace(str(tmp_root), "<tmp>")
    home = os.path.expanduser("~")
    if home:
        text = text.replace(home, "<home>")
    return text


def extract_v0_funcs(ll_text: str, prefixes: tuple[str, ...]) -> list[dict[str, str]]:
    out = []
    # Match LLVM IR function definitions and capture symbol + first few lines
    pattern = re.compile(
        r"(define [^\n]*@(_R[A-Za-z0-9_$]+)\([^\n]*\)\s*[^\n]*\{.*?^\})",
        re.MULTILINE | re.DOTALL,
    )
    for m in pattern.finditer(ll_text):
        body, sym = m.group(1), m.group(2)
        if any(p in sym for p in prefixes):
            out.append({"symbol": sym, "ir": body})
    return out


def run_compile_check(
    work_dir: Path, name: str, code: str, extra_flags: list[str]
) -> dict[str, Any]:
    src = work_dir / f"{name}.rs"
    src.write_text(code, encoding="utf-8")
    out_artifact = work_dir / f"lib{name}.rlib"
    cmd = ["rustc", "--edition=2021", "--crate-type=lib", *extra_flags, "-o", str(out_artifact), str(src)]
    res = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return {
        "flags": ["--edition=2021", "--crate-type=lib", *extra_flags],
        "returncode": res.returncode,
        "stdout": sanitize(res.stdout, work_dir).strip(),
        "stderr": sanitize(res.stderr, work_dir).strip(),
    }


def run_miri_crate(work_dir: Path, name: str, code: str) -> dict[str, Any]:
    crate_dir = work_dir / f"miri_{name}"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (crate_dir / "src" / "main.rs").write_text(code, encoding="utf-8")
    runs: dict[str, Any] = {}
    for label, miriflags in (
        ("stacked_borrows__default", ""),
        ("tree_borrows__default", "-Zmiri-tree-borrows"),
    ):
        env = dict(os.environ)
        if miriflags:
            env["MIRIFLAGS"] = miriflags
        else:
            env.pop("MIRIFLAGS", None)
        res = subprocess.run(
            ["cargo", "miri", "run", "--offline"],
            cwd=crate_dir,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        runs[label] = {
            "miriflags": miriflags or "<default Stacked Borrows>",
            "returncode": res.returncode,
            "stdout": sanitize(res.stdout, work_dir).strip(),
            "stderr": sanitize(res.stderr, work_dir).strip(),
        }
    return runs


def run_binary_and_ir(
    work_dir: Path,
    name: str,
    code: str,
    symbol_filters: tuple[str, ...],
    mir_filters: tuple[str, ...],
) -> dict[str, Any]:
    src = work_dir / f"{name}.rs"
    src.write_text(code, encoding="utf-8")

    mir_dir = work_dir / f"{name}_mir"
    mir_dir.mkdir(parents=True, exist_ok=True)

    ll_o0 = work_dir / f"{name}_o0.ll"
    ll_o2 = work_dir / f"{name}_o2.ll"
    bin_o2 = work_dir / f"{name}_o2"

    c_o0 = subprocess.run(
        ["rustc", "--edition=2021", "-C", "opt-level=0", "--emit=llvm-ir", "-o", str(ll_o0), str(src)],
        capture_output=True,
        text=True,
        check=False,
    )
    c_o2_ll = subprocess.run(
        ["rustc", "--edition=2021", "-C", "opt-level=2", "--emit=llvm-ir", "-o", str(ll_o2), str(src)],
        capture_output=True,
        text=True,
        check=False,
    )
    c_o2_bin = subprocess.run(
        ["rustc", "--edition=2021", "-C", "opt-level=2", "-o", str(bin_o2), str(src)],
        capture_output=True,
        text=True,
        check=False,
    )
    c_mir = subprocess.run(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=0",
            "--emit=mir",
            "-Zdump-mir=all",
            "-Zdump-mir-dir=" + str(mir_dir),
            "-o",
            str(work_dir / f"{name}_mir.bin"),
            str(src),
        ],
        capture_output=True,
        text=True,
        check=False,
    )

    native_res = subprocess.run([str(bin_o2)], capture_output=True, text=True, check=False)

    ll0_funcs = extract_v0_funcs(ll_o0.read_text(encoding="utf-8"), symbol_filters) if ll_o0.exists() else []
    ll2_funcs = extract_v0_funcs(ll_o2.read_text(encoding="utf-8"), symbol_filters) if ll_o2.exists() else []

    mir_excerpts: dict[str, str] = {}
    if c_mir.returncode == 0:
        for p in sorted(mir_dir.glob("*.runtime-optimized.after.mir")):
            if any(f in p.name for f in mir_filters):
                mir_excerpts[p.name] = p.read_text(encoding="utf-8")[:2400]

    miri_runs = run_miri_crate(work_dir, name, code)

    return {
        "rustc_o0_rc": c_o0.returncode,
        "rustc_o2_ll_rc": c_o2_ll.returncode,
        "rustc_o2_bin_rc": c_o2_bin.returncode,
        "rustc_warnings_o0": sanitize(c_o0.stderr, work_dir).strip(),
        "native_run_o2": {
            "returncode": native_res.returncode,
            "stdout": sanitize(native_res.stdout, work_dir).strip(),
            "stderr": sanitize(native_res.stderr, work_dir).strip(),
        },
        "miri_runs": miri_runs,
        "llvm_ir": {
            "opt_0": {
                "matching_fn_count": len(ll0_funcs),
                "symbols": [f["symbol"] for f in ll0_funcs],
                "defined_functions": [f["ir"] for f in ll0_funcs],
            },
            "opt_2": {
                "matching_fn_count": len(ll2_funcs),
                "symbols": [f["symbol"] for f in ll2_funcs],
                "defined_functions": [f["ir"] for f in ll2_funcs],
            },
        },
        "mir_excerpts": mir_excerpts,
    }


CODE_A_VALTREE_DEDUP = r"""#![feature(adt_const_params, unsized_const_params)]
use std::any::TypeId;
use std::marker::ConstParamTy;

#[derive(ConstParamTy, PartialEq, Eq)]
pub struct Tag {
    pub a: u8,
    pub b: bool,
}

#[derive(ConstParamTy, PartialEq, Eq)]
pub struct Padded {
    pub flag: bool,
    pub val: u32,
}

#[derive(ConstParamTy, PartialEq, Eq)]
pub enum Mode {
    Fast,
    Checked(u8),
}

struct TagCarrier<const T: Tag>;
struct PaddedCarrier<const P: Padded>;
struct ModeCarrier<const M: Mode>;
struct StrCarrier<const S: &'static str>;
struct SliceCarrier<const XS: &'static [u8]>;
struct RefTagCarrier<const R: &'static Tag>;

#[inline(never)]
fn size_fn<const N: usize>() -> usize {
    std::hint::black_box(N) * 2
}

#[inline(never)]
fn use_tag<const T: Tag>() -> u8 {
    if std::hint::black_box(T.b) { T.a + 10 } else { T.a }
}

#[inline(never)]
fn use_padded<const P: Padded>() -> u32 {
    if std::hint::black_box(P.flag) { P.val } else { 0 }
}

#[inline(never)]
fn use_mode<const M: Mode>() -> u8 {
    match std::hint::black_box(M) {
        Mode::Fast => 1,
        Mode::Checked(k) => k,
    }
}

#[inline(never)]
fn use_str<const S: &'static str>() -> usize {
    std::hint::black_box(S).len()
}

#[inline(never)]
fn use_slice<const XS: &'static [u8]>() -> usize {
    std::hint::black_box(XS).len()
}

const fn make_padded(v: u32) -> Padded {
    let mut p = Padded { flag: false, val: 0 };
    p.flag = true;
    p.val = v;
    p
}

static TAG_STATIC: Tag = Tag { a: 5, b: true };

fn main() {
    let arr_same = TypeId::of::<[u8; 2 + 2]>() == TypeId::of::<[u8; 4]>();
    let arr_diff = TypeId::of::<[u8; 5]>() == TypeId::of::<[u8; 4]>();
    let tag_same = TypeId::of::<TagCarrier<{ Tag { a: 2 + 3, b: !false } }>>()
        == TypeId::of::<TagCarrier<{ Tag { a: 5, b: true } }>>();
    let pad_same = TypeId::of::<PaddedCarrier<{ make_padded(42) }>>()
        == TypeId::of::<PaddedCarrier<{ Padded { flag: true, val: 40 + 2 } }>>();
    let mode_same = TypeId::of::<ModeCarrier<{ Mode::Checked(3 + 4) }>>()
        == TypeId::of::<ModeCarrier<{ Mode::Checked(7) }>>();
    let str_same = TypeId::of::<StrCarrier<"anneal">>()
        == TypeId::of::<StrCarrier<{ const { "anneal" } }>>();
    let slice_same = TypeId::of::<SliceCarrier<{ &[1, 2, 3] }>>()
        == TypeId::of::<SliceCarrier<{ &[1, 1 + 1, 3] }>>();
    let ref_same = TypeId::of::<RefTagCarrier<{ &TAG_STATIC }>>()
        == TypeId::of::<RefTagCarrier<{ &Tag { a: 2 + 3, b: !false } }>>();

    let sz1 = size_fn::<{ 2 + 2 }>();
    let sz2 = size_fn::<4>();
    let t1 = use_tag::<{ Tag { a: 2 + 3, b: !false } }>();
    let t2 = use_tag::<{ Tag { a: 5, b: true } }>();
    let p1 = use_padded::<{ make_padded(42) }>();
    let p2 = use_padded::<{ Padded { flag: true, val: 42 } }>();
    let m1 = use_mode::<{ Mode::Checked(3 + 4) }>();
    let m2 = use_mode::<{ Mode::Checked(7) }>();
    let s1 = use_str::<"anneal">();
    let s2 = use_str::<{ const { "anneal" } }>();
    let sl1 = use_slice::<{ &[1, 2, 3] }>();
    let sl2 = use_slice::<{ &[1, 1 + 1, 3] }>();

    println!(
        "ARR={arr_same},{arr_diff} TAG={tag_same},{t1},{t2} PAD={pad_same},{p1},{p2} MODE={mode_same},{m1},{m2} STR={str_same},{s1},{s2} SLICE={slice_same},{sl1},{sl2} REF={ref_same} SZ={sz1},{sz2}"
    );
}
"""

CODE_B_GCE_EXEC = r"""#![feature(generic_const_exprs)]
#[inline(never)]
pub fn gce_add_one<const N: usize>(arr: [u8; N + 1]) -> usize
where
    [(); N + 1]:,
{
    std::hint::black_box(&arr).len()
}

fn main() {
    let len = gce_add_one::<3>([1, 2, 3, 4]);
    println!("GCE_LEN={len}");
}
"""

CODE_C_MANUAL_STRUCTURAL_UNSOUND = r"""#![feature(adt_const_params, structural_match)]
use std::any::TypeId;
use std::marker::{ConstParamTy, StructuralPartialEq};

#[derive(ConstParamTy, Eq)]
pub struct Weird(pub u8);

impl PartialEq for Weird {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl StructuralPartialEq for Weird {}

struct Wrap<const W: Weird>;

fn main() {
    let w1 = Weird(1);
    let w2 = Weird(2);
    let rt_eq = w1 == w2;
    let ty_eq = TypeId::of::<Wrap<{ Weird(1) }>>() == TypeId::of::<Wrap<{ Weird(2) }>>();
    println!("RUNTIME_EQ={rt_eq} TYPEID_EQ={ty_eq}");
}
"""


def run_suite() -> dict[str, Any]:
    rv = subprocess.run(["rustc", "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    mv = subprocess.run(["cargo", "miri", "--version"], capture_output=True, text=True, check=True).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="r11_cgen_probe_") as td:
        wd = Path(td)

        suite_a = run_binary_and_ir(
            wd,
            "a_valtree_dedup",
            CODE_A_VALTREE_DEDUP,
            ("size_fn", "use_tag", "use_padded", "use_mode", "use_str", "use_slice"),
            ("main.", "size_fn.", "use_tag.", "use_padded.", "use_mode.", "use_str.", "use_slice."),
        )

        suite_b = {
            "min_const_generics_reject_param_arith": run_compile_check(
                wd,
                "b_min_cg_reject",
                "pub fn bad_min_cg<const N: usize>(arr: [u8; N + 1]) -> usize { arr.len() }\n",
                [],
            ),
            "repeat_expr_count_reject_param_arith": run_compile_check(
                wd,
                "b_repeat_count_reject",
                "pub fn bad_repeat<const N: usize>() -> usize { let a = [0u8; N + 1]; a.len() }\n",
                [],
            ),
            "repeat_expr_count_accept_standalone_param": run_compile_check(
                wd,
                "b_repeat_count_standalone",
                "pub fn ok_repeat<const N: usize>() -> usize { let a = [0u8; N]; a.len() }\n",
                [],
            ),
            "repeat_expr_count_legacy_assoc_const_76200": run_compile_check(
                wd,
                "b_repeat_76200_assoc",
                "pub struct H<T>(core::marker::PhantomData<T>);\nimpl<T> H<T> { pub const LEN: usize = 4; }\npub fn r_h<T>() -> [u8; 4] { [0u8; H::<T>::LEN] }\n",
                [],
            ),
            "repeat_expr_count_depends_on_ty_param": run_compile_check(
                wd,
                "b_repeat_ty_dep",
                "pub fn r_t<T>() -> [u8; 4] { [0u8; { let _: Option<T> = None; 4 }] }\n",
                [],
            ),
            "mcg_type_pos_rejects_ty_param": run_compile_check(
                wd,
                "b_mcg_ty_param",
                "pub fn ty_t<T>() -> [u8; { let _: Option<T> = None; 4 }] { [0u8; 4] }\n",
                [],
            ),
            "gce_body_missing_const_evaluatable_bound": run_compile_check(
                wd,
                "b_gce_body_missing",
                "#![feature(generic_const_exprs)]\npub fn bad_body<const N: usize>() -> usize {\n    let arr = [0u8; N + 1];\n    arr.len()\n}\n",
                [],
            ),
            "gce_caller_missing_const_evaluatable_bound": run_compile_check(
                wd,
                "b_gce_caller_missing",
                "#![feature(generic_const_exprs)]\npub fn callee<const N: usize>() -> usize where [(); N + 1]: { [0u8; N + 1].len() }\npub fn bad_caller<const N: usize>() -> usize { callee::<N>() }\n",
                [],
            ),
            "gce_sig_auto_clause_without_explicit_where": run_compile_check(
                wd,
                "b_gce_sig_auto",
                "#![feature(generic_const_exprs)]\npub fn sig_auto<const N: usize>(arr: [u8; N + 1]) -> usize { arr.len() }\n",
                [],
            ),
            "gce_subtree_satisfies_bound": run_compile_check(
                wd,
                "b_gce_subtree",
                "#![feature(generic_const_exprs)]\npub fn take_inner<const K: usize>(_arr: [u8; K]) {}\npub fn caller<const N: usize>(arr: [u8; N + 1]) where [(); (N + 1) * 2]: {\n    take_inner::<{ N + 1 }>(arr)\n}\n",
                [],
            ),
            "gce_accept_with_where_bound": run_binary_and_ir(
                wd,
                "b_gce_ok",
                CODE_B_GCE_EXEC,
                ("gce_add_one",),
                ("gce_add_one.",),
            ),
            "gce_next_solver_globally_interaction": run_compile_check(
                wd,
                "b_gce_next_solver",
                "#![feature(generic_const_exprs)]\npub fn ok_gce<const N: usize>(arr: [u8; N + 1]) -> usize where [(); N + 1]: { arr.len() }\n",
                ["-Znext-solver=globally"],
            ),
            "gce_syntactic_unification_n_plus_1_vs_1_plus_n": run_compile_check(
                wd,
                "b_gce_e0308",
                "#![feature(generic_const_exprs)]\nfn same_type<T>(_x: T, _y: T) {}\npub fn mismatch<const N: usize>(a: [u8; N + 1], b: [u8; 1 + N])\nwhere\n    [(); N + 1]:,\n    [(); 1 + N]:,\n{\n    same_type(a, b)\n}\n",
                [],
            ),
        }

        suite_c = {
            "negative_f32_const_param": run_compile_check(
                wd,
                "c_f32_mcg",
                "pub fn bad_float<const F: f32>() {}\n",
                [],
            ),
            "negative_f32_adt_const_params": run_compile_check(
                wd,
                "c_f32_adt",
                "#![feature(adt_const_params)]\npub fn bad_float<const F: f32>() {}\n",
                [],
            ),
            "negative_mut_ref_const_param": run_compile_check(
                wd,
                "c_mut_ref_mcg",
                "pub fn bad_mut_ref<const R: &'static mut u8>() {}\n",
                [],
            ),
            "negative_mut_ref_adt_const_params": run_compile_check(
                wd,
                "c_mut_ref_adt",
                "#![feature(adt_const_params, unsized_const_params)]\npub fn bad_mut_ref<const R: &'static mut u8>() {}\n",
                [],
            ),
            "negative_manual_partial_eq_non_structural": run_compile_check(
                wd,
                "c_manual_peq",
                "#![feature(adt_const_params)]\nuse std::marker::ConstParamTy;\n#[derive(ConstParamTy, Eq)]\npub struct CustomEq(pub u8);\nimpl PartialEq for CustomEq {\n    fn eq(&self, _other: &Self) -> bool { true }\n}\n",
                [],
            ),
            "negative_min_adt_private_field": run_compile_check(
                wd,
                "c_min_adt_vis",
                "#![feature(min_adt_const_params)]\nuse std::marker::ConstParamTy;\n#[derive(ConstParamTy, PartialEq, Eq)]\npub struct PrivField(u8);\n",
                [],
            ),
            "positive_adt_private_field": run_compile_check(
                wd,
                "c_adt_vis",
                "#![feature(adt_const_params)]\nuse std::marker::ConstParamTy;\n#[derive(ConstParamTy, PartialEq, Eq)]\npub struct PrivField(u8);\n",
                [],
            ),
            "negative_min_adt_non_exhaustive": run_compile_check(
                wd,
                "c_min_adt_non_exh",
                "#![feature(min_adt_const_params)]\nuse std::marker::ConstParamTy;\n#[non_exhaustive]\n#[derive(ConstParamTy, PartialEq, Eq)]\npub struct NonExh { pub x: u8 }\n",
                [],
            ),
            "negative_union_const_param_ty": run_compile_check(
                wd,
                "c_union",
                "#![feature(adt_const_params)]\nuse std::marker::ConstParamTy;\n#[derive(ConstParamTy)]\npub union BadU { pub a: u8, pub b: i8 }\n",
                [],
            ),
            "manual_structural_peq_unsoundness_witness": run_binary_and_ir(
                wd,
                "c_manual_structural_peq",
                CODE_C_MANUAL_STRUCTURAL_UNSOUND,
                ("main",),
                ("main.",),
            ),
        }

        return {
            "rustc_version": rv,
            "miri_version": mv,
            "experiments": {
                "a_valtree_canonicalization_and_symbol_dedup": suite_a,
                "b_min_const_generics_vs_generic_const_exprs_and_syntactic_equality": suite_b,
                "c_adt_const_params_valtree_and_structural_eq": suite_c,
            },
        }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, help="Optional JSON path to write probe results")
    args = ap.parse_args()
    data = run_suite()
    rendered = json.dumps(data, indent=2, sort_keys=False)
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered + "\n", encoding="utf-8")
        print(f"wrote {args.out} ({len(rendered)} bytes)")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
