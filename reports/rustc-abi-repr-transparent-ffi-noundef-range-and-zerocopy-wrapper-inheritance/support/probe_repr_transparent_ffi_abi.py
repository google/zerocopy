#!/usr/bin/env python3
"""Empirical rustc / LLVM IR / Miri probe for #[repr(transparent)] FFI ABI,
noundef/range attribute inheritance, ManuallyDrop vs MaybeUninit stripping,
and zerocopy::ReadOnly<T> vs zerocopy::Unalign<T> divergence.
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

PROBE_A_IR_RS = r"""#![allow(dead_code, improper_ctypes_definitions)]
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::{NonZeroI32, NonZeroU32};

#[repr(transparent)]
pub struct WrapU32(PhantomData<u8>, pub u32, [u8; 0]);

#[repr(transparent)]
pub struct WrapNz(PhantomData<*const ()>, pub NonZeroU32, ());

#[repr(transparent)]
pub struct WrapNzI32(pub NonZeroI32, PhantomData<u8>);

#[repr(transparent)]
pub struct WrapNzNested(pub WrapNz, [(); 8]);

#[repr(transparent)]
pub struct WrapBool((), pub bool, PhantomData<u16>);

#[repr(transparent)]
pub struct WrapRef<'a>(pub &'a u32, PhantomData<u8>);

#[repr(transparent)]
pub struct WrapSlice<'a>(pub &'a [u32], PhantomData<u8>);

#[repr(C)]
pub struct ReprCU32(pub u32);

#[repr(C)]
pub struct ReprCNz(pub NonZeroU32);

#[unsafe(no_mangle)]
pub extern "C" fn bare_u32(x: u32) -> u32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_u32(x: WrapU32) -> WrapU32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_nz(x: NonZeroU32) -> NonZeroU32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_nz(x: WrapNz) -> WrapNz { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_nzi32(x: NonZeroI32) -> NonZeroI32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_nzi32(x: WrapNzI32) -> WrapNzI32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_nz_nested(x: WrapNzNested) -> WrapNzNested { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_bool(x: bool) -> bool { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_bool(x: WrapBool) -> WrapBool { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_ref(x: &u32) -> &u32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_ref<'a>(x: WrapRef<'a>) -> WrapRef<'a> { x }

#[unsafe(no_mangle)]
pub extern "C" fn md_nz(x: ManuallyDrop<NonZeroU32>) -> ManuallyDrop<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn md_ref(x: ManuallyDrop<&u32>) -> ManuallyDrop<&u32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn mu_nz(x: MaybeUninit<NonZeroU32>) -> MaybeUninit<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn mu_ref(x: MaybeUninit<&u32>) -> MaybeUninit<&u32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn repr_c_u32(x: ReprCU32) -> ReprCU32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn repr_c_nz(x: ReprCNz) -> ReprCNz { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_slice_len(s: &[u32]) -> usize { s.len() }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_slice_len(s: WrapSlice<'_>) -> usize { s.0.len() }

#[unsafe(no_mangle)]
pub extern "Rust" fn bare_slice_len_rust(s: &[u32]) -> usize { s.len() }

#[unsafe(no_mangle)]
pub extern "Rust" fn wrap_slice_len_rust(s: WrapSlice<'_>) -> usize { s.0.len() }
"""

PROBE_A_EXEC_RS = r"""#![allow(dead_code, improper_ctypes, improper_ctypes_definitions)]
use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroU32;

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct WrapU32(PhantomData<u8>, pub u32, [u8; 0]);

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct WrapNz(PhantomData<*const ()>, pub NonZeroU32, ());

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct WrapBool((), pub bool, PhantomData<u16>);

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct WrapRef<'a>(pub &'a u32, PhantomData<u8>);

#[unsafe(no_mangle)]
pub extern "C" fn bare_u32_id(x: u32) -> u32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_u32_id(x: WrapU32) -> WrapU32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn bare_nz_id(x: NonZeroU32) -> NonZeroU32 { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_nz_id(x: WrapNz) -> WrapNz { x }

#[unsafe(no_mangle)]
pub extern "C" fn md_nz_id(x: ManuallyDrop<NonZeroU32>) -> ManuallyDrop<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn mu_nz_id(x: MaybeUninit<NonZeroU32>) -> MaybeUninit<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_bool_id(x: WrapBool) -> WrapBool { x }

#[unsafe(no_mangle)]
pub extern "C" fn wrap_ref_id<'a>(x: WrapRef<'a>) -> WrapRef<'a> { x }

#[unsafe(no_mangle)]
pub extern "C" fn mu_ref_id(x: MaybeUninit<&'static u32>) -> MaybeUninit<&'static u32> { x }

unsafe extern "C" {
    #[link_name = "bare_u32_id"]
    fn call_bare_u32_with_wrap(x: WrapU32) -> WrapU32;

    #[link_name = "bare_nz_id"]
    fn call_bare_nz_with_wrap(x: WrapNz) -> WrapNz;

    #[link_name = "wrap_nz_id"]
    fn call_wrap_nz_with_bare(x: NonZeroU32) -> NonZeroU32;

    #[link_name = "md_nz_id"]
    fn call_md_nz_with_bare(x: NonZeroU32) -> NonZeroU32;

    #[link_name = "wrap_bool_id"]
    fn call_wrap_bool_with_bare(x: bool) -> bool;

    #[link_name = "wrap_ref_id"]
    fn call_wrap_ref_with_bare(x: &u32) -> &u32;
}

static STATIC_VAL: u32 = 123;

fn main() {
    let w = WrapU32(PhantomData, 99, []);
    let w_out = unsafe { call_bare_u32_with_wrap(w) };
    let nz_via_wrap = unsafe { call_bare_nz_with_wrap(WrapNz(PhantomData, NonZeroU32::new(7).unwrap(), ())) };
    let nz_via_bare = unsafe { call_wrap_nz_with_bare(NonZeroU32::new(42).unwrap()) };
    let md_via_bare = unsafe { call_md_nz_with_bare(NonZeroU32::new(5).unwrap()) };
    let b_out = unsafe { call_wrap_bool_with_bare(true) };
    let r_out = unsafe { call_wrap_ref_with_bare(&STATIC_VAL) };
    let _mu_uninit = mu_nz_id(MaybeUninit::<NonZeroU32>::uninit());
    let _mu_zero = mu_nz_id(MaybeUninit::<NonZeroU32>::zeroed());
    let _mu_ref_zero = mu_ref_id(MaybeUninit::<&'static u32>::zeroed());
    let mu_init = mu_nz_id(MaybeUninit::new(NonZeroU32::new(11).unwrap()));
    let mu_val = unsafe { mu_init.assume_init() }.get();
    println!(
        "WRAP_U32={} VIA_BARE={} VIA_WRAP={} MD={} BOOL={} REF={} MU_INIT={} MU_SIZE={}",
        w_out.1,
        nz_via_wrap.1.get(),
        nz_via_bare.get(),
        md_via_bare.get(),
        b_out,
        *r_out,
        mu_val,
        core::mem::size_of::<MaybeUninit<NonZeroU32>>(),
    );
}
"""

MIRI_NEG_CASES: dict[str, str] = {
    "ub_manually_drop_nonzero_uninit": r"""
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZeroU32;
#[unsafe(no_mangle)]
pub extern "C" fn md_nz(x: ManuallyDrop<NonZeroU32>) -> ManuallyDrop<NonZeroU32> { x }
fn main() {
    let bad: ManuallyDrop<NonZeroU32> = unsafe { MaybeUninit::uninit().assume_init() };
    let _ = md_nz(bad);
}
""",
    "ub_wrap_nz_zero": r"""
use core::marker::PhantomData;
use core::num::NonZeroU32;
#[repr(transparent)]
pub struct WrapNz(PhantomData<*const ()>, pub NonZeroU32, ());
#[unsafe(no_mangle)]
pub extern "C" fn wrap_nz(x: WrapNz) -> WrapNz { x }
fn main() {
    let bad: WrapNz = unsafe { core::mem::transmute::<u32, WrapNz>(0) };
    let _ = wrap_nz(bad);
}
""",
    "ub_maybe_uninit_assume_init_zero": r"""
use core::mem::MaybeUninit;
use core::num::NonZeroU32;
#[unsafe(no_mangle)]
pub extern "C" fn mu_nz(x: MaybeUninit<NonZeroU32>) -> MaybeUninit<NonZeroU32> { x }
fn main() {
    let passed = mu_nz(MaybeUninit::<NonZeroU32>::zeroed());
    let _bad = unsafe { passed.assume_init() };
}
""",
    "ub_repr_c_nz_abi_mismatch": r"""
#![allow(improper_ctypes)]
use core::num::NonZeroU32;
#[repr(C)]
pub struct ReprCNz(pub NonZeroU32);
#[unsafe(no_mangle)]
pub extern "C" fn bare_nz(x: NonZeroU32) -> NonZeroU32 { x }
unsafe extern "C" {
    #[link_name = "bare_nz"]
    fn call_as_repr_c(x: ReprCNz) -> ReprCNz;
}
fn main() {
    let _ = unsafe { call_as_repr_c(ReprCNz(NonZeroU32::new(7).unwrap())) };
}
""",
}

NEG_COMPILE_CASES: dict[str, str] = {
    "transparent_align4_zst_rejected": r"""
use core::num::NonZeroU32;
#[repr(transparent)]
pub struct BadTransparent([u32; 0], NonZeroU32);
pub fn use_it(x: BadTransparent) -> NonZeroU32 { x.1 }
""",
    "transparent_with_repr_c_rejected": r"""
#[repr(transparent, C)]
pub struct BadReprCombo(u32);
pub fn use_it(x: BadReprCombo) -> u32 { x.0 }
""",
}

PROBE_B_IR_RS = r"""#![allow(dead_code, improper_ctypes_definitions)]
extern crate zerocopy;
use core::num::{NonZeroU32, NonZeroU8};
use zerocopy::{ReadOnly, Unalign};

#[unsafe(no_mangle)]
pub extern "C" fn zc_readonly_u32(x: ReadOnly<u32>) -> ReadOnly<u32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_readonly_nz(x: ReadOnly<NonZeroU32>) -> ReadOnly<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_readonly_ref<'a>(x: ReadOnly<&'a u32>) -> ReadOnly<&'a u32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_u32(x: Unalign<u32>) -> Unalign<u32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_nz(x: Unalign<NonZeroU32>) -> Unalign<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_u8_nz(x: Unalign<NonZeroU8>) -> Unalign<NonZeroU8> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_ref<'a>(x: Unalign<&'a u32>) -> Unalign<&'a u32> { x }

#[unsafe(no_mangle)]
pub extern "Rust" fn zc_rust_readonly_nz(x: ReadOnly<NonZeroU32>) -> ReadOnly<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "Rust" fn zc_rust_unalign_nz(x: Unalign<NonZeroU32>) -> Unalign<NonZeroU32> { x }
"""

PROBE_B_EXEC_RS = r"""#![allow(dead_code, improper_ctypes, improper_ctypes_definitions)]
use core::num::NonZeroU32;
use zerocopy::{ReadOnly, Unalign};

#[unsafe(no_mangle)]
pub extern "C" fn zc_readonly_nz(x: ReadOnly<NonZeroU32>) -> ReadOnly<NonZeroU32> { x }

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_nz(x: Unalign<NonZeroU32>) -> Unalign<NonZeroU32> { x }

unsafe extern "C" {
    #[link_name = "zc_readonly_nz"]
    fn call_ro_as_bare(x: NonZeroU32) -> NonZeroU32;
}

fn main() {
    let ro = zc_readonly_nz(ReadOnly::new(NonZeroU32::new(77).unwrap()));
    let ro_via_bare = unsafe { call_ro_as_bare(NonZeroU32::new(91).unwrap()) };
    let ua = zc_unalign_nz(Unalign::new(NonZeroU32::new(88).unwrap()));
    println!(
        "RO_SIZE={} RO_ALIGN={} RO_VAL={} RO_VIA_BARE={} UA_SIZE={} UA_ALIGN={} UA_VAL={}",
        core::mem::size_of::<ReadOnly<NonZeroU32>>(),
        core::mem::align_of::<ReadOnly<NonZeroU32>>(),
        ReadOnly::into_inner(ro).get(),
        ro_via_bare.get(),
        core::mem::size_of::<Unalign<NonZeroU32>>(),
        core::mem::align_of::<Unalign<NonZeroU32>>(),
        ua.into_inner().get(),
    );
}
"""

PROBE_B_UNALIGN_MISMATCH_RS = r"""#![allow(improper_ctypes)]
use core::num::NonZeroU32;
use zerocopy::Unalign;

#[unsafe(no_mangle)]
pub extern "C" fn zc_unalign_nz(x: Unalign<NonZeroU32>) -> Unalign<NonZeroU32> { x }

unsafe extern "C" {
    #[link_name = "zc_unalign_nz"]
    fn call_ua_as_bare(x: NonZeroU32) -> NonZeroU32;
}

fn main() {
    let _ = unsafe { call_ua_as_bare(NonZeroU32::new(88).unwrap()) };
}
"""


def scrub(text: str, tmpdir: str | None = None, extra_paths: list[str] | None = None) -> str:
    if extra_paths:
        for p in sorted(extra_paths, key=len, reverse=True):
            if p:
                text = text.replace(p, "<zerocopy>")
    home = str(Path.home())
    if home:
        text = text.replace(home, "<home>")
    if tmpdir:
        text = text.replace(tmpdir, "<tmp>")
    return text


def run_cmd(
    cmd: list[str],
    cwd: Path | None = None,
    tmpdir: str | None = None,
    env: dict[str, str] | None = None,
    extra_scrub: list[str] | None = None,
) -> dict[str, Any]:
    merged_env = None
    if env is not None:
        merged_env = os.environ.copy()
        merged_env.update(env)
    res = subprocess.run(cmd, cwd=cwd, env=merged_env, capture_output=True, text=True)
    return {
        "returncode": res.returncode,
        "stdout": scrub(res.stdout, tmpdir, extra_scrub).strip(),
        "stderr": scrub(res.stderr, tmpdir, extra_scrub).strip(),
    }


def extract_llvm_fns(ir_text: str, names: list[str]) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    lines = ir_text.splitlines()
    for fn in names:
        pat = re.compile(rf"^define\b.*@{re.escape(fn)}\(")
        captured: list[str] = []
        inside = False
        for line in lines:
            if not inside:
                if pat.match(line):
                    inside = True
                    captured.append(line)
            else:
                captured.append(line)
                if line.strip() == "}":
                    break
        out[fn] = captured
    return out


def extract_llvm_aliases(ir_text: str) -> list[str]:
    return sorted(
        line.strip()
        for line in ir_text.splitlines()
        if " alias " in line and line.strip().startswith("@")
    )


def find_zerocopy_dir(explicit: str | None) -> Path:
    candidates: list[Path] = []
    if explicit:
        candidates.append(Path(explicit))
    env_dir = os.environ.get("ZEROCOPY_DIR")
    if env_dir:
        candidates.append(Path(env_dir))
    here = Path(__file__).resolve()
    for parent in here.parents:
        candidates.append(parent / "zerocopy")
        candidates.append(parent.parent / "zerocopy" / "zerocopy")
    projects_dir = Path.home() / "Projects"
    if projects_dir.is_dir():
        for entry in sorted(projects_dir.iterdir()):
            candidates.append(entry / "zerocopy" / "zerocopy")
    for cand in candidates:
        if (cand / "Cargo.toml").is_file() and (cand / "src" / "wrappers.rs").is_file():
            return cand.resolve()
    raise FileNotFoundError(
        "Could not locate zerocopy crate directory; pass --zerocopy-dir or set ZEROCOPY_DIR"
    )


def build_zerocopy_cfgs(rustc_version: str) -> list[str]:
    m = re.search(r"rustc\s+(\d+)\.(\d+)\.(\d+)", rustc_version)
    if not m:
        return []
    major, minor, patch = int(m.group(1)), int(m.group(2)), int(m.group(3))
    ver = (major, minor, patch)
    thresholds = [
        ((1, 100, 0), "no_zerocopy_allocator_api_1_100_0"),
        ((1, 89, 0), "no_zerocopy_simd_x86_avx12_1_89_0"),
        ((1, 81, 0), "no_zerocopy_core_error_1_81_0"),
        ((1, 79, 0), "no_zerocopy_slice_ptr_len_1_79_0"),
        ((1, 78, 0), "no_zerocopy_diagnostic_on_unimplemented_1_78_0"),
        ((1, 61, 0), "no_zerocopy_generic_bounds_in_const_fn_1_61_0"),
        ((1, 60, 0), "no_zerocopy_target_has_atomics_1_60_0"),
        ((1, 59, 0), "no_zerocopy_aarch64_simd_1_59_0"),
        ((1, 87, 0), "no_zerocopy_aarch64_simd_be_1_87_0"),
        ((1, 57, 0), "no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0"),
    ]
    cfgs: list[str] = []
    for thresh, flag in thresholds:
        if ver < thresh:
            cfgs.extend(["--cfg", flag])
    return cfgs


def run_probes(zerocopy_dir: Path) -> dict[str, Any]:
    rustc_ver = run_cmd(["rustc", "--version", "--verbose"])
    miri_ver = run_cmd(["cargo", "+nightly", "miri", "--version"])
    zc_sha_res = run_cmd(["git", "-C", str(zerocopy_dir), "rev-parse", "HEAD"])
    zc_cfgs = build_zerocopy_cfgs(rustc_ver["stdout"])

    fn_names_a = [
        "bare_u32",
        "wrap_u32",
        "bare_nz",
        "wrap_nz",
        "bare_nzi32",
        "wrap_nzi32",
        "wrap_nz_nested",
        "bare_bool",
        "wrap_bool",
        "bare_ref",
        "wrap_ref",
        "md_nz",
        "md_ref",
        "mu_nz",
        "mu_ref",
        "repr_c_u32",
        "repr_c_nz",
        "bare_slice_len",
        "wrap_slice_len",
        "bare_slice_len_rust",
        "wrap_slice_len_rust",
    ]
    fn_names_b = [
        "zc_readonly_u32",
        "zc_readonly_nz",
        "zc_readonly_ref",
        "zc_unalign_u32",
        "zc_unalign_nz",
        "zc_unalign_u8_nz",
        "zc_unalign_ref",
        "zc_rust_readonly_nz",
        "zc_rust_unalign_nz",
    ]

    results: dict[str, Any] = {
        "rustc_version": rustc_ver["stdout"],
        "miri_version": miri_ver["stdout"],
        "zerocopy_crate_dir_version": (zerocopy_dir / "Cargo.toml").read_text().splitlines()[17:21],
        "zerocopy_git_head": zc_sha_res["stdout"] if zc_sha_res["returncode"] == 0 else None,
        "experiments": {
            "a_extern_c_llvm_ir_and_runtime_checks": {},
            "b_zerocopy_readonly_vs_unalign_abi": {},
        },
    }

    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        a_rs = tmp / "probe_a.rs"
        a_rs.write_text(PROBE_A_IR_RS)

        # A1: -Copt-level=2 -Zmerge-functions=disabled --emit=llvm-ir (host x86_64)
        a_ll_nomerge = tmp / "probe_a_nomerge.ll"
        res_a_nomerge = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Zmerge-functions=disabled",
                "--emit=llvm-ir",
                "-o",
                str(a_ll_nomerge),
                str(a_rs),
            ],
            tmpdir=td,
        )
        ir_a_nomerge = a_ll_nomerge.read_text() if a_ll_nomerge.is_file() else ""

        # A2: default -Copt-level=2 --emit=llvm-ir (alias emission via MergeFunctions)
        a_ll_merge = tmp / "probe_a_merge.ll"
        res_a_merge = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "--emit=llvm-ir",
                "-o",
                str(a_ll_merge),
                str(a_rs),
            ],
            tmpdir=td,
        )
        ir_a_merge = a_ll_merge.read_text() if a_ll_merge.is_file() else ""

        # A3: -Copt-level=0 -Zmerge-functions=disabled --emit=llvm-ir
        a_ll_o0 = tmp / "probe_a_o0.ll"
        res_a_o0 = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=0",
                "-Zmerge-functions=disabled",
                "--emit=llvm-ir",
                "-o",
                str(a_ll_o0),
                str(a_rs),
            ],
            tmpdir=td,
        )
        ir_a_o0 = a_ll_o0.read_text() if a_ll_o0.is_file() else ""

        # A4: Cross-target LLVM IR (aarch64-unknown-linux-gnu and i686-unknown-linux-gnu)
        cross_ir_a: dict[str, Any] = {}
        for tgt in ("aarch64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
            ll_path = tmp / f"probe_a_{tgt}.ll"
            c_res = run_cmd(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-type=lib",
                    f"--target={tgt}",
                    "-Copt-level=2",
                    "-Zmerge-functions=disabled",
                    "--emit=llvm-ir",
                    "-o",
                    str(ll_path),
                    str(a_rs),
                ],
                tmpdir=td,
            )
            txt = ll_path.read_text() if ll_path.is_file() else ""
            cross_ir_a[tgt] = {
                "returncode": c_res["returncode"],
                "stderr": c_res["stderr"],
                "llvm_ir_by_fn": extract_llvm_fns(
                    txt, ["bare_nz", "wrap_nz", "md_nz", "mu_nz", "repr_c_nz", "wrap_bool", "wrap_ref"]
                ),
            }

        # A5: Negative compile checks
        neg_compile: dict[str, Any] = {}
        for name, src in NEG_COMPILE_CASES.items():
            f = tmp / f"{name}.rs"
            f.write_text(src)
            r = run_cmd(
                ["rustc", "--edition=2024", "--crate-type=lib", "-o", str(tmp / f"{name}.rlib"), str(f)],
                tmpdir=td,
            )
            neg_compile[name] = r

        # A6: Native binary execution
        a_exec_rs = tmp / "probe_a_exec.rs"
        a_exec_rs.write_text(PROBE_A_EXEC_RS)
        a_bin = tmp / "probe_a_exec"
        a_bin_compile = run_cmd(
            ["rustc", "--edition=2024", "-Copt-level=2", "-o", str(a_bin), str(a_exec_rs)],
            tmpdir=td,
        )
        a_bin_run = run_cmd([str(a_bin)], tmpdir=td) if a_bin_compile["returncode"] == 0 else {}

        # A7: Miri positive roundtrip
        miri_a_dir = tmp / "miri_a"
        (miri_a_dir / "src").mkdir(parents=True)
        (miri_a_dir / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe_a"\nversion = "0.1.0"\nedition = "2024"\n'
        )
        (miri_a_dir / "src" / "main.rs").write_text(PROBE_A_EXEC_RS)
        miri_a_run = run_cmd(
            ["cargo", "+nightly", "miri", "run", "--offline"],
            cwd=miri_a_dir,
            tmpdir=td,
        )

        # A8: Miri negative UB controls
        miri_neg: dict[str, Any] = {}
        for name, src in MIRI_NEG_CASES.items():
            case_dir = tmp / f"miri_{name}"
            (case_dir / "src").mkdir(parents=True)
            (case_dir / "Cargo.toml").write_text(
                f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2024"\n'
            )
            (case_dir / "src" / "main.rs").write_text(src)
            miri_neg[name] = run_cmd(
                ["cargo", "+nightly", "miri", "run", "--offline"],
                cwd=case_dir,
                tmpdir=td,
            )

        results["experiments"]["a_extern_c_llvm_ir_and_runtime_checks"] = {
            "llvm_ir_signatures": {
                "edition": "2024",
                "extra_args": ["-Copt-level=2", "-Zmerge-functions=disabled", "--emit=llvm-ir"],
                "compile_returncode": res_a_nomerge["returncode"],
                "compile_stderr": res_a_nomerge["stderr"],
                "llvm_ir_by_fn": extract_llvm_fns(ir_a_nomerge, fn_names_a),
                "default_o2_compile_returncode": res_a_merge["returncode"],
                "default_o2_merge_functions_aliases": extract_llvm_aliases(ir_a_merge),
                "o0_compile_returncode": res_a_o0["returncode"],
                "o0_llvm_ir_by_fn": extract_llvm_fns(
                    ir_a_o0, ["bare_nz", "wrap_nz", "md_nz", "mu_nz", "wrap_bool", "wrap_ref", "repr_c_nz"]
                ),
            },
            "cross_target_llvm_ir": cross_ir_a,
            "negative_compile_checks": neg_compile,
            "abi_roundtrip_and_maybe_uninit_exec": {
                "edition": "2024",
                "compile_returncode": a_bin_compile["returncode"],
                "compile_stdout": a_bin_compile["stdout"],
                "compile_stderr": a_bin_compile["stderr"],
                "run_returncode": a_bin_run.get("returncode"),
                "run_stdout": a_bin_run.get("stdout"),
                "run_stderr": a_bin_run.get("stderr"),
            },
            "abi_roundtrip_and_maybe_uninit_miri": {
                "edition": "2024",
                "command": "cargo +nightly miri run --offline",
                "returncode": miri_a_run["returncode"],
                "stdout": miri_a_run["stdout"],
                "stderr": miri_a_run["stderr"],
            },
            "miri_ub_negative_controls": miri_neg,
        }

        # Part B: Compile real zerocopy and inspect ReadOnly vs Unalign
        zc_pkg_version = "0.8.64"
        for line in (zerocopy_dir / "Cargo.toml").read_text().splitlines():
            m = re.match(r'^version\s*=\s*"([^"]+)"', line.strip())
            if m:
                zc_pkg_version = m.group(1)
                break
        zc_env = {"CARGO_PKG_VERSION": zc_pkg_version}
        zc_scrub = [str(zerocopy_dir)]

        zc_rlib = tmp / "libzerocopy.rlib"
        zc_compile = run_cmd(
            [
                "rustc",
                "--edition=2021",
                "--crate-type=rlib",
                "--crate-name=zerocopy",
                "-Copt-level=2",
                *zc_cfgs,
                "-o",
                str(zc_rlib),
                str(zerocopy_dir / "src" / "lib.rs"),
            ],
            tmpdir=td,
            env=zc_env,
            extra_scrub=zc_scrub,
        )

        b_ir_rs = tmp / "probe_b.rs"
        b_ir_rs.write_text(PROBE_B_IR_RS)
        b_ll_nomerge = tmp / "probe_b_nomerge.ll"
        b_ir_nomerge_res = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Zmerge-functions=disabled",
                "--emit=llvm-ir",
                "--extern",
                f"zerocopy={zc_rlib}",
                "-o",
                str(b_ll_nomerge),
                str(b_ir_rs),
            ],
            tmpdir=td,
            extra_scrub=zc_scrub,
        )
        ir_b_nomerge = b_ll_nomerge.read_text() if b_ll_nomerge.is_file() else ""

        b_ll_merge = tmp / "probe_b_merge.ll"
        b_ir_merge_res = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "--emit=llvm-ir",
                "--extern",
                f"zerocopy={zc_rlib}",
                "-o",
                str(b_ll_merge),
                str(b_ir_rs),
            ],
            tmpdir=td,
            extra_scrub=zc_scrub,
        )
        ir_b_merge = b_ll_merge.read_text() if b_ll_merge.is_file() else ""

        # Cross-target zerocopy IR
        cross_ir_b: dict[str, Any] = {}
        for tgt in ("aarch64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
            zc_tgt_rlib = tmp / f"libzerocopy_{tgt}.rlib"
            zc_tgt_res = run_cmd(
                [
                    "rustc",
                    "--edition=2021",
                    "--crate-type=rlib",
                    "--crate-name=zerocopy",
                    f"--target={tgt}",
                    "-Copt-level=2",
                    *zc_cfgs,
                    "-o",
                    str(zc_tgt_rlib),
                    str(zerocopy_dir / "src" / "lib.rs"),
                ],
                tmpdir=td,
                env=zc_env,
                extra_scrub=zc_scrub,
            )
            ll_tgt = tmp / f"probe_b_{tgt}.ll"
            b_tgt_res = run_cmd(
                [
                    "rustc",
                    "--edition=2024",
                    "--crate-type=lib",
                    f"--target={tgt}",
                    "-Copt-level=2",
                    "-Zmerge-functions=disabled",
                    "--emit=llvm-ir",
                    "--extern",
                    f"zerocopy={zc_tgt_rlib}",
                    "-o",
                    str(ll_tgt),
                    str(b_ir_rs),
                ],
                tmpdir=td,
                extra_scrub=zc_scrub,
            )
            txt = ll_tgt.read_text() if ll_tgt.is_file() else ""
            cross_ir_b[tgt] = {
                "zerocopy_rlib_returncode": zc_tgt_res["returncode"],
                "probe_returncode": b_tgt_res["returncode"],
                "stderr": b_tgt_res["stderr"],
                "llvm_ir_by_fn": extract_llvm_fns(
                    txt, ["zc_readonly_nz", "zc_unalign_nz", "zc_unalign_u8_nz", "zc_unalign_ref"]
                ),
            }

        # Native execution of Part B
        b_exec_rs = tmp / "probe_b_exec.rs"
        b_exec_rs.write_text(PROBE_B_EXEC_RS)
        b_bin = tmp / "probe_b_exec"
        b_bin_compile = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "-Copt-level=2",
                "--extern",
                f"zerocopy={zc_rlib}",
                "-o",
                str(b_bin),
                str(b_exec_rs),
            ],
            tmpdir=td,
            extra_scrub=zc_scrub,
        )
        b_bin_run = run_cmd([str(b_bin)], tmpdir=td, extra_scrub=zc_scrub) if b_bin_compile["returncode"] == 0 else {}

        # Miri Part B (positive ReadOnly FFI substitution + Unalign mismatch test)
        miri_b_dir = tmp / "miri_b"
        (miri_b_dir / "src").mkdir(parents=True)
        (miri_b_dir / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe_b"\nversion = "0.1.0"\nedition = "2024"\n'
            f'[dependencies]\nzerocopy = {{ path = "{zerocopy_dir}", default-features = false }}\n'
        )
        (miri_b_dir / "src" / "main.rs").write_text(PROBE_B_EXEC_RS)
        miri_b_run = run_cmd(
            ["cargo", "+nightly", "miri", "run", "--offline"],
            cwd=miri_b_dir,
            tmpdir=td,
            extra_scrub=zc_scrub,
        )

        miri_b_mis_dir = tmp / "miri_b_mismatch"
        (miri_b_mis_dir / "src").mkdir(parents=True)
        (miri_b_mis_dir / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe_b_mismatch"\nversion = "0.1.0"\nedition = "2024"\n'
            f'[dependencies]\nzerocopy = {{ path = "{zerocopy_dir}", default-features = false }}\n'
        )
        (miri_b_mis_dir / "src" / "main.rs").write_text(PROBE_B_UNALIGN_MISMATCH_RS)
        miri_b_mismatch = run_cmd(
            ["cargo", "+nightly", "miri", "run", "--offline"],
            cwd=miri_b_mis_dir,
            tmpdir=td,
            extra_scrub=zc_scrub,
        )

        results["experiments"]["b_zerocopy_readonly_vs_unalign_abi"] = {
            "edition_zerocopy": "2021",
            "edition_probe": "2024",
            "zerocopy_cfgs": zc_cfgs,
            "zerocopy_rlib_returncode": zc_compile["returncode"],
            "zerocopy_rlib_stderr": zc_compile["stderr"],
            "ir_compile_returncode": b_ir_nomerge_res["returncode"],
            "ir_compile_stderr": b_ir_nomerge_res["stderr"],
            "llvm_ir_by_fn": extract_llvm_fns(ir_b_nomerge, fn_names_b),
            "default_o2_returncode": b_ir_merge_res["returncode"],
            "default_o2_merge_functions_aliases": extract_llvm_aliases(ir_b_merge),
            "cross_target_llvm_ir": cross_ir_b,
            "bin_compile_returncode": b_bin_compile["returncode"],
            "bin_compile_stderr": b_bin_compile["stderr"],
            "bin_run_returncode": b_bin_run.get("returncode"),
            "bin_run_stdout": b_bin_run.get("stdout"),
            "bin_run_stderr": b_bin_run.get("stderr"),
            "miri_readonly_and_unalign_run": miri_b_run,
            "miri_unalign_as_bare_nz_mismatch": miri_b_mismatch,
        }

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zerocopy-dir", help="Path to local zerocopy crate directory")
    parser.add_argument(
        "--output",
        default=str(Path(__file__).resolve().parent / "probe_results.json"),
        help="Path to write JSON probe output",
    )
    args = parser.parse_args()
    zerocopy_dir = find_zerocopy_dir(args.zerocopy_dir)
    results = run_probes(zerocopy_dir)
    out_path = Path(args.output)
    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
