#!/usr/bin/env python3
"""Standalone empirical probe for rustc feature(unsafe_binders).

Reproduces and records:
1. Static type-system / MIR-build enforcement (!Copy, E0382, E0277, BikeshedGuaranteedNoDrop, E0133).
2. Symbol-mangling v0 ICE vs legacy/hashed/opt-level=2 post-inline behavior.
3. MIR optimization opacity (SROA, GVN) vs ReferencePropagation pass-through vs LLVM -O2 lowering.
4. Miri runtime validity FIXME panic vs -Zmiri-disable-validation borrow-tracker suppression.
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
from pathlib import Path


def resolve_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / name
    if candidate.is_file():
        return str(candidate)
    raise FileNotFoundError(f"cannot locate executable {name!r} on PATH or ~/.cargo/bin")


def sanitize(text: str, tmp_dir: str) -> str:
    text = text.replace(tmp_dir, "<tmp>")
    home = str(Path.home())
    if home:
        text = text.replace(home, "<home>")
    text = re.sub(r"/rustc-dev/[0-9a-f]{7,40}/", "<rustc-dev>/", text)
    text = re.sub(r"/rustc/[0-9a-f]{7,40}/", "<rustc>/", text)
    return text


def run_cmd(cmd: list[str], cwd: str | None = None, env_extra: dict[str, str] | None = None) -> dict:
    env = os.environ.copy()
    if env_extra:
        env.update(env_extra)
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json-out",
        default="",
        help="Optional path to write JSON probe results (default: stdout summary only)",
    )
    args = parser.parse_args()

    rustc = resolve_tool("rustc")
    cargo = resolve_tool("cargo")

    results: dict = {
        "probe_id": "unsafe_binders_v0_mangling_miri_validity_and_mir_opt",
        "rustc_version": run_cmd([rustc, "-vV"])["stdout"].strip(),
        "miri_version": run_cmd([cargo, "+nightly", "miri", "--version"])["stdout"].strip(),
    }

    with tempfile.TemporaryDirectory(prefix="ubinder_probe_") as td:
        # 1. Static enforcement: !Copy, BikeshedGuaranteedNoDrop, and unsafety gate.
        static_cases = {
            "non_copy_shared_ref": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::unwrap_binder;
pub fn copy_shared(b: unsafe<'a> &'a u32) -> (u32, u32) {
    let b2 = b;
    unsafe { (*unwrap_binder!(b), *unwrap_binder!(b2)) }
}
"""
            ),
            "non_copy_mut_ref": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::unwrap_binder;
pub fn copy_mut(b: unsafe<'a> &'a mut u32) -> (u32, u32) {
    let b2 = b;
    unsafe { (*unwrap_binder!(b), *unwrap_binder!(b2)) }
}
"""
            ),
            "non_copy_even_inner_u32": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::unwrap_binder;
pub fn copy_u32_binder(b: unsafe<> u32) -> (u32, u32) {
    let b2 = b;
    unsafe { (unwrap_binder!(b), unwrap_binder!(b2)) }
}
"""
            ),
            "trait_bound_not_copy": (
                """#![feature(unsafe_binders)]
fn req_copy<T: Copy>(x: T) -> (T, T) { (x, x) }
pub fn check(b: unsafe<'a> &'a u32) -> (unsafe<'a> &'a u32, unsafe<'a> &'a u32) {
    req_copy(b)
}
"""
            ),
            "unsafety_gate_wrap": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::wrap_binder;
pub fn bad_wrap(x: &u32) -> unsafe<'a> &'a u32 {
    wrap_binder!(x)
}
"""
            ),
            "unsafety_gate_unwrap": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::unwrap_binder;
pub fn bad_unwrap(b: unsafe<'a> &'a u32) -> u32 {
    *unwrap_binder!(b)
}
"""
            ),
            "wf_rejects_string_binder": (
                """#![feature(unsafe_binders)]
use core::unsafe_binder::wrap_binder;
pub fn bad_string(s: String) -> unsafe<> String {
    unsafe { wrap_binder!(s) }
}
"""
            ),
            "wf_rejects_nested_binder": (
                """#![feature(unsafe_binders)]
pub fn nested(b: unsafe<'b> unsafe<'a> &'a u32) -> &'static u32 {
    unsafe { core::unsafe_binder::unwrap_binder!(core::unsafe_binder::unwrap_binder!(b)) }
}
"""
            ),
            "wf_accepts_manually_drop_string": (
                """#![feature(unsafe_binders)]
use core::mem::ManuallyDrop;
use core::unsafe_binder::{wrap_binder, unwrap_binder};
pub fn wrap_md(s: String) -> String {
    let md = ManuallyDrop::new(s);
    unsafe {
        let b: unsafe<> ManuallyDrop<String> = wrap_binder!(md);
        ManuallyDrop::into_inner(unwrap_binder!(b))
    }
}
"""
            ),
        }
        results["static_checks"] = {}
        for name, src in static_cases.items():
            rs_path = os.path.join(td, f"{name}.rs")
            out_path = os.path.join(td, f"{name}.rlib")
            Path(rs_path).write_text(src, encoding="utf-8")
            r = run_cmd([rustc, "--edition=2024", "--crate-type=lib", rs_path, "-o", out_path])
            results["static_checks"][name] = {
                "returncode": r["returncode"],
                "stderr": sanitize(r["stderr"], td).strip(),
            }

        # 2. Symbol mangling matrix: v0 ICE vs legacy vs hashed vs opt-level=2 post-inline.
        ptr_read_src = """#![feature(unsafe_binders)]
use core::unsafe_binder::{wrap_binder, unwrap_binder};

pub fn generic_ptr_read(x: &mut u32) -> u32 {
    unsafe {
        let b: unsafe<'a> &'a mut u32 = wrap_binder!(x);
        let b2: unsafe<'a> &'a mut u32 = core::ptr::read(&b);
        core::mem::forget(b);
        let r: &mut u32 = unwrap_binder!(b2);
        *r += 1;
        *r
    }
}

fn main() {
    let mut v = 41u32;
    println!("{}", generic_ptr_read(&mut v));
}
"""
        noinline_src = """#![feature(unsafe_binders)]
use core::unsafe_binder::{wrap_binder, unwrap_binder};

#[inline(never)]
fn id_noinline<T>(x: T) -> T { x }

fn main() {
    let mut v = 41u32;
    let r = unsafe {
        let b: unsafe<'a> &'a mut u32 = wrap_binder!(&mut v);
        let b2 = id_noinline(b);
        *unwrap_binder!(b2)
    };
    println!("{}", r);
}
"""
        drop_glue_src = """#![feature(unsafe_binders)]
use core::mem::ManuallyDrop;
use core::unsafe_binder::wrap_binder;

#[inline(never)]
fn drop_any<T>(mut x: T) {
    unsafe { core::ptr::drop_in_place(&raw mut x); }
}

fn main() {
    let b: unsafe<'a> ManuallyDrop<String> = unsafe { wrap_binder!(ManuallyDrop::new(String::from("ok"))) };
    drop_any(b);
    println!("DROP_OK");
}
"""
        rs_ptr = os.path.join(td, "ptr_read.rs")
        rs_ni = os.path.join(td, "noinline.rs")
        rs_dg = os.path.join(td, "drop_glue.rs")
        Path(rs_ptr).write_text(ptr_read_src, encoding="utf-8")
        Path(rs_ni).write_text(noinline_src, encoding="utf-8")
        Path(rs_dg).write_text(drop_glue_src, encoding="utf-8")

        mangle_matrix = [
            ("ptr_read_opt0_default", rs_ptr, ["--edition=2024", "-Copt-level=0"]),
            ("ptr_read_opt0_v0", rs_ptr, ["--edition=2024", "-Copt-level=0", "-Csymbol-mangling-version=v0"]),
            ("ptr_read_opt0_hashed", rs_ptr, ["--edition=2024", "-Copt-level=0", "-Zunstable-options", "-Csymbol-mangling-version=hashed"]),
            ("ptr_read_opt0_legacy", rs_ptr, ["--edition=2024", "-Copt-level=0", "-Zunstable-options", "-Csymbol-mangling-version=legacy"]),
            ("ptr_read_opt2_default", rs_ptr, ["--edition=2024", "-Copt-level=2"]),
            ("ptr_read_opt2_v0", rs_ptr, ["--edition=2024", "-Copt-level=2", "-Csymbol-mangling-version=v0"]),
            ("noinline_opt2_v0", rs_ni, ["--edition=2024", "-Copt-level=2", "-Csymbol-mangling-version=v0"]),
            ("noinline_opt2_legacy", rs_ni, ["--edition=2024", "-Copt-level=2", "-Zunstable-options", "-Csymbol-mangling-version=legacy"]),
            ("drop_glue_opt0_v0", rs_dg, ["--edition=2024", "-Copt-level=0", "-Csymbol-mangling-version=v0"]),
            ("drop_glue_opt0_legacy", rs_dg, ["--edition=2024", "-Copt-level=0", "-Zunstable-options", "-Csymbol-mangling-version=legacy"]),
        ]
        results["mangling"] = {}
        for label, src_path, flags in mangle_matrix:
            bin_path = os.path.join(td, f"bin_{label}")
            r = run_cmd([rustc] + flags + [src_path, "-o", bin_path])
            entry: dict = {
                "flags": flags,
                "returncode": r["returncode"],
                "stderr": sanitize(r["stderr"], td).strip(),
            }
            if r["returncode"] == 0:
                rr = run_cmd([bin_path])
                entry["exec_returncode"] = rr["returncode"]
                entry["exec_stdout"] = rr["stdout"].strip()
            results["mangling"][label] = entry

        # 3. MIR optimizations (SROA, GVN, ReferencePropagation) vs LLVM IR lowering.
        mir_opt_src = """#![feature(unsafe_binders)]
use core::unsafe_binder::{wrap_binder, unwrap_binder};

#[inline(never)]
pub fn wrap_unwrap_ref(x: &u32) -> u32 {
    unsafe {
        let b: unsafe<'a> &'a u32 = wrap_binder!(x);
        *unwrap_binder!(b)
    }
}

#[inline(never)]
pub fn wrap_unwrap_mut(x: &mut u32) -> u32 {
    unsafe {
        let b: unsafe<'a> &'a mut u32 = wrap_binder!(x);
        let r: &mut u32 = unwrap_binder!(b);
        *r += 1;
        *r
    }
}

#[inline(never)]
pub fn wrap_unwrap_tuple(a: u32, b: u64) -> u32 {
    let tup = (a, b);
    unsafe {
        let wb: unsafe<> (u32, u64) = wrap_binder!(tup);
        unwrap_binder!(wb).0
    }
}

#[inline(never)]
pub fn ref_prop_through_unwrap(wb: &unsafe<> (u32, u64)) -> u32 {
    unsafe {
        let p: &u32 = &unwrap_binder!(*wb).0;
        *p
    }
}

#[inline(never)]
pub fn dup_mut_via_ptr_read(x: &mut u32) -> (u32, u32) {
    unsafe {
        let b: unsafe<'a> &'a mut u32 = wrap_binder!(x);
        let b2: unsafe<'a> &'a mut u32 = core::ptr::read(&b);
        let r1: &mut u32 = unwrap_binder!(b);
        let r2: &mut u32 = unwrap_binder!(b2);
        *r1 = 10;
        *r2 = 20;
        (*r1, *r2)
    }
}

fn main() {
    let mut a = 41u32;
    let r1 = wrap_unwrap_ref(&a);
    let r2 = wrap_unwrap_mut(&mut a);
    let t = wrap_unwrap_tuple(7, 99);
    let wb: unsafe<> (u32, u64) = unsafe { wrap_binder!((12u32, 34u64)) };
    let rp = ref_prop_through_unwrap(&wb);
    let mut d = 0u32;
    let dup = dup_mut_via_ptr_read(&mut d);
    println!("REF={} MUT={} TUP={} RP={} DUP={:?}", r1, r2, t, rp, dup);
}
"""
        proj = os.path.join(td, "miri_proj")
        os.makedirs(os.path.join(proj, "src"), exist_ok=True)
        Path(os.path.join(proj, "Cargo.toml")).write_text(
            '[package]\nname = "ubinder_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        main_rs = os.path.join(proj, "src", "main.rs")
        Path(main_rs).write_text(mir_opt_src, encoding="utf-8")

        results["mir_and_llvm"] = {}
        target_fns = [
            "wrap_unwrap_ref",
            "wrap_unwrap_mut",
            "wrap_unwrap_tuple",
            "ref_prop_through_unwrap",
            "dup_mut_via_ptr_read",
        ]
        target_phases = [
            "built.after.mir",
            "analysis-post-cleanup.after.mir",
            "runtime-post-cleanup.after.mir",
            "ReferencePropagation.before.mir",
            "ReferencePropagation.after.mir",
            "ScalarReplacementOfAggregates.before.mir",
            "ScalarReplacementOfAggregates.after.mir",
            "GVN.before.mir",
            "GVN.after.mir",
            "runtime-optimized.after.mir",
        ]
        for label, flags in [
            ("opt0_legacy", ["--edition=2024", "-Copt-level=0", "-Zunstable-options", "-Csymbol-mangling-version=legacy", "-Zmir-opt-level=0"]),
            ("opt2_v0", ["--edition=2024", "-Copt-level=2", "-Csymbol-mangling-version=v0", "-Zmir-opt-level=2"]),
        ]:
            mdir = os.path.join(td, f"mir_{label}")
            os.makedirs(mdir)
            ll_path = os.path.join(td, f"{label}.ll")
            lib_rs = os.path.join(td, "mir_lib.rs")
            Path(lib_rs).write_text(mir_opt_src, encoding="utf-8")
            r = run_cmd([
                rustc, *flags, "--crate-type=lib", "--emit=llvm-ir", "-Zdump-mir=all", f"-Zdump-mir-dir={mdir}", lib_rs, "-o", ll_path
            ])
            ll_txt = Path(ll_path).read_text(encoding="utf-8") if os.path.exists(ll_path) else ""
            llvm_fns = {}
            for line in ll_txt.splitlines():
                if line.startswith("define "):
                    for fn in target_fns:
                        if fn in line:
                            idx = ll_txt.find(line)
                            end = ll_txt.find("\n}", idx)
                            llvm_fns[fn] = ll_txt[idx:end + 2]
            mir_dumps = {}
            for mf in sorted(os.listdir(mdir)):
                if any(fn in mf for fn in target_fns) and any(mf.endswith(ph) for ph in target_phases):
                    mir_dumps[mf] = sanitize(Path(os.path.join(mdir, mf)).read_text(encoding="utf-8"), td)
            bin_run = os.path.join(td, f"native_{label}")
            rb = run_cmd([rustc, *flags, main_rs, "-o", bin_run])
            exec_res = run_cmd([bin_run]) if rb["returncode"] == 0 else {"returncode": rb["returncode"], "stdout": ""}
            results["mir_and_llvm"][label] = {
                "emit_returncode": r["returncode"],
                "exec_returncode": exec_res["returncode"],
                "exec_stdout": exec_res["stdout"].strip(),
                "llvm_ir": llvm_fns,
                "mir_dumps": mir_dumps,
            }

        # 4. Miri differential suite: validation panic vs -Zmiri-disable-validation borrow-tracker suppression.
        results["miri"] = {}
        for label, mflags in [
            ("sb_default", ""),
            ("tb_default", "-Zmiri-tree-borrows"),
            ("sb_disable_validation", "-Zmiri-disable-validation"),
            ("tb_disable_validation", "-Zmiri-tree-borrows -Zmiri-disable-validation"),
        ]:
            r = run_cmd(
                [cargo, "+nightly", "miri", "run"],
                cwd=proj,
                env_extra={"MIRIFLAGS": mflags} if mflags else None,
            )
            results["miri"][label] = {
                "miriflags": mflags,
                "returncode": r["returncode"],
                "stdout": r["stdout"].strip(),
                "stderr": sanitize(r["stderr"], td).strip(),
            }

        # 5. Miri invalid-bool and raw-pointer aliasing controls.
        ctrl_proj = os.path.join(td, "miri_controls")
        os.makedirs(os.path.join(ctrl_proj, "src"), exist_ok=True)
        Path(os.path.join(ctrl_proj, "Cargo.toml")).write_text(
            '[package]\nname = "miri_controls"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        Path(os.path.join(ctrl_proj, "src", "main.rs")).write_text(
            """#![feature(unsafe_binders)]
fn invalid_bool_binder() {
    unsafe {
        let b: unsafe<> bool = core::mem::transmute::<u8, unsafe<> bool>(2u8);
        core::hint::black_box(&b);
    }
    println!("INVALID_BOOL_SURVIVED");
}

fn dup_raw_ptr() {
    let mut x = 0u32;
    unsafe {
        let p: *mut u32 = &raw mut x;
        let r1: &mut u32 = &mut *p;
        let r2: &mut u32 = &mut *p;
        *r1 = 10;
        *r2 = 20;
        println!("DUP_RAW={:?}", (*r1, *r2));
    }
}

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("invalid_bool") => invalid_bool_binder(),
        Some("dup_raw") => dup_raw_ptr(),
        _ => panic!("unknown mode"),
    }
}
""",
            encoding="utf-8",
        )
        results["miri_controls"] = {}
        for mode in ["invalid_bool", "dup_raw"]:
            for label, mflags in [("default", ""), ("disable_validation", "-Zmiri-disable-validation")]:
                r = run_cmd(
                    [cargo, "+nightly", "miri", "run", "--", mode],
                    cwd=ctrl_proj,
                    env_extra={"MIRIFLAGS": mflags} if mflags else None,
                )
                results["miri_controls"][f"{mode}__{label}"] = {
                    "mode": mode,
                    "miriflags": mflags,
                    "returncode": r["returncode"],
                    "stdout": r["stdout"].strip(),
                    "stderr": sanitize(r["stderr"], td).strip(),
                }

    if args.json_out:
        out_p = Path(args.json_out)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")

    print("static_checks:", {k: v["returncode"] for k, v in results["static_checks"].items()})
    print("mangling:", {k: (v["returncode"], v.get("exec_stdout")) for k, v in results["mangling"].items()})
    print("mir_and_llvm:", {k: (v["emit_returncode"], v["exec_stdout"], len(v["llvm_ir"]), len(v["mir_dumps"])) for k, v in results["mir_and_llvm"].items()})
    print("miri:", {k: (v["returncode"], v["stdout"]) for k, v in results["miri"].items()})
    print("miri_controls:", {k: (v["returncode"], v["stdout"]) for k, v in results["miri_controls"].items()})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
