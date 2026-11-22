#!/usr/bin/env python3
"""Live rustc + Miri empirical probe for GCA const items vs generic_const_exprs.

Supports both:
  1. Post-1.100.0 nightlies (`gca_min_const_items`, `gca_const_items`, `core::gca!(...)`,
     default `-Znext-solver=globally`, `#160895` GCE downgrade warning, `E0557` removal of
     `min_generic_const_args`), and
  2. Pre-1.100.0 nightlies such as `1.98.0-nightly` (`min_generic_const_args`,
     `generic_const_args`, `type const` syntax, explicit `-Znext-solver=globally` vs default
     old solver).

Executes real `rustc` and `miri` subprocesses in a temporary directory and emits structured JSON.
Zero hardcoded results; every return code, stdout, and stderr is captured directly from the live
toolchain.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
from typing import Any


def scrub_paths(text: str, tmpdir: str, sysroot: str = "") -> str:
    out = text.replace(tmpdir, "<TMP>")
    if sysroot:
        out = out.replace(sysroot, "<SYSROOT>")
    home = str(pathlib.Path.home())
    if home:
        out = out.replace(home, "<HOME>")
    return out


def run_cmd(
    cmd: list[str],
    *,
    env: dict[str, str] | None = None,
    cwd: str | None = None,
    timeout: int = 60,
) -> tuple[int, str, str]:
    proc = subprocess.run(
        cmd,
        env=env,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


def discover_toolchain() -> dict[str, Any]:
    path_env = os.environ.get("PATH", "")
    cargo_bin = str(pathlib.Path.home() / ".cargo" / "bin")
    if cargo_bin not in path_env.split(os.pathsep) and pathlib.Path(cargo_bin).is_dir():
        path_env = f"{cargo_bin}{os.pathsep}{path_env}"
    env = dict(os.environ, PATH=path_env)

    rustc = shutil.which("rustc", path=path_env)
    if not rustc:
        raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")

    rc, rustc_v, _ = run_cmd([rustc, "--version", "--verbose"], env=env)
    if rc != 0:
        raise RuntimeError("failed to query rustc --version --verbose")

    rc_s, sysroot, _ = run_cmd([rustc, "--print", "sysroot"], env=env)
    sysroot = sysroot.strip() if rc_s == 0 else ""

    miri_bin = None
    if sysroot:
        cand = pathlib.Path(sysroot) / "bin" / "miri"
        if cand.is_file():
            miri_bin = str(cand)

    cargo_miri = shutil.which("cargo-miri", path=path_env)
    miri_version = ""
    if cargo_miri:
        rc_m, m_out, _ = run_cmd(["cargo", "miri", "--version"], env=env)
        if rc_m == 0:
            miri_version = m_out.strip()

    # Detect post-1.100.0 GCA regime by probing `#![feature(gca_min_const_items)]`
    with tempfile.TemporaryDirectory(prefix="gca_detect_") as td:
        probe_rs = pathlib.Path(td) / "detect.rs"
        probe_rs.write_text(
            "#![allow(incomplete_features)]\n"
            "#![feature(gca_min_const_items)]\n"
            "pub const X: usize = core::gca!(1);\n",
            encoding="utf-8",
        )
        rc_d, _, err_d = run_cmd(
            [rustc, "--edition=2024", "--crate-type=lib", "--emit=metadata", str(probe_rs), "-o", str(pathlib.Path(td) / "d.rmeta")],
            env=env,
        )
        regime = "post_1_100_gca" if rc_d == 0 else "pre_1_100_mgca"

    return {
        "env": env,
        "rustc": rustc,
        "rustc_version": rustc_v.strip(),
        "sysroot": sysroot,
        "miri_bin": miri_bin,
        "miri_version": miri_version,
        "regime": regime,
    }


def compile_check(
    tc: dict[str, Any],
    td: str,
    name: str,
    src: str,
    extra_args: list[str] | None = None,
    crate_type: str = "lib",
) -> dict[str, Any]:
    rs = pathlib.Path(td) / f"{name}.rs"
    out = pathlib.Path(td) / f"{name}.out"
    rs.write_text(src, encoding="utf-8")
    cmd = [
        tc["rustc"],
        "--edition=2024",
        f"--crate-type={crate_type}",
        *(extra_args or []),
        str(rs),
        "-o",
        str(out),
    ]
    rc, stdout, stderr = run_cmd(cmd, env=tc["env"])
    return {
        "cmd": [scrub_paths(c, td, tc["sysroot"]) for c in cmd],
        "rc": rc,
        "stdout": scrub_paths(stdout, td, tc["sysroot"]),
        "stderr": scrub_paths(stderr, td, tc["sysroot"]),
        "reverted_next_solver": "reverted the setting to `-Znext-solver=coherence`" in stderr,
        "out_path": str(out),
    }


def run_miri_nocore(
    tc: dict[str, Any],
    td: str,
    name: str,
    src: str,
    extra_args: list[str] | None = None,
) -> dict[str, Any]:
    if not tc["miri_bin"] or not tc["sysroot"]:
        return {"skipped": True, "reason": "miri binary or sysroot unavailable"}
    rs = pathlib.Path(td) / f"{name}.rs"
    rs.write_text(src, encoding="utf-8")
    miri_env = dict(tc["env"])
    lib_dir = str(pathlib.Path(tc["sysroot"]) / "lib")
    prev_ld = miri_env.get("LD_LIBRARY_PATH", "")
    miri_env["LD_LIBRARY_PATH"] = f"{lib_dir}:{prev_ld}" if prev_ld else lib_dir
    cmd = [
        tc["miri_bin"],
        "--edition=2024",
        "--sysroot",
        tc["sysroot"],
        *(extra_args or []),
        str(rs),
    ]
    rc, stdout, stderr = run_cmd(cmd, env=miri_env)
    return {
        "cmd": [scrub_paths(c, td, tc["sysroot"]) for c in cmd],
        "rc": rc,
        "stdout": scrub_paths(stdout, td, tc["sysroot"]),
        "stderr": scrub_paths(stderr, td, tc["sysroot"]),
    }


def run_suite(tc: dict[str, Any]) -> dict[str, Any]:
    regime = tc["regime"]
    results: dict[str, Any] = {
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "regime": regime,
        "rustc_version": tc["rustc_version"],
        "miri_version": tc["miri_version"],
    }

    with tempfile.TemporaryDirectory(prefix="r10_gca_probe_") as td:
        # ------------------------------------------------------------------
        # PART A: Definitional normalization of associated & free const items
        #         under -Znext-solver=globally (native + Miri + MIR check)
        # ------------------------------------------------------------------
        if regime == "post_1_100_gca":
            part_a_src = """#![allow(incomplete_features)]
#![feature(gca_min_const_items, gca_const_items)]

pub trait Tr {
    #[rustc_always_gca]
    const SIZE: usize;
}

pub struct Four;
impl Tr for Four {
    const SIZE: usize = core::gca!(4);
}

pub const GLOBAL: usize = core::gca!(5);

pub fn make_buf<T: Tr>(x: u8) -> [u8; core::gca!(<T as Tr>::SIZE)] {
    [x; core::gca!(<T as Tr>::SIZE)]
}

fn main() {
    let buf: [u8; 4] = make_buf::<Four>(7);
    let g: [u8; 5] = [0u8; core::gca!(GLOBAL)];
    println!("EXACT_LEN={} FIRST={} GLOBAL_LEN={}", buf.len(), buf[0], g.len());
}
"""
            part_a_flags: list[str] = []
            part_a_nocore = """#![allow(incomplete_features, internal_features)]
#![feature(gca_min_const_items, gca_const_items, no_core, lang_items, rustc_attrs)]
#![no_core]
#![no_main]

#[lang = "sized"]
pub trait Sized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "const_param_ty"]
pub trait ConstParamTy {}
impl Copy for u8 {}
impl Copy for usize {}
impl ConstParamTy for usize {}

#[rustc_builtin_macro(gca)]
macro_rules! gca { ($($t:tt)*) => {}; }

pub trait Tr {
    #[rustc_always_gca]
    const SIZE: usize;
}
pub struct Four;
impl Tr for Four {
    const SIZE: usize = gca!(4);
}
pub const GLOBAL: usize = gca!(5);

pub fn make_buf<T: Tr>(x: u8) -> [u8; gca!(<T as Tr>::SIZE)] {
    [x; gca!(<T as Tr>::SIZE)]
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let [b0, b1, b2, b3]: [u8; 4] = make_buf::<Four>(7);
    let [g0, _, _, _, g4]: [u8; 5] = [0u8; gca!(GLOBAL)];
    match (b0, b1, b2, b3, g0, g4) {
        (7, 7, 7, 7, 0, 0) => 0,
        _ => 1,
    }
}
"""
        else:
            part_a_src = """#![allow(incomplete_features)]
#![feature(min_generic_const_args, generic_const_args)]

pub trait Tr {
    type const SIZE: usize;
}

pub struct Four;
impl Tr for Four {
    type const SIZE: usize = 4;
}

pub type const GLOBAL: usize = 5;

pub fn make_buf<T: Tr>(x: u8) -> [u8; <T as Tr>::SIZE] {
    [x; <T as Tr>::SIZE]
}

fn main() {
    let buf: [u8; 4] = make_buf::<Four>(7);
    let g: [u8; 5] = [0u8; GLOBAL];
    println!("EXACT_LEN={} FIRST={} GLOBAL_LEN={}", buf.len(), buf[0], g.len());
}
"""
            part_a_flags = ["-Znext-solver=globally"]
            part_a_nocore = """#![allow(incomplete_features, internal_features)]
#![feature(min_generic_const_args, generic_const_args, no_core, lang_items, rustc_attrs)]
#![no_core]
#![no_main]

#[lang = "sized"]
pub trait Sized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "const_param_ty"]
pub trait ConstParamTy {}
impl Copy for u8 {}
impl Copy for usize {}
impl ConstParamTy for usize {}

pub trait Tr {
    type const SIZE: usize;
}
pub struct Four;
impl Tr for Four {
    type const SIZE: usize = 4;
}
pub type const GLOBAL: usize = 5;

pub fn make_buf<T: Tr>(x: u8) -> [u8; <T as Tr>::SIZE] {
    [x; <T as Tr>::SIZE]
}

#[unsafe(no_mangle)]
pub fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let [b0, b1, b2, b3]: [u8; 4] = make_buf::<Four>(7);
    let [g0, _, _, _, g4]: [u8; 5] = [0u8; GLOBAL];
    match (b0, b1, b2, b3, g0, g4) {
        (7, 7, 7, 7, 0, 0) => 0,
        _ => 1,
    }
}
"""

        comp_a = compile_check(tc, td, "part_a_bin", part_a_src, extra_args=part_a_flags, crate_type="bin")
        native_rc, native_out, native_err = (-1, "", "")
        if comp_a["rc"] == 0:
            native_rc, native_out, native_err = run_cmd([comp_a["out_path"]], env=tc["env"])

        # Dump monomorphized/post-cleanup MIR for part_a_bin to observe erased/normalized lengths
        mir_dump_dir = pathlib.Path(td) / "mir_dump"
        mir_dump_dir.mkdir(exist_ok=True)
        mir_a = compile_check(
            tc,
            td,
            "part_a_mir",
            part_a_src,
            extra_args=[*part_a_flags, "--emit=mir"],
            crate_type="bin",
        )
        mir_excerpt = ""
        if mir_a["rc"] == 0 and pathlib.Path(mir_a["out_path"]).is_file():
            mir_text = pathlib.Path(mir_a["out_path"]).read_text(encoding="utf-8")
            lines = mir_text.splitlines()
            interesting = [
                ln for ln in lines
                if "make_buf" in ln or "[u8; 4]" in ln or "[u8; 5]" in ln or "::SIZE" in ln or "GLOBAL" in ln
            ]
            mir_excerpt = "\n".join(interesting[:40])

        miri_a_sb = run_miri_nocore(tc, td, "part_a_nocore_sb", part_a_nocore, extra_args=part_a_flags)
        miri_a_tb = run_miri_nocore(
            tc, td, "part_a_nocore_tb", part_a_nocore, extra_args=[*part_a_flags, "-Zmiri-tree-borrows"]
        )
        # Negative canary: flip expected value to prove Miri actually executes the assertion
        miri_a_neg = run_miri_nocore(
            tc,
            td,
            "part_a_nocore_neg",
            part_a_nocore.replace("(7, 7, 7, 7, 0, 0)", "(99, 7, 7, 7, 0, 0)"),
            extra_args=part_a_flags,
        )

        # Also test part_a under default solver (without -Znext-solver=globally) in pre-1.100 regime
        part_a_default_solver = None
        if regime == "pre_1_100_mgca":
            part_a_default_solver = compile_check(
                tc, td, "part_a_default_solver", part_a_src, extra_args=[], crate_type="bin"
            )
            part_a_default_solver.pop("out_path", None)

        comp_a.pop("out_path", None)
        results["part_a_gca_const_items_definitional_normalization"] = {
            "compile": comp_a,
            "native_rc": native_rc,
            "native_stdout": native_out.strip(),
            "native_stderr": native_err.strip(),
            "mir_excerpt": mir_excerpt,
            "miri_stacked_borrows": miri_a_sb,
            "miri_tree_borrows": miri_a_tb,
            "miri_negative_canary": miri_a_neg,
            "pre_1_100_without_next_solver_flag": part_a_default_solver,
        }

        # ------------------------------------------------------------------
        # PART B: Feature removal (E0557) / rename transition, plain const compat,
        #         and bare associated const rejection with diagnostic help
        # ------------------------------------------------------------------
        b_removed_mgca = compile_check(
            tc,
            td,
            "removed_min_generic_const_args",
            "#![feature(min_generic_const_args)]\npub const X: usize = 1;\n",
        )
        b_removed_mgca.pop("out_path", None)

        b_gca_feature_probe = compile_check(
            tc,
            td,
            "gca_min_const_items_probe",
            "#![allow(incomplete_features)]\n#![feature(gca_min_const_items)]\npub const X: usize = 1;\n",
        )
        b_gca_feature_probe.pop("out_path", None)

        if regime == "post_1_100_gca":
            b_plain_const = compile_check(
                tc,
                td,
                "gca_preserves_plain_const_in_array_ty",
                "#![allow(incomplete_features)]\n"
                "#![feature(gca_min_const_items, gca_const_items)]\n"
                "pub const PLAIN: usize = 3;\n"
                "pub fn f() -> [u8; PLAIN] { [0; PLAIN] }\n",
            )
            b_bare_assoc = compile_check(
                tc,
                td,
                "bare_assoc_const_without_gca_macro",
                "#![allow(incomplete_features)]\n"
                "#![feature(gca_min_const_items)]\n"
                "pub trait Tr { const N: usize; }\n"
                "pub fn f<T: Tr>() -> [u8; T::N] { [0; T::N] }\n",
            )
        else:
            b_plain_const = compile_check(
                tc,
                td,
                "mgca_plain_const_in_array_ty",
                "#![allow(incomplete_features)]\n"
                "#![feature(min_generic_const_args)]\n"
                "pub const PLAIN: usize = 3;\n"
                "pub fn f() -> [u8; PLAIN] { [0; PLAIN] }\n",
            )
            b_bare_assoc = compile_check(
                tc,
                td,
                "bare_assoc_const_without_type_const",
                "#![allow(incomplete_features)]\n"
                "#![feature(min_generic_const_args)]\n"
                "pub trait Tr { const N: usize; }\n"
                "pub fn f<T: Tr>() -> [u8; T::N] { [0; T::N] }\n",
            )
        b_plain_const.pop("out_path", None)
        b_bare_assoc.pop("out_path", None)

        # Also test generic_const_args requiring -Znext-solver=globally on pre-1.100
        b_gca_requires_next_solver = None
        if regime == "post_1_100_gca":
            b_gca_requires_next_solver = compile_check(
                tc,
                td,
                "gca_const_items_under_coherence_solver",
                "#![allow(incomplete_features)]\n"
                "#![feature(gca_min_const_items, gca_const_items)]\n"
                "pub const X: usize = core::gca!(1);\n",
                extra_args=["-Znext-solver=coherence"],
            )
        else:
            b_gca_requires_next_solver = compile_check(
                tc,
                td,
                "generic_const_args_under_default_solver",
                "#![allow(incomplete_features)]\n"
                "#![feature(min_generic_const_args, generic_const_args)]\n"
                "pub type const X: usize = 1;\n",
                extra_args=[],
            )
        b_gca_requires_next_solver.pop("out_path", None)

        results["part_b_mgca_e0557_removal_and_plain_const_compat"] = {
            "min_generic_const_args_feature_check": b_removed_mgca,
            "gca_min_const_items_feature_check": b_gca_feature_probe,
            "plain_const_in_array_ty": b_plain_const,
            "bare_assoc_const_rejected": b_bare_assoc,
            "const_items_requires_next_solver": b_gca_requires_next_solver,
        }

        # ------------------------------------------------------------------
        # PART C: GCE vs GCA — next-solver downgrade/incompatibility,
        #         N+1 vs 1+N E0308 non-commutativity, and N-1 post-instantiation E0080
        # ------------------------------------------------------------------
        gce_noncomm_src = """#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub fn comm_fail<const N: usize>(a: [u8; N + 1]) -> [u8; 1 + N]
where
    [(); N + 1]:,
    [(); 1 + N]:,
{
    a
}
"""
        gce_uncalled_sub_src = """#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub fn sub_one<const N: usize>() -> [u8; N - 1]
where
    [(); N - 1]:,
{
    [0u8; N - 1]
}
"""
        gce_called_zero_src = """#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub fn sub_one<const N: usize>() -> [u8; N - 1]
where
    [(); N - 1]:,
{
    [0u8; N - 1]
}

pub fn trigger() -> [u8; 0] {
    let _ = sub_one::<0>();
    []
}
"""
        c_gce_noncomm = compile_check(tc, td, "gce_noncomm_default", gce_noncomm_src)
        c_gce_noncomm.pop("out_path", None)

        c_gce_noncomm_ns = compile_check(
            tc, td, "gce_noncomm_next_solver", gce_noncomm_src, extra_args=["-Znext-solver=globally"]
        )
        c_gce_noncomm_ns.pop("out_path", None)

        c_gce_uncalled = compile_check(tc, td, "gce_n_minus_1_uncalled", gce_uncalled_sub_src)
        c_gce_uncalled.pop("out_path", None)

        c_gce_called_zero = compile_check(tc, td, "gce_n_minus_1_called_zero", gce_called_zero_src)
        c_gce_called_zero.pop("out_path", None)

        if regime == "post_1_100_gca":
            gca_arith_src = """#![allow(incomplete_features)]
#![feature(gca_min_const_items, gca_const_items)]
pub trait Tr { #[rustc_always_gca] const N: usize; }
pub fn forbid_arith<T: Tr>() -> [u8; core::gca!(T::N + 1)] {
    [0; core::gca!(T::N + 1)]
}
"""
        else:
            gca_arith_src = """#![allow(incomplete_features)]
#![feature(min_generic_const_args, generic_const_args)]
pub trait Tr { type const N: usize; }
pub fn forbid_arith<T: Tr>() -> [u8; T::N + 1] {
    [0; T::N + 1]
}
"""
        c_gca_arith = compile_check(
            tc, td, "gca_generic_arith_rejected", gca_arith_src, extra_args=part_a_flags
        )
        c_gca_arith.pop("out_path", None)

        # Also test GCE identical syntax N+1 -> N+1 succeeds (sharpening E0308 to syntactic order)
        gce_same_order_src = """#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

pub fn same_order_ok<const N: usize>(a: [u8; N + 1]) -> [u8; N + 1]
where
    [(); N + 1]:,
{
    a
}
"""
        c_gce_same_order = compile_check(tc, td, "gce_same_order_ok", gce_same_order_src)
        c_gce_same_order.pop("out_path", None)

        results["part_c_gce_next_solver_downgrade_noncomm_and_post_mono_vs_gca"] = {
            "gce_noncomm_default_solver": c_gce_noncomm,
            "gce_noncomm_explicit_next_solver_globally": c_gce_noncomm_ns,
            "gce_same_order_n_plus_1_ok": c_gce_same_order,
            "gce_n_minus_1_uncalled_def": c_gce_uncalled,
            "gce_n_minus_1_called_at_0": c_gce_called_zero,
            "gca_generic_arith_rejected_at_def": c_gca_arith,
        }

        # ------------------------------------------------------------------
        # PART D: Cyclic constant E0391 via `is_trivial_const` -> `mir_built`
        # ------------------------------------------------------------------
        part_d_plain_src = """pub const A: usize = B;
pub const B: usize = A;
pub type Arr = [u8; A];
"""
        d_plain = compile_check(tc, td, "part_d_cyclic_plain", part_d_plain_src)
        d_plain.pop("out_path", None)

        if regime == "post_1_100_gca":
            part_d_gca_src = """#![allow(incomplete_features)]
#![feature(gca_min_const_items, gca_const_items)]
pub const A: usize = core::gca!(B);
pub const B: usize = core::gca!(A);
pub type Arr = [u8; core::gca!(A)];
"""
        else:
            part_d_gca_src = """#![allow(incomplete_features)]
#![feature(min_generic_const_args, generic_const_args)]
pub type const A: usize = B;
pub type const B: usize = A;
pub type Arr = [u8; A];
"""
        d_gca = compile_check(tc, td, "part_d_cyclic_gca", part_d_gca_src, extra_args=part_a_flags)
        d_gca.pop("out_path", None)

        results["part_d_cyclic_const_e0391"] = {
            "plain_const_cycle_e0391": d_plain,
            "direct_gca_const_cycle": d_gca,
        }

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", help="Optional path to write JSON results")
    args = parser.parse_args()

    tc = discover_toolchain()
    results = run_suite(tc)
    payload = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        pathlib.Path(args.out).write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
