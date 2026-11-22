#!/usr/bin/env python3
"""Reproducible empirical probe for rustc native contracts (#![feature(contracts)]),
defining-crate vs. caller-crate -Z contract-checks scoping, multi-exit #[ensures]
interception/bypasses, capture/syntax diagnostics, CTFE const_eval_select! bypass,
LLVM range/nuw/nsw deduction, and Miri intrinsic fallback behavior.

Usage:
    python3 support/probe_rustc_contracts.py [--output path/to/results.json]
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Any


def run_cmd(
    cmd: list[str],
    cwd: pathlib.Path | None = None,
    env: dict[str, str] | None = None,
) -> tuple[int, str, str]:
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    return proc.returncode, proc.stdout, proc.stderr


def scrub_text(text: str, extra_roots: list[str] | None = None) -> str:
    """Remove ephemeral temp directories, PIDs, and local filesystem prefixes."""
    out = text
    for root in extra_roots or []:
        if root:
            out = out.replace(root, "<TMPDIR>")
    home = str(pathlib.Path.home())
    if home:
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<TMPDIR>", out)
    out = re.sub(r"thread 'main' \(\d+\)", "thread 'main' (<PID>)", out)
    return out


def extract_llvm_fn(llvm_ir: str, symbol: str) -> str:
    idx = llvm_ir.find(f"@{symbol}(")
    if idx == -1:
        # Fallback for mangled Rust symbols containing the function name
        m = re.search(rf"define [^\n]*@{re.escape(symbol)}[^\n]*\(", llvm_ir)
        if not m:
            m = re.search(rf"define [^\n]*{re.escape(symbol)}[^\n]*\(", llvm_ir)
        if not m:
            return ""
        start = m.start()
        idx = m.end()
    else:
        start = llvm_ir.rfind("define ", 0, idx)
    end = llvm_ir.find("\n}\n", idx)
    if start == -1 or end == -1:
        return ""
    return llvm_ir[start : end + 2]


def resolve_rustc_env() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(pathlib.Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", "").split(os.pathsep):
        env["PATH"] = cargo_bin + os.pathsep + env.get("PATH", "")
    return env


def probe_1_modes(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    src = """#![feature(contracts)]
use core::contracts::{requires, ensures};

#[unsafe(no_mangle)]
#[requires(x < 100)]
#[ensures(move |ret| *ret == x + 1 && *ret > 0 && *ret <= 100)]
pub fn inc_bounded(x: u32) -> u32 {
    x + 1
}

#[unsafe(no_mangle)]
#[requires(true)]
#[ensures(|ret| *ret > 0)]
pub fn buggy_early_return(flag: bool) -> u32 {
    if flag {
        return 0;
    }
    42
}

#[requires(x > 0)]
pub const fn pos(x: u32) -> u32 {
    x
}

pub const GOOD_CONST: u32 = pos(7);

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "ok" => println!(
            "OK={} EARLY_FALSE={} CONST={}",
            inc_bounded(41),
            buggy_early_return(false),
            GOOD_CONST
        ),
        "violate_requires" => println!("REQ={}", inc_bounded(200)),
        "violate_ensures_early" => println!("ENS={}", buggy_early_return(true)),
        _ => {}
    }
}
"""
    src_path = tmp / "contracts_probe.rs"
    src_path.write_text(src)
    roots = [str(tmp)]
    results: dict[str, Any] = {}

    for mode_name, extra_flags in [
        ("default_O2", ["-C", "opt-level=2"]),
        ("contract_yes_O2", ["-C", "opt-level=2", "-Z", "contract-checks=yes"]),
        ("contract_no_O2", ["-C", "opt-level=2", "-Z", "contract-checks=no"]),
    ]:
        sub = tmp / f"p1_{mode_name}"
        sub.mkdir()
        mir_dir = sub / "mir_dump"
        rc, _, err = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-name",
                "contracts_probe",
                *extra_flags,
                "--emit=llvm-ir,mir,link",
                "--out-dir",
                str(sub),
                "-Z",
                "dump-mir=inc_bounded",
                "-Z",
                f"dump-mir-dir={mir_dir}",
                str(src_path),
            ],
            env=env,
        )
        ll = (sub / "contracts_probe.ll").read_text() if rc == 0 else ""
        pc_files = [
            p
            for p in sorted(mir_dir.glob("*runtime-post-cleanup*after.mir"))
            if "closure" not in p.name
        ]
        opt_files = [
            p
            for p in sorted(mir_dir.glob("*runtime-optimized*after.mir"))
            if "closure" not in p.name
        ]
        pc_mir = pc_files[0].read_text() if pc_files else ""
        opt_mir = opt_files[0].read_text() if opt_files else ""
        inc_ir = extract_llvm_fn(ll, "inc_bounded")
        early_ir = extract_llvm_fn(ll, "buggy_early_return")

        runtime_res: dict[str, Any] = {}
        bin_path = sub / "contracts_probe"
        if rc == 0 and bin_path.exists():
            for arg in ("ok", "violate_requires", "violate_ensures_early"):
                rrc, rout, rerr = run_cmd([str(bin_path), arg], env=env)
                runtime_res[arg] = {
                    "rc": rrc,
                    "stdout": rout.strip(),
                    "stderr_lines": [
                        scrub_text(line, roots)
                        for line in rerr.splitlines()
                        if line.strip()
                    ][:5],
                }

        results[mode_name] = {
            "compile_rc": rc,
            "inc_bounded_mir_signals": {
                "has_runtime_checks_contract_checks_postcleanup": "ContractChecks" in pc_mir,
                "has_runtime_checks_contract_checks_opt": "ContractChecks" in opt_mir,
                "has_baked_const_true_postcleanup": "= const true;" in pc_mir,
                "has_baked_const_false_postcleanup": "= const false;" in pc_mir,
                "has_contract_check_requires_postcleanup": "contract_check_requires" in pc_mir,
                "has_contract_check_requires_opt": "contract_check_requires" in opt_mir,
                "has_build_check_ensures_postcleanup": "build_check_ensures" in pc_mir,
                "has_build_check_ensures_opt": "build_check_ensures" in opt_mir,
                "has_contract_check_ensures_postcleanup": "contract_check_ensures" in pc_mir,
                "has_contract_check_ensures_opt": "contract_check_ensures" in opt_mir,
            },
            "inc_bounded_llvm_ir_lines": len(inc_ir.splitlines()),
            "inc_bounded_llvm_ir": inc_ir,
            "inc_bounded_has_range_1_101": "range(i32 1, 101)" in inc_ir,
            "inc_bounded_has_add_nuw_nsw": "add nuw nsw i32" in inc_ir,
            "inc_bounded_has_panic_nounwind_len_21": "panic_nounwind" in inc_ir
            and "i64 noundef 21" in inc_ir,
            "inc_bounded_has_panic_nounwind_len_20": "panic_nounwind" in inc_ir
            and "i64 noundef 20" in inc_ir,
            "buggy_early_return_llvm_ir_lines": len(early_ir.splitlines()),
            "buggy_early_return_llvm_ir": early_ir,
            "buggy_early_return_has_panic_nounwind_len_20": "panic_nounwind" in early_ir
            and "i64 noundef 20" in early_ir,
            "runtime": runtime_res,
        }
    return results


def probe_2_cross_crate(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    up_src = """#![feature(contracts)]
use core::contracts::{requires, ensures};

#[inline]
#[requires(x < 10)]
#[ensures(move |r| *r == x + 1)]
pub fn inline_inc(x: u32) -> u32 {
    x + 1
}

#[inline(always)]
#[requires(x < 10)]
pub fn inline_always_inc(x: u32) -> u32 {
    x + 1
}

#[requires(x.into() < 10u64)]
pub fn generic_inc<T: Copy + Into<u64>>(x: T) -> u64 {
    x.into() + 1
}
"""
    ds_src = """fn main() {
    let which = std::env::args().nth(1).unwrap_or_default();
    match which.as_str() {
        "inline" => println!("UP_INLINE={}", up::inline_inc(50)),
        "inline_always" => println!("UP_ALWAYS={}", up::inline_always_inc(50)),
        "generic" => println!("UP_GENERIC={}", up::generic_inc(50u32)),
        _ => {}
    }
}
"""
    sub = tmp / "p2_cross_crate"
    sub.mkdir()
    (sub / "up.rs").write_text(up_src)
    (sub / "ds.rs").write_text(ds_src)
    roots = [str(tmp)]
    out: dict[str, Any] = {}

    for up_f in ("no", "yes"):
        up_lib = sub / f"libup_{up_f}.rlib"
        urc, _, _ = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=rlib",
                "--crate-name=up",
                "-C",
                "opt-level=2",
                f"-Zcontract-checks={up_f}",
                "-o",
                str(up_lib),
                str(sub / "up.rs"),
            ],
            env=env,
        )
        out[f"up_{up_f}_compile_rc"] = urc
        for ds_f in ("no", "yes"):
            ds_bin = sub / f"ds_{up_f}_{ds_f}"
            drc, _, _ = run_cmd(
                [
                    "rustc",
                    "--edition=2024",
                    "-C",
                    "opt-level=2",
                    f"-Zcontract-checks={ds_f}",
                    "--extern",
                    f"up={up_lib}",
                    "-o",
                    str(ds_bin),
                    str(sub / "ds.rs"),
                ],
                env=env,
            )
            cell: dict[str, Any] = {"compile_rc": drc}
            for which in ("inline", "inline_always", "generic"):
                rrc, rout, rerr = run_cmd([str(ds_bin), which], env=env)
                cell[which] = {
                    "rc": rrc,
                    "stdout": rout.strip(),
                    "failed_requires": "failed requires check" in rerr,
                    "stderr_lines": [
                        scrub_text(l, roots) for l in rerr.splitlines() if l.strip()
                    ][:4],
                }
            out[f"up_{up_f}_ds_{ds_f}"] = cell
    return out


def probe_3_capture_and_syntax(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    sub = tmp / "p3_diag"
    sub.mkdir()
    roots = [str(tmp)]
    cases = {
        "borrow_capture_e0597": """#![feature(contracts)]
use core::contracts::ensures;
#[ensures(|ret| *ret == x + 1)]
pub fn f(x: u32) -> u32 { x + 1 }
""",
        "non_copy_move_capture_e0277": """#![feature(contracts)]
use core::contracts::ensures;
#[ensures(move |ret| *ret == v.len())]
pub fn f(v: Vec<u8>) -> usize { v.len() }
""",
        "non_static_ref_capture": """#![feature(contracts)]
use core::contracts::ensures;
#[ensures(move |ret| *ret == *x + 1)]
pub fn f(x: &u32) -> u32 { *x + 1 }
""",
        "method_call_inference_e0282": """#![feature(contracts)]
use core::contracts::ensures;
#[ensures(|ret| ret.is_ok())]
pub fn f(x: Result<u32, u32>) -> Result<u32, u32> { x }
""",
        "reversed_attr_order": """#![feature(contracts)]
use core::contracts::{requires, ensures};
#[ensures(move |ret| *ret == x + 1)]
#[requires(x < 100)]
pub fn f(x: u32) -> u32 { x + 1 }
""",
        "stacked_requires": """#![feature(contracts)]
use core::contracts::requires;
#[requires(x > 0)]
#[requires(x < 100)]
pub fn f(x: u32) -> u32 { x }
""",
        "async_fn_rejected": """#![feature(contracts)]
use core::contracts::requires;
#[requires(x > 0)]
pub async fn f(x: u32) -> u32 { x }
""",
        "bodyless_trait_fn_rejected": """#![feature(contracts)]
use core::contracts::requires;
pub trait T {
    #[requires(x > 0)]
    fn f(x: u32) -> u32;
}
""",
        "raw_contract_checks_intrinsic_e0093": """#![feature(intrinsics)]
#[rustc_intrinsic]
pub const fn contract_checks() -> bool;
""",
    }
    out: dict[str, Any] = {}
    for name, code in cases.items():
        p = sub / f"{name}.rs"
        p.write_text(code)
        rc, _, err = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Zcontract-checks=yes",
                "--out-dir",
                str(sub),
                str(p),
            ],
            env=env,
        )
        codes = sorted(set(re.findall(r"error\[E\d+\]", err)))
        err_lines = [
            scrub_text(l, roots)
            for l in err.splitlines()
            if l.startswith("error")
        ]
        out[name] = {"rc": rc, "error_codes": codes, "error_lines": err_lines[:4]}
    return out


def probe_4_exit_paths(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    sub = tmp / "p4_exits"
    sub.mkdir()
    roots = [str(tmp)]
    out: dict[str, Any] = {}

    # 4a. ?, do yeet, and unwinding panic
    exits_src = """#![feature(contracts)]
#![feature(yeet_expr)]
use core::contracts::ensures;
use std::panic;

#[ensures(|ret: &Result<u32, u32>| ret.is_ok())]
pub fn try_exit(x: Result<u32, u32>) -> Result<u32, u32> {
    let v = x?;
    Ok(v + 1)
}

#[ensures(|ret: &Result<u32, u32>| ret.is_ok())]
pub fn yeet_exit(fail: bool) -> Result<u32, u32> {
    if fail {
        do yeet 9u32;
    }
    Ok(1)
}

#[ensures(|_| false)]
pub fn panics_before_return() -> u32 {
    panic!("body panicked");
}

fn main() {
    let m = std::env::args().nth(1).unwrap_or_default();
    match m.as_str() {
        "try_ok" => println!("{:?}", try_exit(Ok(1))),
        "try_err" => println!("{:?}", try_exit(Err(1))),
        "yeet_ok" => println!("{:?}", yeet_exit(false)),
        "yeet_err" => println!("{:?}", yeet_exit(true)),
        "unwind_caught" => {
            let res = panic::catch_unwind(|| panics_before_return());
            println!("CAUGHT={}", res.is_err());
        }
        _ => {}
    }
}
"""
    (sub / "exits.rs").write_text(exits_src)
    rc, _, _ = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "-Zcontract-checks=yes",
            "-o",
            str(sub / "exits"),
            str(sub / "exits.rs"),
        ],
        env=env,
    )
    out["try_yeet_unwind_compile_rc"] = rc
    for m in ("try_ok", "try_err", "yeet_ok", "yeet_err", "unwind_caught"):
        rrc, rout, rerr = run_cmd([str(sub / "exits"), m], env=env)
        out[m] = {
            "rc": rrc,
            "stdout": rout.strip(),
            "failed_ensures": "failed ensures check" in rerr,
            "stderr_lines": [
                scrub_text(l, roots) for l in rerr.splitlines() if l.strip()
            ][:4],
        }

    # 4b. Explicit tail call (`become`) bypassing checked_return
    become_src = """#![feature(contracts)]
#![feature(explicit_tail_calls)]
use core::contracts::ensures;

fn helper() -> u32 {
    0
}

#[ensures(|ret| *ret > 0)]
pub fn tail_bypass() -> u32 {
    become helper()
}

fn main() {
    println!("TAIL={}", tail_bypass());
}
"""
    (sub / "become.rs").write_text(become_src)
    brc, _, _ = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "-Zcontract-checks=yes",
            "-o",
            str(sub / "become_bin"),
            str(sub / "become.rs"),
        ],
        env=env,
    )
    if brc == 0:
        rrc, rout, rerr = run_cmd([str(sub / "become_bin")], env=env)
        out["explicit_tail_call_become"] = {
            "compile_rc": brc,
            "runtime_rc": rrc,
            "stdout": rout.strip(),
            "failed_ensures": "failed ensures check" in rerr,
        }
    else:
        out["explicit_tail_call_become"] = {"compile_rc": brc}
    return out


def probe_5_ctfe_bypass(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    sub = tmp / "p5_ctfe"
    sub.mkdir()
    src = """#![feature(contracts)]
use core::contracts::{requires, ensures};

#[requires(x > 0)]
#[ensures(|ret| *ret > 100)]
pub const fn bad_const_fn(x: u32) -> u32 {
    x
}

pub const BAD: u32 = bad_const_fn(0);

fn main() {
    println!("BAD_CONST={}", BAD);
}
"""
    (sub / "ctfe.rs").write_text(src)
    out: dict[str, Any] = {}
    for flag in ("no", "yes"):
        bin_path = sub / f"ctfe_{flag}"
        rc, _, _ = run_cmd(
            [
                "rustc",
                "--edition=2024",
                f"-Zcontract-checks={flag}",
                "-o",
                str(bin_path),
                str(sub / "ctfe.rs"),
            ],
            env=env,
        )
        rrc, rout, _ = run_cmd([str(bin_path)], env=env) if rc == 0 else (-1, "", "")
        out[f"contract_{flag}"] = {
            "compile_rc": rc,
            "runtime_rc": rrc,
            "stdout": rout.strip(),
        }
    return out


def probe_6_miri(tmp: pathlib.Path, env: dict[str, str]) -> dict[str, Any]:
    _, sysroot_out, _ = run_cmd(["rustc", "--print", "sysroot"], env=env)
    sysroot = pathlib.Path(sysroot_out.strip())
    miri_bin = sysroot / "bin" / "miri"
    core_src = sysroot / "lib/rustlib/src/rust/library/core/src/lib.rs"
    if not miri_bin.exists() or not core_src.exists():
        return {"available": False}

    sub = tmp / "p6_miri"
    core_dir = sub / "miri_sysroot/lib/rustlib/x86_64-unknown-linux-gnu/lib"
    core_dir.mkdir(parents=True)
    roots = [str(tmp), str(sysroot)]

    cb = sub / "cb.rs"
    cb.write_text(
        "#![feature(no_core, compiler_builtins)]\n#![no_core]\n#![compiler_builtins]\n"
    )
    rc_cb, _, _ = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-name=compiler_builtins",
            "--crate-type=rlib",
            "--cfg=miri",
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--out-dir",
            str(core_dir),
            str(cb),
        ],
        env=env,
    )
    rc_core, _, _ = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "--crate-name=core",
            "--crate-type=rlib",
            "--cfg=miri",
            "-Zalways-encode-mir",
            "-Copt-level=0",
            "-Cdebug-assertions=on",
            "-Cpanic=abort",
            "-Zforce-unstable-if-unmarked",
            "--out-dir",
            str(core_dir),
            str(core_src),
        ],
        env=env,
    )
    if rc_cb != 0 or rc_core != 0:
        return {"available": True, "core_build_rc": rc_core, "cb_build_rc": rc_cb}

    nostd_src = """#![no_std]
#![no_main]
#![feature(contracts, core_intrinsics)]
use core::contracts::{requires, ensures};

#[requires(x < 100)]
#[ensures(move |ret| *ret == x + 1)]
pub fn inc_bounded(x: u32) -> u32 {
    x + 1
}

#[ensures(|ret| *ret > 0)]
pub fn ensures_only(flag: bool) -> u32 {
    if flag {
        return 0;
    }
    42
}

#[requires(x > 0)]
pub const fn pos(x: u32) -> u32 {
    x
}

pub const BAD_CONST: u32 = pos(0);

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    core::intrinsics::abort()
}

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let _ = BAD_CONST;
    #[cfg(feature = "ensures_only_ok")]
    {
        let _ = ensures_only(false);
        return 0;
    }
    #[cfg(not(feature = "ensures_only_ok"))]
    {
        let r = inc_bounded(41);
        assert!(r == 42);
        #[cfg(feature = "violate_req")]
        {
            let _ = inc_bounded(200);
        }
        #[cfg(feature = "violate_ens")]
        {
            let _ = ensures_only(true);
        }
        0
    }
}
"""
    (sub / "nostd.rs").write_text(nostd_src)
    cases: dict[str, Any] = {"available": True, "core_build_rc": rc_core, "runs": {}}
    for name, extra in [
        ("default_ok", []),
        ("default_violate_req", ["--cfg", 'feature="violate_req"']),
        ("contract_no_violate_req", ["-Zcontract-checks=no", "--cfg", 'feature="violate_req"']),
        ("contract_no_violate_ens", ["-Zcontract-checks=no", "--cfg", 'feature="violate_ens"']),
        ("contract_yes_ok", ["-Zcontract-checks=yes"]),
        ("contract_yes_violate_req", ["-Zcontract-checks=yes", "--cfg", 'feature="violate_req"']),
        (
            "contract_yes_ensures_only_ok",
            ["-Zcontract-checks=yes", "--cfg", 'feature="ensures_only_ok"'],
        ),
    ]:
        rc, _, err = run_cmd(
            [
                str(miri_bin),
                "--edition=2024",
                "--sysroot",
                str(sub / "miri_sysroot"),
                "-Cpanic=abort",
                *extra,
                str(sub / "nostd.rs"),
            ],
            env=env,
        )
        key_lines = [
            scrub_text(l, roots)
            for l in err.splitlines()
            if l.startswith("error:") or "intrinsic_fallback_is_spec" in l
        ]
        cases["runs"][name] = {
            "rc": rc,
            "has_fallback_is_spec_error": "intrinsic_fallback_is_spec" in err,
            "error_lines": key_lines[:4],
        }
    return cases


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=pathlib.Path, default=None)
    args = parser.parse_args()

    env = resolve_rustc_env()
    _, rustc_vv, _ = run_cmd(["rustc", "-vV"], env=env)
    _, miri_v, _ = run_cmd(["cargo", "miri", "--version"], env=env)

    with tempfile.TemporaryDirectory() as tmp_str:
        tmp = pathlib.Path(tmp_str)
        report = {
            "rustc_version": rustc_vv.strip(),
            "miri_version": miri_v.strip(),
            "probe_1_modes": probe_1_modes(tmp, env),
            "probe_2_cross_crate": probe_2_cross_crate(tmp, env),
            "probe_3_capture_and_syntax": probe_3_capture_and_syntax(tmp, env),
            "probe_4_exit_paths": probe_4_exit_paths(tmp, env),
            "probe_5_ctfe_bypass": probe_5_ctfe_bypass(tmp, env),
            "probe_6_miri": probe_6_miri(tmp, env),
        }

    rendered = json.dumps(report, indent=2, sort_keys=False) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
