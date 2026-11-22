#!/usr/bin/env python3
"""Standalone probe of cross-compiler `v_verify != v_ship` semantic drift,
`.rlib` metadata version fencing (`E0514`), stdlib precondition tightening, and
bounded-file semantic equivalence classes across 9 `rustc` toolchains
(`1.78.0` through `1.102.0-nightly`).

Uses only Python 3.10+ standard library, installed `rustup` toolchains, and
optional `--with-git` shallow `git ls-tree` against `https://github.com/rust-lang/rust.git`
strictly inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

TOOLCHAINS = [
    ("1.78.0", "9b00956e56009bab2aa15d7bff10916599e3d6d6"),
    ("1.84.0", "9fc6b43126469e3858e2fe86cafb4f0fd5068869"),
    ("1.93.1", "01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf"),
    ("1.94.0", "4a4ef493e3a1488c6e321570238084b38948f6db"),
    ("1.96.0", "ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96"),
    ("1.99.0", "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4"),
    ("1.99.1", "58cf8f9c35b355199727627d07ae34a4e2846d67"),
    ("1.100.0", "0ef1bc386059596dada8fb65b50425aab2ea637a"),
    ("nightly-2026-11-20", "6905905bb7727fd0f9223f5fdc9ad4e62236d5a2"),
]

RUNTIME_PROBE_RS = r"""
use core::any::{type_name, TypeId};
use core::convert::Infallible;
use std::mem::{align_of, offset_of, size_of};
use std::ops::ControlFlow;
use std::ptr::NonNull;

#[allow(dead_code)]
struct ReprRustMixed { a: u8, b: u64, c: u16, d: u32, e: u8 }

#[repr(C)]
#[allow(dead_code)]
struct ReprCMixed { a: u8, b: u64, c: u16, d: u32, e: u8 }

trait Assoc { type Out; }
impl<T> Assoc for fn() -> T { type Out = T; }
type Never = <fn() -> ! as Assoc>::Out;

fn main() {
    println!("type_name_infallible={}", type_name::<Infallible>());
    println!("type_name_never={}", type_name::<Never>());
    println!("type_id_infallible_eq_never={}", TypeId::of::<Infallible>() == TypeId::of::<Never>());
    println!("repr_rust_size={}", size_of::<ReprRustMixed>());
    println!("repr_rust_align={}", align_of::<ReprRustMixed>());
    println!(
        "repr_rust_offsets={},{},{},{},{}",
        offset_of!(ReprRustMixed, a),
        offset_of!(ReprRustMixed, b),
        offset_of!(ReprRustMixed, c),
        offset_of!(ReprRustMixed, d),
        offset_of!(ReprRustMixed, e),
    );
    println!(
        "repr_c_offsets={},{},{},{},{}",
        offset_of!(ReprCMixed, a),
        offset_of!(ReprCMixed, b),
        offset_of!(ReprCMixed, c),
        offset_of!(ReprCMixed, d),
        offset_of!(ReprCMixed, e),
    );
    println!("opt_nonnull_size={}", size_of::<Option<NonNull<u8>>>());
    println!("cf_opt_infallible_size={}", size_of::<ControlFlow<Option<Infallible>, u32>>());
}
"""

SLICE_NULL_PRECONDITION_RS = r"""
fn main() {
    let p: *const u8 = core::hint::black_box(core::ptr::null());
    let s: &[u8] = unsafe { core::slice::from_raw_parts(p, 0) };
    println!("len={}", s.len());
}
"""

PME_OK_RS = r"""
pub fn dead_generic_pme<T>(run: bool) -> usize {
    if run {
        const { assert!(core::mem::size_of::<T>() <= 4); 1 }
    } else {
        0
    }
}
pub fn call_ok() -> usize { dead_generic_pme::<u32>(false) }
"""

PME_FAIL_RS = PME_OK_RS + "\npub fn call_fail() -> usize { dead_generic_pme::<u64>(false) }\n"

DIVERGING_FALLBACK_RS = r"""
trait DefaultUnit {
    fn make() -> Self;
}
impl DefaultUnit for () {
    fn make() -> Self {}
}
pub fn probe_fallback(flag: bool) {
    if flag {
        return;
    }
    let _x = if true {
        return
    } else {
        DefaultUnit::make()
    };
}
"""

BOUNDED_PATHS = [
    "compiler/rustc_middle/src/mir/syntax.rs",
    "compiler/rustc_const_eval/src/interpret",
    "compiler/rustc_abi/src",
    "library/core/src/convert/mod.rs",
]

# Pre-recorded upstream Git blob/tree SHA-1s for offline reproduction when `--no-git` is passed.
RECORDED_BOUNDED_GIT_OBJECTS = {
    "1.78.0": {
        "commit": "9b00956e56009bab2aa15d7bff10916599e3d6d6",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "0ab797134c0afddba04a14b36285743a3e90e8c1",
            "compiler/rustc_const_eval/src/interpret": "b89dea55402407336589dd4240dc90b66074f566",
            "compiler/rustc_abi/src": "8aa40558a14737ae62c47f83fe3611419cce4eca",
            "library/core/src/convert/mod.rs": "63fd23ea9a9d355db626069499be4be686d3579e",
        },
    },
    "1.84.0": {
        "commit": "9fc6b43126469e3858e2fe86cafb4f0fd5068869",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "fea940ea47c47e47fb5c1177c86af3ae213d5d49",
            "compiler/rustc_const_eval/src/interpret": "9142875ff42f0a9267e7a00daaee495f1114ab92",
            "compiler/rustc_abi/src": "38b974b1639a7ef4be076cda171fb94faeee8c17",
            "library/core/src/convert/mod.rs": "432e55e8c9a4cbb5f0d2dadae1e8601db9c4e37e",
        },
    },
    "1.93.1": {
        "commit": "01f6ddf7588f42ae2d7eb0a2f21d44e8e96674cf",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "204ad4815147b46360334e6f295a97e18ec8af15",
            "compiler/rustc_const_eval/src/interpret": "2f8efa331ceda8fa753e1aff2989b8e6330f7e53",
            "compiler/rustc_abi/src": "ccd705e69193ba714b428984632148850456f790",
            "library/core/src/convert/mod.rs": "89cda30c03036e26704e1f4b505805b571b42be9",
        },
    },
    "1.94.0": {
        "commit": "4a4ef493e3a1488c6e321570238084b38948f6db",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "6ec874fb15f7155c5ec1239f7cac548459200dc4",
            "compiler/rustc_const_eval/src/interpret": "1ca6125d306ee7ded7951b3187cf90d49b354826",
            "compiler/rustc_abi/src": "58eaf08ac2089e1bd551148ab56bb2da86913506",
            "library/core/src/convert/mod.rs": "ef4ab15f93c0b454bc4e2334a920b3923d19e7c6",
        },
    },
    "1.96.0": {
        "commit": "ac68faa20c58cbccd01ee7208bf3b6e93a7d7f96",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "455089f285d17c51ad48ef5f0bc357534b5f6915",
            "compiler/rustc_const_eval/src/interpret": "934d46763ba9c36d4e5424d54dd334772f00d1ec",
            "compiler/rustc_abi/src": "1890b534d54f908353a44fc3b7eb73bc3b3477d1",
            "library/core/src/convert/mod.rs": "ef4ab15f93c0b454bc4e2334a920b3923d19e7c6",
        },
    },
    "1.99.0": {
        "commit": "b940084d7eb6a299eb4bfeb8e34901bc051e7ac4",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "4e2d16625266cf505f00275f5c0ba52713e68be1",
            "compiler/rustc_const_eval/src/interpret": "4840404acb814fbcc0ce17e108fdfac8205aadad",
            "compiler/rustc_abi/src": "56b68c74138f0ac37e404a00fc33bd3678abd460",
            "library/core/src/convert/mod.rs": "912623b73050e7936a1fbadee6018e57466ba097",
        },
    },
    "1.99.1": {
        "commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "4e2d16625266cf505f00275f5c0ba52713e68be1",
            "compiler/rustc_const_eval/src/interpret": "4840404acb814fbcc0ce17e108fdfac8205aadad",
            "compiler/rustc_abi/src": "56b68c74138f0ac37e404a00fc33bd3678abd460",
            "library/core/src/convert/mod.rs": "912623b73050e7936a1fbadee6018e57466ba097",
        },
    },
    "1.100.0": {
        "commit": "0ef1bc386059596dada8fb65b50425aab2ea637a",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "6bb0190cd70b81fee71348e000e5d133b2f25d46",
            "compiler/rustc_const_eval/src/interpret": "7bfdd4df52e5477b04351729dd2947a99e725e29",
            "compiler/rustc_abi/src": "1f6c6df5f816885093f8db2267416ea4819ca1a0",
            "library/core/src/convert/mod.rs": "c86c70b5c4ca160ec2996b49a6b1b50877f04051",
        },
    },
    "nightly-2026-11-20": {
        "commit": "6905905bb7727fd0f9223f5fdc9ad4e62236d5a2",
        "objects": {
            "compiler/rustc_middle/src/mir/syntax.rs": "7db6a7390d539f100332d9f38a49be2c6c7d7348",
            "compiler/rustc_const_eval/src/interpret": "362696018bf8da2d791c3d39906a740a2b1e00b2",
            "compiler/rustc_abi/src": "bc69a55121b3fd60d46497a368702392fe91fe77",
            "library/core/src/convert/mod.rs": "c86c70b5c4ca160ec2996b49a6b1b50877f04051",
        },
    },
}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=None)
    parser.add_argument("--with-git", action="store_true")
    args = parser.parse_args()

    out_data: dict[str, object] = {
        "toolchains": {},
        "rlib_cross_link": [],
        "bounded_git_objects": {},
    }
    with tempfile.TemporaryDirectory() as tmp_s:
        tmp = Path(tmp_s)
        probe_rs = tmp / "probe.rs"
        probe_rs.write_text(RUNTIME_PROBE_RS, encoding="utf-8")
        slice_rs = tmp / "slice_null.rs"
        slice_rs.write_text(SLICE_NULL_PRECONDITION_RS, encoding="utf-8")
        pme_ok = tmp / "pme_ok.rs"
        pme_ok.write_text(PME_OK_RS, encoding="utf-8")
        pme_fail = tmp / "pme_fail.rs"
        pme_fail.write_text(PME_FAIL_RS, encoding="utf-8")
        div_rs = tmp / "div_fallback.rs"
        div_rs.write_text(DIVERGING_FALLBACK_RS, encoding="utf-8")

        rlib_src = tmp / "dep.rs"
        rlib_src.write_text("pub fn add_one(x: u32) -> u32 { x + 1 }\n", encoding="utf-8")
        consumer_src = tmp / "consumer.rs"
        consumer_src.write_text(
            "extern crate dep;\npub fn two() -> u32 { dep::add_one(1) }\n",
            encoding="utf-8",
        )
        rlib_paths: dict[str, Path] = {}

        for tc, sha in TOOLCHAINS:
            vv = subprocess.run(
                ["rustup", "run", tc, "rustc", "-vV"],
                capture_output=True,
                text=True,
                check=False,
            )
            if vv.returncode != 0:
                out_data["toolchains"][tc] = {"installed": False}
                continue
            b = tmp / f"bin_{tc.replace('.', '_')}"
            subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "-O", str(probe_rs), "-o", str(b)],
                check=True,
                capture_output=True,
            )
            rt = subprocess.run([str(b)], check=True, capture_output=True, text=True).stdout.strip().splitlines()
            rt_kv = dict(line.split("=", 1) for line in rt)

            sb = tmp / f"slice_{tc.replace('.', '_')}"
            subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "-C", "debug-assertions=yes", str(slice_rs), "-o", str(sb)],
                check=True,
                capture_output=True,
            )
            sproc = subprocess.run([str(sb)], check=False, capture_output=True, text=True)
            slice_aborted = sproc.returncode != 0
            slice_stderr_head = ""
            for sline in sproc.stderr.splitlines():
                if "unsafe precondition" in sline or "slice::from_raw_parts" in sline:
                    slice_stderr_head = sline.strip()
                    break

            rand_kv = None
            if tc.startswith("nightly"):
                rb = tmp / "bin_rand"
                subprocess.run(
                    [
                        "rustup", "run", tc, "rustc", "--edition=2021", "-O",
                        "-Zrandomize-layout", "-Zlayout-seed=7", str(probe_rs), "-o", str(rb),
                    ],
                    check=True,
                    capture_output=True,
                )
                rrt = subprocess.run([str(rb)], check=True, capture_output=True, text=True).stdout.strip().splitlines()
                rand_kv = dict(line.split("=", 1) for line in rrt)

            c_ok = subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "--crate-type=lib", str(pme_ok), "-o", str(tmp / "ok.rlib")],
                capture_output=True,
                text=True,
                check=False,
            )
            c_fl = subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "--crate-type=lib", str(pme_fail), "-o", str(tmp / "fl.rlib")],
                capture_output=True,
                text=True,
                check=False,
            )
            c_dv = subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "--crate-type=lib", str(div_rs), "-o", str(tmp / "dv.rlib")],
                capture_output=True,
                text=True,
                check=False,
            )

            rlib_p = tmp / f"libdep_{tc.replace('.', '_')}.rlib"
            rp = subprocess.run(
                ["rustup", "run", tc, "rustc", "--edition=2021", "--crate-type=rlib", str(rlib_src), "-o", str(rlib_p)],
                capture_output=True,
                text=True,
                check=False,
            )
            if rp.returncode == 0:
                rlib_paths[tc] = rlib_p

            out_data["toolchains"][tc] = {
                "commit": sha,
                "rustc_vV": vv.stdout.strip().splitlines(),
                "runtime": rt_kv,
                "runtime_randomized_seed7": rand_kv,
                "slice_from_raw_parts_null_zero_len_aborted_debug": slice_aborted,
                "slice_from_raw_parts_null_zero_len_diag": slice_stderr_head,
                "pme_u32_rc": c_ok.returncode,
                "pme_u64_dead_branch_rc": c_fl.returncode,
                "pme_u64_err_head": c_fl.stderr.splitlines()[0] if c_fl.stderr else "",
                "diverging_fallback_rc": c_dv.returncode,
                "diverging_fallback_diag_head": c_dv.stderr.splitlines()[0] if c_dv.stderr else "",
            }

        pairs = [("1.93.1", "1.94.0"), ("1.99.1", "1.100.0"), ("1.100.0", "nightly-2026-11-20")]
        for prod_tc, cons_tc in pairs:
            if prod_tc in rlib_paths and cons_tc in rlib_paths:
                cp = subprocess.run(
                    [
                        "rustup", "run", cons_tc, "rustc",
                        "--edition=2021", "--crate-type=rlib",
                        "--extern", f"dep={rlib_paths[prod_tc]}",
                        str(consumer_src), "-o", str(tmp / "libconsumer.rlib"),
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                out_data["rlib_cross_link"].append(
                    {
                        "producer": prod_tc,
                        "consumer": cons_tc,
                        "rc": cp.returncode,
                        "stderr_first_line": cp.stderr.splitlines()[0] if cp.stderr else "",
                    }
                )

        if args.with_git:
            rs = tmp / "rust"
            subprocess.run(["git", "init", str(rs)], check=True, capture_output=True)
            subprocess.run(
                ["git", "-C", str(rs), "remote", "add", "origin", "https://github.com/rust-lang/rust.git"],
                check=True,
                capture_output=True,
            )
            subprocess.run(
                ["git", "-C", str(rs), "fetch", "--filter=blob:none", "--depth=1", "origin", *[s for _, s in TOOLCHAINS]],
                check=True,
                capture_output=True,
            )
            for tc, sha in TOOLCHAINS:
                objs: dict[str, str] = {}
                for p in BOUNDED_PATHS:
                    ls = subprocess.run(
                        ["git", "-C", str(rs), "ls-tree", sha, p],
                        check=True,
                        capture_output=True,
                        text=True,
                    ).stdout.strip()
                    objs[p] = ls.split()[2] if ls else "MISSING"
                out_data["bounded_git_objects"][tc] = {"commit": sha, "objects": objs}
        else:
            out_data["bounded_git_objects"] = RECORDED_BOUNDED_GIT_OBJECTS

    rendered = json.dumps(out_data, indent=2) + "\n"
    if args.out is not None:
        args.out.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
