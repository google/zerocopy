#!/usr/bin/env python3
"""Reproducible empirical probe for rustc pattern_types, nested Option niche
stacking, LLVM range/nonnull dead-branch elimination, -Z ub-checks vs. Miri
validity cliff, Or-pattern layout restrictions, and rustc_transmute rejection.

Uses only the Python 3.10+ standard library and invokes the active `rustc` and
`cargo miri` toolchains inside a temporary directory cleaned up on exit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

PROBE_RS = r"""#![allow(internal_features)]
#![feature(pattern_types, pattern_type_macro)]

use core::mem::{size_of, transmute};
use core::num::NonZero;
use core::ptr::NonNull;
use std::pat::pattern_type;

type Pat1To10 = pattern_type!(u8 is 1..=10);
type PatPosI32 = pattern_type!(i32 is 1..);
type PatNonNull = pattern_type!(*const u8 is !null);
type Pat254 = pattern_type!(u8 is 1..=254);
type PatSignedNonZero = pattern_type!(i8 is ..=-1 | 1..);

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn take_pat_u8(x: Pat1To10) -> u8 {
    let v: u8 = unsafe { transmute(x) };
    if v == 0 || v > 10 {
        panic!("impossible out-of-range Pat1To10");
    }
    v
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ret_pat_u8(x: u8) -> Pat1To10 {
    assert!((1..=10).contains(&x), "ret_pat_u8 precondition violated");
    unsafe { transmute(x) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn take_pat_pos_i32(x: PatPosI32) -> i32 {
    let v: i32 = unsafe { transmute(x) };
    if v <= 0 {
        panic!("impossible");
    }
    v
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn take_pat_nonnull(p: PatNonNull) -> usize {
    let raw: *const u8 = unsafe { transmute(p) };
    if raw.is_null() {
        panic!("impossible null");
    }
    raw as usize
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "sizes".to_string());
    match mode.as_str() {
        "sizes" => {
            println!(
                "SIZES Pat1To10={} Opt={} OptOpt={} Opt3={} PatPosI32={} OptPosI32={} PatNonNull={} OptNonNull={} OptNZ={} Opt2NZ={} OptNN={} Opt2NN={} OptBox={} Opt2Box={} PatSignedNZ={} OptSignedNZ={} Opt2SignedNZ={} Pat254={} Opt254={} Opt2_254={} Opt3_254={}",
                size_of::<Pat1To10>(),
                size_of::<Option<Pat1To10>>(),
                size_of::<Option<Option<Pat1To10>>>(),
                size_of::<Option<Option<Option<Pat1To10>>>>(),
                size_of::<PatPosI32>(),
                size_of::<Option<PatPosI32>>(),
                size_of::<PatNonNull>(),
                size_of::<Option<PatNonNull>>(),
                size_of::<Option<NonZero<u8>>>(),
                size_of::<Option<Option<NonZero<u8>>>>(),
                size_of::<Option<NonNull<u8>>>(),
                size_of::<Option<Option<NonNull<u8>>>>(),
                size_of::<Option<Box<u8>>>(),
                size_of::<Option<Option<Box<u8>>>>(),
                size_of::<PatSignedNonZero>(),
                size_of::<Option<PatSignedNonZero>>(),
                size_of::<Option<Option<PatSignedNonZero>>>(),
                size_of::<Pat254>(),
                size_of::<Option<Pat254>>(),
                size_of::<Option<Option<Pat254>>>(),
                size_of::<Option<Option<Option<Pat254>>>>(),
            );
            let n1: u8 = unsafe { transmute::<Option<Pat1To10>, u8>(None) };
            let n2: u8 = unsafe { transmute::<Option<Option<Pat1To10>>, u8>(None) };
            let n2_inner: u8 = unsafe { transmute::<Option<Option<Pat1To10>>, u8>(Some(None)) };
            let n3: u8 = unsafe { transmute::<Option<Option<Option<Pat1To10>>>, u8>(None) };
            let p254_n1: u8 = unsafe { transmute::<Option<Pat254>, u8>(None) };
            let p254_n2: u8 = unsafe { transmute::<Option<Option<Pat254>>, u8>(None) };
            let snz_none: u8 = unsafe { transmute::<Option<PatSignedNonZero>, u8>(None) };
            println!(
                "NICHE_BYTES OptPat1To10_None={} Opt2_None={} Opt2_SomeNone={} Opt3_None={} OptPat254_None={} Opt2Pat254_None={} OptSignedNZ_None={}",
                n1, n2, n2_inner, n3, p254_n1, p254_n2, snz_none
            );
            let ok = take_pat_u8(ret_pat_u8(7));
            let pos = take_pat_pos_i32(unsafe { transmute::<i32, PatPosI32>(42) });
            let x: u8 = 9;
            let nn = take_pat_nonnull(unsafe { transmute::<*const u8, PatNonNull>(&x as *const u8) });
            assert_eq!(ok, 7);
            assert_eq!(pos, 42);
            assert_ne!(nn, 0);
        }
        "bad_pat_u8_11" => {
            let bad: Pat1To10 = unsafe { transmute::<u8, Pat1To10>(std::hint::black_box(11u8)) };
            let back: u8 = unsafe { transmute::<Pat1To10, u8>(bad) };
            println!("BAD_PAT_U8={}", back);
        }
        "bad_pat_u8_11_call_opt" => {
            let bad: Pat1To10 = unsafe { transmute::<u8, Pat1To10>(std::hint::black_box(11u8)) };
            let v = take_pat_u8(bad);
            println!("MISCOMPILED_TAKE_PAT_U8={}", v);
        }
        "bad_pat_nonnull" => {
            let bad: PatNonNull =
                unsafe { transmute::<*const u8, PatNonNull>(std::hint::black_box(core::ptr::null())) };
            let raw: *const u8 = unsafe { transmute::<PatNonNull, *const u8>(bad) };
            println!("BAD_PAT_NN={:#x}", raw as usize);
        }
        "bad_pat_nonnull_call_opt" => {
            let bad: PatNonNull =
                unsafe { transmute::<*const u8, PatNonNull>(std::hint::black_box(core::ptr::null())) };
            let addr = take_pat_nonnull(bad);
            println!("MISCOMPILED_TAKE_PAT_NN={:#x}", addr);
        }
        "bad_nonzero_transmute" => {
            let bad: NonZero<u8> =
                unsafe { transmute::<u8, NonZero<u8>>(std::hint::black_box(0u8)) };
            println!("BAD_NZ_TX={}", bad.get());
        }
        "bad_nonzero_new_unchecked" => {
            let bad: NonZero<u8> = unsafe { NonZero::<u8>::new_unchecked(std::hint::black_box(0u8)) };
            println!("BAD_NZ_NU={}", bad.get());
        }
        "bad_opt_pat_enum_transmute" => {
            let bad: Option<Pat1To10> =
                unsafe { transmute::<u8, Option<Pat1To10>>(std::hint::black_box(99u8)) };
            println!("BAD_OPT_PAT_IS_SOME={}", bad.is_some());
        }
        other => panic!("unknown mode: {other}"),
    }
}
"""

EXTRA_SNIPPETS: dict[str, str] = {
    "pat_or_wrapping_range_unsigned": r"""#![feature(pattern_types, pattern_type_macro)]
use std::pat::pattern_type;
pub type WrapU8 = pattern_type!(u8 is 250..=255 | 0..=5);
pub const OPT_SIZE: usize = core::mem::size_of::<Option<WrapU8>>();
""",
    "pat_or_wrapping_range_signed": r"""#![feature(pattern_types, pattern_type_macro)]
use std::pat::pattern_type;
pub type NonZeroI8Pat = pattern_type!(i8 is ..=-1 | 1..);
pub const OPT_SIZE: usize = core::mem::size_of::<Option<NonZeroI8Pat>>();
""",
    "transmute_from_pat_to_u8": r"""#![feature(pattern_types, pattern_type_macro, transmutability)]
use core::mem::{Assume, TransmuteFrom};
use std::pat::pattern_type;
type Pat1To10 = pattern_type!(u8 is 1..=10);
pub fn check<Src, Dst>() where Dst: TransmuteFrom<Src, { Assume::NOTHING }> {}
pub fn test() { check::<Pat1To10, u8>(); }
""",
    "transmute_from_u8_to_pat_validity": r"""#![feature(pattern_types, pattern_type_macro, transmutability)]
use core::mem::{Assume, TransmuteFrom};
use std::pat::pattern_type;
type Pat1To10 = pattern_type!(u8 is 1..=10);
pub fn check<Src, Dst>() where Dst: TransmuteFrom<Src, { Assume::NOTHING }> {}
pub fn test() { check::<u8, Pat1To10>(); }
""",
    "transmute_from_nonzero_u8_to_u8": r"""#![feature(transmutability)]
use core::mem::{Assume, TransmuteFrom};
use core::num::NonZero;
pub fn check<Src, Dst>() where Dst: TransmuteFrom<Src, { Assume::NOTHING }> {}
pub fn test() { check::<NonZero<u8>, u8>(); }
""",
}

RUNTIME_MODES = [
    "sizes",
    "bad_pat_u8_11",
    "bad_pat_u8_11_call_opt",
    "bad_pat_nonnull",
    "bad_pat_nonnull_call_opt",
    "bad_nonzero_transmute",
    "bad_nonzero_new_unchecked",
    "bad_opt_pat_enum_transmute",
]


def scrub(text: str, tmp_dir: str) -> str:
    text = text.replace(tmp_dir, "<TMP>")
    text = text.replace(str(Path.home()), "<HOME>")
    text = re.sub(r"\(\d+\) panicked at", "(<TID>) panicked at", text)
    text = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "<TMP>", text)
    return text


def extract_ir_fn(ir_text: str, fn_name: str) -> str | None:
    pattern = re.compile(
        rf"(define [^\n]*@{re.escape(fn_name)}\([^\n]*\{{.*?\n\}})",
        re.DOTALL,
    )
    m = pattern.search(ir_text)
    return m.group(1) if m else None


def run_build_profile(tmp: Path, name: str, flags: list[str]) -> dict[str, Any]:
    prof_dir = tmp / name
    prof_dir.mkdir(parents=True, exist_ok=True)
    src = tmp / "pat_probe.rs"
    bin_path = prof_dir / "pat_probe"
    cmd = [
        "rustc",
        "--edition=2024",
        *flags,
        "--emit=link,llvm-ir,mir",
        "-o",
        str(bin_path),
        str(src),
    ]
    comp = subprocess.run(cmd, capture_output=True, text=True)
    result: dict[str, Any] = {
        "flags": flags,
        "compile_rc": comp.returncode,
        "compile_stderr": scrub(comp.stderr, str(tmp)),
        "ir_fns": {},
        "mir_has_pat_syntax": {},
        "runtime": {},
    }
    if comp.returncode != 0:
        return result

    ll_files = list(prof_dir.glob("*.ll"))
    mir_files = list(prof_dir.glob("*.mir"))
    if ll_files:
        ir_text = ll_files[0].read_text(encoding="utf-8", errors="replace")
        for fn_name in ("take_pat_u8", "ret_pat_u8", "take_pat_pos_i32", "take_pat_nonnull"):
            result["ir_fns"][fn_name] = extract_ir_fn(ir_text, fn_name)
    if mir_files:
        mir_text = mir_files[0].read_text(encoding="utf-8", errors="replace")
        result["mir_has_pat_syntax"] = {
            "has_is_1_10": "is 1..=10" in mir_text,
            "has_is_not_null": "is !null" in mir_text,
        }

    exe_candidates = [p for p in prof_dir.iterdir() if p.is_file() and os.access(p, os.X_OK)]
    exe = bin_path if bin_path.exists() else (exe_candidates[0] if exe_candidates else bin_path)
    for mode in RUNTIME_MODES:
        proc = subprocess.run([str(exe), mode], capture_output=True, text=True, timeout=30)
        stderr_lines = [scrub(line, str(tmp)) for line in proc.stderr.splitlines()[:8]]
        result["runtime"][mode] = {
            "rc": proc.returncode,
            "stdout": scrub(proc.stdout.strip(), str(tmp)),
            "stderr_head": stderr_lines,
        }
    return result


def run_miri_oracle(tmp: Path) -> dict[str, Any]:
    proj = tmp / "miri_proj"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        '[package]\nname = "pat_miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(PROBE_RS, encoding="utf-8")

    out: dict[str, Any] = {}
    for mode in RUNTIME_MODES:
        proc = subprocess.run(
            ["cargo", "miri", "run", "--quiet", "--", mode],
            cwd=str(proj),
            capture_output=True,
            text=True,
            timeout=180,
        )
        ub_lines = [
            scrub(line.strip(), str(tmp))
            for line in proc.stderr.splitlines()
            if (
                "Undefined Behavior" in line
                or "encountered" in line
                or "panicked at" in line
                or "this indicates a bug" in line
            )
        ][:6]
        out[mode] = {
            "rc": proc.returncode,
            "stdout": scrub(proc.stdout.strip(), str(tmp)),
            "ub_lines": ub_lines,
        }
    return out


def run_extra_checks(tmp: Path) -> dict[str, Any]:
    out: dict[str, Any] = {}
    extra_dir = tmp / "extra"
    extra_dir.mkdir(parents=True, exist_ok=True)
    for name, code in EXTRA_SNIPPETS.items():
        rs = extra_dir / f"{name}.rs"
        rs.write_text(code, encoding="utf-8")
        proc = subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "--emit=metadata",
                "-o",
                str(extra_dir / f"{name}.rmeta"),
                str(rs),
            ],
            capture_output=True,
            text=True,
            timeout=30,
        )
        err_lines = [
            scrub(line.strip(), str(tmp))
            for line in proc.stderr.splitlines()
            if (
                line.startswith("error")
                or "is not yet supported" in line
                or "only signed integer" in line
                or "For more information" in line
            )
        ][:8]
        out[name] = {"ok": proc.returncode == 0, "err_head": err_lines}
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Optional JSON output path")
    parser.add_argument("--skip-miri", action="store_true", help="Skip cargo miri runs")
    args = parser.parse_args()

    rustc_v = subprocess.run(["rustc", "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    miri_v_proc = subprocess.run(["cargo", "miri", "--version"], capture_output=True, text=True)
    miri_v = miri_v_proc.stdout.strip() if miri_v_proc.returncode == 0 else "unavailable"

    with tempfile.TemporaryDirectory(prefix="pat_probe_") as tmp_str:
        tmp = Path(tmp_str)
        (tmp / "pat_probe.rs").write_text(PROBE_RS, encoding="utf-8")

        report: dict[str, Any] = {
            "rustc_version": rustc_v,
            "miri_version": miri_v,
            "opt2_ub_no": run_build_profile(tmp, "opt2_ub_no", ["-C", "opt-level=2", "-Z", "ub-checks=no"]),
            "opt0_ub_yes": run_build_profile(tmp, "opt0_ub_yes", ["-C", "opt-level=0", "-Z", "ub-checks=yes"]),
            "extra_pat_checks": run_extra_checks(tmp),
        }
        if not args.skip_miri and miri_v_proc.returncode == 0:
            report["miri_oracle"] = run_miri_oracle(tmp)

    payload = json.dumps(report, indent=2) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
