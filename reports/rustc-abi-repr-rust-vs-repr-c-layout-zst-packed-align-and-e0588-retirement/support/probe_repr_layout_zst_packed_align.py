#!/usr/bin/env python3
"""Live rustc probe suite for repr(Rust) vs repr(C) struct layout, -Zrandomize-layout,
ZST alignment propagation, #[repr(packed/align/transparent)] diagnostics, E0588 vs
aligned_fields_in_packed divergence, and zerocopy Unalign/ReadOnly layout invariants.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def _rustc_env() -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", "").split(":"):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    return env


def _sanitize(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir + "/", "<tmp>/").replace(tmpdir, "<tmp>").strip()


def _parse_rustc_version_verbose(raw: str) -> dict[str, str]:
    info: dict[str, str] = {"raw": raw.strip()}
    lines = [line.strip() for line in raw.strip().splitlines() if line.strip()]
    if lines:
        info["headline"] = lines[0]
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip().replace("-", "_").replace(" ", "_").lower()] = v.strip()
    return info


def _compile_and_maybe_run(
    src: str,
    *,
    edition: str = "2024",
    extra_args: list[str] | None = None,
    crate_type: str = "bin",
    run_binary: bool = True,
    env: dict[str, str],
) -> dict[str, Any]:
    extra = list(extra_args or [])
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        rs_path = tmp / "probe.rs"
        rs_path.write_text(src, encoding="utf-8")
        out_path = tmp / ("probe_bin" if crate_type == "bin" else "libprobe.rmeta")
        cmd = ["rustc", "--edition", edition, "--crate-type", crate_type]
        if crate_type != "bin":
            cmd.append("--emit=metadata")
        cmd.extend(extra)
        cmd.extend(["-o", str(out_path), str(rs_path)])

        comp = subprocess.run(cmd, capture_output=True, text=True, env=env, check=False)
        record: dict[str, Any] = {
            "edition": edition,
            "crate_type": crate_type,
            "extra_args": extra,
            "compile_returncode": comp.returncode,
            "compile_stdout": _sanitize(comp.stdout, tmpdir),
            "compile_stderr": _sanitize(comp.stderr, tmpdir),
        }
        if comp.returncode == 0 and run_binary and crate_type == "bin":
            run = subprocess.run([str(out_path)], capture_output=True, text=True, env=env, check=False)
            record["run_returncode"] = run.returncode
            record["run_stdout"] = _sanitize(run.stdout, tmpdir)
            record["run_stderr"] = _sanitize(run.stderr, tmpdir)
        return record


def _filter_user_print_type_sizes(stdout: str, names: tuple[str, ...]) -> list[str]:
    kept: list[str] = []
    capture = False
    for line in stdout.splitlines():
        if line.startswith("print-type-size type: `"):
            capture = any(f"`{name}`" in line or f"`{name}<" in line for name in names)
        if capture:
            kept.append(line)
    return kept


def run_experiment_a(env: dict[str, str]) -> dict[str, Any]:
    src = """#![allow(dead_code)]
use std::mem::{align_of, offset_of, size_of};

pub struct SDefault {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(C)]
pub struct SC {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(packed)]
pub struct SPacked {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(packed(2))]
pub struct SPacked2 {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(C, align(16))]
pub struct SCAlign16 {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(C, packed)]
pub struct SCPacked {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

#[repr(C, packed(2))]
pub struct SCPacked2 {
    pub a: u8,
    pub b: u64,
    pub c: u8,
    pub d: u16,
}

pub struct SingleRust {
    pub only: u32,
}

fn main() {
    println!(
        "repr(Rust): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SDefault>(), align_of::<SDefault>(),
        offset_of!(SDefault, a), offset_of!(SDefault, b),
        offset_of!(SDefault, c), offset_of!(SDefault, d),
    );
    println!(
        "repr(C): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SC>(), align_of::<SC>(),
        offset_of!(SC, a), offset_of!(SC, b),
        offset_of!(SC, c), offset_of!(SC, d),
    );
    println!(
        "repr(packed): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SPacked>(), align_of::<SPacked>(),
        offset_of!(SPacked, a), offset_of!(SPacked, b),
        offset_of!(SPacked, c), offset_of!(SPacked, d),
    );
    println!(
        "repr(packed(2)): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SPacked2>(), align_of::<SPacked2>(),
        offset_of!(SPacked2, a), offset_of!(SPacked2, b),
        offset_of!(SPacked2, c), offset_of!(SPacked2, d),
    );
    println!(
        "repr(C,align(16)): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SCAlign16>(), align_of::<SCAlign16>(),
        offset_of!(SCAlign16, a), offset_of!(SCAlign16, b),
        offset_of!(SCAlign16, c), offset_of!(SCAlign16, d),
    );
    println!(
        "repr(C,packed): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SCPacked>(), align_of::<SCPacked>(),
        offset_of!(SCPacked, a), offset_of!(SCPacked, b),
        offset_of!(SCPacked, c), offset_of!(SCPacked, d),
    );
    println!(
        "repr(C,packed(2)): size={} align={} offsets=(a:{},b:{},c:{},d:{})",
        size_of::<SCPacked2>(), align_of::<SCPacked2>(),
        offset_of!(SCPacked2, a), offset_of!(SCPacked2, b),
        offset_of!(SCPacked2, c), offset_of!(SCPacked2, d),
    );
    println!(
        "tuple: size={} align={} offsets=(0:{},1:{},2:{},3:{})",
        size_of::<(u8, u64, u8, u16)>(), align_of::<(u8, u64, u8, u16)>(),
        offset_of!((u8, u64, u8, u16), 0), offset_of!((u8, u64, u8, u16), 1),
        offset_of!((u8, u64, u8, u16), 2), offset_of!((u8, u64, u8, u16), 3),
    );
    println!(
        "SingleRust: size={} align={} offset=(only:{})",
        size_of::<SingleRust>(), align_of::<SingleRust>(),
        offset_of!(SingleRust, only),
    );
}
"""
    user_types = ("SDefault", "SC", "SPacked", "SPacked2", "SCAlign16", "SCPacked", "SCPacked2", "SingleRust")
    configs = {
        "default": ["-Zprint-type-sizes"],
        "randomize_layout_seed_1": ["-Zrandomize-layout", "-Zlayout-seed=1", "-Zprint-type-sizes"],
        "randomize_layout_seed_42": ["-Zrandomize-layout", "-Zlayout-seed=42", "-Zprint-type-sizes"],
        "randomize_layout_seed_99": ["-Zrandomize-layout", "-Zlayout-seed=99", "-Zprint-type-sizes"],
    }
    out: dict[str, Any] = {}
    for key, args in configs.items():
        res = _compile_and_maybe_run(src, extra_args=args, env=env)
        res["user_print_type_sizes"] = _filter_user_print_type_sizes(res["compile_stdout"], user_types)
        out[key] = res
    return out


def run_experiment_b(env: dict[str, str]) -> dict[str, Any]:
    src = """#![allow(dead_code)]
use std::marker::PhantomData;
use std::mem::{align_of, offset_of, size_of};

pub struct Align16Zst(pub [u128; 0]);

#[repr(align(16))]
pub struct Align16ZstAttr;

pub struct OneZstPhantom(pub PhantomData<u128>);

#[repr(C)]
pub struct ReprCZstMid {
    pub a: u8,
    pub z: Align16Zst,
    pub b: u8,
}

#[repr(C)]
pub struct ReprCZstEnd {
    pub a: u8,
    pub b: u8,
    pub z: Align16Zst,
}

pub struct ReprRustZst {
    pub a: u8,
    pub z: Align16Zst,
    pub b: u8,
}

pub struct ReprRustTwoZsts {
    pub a: u8,
    pub z1: Align16Zst,
    pub b: u8,
    pub z2: Align16Zst,
}

pub struct ReprRustMixedZsts {
    pub a: u8,
    pub z1: Align16Zst,
    pub b: u8,
    pub z2: (),
}

pub struct PureZst {
    pub z1: Align16Zst,
    pub z2: Align16Zst,
}

pub struct Pure1Zst {
    pub u: (),
    pub p: PhantomData<u64>,
}

fn main() {
    println!("Align16Zst: size={} align={}", size_of::<Align16Zst>(), align_of::<Align16Zst>());
    println!("Align16ZstAttr: size={} align={}", size_of::<Align16ZstAttr>(), align_of::<Align16ZstAttr>());
    println!("OneZstPhantom: size={} align={}", size_of::<OneZstPhantom>(), align_of::<OneZstPhantom>());
    println!(
        "ReprCZstMid: size={} align={} offsets=(a:{},z:{},b:{})",
        size_of::<ReprCZstMid>(), align_of::<ReprCZstMid>(),
        offset_of!(ReprCZstMid, a), offset_of!(ReprCZstMid, z), offset_of!(ReprCZstMid, b),
    );
    println!(
        "ReprCZstEnd: size={} align={} offsets=(a:{},b:{},z:{})",
        size_of::<ReprCZstEnd>(), align_of::<ReprCZstEnd>(),
        offset_of!(ReprCZstEnd, a), offset_of!(ReprCZstEnd, b), offset_of!(ReprCZstEnd, z),
    );
    println!(
        "ReprRustZst: size={} align={} offsets=(a:{},z:{},b:{})",
        size_of::<ReprRustZst>(), align_of::<ReprRustZst>(),
        offset_of!(ReprRustZst, a), offset_of!(ReprRustZst, z), offset_of!(ReprRustZst, b),
    );
    println!(
        "ReprRustTwoZsts: size={} align={} offsets=(a:{},z1:{},b:{},z2:{})",
        size_of::<ReprRustTwoZsts>(), align_of::<ReprRustTwoZsts>(),
        offset_of!(ReprRustTwoZsts, a), offset_of!(ReprRustTwoZsts, z1),
        offset_of!(ReprRustTwoZsts, b), offset_of!(ReprRustTwoZsts, z2),
    );
    println!(
        "ReprRustMixedZsts: size={} align={} offsets=(a:{},z1:{},b:{},z2:{})",
        size_of::<ReprRustMixedZsts>(), align_of::<ReprRustMixedZsts>(),
        offset_of!(ReprRustMixedZsts, a), offset_of!(ReprRustMixedZsts, z1),
        offset_of!(ReprRustMixedZsts, b), offset_of!(ReprRustMixedZsts, z2),
    );
    println!(
        "PureZst: size={} align={} offsets=(z1:{},z2:{})",
        size_of::<PureZst>(), align_of::<PureZst>(),
        offset_of!(PureZst, z1), offset_of!(PureZst, z2),
    );
    println!(
        "Pure1Zst: size={} align={} offsets=(u:{},p:{})",
        size_of::<Pure1Zst>(), align_of::<Pure1Zst>(),
        offset_of!(Pure1Zst, u), offset_of!(Pure1Zst, p),
    );
}
"""
    user_types = (
        "Align16Zst", "Align16ZstAttr", "OneZstPhantom",
        "ReprCZstMid", "ReprCZstEnd", "ReprRustZst", "ReprRustTwoZsts", "ReprRustMixedZsts", "PureZst", "Pure1Zst",
    )
    res = _compile_and_maybe_run(src, extra_args=["-Zprint-type-sizes"], env=env)
    res["user_print_type_sizes"] = _filter_user_print_type_sizes(res["compile_stdout"], user_types)
    return res


def run_experiment_c(env: dict[str, str]) -> dict[str, Any]:
    explain = subprocess.run(["rustc", "--explain", "E0588"], capture_output=True, text=True, env=env, check=False)
    cases: dict[str, tuple[str, str]] = {
        "packed_and_align_e0587": (
            "lib",
            """#[repr(packed, align(8))]
pub struct Bad { pub x: u32 }
""",
        ),
        "packed_conflict_e0634": (
            "lib",
            """#[repr(packed(2), packed(4))]
pub struct Bad { pub x: u32 }
""",
        ),
        "transparent_two_non_zst_e0690": (
            "lib",
            """#[repr(transparent)]
pub struct Bad(pub u32, pub u8);
""",
        ),
        "transparent_with_non_1_aligned_zst_and_u8_e0690": (
            "lib",
            """#[repr(transparent)]
pub struct Bad(pub u8, pub [u32; 0]);
""",
        ),
        "transparent_with_repr_c_zst_and_u8_e0690": (
            "lib",
            """#[repr(C)]
pub struct CZst;
#[repr(transparent)]
pub struct Bad(pub u8, pub CZst);
""",
        ),
        "transparent_with_single_non_1_aligned_zst_only": (
            "bin",
            """#[repr(transparent)]
pub struct SingleNon1Zst(pub [u32; 0]);
fn main() {
    println!("SingleNon1Zst: size={} align={}", std::mem::size_of::<SingleNon1Zst>(), std::mem::align_of::<SingleNon1Zst>());
}
""",
        ),
        "transparent_with_other_repr_e0692": (
            "lib",
            """#[repr(transparent, C)]
pub struct Bad(pub u32);
""",
        ),
        "packed_containing_align_field_rust_outer": (
            "bin",
            """#[repr(align(8))]
pub struct Aligned8(pub u8);
#[repr(packed)]
pub struct Bad(pub Aligned8);
fn main() {
    println!("Bad: size={} align={}", std::mem::size_of::<Bad>(), std::mem::align_of::<Bad>());
}
""",
        ),
        "packed_containing_align_field_c_both": (
            "bin",
            """#[repr(C, align(8))]
pub struct CAligned8(pub u8);
#[repr(C, packed)]
pub struct CBad(pub CAligned8);
fn main() {
    println!("CBad: size={} align={}", std::mem::size_of::<CBad>(), std::mem::align_of::<CBad>());
}
""",
        ),
        "packed_containing_align_field_c_both_allow_lint": (
            "bin",
            """#[repr(C, align(8))]
pub struct CAligned8(pub u8);
#[allow(aligned_fields_in_packed)]
#[repr(C, packed)]
pub struct CBad(pub CAligned8);
fn main() {
    println!("CBadAllowed: size={} align={}", std::mem::size_of::<CBad>(), std::mem::align_of::<CBad>());
}
""",
        ),
        "packed_containing_align_field_generic_bypass": (
            "bin",
            """#[repr(align(8))]
pub struct Aligned8(pub u8);
#[repr(C, packed)]
pub struct GenericPacked<T>(pub T);
fn main() {
    println!("GenericPacked<Aligned8>: size={} align={}", std::mem::size_of::<GenericPacked<Aligned8>>(), std::mem::align_of::<GenericPacked<Aligned8>>());
}
""",
        ),
    }

    out: dict[str, Any] = {
        "explain_e0588_returncode": explain.returncode,
        "explain_e0588_head": explain.stdout.splitlines()[:12],
        "e0588_retired_in_explain": "no longer emitted" in explain.stdout,
    }
    for name, (ctype, src) in cases.items():
        out[name] = _compile_and_maybe_run(
            src,
            crate_type=ctype,
            run_binary=(ctype == "bin"),
            env=env,
        )
    return out


def run_experiment_d(env: dict[str, str]) -> dict[str, Any]:
    src = """#![allow(dead_code)]
use std::mem::{align_of, offset_of, size_of};

#[repr(C, packed)]
pub struct ZcUnalign<T>(pub T);

#[repr(C)]
pub struct ZcPacketHeader {
    pub tag: u8,
    pub val: ZcUnalign<u64>,
    pub tail: u8,
}

#[repr(transparent)]
pub struct ZcReadOnly<T: ?Sized> {
    pub inner: T,
}

pub struct ZcReadOnlyTuple(pub u8, pub u64);

#[repr(align(8))]
pub struct Aligned8(pub u8);

fn main() {
    println!("ZcUnalign<u64>: size={} align={}", size_of::<ZcUnalign<u64>>(), align_of::<ZcUnalign<u64>>());
    println!(
        "ZcPacketHeader: size={} align={} offsets=(tag:{},val:{},tail:{})",
        size_of::<ZcPacketHeader>(), align_of::<ZcPacketHeader>(),
        offset_of!(ZcPacketHeader, tag), offset_of!(ZcPacketHeader, val), offset_of!(ZcPacketHeader, tail),
    );
    println!(
        "ZcReadOnly<(u8, u64)> vs (u8, u64): ro=({},{}) inner=({},{})",
        size_of::<ZcReadOnly<(u8, u64)>>(), align_of::<ZcReadOnly<(u8, u64)>>(),
        size_of::<(u8, u64)>(), align_of::<(u8, u64)>(),
    );
    println!(
        "ZcReadOnly<ZcReadOnlyTuple>: size={} align={}",
        size_of::<ZcReadOnly<ZcReadOnlyTuple>>(), align_of::<ZcReadOnly<ZcReadOnlyTuple>>(),
    );
    println!(
        "Aligned8=({},{}) vs Generic ZcUnalign<Aligned8>=({},{})",
        size_of::<Aligned8>(), align_of::<Aligned8>(),
        size_of::<ZcUnalign<Aligned8>>(), align_of::<ZcUnalign<Aligned8>>(),
    );
}
"""
    user_types = ("ZcUnalign", "ZcPacketHeader", "ZcReadOnly", "ZcReadOnlyTuple", "Aligned8")
    res = _compile_and_maybe_run(src, extra_args=["-Zprint-type-sizes"], env=env)
    res["user_print_type_sizes"] = _filter_user_print_type_sizes(res["compile_stdout"], user_types)
    return res


def run_experiment_e_dump_layout(env: dict[str, str]) -> dict[str, Any]:
    src = """#![feature(rustc_attrs)]
#![allow(dead_code, internal_features)]
use core::marker::PhantomData;

#[repr(align(8))]
pub struct Aligned8(pub u8);

#[repr(align(16))]
pub struct Align16Zst;

#[repr(C, packed)]
pub struct ZcUnalign<T>(pub T);

#[repr(transparent)]
pub struct TransZst(pub PhantomData<u8>, pub u64);

#[repr(transparent)]
pub struct TransSingleNon1Zst(pub [u32; 0]);

#[repr(transparent)]
pub struct TransAlign16Zst(pub Align16Zst);

#[repr(C)]
pub struct ReprCSingle(pub u64);

pub struct ReprRustSingle(pub u64);

pub struct SDefault { pub a: u8, pub b: u64, pub c: u8, pub d: u16 }

#[rustc_dump_layout(debug)]
pub type DumpUnalignAligned8 = ZcUnalign<Aligned8>;
#[rustc_dump_layout(debug)]
pub type DumpTransZst = TransZst;
#[rustc_dump_layout(debug)]
pub type DumpTransSingleNon1Zst = TransSingleNon1Zst;
#[rustc_dump_layout(debug)]
pub type DumpTransAlign16Zst = TransAlign16Zst;
#[rustc_dump_layout(debug)]
pub type DumpReprCSingle = ReprCSingle;
#[rustc_dump_layout(debug)]
pub type DumpReprRustSingle = ReprRustSingle;
#[rustc_dump_layout(debug)]
pub type DumpSDefault = SDefault;
"""
    res = _compile_and_maybe_run(src, crate_type="lib", run_binary=False, env=env)
    return res


def main() -> int:
    env = _rustc_env()
    ver = subprocess.run(["rustc", "--version", "--verbose"], capture_output=True, text=True, env=env, check=True)
    results = {
        "rustc_version": _parse_rustc_version_verbose(ver.stdout),
        "experiments": {
            "a_tuple_repr_matrix_and_randomize_layout": run_experiment_a(env),
            "b_zst_alignment_only_impact": run_experiment_b(env),
            "c_illegal_repr_diagnostics": run_experiment_c(env),
            "d_zerocopy_first_customer_layouts": run_experiment_d(env),
            "e_rustc_dump_layout_internals": run_experiment_e_dump_layout(env),
        },
    }
    out_path = Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    print("rustc:", results["rustc_version"].get("headline"))
    print("E0588 retired:", results["experiments"]["c_illegal_repr_diagnostics"]["e0588_retired_in_explain"])
    print("Exp A default:\n" + results["experiments"]["a_tuple_repr_matrix_and_randomize_layout"]["default"]["run_stdout"])
    print("Exp B:\n" + results["experiments"]["b_zst_alignment_only_impact"]["run_stdout"])
    print("Exp D:\n" + results["experiments"]["d_zerocopy_first_customer_layouts"]["run_stdout"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
