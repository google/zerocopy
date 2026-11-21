#!/usr/bin/env python3
"""Standalone empirical probe for rustc TagEncoding::Niche wrapping tag arithmetic,
variant-order size non-monotonicity, StatementKind::SetDiscriminant write-order UB,
niche-hole / dead-slot InvalidTag UB, LLVM !range/assume metadata, x86-64 disassembly,
and MIR enum-operation counts.

Executes real `rustc`, `miri` (with an offline core-only sysroot built from `rust-src`
so the probe runs deterministically without crates.io network access), LLVM IR emission,
and x86-64 assembly emission. Emits sanitized JSON with temporary paths scrubbed.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _run(
    cmd: list[str],
    *,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def _scrub(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for old, new in replacements:
        if old:
            out = out.replace(old, new)
    return out


def _find_tool(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    cargo_bin = Path.home() / ".cargo" / "bin" / name
    if cargo_bin.exists():
        return str(cargo_bin)
    raise RuntimeError(f"Required tool not found on PATH or ~/.cargo/bin: {name}")


def _find_miri_bin(rustc_bin: str) -> str:
    # Prefer `rustup which miri` when available, else sibling of rustc.
    rustup = shutil.which("rustup") or str(Path.home() / ".cargo" / "bin" / "rustup")
    if Path(rustup).exists():
        p = _run([rustup, "which", "miri"])
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    sysroot = _run([rustc_bin, "--print", "sysroot"]).stdout.strip()
    cand = Path(sysroot) / "bin" / "miri"
    if cand.exists():
        return str(cand)
    raise RuntimeError("Could not locate `miri` binary for active rustc toolchain")


def _build_core_miri_sysroot(rustc_bin: str, workdir: Path, target_triple: str) -> Path:
    """Build a minimal offline `no_std` Miri sysroot (core + empty compiler_builtins)
    with `-Zalways-encode-mir` directly from `rust-src`."""
    sysroot = Path(_run([rustc_bin, "--print", "sysroot"]).stdout.strip())
    core_lib = sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "lib.rs"
    if not core_lib.exists():
        raise RuntimeError(f"rust-src libcore not found at expected toolchain path (missing rust-src component?)")

    mroot = workdir / "miri_core_sysroot"
    libdir = mroot / "lib" / "rustlib" / target_triple / "lib"
    libdir.mkdir(parents=True, exist_ok=True)

    cb_src = workdir / "compiler_builtins_stub.rs"
    cb_src.write_text(
        "#![feature(no_core, compiler_builtins)]\n"
        "#![no_core]\n"
        "#![compiler_builtins]\n",
        encoding="utf-8",
    )

    p_core = _run(
        [
            rustc_bin,
            "--crate-name", "core",
            "--crate-type", "rlib",
            "--edition", "2024",
            "-C", "panic=abort",
            "-Zalways-encode-mir",
            "-Zforce-unstable-if-unmarked",
            "-C", "opt-level=0",
            "-C", "debug-assertions=on",
            "-Zub-checks=yes",
            "--cfg=miri",
            str(core_lib),
            "-o", str(libdir / "libcore.rlib"),
        ],
        timeout=180,
    )
    if p_core.returncode != 0:
        raise RuntimeError(f"Failed to compile libcore for Miri sysroot:\n{p_core.stderr}")

    p_cb = _run(
        [
            rustc_bin,
            "--crate-name", "compiler_builtins",
            "--crate-type", "rlib",
            "--edition", "2024",
            "-C", "panic=abort",
            "-Zalways-encode-mir",
            "-Zforce-unstable-if-unmarked",
            str(cb_src),
            "-o", str(libdir / "libcompiler_builtins.rlib"),
        ],
        timeout=60,
    )
    if p_cb.returncode != 0:
        raise RuntimeError(f"Failed to compile compiler_builtins stub:\n{p_cb.stderr}")

    return mroot


def _enum_1_to_n_def(name: str, high: int) -> str:
    variants = ", ".join(f"V{i} = {i}" for i in range(1, high + 1))
    return (
        "#[repr(u8)]\n"
        "#[derive(Copy, Clone, Eq, PartialEq)]\n"
        "#[allow(dead_code)]\n"
        f"pub enum {name} {{ {variants} }}\n"
    )


def _extract_asm_function(asm_text: str, symbol_substr: str) -> str:
    lines = asm_text.splitlines()
    out: list[str] = []
    capturing = False
    for ln in lines:
        if not capturing:
            if symbol_substr in ln and ln.endswith(":"):
                capturing = True
                out.append(ln)
        else:
            out.append(ln)
            if ln.strip() == ".cfi_endproc":
                break
    return "\n".join(out) + ("\n" if out else "")


def _normalize_asm_instructions(asm_func: str) -> list[str]:
    """Extract only machine instructions (stripping labels, directives, comments)
    to compare semantic instruction parity across functions."""
    insns: list[str] = []
    for ln in asm_func.splitlines():
        s = ln.split("#", 1)[0].strip()
        if not s or s.endswith(":") or s.startswith("."):
            continue
        insns.append(re.sub(r"\s+", " ", s))
    return insns


def _extract_llvm_function(ll_text: str, name_substr: str) -> str:
    lines = ll_text.splitlines()
    out: list[str] = []
    capturing = False
    for ln in lines:
        if not capturing:
            if ln.startswith("define ") and name_substr in ln:
                capturing = True
                out.append(ln)
        else:
            out.append(ln)
            if ln.strip() == "}":
                break
    return "\n".join(out)


def _run_part_a(
    rustc_bin: str,
    miri_bin: str,
    mroot: Path,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
) -> dict[str, Any]:
    inner_254 = _enum_1_to_n_def("Inner1To254", 254)
    inner_253 = _enum_1_to_n_def("Inner1To253", 253)

    # 1. Native std program reporting exact layout sizes, alignments, and byte encodings.
    part_a_std = workdir / "part_a_std.rs"
    part_a_std.write_text(
        inner_254
        + inner_253
        + r"""
use core::cell::UnsafeCell;
use core::mem::{align_of, size_of, transmute};
use core::num::NonZero;

#[derive(Copy, Clone)]
pub enum OuterThreeEdge {
    UntaggedPayload(Inner1To254),
    FirstNiche,
    SecondNiche,
}

#[derive(Copy, Clone)]
pub enum OuterThreeEdgeTail {
    FirstNiche,
    SecondNiche,
    UntaggedPayload(Inner1To254),
}

#[derive(Copy, Clone)]
pub enum OuterThreeMiddle {
    FirstNiche,
    UntaggedPayload(Inner1To254),
    SecondNiche,
}

#[derive(Copy, Clone)]
pub enum OuterThreeMiddle3Niches {
    FirstNiche,
    UntaggedPayload(Inner1To253),
    SecondNiche,
}

#[repr(u8)]
#[derive(Copy, Clone)]
#[allow(dead_code)]
pub enum OuterExplicitReprU8 {
    UntaggedPayload(Inner1To254) = 0,
    FirstNiche = 10,
    SecondNiche = 20,
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn classify_outer_edge(x: OuterThreeEdge) -> u8 {
    match x {
        OuterThreeEdge::UntaggedPayload(_) => 10,
        OuterThreeEdge::FirstNiche => 20,
        OuterThreeEdge::SecondNiche => 30,
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn classify_middle_3niches(x: OuterThreeMiddle3Niches) -> u8 {
    match x {
        OuterThreeMiddle3Niches::FirstNiche => 10,
        OuterThreeMiddle3Niches::UntaggedPayload(_) => 20,
        OuterThreeMiddle3Niches::SecondNiche => 30,
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub extern "C" fn classify_opt2_bool(x: Option<Option<bool>>) -> u8 {
    match x {
        Some(Some(false)) => 1,
        Some(Some(true)) => 2,
        Some(None) => 3,
        None => 4,
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn load_opt_bool_from_ref(x: &Option<bool>) -> u8 {
    match *x {
        Some(false) => 0,
        Some(true) => 1,
        None => 2,
    }
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn load_inner254_from_ref(x: &Inner1To254) -> u8 {
    *x as u8
}

fn main() {
    let edge_u1: u8 = unsafe { transmute(OuterThreeEdge::UntaggedPayload(Inner1To254::V1)) };
    let edge_u254: u8 = unsafe { transmute(OuterThreeEdge::UntaggedPayload(Inner1To254::V254)) };
    let edge_n1: u8 = unsafe { transmute(OuterThreeEdge::FirstNiche) };
    let edge_n2: u8 = unsafe { transmute(OuterThreeEdge::SecondNiche) };

    let tail_n1: u8 = unsafe { transmute(OuterThreeEdgeTail::FirstNiche) };
    let tail_n2: u8 = unsafe { transmute(OuterThreeEdgeTail::SecondNiche) };
    let tail_u1: u8 = unsafe { transmute(OuterThreeEdgeTail::UntaggedPayload(Inner1To254::V1)) };

    let mid3_n1: u8 = unsafe { transmute(OuterThreeMiddle3Niches::FirstNiche) };
    let mid3_u1: u8 = unsafe { transmute(OuterThreeMiddle3Niches::UntaggedPayload(Inner1To253::V1)) };
    let mid3_u253: u8 = unsafe { transmute(OuterThreeMiddle3Niches::UntaggedPayload(Inner1To253::V253)) };
    let mid3_n2: u8 = unsafe { transmute(OuterThreeMiddle3Niches::SecondNiche) };

    let opt_b_f: u8 = unsafe { transmute(Some(false)) };
    let opt_b_t: u8 = unsafe { transmute(Some(true)) };
    let opt_b_n: u8 = unsafe { transmute(Option::<bool>::None) };
    let opt2_b_n: u8 = unsafe { transmute(Option::<Option<bool>>::None) };
    let opt3_b_n: u8 = unsafe { transmute(Option::<Option<Option<bool>>>::None) };
    let opt_nz_n: u8 = unsafe { transmute(Option::<NonZero<u8>>::None) };

    let opt_ref_none: usize = unsafe { transmute(Option::<&u32>::None) };
    let res_ref_err: usize = unsafe { transmute(Result::<&u32, ()>::Err(())) };

    let c0 = classify_outer_edge(OuterThreeEdge::UntaggedPayload(Inner1To254::V42));
    let c1 = classify_outer_edge(OuterThreeEdge::FirstNiche);
    let c2 = classify_outer_edge(OuterThreeEdge::SecondNiche);

    let m0 = classify_middle_3niches(OuterThreeMiddle3Niches::FirstNiche);
    let m1 = classify_middle_3niches(OuterThreeMiddle3Niches::UntaggedPayload(Inner1To253::V42));
    let m2 = classify_middle_3niches(OuterThreeMiddle3Niches::SecondNiche);

    let o0 = classify_opt2_bool(Some(Some(false)));
    let o1 = classify_opt2_bool(Some(Some(true)));
    let o2 = classify_opt2_bool(Some(None));
    let o3 = classify_opt2_bool(None);

    let lb = load_opt_bool_from_ref(&Some(true));
    let li = load_inner254_from_ref(&Inner1To254::V7);

    // Find the dead middle byte among {0, 254, 255} not occupied by mid3_n1 or mid3_n2.
    let mut dead_mid3: i32 = -1;
    for b in [254u8, 255u8, 0u8] {
        if b != mid3_n1 && b != mid3_n2 {
            dead_mid3 = b as i32;
        }
    }

    println!("{{");
    println!("  \"sizes_bytes\": {{");
    println!("    \"Inner1To254\": {},", size_of::<Inner1To254>());
    println!("    \"OuterThreeEdge\": {},", size_of::<OuterThreeEdge>());
    println!("    \"OuterThreeEdgeTail\": {},", size_of::<OuterThreeEdgeTail>());
    println!("    \"OuterThreeMiddle\": {},", size_of::<OuterThreeMiddle>());
    println!("    \"Inner1To253\": {},", size_of::<Inner1To253>());
    println!("    \"OuterThreeMiddle3Niches\": {},", size_of::<OuterThreeMiddle3Niches>());
    println!("    \"OuterExplicitReprU8\": {},", size_of::<OuterExplicitReprU8>());
    println!("    \"Option_bool\": {},", size_of::<Option<bool>>());
    println!("    \"Option_Option_bool\": {},", size_of::<Option<Option<bool>>>());
    println!("    \"Option_Option_Option_bool\": {},", size_of::<Option<Option<Option<bool>>>>());
    println!("    \"Option_NonZero_u8\": {},", size_of::<Option<NonZero<u8>>>());
    println!("    \"Option_Option_NonZero_u8\": {},", size_of::<Option<Option<NonZero<u8>>>>());
    println!("    \"Option_OuterThreeEdge\": {},", size_of::<Option<OuterThreeEdge>>());
    println!("    \"Option_ref_u32\": {},", size_of::<Option<&u32>>());
    println!("    \"Result_ref_u32_unit\": {},", size_of::<Result<&u32, ()>>());
    println!("    \"Option_Option_ref_u32\": {},", size_of::<Option<Option<&u32>>>());
    println!("    \"Option_ref_slice_u32\": {},", size_of::<Option<&[u32]>>());
    println!("    \"Option_UnsafeCell_bool\": {},", size_of::<Option<UnsafeCell<bool>>>());
    println!("    \"Option_UnsafeCell_NonZero_u8\": {}", size_of::<Option<UnsafeCell<NonZero<u8>>>>());
    println!("  }},");
    println!("  \"aligns_bytes\": {{");
    println!("    \"OuterThreeEdge\": {},", align_of::<OuterThreeEdge>());
    println!("    \"OuterThreeMiddle\": {},", align_of::<OuterThreeMiddle>());
    println!("    \"Option_ref_u32\": {},", align_of::<Option<&u32>>());
    println!("    \"Result_ref_u32_unit\": {}", align_of::<Result<&u32, ()>>());
    println!("  }},");
    println!("  \"raw_bytes\": {{");
    println!("    \"OuterThreeEdge\": {{\"FirstNiche\": {}, \"UntaggedPayload_V1\": {}, \"UntaggedPayload_V254\": {}, \"SecondNiche\": {}}},", edge_n1, edge_u1, edge_u254, edge_n2);
    println!("    \"OuterThreeEdgeTail\": {{\"FirstNiche\": {}, \"SecondNiche\": {}, \"UntaggedPayload_V1\": {}}},", tail_n1, tail_n2, tail_u1);
    println!("    \"OuterThreeMiddle3Niches\": {{\"FirstNiche\": {}, \"UntaggedPayload_V1\": {}, \"UntaggedPayload_V253\": {}, \"SecondNiche\": {}, \"dead_middle_niche_byte\": {}}},", mid3_n1, mid3_u1, mid3_u253, mid3_n2, dead_mid3);
    println!("    \"Option_bool\": {{\"Some_false\": {}, \"Some_true\": {}, \"None\": {}}},", opt_b_f, opt_b_t, opt_b_n);
    println!("    \"Option_Option_bool_None\": {},", opt2_b_n);
    println!("    \"Option_Option_Option_bool_None\": {},", opt3_b_n);
    println!("    \"Option_NonZero_u8_None\": {},", opt_nz_n);
    println!("    \"Option_ref_u32_None_usize\": {},", opt_ref_none);
    println!("    \"Result_ref_u32_unit_Err_usize\": {}", res_ref_err);
    println!("  }},");
    println!("  \"classifications\": {{");
    println!("    \"OuterThreeEdge\": [{}, {}, {}],", c0, c1, c2);
    println!("    \"OuterThreeMiddle3Niches\": [{}, {}, {}],", m0, m1, m2);
    println!("    \"Option_Option_bool\": [{}, {}, {}, {}],", o0, o1, o2, o3);
    println!("    \"load_checks\": [{}, {}]", lb, li);
    println!("  }}");
    println!("}}");
}
""",
        encoding="utf-8",
    )

    bin_a = workdir / "part_a_bin"
    p_build = _run([rustc_bin, "--edition=2024", "-C", "opt-level=2", str(part_a_std), "-o", str(bin_a)])
    if p_build.returncode != 0:
        raise RuntimeError(f"part_a_std build failed:\n{p_build.stderr}")
    p_exec = _run([str(bin_a)])
    if p_exec.returncode != 0:
        raise RuntimeError(f"part_a_std run failed:\n{p_exec.stderr}")
    runtime_data = json.loads(p_exec.stdout)

    # 2. Emit -Zprint-type-sizes, LLVM IR, and x86-64 assembly at -C opt-level=2
    p_ts = _run([rustc_bin, "--edition=2024", "-C", "opt-level=2", "-Zprint-type-sizes", str(part_a_std), "-o", str(workdir / "part_a_ts")])
    type_size_blocks: dict[str, list[str]] = {}
    target_types = [
        "OuterThreeEdge",
        "OuterThreeEdgeTail",
        "OuterThreeMiddle",
        "OuterThreeMiddle3Niches",
        "OuterExplicitReprU8",
        "Option<Option<bool>>",
        "Option<&u32>",
        "Result<&u32, ()>",
        "Option<UnsafeCell<bool>>",
    ]
    cur_key: str | None = None
    for ln in p_ts.stdout.splitlines():
        if ln.startswith("print-type-size type: `"):
            cur_key = None
            for t in target_types:
                # Exact or suffix match inside backticks
                m = re.search(r"`([^`]+)`", ln)
                if m:
                    ty_name = m.group(1)
                    if (
                        ty_name == t
                        or ty_name.endswith(f"::{t}")
                        or (t == "Option<Option<bool>>" and ty_name == "std::option::Option<std::option::Option<bool>>")
                        or (t == "Option<&u32>" and ty_name == "std::option::Option<&u32>")
                        or (t == "Result<&u32, ()>" and ty_name == "std::result::Result<&u32, ()>")
                        or (t == "Option<UnsafeCell<bool>>" and ty_name == "std::option::Option<std::cell::UnsafeCell<bool>>")
                    ):
                        cur_key = t
                        type_size_blocks[cur_key] = [ln]
                        break
        elif cur_key is not None and ln.startswith("print-type-size"):
            type_size_blocks[cur_key].append(ln)
        else:
            cur_key = None

    ll_path = workdir / "part_a.ll"
    asm_path = workdir / "part_a.s"
    p_emit = _run([
        rustc_bin, "--edition=2024", "-C", "opt-level=2",
        "--emit=llvm-ir=" + str(ll_path),
        "--emit=asm=" + str(asm_path),
        str(part_a_std),
    ])
    if p_emit.returncode != 0:
        raise RuntimeError(f"part_a emit failed:\n{p_emit.stderr}")

    ll_text = ll_path.read_text(encoding="utf-8")
    asm_text = asm_path.read_text(encoding="utf-8")

    # Extract !range metadata definitions referenced in emitted LLVM IR functions
    range_md_defs = [ln for ln in ll_text.splitlines() if re.match(r"^!\d+\s*=\s*!\{i\d+\s+", ln)]

    # 3. Also run a Miri verification of the layout & classification invariants (no_std)
    part_a_miri = workdir / "part_a_miri.rs"
    part_a_miri.write_text(
        "#![no_std]\n#![no_main]\n"
        + inner_254
        + inner_253
        + r"""
use core::mem::{size_of, transmute};
use core::num::NonZero;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[derive(Copy, Clone)]
pub enum OuterThreeEdge { UntaggedPayload(Inner1To254), FirstNiche, SecondNiche }
#[derive(Copy, Clone)]
pub enum OuterThreeMiddle { FirstNiche, UntaggedPayload(Inner1To254), SecondNiche }
#[derive(Copy, Clone)]
pub enum OuterThreeMiddle3Niches { FirstNiche, UntaggedPayload(Inner1To253), SecondNiche }

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    assert!(size_of::<Inner1To254>() == 1);
    assert!(size_of::<OuterThreeEdge>() == 1);
    assert!(size_of::<OuterThreeMiddle>() == 2);
    assert!(size_of::<OuterThreeMiddle3Niches>() == 1);
    assert!(size_of::<Option<Option<bool>>>() == 1);
    assert!(size_of::<Option<&u32>>() == size_of::<&u32>());
    assert!(size_of::<Result<&u32, ()>>() == size_of::<&u32>());
    let b1: u8 = unsafe { transmute(OuterThreeEdge::FirstNiche) };
    let b2: u8 = unsafe { transmute(OuterThreeEdge::SecondNiche) };
    let bu: u8 = unsafe { transmute(OuterThreeEdge::UntaggedPayload(Inner1To254::V42)) };
    assert!(b1 == 255 && b2 == 0 && bu == 42);
    let m1: u8 = unsafe { transmute(OuterThreeMiddle3Niches::FirstNiche) };
    let m2: u8 = unsafe { transmute(OuterThreeMiddle3Niches::SecondNiche) };
    assert!(m1 == 254 && m2 == 0);
    let nz_none: u8 = unsafe { transmute(Option::<NonZero<u8>>::None) };
    assert!(nz_none == 0);
    0
}
""",
        encoding="utf-8",
    )
    p_miri_a = _run([miri_bin, "--edition=2024", "-C", "panic=abort", "--sysroot", str(mroot), str(part_a_miri)])

    return {
        "runtime": runtime_data,
        "miri_rc": p_miri_a.returncode,
        "miri_stderr": _scrub(p_miri_a.stderr.strip(), scrub_rules),
        "print_type_sizes": type_size_blocks,
        "llvm_ir": {
            "classify_outer_edge": _extract_llvm_function(ll_text, "classify_outer_edge"),
            "classify_middle_3niches": _extract_llvm_function(ll_text, "classify_middle_3niches"),
            "classify_opt2_bool": _extract_llvm_function(ll_text, "classify_opt2_bool"),
            "load_opt_bool_from_ref": _extract_llvm_function(ll_text, "load_opt_bool_from_ref"),
            "load_inner254_from_ref": _extract_llvm_function(ll_text, "load_inner254_from_ref"),
            "range_metadata_nodes": range_md_defs,
        },
        "x86_64_asm_opt2": {
            "classify_outer_edge": _extract_asm_function(asm_text, "classify_outer_edge"),
            "classify_middle_3niches": _extract_asm_function(asm_text, "classify_middle_3niches"),
            "classify_opt2_bool": _extract_asm_function(asm_text, "classify_opt2_bool"),
        },
    }


def _run_ub_case(
    name: str,
    std_src: str,
    nostd_src: str,
    rustc_bin: str,
    miri_bin: str,
    mroot: Path,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
    asm_symbol: str | None = None,
) -> dict[str, Any]:
    std_path = workdir / f"{name}_std.rs"
    nostd_path = workdir / f"{name}_nostd.rs"
    bin_path = workdir / f"{name}_bin"
    asm_path = workdir / f"{name}.s"
    std_path.write_text(std_src, encoding="utf-8")
    nostd_path.write_text(nostd_src, encoding="utf-8")

    p_build = _run([rustc_bin, "--edition=2024", "-C", "opt-level=2", str(std_path), "-o", str(bin_path)])
    if p_build.returncode != 0:
        raise RuntimeError(f"Case {name} native build failed:\n{p_build.stderr}")
    p_native = _run([str(bin_path)])

    p_miri = _run([
        miri_bin, "--edition=2024", "-C", "panic=abort", "-C", "opt-level=0",
        "--sysroot", str(mroot), str(nostd_path),
    ])

    diag_lines: list[str] = []
    if p_miri.returncode != 0:
        in_error = False
        for ln in p_miri.stderr.splitlines():
            if "error: Undefined Behavior:" in ln:
                in_error = True
            if in_error and any(tok in ln for tok in ("error: Undefined Behavior:", "Undefined Behavior occurred here", "= help:", "-->", "at ")):
                diag_lines.append(_scrub(ln, scrub_rules))

    result: dict[str, Any] = {
        "native_opt2_rc": p_native.returncode,
        "native_opt2_stdout": p_native.stdout.strip(),
        "miri_opt0_rc": p_miri.returncode,
        "miri_diag_head": diag_lines[:8],
    }

    if asm_symbol:
        p_asm = _run([
            rustc_bin, "--edition=2024", "-C", "opt-level=2",
            "--emit=asm=" + str(asm_path), str(std_path),
        ])
        if p_asm.returncode == 0:
            asm_func = _extract_asm_function(asm_path.read_text(encoding="utf-8"), asm_symbol)
            result["asm_func"] = asm_func
            result["asm_instructions"] = _normalize_asm_instructions(asm_func)

    return result


def _run_part_b(
    rustc_bin: str,
    miri_bin: str,
    mroot: Path,
    workdir: Path,
    scrub_rules: list[tuple[str, str]],
    dead_mid3_byte: int,
) -> dict[str, Any]:
    inner_253 = _enum_1_to_n_def("Inner1To253", 253)

    # B1: Valid write order — payload before SetDiscriminant(RET, 1)
    b1_body = """
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
use core::num::NonZero;

#[inline(never)]
#[unsafe(no_mangle)]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub extern "C" fn make_some_nz(v: NonZero<u8>) -> Option<NonZero<u8>> {
    mir! {
        {
            place!(Field(Variant(RET, 1), 0)) = v;
            SetDiscriminant(RET, 1);
            Return()
        }
    }
}
"""
    b1_std = b1_body + """
fn main() {
    let x = make_some_nz(NonZero::new(7).unwrap());
    assert_eq!(x.map(|n| n.get()), Some(7));
    println!("OK:{}", x.unwrap().get());
}
"""
    b1_nostd = "#![no_std]\n#![no_main]\n" + b1_body + """
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = make_some_nz(NonZero::new(7).unwrap());
    match x { Some(n) if n.get() == 7 => 0, _ => 2 }
}
"""

    # B2a: Reordered SetDiscriminant(RET, 1) BEFORE payload write over None-initialized RET
    # -> triggers InvalidNichedEnumVariantWritten in Miri!
    b2a_body = """
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
use core::num::NonZero;

#[inline(never)]
#[unsafe(no_mangle)]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub extern "C" fn make_some_nz(v: NonZero<u8>) -> Option<NonZero<u8>> {
    mir! {
        {
            RET = Option::None;
            SetDiscriminant(RET, 1);
            place!(Field(Variant(RET, 1), 0)) = v;
            Return()
        }
    }
}
"""
    b2a_std = b2a_body + """
fn main() {
    let x = make_some_nz(NonZero::new(7).unwrap());
    assert_eq!(x.map(|n| n.get()), Some(7));
    println!("OK:{}", x.unwrap().get());
}
"""
    b2a_nostd = "#![no_std]\n#![no_main]\n" + b2a_body + """
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = make_some_nz(NonZero::new(7).unwrap());
    match x { Some(n) if n.get() == 7 => 0, _ => 2 }
}
"""

    # B2b: Reordered SetDiscriminant(RET, 1) BEFORE payload write over UNINITIALIZED RET
    # -> triggers uninitialized read UB during write_discriminant's validation read!
    b2b_body = """
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;
use core::num::NonZero;

#[inline(never)]
#[unsafe(no_mangle)]
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub extern "C" fn make_some_nz(v: NonZero<u8>) -> Option<NonZero<u8>> {
    mir! {
        {
            SetDiscriminant(RET, 1);
            place!(Field(Variant(RET, 1), 0)) = v;
            Return()
        }
    }
}
"""
    b2b_std = b2b_body + """
fn main() {
    let x = make_some_nz(NonZero::new(7).unwrap());
    assert_eq!(x.map(|n| n.get()), Some(7));
    println!("OK:{}", x.unwrap().get());
}
"""
    b2b_nostd = "#![no_std]\n#![no_main]\n" + b2b_body + """
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let x = make_some_nz(NonZero::new(7).unwrap());
    match x { Some(n) if n.get() == 7 => 0, _ => 2 }
}
"""

    # B3: Option<bool> byte 0x03 niche hole (outside valid_range 0..=2) via raw-ptr read -> direct InvalidTag(0x03)
    b3_std = """
fn main() {
    let raw: u8 = core::hint::black_box(3u8);
    let p = (&raw as *const u8) as *const Option<bool>;
    let tag = unsafe {
        match *p {
            Some(false) => 0u8,
            Some(true) => 1u8,
            None => 2u8,
        }
    };
    println!("TAG:{}", tag);
}
"""
    b3_nostd = """
#![no_std]
#![no_main]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: u8 = core::hint::black_box(3u8);
    let p = (&raw as *const u8) as *const Option<bool>;
    unsafe {
        match *p {
            Some(false) => 0,
            Some(true) => 1,
            None => 2,
        }
    }
}
"""

    # B4: OuterThreeMiddle3Niches dead middle slot (0xff) inside niche_variants AND inside valid_range!
    # Raw-ptr read triggers discriminant.rs:188-193 (`variant_index == untagged_variant` -> InvalidTag(0xff))!
    b4_common = (
        inner_253
        + f"""
#[derive(Copy, Clone)]
pub enum OuterThreeMiddle3Niches {{
    FirstNiche,
    UntaggedPayload(Inner1To253),
    SecondNiche,
}}
const DEAD_BYTE: u8 = {dead_mid3_byte}u8;
"""
    )
    b4_std = b4_common + """
fn main() {
    let raw: u8 = core::hint::black_box(DEAD_BYTE);
    let p = (&raw as *const u8) as *const OuterThreeMiddle3Niches;
    let tag = unsafe {
        match *p {
            OuterThreeMiddle3Niches::FirstNiche => 10u8,
            OuterThreeMiddle3Niches::UntaggedPayload(_) => 20u8,
            OuterThreeMiddle3Niches::SecondNiche => 30u8,
        }
    };
    println!("TAG:{}", tag);
}
"""
    b4_nostd = "#![no_std]\n#![no_main]\n" + b4_common + """
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let raw: u8 = core::hint::black_box(DEAD_BYTE);
    let p = (&raw as *const u8) as *const OuterThreeMiddle3Niches;
    unsafe {
        match *p {
            OuterThreeMiddle3Niches::FirstNiche => 10,
            OuterThreeMiddle3Niches::UntaggedPayload(_) => 20,
            OuterThreeMiddle3Niches::SecondNiche => 30,
        }
    }
}
"""

    b1 = _run_ub_case("b1_valid", b1_std, b1_nostd, rustc_bin, miri_bin, mroot, workdir, scrub_rules, asm_symbol="make_some_nz")
    b2a = _run_ub_case("b2a_reordered_none", b2a_std, b2a_nostd, rustc_bin, miri_bin, mroot, workdir, scrub_rules, asm_symbol="make_some_nz")
    b2b = _run_ub_case("b2b_reordered_uninit", b2b_std, b2b_nostd, rustc_bin, miri_bin, mroot, workdir, scrub_rules, asm_symbol="make_some_nz")
    b3 = _run_ub_case("b3_opt_bool_byte3", b3_std, b3_nostd, rustc_bin, miri_bin, mroot, workdir, scrub_rules)
    b4 = _run_ub_case("b4_middle_dead_slot", b4_std, b4_nostd, rustc_bin, miri_bin, mroot, workdir, scrub_rules)

    return {
        "valid_payload_before_set_discriminant": b1,
        "reordered_set_discriminant_before_payload_over_none_ub": b2a,
        "reordered_set_discriminant_before_payload_over_uninit_ub": b2b,
        "native_opt2_machine_code_identical_b1_b2a_b2b": (
            b1.get("asm_instructions") == b2a.get("asm_instructions") == b2b.get("asm_instructions")
            and bool(b1.get("asm_instructions"))
        ),
        "option_bool_byte3_niche_hole_ub": b3,
        "middle_3niches_dead_slot_invalid_tag_ub": b4,
    }


NON_ADT_HEADS = {
    "Add", "AddUnchecked", "AddWithOverflow", "Sub", "SubUnchecked", "SubWithOverflow",
    "Mul", "MulUnchecked", "MulWithOverflow", "Div", "Rem", "BitXor", "BitAnd", "BitOr",
    "Shl", "ShlUnchecked", "Shr", "ShrUnchecked", "Eq", "Lt", "Le", "Ne", "Ge", "Gt",
    "Cmp", "Offset", "Not", "Neg", "PtrMetadata", "Len", "CopyForDeref",
    "WrapUnsafeBinder", "ShallowInitBox", "NullaryOp", "AlignOf", "SizeOf", "UbChecks",
    "ContractChecks", "OffsetOf", "ThreadLocalRef", "Repeat", "Cast", "Discriminant",
}


def _strip_turbofish(s: str) -> str:
    out: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        if s[i : i + 3] == "::<":
            depth = 1
            i += 3
            while i < n and depth > 0:
                if s[i] == "<":
                    depth += 1
                elif s[i] == ">":
                    depth -= 1
                i += 1
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def _count_mir_enum_ops(mir_dir: Path) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for label, suffix in (
        ("post_cleanup", "*runtime-post-cleanup.after.mir"),
        ("final_optimized", "*runtime-optimized.after.mir"),
    ):
        files = sorted(glob.glob(str(mir_dir / suffix)))
        set_discr = discr_rv = downcast = adt_agg = 0
        for fp in files:
            txt = Path(fp).read_text(encoding="utf-8", errors="replace")
            set_discr += len(re.findall(r"^\s*discriminant\(.+\)\s*=", txt, re.M))
            discr_rv += len(re.findall(r"=\s*discriminant\(", txt))
            downcast += len(re.findall(r"\bas\s+[A-Za-z_][A-Za-z0-9_]*\)", txt))
            for ln in txt.splitlines():
                s = ln.strip()
                if " = " in s and not s.startswith("//") and not s.startswith("let "):
                    rhs = s.split(" = ", 1)[1]
                    rhs_clean = _strip_turbofish(rhs)
                    m = re.match(r"^((?:[a-zA-Z0-9_]+::)*([A-Z][a-zA-Z0-9_]*))\s*[\(\{]", rhs_clean)
                    if m and m.group(1) not in NON_ADT_HEADS and m.group(2) not in NON_ADT_HEADS:
                        adt_agg += 1
        out[label] = {
            "bodies": len(files),
            "set_discriminant_stmts": set_discr,
            "discriminant_rvalues": discr_rv,
            "downcast_projections": downcast,
            "adt_aggregates": adt_agg,
        }
    return out


def _run_part_c(
    rustc_bin: str,
    workdir: Path,
    zerocopy_src: Path | None,
) -> dict[str, Any]:
    # 1. Async coroutine probe proving StateTransform DOES emit SetDiscriminant
    async_src = workdir / "async_probe.rs"
    async_src.write_text(
        "pub async fn two_step(x: u32) -> u32 {\n"
        "    let a = core::future::ready(x + 1).await;\n"
        "    a + 2\n"
        "}\n",
        encoding="utf-8",
    )
    async_mir = workdir / "async_mir"
    async_mir.mkdir(parents=True, exist_ok=True)
    p_async = _run([
        rustc_bin, "--edition=2024", "--crate-type", "lib", "-O",
        "-Zdump-mir=runtime-post-cleanup | runtime-optimized",
        f"-Zdump-mir-dir={async_mir}",
        str(async_src), "-o", str(workdir / "libasync_probe.rlib"),
    ])
    if p_async.returncode != 0:
        raise RuntimeError(f"async probe failed:\n{p_async.stderr}")

    async_counts = _count_mir_enum_ops(async_mir)
    async_set_discr_lines: list[str] = []
    for fp in sorted(glob.glob(str(async_mir / "*runtime-post-cleanup.after.mir"))):
        for ln in Path(fp).read_text(encoding="utf-8").splitlines():
            if re.search(r"^\s*discriminant\(.+\)\s*=", ln):
                async_set_discr_lines.append(ln.strip())

    result: dict[str, Any] = {
        "async_coroutine_probe": {
            "counts": async_counts,
            "post_cleanup_set_discriminant_lines": async_set_discr_lines,
        }
    }

    # 2. Optional live zerocopy crate MIR census (std+alloc+simd and default no_std)
    if zerocopy_src is not None:
        zc_dir = zerocopy_src
        build_rs = zc_dir / "build.rs"
        lib_rs = zc_dir / "src" / "lib.rs"
        cargo_toml = zc_dir / "Cargo.toml"
        if not lib_rs.exists() or not build_rs.exists():
            raise RuntimeError(f"--zerocopy-src missing src/lib.rs or build.rs: {zc_dir}")
        ver_m = re.search(r'^version\s*=\s*"([^"]+)"', cargo_toml.read_text(encoding="utf-8"), re.M)
        pkg_ver = ver_m.group(1) if ver_m else "0.0.0"

        bs_bin = workdir / "zc_build_script"
        p_bs = _run([rustc_bin, "--edition=2021", str(build_rs), "-o", str(bs_bin)])
        if p_bs.returncode != 0:
            raise RuntimeError(f"zerocopy build.rs compile failed:\n{p_bs.stderr}")
        bs_env = os.environ.copy()
        bs_env["RUSTC"] = rustc_bin
        bs_env["CARGO_MANIFEST_DIR"] = str(zc_dir)
        bs_env["CARGO_PKG_NAME"] = "zerocopy"
        p_bs_run = _run([str(bs_bin)], cwd=str(zc_dir), env=bs_env)
        if p_bs_run.returncode != 0:
            raise RuntimeError(f"zerocopy build.rs run failed:\n{p_bs_run.stderr}")
        cfgs: list[str] = []
        for ln in p_bs_run.stdout.splitlines():
            if ln.startswith("cargo:rustc-cfg="):
                cfgs.extend(["--cfg", ln.split("cargo:rustc-cfg=", 1)[1].strip()])

        zc_results: dict[str, Any] = {"crate_version": pkg_ver, "build_cfgs": cfgs}
        for profile_name, extra_cfgs in (
            ("std_alloc_simd", ["--cfg", 'feature="simd"', "--cfg", 'feature="alloc"', "--cfg", 'feature="std"']),
            ("default_no_std", []),
        ):
            mir_dir = workdir / f"zc_mir_{profile_name}"
            mir_dir.mkdir(parents=True, exist_ok=True)
            zc_env = os.environ.copy()
            zc_env["CARGO_PKG_VERSION"] = pkg_ver
            p_zc = _run(
                [
                    rustc_bin, "--edition=2021", "--crate-name", "zerocopy", "--crate-type", "lib", "-O",
                    *extra_cfgs, *cfgs,
                    "-Zdump-mir=runtime-post-cleanup | runtime-optimized",
                    f"-Zdump-mir-dir={mir_dir}",
                    str(lib_rs), "-o", str(workdir / f"libzerocopy_{profile_name}.rlib"),
                ],
                env=zc_env,
                timeout=180,
            )
            if p_zc.returncode != 0:
                raise RuntimeError(f"zerocopy ({profile_name}) compile failed:\n{p_zc.stderr}")
            zc_results[profile_name] = _count_mir_enum_ops(mir_dir)
        result["zerocopy_mir_census"] = zc_results

    return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, help="Output JSON path (prints to stdout if omitted)")
    ap.add_argument(
        "--zerocopy-src",
        type=Path,
        default=None,
        help="Optional path to zerocopy crate root (containing Cargo.toml, build.rs, src/lib.rs) for live MIR enum-op census",
    )
    args = ap.parse_args()

    rustc_bin = _find_tool("rustc")
    miri_bin = _find_miri_bin(rustc_bin)
    rustc_vv = _run([rustc_bin, "-vV"]).stdout.strip()
    miri_ver = _run([miri_bin, "--version"]).stdout.strip()
    host_m = re.search(r"^host:\s*(\S+)", rustc_vv, re.M)
    target_triple = host_m.group(1) if host_m else "x86_64-unknown-linux-gnu"

    with tempfile.TemporaryDirectory(prefix="probe_niche_") as td:
        workdir = Path(td)
        scrub_rules = [
            (str(workdir), "<TMPDIR>"),
            (str(Path.home()), "<HOME>"),
        ]
        mroot = _build_core_miri_sysroot(rustc_bin, workdir, target_triple)
        part_a = _run_part_a(rustc_bin, miri_bin, mroot, workdir, scrub_rules)
        dead_mid3 = int(part_a["runtime"]["raw_bytes"]["OuterThreeMiddle3Niches"]["dead_middle_niche_byte"])
        part_b = _run_part_b(rustc_bin, miri_bin, mroot, workdir, scrub_rules, dead_mid3)
        part_c = _run_part_c(rustc_bin, workdir, args.zerocopy_src)

    payload = {
        "rustc_version": rustc_vv,
        "miri_version": miri_ver,
        "target_triple": target_triple,
        "part_a_wrapping_niche_and_layout": part_a,
        "part_b_set_discriminant_and_invalid_tag_ub": part_b,
        "part_c_mir_enum_ops": part_c,
    }

    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded, encoding="utf-8")
        print(f"Wrote {args.out} ({len(encoded)} bytes)")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
