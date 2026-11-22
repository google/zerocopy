#!/usr/bin/env python3
"""Reproducible cross-crate probe for rustc crate-type symbol export levels,
.rmeta MIR encoding vs. cross_crate_inlinable decoupling, and -Z share-generics.

Requires: rustc (nightly, for #![feature(linkage)] and -Z flags), llvm-ar,
llvm-nm, and llvm-readobj (discovered from rustc's sysroot or PATH).

Usage:
    python3 probe_rmeta_export_and_share_generics.py [--out <path.json>]
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

UPSTREAM_SRC = r"""#![feature(linkage)]

#[unsafe(no_mangle)]
pub extern "C" fn c_api_no_mangle(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[unsafe(export_name = "custom_c_export_sym")]
pub extern "C" fn internal_rust_name(x: u32) -> u32 {
    x.wrapping_add(2)
}

#[linkage = "weak"]
#[unsafe(no_mangle)]
pub extern "C" fn weak_c_hook(x: u32) -> u32 {
    x.wrapping_mul(3)
}

#[unsafe(no_mangle)]
#[unsafe(link_section = ".my_custom_sec")]
pub static CUSTOM_SEC_VAL: u64 = 0x1122_3344_5566_7788;

pub fn rust_unmarked_leaf(x: u32) -> u32 {
    x.wrapping_mul(5).wrapping_add(7)
}

#[inline]
pub fn rust_marked_inline(x: u32) -> u32 {
    x.wrapping_mul(11).wrapping_add(13)
}

#[inline(never)]
pub fn rust_marked_noinline(x: u32) -> u32 {
    x.wrapping_mul(17).wrapping_add(19)
}

#[inline(never)]
pub fn opaque_step(x: u64) -> u64 {
    x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407)
}

pub fn generic_shared<T: Copy + Into<u64>>(x: T, y: T) -> u64 {
    let mut acc = opaque_step(x.into());
    acc ^= opaque_step(y.into());
    acc = opaque_step(acc.wrapping_add(1));
    acc ^ opaque_step(acc.wrapping_add(2))
}

#[inline(never)]
pub fn generic_noinline<T: Copy + Into<u64>>(x: T, y: T) -> u64 {
    let mut acc = opaque_step(x.into());
    acc ^= opaque_step(y.into());
    acc = opaque_step(acc.wrapping_add(3));
    acc ^ opaque_step(acc.wrapping_add(4))
}

pub fn generic_tiny_leaf<T: Copy + core::ops::Add<Output = T>>(x: T, y: T) -> T {
    x + y
}

pub fn upstream_instantiate_u32(a: u32, b: u32) -> u64 {
    let s1 = generic_shared::<u32>(a, b);
    let s2 = generic_noinline::<u32>(a, b);
    let s3 = generic_tiny_leaf::<u32>(a, b) as u64;
    let s4 = rust_marked_noinline(a) as u64;
    s1.wrapping_add(s2).wrapping_add(s3).wrapping_add(s4)
}
"""

DOWNSTREAM_MIR_SRC = r"""extern crate upstream;

#[unsafe(no_mangle)]
pub extern "C" fn ds_call_unmarked(x: u32) -> u32 {
    upstream::rust_unmarked_leaf(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn ds_call_marked_inline(x: u32) -> u32 {
    upstream::rust_marked_inline(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn ds_call_marked_noinline(x: u32) -> u32 {
    upstream::rust_marked_noinline(x)
}
"""

DOWNSTREAM_SHARE_SRC = r"""extern crate upstream;

#[unsafe(no_mangle)]
pub extern "C" fn ds_use_generics(a: u32, b: u32, c: u64, d: u64) -> u64 {
    let r1 = upstream::generic_shared::<u32>(a, b);
    let r2 = upstream::generic_noinline::<u32>(a, b);
    let r3 = upstream::generic_shared::<u64>(c, d);
    let r4 = upstream::generic_noinline::<u64>(c, d);
    let r5 = upstream::generic_tiny_leaf::<u32>(a, b) as u64;
    r1.wrapping_add(r2).wrapping_add(r3).wrapping_add(r4).wrapping_add(r5)
}
"""

MAIN_SHARE_SRC = r"""extern crate ds;
extern crate upstream;

fn main() {
    let v = ds::ds_use_generics(10, 20, 30, 40);
    let u = upstream::upstream_instantiate_u32(10, 20);
    println!("{v}:{u}");
}
"""

WEAK_OVERRIDE_SRC = r"""extern crate upstream;

#[unsafe(no_mangle)]
pub extern "C" fn weak_c_hook(x: u32) -> u32 {
    x.wrapping_add(999)
}

fn main() {
    let weak_res = weak_c_hook(5);
    let c_res = upstream::c_api_no_mangle(5);
    let sec_val = upstream::CUSTOM_SEC_VAL;
    println!("{weak_res}:{c_res}:{sec_val:#x}");
}
"""


def find_toolchain() -> tuple[str, str, str, dict[str, str], dict[str, str]]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if Path(cargo_bin).is_dir() and cargo_bin not in env.get("PATH", "").split(":"):
        env["PATH"] = cargo_bin + ":" + env.get("PATH", "")
    rustc = shutil.which("rustc", path=env["PATH"])
    if not rustc:
        raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")
    vv = subprocess.check_output([rustc, "-vV"], text=True, env=env).strip()
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True, env=env).strip()
    host = ""
    for line in vv.splitlines():
        if line.startswith("host:"):
            host = line.split(":", 1)[1].strip()
    llvm_dir = Path(sysroot) / "lib" / "rustlib" / host / "bin"
    tools: dict[str, str] = {}
    for name in ("llvm-ar", "llvm-nm", "llvm-readobj"):
        cand = llvm_dir / name
        if cand.is_file():
            tools[name] = str(cand)
        else:
            found = shutil.which(name, path=env["PATH"])
            if not found:
                raise RuntimeError(f"Required LLVM tool {name!r} not found")
            tools[name] = found
    return rustc, vv, host, tools, env


def run(cmd: list[str], env: dict[str, str], cwd: Path | None = None) -> str:
    res = subprocess.run(cmd, env=env, cwd=cwd, capture_output=True, text=True)
    if res.returncode != 0:
        raise RuntimeError(
            f"Command failed (exit {res.returncode}): {cmd[0]}\nSTDOUT:\n{res.stdout}\nSTDERR:\n{res.stderr}"
        )
    return res.stdout


def parse_ar_tv(text: str) -> list[dict[str, object]]:
    members: list[dict[str, object]] = []
    for line in text.splitlines():
        parts = line.split()
        if len(parts) >= 8:
            try:
                size: int | None = int(parts[2])
            except ValueError:
                size = None
            members.append({"name": parts[-1], "size_bytes": size})
    return members


def extract_fn_ir(ir_text: str, fn_name: str) -> str:
    m = re.search(
        rf"(define [^\n]*@{re.escape(fn_name)}\([^\n]*\{{.*?^\}})",
        ir_text,
        re.S | re.M,
    )
    return m.group(1) if m else ""


def extract_v0_instantiating_suffix(line: str) -> str | None:
    m = re.search(r"@(_R[A-Za-z0-9_]+)\(", line)
    if not m:
        return None
    sym = m.group(1)
    # In Rust v0 mangling, a generic instantiation ends with E<instantiating_crate_path>
    # where instantiating_crate_path is either a backreference (B<base62>_) or a crate root (C...).
    idx = sym.rfind("E")
    return sym[idx:] if idx != -1 else None


def run_probe() -> dict[str, object]:
    rustc, vv, host, tools, env = find_toolchain()
    result: dict[str, object] = {
        "rustc_version": vv,
        "host": host,
    }

    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        up_rs = tmp / "upstream.rs"
        ds_mir_rs = tmp / "ds_mir.rs"
        ds_share_rs = tmp / "ds_share.rs"
        main_share_rs = tmp / "main_share.rs"
        weak_override_rs = tmp / "weak_override.rs"
        up_rs.write_text(UPSTREAM_SRC)
        ds_mir_rs.write_text(DOWNSTREAM_MIR_SRC)
        ds_share_rs.write_text(DOWNSTREAM_SHARE_SRC)
        main_share_rs.write_text(MAIN_SHARE_SRC)
        weak_override_rs.write_text(WEAK_OVERRIDE_SRC)

        # ------------------------------------------------------------------
        # Part A: 4-crate-type matrix + combined (cdylib + rlib) + weak override
        # ------------------------------------------------------------------
        part_a: dict[str, object] = {}
        rlib_for_weak: Path | None = None
        for ct, fname in [
            ("rlib", "libupstream.rlib"),
            ("dylib", "libupstream.so"),
            ("cdylib", "libupstream_cdylib.so"),
            ("staticlib", "libupstream.a"),
        ]:
            ct_dir = tmp / f"ct_{ct}"
            ct_dir.mkdir()
            out_file = ct_dir / fname
            run(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-name=upstream",
                    f"--crate-type={ct}",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "symbol-mangling-version=v0",
                    "-o",
                    str(out_file),
                    str(up_rs),
                ],
                env,
            )
            if ct == "rlib":
                rlib_for_weak = out_file

            info: dict[str, object] = {"file_bytes": out_file.stat().st_size}
            if ct in ("rlib", "staticlib"):
                members = parse_ar_tv(run([tools["llvm-ar"], "tv", str(out_file)], env))
                info["archive_member_count"] = len(members)
                info["archive_members_head"] = members[:6]
                rmeta = [m for m in members if m["name"] == "lib.rmeta"]
                rmeta_link = [m for m in members if m["name"] == "lib.rmeta-link"]
                info["lib_rmeta_bytes"] = rmeta[0]["size_bytes"] if rmeta else None
                info["has_lib_rmeta_link"] = bool(rmeta_link)
                info["lib_rmeta_link_bytes"] = (
                    rmeta_link[0]["size_bytes"] if rmeta_link else None
                )
                nm_out = run([tools["llvm-nm"], "--defined-only", str(out_file)], env)
                info["has_c_api_no_mangle"] = bool(
                    re.search(r"\bT c_api_no_mangle$", nm_out, re.M)
                )
                info["has_custom_c_export_sym"] = bool(
                    re.search(r"\bT custom_c_export_sym$", nm_out, re.M)
                )
                info["has_CUSTOM_SEC_VAL"] = bool(
                    re.search(r"\b[RD] CUSTOM_SEC_VAL$", nm_out, re.M)
                )
                info["has_upstream_instantiate_u32_global"] = bool(
                    re.search(r"\bT _R[^\n]*upstream_instantiate_u32$", nm_out, re.M)
                )
                info["has_upstream_instantiate_u32_any"] = (
                    "upstream_instantiate_u32" in nm_out
                )
                info["weak_c_hook_lines"] = [
                    l.strip() for l in nm_out.splitlines() if "weak_c_hook" in l
                ]
                # Extract first .rcgu.o to verify .my_custom_sec and lib.rmeta-link section
                ext_dir = ct_dir / "extracted"
                ext_dir.mkdir()
                rcgu_names = [
                    str(m["name"])
                    for m in members
                    if str(m["name"]).startswith("libupstream.")
                    and str(m["name"]).endswith(".rcgu.o")
                ]
                has_sec = False
                for rcgu in rcgu_names:
                    run([tools["llvm-ar"], "x", str(out_file), rcgu], env, cwd=ext_dir)
                    sec_out = run(
                        [tools["llvm-readobj"], "--sections", str(ext_dir / rcgu)], env
                    )
                    if ".my_custom_sec" in sec_out:
                        has_sec = True
                info["has_my_custom_sec"] = has_sec
                if rmeta_link:
                    run(
                        [tools["llvm-ar"], "x", str(out_file), "lib.rmeta-link"],
                        env,
                        cwd=ext_dir,
                    )
                    rl_secs = run(
                        [
                            tools["llvm-readobj"],
                            "--sections",
                            str(ext_dir / "lib.rmeta-link"),
                        ],
                        env,
                    )
                    info["lib_rmeta_link_has_section"] = ".rmeta-link" in rl_secs
            else:
                nm_dyn = run(
                    [tools["llvm-nm"], "-D", "--defined-only", str(out_file)], env
                )
                dyn_lines = [l.strip() for l in nm_dyn.splitlines() if l.strip()]
                info["defined_dyn_symbol_count"] = len(dyn_lines)
                info["has_c_api_no_mangle"] = any(
                    re.search(r"\bT c_api_no_mangle$", l) for l in dyn_lines
                )
                info["has_custom_c_export_sym"] = any(
                    re.search(r"\bT custom_c_export_sym$", l) for l in dyn_lines
                )
                info["has_CUSTOM_SEC_VAL"] = any(
                    re.search(r"\b[RD] CUSTOM_SEC_VAL$", l) for l in dyn_lines
                )
                info["has_upstream_instantiate_u32"] = any(
                    "upstream_instantiate_u32" in l for l in dyn_lines
                )
                info["has_rust_metadata_symbol"] = any(
                    "rust_metadata_upstream_" in l for l in dyn_lines
                )
                info["weak_c_hook_lines"] = [
                    l for l in dyn_lines if "weak_c_hook" in l
                ]
                secs = run([tools["llvm-readobj"], "--sections", str(out_file)], env)
                info["has_my_custom_sec"] = ".my_custom_sec" in secs
                if len(dyn_lines) <= 20:
                    info["all_defined_dyn_symbols"] = dyn_lines
                else:
                    info["upstream_matching_dyn_symbols"] = [
                        l
                        for l in dyn_lines
                        if any(
                            k in l
                            for k in (
                                "c_api_no_mangle",
                                "custom_c_export_sym",
                                "weak_c_hook",
                                "CUSTOM_SEC_VAL",
                                "upstream_instantiate_u32",
                                "rust_marked_noinline",
                                "generic_shared",
                                "generic_noinline",
                                "rust_metadata_upstream_",
                            )
                        )
                    ]
            part_a[ct] = info

        # Combined --crate-type=cdylib --crate-type=rlib join test
        comb_dir = tmp / "ct_cdylib_plus_rlib"
        comb_dir.mkdir()
        run(
            [
                rustc,
                "--edition=2024",
                "--crate-name=upstream",
                "--crate-type=cdylib",
                "--crate-type=rlib",
                "-C",
                "opt-level=2",
                "-C",
                "symbol-mangling-version=v0",
                "--out-dir",
                str(comb_dir),
                str(up_rs),
            ],
            env,
        )
        comb_so = comb_dir / "libupstream.so"
        comb_rlib = comb_dir / "libupstream.rlib"
        comb_dyn = [
            l.strip()
            for l in run(
                [tools["llvm-nm"], "-D", "--defined-only", str(comb_so)], env
            ).splitlines()
            if l.strip()
        ]
        comb_rlib_nm = run([tools["llvm-nm"], "--defined-only", str(comb_rlib)], env)
        comb_rlib_ar = parse_ar_tv(run([tools["llvm-ar"], "tv", str(comb_rlib)], env))
        part_a["combined_cdylib_and_rlib"] = {
            "cdylib_defined_dyn_symbol_count": len(comb_dyn),
            "cdylib_all_defined_dyn_symbols": comb_dyn,
            "cdylib_has_upstream_instantiate_u32": any(
                "upstream_instantiate_u32" in l for l in comb_dyn
            ),
            "rlib_has_lib_rmeta": any(m["name"] == "lib.rmeta" for m in comb_rlib_ar),
            "rlib_has_lib_rmeta_link": any(
                m["name"] == "lib.rmeta-link" for m in comb_rlib_ar
            ),
            "rlib_has_upstream_instantiate_u32_global": bool(
                re.search(r"\bT _R[^\n]*upstream_instantiate_u32$", comb_rlib_nm, re.M)
            ),
        }

        # Weak linkage override execution check
        assert rlib_for_weak is not None
        weak_bin = tmp / "weak_override_bin"
        run(
            [
                rustc,
                "--edition=2024",
                "--crate-type=bin",
                "-C",
                "opt-level=2",
                "--extern",
                f"upstream={rlib_for_weak}",
                "-o",
                str(weak_bin),
                str(weak_override_rs),
            ],
            env,
        )
        weak_stdout = run([str(weak_bin)], env).strip()
        part_a["weak_c_hook_strong_override_test"] = {
            "link_and_exec_ok": True,
            "stdout": weak_stdout,
            "expected": "1004:6:0x1122334455667788",
            "strong_override_won": weak_stdout == "1004:6:0x1122334455667788",
        }

        result["part_a_crate_types_and_symbol_export"] = part_a

        # ------------------------------------------------------------------
        # Part B: .rmeta should_encode_mir vs. cross_crate_inlinable matrix
        # ------------------------------------------------------------------
        part_b: dict[str, object] = {}
        mir_modes: list[tuple[str, list[str], list[str]]] = [
            ("default_non_incr", [], []),
            ("threshold_never", ["-Z", "cross-crate-inline-threshold=never"], []),
            ("incremental_default", ["-C", f"incremental={tmp}/incr_def"], []),
            (
                "incremental_always_encode_mir",
                ["-C", f"incremental={tmp}/incr_aem", "-Z", "always-encode-mir"],
                [],
            ),
            (
                "incremental_always_encode_mir_plus_ds_inline_mir",
                ["-C", f"incremental={tmp}/incr_aem2", "-Z", "always-encode-mir"],
                ["-Z", "inline-mir=yes", "-Z", "inline-mir-threshold=1000"],
            ),
            (
                "incremental_threshold_always",
                [
                    "-C",
                    f"incremental={tmp}/incr_ta",
                    "-Z",
                    "cross-crate-inline-threshold=always",
                ],
                [],
            ),
        ]
        for label, up_extra, ds_extra in mir_modes:
            mdir = tmp / f"mir_{label}"
            mdir.mkdir()
            up_rlib = mdir / "libupstream.rlib"
            run(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-name=upstream",
                    "--crate-type=rlib",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "symbol-mangling-version=v0",
                    *up_extra,
                    "-o",
                    str(up_rlib),
                    str(up_rs),
                ],
                env,
            )
            members = parse_ar_tv(run([tools["llvm-ar"], "tv", str(up_rlib)], env))
            rmeta_bytes = [
                m["size_bytes"] for m in members if m["name"] == "lib.rmeta"
            ][0]
            ds_ll = mdir / "ds_mir.ll"
            run(
                [
                    rustc,
                    "--edition=2024",
                    "--crate-name=ds_mir",
                    "--crate-type=rlib",
                    "--emit=llvm-ir",
                    "-C",
                    "opt-level=2",
                    "-C",
                    "symbol-mangling-version=v0",
                    *ds_extra,
                    "--extern",
                    f"upstream={up_rlib}",
                    "-o",
                    str(ds_ll),
                    str(ds_mir_rs),
                ],
                env,
            )
            ir = ds_ll.read_text()
            body_unmarked = extract_fn_ir(ir, "ds_call_unmarked")
            body_inline = extract_fn_ir(ir, "ds_call_marked_inline")
            body_noinline = extract_fn_ir(ir, "ds_call_marked_noinline")
            # Check whether rust_marked_noinline is defined locally or declared externally in ds_mir.ll
            noinline_decls = [
                l.strip()
                for l in ir.splitlines()
                if l.startswith(("define ", "declare "))
                and "rust_marked_noinline" in l
            ]
            part_b[label] = {
                "lib_rmeta_bytes": rmeta_bytes,
                "ds_call_unmarked_calls_external": (
                    "call " in body_unmarked or "invoke " in body_unmarked
                ),
                "ds_call_marked_inline_calls_external": (
                    "call " in body_inline or "invoke " in body_inline
                ),
                "ds_call_marked_noinline_calls_external": (
                    "call " in body_noinline or "invoke " in body_noinline
                ),
                "ds_rust_marked_noinline_decls_and_defs": noinline_decls,
                "ds_call_unmarked_ir_snippet": [
                    l.strip() for l in body_unmarked.splitlines() if l.strip()
                ],
                "ds_call_marked_inline_ir_snippet": [
                    l.strip() for l in body_inline.splitlines() if l.strip()
                ],
            }
        result["part_b_rmeta_should_encode_mir"] = part_b

        # ------------------------------------------------------------------
        # Part C: -Z share-generics=yes vs. no across -O0 and -O2
        # ------------------------------------------------------------------
        part_c: dict[str, object] = {}
        runtime_outputs: set[str] = set()
        for opt in ("0", "2"):
            for sg_flag in ("yes", "no"):
                key = f"O{opt}_share_generics_{sg_flag}"
                sdir = tmp / key
                sdir.mkdir()
                up_rlib = sdir / "libupstream.rlib"
                run(
                    [
                        rustc,
                        "--edition=2024",
                        "--crate-name=upstream",
                        "--crate-type=rlib",
                        f"-Copt-level={opt}",
                        "-Csymbol-mangling-version=v0",
                        f"-Zshare-generics={sg_flag}",
                        "-o",
                        str(up_rlib),
                        str(up_rs),
                    ],
                    env,
                )
                ds_ll = sdir / "ds.ll"
                run(
                    [
                        rustc,
                        "--edition=2024",
                        "--crate-name=ds",
                        "--crate-type=rlib",
                        "--emit=llvm-ir",
                        f"-Copt-level={opt}",
                        "-Csymbol-mangling-version=v0",
                        f"-Zshare-generics={sg_flag}",
                        "--extern",
                        f"upstream={up_rlib}",
                        "-o",
                        str(ds_ll),
                        str(ds_share_rs),
                    ],
                    env,
                )
                ir = ds_ll.read_text()
                gen_lines = [
                    l.strip()
                    for l in ir.splitlines()
                    if l.startswith(("define ", "declare "))
                    and (
                        "generic_shared" in l
                        or "generic_noinline" in l
                        or "generic_tiny_leaf" in l
                    )
                ]
                up_nm = [
                    l.strip()
                    for l in run(
                        [tools["llvm-nm"], "--defined-only", str(up_rlib)], env
                    ).splitlines()
                    if (
                        "generic_shared" in l
                        or "generic_noinline" in l
                        or "generic_tiny_leaf" in l
                    )
                ]

                def classify(sym_sub: str, type_code: str) -> dict[str, object]:
                    # In v0 mangling: u32 = 'm', u64 = 'y'
                    pat = f"{sym_sub}{type_code}E"
                    matched = [l for l in gen_lines if pat in l]
                    defined_ext = [
                        l
                        for l in matched
                        if l.startswith("define ") and not l.startswith("define internal ")
                    ]
                    defined_int = [
                        l for l in matched if l.startswith("define internal ")
                    ]
                    declared = [l for l in matched if l.startswith("declare ")]
                    return {
                        "defined_external": len(defined_ext),
                        "defined_internal": len(defined_int),
                        "declared_external": len(declared),
                        "ir_lines": matched,
                        "instantiating_crate_suffixes": [
                            extract_v0_instantiating_suffix(l) for l in matched
                        ],
                    }

                # Compile ds.rlib and link+run executable to prove link safety and runtime parity
                ds_rlib = sdir / "libds.rlib"
                run(
                    [
                        rustc,
                        "--edition=2024",
                        "--crate-name=ds",
                        "--crate-type=rlib",
                        f"-Copt-level={opt}",
                        "-Csymbol-mangling-version=v0",
                        f"-Zshare-generics={sg_flag}",
                        "--extern",
                        f"upstream={up_rlib}",
                        "-o",
                        str(ds_rlib),
                        str(ds_share_rs),
                    ],
                    env,
                )
                exe = sdir / "main_bin"
                run(
                    [
                        rustc,
                        "--edition=2024",
                        "--crate-type=bin",
                        f"-Copt-level={opt}",
                        "-Csymbol-mangling-version=v0",
                        f"-Zshare-generics={sg_flag}",
                        "-L",
                        f"dependency={sdir}",
                        "--extern",
                        f"upstream={up_rlib}",
                        "--extern",
                        f"ds={ds_rlib}",
                        "-o",
                        str(exe),
                        str(main_share_rs),
                    ],
                    env,
                )
                stdout = run([str(exe)], env).strip()
                runtime_outputs.add(stdout)

                part_c[key] = {
                    "upstream_rlib_generic_symbols": up_nm,
                    "generic_shared_u32": classify("14generic_shared", "m"),
                    "generic_noinline_u32": classify("16generic_noinline", "m"),
                    "generic_shared_u64": classify("14generic_shared", "y"),
                    "generic_noinline_u64": classify("16generic_noinline", "y"),
                    "generic_tiny_leaf_u32": classify("17generic_tiny_leaf", "m"),
                    "link_and_exec_ok": True,
                    "runtime_output": stdout,
                }
        part_c["all_modes_runtime_identical"] = len(runtime_outputs) == 1
        result["part_c_share_generics"] = part_c

    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, help="Optional JSON output path")
    args = parser.parse_args()
    data = run_probe()
    rendered = json.dumps(data, indent=2, sort_keys=False) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
