#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/LICENSE-2.0>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
import re
import subprocess
import tempfile

RUST_ROOT = "os.environ.get("RUST_1991_ROOT", ".")"
LLVM_ROOT = "/usr/local/google/home/joshlf/workspace/rust/src/llvm-project/llvm"
OUT_JSON = "/tmp/f3_xlto_metrics.json"
TMP_DIR = "/tmp"


def parse_llvm_instruction_def():
    inst_def = os.path.join(LLVM_ROOT, "include/llvm/IR/Instruction.def")
    categories = {
        "TERM_INST": [],
        "UNARY_INST": [],
        "BINARY_INST": [],
        "MEMORY_INST": [],
        "CAST_INST": [],
        "FUNCLET_PAD_INST": [],
        "OTHER_INST": [],
    }
    if os.path.exists(inst_def):
        with open(inst_def, "r", encoding="utf-8") as fh:
            for line in fh:
                for cat in categories:
                    m = re.match(rf"^\s*HANDLE_{cat}\s*\(\s*(\d+)\s*,\s*([A-Za-z0-9_]+)\s*,\s*([A-Za-z0-9_]+)\s*\)", line)
                    if m:
                        categories[cat].append({
                            "opcode": int(m.group(1)),
                            "name": m.group(2),
                            "class": m.group(3),
                        })
    total = sum(len(v) for v in categories.values())
    return {"total_opcodes": total, "categories": categories}


def find_toolchain_binaries():
    sysroot = subprocess.check_output(
        ["rustup", "run", "1.99.1-x86_64-unknown-linux-gnu", "rustc", "--print", "sysroot"],
        text=True,
    ).strip()
    llvm_bin = os.path.join(sysroot, "lib/rustlib/x86_64-unknown-linux-gnu/bin")
    rustc = os.path.join(sysroot, "bin/rustc")
    return sysroot, rustc, llvm_bin


def run_empirical_xlto_probe():
    os.makedirs(TMP_DIR, exist_ok=True)
    sysroot, rustc, llvm_bin = find_toolchain_binaries()
    bcanalyzer = os.path.join(llvm_bin, "llvm-bcanalyzer")
    llvm_dis = os.path.join(llvm_bin, "llvm-dis")
    llvm_nm = os.path.join(llvm_bin, "llvm-nm")
    llvm_lto2 = os.path.join(llvm_bin, "llvm-lto2")

    work = tempfile.mkdtemp(dir=TMP_DIR, prefix="xlto_probe_")
    rs_src = os.path.join(work, "ffi_math.rs")
    with open(rs_src, "w", encoding="utf-8") as fh:
        fh.write(
            """#![crate_type = "rlib"]
#![no_std]

unsafe extern "C" {
    fn c_scale_add(x: i32, scale: i32, bias: *const i32) -> i32;
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_compute(x: i32, bias: &i32) -> i32 {
    unsafe { c_scale_add(x, 4, bias as *const i32) + 1 }
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_leaf_add(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}
"""
        )

    # 1. Compile normal rlib vs -Clinker-plugin-lto rlib
    rlib_normal = os.path.join(work, "libffi_math_normal.rlib")
    rlib_xlto = os.path.join(work, "libffi_math_xlto.rlib")
    ir_out = os.path.join(work, "ffi_math.ll")
    bc_out = os.path.join(work, "ffi_math.bc")

    subprocess.run([rustc, "-O", rs_src, "-o", rlib_normal], check=True)
    subprocess.run([rustc, "-O", "-Clinker-plugin-lto", rs_src, "-o", rlib_xlto], check=True)
    subprocess.run([rustc, "-O", "--emit=llvm-ir", rs_src, "-o", ir_out], check=True)
    subprocess.run([rustc, "-O", "-Clinker-plugin-lto", "--emit=llvm-bc", rs_src, "-o", bc_out], check=True)

    # Inspect archive members of rlib_normal vs rlib_xlto
    ar_normal = subprocess.check_output(["ar", "t", rlib_normal], text=True).splitlines()
    ar_xlto = subprocess.check_output(["ar", "t", rlib_xlto], text=True).splitlines()

    # Extract members to inspect magic bytes
    norm_dir = os.path.join(work, "norm_extract")
    xlto_dir = os.path.join(work, "xlto_extract")
    os.makedirs(norm_dir, exist_ok=True)
    os.makedirs(xlto_dir, exist_ok=True)
    subprocess.run(["ar", "x", rlib_normal], cwd=norm_dir, check=True)
    subprocess.run(["ar", "x", rlib_xlto], cwd=xlto_dir, check=True)

    def member_magic(d):
        res = {}
        for f in sorted(os.listdir(d)):
            p = os.path.join(d, f)
            with open(p, "rb") as fh:
                hdr = fh.read(8)
            res[f] = {
                "size_bytes": os.path.getsize(p),
                "magic_hex": hdr.hex(),
                "is_elf": hdr.startswith(b"\x7fELF"),
                "is_raw_bitcode": hdr.startswith(b"BC\xc0\xde"),
            }
        return res

    norm_members = member_magic(norm_dir)
    xlto_members = member_magic(xlto_dir)

    # Run llvm-bcanalyzer on the bitcode object from xlto_dir
    bcanalyzer_summary = ""
    for f, meta in xlto_members.items():
        if meta["is_raw_bitcode"] and os.path.exists(bcanalyzer):
            bcanalyzer_summary = subprocess.check_output(
                [bcanalyzer, "--dump", os.path.join(xlto_dir, f)],
                text=True,
                stderr=subprocess.STDOUT,
            )
            break

    with open(ir_out, "r", encoding="utf-8") as fh:
        rust_ir_text = fh.read()

    # Check if clang is available on host to compare clang -O2 -flto=thin IR/bitcode
    clang_info = {"available": False}
    clang_bin = None
    for cand in ["clang", "clang-19", "clang-18", "clang-17"]:
        r = subprocess.run(["which", cand], capture_output=True, text=True)
        if r.returncode == 0:
            clang_bin = r.stdout.strip()
            break
    if clang_bin:
        c_src = os.path.join(work, "c_scale.c")
        c_ll = os.path.join(work, "c_scale.ll")
        with open(c_src, "w", encoding="utf-8") as fh:
            fh.write(
                """#include <stdint.h>
extern int32_t rust_leaf_add(int32_t a, int32_t b);
int32_t c_scale_add(int32_t x, int32_t scale, const int32_t *bias) {
    return rust_leaf_add(x * scale, *bias);
}
"""
            )
        ver = subprocess.check_output([clang_bin, "--version"], text=True).splitlines()[0]
        subprocess.run([clang_bin, "-O2", "-flto=thin", "-S", "-emit-llvm", c_src, "-o", c_ll], check=True)
        with open(c_ll, "r", encoding="utf-8") as fh:
            c_ir_text = fh.read()
        clang_info = {
            "available": True,
            "clang_version": ver,
            "has_tbaa_metadata": "!tbaa" in c_ir_text,
            "has_nsw_flag": "nsw" in c_ir_text,
            "has_mustprogress": "mustprogress" in c_ir_text,
            "c_ir_snippet": c_ir_text,
        }

    # Extract top-level blocks from bcanalyzer output
    bc_blocks = re.findall(r"<([A-Z0-9_]+)\s+NumWords=\d+", bcanalyzer_summary)

    return {
        "rustc_sysroot": sysroot,
        "normal_rlib_members": norm_members,
        "linker_plugin_lto_rlib_members": xlto_members,
        "bitcode_top_blocks": sorted(list(set(bc_blocks))),
        "bcanalyzer_head": "\n".join(bcanalyzer_summary.splitlines()[:45]),
        "rust_ir_snippet": rust_ir_text,
        "clang_comparison": clang_info,
    }


def main():
    inst_data = parse_llvm_instruction_def()
    probe_data = run_empirical_xlto_probe()
    out = {
        "llvm_23_1_1_instruction_def": inst_data,
        "empirical_probe": probe_data,
    }
    with open(OUT_JSON, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=2)
    print("Wrote", OUT_JSON)
    print("LLVM 23.1.1 total opcodes:", inst_data["total_opcodes"])
    for k, v in inst_data["categories"].items():
        print(f"  {k}: {len(v)} ({', '.join(x['name'] for x in v[:6])}...)")
    print("Normal rlib members:", probe_data["normal_rlib_members"])
    print("XLTO rlib members:", probe_data["linker_plugin_lto_rlib_members"])
    print("Bitcode blocks:", probe_data["bitcode_top_blocks"])
    print("Clang available:", probe_data["clang_comparison"]["available"])


if __name__ == "__main__":
    main()
