#!/usr/bin/env python3
"""Standalone empirical probe for rustc scalable vectors, next-solver DUMMY_SP
tuple WF bypass, AArch64 SVE stack-smashing codegen/QEMU execution, RISC-V RVV
debuginfo ICE, and autodiff/offload codegen gates.

Runs exclusively real rustc (and optional qemu-aarch64 + bundled llvm-objdump)
invocations inside a temporary directory and scrubs host-local paths and
compiler source build-SHA paths from all emitted JSON records.
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
from typing import Any

PATH_SHA_RE = re.compile(r"/rustc-" + r"dev/[0-9a-f]{40}/")


def scrub_text(text: str, tmpdir: str, home: str) -> str:
    """Remove host-local paths, usernames, and compiler source build-SHA paths."""
    out = text.replace(tmpdir, "<TMP>")
    if home:
        out = out.replace(home, "<HOME>")
    out = PATH_SHA_RE.sub("<RUSTC_SRC>/", out)
    # Scrub any remaining user-directory prefixes dynamically without hardcoding them
    user_root = os.path.dirname(home) if home else ""
    if user_root and user_root != "/":
        out = re.sub(re.escape(user_root) + r"/[^/\s'\"]+/", "<HOME>/", out)
    return out


def find_tool(name: str, extra_dirs: list[str]) -> str | None:
    for d in extra_dirs:
        cand = os.path.join(d, name)
        if os.path.isfile(cand) and os.access(cand, os.X_OK):
            return cand
    return shutil.which(name)


def run_rustc_case(
    rustc: str,
    src: str,
    args: list[str],
    filename: str,
    emit_ir: bool = False,
    emit_asm: bool = False,
    crate_type: str = "lib",
) -> dict[str, Any]:
    home = os.path.expanduser("~")
    with tempfile.TemporaryDirectory() as td:
        src_path = os.path.join(td, filename)
        with open(src_path, "w", encoding="utf-8") as f:
            f.write(src)
        cmd = [rustc, src_path, f"--crate-type={crate_type}", "--out-dir", td] + args
        if emit_ir:
            cmd.append("--emit=llvm-ir")
        if emit_asm:
            cmd.append("--emit=asm")
        env = dict(os.environ)
        env["RUSTC_ICE"] = "0"
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
        stderr_clean = scrub_text(proc.stderr, td, home)
        is_ice = (
            proc.returncode == 101
            or "internal compiler error" in proc.stderr
            or "panicked at" in proc.stderr
        )
        stem = os.path.splitext(filename)[0]
        ir_excerpt: list[str] = []
        if emit_ir:
            ll_path = os.path.join(td, f"{stem}.ll")
            if os.path.exists(ll_path):
                ll_text = open(ll_path, encoding="utf-8").read()
                for line in ll_text.splitlines():
                    s = line.strip()
                    if any(
                        tok in s
                        for tok in (
                            "define ",
                            "alloca ",
                            "store <vscale",
                            "load <vscale",
                            "ret i64 ",
                            "store i64 17",
                            "DIFlagVector",
                            "DISubrange",
                            "DW_OP_bregx",
                        )
                    ):
                        ir_excerpt.append(scrub_text(s[:220], td, home))
        asm_excerpt: list[str] = []
        if emit_asm:
            asm_path = os.path.join(td, f"{stem}.s")
            if os.path.exists(asm_path):
                asm_text = open(asm_path, encoding="utf-8").read()
                for line in asm_text.splitlines():
                    s = line.strip()
                    if (
                        s.endswith(":")
                        and not s.startswith(".")
                        or any(
                            op in s
                            for op in (
                                "sub\tsp",
                                "add\tsp",
                                "stp\tx29",
                                "ldp\tx29",
                                "str\tz",
                                "ldr\tz",
                                "str\tx9",
                                "ldr\tx0",
                                "ldrb\tw0",
                                "mov\tz0",
                                "bl\t",
                                "ret",
                            )
                        )
                    ):
                        asm_excerpt.append(line.rstrip())
        stderr_lines = stderr_clean.splitlines()
        # Keep concise head up to first 24 lines (preserving panic header + location)
        stderr_head = "\n".join(stderr_lines[:24])
        if stderr_lines:
            stderr_head += "\n"
        return {
            "rc": proc.returncode,
            "is_ice": is_ice,
            "stderr_head": stderr_head,
            "llvm_ir_excerpt": ir_excerpt[:20],
            "asm_excerpt": asm_excerpt[:40],
        }


NOCORE_HEADER = """#![feature(no_core, lang_items, rustc_attrs, intrinsics)]
#![no_core]
#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] unsafe trait Freeze {}
impl Copy for u32 {}
impl Copy for u64 {}
impl Copy for i32 {}
impl Copy for usize {}
#[rustc_scalable_vector(4)]
pub struct SvU32(u32);
impl Copy for SvU32 {}
"""

NOSTD_SVE_HEADER = """#![feature(rustc_attrs)]
#![no_std]
#[rustc_scalable_vector(4)]
#[derive(Copy, Clone)]
pub struct SvU32(u32);
"""

AARCH64_SVE_ELF_SRC = r"""#![feature(rustc_attrs, link_llvm_intrinsics, simd_ffi)]
#![no_std]
#![no_main]

use core::arch::asm;

#[rustc_scalable_vector(4)]
#[derive(Copy, Clone)]
pub struct SvU32(u32);

unsafe extern "C" {
    #[link_name = "llvm.aarch64.sve.dup.x.nxv4i32"]
    fn sv_dup_u32(x: u32) -> SvU32;
}

pub struct GenericPair<T> {
    pub first: T,
    pub canary: u64,
}

#[inline(never)]
pub fn overwrite_first_safely<T>(p: &mut GenericPair<T>, v: T) {
    p.first = v;
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn run_test() -> u64 {
    let z0 = unsafe { sv_dup_u32(0) };
    let z42 = unsafe { sv_dup_u32(42) };
    let mut pair = GenericPair { first: z0, canary: 17 };
    overwrite_first_safely(&mut pair, z42);
    pair.canary & 0xff
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    let code = run_test();
    unsafe {
        asm!(
            "mov x8, #94",
            "svc #0",
            in("x0") code,
            options(noreturn),
        );
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
"""


def probe_sve_elf_and_qemu(rustc: str, sysroot: str) -> dict[str, Any]:
    home = os.path.expanduser("~")
    host_bin = os.path.join(sysroot, "lib", "rustlib", "x86_64-unknown-linux-gnu", "bin")
    ld_lld = os.path.join(host_bin, "gcc-ld", "ld.lld")
    llvm_objdump = os.path.join(host_bin, "llvm-objdump")
    qemu = shutil.which("qemu-aarch64") or shutil.which("qemu-aarch64-static")

    result: dict[str, Any] = {
        "static_elf_build_rc": None,
        "disassembly": [],
        "qemu_aarch64_available": qemu is not None,
        "qemu_version": None,
        "qemu_runs": {},
    }
    if qemu is not None:
        qv = subprocess.run([qemu, "--version"], capture_output=True, text=True)
        result["qemu_version"] = (qv.stdout.splitlines() or [""])[0].strip()

    if not os.path.isfile(ld_lld):
        result["error"] = "bundled ld.lld not found in rustc sysroot"
        return result

    with tempfile.TemporaryDirectory() as td:
        rs = os.path.join(td, "sve_smash.rs")
        elf = os.path.join(td, "sve_smash")
        with open(rs, "w", encoding="utf-8") as f:
            f.write(AARCH64_SVE_ELF_SRC)
        cmd = [
            rustc,
            rs,
            "--target=aarch64-unknown-linux-gnu",
            "-C",
            "target-feature=+sve",
            "-C",
            "opt-level=2",
            "-C",
            "panic=abort",
            "-C",
            f"linker={ld_lld}",
            "-C",
            "linker-flavor=ld",
            "-C",
            "relocation-model=static",
            "-C",
            "link-arg=-e_start",
            "-C",
            "link-arg=-static",
            "-o",
            elf,
        ]
        env = dict(os.environ)
        env["RUSTC_ICE"] = "0"
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
        result["static_elf_build_rc"] = proc.returncode
        if proc.returncode != 0:
            result["build_stderr"] = scrub_text(proc.stderr, td, home)
            return result

        if os.path.isfile(llvm_objdump):
            od = subprocess.run(
                [llvm_objdump, "-d", "--mattr=+sve", elf],
                capture_output=True,
                text=True,
            )
            result["disassembly"] = [
                scrub_text(line.rstrip(), td, home)
                for line in od.stdout.splitlines()
                if line.strip()
            ]

        if qemu is not None:
            configs = [
                ("sve_128_vscale_1", "max,sve128=on,sve256=off,sve512=off", 16),
                ("sve_256_vscale_2", "max,sve128=on,sve256=on,sve512=off", 32),
                ("sve_512_vscale_4", "max,sve128=on,sve256=on,sve512=on", 64),
            ]
            for name, cpu_arg, vec_bytes in configs:
                qr = subprocess.run(
                    [qemu, "-cpu", cpu_arg, elf],
                    capture_output=True,
                    text=True,
                )
                result["qemu_runs"][name] = {
                    "cpu_flag": cpu_arg,
                    "hardware_vector_bytes": vec_bytes,
                    "ctfe_size_of_svu32": 16,
                    "exit_code": qr.returncode,
                    "expected_uncorrupted_canary": 17,
                    "stderr": scrub_text(qr.stderr.strip(), td, home),
                }
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=shutil.which("rustc") or "rustc")
    parser.add_argument("--out", default="-", help="Output JSON path or '-' for stdout")
    args = parser.parse_args()

    rustc = args.rustc
    ver_proc = subprocess.run([rustc, "--version", "--verbose"], capture_output=True, text=True)
    if ver_proc.returncode != 0:
        print(f"failed to invoke {rustc}: {ver_proc.stderr}", file=sys.stderr)
        return 1
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()

    aarch64_sve = ["--target=aarch64-unknown-linux-gnu", "-C", "target-feature=+sve"]
    rv64_v = ["--target=riscv64gc-unknown-linux-gnu", "-C", "target-feature=+v"]
    rv32_v = ["--target=riscv32imac-unknown-none-elf", "-C", "target-feature=+v"]

    checks: dict[str, Any] = {}

    # 1. Direct ADT & architecture checks
    checks["direct_struct_field_rejected"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub struct BadStruct { pub v: SvU32, pub x: u64 }\n",
        aarch64_sve,
        "direct_struct.rs",
    )
    checks["direct_enum_field_rejected"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub enum BadEnum { A(SvU32), B(u64) }\n",
        aarch64_sve,
        "direct_enum.rs",
    )
    checks["direct_union_field_rejected"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub union BadUnion { pub v: SvU32, pub x: u64 }\n",
        aarch64_sve,
        "direct_union.rs",
    )
    checks["x86_64_arch_rejected"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn id(v: SvU32) -> SvU32 { v }\n",
        ["--target=x86_64-unknown-linux-gnu"],
        "x86_64_rejected.rs",
    )

    # 2. Solver matrix: -Znext-solver=no vs -Znext-solver=globally (and default)
    checks["direct_tuple_default_solver"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn bad_tup(v: SvU32) -> (SvU32, u64) { (v, 1) }\n",
        aarch64_sve,
        "direct_tuple_default.rs",
        emit_ir=True,
    )
    checks["direct_tuple_old_solver_no"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn bad_tup(v: SvU32) -> (SvU32, u64) { (v, 1) }\n",
        aarch64_sve + ["-Znext-solver=no"],
        "direct_tuple_old.rs",
        emit_ir=True,
    )
    checks["direct_tuple_next_solver_globally_dummysp_bypass"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn bad_tup(v: SvU32) -> (SvU32, u64) { (v, 1) }\n",
        aarch64_sve + ["-Znext-solver=globally"],
        "direct_tuple_next.rs",
        emit_ir=True,
    )
    checks["direct_array_old_solver_no_bypass"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn direct_arr(a: SvU32, b: SvU32) -> [SvU32; 2] { [a, b] }\n",
        aarch64_sve + ["-Znext-solver=no"],
        "direct_array_old.rs",
        emit_ir=True,
    )
    checks["direct_array_next_solver_globally_bypass"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn direct_arr(a: SvU32, b: SvU32) -> [SvU32; 2] { [a, b] }\n",
        aarch64_sve + ["-Znext-solver=globally"],
        "direct_array_next.rs",
        emit_ir=True,
    )

    # 3. Generic WF bypasses & closure captures (both solvers)
    checks["generic_struct_old_solver_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "pub struct GenericPair<T> { pub first: T, pub canary: u64 }\n"
        + "pub fn bypass_struct(v: SvU32) -> GenericPair<SvU32> { GenericPair { first: v, canary: 17 } }\n",
        aarch64_sve + ["-Znext-solver=no"],
        "generic_struct_old.rs",
        emit_ir=True,
    )
    checks["generic_struct_next_solver_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "pub struct GenericPair<T> { pub first: T, pub canary: u64 }\n"
        + "pub fn bypass_struct(v: SvU32) -> GenericPair<SvU32> { GenericPair { first: v, canary: 17 } }\n",
        aarch64_sve + ["-Znext-solver=globally"],
        "generic_struct_next.rs",
        emit_ir=True,
    )
    checks["generic_enum_and_union_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "pub enum GenericEnum<T> { A(T), B(u64) }\n"
        + "pub union GenericUnion<T: Copy> { pub a: T, pub b: u64 }\n"
        + "#[unsafe(no_mangle)] pub fn mk_enum(v: SvU32) -> GenericEnum<SvU32> { GenericEnum::A(v) }\n"
        + "#[unsafe(no_mangle)] pub fn mk_union(v: SvU32) -> GenericUnion<SvU32> { GenericUnion { a: v } }\n",
        aarch64_sve,
        "generic_enum_union.rs",
        emit_ir=True,
    )
    checks["generic_tuple_old_solver_no"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "#[inline(never)] fn mk_pair<T>(a: T, b: u64) -> (T, u64) { (a, b) }\n"
        + "pub fn bypass_tuple(v: SvU32) -> u64 { mk_pair(v, 7).1 }\n",
        aarch64_sve + ["-Znext-solver=no"],
        "generic_tuple_old.rs",
        emit_ir=True,
    )
    checks["generic_tuple_next_solver_globally_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "#[inline(never)] fn mk_pair<T>(a: T, b: u64) -> (T, u64) { (a, b) }\n"
        + "pub fn bypass_tuple(v: SvU32) -> u64 { mk_pair(v, 7).1 }\n",
        aarch64_sve + ["-Znext-solver=globally"],
        "generic_tuple_next.rs",
        emit_ir=True,
    )
    checks["generic_array_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "#[inline(never)] fn mk_arr<T>(a: T, b: T) -> [T; 2] { [a, b] }\n"
        + "pub fn bypass_array(a: SvU32, b: SvU32) -> [SvU32; 2] { mk_arr(a, b) }\n",
        aarch64_sve,
        "generic_array.rs",
        emit_ir=True,
    )
    checks["closure_capture_old_solver_no"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "#[inline(never)] fn run_fn<F: FnOnce() -> u64>(f: F) -> u64 { f() }\n"
        + "pub fn bypass_closure(v: SvU32, canary: u64) -> u64 { run_fn(move || { let _ = v; canary }) }\n",
        aarch64_sve + ["-Znext-solver=no"],
        "closure_old.rs",
        emit_ir=True,
    )
    checks["closure_capture_next_solver_globally_bypass"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "#[inline(never)] fn run_fn<F: FnOnce() -> u64>(f: F) -> u64 { f() }\n"
        + "pub fn bypass_closure(v: SvU32, canary: u64) -> u64 { run_fn(move || { let _ = v; canary }) }\n",
        aarch64_sve + ["-Znext-solver=globally"],
        "closure_next.rs",
        emit_ir=True,
    )

    # 4. CTFE layout sizes & offsets (vscale = 1 illusion)
    checks["ctfe_layout_sizes_and_offsets"] = run_rustc_case(
        rustc,
        NOSTD_SVE_HEADER
        + "pub struct GenericPair<T> { pub first: T, pub canary: u64 }\n"
        + "#[unsafe(no_mangle)] pub fn sz_sv() -> usize { core::mem::size_of::<SvU32>() }\n"
        + "#[unsafe(no_mangle)] pub fn al_sv() -> usize { core::mem::align_of::<SvU32>() }\n"
        + "#[unsafe(no_mangle)] pub fn sz_pair() -> usize { core::mem::size_of::<GenericPair<SvU32>>() }\n"
        + "#[unsafe(no_mangle)] pub fn off_canary() -> usize { core::mem::offset_of!(GenericPair<SvU32>, canary) }\n"
        + "#[unsafe(no_mangle)] pub fn layout_sz() -> usize { core::alloc::Layout::new::<SvU32>().size() }\n",
        aarch64_sve + ["-C", "opt-level=1", "-Z", "merge-functions=disabled"],
        "ctfe_sizes.rs",
        emit_ir=True,
    )

    # 5. Multi-vector containers (x1, x2, x7, x8, x9)
    for count in (1, 2, 7, 8, 9):
        fields = ", ".join(["SvU32"] * count)
        src = (
            NOSTD_SVE_HEADER
            + f"#[rustc_scalable_vector]\npub struct SvU32x{count}({fields});\n"
            + (f"pub fn id{count}(x: SvU32x{count}) -> SvU32x{count} {{ x }}\n" if count <= 8 else "")
        )
        checks[f"multi_vector_x{count}"] = run_rustc_case(
            rustc, src, aarch64_sve, f"multi_vec_x{count}.rs", emit_ir=(count <= 8)
        )

    # 6. Debuginfo: AArch64 SVE (normal + count=1 truncation + bool) vs RISC-V RVV ICE
    checks["aarch64_sve_debuginfo2_ok"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn id_sve(v: SvU32) -> SvU32 { v }\n",
        aarch64_sve + ["-C", "debuginfo=2"],
        "aarch64_dbg2.rs",
        emit_ir=True,
    )
    checks["aarch64_sve_debuginfo2_count1_div2_zero"] = run_rustc_case(
        rustc,
        "#![feature(rustc_attrs)]\n#![no_std]\n#[rustc_scalable_vector(1)]\n#[derive(Copy, Clone)]\npub struct SvU64_1(u64);\n#[unsafe(no_mangle)] pub fn id_c1(v: SvU64_1) -> SvU64_1 { v }\n",
        aarch64_sve + ["-C", "debuginfo=2"],
        "aarch64_dbg2_c1.rs",
        emit_ir=True,
    )
    checks["riscv64_rvv_debuginfo0_ok"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn id_rv(v: SvU32) -> SvU32 { v }\n",
        rv64_v + ["-C", "debuginfo=0"],
        "rv64_d0.rs",
        emit_ir=True,
    )
    checks["riscv64_rvv_debuginfo2_live_ice"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn id_rv(v: SvU32) -> SvU32 { v }\n",
        rv64_v + ["-C", "debuginfo=2"],
        "rv64_d2.rs",
    )
    checks["riscv32_rvv_debuginfo2_live_ice"] = run_rustc_case(
        rustc,
        NOCORE_HEADER + "pub fn id_rv32(v: SvU32) -> SvU32 { v }\n",
        rv32_v + ["-C", "debuginfo=2"],
        "rv32_d2.rs",
    )

    # 7. Autodiff & Offload codegen gates
    autodiff_src = (
        "#![feature(autodiff)]\n"
        "use std::autodiff::autodiff_reverse;\n"
        "#[autodiff_reverse(df, Duplicated, Active)]\n"
        "pub fn f(x: &f64) -> f64 { *x * *x }\n"
    )
    autodiff_offload: dict[str, Any] = {
        "autodiff_without_z_flag": run_rustc_case(
            rustc, autodiff_src, ["-C", "lto=fat"], "autodiff_no_z.rs"
        ),
        "autodiff_with_z_enable_missing_enzyme": run_rustc_case(
            rustc, autodiff_src, ["-Z", "autodiff=Enable", "-C", "lto=fat"], "autodiff_z_enable.rs"
        ),
    }
    # Offload signature changed from 5 args (1.98) to 6 args (1.102+ adding device_id: i32)
    offload_6arg = (
        "#![feature(core_intrinsics)]\n"
        "pub fn k(_x: *mut f64) {}\n"
        "pub fn run(x: *mut f64) {\n"
        "    core::intrinsics::offload::<_, _, ()>(k, [1, 1, 1], [1, 1, 1], 0, -1, (x,));\n"
        "}\n"
    )
    offload_5arg = (
        "#![feature(core_intrinsics)]\n"
        "pub fn k(_x: *mut f64) {}\n"
        "pub fn run(x: *mut f64) {\n"
        "    core::intrinsics::offload::<_, _, ()>(k, [1, 1, 1], [1, 1, 1], 0, (x,));\n"
        "}\n"
    )
    r6 = run_rustc_case(rustc, offload_6arg, [], "offload_6arg.rs")
    if "takes 5 arguments" in r6["stderr_head"]:
        autodiff_offload["offload_safe_intrinsic_missing_enable_and_fat_lto"] = run_rustc_case(
            rustc, offload_5arg, [], "offload_5arg.rs"
        )
        autodiff_offload["offload_arity_detected"] = 5
    else:
        autodiff_offload["offload_safe_intrinsic_missing_enable_and_fat_lto"] = r6
        autodiff_offload["offload_arity_detected"] = 6

    sve_elf_qemu = probe_sve_elf_and_qemu(rustc, sysroot)

    payload = {
        "rustc_version": ver_proc.stdout.strip(),
        "scalable_vector_checks": checks,
        "aarch64_sve_elf_and_qemu": sve_elf_qemu,
        "autodiff_and_offload": autodiff_offload,
    }

    text = json.dumps(payload, indent=2, ensure_ascii=True) + "\n"
    if args.out == "-":
        sys.stdout.write(text)
    else:
        Path(args.out).write_text(text, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
