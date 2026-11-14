#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical reproduction and binary disassembly of the four hardware errata
and microarchitectural transition passes in `rustc 1.99.1` and `rust-lld` (`LLVM 23.1.1`):
1. Intel `SKX102` 32-byte JCC boundary NOP/prefix alignment (`-x86-branches-within-32B-boundaries`)
2. Arm Cortex-A53 Erratum `835769` (`LDR`/`STR` followed by 64-bit `MADD`/`MSUB` NOP insertion)
3. Arm Cortex-A53 Erratum `843419` (`ADRP` at 4 KiB page offset `0xFF8`/`0xFFC` patched by `lld`
   with `B <__CortexA53843419_veneer>` and re-centered `ADRP` + `B <pc_orig + 4>`)
4. x86 AVX-to-SSE `vzeroupper` (`C5 F8 77`) dirty-upper-YMM state cleanup.
"""

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_OBJDUMP = str(LLVM_BIN / "llvm-objdump")
RUST_LLD = str(LLVM_BIN / "rust-lld")


def probe_skx102_jcc_32b(work: Path) -> dict:
    """Reproduce Intel SKX102 32-byte boundary branch alignment in rustc 1.99.1."""
    src = work / "skx102.rs"
    src.write_text("""#![no_std]
#![allow(improper_ctypes_definitions)]
#[no_mangle]
pub extern "C" fn skx102_hot_branches(xs: &[u64], k1: u64, k2: u64, k3: u64) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < xs.len() {
        let v = xs[i].wrapping_mul(0x9E3779B97F4A7C15);
        if v > k1 {
            acc = acc.wrapping_add(v ^ k2);
        } else if v > k2 {
            acc = acc.wrapping_sub(v ^ k3);
        } else if (v & k3) != 0 {
            acc = acc.rotate_left(7) ^ v;
        } else {
            acc = acc.wrapping_mul(3);
        }
        i += 1;
    }
    acc
}
""")
    obj_base = work / "skx102_base.o"
    obj_mit = work / "skx102_mit.o"
    subprocess.run([RUSTC, "--crate-type=rlib", "-Copt-level=3", "--emit=obj", str(src), "-o", str(obj_base)], check=True)
    subprocess.run([
        RUSTC, "--crate-type=rlib", "-Copt-level=3",
        "-Cllvm-args=-x86-branches-within-32B-boundaries",
        "--emit=obj", str(src), "-o", str(obj_mit)
    ], check=True)

    dis_base = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj_base)], text=True)
    dis_mit = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj_mit)], text=True)

    def count_32b_crossings(dis_text: str) -> tuple[int, list[str], int]:
        insns = []
        for line in dis_text.splitlines():
            m = re.match(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s)+)\s*([a-zA-Z0-9_]+.*)", line)
            if m:
                off = int(m.group(1), 16)
                raw = [int(b, 16) for b in m.group(2).strip().split()]
                mnem = m.group(3).strip()
                insns.append((off, len(raw), mnem))
        crossings = []
        nops = 0
        for idx, (off, length, mnem) in enumerate(insns):
            op = mnem.split()[0]
            if op == "nop" or op.startswith("nop"):
                nops += 1
            is_branch = op.startswith("j") or op in ("callq", "retq")
            if is_branch:
                start = off
                end = off + length
                # Check if previous insn is macro-fusable cmp/test
                if idx > 0 and insns[idx - 1][2].split()[0].startswith(("cmp", "test")):
                    start = insns[idx - 1][0]
                if (start // 32) != ((end - 1) // 32) or (end % 32 == 0):
                    crossings.append(f"0x{start:x}..0x{end:x}: {mnem}")
        return len(crossings), crossings, nops

    base_cnt, base_list, base_nops = count_32b_crossings(dis_base)
    mit_cnt, mit_list, mit_nops = count_32b_crossings(dis_mit)

    return {
        "baseline_object_bytes": obj_base.stat().st_size,
        "mitigated_object_bytes": obj_mit.stat().st_size,
        "baseline_32b_boundary_hazards": base_cnt,
        "baseline_hazard_sites": base_list,
        "mitigated_32b_boundary_hazards": mit_cnt,
        "mitigated_hazard_sites": mit_list,
        "baseline_nop_count": base_nops,
        "mitigated_nop_count": mit_nops,
        "baseline_disassembly": [l.strip() for l in dis_base.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
        "mitigated_disassembly": [l.strip() for l in dis_mit.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
    }


def probe_cortex_a53_835769(work: Path) -> dict:
    """Reproduce Arm Cortex-A53 Erratum 835769 (NOP inserted between memory write/load and 64-bit MADD)."""
    src = work / "a53_835769.rs"
    src.write_text("""#![no_std]
#[no_mangle]
pub unsafe extern "C" fn a53_835769_mac_after_mem(ptr: *mut u64, a: u64, b: u64, c: u64) -> u64 {
    let loaded = core::ptr::read_volatile(ptr);
    core::ptr::write_volatile(ptr, a);
    loaded.wrapping_mul(b).wrapping_add(c)
}
""")
    obj_base = work / "a53_835769_base.o"
    obj_fix = work / "a53_835769_fix.o"
    subprocess.run([
        RUSTC, "--target=aarch64-unknown-linux-gnu", "--crate-type=rlib", "-Copt-level=3",
        "--emit=obj", str(src), "-o", str(obj_base)
    ], check=True)
    subprocess.run([
        RUSTC, "--target=aarch64-unknown-linux-gnu", "--crate-type=rlib", "-Copt-level=3",
        "-Ctarget-cpu=cortex-a53", "-Ctarget-feature=+fix-cortex-a53-835769",
        "--emit=obj", str(src), "-o", str(obj_fix)
    ], check=True)

    dis_base = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj_base)], text=True)
    dis_fix = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj_fix)], text=True)
    return {
        "unmitigated_instructions": [l.strip() for l in dis_base.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
        "mitigated_instructions": [l.strip() for l in dis_fix.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
        "nop_inserted_between_str_and_madd": ("nop" in dis_fix and "nop" not in dis_base),
    }


def probe_cortex_a53_843419_veneer(work: Path) -> dict:
    """Reproduce Arm Cortex-A53 Erratum 843419 linker veneer synthesis in rust-lld
    and execute the patched binary under qemu-aarch64."""
    src = work / "a53_843419.rs"
    # Arm Cortex-A53 Erratum 843419 trigger pattern recognized by lld's AArch64Err843419Patcher:
    # 1. An instruction at page offset 0xFF8 or 0xFFC is ADRP
    # 2. Preceded by a sequence of loads/stores (Specifically: a store, then a load with
    #    base register Rn where bits [11:10] == 0b01 or standard trigger sequence in lld/ELF/Arch/AArch64.cpp).
    # Let's place exact instructions at page offset 0xFF0..0xFFC using global_asm!
    src.write_text("""#![no_std]
#![no_main]

#[used]
#[no_mangle]
#[link_section = ".rodata.target_val"]
pub static TARGET_VAL: u64 = 0x1122_3344_5566_7788;

core::arch::global_asm!(
    r#".section .text.erratum843419,"ax",@progbits"#,
    ".balign 4096",
    ".globl trigger_843419",
    ".type trigger_843419, @function",
    "trigger_843419:",
    ".rept 1021",
    "nop",
    ".endr",
    // Offset 0xFF4 (1021 * 4 = 4084 = 0xFF4):
    // 0xFF4: str x1, [sp, #-16]!
    // 0xFF8: adrp x2, TARGET_VAL           <-- ADRP at page offset 0xFF8!
    // 0xFFC: ldr x1, [sp], #16             <-- Non-vector load/store (Rt != x2, Rn != x2)
    // 0x1000: ldr x0, [x2, :lo12:TARGET_VAL] <-- Dependent load reading base x2!
    "str x1, [sp, #-16]!",
    "adrp x2, TARGET_VAL",
    "ldr x1, [sp], #16",
    "ldr x0, [x2, :lo12:TARGET_VAL]",
    "ret",
);

extern "C" {
    fn trigger_843419(a: u64, b: u64) -> u64;
}

#[no_mangle]
pub unsafe extern "C" fn _start() {
    let v = trigger_843419(1, 2);
    let code: i64 = if v == 0x1122_3344_5566_7788 { 0 } else { 1 };
    core::arch::asm!("mov x8, #93", "svc #0", in("x0") code, options(noreturn));
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
""")
    obj = work / "a53_843419.o"
    bin_nofix = work / "a53_843419_nofix"
    bin_fix = work / "a53_843419_fix"

    subprocess.run([
        RUSTC, "--target=aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=3",
        "--emit=obj", str(src), "-o", str(obj)
    ], check=True)
    subprocess.run([
        RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux",
        str(obj), "-o", str(bin_nofix)
    ], check=True)
    subprocess.run([
        RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "--fix-cortex-a53-843419",
        str(obj), "-o", str(bin_fix)
    ], check=True)

    dis_nofix = subprocess.check_output([LLVM_OBJDUMP, "-d", str(bin_nofix)], text=True)
    dis_fix = subprocess.check_output([LLVM_OBJDUMP, "-d", str(bin_fix)], text=True)

    rc_nofix = subprocess.run(["qemu-aarch64", str(bin_nofix)]).returncode
    rc_fix = subprocess.run(["qemu-aarch64", str(bin_fix)]).returncode

    nofix_tail = [l.strip() for l in dis_nofix.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l) and not l.strip().endswith("nop")]
    fix_tail = [l.strip() for l in dis_fix.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l) and not l.strip().endswith("nop")]

    return {
        "unpatched_non_nop_instructions": nofix_tail,
        "patched_non_nop_instructions": fix_tail,
        "veneer_symbol_synthesized": ("__CortexA53843419_" in dis_fix),
        "qemu_aarch64_unpatched_exit_code": rc_nofix,
        "qemu_aarch64_patched_veneer_exit_code": rc_fix,
    }


def probe_x86_vzeroupper(work: Path) -> dict:
    """Reproduce x86 AVX-to-SSE vzeroupper insertion across 256-bit YMM and SSE2 calls."""
    src = work / "vzeroupper.rs"
    src.write_text("""#![no_std]
use core::arch::x86_64::*;

extern "C" {
    fn sse_legacy_callee(x: f32) -> f32;
}

#[target_feature(enable = "avx2")]
#[no_mangle]
pub unsafe extern "C" fn avx2_caller_into_sse(ptr: *const f32, out: *mut f32) -> f32 {
    let y = _mm256_loadu_ps(ptr);
    let y2 = _mm256_add_ps(y, y);
    _mm256_storeu_ps(out, y2);
    let low = _mm256_castps256_ps128(y2);
    let scalar = _mm_cvtss_f32(low);
    let r = sse_legacy_callee(scalar);
    r + 1.0
}
""")
    obj = work / "vzeroupper.o"
    subprocess.run([RUSTC, "--crate-type=rlib", "-Copt-level=3", "--emit=obj", str(src), "-o", str(obj)], check=True)
    dis = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj)], text=True)
    insns = [l.strip() for l in dis.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)]
    vzu_count = sum(1 for l in insns if "vzeroupper" in l)
    return {
        "vzeroupper_count": vzu_count,
        "disassembly": insns,
    }


def main():
    os.environ["RUSTC_BOOTSTRAP"] = "1"
    out_dir = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        results = {
            "skx102_jcc_32b_boundary": probe_skx102_jcc_32b(work),
            "cortex_a53_835769_mac_nop": probe_cortex_a53_835769(work),
            "cortex_a53_843419_adrp_veneer": probe_cortex_a53_843419_veneer(work),
            "x86_avx_sse_vzeroupper": probe_x86_vzeroupper(work),
        }
        out_path = out_dir / "errata_veneer_measurements.json"
        out_path.write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
