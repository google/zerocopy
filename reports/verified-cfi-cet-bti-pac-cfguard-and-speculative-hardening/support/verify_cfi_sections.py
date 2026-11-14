#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""8-target CFI and speculative-execution hardening instruction, section, and
live execution oracle (`rustc 1.99.1`, `llvm-objdump`, `llvm-readobj`, `qemu-aarch64`)."""

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
LLVM_READOBJ = str(LLVM_BIN / "llvm-readobj")
RUST_LLD = str(LLVM_BIN / "rust-lld")

PROBE_CFI_RS = """#![no_std]

#[no_mangle]
pub extern "C" fn cfi_target_a(x: u64) -> u64 {
    x.wrapping_add(11)
}

#[no_mangle]
pub extern "C" fn cfi_target_b(x: u64) -> u64 {
    x.wrapping_mul(3)
}

#[used]
#[no_mangle]
pub static CFI_ADDR_TAKEN_TABLE: [extern "C" fn(u64) -> u64; 2] = [cfi_target_a, cfi_target_b];

extern "C-unwind" {
    fn may_unwind_Action(x: u64) -> u64;
}

pub struct DropGuard(pub *mut u64);
impl Drop for DropGuard {
    fn drop(&mut self) {
        unsafe { core::ptr::write_volatile(self.0, 99); }
    }
}

#[no_mangle]
pub unsafe extern "C-unwind" fn cfi_ehcont_landing_pad(slot: *mut u64, x: u64) -> u64 {
    let _g = DropGuard(slot);
    may_unwind_Action(x) + 1
}

#[no_mangle]
pub extern "C" fn cfi_indirect_dispatch(fp: extern "C" fn(u64) -> u64, x: u64, sel: u32) -> u64 {
    let v = fp(x);
    match sel {
        0 => v.wrapping_add(1),
        1 => v.wrapping_add(2),
        2 => v.wrapping_add(4),
        3 => v.wrapping_add(8),
        4 => v.wrapping_add(16),
        5 => v.wrapping_add(32),
        6 => v.wrapping_add(64),
        _ => v.wrapping_add(128),
    }
}
"""


def inspect_cet_x86(work: Path) -> dict:
    src = work / "cet.rs"
    src.write_text(PROBE_CFI_RS)
    results = {}
    for target in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
        obj = work / f"cet_{target}.o"
        subprocess.run([
            RUSTC, f"--target={target}", "--crate-type=rlib", "-Copt-level=2",
            "-Zcf-protection=full", "--emit=obj", str(src), "-o", str(obj)
        ], check=True)
        dis = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj)], text=True)
        notes = subprocess.check_output([LLVM_READOBJ, "--notes", "--sections", str(obj)], text=True)
        endbr_mnem = "endbr64" if target.startswith("x86_64") else "endbr32"
        endbr_count = sum(1 for l in dis.splitlines() if endbr_mnem in l)
        results[target] = {
            "endbr_mnemonic": endbr_mnem,
            "endbr_encoding_hex": "f3 0f 1e fa" if target.startswith("x86_64") else "f3 0f 1e fb",
            "endbr_count_in_probe": endbr_count,
            "has_note_gnu_property": (".note.gnu.property" in notes),
            "ibt_and_shstk_feature_bits_present": ("IBT" in notes and "SHSTK" in notes),
            "sample_disassembly": [l.strip() for l in dis.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)][:12],
        }
    return results


def inspect_aarch64_bti_pac_gcs_and_run_qemu(work: Path) -> dict:
    src = work / "bti_pac.rs"
    src.write_text(PROBE_CFI_RS)
    results = {}
    for target in ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin", "aarch64-pc-windows-msvc"]:
        obj = work / f"bti_{target}.o"
        asm = work / f"bti_{target}.s"
        subprocess.run([
            RUSTC, f"--target={target}", "--crate-type=rlib", "-Copt-level=2",
            "-Zbranch-protection=bti,pac-ret,leaf,gcs",
            "-Cunsafe-allow-abi-mismatch=branch-protection",
            f"--emit=obj={obj},asm={asm}", str(src)
        ], check=True)
        dis = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj)], text=True)
        asm_txt = asm.read_text()
        readobj = subprocess.check_output([LLVM_READOBJ, "--sections", str(obj)], text=True)
        results[target] = {
            "bti_c_hint34_or_paciasp_emitted": ("hint\t#34" in asm_txt or "bti\tc" in dis or "paciasp" in dis or "hint\t#25" in asm_txt),
            "autiasp_hint29_emitted": ("hint\t#29" in asm_txt or "autiasp" in dis),
            "gcs_chkfeat_x16_emitted": ("hint\t#40" in asm_txt or "chkfeat" in dis or "d503251f" in dis),
            "has_gnu_property_section": (".note.gnu.property" in readobj),
            "sample_disassembly": [l.strip() for l in dis.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)][:14],
        }

    # Live execution of BTI + PAC-RET + Leaf + GCS binary under qemu-aarch64 -cpu max!
    exe_src = work / "bti_pac_main.rs"
    exe_src.write_text("""#![no_std]
#![no_main]

#[inline(never)]
#[no_mangle]
pub extern "C" fn pac_bti_callee(x: u64) -> u64 {
    x.wrapping_mul(7).wrapping_add(3)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn pac_bti_caller(fp: extern "C" fn(u64) -> u64, v: u64) -> u64 {
    fp(v) + 10
}

#[no_mangle]
pub unsafe extern "C" fn _start() {
    let fp: extern "C" fn(u64) -> u64 = core::hint::black_box(pac_bti_callee);
    let r = pac_bti_caller(fp, 5);
    let code: i64 = if r == 48 { 0 } else { 1 };
    core::arch::asm!("mov x8, #93", "svc #0", in("x0") code, options(noreturn));
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
""")
    exe_obj = work / "bti_pac_main.o"
    exe_bin = work / "bti_pac_main"
    subprocess.run([
        RUSTC, "--target=aarch64-unknown-linux-gnu", "-Cpanic=abort", "-Copt-level=2",
        "-Zbranch-protection=bti,pac-ret,leaf",
        "-Cunsafe-allow-abi-mismatch=branch-protection",
        "-Ctarget-feature=+bti,+paca,+pacg",
        "--emit=obj", str(exe_src), "-o", str(exe_obj)
    ], check=True)
    subprocess.run([RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", str(exe_obj), "-o", str(exe_bin)], check=True)
    rc_qemu = subprocess.run(["qemu-aarch64", "-cpu", "max", str(exe_bin)]).returncode
    exe_dis = subprocess.check_output([LLVM_OBJDUMP, "-d", str(exe_bin)], text=True)
    results["qemu_aarch64_live_bti_pac_execution"] = {
        "exit_code": rc_qemu,
        "passed": (rc_qemu == 0),
        "disassembly": [l.strip() for l in exe_dis.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
    }
    return results


def inspect_windows_cfguard_and_ehcont(work: Path) -> dict:
    src = work / "cfguard.rs"
    src.write_text(PROBE_CFI_RS)
    results = {}
    for target in ["x86_64-pc-windows-msvc", "i686-pc-windows-msvc", "aarch64-pc-windows-msvc", "x86_64-pc-windows-gnu"]:
        obj = work / f"cfg_{target}.o"
        asm = work / f"cfg_{target}.s"
        extra = ["-Zehcont-guard"] if target == "x86_64-pc-windows-msvc" else []
        subprocess.run([
            RUSTC, f"--target={target}", "--crate-type=rlib", "-Copt-level=2",
            "-Ccontrol-flow-guard=checks", *extra,
            f"--emit=obj={obj},asm={asm}", str(src)
        ], check=True)
        readobj = subprocess.check_output([LLVM_READOBJ, "--sections", "--symbols", str(obj)], text=True)
        asm_txt = asm.read_text()
        sec_names = re.findall(r"Name:\s*(\.[A-Za-z0-9_$]+)", readobj)
        results[target] = {
            "coff_sections": sec_names,
            "has_gfids_y": (".gfids$y" in sec_names),
            "has_giats_y": (".giats$y" in sec_names),
            "has_gehcont_y": (".gehcont$y" in sec_names),
            "uses_guard_dispatch_or_check_icall": ("__guard_dispatch_icall_fptr" in asm_txt or "__guard_check_icall_fptr" in asm_txt),
            "feat_00_flags_in_asm": [l.strip() for l in asm_txt.splitlines() if "@feat.00" in l or ".symidx" in l],
        }
    return results


def inspect_retpoline_return_thunk_and_ssp(work: Path) -> dict:
    src = work / "retpoline.rs"
    src.write_text("""#![no_std]
#[no_mangle]
pub extern "C" fn retpoline_and_ssp_caller(fp: extern "C" fn(u64) -> u64, x: u64) -> u64 {
    let mut buf = [0u8; 64];
    buf[0] = x as u8;
    let r = fp(x + (buf[0] as u64));
    unsafe { core::ptr::read_volatile(&buf[0]) as u64 + r }
}
""")
    obj = work / "retpoline.o"
    asm = work / "retpoline.s"
    subprocess.run([
        RUSTC, "--target=x86_64-unknown-linux-gnu", "--crate-type=rlib", "-Copt-level=2",
        "-Zretpoline", "-Zfunction-return=thunk-extern", "-Zstack-protector=all",
        "-Cunsafe-allow-abi-mismatch=retpoline",
        f"--emit=obj={obj},asm={asm}", str(src)
    ], check=True)
    dis = subprocess.check_output([LLVM_OBJDUMP, "-d", str(obj)], text=True)
    asm_txt = asm.read_text()
    return {
        "has_llvm_retpoline_r11_comdat": ("__llvm_retpoline_r11" in asm_txt),
        "has_x86_return_thunk_jmp": ("__x86_return_thunk" in asm_txt),
        "has_fs_40_stack_canary": ("%fs:40" in asm_txt),
        "disassembly": [l.strip() for l in dis.splitlines() if re.match(r"^\s*[0-9a-fA-F]+:", l)],
    }


def main():
    os.environ["RUSTC_BOOTSTRAP"] = "1"
    out_dir = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        data = {
            "intel_cet_ibt_shstk": inspect_cet_x86(work),
            "aarch64_bti_pac_ret_gcs": inspect_aarch64_bti_pac_gcs_and_run_qemu(work),
            "windows_cfguard_and_ehcont": inspect_windows_cfguard_and_ehcont(work),
            "spectre_v2_retpoline_return_thunk_and_ssp": inspect_retpoline_return_thunk_and_ssp(work),
        }
        out_path = out_dir / "cfi_hardening_obligations.json"
        out_path.write_text(json.dumps(data, indent=2) + "\n")
        print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main()
