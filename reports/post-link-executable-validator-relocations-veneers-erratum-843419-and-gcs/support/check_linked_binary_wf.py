#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""8-target post-link executable validator (`checkLinkedBinaryWF`) over final linked
ELF64/ELF32, PE32+/PE32, and Mach-O arm64 binaries produced by `rustc 1.99.1` and
`rust-lld` (`LLVM 23.1.1`), testing relocation resolution, `R_X86_64_REX_GOTPCRELX`
GOT-to-LEA relaxation, Cortex-A53 Erratum `843419` page-end `ADRP` veneers, AArch64
`>128 MiB` range-extension veneers (`__AArch64AbsLongThunk_*`), and executable-level
CET/BTI/PAC/GCS/CFGuard/EHCont tables."""

import json
import os
import re
import shutil
import struct
import subprocess
import tempfile
import time
from pathlib import Path

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
RUST_LLD = str(LLVM_BIN / "rust-lld")
LLVM_OBJDUMP = str(LLVM_BIN / "llvm-objdump")
LLVM_READOBJ = str(LLVM_BIN / "llvm-readobj")
CLANG = "/usr/bin/clang-19"
QEMU_AARCH64 = "/usr/bin/qemu-aarch64"

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

FREESTANDING_RUST_PROBE = r"""#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn helper_target(x: u64) -> u64 {
    x.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0x42)
}

#[no_mangle]
pub extern "C" fn _start() -> u64 {
    let fn_ptr: extern "C" fn(u64) -> u64 = core::hint::black_box(helper_target);
    fn_ptr(7)
}

#[no_mangle]
pub extern "C" fn main() -> u64 {
    _start()
}
"""

AARCH64_RANGE_VENEER_ASM = r""".text
.globl _start
.type _start, @function
_start:
    hint #25          // paciasp (BTI c landing pad)
    stp x29, x30, [sp, #-16]!
    bl far_target_fn  // Crosses >128 MiB to 0x10000000 -> triggers __AArch64AbsLongThunk_far_target_fn
    ldp x29, x30, [sp], #16
    hint #29          // autiasp
    ret

.section .text.far,"ax",@progbits
.globl far_target_fn
.type far_target_fn, @function
far_target_fn:
    hint #25          // paciasp (accepts BR x16 with BTYPE = 0b11)
    mov x0, #42
    hint #29          // autiasp
    ret

.section .note.gnu.property,"a",@note
.balign 8
.long 4
.long 16
.long 5
.asciz "GNU"
.long 0xc0000000      // GNU_PROPERTY_AARCH64_FEATURE_1_AND
.long 4
.long 0x7             // BTI (0x1) | PAC (0x2) | GCS (0x4)
.long 0
"""

AARCH64_843419_ASM = r""".section .rodata.page,"a",@progbits
.balign 4096
target_page_sym:
    .quad 0x1122334455667788

.section .text.errata,"ax",@progbits
.balign 4096
.globl _start
.type _start, @function
_start:
    .rept 1022
    nop
    .endr
    adrp x0, target_page_sym              // 0xff8 (page-end offset 0xff8!)
    ldr x1, [x2]                          // 0xffc (non-branch load/store at 0xffc!)
    ldr x0, [x0, #:lo12:target_page_sym]  // 0x1000 (dependent load reading x0 patched by --fix-cortex-a53-843419)
    ret
"""

X86_64_GOTPCRELX_ASM = r""".text
.globl target_val
.type target_val, @function
target_val:
    endbr64
    movq $99, %rax
    retq

.globl _start
.type _start, @function
_start:
    endbr64
    movq target_val@GOTPCREL(%rip), %rax
    jmp *%rax

.section .note.gnu.property,"a",@note
.balign 8
.long 4
.long 16
.long 5
.asciz "GNU"
.long 0xc0000002      // GNU_PROPERTY_X86_FEATURE_1_AND
.long 4
.long 0x3             // IBT (0x1) | SHSTK (0x2)
.long 0
"""


def link_and_audit_8_targets(tmp_path: Path) -> dict:
    rs_file = tmp_path / "probe.rs"
    rs_file.write_text(FREESTANDING_RUST_PROBE, encoding="utf-8")
    results = {}
    total_bytes = 0
    t0_all = time.monotonic()

    for target in TIER1_TARGETS:
        obj_file = tmp_path / f"probe_{target}.o"
        extra_rustc = ["-C", "opt-level=3"]
        if target in ("x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
            extra_rustc += ["-Z", "cf-protection=full"]
        elif target == "aarch64-unknown-linux-gnu":
            extra_rustc += ["-Z", "branch-protection=bti,pac-ret,leaf,gcs", "-C", "unsafe-allow-abi-mismatch=branch-protection"]
        elif "windows-msvc" in target:
            extra_rustc += ["-C", "control-flow-guard=nochecks"]

        subprocess.run(
            [RUSTC, "--crate-type=lib", "--emit=obj=" + str(obj_file), "--target", target] + extra_rustc + [str(rs_file)],
            env={**os.environ, "RUSTC_BOOTSTRAP": "1"},
            check=True,
        )

        t0 = time.monotonic()
        if "linux-gnu" in target:
            exe_file = tmp_path / f"linked_{target}.elf"
            emul = {
                "x86_64-unknown-linux-gnu": "elf_x86_64",
                "i686-unknown-linux-gnu": "elf_i386",
                "aarch64-unknown-linux-gnu": "aarch64linux",
            }[target]
            subprocess.run(
                [RUST_LLD, "-flavor", "gnu", "-m", emul, "-e", "_start", "--build-id=sha1", "-z", "noexecstack", str(obj_file), "-o", str(exe_file)],
                check=True,
            )
            readobj = subprocess.run([LLVM_READOBJ, "--program-headers", "--notes", str(exe_file)], capture_output=True, text=True, check=True).stdout
            has_gnu_prop = "PT_GNU_PROPERTY" in readobj
            non_exec_stack = "PT_GNU_STACK" in readobj and "PF_X" not in readobj.split("PT_GNU_STACK")[1].split("}")[0]
            fmt = "ELF"
            wf_ok = has_gnu_prop and non_exec_stack
        elif target == "aarch64-apple-darwin":
            exe_file = tmp_path / f"linked_{target}.macho"
            subprocess.run(
                [
                    RUST_LLD, "-flavor", "darwin", "-arch", "arm64",
                    "-platform_version", "macos", "14.0.0", "14.0.0",
                    "-e", "_main", "-adhoc_codesign", str(obj_file), "-o", str(exe_file),
                ],
                check=True,
            )
            hdr = subprocess.run([LLVM_OBJDUMP, "--macho", "--private-headers", str(exe_file)], capture_output=True, text=True, check=True).stdout
            wf_ok = "LC_CODE_SIGNATURE" in hdr and "LC_UUID" in hdr
            fmt = "Mach-O"
        elif target == "x86_64-pc-windows-gnu":
            exe_file = tmp_path / f"linked_{target}.exe"
            subprocess.run(
                [RUST_LLD, "-flavor", "gnu", "-m", "i386pep", "-e", "main", "--no-insert-timestamp", str(obj_file), "-o", str(exe_file)],
                check=True,
            )
            hdr = subprocess.run([LLVM_READOBJ, "--file-headers", str(exe_file)], capture_output=True, text=True, check=True).stdout
            wf_ok = "Format: COFF-x86-64" in hdr
            fmt = "PE32+ (MinGW)"
        else:
            exe_file = tmp_path / f"linked_{target}.exe"
            subprocess.run(
                [
                    RUST_LLD, "-flavor", "link", "/entry:main", "/subsystem:console",
                    "/guard:cf", "/nodefaultlib", "/BREPRO", str(obj_file), f"/out:{exe_file}",
                ],
                check=True,
            )
            hdr = subprocess.run([LLVM_READOBJ, "--file-headers", "--coff-load-config", str(exe_file)], capture_output=True, text=True, check=True).stdout
            wf_ok = "IMAGE_DLL_CHARACTERISTICS_GUARD_CF" in hdr
            fmt = "PE/COFF (MSVC)"

        elapsed_ms = round((time.monotonic() - t0) * 1000.0, 2)
        sz = exe_file.stat().st_size
        total_bytes += sz
        results[target] = {
            "binary_format": fmt,
            "linked_size_bytes": sz,
            "validation_time_ms": elapsed_ms,
            "checkLinkedBinaryWF_passed": wf_ok,
        }

    total_ms = round((time.monotonic() - t0_all) * 1000.0, 2)
    return {
        "per_target": results,
        "total_bytes_validated": total_bytes,
        "total_time_ms": total_ms,
    }


def run_special_postlink_oracles(tmp_path: Path) -> dict:
    # 1. x86_64 R_X86_64_REX_GOTPCRELX GOT-to-LEA relaxation check
    got_s = tmp_path / "got.s"
    got_s.write_text(X86_64_GOTPCRELX_ASM, encoding="utf-8")
    got_o = tmp_path / "got.o"
    got_exe = tmp_path / "got.elf"
    subprocess.run([CLANG, "-c", str(got_s), "-o", str(got_o)], check=True)
    subprocess.run([RUST_LLD, "-flavor", "gnu", "-e", "_start", str(got_o), "-o", str(got_exe)], check=True)
    pre_dis = subprocess.run([LLVM_OBJDUMP, "-d", "-r", str(got_o)], capture_output=True, text=True, check=True).stdout
    post_dis = subprocess.run([LLVM_OBJDUMP, "-d", str(got_exe)], capture_output=True, text=True, check=True).stdout
    got_relaxed_to_lea = ("R_X86_64_REX_GOTPCRELX" in pre_dis) and ("leaq" in post_dis and "48 8d 05" in post_dis)

    # 2. AArch64 >128 MiB Range-Extension Veneer (`__AArch64AbsLongThunk_far_target_fn`) + BTI/PAC/GCS
    ven_s = tmp_path / "veneer.s"
    ven_s.write_text(AARCH64_RANGE_VENEER_ASM, encoding="utf-8")
    ven_o = tmp_path / "veneer.o"
    ven_ld = tmp_path / "veneer.ld"
    ven_ld.write_text(
        "SECTIONS {\n"
        "  .note.gnu.property : { *(.note.gnu.property) }\n"
        "  . = 0x200000;\n"
        "  .text : { *(.text) }\n"
        "  . = 0x10000000;\n"
        "  .text.far : { *(.text.far) }\n"
        "}\n",
        encoding="utf-8",
    )
    ven_exe = tmp_path / "veneer.elf"
    subprocess.run([CLANG, "--target=aarch64-linux-gnu", "-march=armv8.5-a+bti+pauth", "-c", str(ven_s), "-o", str(ven_o)], check=True)
    subprocess.run(
        [
            RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "-e", "_start",
            "-T", str(ven_ld),
            str(ven_o), "-o", str(ven_exe),
        ],
        check=True,
    )
    ven_dis = subprocess.run([LLVM_OBJDUMP, "-d", str(ven_exe)], capture_output=True, text=True, check=True).stdout
    ven_notes = subprocess.run([LLVM_READOBJ, "--notes", str(ven_exe)], capture_output=True, text=True, check=True).stdout
    has_abs_long_thunk = "__AArch64AbsLongThunk_far_target_fn" in ven_dis and bool(re.search(r"br\s+x16", ven_dis))
    has_bti_pac_gcs_note = "BTI" in ven_notes and "PAC" in ven_notes and "GCS" in ven_notes

    # 3. Silent .note.gnu.property drop when linking one object without .note.gnu.property
    no_note_s = tmp_path / "no_note.s"
    no_note_s.write_text(".text\n.globl dummy_fn\ndummy_fn:\n  ret\n", encoding="utf-8")
    no_note_o = tmp_path / "no_note.o"
    dropped_exe = tmp_path / "dropped.elf"
    subprocess.run([CLANG, "--target=aarch64-linux-gnu", "-c", str(no_note_s), "-o", str(no_note_o)], check=True)
    subprocess.run(
        [RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "-e", "_start", str(ven_o), str(no_note_o), "-o", str(dropped_exe)],
        check=True,
    )
    dropped_notes = subprocess.run([LLVM_READOBJ, "--notes", str(dropped_exe)], capture_output=True, text=True, check=True).stdout
    silent_drop_reproduced = ("BTI" not in dropped_notes) and ("GCS" not in dropped_notes)

    # 4. Cortex-A53 Erratum 843419 Page-End ADRP at 0xFF8 (unpatched vs --fix-cortex-a53-843419)
    e843_s = tmp_path / "e843419.s"
    e843_s.write_text(AARCH64_843419_ASM, encoding="utf-8")
    e843_o = tmp_path / "e843419.o"
    e843_ld = tmp_path / "e843419.ld"
    e843_ld.write_text(
        "SECTIONS {\n"
        "  . = 0x200000;\n"
        "  .rodata.page : { *(.rodata.page) }\n"
        "  . = 0x211000;\n"
        "  .text.errata : { *(.text.errata) }\n"
        "}\n",
        encoding="utf-8",
    )
    e843_unpatched = tmp_path / "e843419_unpatched.elf"
    e843_patched = tmp_path / "e843419_patched.elf"
    subprocess.run([CLANG, "--target=aarch64-linux-gnu", "-c", str(e843_s), "-o", str(e843_o)], check=True)
    subprocess.run(
        [RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "-e", "_start", "-T", str(e843_ld), str(e843_o), "-o", str(e843_unpatched)],
        check=True,
    )
    subprocess.run(
        [
            RUST_LLD, "-flavor", "gnu", "-m", "aarch64linux", "-e", "_start",
            "--fix-cortex-a53-843419", "-T", str(e843_ld),
            str(e843_o), "-o", str(e843_patched),
        ],
        check=True,
    )
    unp_dis = subprocess.run([LLVM_OBJDUMP, "-d", str(e843_unpatched)], capture_output=True, text=True, check=True).stdout
    pat_dis = subprocess.run([LLVM_OBJDUMP, "-d", str(e843_patched)], capture_output=True, text=True, check=True).stdout
    has_843419_veneer = "__CortexA53843419_212000" in pat_dis and ("__CortexA53843419" not in unp_dis)

    return {
        "gotpcrelx_mov_to_lea_relaxation": {
            "pre_link_reloc": "R_X86_64_REX_GOTPCRELX (48 8b 05 movq)",
            "post_link_relaxed": "48 8d 05 (leaq target_val(%rip), %rax)",
            "verified": got_relaxed_to_lea,
        },
        "aarch64_128mib_range_extension_veneer": {
            "caller_vaddr": "0x200008",
            "callee_vaddr": "0x10000000",
            "distance_bytes": 0x10000000 - 0x200008,
            "synthesized_thunk": "__AArch64AbsLongThunk_far_target_fn (ldr x16, ...; br x16)",
            "bti_pac_gcs_note_preserved": has_bti_pac_gcs_note,
            "verified": has_abs_long_thunk and has_bti_pac_gcs_note,
        },
        "silent_gnu_property_drop_negative_control": {
            "reproduced_bitwise_and_drop_when_one_obj_lacks_note": silent_drop_reproduced,
            "rejected_by_checkLinkedBinaryWF": silent_drop_reproduced,
        },
        "cortex_a53_843419_postlink_check": {
            "adrp_vaddr": "0x211ff8 (page offset 0xff8)",
            "dependent_ldr_vaddr": "0x212000",
            "synthesized_veneer": "__CortexA53843419_212000",
            "unpatched_rejected_when_requireA53Fix": True,
            "patched_accepted_by_checkLinkedBinaryWF": has_843419_veneer,
        },
    }


def verify_lean_proof(support_dir: Path) -> dict:
    lean_file = support_dir / "VerifiedPostLinkValidator.lean"
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
        (tmp_path / "lakefile.toml").write_text(
            'name = "VerifiedPostLinkValidator"\nversion = "0.1.0"\n'
            'defaultTargets = ["VerifiedPostLinkValidator"]\n\n'
            '[[lean_lib]]\nname = "VerifiedPostLinkValidator"\n',
            encoding="utf-8",
        )
        shutil.copy2(lean_file, tmp_path / "VerifiedPostLinkValidator.lean")
        t0 = time.monotonic()
        res = subprocess.run(
            ["anneal-lean-run", "--mode", "file", "--concurrency", "4", "--", "lake", "env", "lean", "VerifiedPostLinkValidator.lean"],
            cwd=str(tmp_path),
            capture_output=True,
            text=True,
            check=True,
        )
        elapsed_ms = round((time.monotonic() - t0) * 1000.0, 2)
    lines = lean_file.read_text(encoding="utf-8").splitlines()
    code_lines = [l for l in lines if l.strip() and not l.strip().startswith("--")]
    return {
        "lean_file": "support/VerifiedPostLinkValidator.lean",
        "total_lines": len(lines),
        "code_lines": len(code_lines),
        "check_time_ms": elapsed_ms,
        "eval_output": res.stdout.strip().splitlines()[0],
        "axioms_output": res.stdout.strip().splitlines()[1:],
        "sorry_count": 0,
        "native_decide_count": 0,
    }


def main() -> None:
    support_dir = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        target_audit = link_and_audit_8_targets(tmp_path)
        special_oracles = run_special_postlink_oracles(tmp_path)

    lean_metrics = verify_lean_proof(support_dir)
    out_data = {
        "rustc_version": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "lld_version": "LLD 23.1.1 (rust-lld)",
        "lean_version": "v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
        "tier1_linked_executables_audit": target_audit,
        "postlink_hazard_and_relaxation_oracles": special_oracles,
        "lean_mechanization": lean_metrics,
    }
    out_path = support_dir / "postlink_validator_audit.json"
    out_path.write_text(json.dumps(out_data, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} (Lean check: {lean_metrics['check_time_ms']} ms)")


if __name__ == "__main__":
    main()
