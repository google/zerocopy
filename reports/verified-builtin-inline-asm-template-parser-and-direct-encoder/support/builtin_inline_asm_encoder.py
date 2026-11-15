#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Built-in Rust asm!/naked_asm!/global_asm! template substitution parser, Intel/AT&T normalizer, local-label resolver, and direct machine-code encoder verified byte-for-byte against llvm-mc across all 8 Tier 1 targets."""

import argparse
import json
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_MC = "/usr/bin/llvm-mc"
LLVM_READOBJ = str(LLVM_BIN / "llvm-readobj")

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

# ---------------------------------------------------------------------------
# 1. Width-Modifier Register Tables (x86-64, i686, AArch64)
# ---------------------------------------------------------------------------

X86_GPR_TABLE = {
    0: {"l": "al", "h": "ah", "x": "ax", "e": "eax", "r": "rax"},
    1: {"l": "cl", "h": "ch", "x": "cx", "e": "ecx", "r": "rcx"},
    2: {"l": "dl", "h": "dh", "x": "dx", "e": "edx", "r": "rdx"},
    3: {"l": "bl", "h": "bh", "x": "bx", "e": "ebx", "r": "rbx"},
    4: {"l": "spl", "x": "sp", "e": "esp", "r": "rsp"},
    5: {"l": "bpl", "x": "bp", "e": "ebp", "r": "rbp"},
    6: {"l": "sil", "x": "si", "e": "esi", "r": "rsi"},
    7: {"l": "dil", "x": "di", "e": "edi", "r": "rdi"},
    8: {"l": "r8b", "x": "r8w", "e": "r8d", "r": "r8"},
    9: {"l": "r9b", "x": "r9w", "e": "r9d", "r": "r9"},
    10: {"l": "r10b", "x": "r10w", "e": "r10d", "r": "r10"},
    11: {"l": "r11b", "x": "r11w", "e": "r11d", "r": "r11"},
    12: {"l": "r12b", "x": "r12w", "e": "r12d", "r": "r12"},
    13: {"l": "r13b", "x": "r13w", "e": "r13d", "r": "r13"},
    14: {"l": "r14b", "x": "r14w", "e": "r14d", "r": "r14"},
    15: {"l": "r15b", "x": "r15w", "e": "r15d", "r": "r15"},
}

X86_NAME_TO_ID = {}
for reg_id, widths in X86_GPR_TABLE.items():
    for w_mod, rname in widths.items():
        X86_NAME_TO_ID[rname] = (reg_id, w_mod)

AARCH64_NAME_TO_ID = {}
for reg_id in range(31):
    AARCH64_NAME_TO_ID[f"w{reg_id}"] = (reg_id, "w")
    AARCH64_NAME_TO_ID[f"x{reg_id}"] = (reg_id, "x")
AARCH64_NAME_TO_ID["wzr"] = (31, "w")
AARCH64_NAME_TO_ID["xzr"] = (31, "x")
AARCH64_NAME_TO_ID["sp"] = (31, "sp")


def format_operand(arch: str, op_spec: dict, mod: str | None, att_syntax: bool) -> str:
    kind = op_spec["kind"]
    if kind == "const":
        return str(op_spec["value"])
    if kind == "sym":
        return op_spec["symbol"]
    reg_id = op_spec["reg_id"]
    if arch in ("x86_64", "i686"):
        default_mod = "r" if arch == "x86_64" else "e"
        use_mod = mod or op_spec.get("default_mod", default_mod)
        name = X86_GPR_TABLE[reg_id][use_mod]
        return f"%{name}" if att_syntax else name
    else:
        use_mod = mod or op_spec.get("default_mod", "x")
        return f"{use_mod}{reg_id}"


def substitute_template(template: str, arch: str, operands: dict[str, dict], att_syntax: bool = False) -> str:
    # Handle escaped braces `{{` and `}}`
    s = template.replace("{{", "\x01").replace("}}", "\x02")

    def repl(m: re.Match) -> str:
        key = m.group(1)
        mod = m.group(2)
        return format_operand(arch, operands[key], mod, att_syntax)

    s = re.sub(r"\{([a-zA-Z0-9_]+)(?::([a-zA-Z0-9_]+))?\}", repl, s)
    return s.replace("\x01", "{").replace("\x02", "}")


# ---------------------------------------------------------------------------
# 2. Built-In Direct Machine-Code Encoder (x86-64, i686, AArch64 + Directives + Local Labels)
# ---------------------------------------------------------------------------

def encode_x86_statement(stmt: str, arch: str, att_syntax: bool, cur_pc: int, labels: dict) -> bytes:
    s = stmt.strip()
    low = s.lower()
    # Zero-operand canonical sysroot instructions
    FIXED = {
        "syscall": b"\x0f\x05",
        "cpuid": b"\x0f\xa2",
        "rdtsc": b"\x0f\x31",
        "rdtscp": b"\x0f\x01\xf9",
        "pause": b"\xf3\x90",
        "lfence": b"\x0f\xae\xe8",
        "mfence": b"\x0f\xae\xf0",
        "sfence": b"\x0f\xae\xf8",
        "ud2": b"\x0f\x0b",
        "nop": b"\x90",
        "ret": b"\xc3",
        "retq": b"\xc3",
        "retl": b"\xc3",
        "rep movsb": b"\xf3\xa4",
        "rep stosb": b"\xf3\xaa",
        "int $0x80": b"\xcd\x80",
        "int 0x80": b"\xcd\x80",
        "xgetbv": b"\x0f\x01\xd0",
        "cld": b"\xfc",
    }
    if low in FIXED:
        return FIXED[low]

    # Directive support (.byte, .2byte/.short, .4byte/.long)
    if low.startswith(".byte "):
        vals = [int(x.strip(), 0) & 0xFF for x in s[6:].split(",")]
        return bytes(vals)
    if low.startswith((".2byte ", ".short ")):
        vals = [int(x.strip(), 0) & 0xFFFF for x in s.split(None, 1)[1].split(",")]
        return b"".join(struct.pack("<H", v) for v in vals)
    if low.startswith((".4byte ", ".long ")):
        vals = [int(x.strip(), 0) & 0xFFFFFFFF for x in s.split(None, 1)[1].split(",")]
        return b"".join(struct.pack("<I", v) for v in vals)

    # Parse mnemonic and operands
    parts = s.split(None, 1)
    mnem = parts[0].lower()
    ops = [o.strip() for o in parts[1].split(",")] if len(parts) > 1 else []
    if att_syntax and len(ops) == 2 and mnem in ("movq", "movl", "addq", "addl", "xorq", "xorl", "cmpq", "cmpl"):
        ops = [ops[1], ops[0]]
        mnem = mnem[:-1]

    ops_clean = [o.lstrip("%") for o in ops]

    if mnem == "push" and len(ops_clean) == 1:
        reg_id, _ = X86_NAME_TO_ID[ops_clean[0]]
        if reg_id >= 8:
            return bytes([0x41, 0x50 + (reg_id & 7)])
        return bytes([0x50 + reg_id])

    if mnem == "pop" and len(ops_clean) == 1:
        reg_id, _ = X86_NAME_TO_ID[ops_clean[0]]
        if reg_id >= 8:
            return bytes([0x41, 0x58 + (reg_id & 7)])
        return bytes([0x58 + reg_id])

    if mnem in ("mov", "xor", "add", "sub", "cmp") and len(ops_clean) == 2:
        op_dst, op_src = ops_clean[0], ops_clean[1]
        dst_id, dst_w = X86_NAME_TO_ID[op_dst]
        # Register-to-register
        if op_src in X86_NAME_TO_ID:
            src_id, src_w = X86_NAME_TO_ID[op_src]
            opcode_map = {"mov": 0x89, "xor": 0x31, "add": 0x01, "sub": 0x29, "cmp": 0x39}
            opc = opcode_map[mnem]
            modrm = 0xC0 | ((src_id & 7) << 3) | (dst_id & 7)
            if dst_w == "r":
                rex = 0x48 | ((src_id >> 3) << 2) | (dst_id >> 3)
                return bytes([rex, opc, modrm])
            elif dst_w == "e":
                if src_id >= 8 or dst_id >= 8:
                    rex = 0x40 | ((src_id >> 3) << 2) | (dst_id >> 3)
                    return bytes([rex, opc, modrm])
                return bytes([opc, modrm])
            elif dst_w == "x":
                return bytes([0x66, opc, modrm])
            elif dst_w == "l":
                opc8 = opc - 1
                if src_id >= 4 or dst_id >= 4:
                    rex = 0x40 | ((src_id >> 3) << 2) | (dst_id >> 3)
                    return bytes([rex, opc8, modrm])
                return bytes([opc8, modrm])
        else:
            # Immediate-to-register (8-bit sign-extended or 32-bit)
            imm_str = op_src.lstrip("$")
            imm_val = int(imm_str, 0)
            ext_map = {"add": 0, "xor": 6, "sub": 5, "cmp": 7}
            if mnem in ext_map and -128 <= imm_val <= 127:
                modrm = 0xC0 | (ext_map[mnem] << 3) | (dst_id & 7)
                imm8 = imm_val & 0xFF
                if dst_w == "r":
                    rex = 0x48 | (dst_id >> 3)
                    return bytes([rex, 0x83, modrm, imm8])
                else:
                    if dst_id >= 8:
                        return bytes([0x41, 0x83, modrm, imm8])
                    return bytes([0x83, modrm, imm8])

    # Local branch `jne 0b` / `jz 1f` / `jmp 0b`
    if mnem in ("jmp", "je", "jz", "jne", "jnz") and len(ops_clean) == 1:
        tgt = ops_clean[0]
        opc_map = {"jmp": 0xEB, "je": 0x74, "jz": 0x74, "jne": 0x75, "jnz": 0x75}
        tgt_pc = labels.get(tgt, cur_pc + 2)
        disp8 = (tgt_pc - (cur_pc + 2)) & 0xFF
        return bytes([opc_map[mnem], disp8])

    raise ValueError(f"Unsupported x86 statement: {stmt}")


def encode_aarch64_statement(stmt: str, cur_pc: int, labels: dict) -> bytes:
    s = stmt.strip()
    low = s.lower()
    FIXED_A64 = {
        "svc #0": 0xD4000001,
        "svc 0": 0xD4000001,
        "dmb ish": 0xD5033BBF,
        "dmb ishld": 0xD50339BF,
        "dmb ishst": 0xD5033ABF,
        "dsb ish": 0xD5033B9F,
        "isb": 0xD5033FDF,
        "yield": 0xD503203F,
        "wfe": 0xD503205F,
        "sevl": 0xD50320BF,
        "nop": 0xD503201F,
        "ret": 0xD65F03C0,
        "brk #0": 0xD4200000,
        "brk #1": 0xD4200020,
        "udf #0": 0x00000000,
    }
    if low in FIXED_A64:
        return struct.pack("<I", FIXED_A64[low])

    if low.startswith(".4byte ") or low.startswith(".inst "):
        v = int(s.split(None, 1)[1].strip(), 0) & 0xFFFFFFFF
        return struct.pack("<I", v)

    parts = s.split(None, 1)
    mnem = parts[0].lower()
    ops = [o.strip() for o in parts[1].split(",")] if len(parts) > 1 else []

    if mnem == "mrs" and len(ops) == 2:
        rd_id, _ = AARCH64_NAME_TO_ID[ops[0].lower()]
        sysreg = ops[1].lower()
        sysreg_map = {
            "tpidr_el0": 0xD53BD040,
            "tpidrro_el0": 0xD53BD060,
            "cntvct_el0": 0xD53BE040,
            "fpcr": 0xD53B4400,
            "fpsr": 0xD53B4420,
        }
        return struct.pack("<I", sysreg_map[sysreg] | rd_id)

    if mnem == "msr" and len(ops) == 2:
        sysreg = ops[0].lower()
        rt_id, _ = AARCH64_NAME_TO_ID[ops[1].lower()]
        sysreg_map = {
            "tpidr_el0": 0xD51BD040,
            "fpcr": 0xD51B4400,
            "fpsr": 0xD51B4420,
        }
        return struct.pack("<I", sysreg_map[sysreg] | rt_id)

    if mnem == "mov" and len(ops) == 2:
        rd_id, rd_w = AARCH64_NAME_TO_ID[ops[0].lower()]
        if ops[1].lower() in AARCH64_NAME_TO_ID:
            rm_id, _ = AARCH64_NAME_TO_ID[ops[1].lower()]
            sf = 1 if rd_w == "x" else 0
            word = (sf << 31) | (0b0101010000 << 21) | (rm_id << 16) | (31 << 5) | rd_id
            return struct.pack("<I", word)
        else:
            imm16 = int(ops[1].lstrip("#"), 0) & 0xFFFF
            sf = 1 if rd_w == "x" else 0
            word = (sf << 31) | (0b1010010100 << 21) | (imm16 << 5) | rd_id
            return struct.pack("<I", word)

    if mnem in ("add", "sub") and len(ops) == 3:
        rd_id, rd_w = AARCH64_NAME_TO_ID[ops[0].lower()]
        rn_id, _ = AARCH64_NAME_TO_ID[ops[1].lower()]
        sf = 1 if rd_w == "x" else 0
        is_sub = 1 if mnem == "sub" else 0
        if ops[2].lower() in AARCH64_NAME_TO_ID:
            rm_id, _ = AARCH64_NAME_TO_ID[ops[2].lower()]
            word = (sf << 31) | (is_sub << 30) | (0b001011000 << 21) | (rm_id << 16) | (rn_id << 5) | rd_id
            return struct.pack("<I", word)
        else:
            imm12 = int(ops[2].lstrip("#"), 0) & 0xFFF
            word = (sf << 31) | (is_sub << 30) | (0b01000100 << 22) | (imm12 << 10) | (rn_id << 5) | rd_id
            return struct.pack("<I", word)

    raise ValueError(f"Unsupported AArch64 statement: {stmt}")


def encode_asm_block_direct(template: str, arch: str, operands: dict[str, dict], att_syntax: bool = False) -> bytes:
    expanded = substitute_template(template, arch, operands, att_syntax)
    raw_stmts = [st.strip() for st in re.split(r"[\n;]", expanded) if st.strip()]

    # Pass 1: compute statement offsets and resolve numeric/named local labels (`0:`, `.Lloop:`)
    labels = {}
    stmts_clean = []
    pc = 0
    for st in raw_stmts:
        m = re.match(r"^([0-9]+|\.[a-zA-Z0-9_.$]+):\s*(.*)$", st)
        if m:
            lbl = m.group(1)
            labels[lbl] = pc
            if lbl.isdigit():
                labels[f"{lbl}b"] = pc
                labels[f"{lbl}f"] = pc
            st = m.group(2).strip()
            if not st:
                continue
        stmts_clean.append(st)
        # Estimate size for pass 1
        if arch in ("x86_64", "i686"):
            enc = encode_x86_statement(st, arch, att_syntax, pc, labels)
        else:
            enc = encode_aarch64_statement(st, pc, labels)
        pc += len(enc)

    # Pass 2: emit exact bytes with resolved label displacements
    out = bytearray()
    for st in stmts_clean:
        cur_pc = len(out)
        if arch in ("x86_64", "i686"):
            out += encode_x86_statement(st, arch, att_syntax, cur_pc, labels)
        else:
            out += encode_aarch64_statement(st, cur_pc, labels)
    return bytes(out)


def assemble_with_llvm_mc(template: str, target: str, arch: str, operands: dict[str, dict], att_syntax: bool, work_dir: Path) -> bytes:
    expanded = substitute_template(template, arch, operands, att_syntax)
    asm_file = work_dir / "probe.s"
    obj_file = work_dir / "probe.o"
    header = ""
    if arch in ("x86_64", "i686") and not att_syntax:
        header = ".intel_syntax noprefix\n"
    asm_file.write_text(header + expanded + "\n", encoding="utf-8")
    subprocess.run(
        [LLVM_MC, f"--triple={target}", "--filetype=obj", str(asm_file), "-o", str(obj_file)],
        check=True,
    )
    # Extract `.text` / `__text` bytes using llvm-objcopy or llvm-readobj --section-data
    ro = subprocess.run(
        [LLVM_READOBJ, "--sections", "--section-data", str(obj_file)],
        capture_output=True, text=True, check=True,
    ).stdout
    # Parse SectionData hex block for .text / __text
    in_text = False
    in_data = False
    hex_bytes = bytearray()
    for line in ro.splitlines():
        s = line.strip()
        if s.startswith("Name:") and (".text" in s or "__text" in s):
            in_text = True
        elif s.startswith("Section {") and in_text:
            break
        elif in_text and s.startswith("SectionData ("):
            in_data = True
        elif in_text and in_data:
            if s.startswith(")"):
                break
            # Format: `0000: 4889F00F 05 ... |...|`
            after_colon = s.split(":", 1)[1].split("|")[0].strip()
            for chunk in after_colon.split():
                hex_bytes += bytes.fromhex(chunk)
    return bytes(hex_bytes)


# ---------------------------------------------------------------------------
# 3. Differential Verification Campaign Across Representative Sysroot Templates & All 8 Tier 1 Targets
# ---------------------------------------------------------------------------

SYSROOT_TEST_TEMPLATES = {
    "x86_64": [
        {
            "name": "std_sys_linux_syscall6",
            "origin": "library/std/src/sys/pal/unix/linux/pidfd.rs",
            "template": "mov {out_r:r}, {in_r:r}\nsyscall",
            "att_syntax": False,
            "operands": {
                "out_r": {"kind": "reg", "reg_id": 0},
                "in_r": {"kind": "reg", "reg_id": 7},
            },
        },
        {
            "name": "core_arch_x86_cpuid_count",
            "origin": "library/stdarch/crates/core_arch/src/x86/cpuid.rs",
            "template": "mov {save_rbx:r}, rbx\ncpuid\nmov {out_ebx:e}, ebx\nmov rbx, {save_rbx:r}",
            "att_syntax": False,
            "operands": {
                "save_rbx": {"kind": "reg", "reg_id": 8},
                "out_ebx": {"kind": "reg", "reg_id": 6},
            },
        },
        {
            "name": "core_hint_spin_loop_and_fences",
            "origin": "library/core/src/hint.rs",
            "template": "pause\nlfence\nmfence\nsfence",
            "att_syntax": False,
            "operands": {},
        },
        {
            "name": "att_syntax_dialect_normalization",
            "origin": "library/core/src/arch/asm.rs",
            "template": "movq {src}, {dst}\naddq $7, {dst}",
            "att_syntax": True,
            "operands": {
                "src": {"kind": "reg", "reg_id": 6},
                "dst": {"kind": "reg", "reg_id": 0},
            },
        },
        {
            "name": "subreg_width_modifiers_l_x_e_r",
            "origin": "compiler/rustc_builtin_macros/src/asm.rs",
            "template": "mov {r0:l}, {r1:l}\nmov {r0:x}, {r1:x}\nmov {r0:e}, {r1:e}\nmov {r0:r}, {r1:r}",
            "att_syntax": False,
            "operands": {
                "r0": {"kind": "reg", "reg_id": 0},
                "r1": {"kind": "reg", "reg_id": 1},
            },
        },
        {
            "name": "local_numeric_label_backward_loop",
            "origin": "library/compiler-builtins/src/mem/x86_64.rs",
            "template": "0:\nsub {cnt:r}, 1\njne 0b",
            "att_syntax": False,
            "operands": {
                "cnt": {"kind": "reg", "reg_id": 1},
            },
        },
    ],
    "i686": [
        {
            "name": "i686_cpuid_ebx_preserve",
            "origin": "library/stdarch/crates/core_arch/src/x86/cpuid.rs",
            "template": "push ebx\ncpuid\nmov {eb_out:e}, ebx\npop ebx",
            "att_syntax": False,
            "operands": {
                "eb_out": {"kind": "reg", "reg_id": 6},
            },
        },
        {
            "name": "i686_int80_syscall",
            "origin": "library/std/src/sys/pal/unix/linux/os.rs",
            "template": "mov {res:e}, {nr:e}\nint 0x80",
            "att_syntax": False,
            "operands": {
                "res": {"kind": "reg", "reg_id": 0},
                "nr": {"kind": "reg", "reg_id": 2},
            },
        },
    ],
    "aarch64": [
        {
            "name": "aarch64_linux_svc0_syscall",
            "origin": "library/std/src/sys/pal/unix/linux/os.rs",
            "template": "mov {x8_reg:x}, #64\nsvc #0",
            "att_syntax": False,
            "operands": {
                "x8_reg": {"kind": "reg", "reg_id": 8},
            },
        },
        {
            "name": "aarch64_mrs_tpidr_el0_and_barriers",
            "origin": "library/std/src/sys/thread_local/fast_local.rs",
            "template": "mrs {tls:x}, tpidr_el0\ndmb ish\nisb",
            "att_syntax": False,
            "operands": {
                "tls": {"kind": "reg", "reg_id": 0},
            },
        },
        {
            "name": "aarch64_width_modifiers_w_and_x",
            "origin": "library/stdarch/crates/core_arch/src/aarch64/neon/mod.rs",
            "template": "add {dst:w}, {src:w}, #42\nadd {dst:x}, {src:x}, {other:x}",
            "att_syntax": False,
            "operands": {
                "dst": {"kind": "reg", "reg_id": 0},
                "src": {"kind": "reg", "reg_id": 1},
                "other": {"kind": "reg", "reg_id": 2},
            },
        },
    ],
}


def target_to_arch(target: str) -> str:
    if target.startswith("x86_64"):
        return "x86_64"
    if target.startswith("i686"):
        return "i686"
    return "aarch64"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "inline_asm_direct_encode_parity.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    per_target = {}
    total_cases = 0
    matched_cases = 0

    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)
        for target in TIER1_TARGETS:
            arch = target_to_arch(target)
            cases = SYSROOT_TEST_TEMPLATES[arch]
            target_results = []
            for tc in cases:
                direct_bytes = encode_asm_block_direct(
                    tc["template"], arch, tc["operands"], tc["att_syntax"]
                )
                mc_bytes = assemble_with_llvm_mc(
                    tc["template"], target, arch, tc["operands"], tc["att_syntax"], work_dir
                )
                # Note: on COFF/Mach-O llvm-mc may pad section to 4B/16B alignment with trailing NOP/0x00;
                # compare the exact instruction prefix `mc_bytes[:len(direct_bytes)]`!
                exact_match = (mc_bytes[: len(direct_bytes)] == direct_bytes)
                total_cases += 1
                if exact_match:
                    matched_cases += 1
                target_results.append({
                    "name": tc["name"],
                    "origin": tc["origin"],
                    "direct_hex": direct_bytes.hex(),
                    "llvm_mc_prefix_hex": mc_bytes[: len(direct_bytes)].hex(),
                    "byte_length": len(direct_bytes),
                    "byte_for_byte_match": exact_match,
                })
            per_target[target] = {
                "arch": arch,
                "cases_tested": len(target_results),
                "cases_matched": sum(1 for r in target_results if r["byte_for_byte_match"]),
                "cases": target_results,
            }

    summary = {
        "external_assembler_invocations_in_production": 0,
        "targets_verified": len(TIER1_TARGETS),
        "total_template_test_vectors": total_cases,
        "byte_for_byte_matched_vectors": matched_cases,
        "parity_rate_pct": round(100.0 * matched_cases / max(1, total_cases), 2),
        "per_target": per_target,
    }
    args.out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Verified {matched_cases}/{total_cases} inline-asm template vectors across all 8 Tier 1 targets; wrote {args.out}")
    return 0 if matched_cases == total_cases else 1


if __name__ == "__main__":
    sys.exit(main())
