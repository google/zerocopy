#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
Untrusted stock-`gcc -O2 -S` to 32-byte-bundled PIC Multi-Function x86-64 SFI
assembly rewriter (`sfi_gcc_rewriter.py`).

Design contract:
  - Input: AT&T assembly produced by stock `gcc 15.2.0` with:
      `-O2 -fPIC -fvisibility=hidden -fno-tree-vectorize`
      `-ffixed-rbp -ffixed-rbx -ffixed-r11 -ffixed-r12`
      `-ffixed-r13 -ffixed-r14 -ffixed-r15`
      `-mno-red-zone -fno-stack-protector -fno-unwind-tables`
      `-fno-asynchronous-unwind-tables -fcf-protection=none -S`
  - Register partition:
      `%r15` = read-only 64-bit PIC `code_base`
      `%r14` = read-only 64-bit `arena_base` (`4 GiB` RW + `+-64 KiB` guard)
      `%r13` = 32-bit zero-extended `guest_sp` (`movl`/`addl`/`subl` on `%r13d`)
      `%r11` = reserved SFI address/control-flow macro scratch register
      `%rsp, %rbp, %rbx, %r12` = strictly untouched host registers
  - Trust boundary: 100% untrusted outside the TCB. Every emitted `.o` must pass
    the mechanized `checkSfiPicMultiFn` byte-level verifier before loading.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

RODATA_ARENA_OFF = 0x10000

REG64_TO_32 = {
    "%rax": "%eax",
    "%rcx": "%ecx",
    "%rdx": "%edx",
    "%rbx": "%ebx",
    "%rsi": "%esi",
    "%rdi": "%edi",
    "%rbp": "%ebp",
    "%rsp": "%esp",
    "%r8": "%r8d",
    "%r9": "%r9d",
    "%r10": "%r10d",
    "%r11": "%r11d",
    "%r12": "%r12d",
    "%r13": "%r13d",
    "%r14": "%r14d",
    "%r15": "%r15d",
}

JCC_MNEMONICS = {
    "je", "jne", "jz", "jnz", "jb", "jae", "jbe", "ja",
    "jc", "jnc", "jnb", "jna", "jnae", "jnbe",
    "jl", "jge", "jle", "jg", "js", "jns",
}

ALU_BIN_MNEMONICS = {
    "addq", "addl", "subq", "subl", "xorq", "xorl",
    "andq", "andl", "orq", "orl", "cmpq", "cmpl", "testq", "testl",
}


def to_reg32(reg: str) -> str:
    reg = reg.strip()
    if reg in REG64_TO_32:
        return REG64_TO_32[reg]
    return reg


def split_operands(arg_str: str) -> list[str]:
    ops: list[str] = []
    cur: list[str] = []
    depth = 0
    for ch in arg_str:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            ops.append("".join(cur).strip())
            cur = []
            continue
        cur.append(ch)
    if cur:
        ops.append("".join(cur).strip())
    return ops


def is_mem_operand(op: str) -> bool:
    return "(" in op and ")" in op


MEM_RE = re.compile(r"^([^(]*)\(([^)]*)\)$")


def sandbox_addr_setup(mem_op: str) -> tuple[list[str], str]:
    """
    Lower an AT&T memory operand into zero-flag-clobbering setup instructions
    plus the sandboxed memory operand string:
      - `disp(%rsp)` -> `([], f"{disp}(%r14,%r13,1)")` (uses inductive `r13 < 2^32`)
      - `(%reg)` -> `([f"movl {reg32}, %r11d"], "(%r14,%r11,1)")`
      - `disp(base,idx,scale)` -> `leaq` into `%r11` + `movl %r11d, %r11d` + `(%r14,%r11,1)`
    """
    m = MEM_RE.match(mem_op.strip())
    if not m:
        raise ValueError(f"unrecognized memory operand: {mem_op!r}")
    disp, inner = m.group(1).strip(), m.group(2).strip()
    parts = [p.strip() for p in inner.split(",")]

    if len(parts) == 1 and parts[0] == "%rsp":
        d_prefix = disp if disp else ""
        return [], f"{d_prefix}(%r14,%r13,1)"

    if len(parts) == 1 and not disp and parts[0].startswith("%"):
        r32 = to_reg32(parts[0])
        return [f"movl {r32}, %r11d"], "(%r14,%r11,1)"

    # Handle `disp(,idx,scale)` (SIB `base = none`) by zeroing `%r11d` as base
    if len(parts) == 3 and parts[0] == "":
        d_prefix = disp if disp else "0"
        return [
            "movl $0, %r11d",
            f"leaq {d_prefix}(%r11,{parts[1]},{parts[2]}), %r11",
            "movl %r11d, %r11d",
        ], "(%r14,%r11,1)"

    return [
        f"leaq {mem_op.strip()}, %r11",
        "movl %r11d, %r11d",
    ], "(%r14,%r11,1)"


@dataclass
class RewriteConfig:
    code_size_pow2: int = 2048
    rodata_arena_off: int = RODATA_ARENA_OFF
    external_hostcall_sym: str = "sfi_hostcall"
    trampoline_sym: str = "sfi_hostcall_trampoline"


def rewrite_gcc_att_to_sfi(asm_src: str, cfg: RewriteConfig | None = None) -> str:
    if cfg is None:
        cfg = RewriteConfig()
    assert (cfg.code_size_pow2 & (cfg.code_size_pow2 - 1)) == 0 and cfg.code_size_pow2 >= 128
    code_mask = cfg.code_size_pow2 - 32

    lines = asm_src.splitlines()

    # Pass 1: Separate `.rodata` jump tables from `.text` and collect all branch/jump-table targets.
    in_rodata = False
    rodata_lines: list[str] = []
    text_lines: list[str] = []
    rodata_labels: set[str] = set()
    branch_targets: set[str] = set()
    func_labels: set[str] = set()
    cur_ro_label: str | None = None

    for raw in lines:
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith(".section") and ".rodata" in s:
            in_rodata = True
            continue
        if s == ".text" or (s.startswith(".section") and ".text" in s):
            in_rodata = False
            continue
        if s.startswith(".section") and ".note" in s:
            in_rodata = False
            continue
        if any(
            s.startswith(d)
            for d in (".file", ".ident", ".size", ".p2align", ".align", ".cfi_")
        ):
            continue
        if s.startswith(".type") and "@function" in s:
            fn_name = s.split()[1].rstrip(",")
            func_labels.add(fn_name)
            branch_targets.add(fn_name)
            continue

        if in_rodata:
            if s.endswith(":"):
                lbl = s[:-1].strip()
                rodata_labels.add(lbl)
                cur_ro_label = lbl
                rodata_lines.append(f"{lbl}:")
            elif s.startswith(".long") and cur_ro_label is not None:
                expr = s[len(".long") :].strip()
                # Rewrite `.long .Ltarget-.Ltable` ->
                # `.long (.Ltarget - __sfi_text_start) - (RODATA_OFF + (cur_ro_label - __sfi_rodata_start))`
                lhs = expr.split("-", 1)[0].strip()
                branch_targets.add(lhs)
                rodata_lines.append(
                    f"    .long ({lhs} - __sfi_text_start) - ({cfg.rodata_arena_off} + ({cur_ro_label} - __sfi_rodata_start))"
                )
            else:
                rodata_lines.append("    " + s)
        else:
            text_lines.append(s)
            if not s.endswith(":") and not s.startswith("."):
                parts = s.split(None, 1)
                mnem = parts[0]
                arg = parts[1].strip() if len(parts) > 1 else ""
                if (mnem == "jmp" or mnem in JCC_MNEMONICS or mnem == "call") and not arg.startswith("*"):
                    tgt = arg.split("@", 1)[0].strip()
                    branch_targets.add(tgt)

    # Pass 2: Emit bundled `.text` with Portal 0 (`0x00`), Portal 1 (`0x20`),
    # rewritten instructions, and power-of-2 guard bundle padding.
    out: list[str] = [
        '    .section .text.sfi, "ax", @progbits',
        "    .bundle_align_mode 5",
        "    .p2align 5",
        "    .globl __sfi_text_start",
        "__sfi_text_start:",
        "__sfi_portal_exit:",
        "    ret",
        "    .p2align 5",
        "__sfi_portal_hostcall:",
        f"    jmp {cfg.trampoline_sym}",
        "    .p2align 5",
    ]

    ret_site_id = 0

    for s in text_lines:
        if s.startswith(".globl"):
            out.append("    " + s)
            continue
        if s.endswith(":"):
            lbl = s[:-1].strip()
            if lbl in branch_targets or lbl in func_labels:
                out.append("    .p2align 5")
            out.append(f"{lbl}:")
            continue
        if s.startswith("."):
            continue

        parts = s.split(None, 1)
        mnem = parts[0]
        arg_str = parts[1].strip() if len(parts) > 1 else ""
        ops = split_operands(arg_str) if arg_str else []

        # 1. `ret` -> masked PIC indirect return via `[r14 + r13]` and `%r15`
        if mnem == "ret":
            out.extend([
                "    .bundle_lock",
                "    movl (%r14,%r13,1), %r11d",
                "    addl $8, %r13d",
                f"    andl ${code_mask}, %r11d",
                "    leaq (%r15,%r11,1), %r11",
                "    jmp *%r11",
                "    .bundle_unlock",
            ])
            continue

        # 2. Direct / GOT-relaxed `call` -> bundle-aligned guest-stack call
        if mnem == "call":
            raw_tgt = arg_str.lstrip("*")
            sym = raw_tgt.split("@", 1)[0].split("(", 1)[0].strip()
            ret_lbl = f".Lsfi_callret_{ret_site_id}"
            ret_site_id += 1
            jump_tgt = "__sfi_portal_hostcall" if sym == cfg.external_hostcall_sym else sym
            out.extend([
                "    .bundle_lock",
                "    subl $8, %r13d",
                f"    movl $({ret_lbl} - __sfi_text_start), %r11d",
                "    movq %r11, (%r14,%r13,1)",
                f"    jmp {jump_tgt}",
                "    .bundle_unlock",
                "    .p2align 5",
                f"{ret_lbl}:",
            ])
            continue

        # 3. Indirect `jmp *%reg` -> masked PIC indirect jump
        if mnem == "jmp" and arg_str.startswith("*%"):
            reg = arg_str[1:].strip()
            reg32 = to_reg32(reg)
            out.extend([
                "    .bundle_lock",
                f"    movl {reg32}, %r11d",
                f"    andl ${code_mask}, %r11d",
                "    leaq (%r15,%r11,1), %r11",
                "    jmp *%r11",
                "    .bundle_unlock",
            ])
            continue

        # 4. Stack-pointer arithmetic on `%rsp` -> 32-bit zero-extended `%r13d`
        if mnem in ("subq", "addq") and len(ops) == 2 and ops[1] == "%rsp":
            mnem32 = "subl" if mnem == "subq" else "addl"
            out.append(f"    {mnem32} {ops[0]}, %r13d")
            continue

        # 5. RIP-relative `.rodata` jump-table base `leaq .Ltable(%rip), %dst`
        if mnem == "leaq" and len(ops) == 2 and ops[0].endswith("(%rip)"):
            sym = ops[0][: -len("(%rip)")].strip()
            if sym in rodata_labels:
                dst32 = to_reg32(ops[1])
                out.append(
                    f"    movl $({cfg.rodata_arena_off} + ({sym} - __sfi_rodata_start)), {dst32}"
                )
                continue

        # 6. `leaq disp(,idx,scale), %dst` (SIB `base = none` normalization)
        if mnem == "leaq" and len(ops) == 2 and is_mem_operand(ops[0]):
            m = MEM_RE.match(ops[0])
            assert m is not None
            disp, inner = m.group(1).strip(), m.group(2).strip()
            iparts = [p.strip() for p in inner.split(",")]
            if len(iparts) == 3 and iparts[0] == "":
                d_prefix = disp if disp else "0"
                out.append("    movl $0, %r11d")
                out.append(f"    leaq {d_prefix}(%r11,{iparts[1]},{iparts[2]}), {ops[1]}")
                continue

        # 7. Memory loads / stores / ALU-with-memory
        if mnem != "leaq" and any(is_mem_operand(o) for o in ops):
            if mnem in ("movq", "movl", "movslq") and len(ops) == 2:
                if is_mem_operand(ops[0]):
                    setup, sb_mem = sandbox_addr_setup(ops[0])
                    if not setup:
                        out.append(f"    {mnem} {sb_mem}, {ops[1]}")
                    else:
                        out.extend("    " + ln for ln in setup[:-1])
                        out.append("    .bundle_lock")
                        out.append("    " + setup[-1])
                        out.append(f"    {mnem} {sb_mem}, {ops[1]}")
                        out.append("    .bundle_unlock")
                    continue
                if is_mem_operand(ops[1]):
                    setup, sb_mem = sandbox_addr_setup(ops[1])
                    if not setup:
                        out.append(f"    {mnem} {ops[0]}, {sb_mem}")
                    else:
                        out.extend("    " + ln for ln in setup[:-1])
                        out.append("    .bundle_lock")
                        out.append("    " + setup[-1])
                        out.append(f"    {mnem} {ops[0]}, {sb_mem}")
                        out.append("    .bundle_unlock")
                    continue

            if mnem in ALU_BIN_MNEMONICS and len(ops) == 2:
                is_64 = mnem.endswith("q")
                load_mnem = "movq" if is_64 else "movl"
                tmp_reg = "%r11" if is_64 else "%r11d"
                if is_mem_operand(ops[0]):
                    setup, sb_mem = sandbox_addr_setup(ops[0])
                    if not setup:
                        out.append(f"    {load_mnem} {sb_mem}, {tmp_reg}")
                    else:
                        out.extend("    " + ln for ln in setup[:-1])
                        out.append("    .bundle_lock")
                        out.append("    " + setup[-1])
                        out.append(f"    {load_mnem} {sb_mem}, {tmp_reg}")
                        out.append("    .bundle_unlock")
                    out.append(f"    {mnem} {tmp_reg}, {ops[1]}")
                    continue
                if is_mem_operand(ops[1]):
                    # e.g. `cmpq %rdi, (%rsp)` (AT&T `cmp src1, src2` computes `src2 - src1`!)
                    if not mnem.startswith(("cmp", "test")):
                        raise ValueError(f"unsupported RMW memory ALU instruction: {s!r}")
                    setup, sb_mem = sandbox_addr_setup(ops[1])
                    if not setup:
                        out.append(f"    {load_mnem} {sb_mem}, {tmp_reg}")
                    else:
                        out.extend("    " + ln for ln in setup[:-1])
                        out.append("    .bundle_lock")
                        out.append("    " + setup[-1])
                        out.append(f"    {load_mnem} {sb_mem}, {tmp_reg}")
                        out.append("    .bundle_unlock")
                    out.append(f"    {mnem} {ops[0]}, {tmp_reg}")
                    continue

            raise ValueError(f"unhandled memory instruction in SFI rewriter: {s!r}")

        # 8. Pure register/branch instruction (`salq` -> `shlq` canonicalization)
        out.append("    " + s)

    # Pad `.text.sfi` up to `cfg.code_size_pow2` and terminate the final
    # 32-byte bundle (`cfg.code_size_pow2 - 32 .. cfg.code_size_pow2`) with a
    # 5-byte `jmp __sfi_portal_exit` ending at byte 32 (`off = 27..32`) so no
    # linear instruction stream can fall off `cfg.code_size_pow2`.
    out.extend([
        "    .p2align 5",
        "    .globl __sfi_text_used_end",
        "__sfi_text_used_end:",
        f"    .org __sfi_text_start + {cfg.code_size_pow2 - 32}, 0x90",
        "    .byte 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
        "    .byte 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
        "    .byte 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
        "    .byte 0x0f, 0x1f, 0x00",
        "    .byte 0xe9",
        "    .long __sfi_portal_exit - (. + 4)",
        "    .globl __sfi_text_end",
        "__sfi_text_end:",
    ])

    if rodata_lines:
        out.extend([
            "",
            '    .section .sfi_rodata, "a", @progbits',
            "    .p2align 3",
            "    .globl __sfi_rodata_start",
            "__sfi_rodata_start:",
            *rodata_lines,
            "    .globl __sfi_rodata_end",
            "__sfi_rodata_end:",
        ])

    out.append('    .section .note.GNU-stack,"",@progbits')
    return "\n".join(out) + "\n"
