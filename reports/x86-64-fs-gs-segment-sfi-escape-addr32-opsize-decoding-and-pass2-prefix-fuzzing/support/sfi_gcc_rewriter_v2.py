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
assembly rewriter v2 (`sfi_gcc_rewriter_v2.py`).

Upgrades over v1 (`sfi_gcc_rewriter.py`):
  1. Supports stock `gcc 15.2.0 -O2 -fPIC -fstack-protector-strong` /
     `-fstack-protector-all` (`%fs:40` / `%fs:0x28` + `__stack_chk_fail@PLT`)
     in addition to `-fno-stack-protector`:
       - `arena_guarded` mode (default): lowers `%fs:40` / `%fs:0x28` prologue
         loads and epilogue `subq`/`xorq`/`cmpq` checks to a loader-managed
         `PROT_READ` canary page inside the 4 GiB SFI arena (`canary_arena_off =
         0xFE28` in `[arenaBase + 0xF000, arenaBase + 0x10000)`), and lowers
         `call __stack_chk_fail@PLT` to `movabsq $0xBADCA028DEAD0001, %rax;
         jmp __sfi_portal_exit` (aborting immediately to the Rust host via
         Portal 0 without reading any corrupted guest stack slot or killing the
         host process).
       - `strip` mode: elides `%fs:40` canary loads/checks when intra-sandbox
         stack frames need no canary check.
  2. Fail-closed prefix hygiene: rejects any non-canary `%fs:` or `%gs:`
     segment override, any `addr32` / 32-bit `(%e..)` effective-address
     operand, and any 16-bit stack/branch override (`pushw`, `popw`, `retw`,
     `leavew`, `data16`, `addr32`), ensuring zero `0x64`/`0x65`/`0x67` or
     `0x66` stack/control-flow bytes enter `.text.sfi`.
  3. 100% untrusted outside the TCB: every emitted `.o` must pass the
     kernel-checked `PicMultiFnSfiV2.checkSfiPicMultiFnV2` byte verifier.
"""

from __future__ import annotations

from dataclasses import dataclass
import re

RODATA_ARENA_OFF = 0x10000
CANARY_ARENA_OFF = 0xFE28
CANARY_ABORT_SENTINEL = 0xBADCA028DEAD0001

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

REG32_TO_64 = {v: k for k, v in REG64_TO_32.items()}

JCC_MNEMONICS = {
    "je", "jne", "jz", "jnz", "jb", "jae", "jbe", "ja",
    "jc", "jnc", "jnb", "jna", "jnae", "jnbe",
    "jl", "jge", "jle", "jg", "js", "jns",
}

ALU_BIN_MNEMONICS = {
    "addq", "addl", "subq", "subl", "xorq", "xorl",
    "andq", "andl", "orq", "orl", "cmpq", "cmpl", "testq", "testl",
}

FORBIDDEN_PREFIX_MNEMONICS = {
    "data16", "addr32", "fs", "gs", "pushw", "popw", "retw", "leavew",
    "jmpw", "callw",
}

FS_CANARY_OPS = {"%fs:40", "%fs:0x28"}


def to_reg32(reg: str) -> str:
    reg = reg.strip()
    return REG64_TO_32.get(reg, reg)


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
    return ("(" in op and ")" in op) or op.startswith(("%fs:", "%gs:"))


MEM_RE = re.compile(r"^([^(]*)\(([^)]*)\)$")


def check_no_forbidden_seg_or_addr32(op: str) -> None:
    s = op.strip()
    if "%gs" in s:
        raise ValueError(f"forbidden %gs segment override in SFI input: {op!r}")
    if "%fs" in s and s not in FS_CANARY_OPS:
        raise ValueError(f"forbidden non-canary %fs segment override in SFI input: {op!r}")
    if "%esp" in s or "%ebp" in s:
        raise ValueError(f"forbidden 32-bit %esp/%ebp address register in SFI input: {op!r}")


def sandbox_addr_setup(mem_op: str) -> tuple[list[str], str]:
    """Lower an AT&T memory operand into RFLAGS-preserving setup + `[r14 + idx]`:
      - `disp(%rsp)` -> `([], f"{disp}(%r14,%r13,1)")` (inductive `r13 < 2^32`)
      - `(%reg)` or `(%reg32)` -> `([f"movl {reg32}, %r11d"], "(%r14,%r11,1)")`
        (eliminating GCC's `0x67` `addr32` prefix on `(uintptr_t)uint32_off`!)
      - `disp(%reg32)` -> `movl %reg32, %r11d; leaq disp(%r11), %r11; movl %r11d, %r11d`
      - `disp(base64,idx64,scale)` -> `leaq` into `%r11` + `movl %r11d, %r11d` + `(%r14,%r11,1)`
    """
    check_no_forbidden_seg_or_addr32(mem_op)
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

    if len(parts) == 1 and parts[0] in REG32_TO_64:
        d_prefix = disp if disp else "0"
        return [
            f"movl {parts[0]}, %r11d",
            f"leaq {d_prefix}(%r11), %r11",
            "movl %r11d, %r11d",
        ], "(%r14,%r11,1)"

    if any(p in REG32_TO_64 for p in parts if p):
        raise ValueError(f"unsupported multi-reg 32-bit addr32 SIB in SFI input: {mem_op!r}")

    # Replace any `%rsp` base/index in multi-part SIB addressing (`(%rsp,%rax,8)`)
    # with guest stack pointer `%r13` so host `%rsp` is never read as a guest offset!
    norm_parts = ["%r13" if p == "%rsp" else p for p in parts]
    norm_mem = f"{disp}({','.join(norm_parts)})"

    if len(norm_parts) == 3 and norm_parts[0] == "":
        d_prefix = disp if disp else "0"
        return [
            "movl $0, %r11d",
            f"leaq {d_prefix}(%r11,{norm_parts[1]},{norm_parts[2]}), %r11",
            "movl %r11d, %r11d",
        ], "(%r14,%r11,1)"

    return [
        f"leaq {norm_mem}, %r11",
        "movl %r11d, %r11d",
    ], "(%r14,%r11,1)"


@dataclass
class RewriteConfigV2:
    code_size_pow2: int = 2048
    rodata_arena_off: int = RODATA_ARENA_OFF
    canary_arena_off: int = CANARY_ARENA_OFF
    canary_mode: str = "arena_guarded"  # "arena_guarded" | "strip"
    canary_abort_sentinel: int = CANARY_ABORT_SENTINEL
    external_hostcall_sym: str = "sfi_hostcall"
    trampoline_sym: str = "sfi_hostcall_trampoline"


def rewrite_gcc_att_to_sfi_v2(asm_src: str, cfg: RewriteConfigV2 | None = None) -> str:
    if cfg is None:
        cfg = RewriteConfigV2()
    if cfg.canary_mode not in ("arena_guarded", "strip"):
        raise ValueError(f"unsupported canary_mode: {cfg.canary_mode!r}")
    assert (cfg.code_size_pow2 & (cfg.code_size_pow2 - 1)) == 0 and cfg.code_size_pow2 >= 128
    code_mask = cfg.code_size_pow2 - 32

    lines = asm_src.splitlines()

    # Pass 1: Separate `.rodata` jump tables from `.text` and collect branch targets.
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
    strip_skip_next_jne = False

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
        if mnem in FORBIDDEN_PREFIX_MNEMONICS:
            raise ValueError(f"forbidden prefix/16-bit/addr32 mnemonic in SFI input: {s!r}")
        arg_str = parts[1].strip() if len(parts) > 1 else ""
        ops = split_operands(arg_str) if arg_str else []
        for op in ops:
            check_no_forbidden_seg_or_addr32(op)

        if strip_skip_next_jne:
            strip_skip_next_jne = False
            if mnem in ("jne", "jnz"):
                continue

        # 0. Stack-protector `%fs:40` / `%fs:0x28` prologue load & epilogue check
        if len(ops) == 2 and ops[0] in FS_CANARY_OPS:
            if mnem == "movq":
                if cfg.canary_mode == "strip":
                    out.append(f"    movl $0, {to_reg32(ops[1])}")
                else:
                    out.extend([
                        "    .bundle_lock",
                        f"    movl ${cfg.canary_arena_off}, %r11d",
                        f"    movq (%r14,%r11,1), {ops[1]}",
                        "    .bundle_unlock",
                    ])
                continue
            if mnem in ("subq", "xorq", "cmpq"):
                if cfg.canary_mode == "strip":
                    out.append(f"    xorl {to_reg32(ops[1])}, {to_reg32(ops[1])}")
                    strip_skip_next_jne = True
                else:
                    out.extend([
                        "    .bundle_lock",
                        f"    movl ${cfg.canary_arena_off}, %r11d",
                        "    movq (%r14,%r11,1), %r11",
                        "    .bundle_unlock",
                        f"    {mnem} %r11, {ops[1]}",
                    ])
                continue
            raise ValueError(f"unsupported %fs:40 stack-protector instruction: {s!r}")

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

        # 2. Direct / GOT-relaxed `call` (including `__stack_chk_fail@PLT`)
        if mnem == "call":
            raw_tgt = arg_str.lstrip("*")
            sym = raw_tgt.split("@", 1)[0].split("(", 1)[0].strip()
            if sym == "__stack_chk_fail":
                out.extend([
                    f"    movabsq ${cfg.canary_abort_sentinel}, %rax",
                    "    jmp __sfi_portal_exit",
                ])
                continue
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

            raise ValueError(f"unhandled memory instruction in SFI rewriter v2: {s!r}")

        # 8. Pure register/branch instruction (`salq` -> `shlq` canonicalization)
        if mnem == "salq":
            s = "shlq " + arg_str
        out.append("    " + s)

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
