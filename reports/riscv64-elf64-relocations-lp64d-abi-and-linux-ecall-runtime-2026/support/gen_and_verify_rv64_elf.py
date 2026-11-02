#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Self-contained RV64GC ELF64 relocatable object generator, linker probe, and
QEMU user-mode execution harness.

Verifies:
1. ELF64 `ET_REL` header (`EM_RISCV = 243`, `e_flags = 0x0005`) and `.symtab`
   local-before-global ordering (`sh_info` invariant), including a negative
   control `.o` rejected by `rust-lld -flavor gnu -m elf64lriscv`.
2. Indirect `R_RISCV_PCREL_LO12_I` (24) / `R_RISCV_PCREL_LO12_S` (25)
   relocations whose `r_sym` references the local `.Lpcrel_hi*` symbol on the
   paired `auipc` (`R_RISCV_PCREL_HI20` = 23), including a negative control `.o`
   whose `R_RISCV_PCREL_LO12_I` points directly to the `.rodata` symbol and is
   rejected by `rust-lld`.
3. Large stack frame (`2,720` bytes = `112` slots, `> 2,047` bytes) materialization
   using `lui` + `addi` sign-extension compensation (`hi20 = (imm + 0x800) >> 12`,
   `lo12 = imm & 0xfff`) and dedicated scratch registers `t3` (`x28`) and `t4`
   (`x29`).
4. Conditional branch relaxation (`beq` inverted over `jal x0, target` spanning
   `4,124` bytes `> 4,094` bytes) and `fence iorw, iorw` (`0x0ff0000f`).
5. `LP64D` `ScalarPair` return in `(a0, a1)`, `R_RISCV_CALL_PLT` (19) cross-function
   call, `.data.rel.ro` 3-word trait-object vtable (`[drop_in_place, 16, 8,
   vtable_method_add]`) populated via `R_RISCV_64` (2), and freestanding Linux
   `riscv64` syscalls (`SYS_mmap = 222`, `SYS_getrandom = 278`, `SYS_write = 64`,
   `SYS_exit = 93`) executed under `qemu-riscv64`.
"""

import hashlib
import json
import os
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path

# ============================================================================
# 1. RV64I / RV64GC 32-Bit Instruction Encoders
# ============================================================================

X0 = 0   # zero
RA = 1   # x1 (caller-saved return address)
SP = 2   # x2 (callee-saved stack pointer, 16-byte aligned)
GP = 3   # x3 (global pointer)
TP = 4   # x4 (thread pointer)
T0 = 5   # x5 (temporary 0)
T1 = 6   # x6 (temporary 1)
T2 = 7   # x7 (temporary 2)
S0 = 8   # x8 / fp (callee-saved frame pointer)
S1 = 9   # x9 (callee-saved)
A0 = 10  # x10 (arg 0 / return 0)
A1 = 11  # x11 (arg 1 / return 1)
A2 = 12  # x12 (arg 2)
A3 = 13  # x13 (arg 3)
A4 = 14  # x14 (arg 4)
A5 = 15  # x15 (arg 5)
A6 = 16  # x16 (arg 6)
A7 = 17  # x17 (arg 7 / Linux syscall number)
T3 = 28  # x28 (large-frame scratch register 0)
T4 = 29  # x29 (large-frame scratch register 1)
T5 = 30  # x30 (temporary 5)
T6 = 31  # x31 (far-branch scratch register)


def enc_r(opcode: int, funct3: int, funct7: int, rd: int, rs1: int, rs2: int) -> bytes:
    w = (
        (opcode & 0x7F)
        | ((rd & 0x1F) << 7)
        | ((funct3 & 0x7) << 12)
        | ((rs1 & 0x1F) << 15)
        | ((rs2 & 0x1F) << 20)
        | ((funct7 & 0x7F) << 25)
    )
    return struct.pack("<I", w)


def enc_i(opcode: int, funct3: int, rd: int, rs1: int, imm12: int) -> bytes:
    w = (
        (opcode & 0x7F)
        | ((rd & 0x1F) << 7)
        | ((funct3 & 0x7) << 12)
        | ((rs1 & 0x1F) << 15)
        | ((imm12 & 0xFFF) << 20)
    )
    return struct.pack("<I", w)


def enc_s(opcode: int, funct3: int, rs1: int, rs2: int, imm12: int) -> bytes:
    imm = imm12 & 0xFFF
    w = (
        (opcode & 0x7F)
        | ((imm & 0x1F) << 7)
        | ((funct3 & 0x7) << 12)
        | ((rs1 & 0x1F) << 15)
        | ((rs2 & 0x1F) << 20)
        | (((imm >> 5) & 0x7F) << 25)
    )
    return struct.pack("<I", w)


def enc_b(opcode: int, funct3: int, rs1: int, rs2: int, imm13: int) -> bytes:
    assert imm13 % 2 == 0 and -4096 <= imm13 <= 4094, f"B-type overflow: {imm13}"
    imm = imm13 & 0x1FFF
    b11 = (imm >> 11) & 1
    b4_1 = (imm >> 1) & 0xF
    b10_5 = (imm >> 5) & 0x3F
    b12 = (imm >> 12) & 1
    w = (
        (opcode & 0x7F)
        | (b11 << 7)
        | (b4_1 << 8)
        | ((funct3 & 0x7) << 12)
        | ((rs1 & 0x1F) << 15)
        | ((rs2 & 0x1F) << 20)
        | (b10_5 << 25)
        | (b12 << 31)
    )
    return struct.pack("<I", w)


def enc_u(opcode: int, rd: int, imm20: int) -> bytes:
    w = (opcode & 0x7F) | ((rd & 0x1F) << 7) | ((imm20 & 0xFFFFF) << 12)
    return struct.pack("<I", w)


def enc_j(opcode: int, rd: int, imm21: int) -> bytes:
    assert imm21 % 2 == 0 and -1048576 <= imm21 <= 1048574, f"J-type overflow: {imm21}"
    imm = imm21 & 0x1FFFFF
    b19_12 = (imm >> 12) & 0xFF
    b11 = (imm >> 11) & 1
    b10_1 = (imm >> 1) & 0x3FF
    b20 = (imm >> 20) & 1
    w = (
        (opcode & 0x7F)
        | ((rd & 0x1F) << 7)
        | (b19_12 << 12)
        | (b11 << 20)
        | (b10_1 << 21)
        | (b20 << 31)
    )
    return struct.pack("<I", w)


# Convenience instruction builders
def rv_nop() -> bytes:
    return enc_i(0x13, 0x0, X0, X0, 0)


def rv_addi(rd: int, rs1: int, imm12: int) -> bytes:
    return enc_i(0x13, 0x0, rd, rs1, imm12)


def rv_add(rd: int, rs1: int, rs2: int) -> bytes:
    return enc_r(0x33, 0x0, 0x00, rd, rs1, rs2)


def rv_xor(rd: int, rs1: int, rs2: int) -> bytes:
    return enc_r(0x33, 0x4, 0x00, rd, rs1, rs2)


def rv_lui(rd: int, imm20: int) -> bytes:
    return enc_u(0x37, rd, imm20)


def rv_auipc(rd: int, imm20: int) -> bytes:
    return enc_u(0x17, rd, imm20)


def rv_ld(rd: int, rs1: int, imm12: int) -> bytes:
    return enc_i(0x03, 0x3, rd, rs1, imm12)


def rv_sd(rs2: int, rs1: int, imm12: int) -> bytes:
    return enc_s(0x23, 0x3, rs1, rs2, imm12)


def rv_beq(rs1: int, rs2: int, imm13: int) -> bytes:
    return enc_b(0x63, 0x0, rs1, rs2, imm13)


def rv_bne(rs1: int, rs2: int, imm13: int) -> bytes:
    return enc_b(0x63, 0x1, rs1, rs2, imm13)


def rv_jal(rd: int, imm21: int) -> bytes:
    return enc_j(0x6F, rd, imm21)


def rv_jalr(rd: int, rs1: int, imm12: int) -> bytes:
    return enc_i(0x67, 0x0, rd, rs1, imm12)


def rv_ret() -> bytes:
    return rv_jalr(X0, RA, 0)


def rv_ecall() -> bytes:
    return enc_i(0x73, 0x0, X0, X0, 0)


def rv_fence_iorw() -> bytes:
    # opcode = 0x0f (MISC-MEM), funct3 = 0, rd = x0, rs1 = x0,
    # fm = 0, pred = 0xf (iorw), succ = 0xf (iorw) -> imm12 = 0x0ff -> 0x0ff0000f
    return enc_i(0x0F, 0x0, X0, X0, 0x0FF)


def split_hi20_lo12(imm: int) -> tuple[int, int]:
    """Compensated 32-bit signed immediate split for `lui` + `addi`/`ld`/`sd`:
    `hi20 = ((imm + 0x800) >> 12) & 0xfffff`, `lo12 = imm & 0xfff` (signed in [-2048, 2047]).
    """
    hi20 = ((imm + 0x800) >> 12) & 0xFFFFF
    lo12_u = imm & 0xFFF
    lo12_s = lo12_u - 0x1000 if lo12_u >= 0x800 else lo12_u
    # Verify exact mathematical reconstruction in signed 32-bit arithmetic:
    hi_signed = hi20 - 0x100000 if hi20 >= 0x80000 else hi20
    assert (hi_signed << 12) + lo12_s == imm
    return hi20, lo12_s


def emit_large_offset_add(scratch: int, base: int, offset: int) -> bytes:
    """Materialize `scratch = base + offset` for any 32-bit signed `offset`
    using `lui scratch, hi20; addi scratch, scratch, lo12; add scratch, base, scratch`."""
    hi20, lo12 = split_hi20_lo12(offset)
    return rv_lui(scratch, hi20) + rv_addi(scratch, scratch, lo12) + rv_add(scratch, base, scratch)


# ============================================================================
# 2. ELF64 `ET_REL` Object Builder (`EM_RISCV = 243`, `e_flags = 0x0005`)
# ============================================================================

ET_REL = 1
EM_RISCV = 243
EF_RISCV_RVC = 0x0001
EF_RISCV_FLOAT_ABI_DOUBLE = 0x0004

SHT_NULL = 0
SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHT_STRTAB = 3
SHT_RELA = 4

SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHF_INFO_LINK = 0x40

STB_LOCAL = 0
STB_GLOBAL = 1

STT_NOTYPE = 0
STT_OBJECT = 1
STT_FUNC = 2
STT_SECTION = 3

R_RISCV_64 = 2
R_RISCV_CALL_PLT = 19
R_RISCV_PCREL_HI20 = 23
R_RISCV_PCREL_LO12_I = 24
R_RISCV_PCREL_LO12_S = 25


def pack_elf64_sym(
    name_off: int, bind: int, sym_type: int, shndx: int, value: int, size: int
) -> bytes:
    st_info = ((bind & 0xF) << 4) | (sym_type & 0xF)
    return struct.pack("<IBBHQQ", name_off, st_info, 0, shndx, value, size)


def pack_elf64_rela(offset: int, sym_idx: int, r_type: int, addend: int) -> bytes:
    r_info = ((sym_idx & 0xFFFFFFFF) << 32) | (r_type & 0xFFFFFFFF)
    return struct.pack("<QQq", offset, r_info, addend)


def pack_elf64_shdr(
    name: int,
    sh_type: int,
    flags: int,
    addr: int,
    offset: int,
    size: int,
    link: int,
    info: int,
    addralign: int,
    entsize: int,
) -> bytes:
    return struct.pack(
        "<IIQQQQIIQQ",
        name,
        sh_type,
        flags,
        addr,
        offset,
        size,
        link,
        info,
        addralign,
        entsize,
    )


class StrTab:
    def __init__(self) -> None:
        self.buf = bytearray(b"\x00")

    def add(self, s: str) -> int:
        off = len(self.buf)
        self.buf.extend(s.encode("ascii") + b"\x00")
        return off


def build_elf64_object(
    text_bytes: bytes,
    rodata_bytes: bytes,
    data_rel_ro_bytes: bytes,
    symbols: list[tuple[str, int, int, int, int, int]],
    rela_text: list[tuple[int, int, int, int]],
    rela_data_rel_ro: list[tuple[int, int, int, int]],
    symtab_sh_info_override: int | None = None,
) -> bytes:
    """Assemble a complete ELF64 `ET_REL` object file (`EM_RISCV = 243`).

    Sections:
      0: NULL
      1: .text
      2: .rodata
      3: .data.rel.ro
      4: .rela.text
      5: .rela.data.rel.ro
      6: .symtab
      7: .strtab
      8: .shstrtab
    """
    shstr = StrTab()
    sh_text_name = shstr.add(".text")
    sh_rodata_name = shstr.add(".rodata")
    sh_data_rel_ro_name = shstr.add(".data.rel.ro")
    sh_rela_text_name = shstr.add(".rela.text")
    sh_rela_data_name = shstr.add(".rela.data.rel.ro")
    sh_symtab_name = shstr.add(".symtab")
    sh_strtab_name = shstr.add(".strtab")
    sh_shstrtab_name = shstr.add(".shstrtab")

    strtab = StrTab()
    sym_entries = [pack_elf64_sym(0, STB_LOCAL, STT_NOTYPE, 0, 0, 0)]  # index 0: STN_UNDEF
    first_non_local = 1
    seen_non_local = False
    for idx, (name, bind, stype, shndx, val, sz) in enumerate(symbols, start=1):
        name_off = strtab.add(name) if name else 0
        sym_entries.append(pack_elf64_sym(name_off, bind, stype, shndx, val, sz))
        if bind == STB_LOCAL and not seen_non_local:
            first_non_local = idx + 1
        else:
            seen_non_local = True

    symtab_sh_info = (
        symtab_sh_info_override if symtab_sh_info_override is not None else first_non_local
    )

    symtab_bytes = b"".join(sym_entries)
    rela_text_bytes = b"".join(pack_elf64_rela(*r) for r in rela_text)
    rela_data_bytes = b"".join(pack_elf64_rela(*r) for r in rela_data_rel_ro)
    strtab_bytes = bytes(strtab.buf)
    shstrtab_bytes = bytes(shstr.buf)

    out = bytearray(64)  # space for Elf64_Ehdr

    def append_aligned(blob: bytes, align: int) -> int:
        while len(out) % align != 0:
            out.append(0)
        off = len(out)
        out.extend(blob)
        return off

    text_off = append_aligned(text_bytes, 4)
    rodata_off = append_aligned(rodata_bytes, 8)
    data_rel_ro_off = append_aligned(data_rel_ro_bytes, 8)
    rela_text_off = append_aligned(rela_text_bytes, 8)
    rela_data_off = append_aligned(rela_data_bytes, 8)
    symtab_off = append_aligned(symtab_bytes, 8)
    strtab_off = append_aligned(strtab_bytes, 1)
    shstrtab_off = append_aligned(shstrtab_bytes, 1)

    while len(out) % 8 != 0:
        out.append(0)
    shoff = len(out)

    shdrs = [
        pack_elf64_shdr(0, SHT_NULL, 0, 0, 0, 0, 0, 0, 0, 0),
        pack_elf64_shdr(
            sh_text_name,
            SHT_PROGBITS,
            SHF_ALLOC | SHF_EXECINSTR,
            0,
            text_off,
            len(text_bytes),
            0,
            0,
            4,
            0,
        ),
        pack_elf64_shdr(
            sh_rodata_name,
            SHT_PROGBITS,
            SHF_ALLOC,
            0,
            rodata_off,
            len(rodata_bytes),
            0,
            0,
            8,
            0,
        ),
        pack_elf64_shdr(
            sh_data_rel_ro_name,
            SHT_PROGBITS,
            SHF_ALLOC | SHF_WRITE,
            0,
            data_rel_ro_off,
            len(data_rel_ro_bytes),
            0,
            0,
            8,
            0,
        ),
        pack_elf64_shdr(
            sh_rela_text_name,
            SHT_RELA,
            SHF_INFO_LINK,
            0,
            rela_text_off,
            len(rela_text_bytes),
            6,  # sh_link = .symtab
            1,  # sh_info = .text
            8,
            24,
        ),
        pack_elf64_shdr(
            sh_rela_data_name,
            SHT_RELA,
            SHF_INFO_LINK,
            0,
            rela_data_off,
            len(rela_data_bytes),
            6,  # sh_link = .symtab
            3,  # sh_info = .data.rel.ro
            8,
            24,
        ),
        pack_elf64_shdr(
            sh_symtab_name,
            SHT_SYMTAB,
            0,
            0,
            symtab_off,
            len(symtab_bytes),
            7,  # sh_link = .strtab
            symtab_sh_info,
            8,
            24,
        ),
        pack_elf64_shdr(
            sh_strtab_name, SHT_STRTAB, 0, 0, strtab_off, len(strtab_bytes), 0, 0, 1, 0
        ),
        pack_elf64_shdr(
            sh_shstrtab_name,
            SHT_STRTAB,
            0,
            0,
            shstrtab_off,
            len(shstrtab_bytes),
            0,
            0,
            1,
            0,
        ),
    ]
    out.extend(b"".join(shdrs))

    e_ident = b"\x7fELF\x02\x01\x01\x00" + b"\x00" * 8
    ehdr = struct.pack(
        "<16sHHIQQQIHHHHHH",
        e_ident,
        ET_REL,
        EM_RISCV,
        1,
        0,
        0,
        shoff,
        EF_RISCV_RVC | EF_RISCV_FLOAT_ABI_DOUBLE,  # 0x0005
        64,
        0,
        0,
        64,
        len(shdrs),
        8,  # e_shstrndx
    )
    out[:64] = ehdr
    return bytes(out)


# ============================================================================
# 3. Negative Linker Probes (`rust-lld -flavor gnu -m elf64lriscv`)
# ============================================================================


def build_negative_probe_symtab_order() -> bytes:
    """Negative Probe 1: Places a local symbol `.Lpcrel_hi0` (`STB_LOCAL`) after
    a global symbol `_start` (`STB_GLOBAL`) with `sh_info = 1`, violating the
    ELF64 symbol table partition rule."""
    text = rv_addi(A0, X0, 0) + rv_addi(A7, X0, 93) + rv_ecall()
    symbols = [
        ("_start", STB_GLOBAL, STT_FUNC, 1, 0, len(text)),     # index 1 (GLOBAL)
        (".Lpcrel_hi0", STB_LOCAL, STT_NOTYPE, 1, 0, 0),       # index 2 (LOCAL after GLOBAL!)
    ]
    return build_elf64_object(
        text_bytes=text,
        rodata_bytes=b"hello\x00\x00\x00",
        data_rel_ro_bytes=b"",
        symbols=symbols,
        rela_text=[],
        rela_data_rel_ro=[],
        symtab_sh_info_override=1,
    )


def build_negative_probe_direct_lo12() -> bytes:
    """Negative Probe 2: Emits `R_RISCV_PCREL_LO12_I` (24) whose `r_sym` points
    directly to `rodata_banner` (symbol 2) instead of the local `.Lpcrel_hi0`
    symbol at the paired `auipc` instruction (symbol 1)."""
    text = (
        rv_auipc(A1, 0)           # offset 0: R_RISCV_PCREL_HI20 -> rodata_banner
        + rv_addi(A1, A1, 0)      # offset 4: R_RISCV_PCREL_LO12_I -> WRONG r_sym (rodata_banner)
        + rv_addi(A0, X0, 0)
        + rv_addi(A7, X0, 93)
        + rv_ecall()
    )
    symbols = [
        (".Lpcrel_hi0", STB_LOCAL, STT_NOTYPE, 1, 0, 0),       # sym 1: local label at text+0
        ("rodata_banner", STB_LOCAL, STT_OBJECT, 2, 0, 8),     # sym 2: .rodata target
        ("_start", STB_GLOBAL, STT_FUNC, 1, 0, len(text)),     # sym 3: global entry
    ]
    rela_text = [
        (0, 2, R_RISCV_PCREL_HI20, 0),
        (4, 2, R_RISCV_PCREL_LO12_I, 0),  # BUG: points to sym 2 (rodata_banner) instead of sym 1!
    ]
    return build_elf64_object(
        text_bytes=text,
        rodata_bytes=b"hello\x00\x00\x00",
        data_rel_ro_bytes=b"",
        symbols=symbols,
        rela_text=rela_text,
        rela_data_rel_ro=[],
    )


# ============================================================================
# 4. Positive End-to-End `RV64GC` ELF64 Probe (`probe_rv64gc.o`)
# ============================================================================

BANNER_TEXT = b"RV64GC_ELF64_LP64D_VTABLE_LARGE_FRAME_ECALL_VERIFIED_OK\n"
assert len(BANNER_TEXT) == 56


def build_positive_probe_rv64gc() -> bytes:
    """Build `probe_rv64gc.o` exercising:
    - `drop_noop` (offset 0)
    - `vtable_method_add` (offset 4): executes `fence iorw, iorw` (`0x0ff0000f`),
      loads `*data_ptr` (`ld t0, 0(a0)`), adds `bonus` (`add a0, t0, a1`), returns.
    - `callee_with_large_frame` (offset 16):
      - Allocates a 2,720-byte frame (`112` slots, `> 2,047` bytes) via
        `lui t4, hi20(-2720); addi t4, t4, lo12(-2720); add sp, sp, t4`.
      - Saves `ra` at `sp + 2712` and `s0` at `sp + 2704` via `t4`.
      - Stores `a0` at `sp + 2400` via `t4` and reloads it into `t0` via `t3`.
      - Executes a relaxed conditional branch (`beq t0, x0, +8; jal x0, +4128`)
        jumping across `1,030` `nop`s (`4,120` bytes `> 4,094`-byte B-type limit).
      - Returns LP64D `ScalarPair` `(a0 = x + y, a1 = x ^ y)` after restoring
        `ra`, `s0`, and deallocating the `2,720`-byte frame via `t4`.
    - `_start`:
      - Calls `callee_with_large_frame(40, 2)` via `R_RISCV_CALL_PLT` (19).
      - Loads `.data.rel.ro` 3-word vtable (`[drop_noop, 16, 8, vtable_method_add]`)
        via `R_RISCV_PCREL_HI20` (23) + indirect `R_RISCV_PCREL_LO12_I` (24)
        referencing `.Lpcrel_hi_vtable`.
      - Verifies vtable header (`size == 16`, `align == 8`) and invokes `method_0`
        at offset `24(t0)` (`jalr ra, 0(t1)`).
      - Invokes Linux `riscv64` `SYS_mmap` (222), `SYS_getrandom` (278),
        `SYS_write` (64) on `rodata_banner` (loaded via `R_RISCV_PCREL_HI20` +
        indirect `R_RISCV_PCREL_LO12_I` referencing `.Lpcrel_hi_banner`), and
        `SYS_exit` (93) with exit code `0`.
    """
    text = bytearray()
    rela_text: list[tuple[int, int, int, int]] = []

    # Function 1: `drop_noop` at text+0
    off_drop_noop = len(text)
    text.extend(rv_ret())

    # Function 2: `vtable_method_add` at text+4
    off_vtable_method_add = len(text)
    text.extend(
        rv_fence_iorw()          # 0x0ff0000f (fence iorw, iorw)
        + rv_ld(T0, A0, 0)       # t0 = *data_ptr
        + rv_add(A0, T0, A1)     # a0 = t0 + bonus
        + rv_ret()
    )

    # Function 3: `callee_with_large_frame` at text+20
    off_callee_large = len(text)
    frame_size = 2720  # > 2047 (12-bit signed immediate max)
    # Prologue: allocate 2720-byte frame and save ra (sp+2712), s0 (sp+2704)
    text.extend(emit_large_offset_add(T4, SP, -frame_size))
    text.extend(rv_add(SP, T4, X0))
    text.extend(emit_large_offset_add(T4, SP, frame_size - 8))
    text.extend(rv_sd(RA, T4, 0))
    text.extend(emit_large_offset_add(T4, SP, frame_size - 16))
    text.extend(rv_sd(S0, T4, 0))

    # Spill `a0` to deep slot `sp + 2400` (> 2047) using scratch `t4`,
    # then reload into `t0` using scratch `t3`
    text.extend(emit_large_offset_add(T4, SP, 2400))
    text.extend(rv_sd(A0, T4, 0))
    text.extend(emit_large_offset_add(T3, SP, 2400))
    text.extend(rv_ld(T0, T3, 0))

    # Relaxed conditional branch over 1,030 NOPs (4,120 bytes > 4,094-byte B-type limit):
    # Logical branch: `bne t0, x0, target_after_nops`
    # Relaxed form:   `beq t0, x0, +8; jal x0, +4128` (skips 1 instruction + 1030 NOPs + 1 fail insn)
    nop_count = 1030
    jal_disp = 4 + (nop_count * 4) + 4  # 4128 bytes (> 4094!)
    text.extend(rv_beq(T0, X0, 8))
    text.extend(rv_jal(X0, jal_disp))
    for _ in range(nop_count):
        text.extend(rv_nop())
    # Fallthrough if t0 == 0 (unreachable when called with x = 40):
    text.extend(rv_addi(A0, X0, 99))

    # Target of relaxed branch: compute LP64D ScalarPair return (a0 = x + y, a1 = x ^ y)
    text.extend(rv_add(A0, T0, A1))
    text.extend(rv_xor(A1, T0, A1))

    # Epilogue: restore ra, s0, deallocate 2,720-byte frame via `t4`, return
    text.extend(emit_large_offset_add(T4, SP, frame_size - 8))
    text.extend(rv_ld(RA, T4, 0))
    text.extend(emit_large_offset_add(T4, SP, frame_size - 16))
    text.extend(rv_ld(S0, T4, 0))
    text.extend(emit_large_offset_add(T4, SP, frame_size))
    text.extend(rv_add(SP, T4, X0))
    text.extend(rv_ret())

    # Function 4: `_start` (global entry point)
    off_start = len(text)

    # Step 1: Call `callee_with_large_frame(40, 2)` via `R_RISCV_CALL_PLT` (19)
    text.extend(rv_addi(A0, X0, 40))
    text.extend(rv_addi(A1, X0, 2))
    off_call_plt = len(text)
    text.extend(rv_auipc(RA, 0) + rv_jalr(RA, RA, 0))
    # Verify ScalarPair return: a0 == 42 (40 + 2) and a1 == 42 (40 ^ 2)
    text.extend(rv_addi(T0, X0, 42))
    text.extend(rv_beq(A0, T0, 16))
    text.extend(rv_addi(A0, X0, 1) + rv_addi(A7, X0, 93) + rv_ecall())
    text.extend(rv_beq(A1, T0, 16))
    text.extend(rv_addi(A0, X0, 2) + rv_addi(A7, X0, 93) + rv_ecall())

    # Step 2: Allocate a 4096-byte page via Linux `SYS_mmap` (222)
    # mmap(NULL, 4096, PROT_READ|PROT_WRITE=3, MAP_PRIVATE|MAP_ANONYMOUS=0x22, -1, 0)
    text.extend(
        rv_addi(A0, X0, 0)
        + rv_addi(A1, X0, 1024)
        + rv_addi(A2, X0, 3)
        + rv_addi(A3, X0, 0x22)
        + rv_addi(A4, X0, -1)
        + rv_addi(A5, X0, 0)
        + rv_addi(A7, X0, 222)
        + rv_ecall()
    )
    # Save mmap pointer in callee-saved `s1` (`x9`) and store `100` at `0(s1)`
    text.extend(rv_add(S1, A0, X0))
    text.extend(rv_addi(T0, X0, 100))
    text.extend(rv_sd(T0, S1, 0))

    # Step 3: Load 3-word trait-object vtable from `.data.rel.ro` using
    # `R_RISCV_PCREL_HI20` (23) + indirect `R_RISCV_PCREL_LO12_I` (24)
    off_pcrel_hi_vtable = len(text)
    text.extend(rv_auipc(T0, 0))
    off_pcrel_lo_vtable = len(text)
    text.extend(rv_addi(T0, T0, 0))

    # Verify vtable size == 16 at 8(t0) and align == 8 at 16(t0)
    text.extend(rv_ld(T1, T0, 8))
    text.extend(rv_addi(T2, X0, 16))
    text.extend(rv_beq(T1, T2, 16))
    text.extend(rv_addi(A0, X0, 3) + rv_addi(A7, X0, 93) + rv_ecall())

    text.extend(rv_ld(T1, T0, 16))
    text.extend(rv_addi(T2, X0, 8))
    text.extend(rv_beq(T1, T2, 16))
    text.extend(rv_addi(A0, X0, 4) + rv_addi(A7, X0, 93) + rv_ecall())

    # Dynamically dispatch `method_0` (`vtable_method_add`) at offset 24(t0)
    # with `data_ptr = s1` (`*s1 == 100`) and `bonus = 23` -> returns `123`
    text.extend(rv_ld(T1, T0, 24))
    text.extend(rv_add(A0, S1, X0))
    text.extend(rv_addi(A1, X0, 23))
    text.extend(rv_jalr(RA, T1, 0))
    text.extend(rv_addi(T2, X0, 123))
    text.extend(rv_beq(A0, T2, 16))
    text.extend(rv_addi(A0, X0, 5) + rv_addi(A7, X0, 93) + rv_ecall())

    # Step 4: Test S-type indirect relocation `R_RISCV_PCREL_LO12_S` (25) by
    # storing `123` (`a0`) into writable `tls_slot_data` (in `.data.rel.ro` at
    # offset 32) via `auipc t0, 0` (`R_RISCV_PCREL_HI20`) + `sd a0, 0(t0)`
    # (`R_RISCV_PCREL_LO12_S` referencing `.Lpcrel_hi_store`), and reading it
    # via `tp` (`x4`) local-exec thread pointer (`addi tp, t0, ...` / `ld t1, 0(tp)`).
    off_pcrel_hi_store = len(text)
    text.extend(rv_auipc(T0, 0))
    off_pcrel_lo_store = len(text)
    text.extend(rv_sd(A0, T0, 0))

    # Materialize address of `tls_slot_data` into `tp` (`x4`) via `.Lpcrel_hi_tls`
    # and read back `0(tp)` to verify `R_RISCV_PCREL_LO12_S` + `tp`-relative load:
    off_pcrel_hi_tls = len(text)
    text.extend(rv_auipc(TP, 0))
    off_pcrel_lo_tls = len(text)
    text.extend(rv_addi(TP, TP, 0))
    text.extend(rv_ld(T1, TP, 0))
    text.extend(rv_addi(T2, X0, 123))
    text.extend(rv_beq(T1, T2, 16))
    text.extend(rv_addi(A0, X0, 6) + rv_addi(A7, X0, 93) + rv_ecall())

    # Step 5: Invoke `SYS_getrandom` (278) for 8 bytes at `s1 + 64`
    text.extend(
        rv_addi(A0, S1, 64)
        + rv_addi(A1, X0, 8)
        + rv_addi(A2, X0, 0)
        + rv_addi(A7, X0, 278)
        + rv_ecall()
    )
    text.extend(rv_addi(T2, X0, 8))
    text.extend(rv_beq(A0, T2, 16))
    text.extend(rv_addi(A0, X0, 7) + rv_addi(A7, X0, 93) + rv_ecall())

    # Step 6: Load `.rodata` banner via `R_RISCV_PCREL_HI20` (23) + indirect
    # `R_RISCV_PCREL_LO12_I` (24) and write 56 bytes to stdout via `SYS_write` (64)
    off_pcrel_hi_banner = len(text)
    text.extend(rv_auipc(A1, 0))
    off_pcrel_lo_banner = len(text)
    text.extend(rv_addi(A1, A1, 0))
    text.extend(
        rv_addi(A0, X0, 1)
        + rv_addi(A2, X0, len(BANNER_TEXT))
        + rv_addi(A7, X0, 64)
        + rv_ecall()
    )

    # Step 7: Exit cleanly with status 0 via `SYS_exit` (93)
    text.extend(rv_addi(A0, X0, 0) + rv_addi(A7, X0, 93) + rv_ecall())

    # `.data.rel.ro`: 3-word trait-object vtable header + 1 method pointer (32 bytes)
    # followed by an 8-byte writable slot `tls_slot_data` at offset 32 (total 40 bytes):
    # [0]: drop_noop (relocated by R_RISCV_64)
    # [8]: size = 16
    # [16]: align = 8
    # [24]: vtable_method_add (relocated by R_RISCV_64)
    # [32]: tls_slot_data = 0 (written via R_RISCV_PCREL_LO12_S and read via tp)
    data_rel_ro = struct.pack("<QQQQQ", 0, 16, 8, 0, 0)

    # Symbol table: ALL STB_LOCAL symbols MUST precede ALL STB_GLOBAL symbols!
    # Index 0 is STN_UNDEF.
    symbols = [
        # sym 1: local function `drop_noop`
        ("drop_noop", STB_LOCAL, STT_FUNC, 1, off_drop_noop, 4),
        # sym 2: local function `vtable_method_add`
        ("vtable_method_add", STB_LOCAL, STT_FUNC, 1, off_vtable_method_add, 16),
        # sym 3: local function `callee_with_large_frame`
        (
            "callee_with_large_frame",
            STB_LOCAL,
            STT_FUNC,
            1,
            off_callee_large,
            off_start - off_callee_large,
        ),
        # sym 4: local object `rodata_banner` in `.rodata` (shndx = 2)
        ("rodata_banner", STB_LOCAL, STT_OBJECT, 2, 0, len(BANNER_TEXT)),
        # sym 5: local object `trait_vtable` in `.data.rel.ro` (shndx = 3, offset 0)
        ("trait_vtable", STB_LOCAL, STT_OBJECT, 3, 0, 32),
        # sym 6: local object `tls_slot_data` in `.data.rel.ro` (shndx = 3, offset 32)
        ("tls_slot_data", STB_LOCAL, STT_OBJECT, 3, 32, 8),
        # sym 7: local label `.Lpcrel_hi_vtable` at `off_pcrel_hi_vtable` in `.text`
        (".Lpcrel_hi_vtable", STB_LOCAL, STT_NOTYPE, 1, off_pcrel_hi_vtable, 0),
        # sym 8: local label `.Lpcrel_hi_store` at `off_pcrel_hi_store` in `.text`
        (".Lpcrel_hi_store", STB_LOCAL, STT_NOTYPE, 1, off_pcrel_hi_store, 0),
        # sym 9: local label `.Lpcrel_hi_tls` at `off_pcrel_hi_tls` in `.text`
        (".Lpcrel_hi_tls", STB_LOCAL, STT_NOTYPE, 1, off_pcrel_hi_tls, 0),
        # sym 10: local label `.Lpcrel_hi_banner` at `off_pcrel_hi_banner` in `.text`
        (".Lpcrel_hi_banner", STB_LOCAL, STT_NOTYPE, 1, off_pcrel_hi_banner, 0),
        # sym 11: global entry `_start` in `.text` (sh_info = 11!)
        ("_start", STB_GLOBAL, STT_FUNC, 1, off_start, len(text) - off_start),
    ]

    rela_text = [
        # Cross-function call to `callee_with_large_frame` (sym 3)
        (off_call_plt, 3, R_RISCV_CALL_PLT, 0),
        # Paired PC-relative load of `trait_vtable` (sym 5) via `.Lpcrel_hi_vtable` (sym 7)
        (off_pcrel_hi_vtable, 5, R_RISCV_PCREL_HI20, 0),
        (off_pcrel_lo_vtable, 7, R_RISCV_PCREL_LO12_I, 0),
        # Paired PC-relative S-type store to `tls_slot_data` (sym 6) via `.Lpcrel_hi_store` (sym 8)
        (off_pcrel_hi_store, 6, R_RISCV_PCREL_HI20, 0),
        (off_pcrel_lo_store, 8, R_RISCV_PCREL_LO12_S, 0),
        # Paired PC-relative address load of `tls_slot_data` (sym 6) into `tp` via `.Lpcrel_hi_tls` (sym 9)
        (off_pcrel_hi_tls, 6, R_RISCV_PCREL_HI20, 0),
        (off_pcrel_lo_tls, 9, R_RISCV_PCREL_LO12_I, 0),
        # Paired PC-relative load of `rodata_banner` (sym 4) via `.Lpcrel_hi_banner` (sym 10)
        (off_pcrel_hi_banner, 4, R_RISCV_PCREL_HI20, 0),
        (off_pcrel_lo_banner, 10, R_RISCV_PCREL_LO12_I, 0),
    ]

    rela_data_rel_ro = [
        # vtable[0] = drop_noop (sym 1)
        (0, 1, R_RISCV_64, 0),
        # vtable[3] (byte offset 24) = vtable_method_add (sym 2)
        (24, 2, R_RISCV_64, 0),
    ]

    return build_elf64_object(
        text_bytes=bytes(text),
        rodata_bytes=BANNER_TEXT,
        data_rel_ro_bytes=data_rel_ro,
        symbols=symbols,
        rela_text=rela_text,
        rela_data_rel_ro=rela_data_rel_ro,
    )


def find_rust_lld() -> str:
    env_lld = os.environ.get("RUST_LLD")
    if env_lld and Path(env_lld).is_file():
        return env_lld
    for tc in ["+1.93.1", ""]:
        cmd = ["rustc"] + ([tc] if tc else []) + ["--print", "sysroot"]
        res = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if res.returncode == 0:
            candidate = (
                Path(res.stdout.strip())
                / "lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
            )
            if candidate.is_file():
                return str(candidate)
    found = shutil.which("rust-lld") or shutil.which("ld.lld")
    if found:
        return found
    raise RuntimeError("Could not locate rust-lld or ld.lld")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sanitize_output(text: str, work_dir: Path) -> str:
    """Replace temporary or local filesystem prefixes with relative artifact names."""
    return text.replace(str(work_dir) + "/", "").replace(str(work_dir), ".")


def main() -> None:
    support_dir = Path(__file__).resolve().parent
    rust_lld = find_rust_lld()
    llvm_readelf = shutil.which("llvm-readelf-21") or shutil.which("llvm-readelf") or "llvm-readelf"
    llvm_objdump = shutil.which("llvm-objdump-21") or shutil.which("llvm-objdump") or "llvm-objdump"
    qemu_riscv64 = shutil.which("qemu-riscv64") or "qemu-riscv64"

    with tempfile.TemporaryDirectory() as tmp:
        tmp_dir = Path(tmp)

        # 1. Run Negative Probe 1 (.symtab ordering violation)
        neg1_bytes = build_negative_probe_symtab_order()
        neg1_o = tmp_dir / "neg_symtab_order.o"
        neg1_elf = tmp_dir / "neg_symtab_order.elf"
        neg1_o.write_bytes(neg1_bytes)
        res_neg1 = subprocess.run(
            [rust_lld, "-flavor", "gnu", "-m", "elf64lriscv", "-static", "-e", "_start", "neg_symtab_order.o", "-o", "neg_symtab_order.elf"],
            cwd=tmp_dir,
            capture_output=True,
            text=True,
            check=False,
        )
        assert res_neg1.returncode != 0, "Expected rust-lld to reject neg_symtab_order.o"

        # 2. Run Negative Probe 2 (Direct R_RISCV_PCREL_LO12_I r_sym)
        neg2_bytes = build_negative_probe_direct_lo12()
        neg2_o = tmp_dir / "neg_direct_lo12.o"
        neg2_elf = tmp_dir / "neg_direct_lo12.elf"
        neg2_o.write_bytes(neg2_bytes)
        res_neg2 = subprocess.run(
            [rust_lld, "-flavor", "gnu", "-m", "elf64lriscv", "-static", "-e", "_start", "neg_direct_lo12.o", "-o", "neg_direct_lo12.elf"],
            cwd=tmp_dir,
            capture_output=True,
            text=True,
            check=False,
        )
        assert res_neg2.returncode != 0, "Expected rust-lld to reject neg_direct_lo12.o"

    # 3. Build, Link, Inspect, and Execute Positive Probe (`probe_rv64gc.o` -> `probe_rv64gc.elf`)
    pos_o_bytes = build_positive_probe_rv64gc()
    pos_o_path = support_dir / "probe_rv64gc.o"
    pos_elf_path = support_dir / "probe_rv64gc.elf"
    pos_o_path.write_bytes(pos_o_bytes)

    res_link = subprocess.run(
        [
            rust_lld,
            "-flavor",
            "gnu",
            "-m",
            "elf64lriscv",
            "-static",
            "-e",
            "_start",
            "probe_rv64gc.o",
            "-o",
            "probe_rv64gc.elf",
        ],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )

    res_readelf_o = subprocess.run(
        [llvm_readelf, "-h", "-S", "-s", "-r", "probe_rv64gc.o"],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )
    res_objdump_o = subprocess.run(
        [llvm_objdump, "-d", "-r", "--no-show-raw-insn", "probe_rv64gc.o"],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )
    res_readelf_elf = subprocess.run(
        [llvm_readelf, "-h", "-S", "-s", "probe_rv64gc.elf"],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )
    res_objdump_elf = subprocess.run(
        [llvm_objdump, "-d", "--no-show-raw-insn", "probe_rv64gc.elf"],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )
    res_qemu = subprocess.run(
        [qemu_riscv64, "./probe_rv64gc.elf"],
        cwd=support_dir,
        capture_output=True,
        text=True,
        check=True,
    )
    assert res_qemu.stdout.encode("ascii") == BANNER_TEXT
    assert res_qemu.returncode == 0

    def elide_nops(disasm: str) -> str:
        lines = disasm.splitlines()
        out_lines: list[str] = []
        nop_run = 0
        for line in lines:
            if "\tnop" in line or line.strip().endswith("nop"):
                nop_run += 1
                if nop_run <= 3:
                    out_lines.append(line)
                elif nop_run == 4:
                    out_lines.append(
                        "    ... [1027 identical `nop` instructions omitted (4,108 bytes)] ..."
                    )
            else:
                nop_run = 0
                out_lines.append(line)
        return "\n".join(out_lines)

    report_lines = [
        "=== 1. NEGATIVE PROBE A: .symtab STB_LOCAL-After-STB_GLOBAL Rejection ===",
        f"Command: rust-lld -flavor gnu -m elf64lriscv -static -e _start neg_symtab_order.o -o neg_symtab_order.elf",
        f"Exit code: {res_neg1.returncode}",
        f"Stderr:\n{res_neg1.stderr.strip()}",
        "",
        "=== 2. NEGATIVE PROBE B: Direct R_RISCV_PCREL_LO12_I (r_sym -> .rodata) Rejection ===",
        f"Command: rust-lld -flavor gnu -m elf64lriscv -static -e _start neg_direct_lo12.o -o neg_direct_lo12.elf",
        f"Exit code: {res_neg2.returncode}",
        f"Stderr:\n{res_neg2.stderr.strip()}",
        "",
        "=== 3. POSITIVE PROBE: llvm-readelf -h -S -s -r probe_rv64gc.o ===",
        res_readelf_o.stdout.strip(),
        "",
        "=== 4. POSITIVE PROBE: llvm-objdump -d -r probe_rv64gc.o (with 1,030-NOP span elided) ===",
        elide_nops(res_objdump_o.stdout),
        "",
        "=== 5. LINKED EXECUTABLE: llvm-readelf -h -S -s probe_rv64gc.elf ===",
        res_readelf_elf.stdout.strip(),
        "",
        "=== 6. LINKED EXECUTABLE DISASSEMBLY: llvm-objdump -d probe_rv64gc.elf ===",
        elide_nops(res_objdump_elf.stdout),
        "",
        "=== 7. QEMU-RISCV64 EXECUTION: qemu-riscv64 ./probe_rv64gc.elf ===",
        f"Exit code: {res_qemu.returncode}",
        f"Stdout: {res_qemu.stdout.strip()}",
        "",
    ]

    verification_output_path = support_dir / "verification_output.txt"
    verification_output_path.write_text("\n".join(report_lines), encoding="utf-8")

    ledger = {
        "negative_probe_symtab_order": {
            "object_sha256": sha256_bytes(neg1_bytes),
            "object_size_bytes": len(neg1_bytes),
            "lld_exit_code": res_neg1.returncode,
            "lld_stderr": res_neg1.stderr.strip(),
        },
        "negative_probe_direct_lo12": {
            "object_sha256": sha256_bytes(neg2_bytes),
            "object_size_bytes": len(neg2_bytes),
            "lld_exit_code": res_neg2.returncode,
            "lld_stderr": res_neg2.stderr.strip(),
        },
        "positive_probe_rv64gc": {
            "object_file": "support/probe_rv64gc.o",
            "object_sha256": sha256_bytes(pos_o_bytes),
            "object_size_bytes": len(pos_o_bytes),
            "executable_file": "support/probe_rv64gc.elf",
            "executable_sha256": sha256_bytes(pos_elf_path.read_bytes()),
            "executable_size_bytes": pos_elf_path.stat().st_size,
            "lld_exit_code": res_link.returncode,
            "qemu_exit_code": res_qemu.returncode,
            "qemu_stdout": res_qemu.stdout,
        },
    }
    (support_dir / "probe_ledger.json").write_text(
        json.dumps(ledger, indent=2) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
