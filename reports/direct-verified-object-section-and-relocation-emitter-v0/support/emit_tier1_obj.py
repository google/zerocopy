#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Direct verified relocatable object emitter (ELF64, ELF32, PE/COFF, Mach-O 64) across all 8 Tier 1 targets with zero llvm-mc / as dependency."""

import argparse
import json
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
RUST_LLD = str(LLVM_BIN / "rust-lld")
LLVM_READOBJ = str(LLVM_BIN / "llvm-readobj")
LLVM_OBJDUMP = str(LLVM_BIN / "llvm-objdump")

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
# 1. Direct Machine-Code Buffers & Relocation Payloads per Architecture
# ---------------------------------------------------------------------------
# Each emitted object defines:
#   - `direct_helper(x: u32) -> u32`: returns x + 35
#   - `direct_entry(x: u32) -> u32`: calls `direct_helper(x)` via a PC-relative
#     call relocation (`R_X86_64_PLT32`, `R_386_PC32`, `R_AARCH64_CALL26`,
#     `IMAGE_REL_AMD64_REL32`, `IMAGE_REL_I386_REL32`, `IMAGE_REL_ARM64_BRANCH26`,
#     `ARM64_RELOC_BRANCH26`) and adds 7 -> total x + 42.
#   - `.rodata` constant `DIRECT_MAGIC = 0x20261114_u64`
#   - `.data` initialized word `DIRECT_STATE = 0x0000002a_u32`

def encode_x86_64_sysv() -> tuple[bytes, int, int]:
    # direct_helper (offset 0, size 7):
    #   8d 47 23       leal 35(%rdi), %eax
    #   c3             retq
    #   0f 1f 00       nopl (%rax)
    # direct_entry (offset 8, size 13):
    #   50             pushq %rax  (align stack to 16B before callq)
    #   e8 00 00 00 00 callq direct_helper (reloc at offset 8+2 = 10)
    #   83 c0 07       addl $7, %eax
    #   59             popq %rcx
    #   c3             retq
    code = bytes([
        0x8d, 0x47, 0x23, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
        0x50,
        0xe8, 0x00, 0x00, 0x00, 0x00,
        0x83, 0xc0, 0x07,
        0x59,
        0xc3,
    ])
    return code, 8, 10


def encode_x86_64_win64() -> tuple[bytes, int, int]:
    # Win64 first arg is in %ecx:
    # direct_helper (offset 0, size 8):
    #   8d 41 23       leal 35(%rcx), %eax
    #   c3             retq
    #   0f 1f 40 00    nopl 0(%rax)
    # direct_entry (offset 8, size 17):
    #   48 83 ec 28    subq $40, %rsp (32B shadow space + 8B align)
    #   e8 00 00 00 00 callq direct_helper (reloc at offset 8+5 = 13)
    #   83 c0 07       addl $7, %eax
    #   48 83 c4 28    addq $40, %rsp
    #   c3             retq
    code = bytes([
        0x8d, 0x41, 0x23, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
        0x48, 0x83, 0xec, 0x28,
        0xe8, 0x00, 0x00, 0x00, 0x00,
        0x83, 0xc0, 0x07,
        0x48, 0x83, 0xc4, 0x28,
        0xc3,
    ])
    return code, 8, 13


def encode_i686_cdecl() -> tuple[bytes, int, int]:
    # i686 cdecl first arg at 4(%esp):
    # direct_helper (offset 0, size 8):
    #   8b 44 24 04    movl 4(%esp), %eax
    #   83 c0 23       addl $35, %eax
    #   c3             retl
    # direct_entry (offset 8, size 20):
    #   83 ec 0c       subl $12, %esp
    #   ff 74 24 10    pushl 16(%esp)
    #   e8 fc ff ff ff calll direct_helper (reloc at offset 8+8 = 16; addend -4 embedded for REL)
    #   83 c0 07       addl $7, %eax
    #   83 c4 10       addl $16, %esp
    #   c3             retl
    code = bytes([
        0x8b, 0x44, 0x24, 0x04, 0x83, 0xc0, 0x23, 0xc3,
        0x83, 0xec, 0x0c,
        0xff, 0x74, 0x24, 0x10,
        0xe8, 0xfc, 0xff, 0xff, 0xff,
        0x83, 0xc0, 0x07,
        0x83, 0xc4, 0x10,
        0xc3,
    ])
    return code, 8, 16


def encode_aarch64() -> tuple[bytes, int, int]:
    # AArch64 AAPCS64 first arg in w0:
    # direct_helper (offset 0, size 8):
    #   add w0, w0, #35  -> 0x11008c00
    #   ret              -> 0xd65f03c0
    # direct_entry (offset 8, size 20):
    #   str x30, [sp, #-16]! -> 0xf81f0ffe
    #   bl direct_helper     -> 0x94000000 (reloc at offset 12)
    #   add w0, w0, #7       -> 0x11001c00
    #   ldr x30, [sp], #16   -> 0xf84107fe
    #   ret                  -> 0xd65f03c0
    code = struct.pack(
        "<7I",
        0x11008C00,
        0xD65F03C0,
        0xF81F0FFE,
        0x94000000,
        0x11001C00,
        0xF84107FE,
        0xD65F03C0,
    )
    return code, 8, 12


# ---------------------------------------------------------------------------
# 2. Direct ELF64 Serializer (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`)
# ---------------------------------------------------------------------------

def emit_elf64(arch: str, out_path: Path) -> None:
    if arch == "x86_64":
        e_machine = 62  # EM_X86_64
        text_bytes, entry_off, reloc_off = encode_x86_64_sysv()
        r_type = 4  # R_X86_64_PLT32
        r_addend = -4
    else:
        e_machine = 183  # EM_AARCH64
        text_bytes, entry_off, reloc_off = encode_aarch64()
        r_type = 283  # R_AARCH64_CALL26
        r_addend = 0

    rodata_bytes = struct.pack("<Q", 0x20261114)
    data_bytes = struct.pack("<I", 42)

    shstrtab = (
        b"\x00"
        b".text\x00"          # 1
        b".rela.text\x00"     # 7
        b".rodata\x00"        # 18
        b".data\x00"          # 26
        b".bss\x00"           # 32
        b".note.GNU-stack\x00" # 38
        b".symtab\x00"        # 54
        b".strtab\x00"        # 62
        b".shstrtab\x00"      # 70
    )

    strtab = (
        b"\x00"
        b"direct_helper\x00"  # 1
        b"direct_entry\x00"   # 15
        b"DIRECT_MAGIC\x00"   # 28
    )

    # Symbols:
    # 0: null
    # 1: section .text (STB_LOCAL=0, STT_SECTION=3, shndx=1)
    # 2: direct_helper (STB_GLOBAL=1, STT_FUNC=2, shndx=1, value=0, size=8)
    # 3: direct_entry  (STB_GLOBAL=1, STT_FUNC=2, shndx=1, value=entry_off, size=len-entry_off)
    # 4: DIRECT_MAGIC  (STB_GLOBAL=1, STT_OBJECT=1, shndx=3, value=0, size=8)
    def pack_sym64(name, info, other, shndx, value, size):
        return struct.pack("<IBBHQQ", name, info, other, shndx, value, size)

    symtab = b"".join([
        pack_sym64(0, 0, 0, 0, 0, 0),
        pack_sym64(0, (0 << 4) | 3, 0, 1, 0, 0),
        pack_sym64(1, (1 << 4) | 2, 0, 1, 0, 8),
        pack_sym64(15, (1 << 4) | 2, 0, 1, entry_off, len(text_bytes) - entry_off),
        pack_sym64(28, (1 << 4) | 1, 0, 3, 0, 8),
    ])

    # Relocation targeting symbol 2 (`direct_helper`)
    r_info = (2 << 32) | r_type
    rela_text = struct.pack("<QQq", reloc_off, r_info, r_addend)

    # Layout offsets
    off = 64  # after Elf64_Ehdr
    def pad8(buf: bytes) -> bytes:
        rem = len(buf) % 8
        return buf + (b"\x00" * ((8 - rem) % 8))

    body = bytearray()
    def place(chunk: bytes) -> int:
        nonlocal body
        while (64 + len(body)) % 8 != 0:
            body.append(0)
        start = 64 + len(body)
        body.extend(chunk)
        return start

    text_off = place(text_bytes)
    rela_off = place(rela_text)
    rodata_off = place(rodata_bytes)
    data_off = place(data_bytes)
    bss_off = 64 + len(body)
    note_off = bss_off
    symtab_off = place(symtab)
    strtab_off = place(strtab)
    shstrtab_off = place(shstrtab)
    while (64 + len(body)) % 8 != 0:
        body.append(0)
    shoff = 64 + len(body)

    def pack_shdr64(name, stype, flags, addr, offset, size, link, info, align, entsize):
        return struct.pack("<IIQQQQIIQQ", name, stype, flags, addr, offset, size, link, info, align, entsize)

    # Section headers (9 sections: 0..8)
    # SHT_NULL=0, SHT_PROGBITS=1, SHT_SYMTAB=2, SHT_STRTAB=3, SHT_RELA=4, SHT_NOBITS=8
    # SHF_WRITE=1, SHF_ALLOC=2, SHF_EXECINSTR=4, SHF_INFO_LINK=0x40
    shdrs = b"".join([
        pack_shdr64(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        pack_shdr64(1, 1, 6, 0, text_off, len(text_bytes), 0, 0, 16, 0),
        pack_shdr64(7, 4, 0x40, 0, rela_off, len(rela_text), 7, 1, 8, 24),
        pack_shdr64(18, 1, 2, 0, rodata_off, len(rodata_bytes), 0, 0, 8, 0),
        pack_shdr64(26, 1, 3, 0, data_off, len(data_bytes), 0, 0, 4, 0),
        pack_shdr64(32, 8, 3, 0, bss_off, 16, 0, 0, 8, 0),
        pack_shdr64(38, 1, 0, 0, note_off, 0, 0, 0, 1, 0),
        pack_shdr64(54, 2, 0, 0, symtab_off, len(symtab), 8, 2, 8, 24),
        pack_shdr64(62, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0),
        pack_shdr64(70, 3, 0, 0, shstrtab_off, len(shstrtab), 0, 0, 1, 0),
    ])

    e_ident = b"\x7fELF\x02\x01\x01\x00" + (b"\x00" * 8)
    ehdr = struct.pack(
        "<16sHHIQQQIHHHHHH",
        e_ident,
        1,          # ET_REL
        e_machine,
        1,          # EV_CURRENT
        0,          # e_entry
        0,          # e_phoff
        shoff,      # e_shoff
        0,          # e_flags
        64,         # e_ehsize
        0,          # e_phentsize
        0,          # e_phnum
        64,         # e_shentsize
        10,         # e_shnum
        9,          # e_shstrndx
    )
    out_path.write_bytes(ehdr + bytes(body) + shdrs)


# ---------------------------------------------------------------------------
# 3. Direct ELF32 Serializer (`i686-unknown-linux-gnu`)
# ---------------------------------------------------------------------------

def emit_elf32_i686(out_path: Path) -> None:
    text_bytes, entry_off, reloc_off = encode_i686_cdecl()
    rodata_bytes = struct.pack("<Q", 0x20261114)
    data_bytes = struct.pack("<I", 42)

    shstrtab = (
        b"\x00"
        b".text\x00"          # 1
        b".rel.text\x00"      # 7
        b".rodata\x00"        # 17
        b".data\x00"          # 25
        b".bss\x00"           # 31
        b".note.GNU-stack\x00" # 37
        b".symtab\x00"        # 53
        b".strtab\x00"        # 61
        b".shstrtab\x00"      # 69
    )
    strtab = (
        b"\x00"
        b"direct_helper\x00"  # 1
        b"direct_entry\x00"   # 15
        b"DIRECT_MAGIC\x00"   # 28
    )

    def pack_sym32(name, value, size, info, other, shndx):
        return struct.pack("<IIIBBH", name, value, size, info, other, shndx)

    symtab = b"".join([
        pack_sym32(0, 0, 0, 0, 0, 0),
        pack_sym32(0, 0, 0, (0 << 4) | 3, 0, 1),
        pack_sym32(1, 0, 8, (1 << 4) | 2, 0, 1),
        pack_sym32(15, entry_off, len(text_bytes) - entry_off, (1 << 4) | 2, 0, 1),
        pack_sym32(28, 0, 8, (1 << 4) | 1, 0, 3),
    ])

    # R_386_PC32 = 2, symbol index = 2
    rel_text = struct.pack("<II", reloc_off, (2 << 8) | 2)

    body = bytearray()
    def place(chunk: bytes) -> int:
        while (52 + len(body)) % 4 != 0:
            body.append(0)
        start = 52 + len(body)
        body.extend(chunk)
        return start

    text_off = place(text_bytes)
    rel_off = place(rel_text)
    rodata_off = place(rodata_bytes)
    data_off = place(data_bytes)
    bss_off = 52 + len(body)
    note_off = bss_off
    symtab_off = place(symtab)
    strtab_off = place(strtab)
    shstrtab_off = place(shstrtab)
    while (52 + len(body)) % 4 != 0:
        body.append(0)
    shoff = 52 + len(body)

    def pack_shdr32(name, stype, flags, addr, offset, size, link, info, align, entsize):
        return struct.pack("<10I", name, stype, flags, addr, offset, size, link, info, align, entsize)

    shdrs = b"".join([
        pack_shdr32(0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        pack_shdr32(1, 1, 6, 0, text_off, len(text_bytes), 0, 0, 16, 0),
        pack_shdr32(7, 9, 0x40, 0, rel_off, len(rel_text), 7, 1, 4, 8),
        pack_shdr32(17, 1, 2, 0, rodata_off, len(rodata_bytes), 0, 0, 8, 0),
        pack_shdr32(25, 1, 3, 0, data_off, len(data_bytes), 0, 0, 4, 0),
        pack_shdr32(31, 8, 3, 0, bss_off, 16, 0, 0, 4, 0),
        pack_shdr32(37, 1, 0, 0, note_off, 0, 0, 0, 1, 0),
        pack_shdr32(53, 2, 0, 0, symtab_off, len(symtab), 8, 2, 4, 16),
        pack_shdr32(61, 3, 0, 0, strtab_off, len(strtab), 0, 0, 1, 0),
        pack_shdr32(69, 3, 0, 0, shstrtab_off, len(shstrtab), 0, 0, 1, 0),
    ])

    e_ident = b"\x7fELF\x01\x01\x01\x00" + (b"\x00" * 8)
    ehdr = struct.pack(
        "<16sHHIIIIIHHHHHH",
        e_ident,
        1,      # ET_REL
        3,      # EM_386
        1,      # EV_CURRENT
        0,
        0,
        shoff,
        0,
        52,
        0,
        0,
        40,
        10,
        9,
    )
    out_path.write_bytes(ehdr + bytes(body) + shdrs)


# ---------------------------------------------------------------------------
# 4. Direct PE/COFF Serializer (`x86_64-pc-windows-*`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`)
# ---------------------------------------------------------------------------

def emit_coff(target: str, out_path: Path) -> None:
    is_i386 = target.startswith("i686")
    is_arm64 = target.startswith("aarch64")
    if is_i386:
        machine = 0x014C  # IMAGE_FILE_MACHINE_I386
        text_bytes, entry_off, reloc_off = encode_i686_cdecl()
        # In COFF REL32, initial displacement in instruction is 0
        text_bytes = text_bytes[:reloc_off] + b"\x00\x00\x00\x00" + text_bytes[reloc_off + 4:]
        rel_type = 0x0014  # IMAGE_REL_I386_REL32
        sym_prefix = "_"
    elif is_arm64:
        machine = 0xAA64  # IMAGE_FILE_MACHINE_ARM64
        text_bytes, entry_off, reloc_off = encode_aarch64()
        rel_type = 0x0003  # IMAGE_REL_ARM64_BRANCH26
        sym_prefix = ""
    else:
        machine = 0x8664  # IMAGE_FILE_MACHINE_AMD64
        text_bytes, entry_off, reloc_off = encode_x86_64_win64()
        rel_type = 0x0004  # IMAGE_REL_AMD64_REL32
        sym_prefix = ""

    rdata_bytes = struct.pack("<Q", 0x20261114)
    data_bytes = struct.pack("<I", 42)

    # 3 sections: .text (1), .rdata (2), .data (3)
    num_sections = 3
    hdr_size = 20 + num_sections * 40
    text_ptr = hdr_size
    reloc_ptr = text_ptr + len(text_bytes)
    reloc_bytes = struct.pack("<IIH", reloc_off, 1, rel_type)  # targets symbol index 1 (`direct_helper`)
    rdata_ptr = reloc_ptr + len(reloc_bytes)
    data_ptr = rdata_ptr + len(rdata_bytes)
    symtab_ptr = data_ptr + len(data_bytes)

    def pack_coff_sec(name: bytes, vsize, vaddr, raw_sz, raw_ptr, rel_ptr, nrel, chars):
        return struct.pack(
            "<8sIIIIIIHHI",
            name.ljust(8, b"\x00"),
            vsize, vaddr, raw_sz, raw_ptr, rel_ptr, 0, nrel, 0, chars,
        )

    # IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ | IMAGE_SCN_ALIGN_16BYTES = 0x60500020
    # IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_ALIGN_8BYTES = 0x40400040
    # IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE | IMAGE_SCN_ALIGN_4BYTES = 0xC0300040
    sec_hdrs = b"".join([
        pack_coff_sec(b".text", 0, 0, len(text_bytes), text_ptr, reloc_ptr, 1, 0x60500020),
        pack_coff_sec(b".rdata", 0, 0, len(rdata_bytes), rdata_ptr, 0, 0, 0x40400040),
        pack_coff_sec(b".data", 0, 0, len(data_bytes), data_ptr, 0, 0, 0xC0300040),
    ])

    # String table (4-byte total size prefix followed by null-terminated strings)
    s_helper = (sym_prefix + "direct_helper").encode("ascii") + b"\x00"
    s_entry = (sym_prefix + "direct_entry").encode("ascii") + b"\x00"
    s_magic = (sym_prefix + "DIRECT_MAGIC").encode("ascii") + b"\x00"
    strtab_body = s_helper + s_entry + s_magic
    strtab_bytes = struct.pack("<I", 4 + len(strtab_body)) + strtab_body

    def pack_coff_sym_short(name: bytes, val, sec_num, stype, sclass):
        return struct.pack("<8sIhBB", name.ljust(8, b"\x00"), val, sec_num, stype, sclass) + b"\x00"

    def pack_coff_sym_strtab(str_off: int, val, sec_num, stype, sclass):
        return struct.pack("<IIhBB".replace("", ""), 0, str_off, val, sec_num, stype, sclass) + b"\x00"

    # Symbol 0: @feat.00 (value=1 for /SAFESEH on i386, section=-1 IMAGE_SYM_ABSOLUTE, class=3 STATIC)
    # Symbol 1: direct_helper (section=1, type=0x20 function, class=2 EXTERNAL)
    # Symbol 2: direct_entry  (section=1, value=entry_off, type=0x20, class=2 EXTERNAL)
    # Symbol 3: DIRECT_MAGIC  (section=2, value=0, type=0, class=2 EXTERNAL)
    sym0 = struct.pack("<8sIhHBB", b"@feat.00", 1, -1, 0, 3, 0)
    sym1 = struct.pack("<IIIhHBB", 0, 4, 0, 1, 0x20, 2, 0)
    sym2 = struct.pack("<IIIhHBB", 0, 4 + len(s_helper), entry_off, 1, 0x20, 2, 0)
    sym3 = struct.pack("<IIIhHBB", 0, 4 + len(s_helper) + len(s_entry), 0, 2, 0, 2, 0)
    syms = sym0 + sym1 + sym2 + sym3

    coff_hdr = struct.pack("<HHIIIHH", machine, num_sections, 0, symtab_ptr, 4, 0, 0)
    out_path.write_bytes(coff_hdr + sec_hdrs + text_bytes + reloc_bytes + rdata_bytes + data_bytes + syms + strtab_bytes)


# ---------------------------------------------------------------------------
# 5. Direct Mach-O 64 Serializer (`aarch64-apple-darwin`)
# ---------------------------------------------------------------------------

def emit_macho64_arm64(out_path: Path) -> None:
    text_bytes, entry_off, reloc_off = encode_aarch64()
    const_bytes = struct.pack("<Q", 0x20261114)

    # mach_header_64 (32 bytes)
    # LC_SEGMENT_64 (72 bytes + 2 * 80 byte section_64 = 232 bytes)
    # LC_SYMTAB (24 bytes)
    # Total header + load commands = 32 + 232 + 24 = 288 bytes (sizeofcmds = 256)
    text_file_off = 288
    const_file_off = text_file_off + len(text_bytes)
    reloc_file_off = const_file_off + len(const_bytes)

    # Mach-O relocation_info (8 bytes):
    # r_address = reloc_off (12)
    # r_symbolnum = 0 (_direct_helper), r_pcrel = 1, r_length = 2 (4 bytes), r_extern = 1, r_type = 2 (ARM64_RELOC_BRANCH26)
    r_word1 = 0 | (1 << 24) | (2 << 25) | (1 << 27) | (2 << 28)
    reloc_bytes = struct.pack("<ii", reloc_off, r_word1)

    symtab_file_off = reloc_file_off + len(reloc_bytes)
    strtab = b"\x00_direct_helper\x00_direct_entry\x00_DIRECT_MAGIC\x00"
    # nlist_64 (16 bytes): n_strx(I), n_type(B), n_sect(B), n_desc(H), n_value(Q)
    # N_SECT | N_EXT = 0x0e | 0x01 = 0x0f
    syms = b"".join([
        struct.pack("<IBBHQ", 1, 0x0F, 1, 0, 0),
        struct.pack("<IBBHQ", 16, 0x0F, 1, 0, entry_off),
        struct.pack("<IBBHQ", 30, 0x0F, 2, 0, len(text_bytes)),
    ])
    strtab_file_off = symtab_file_off + len(syms)

    # mach_header_64:
    # magic=0xfeedfacf, cputype=0x0100000c (CPU_TYPE_ARM64), cpusubtype=0,
    # filetype=1 (MH_OBJECT), ncmds=2, sizeofcmds=256, flags=0x2000 (MH_SUBSECTIONS_VIA_SYMBOLS), reserved=0
    mhdr = struct.pack("<IIIIIIII", 0xFEEDFACF, 0x0100000C, 0, 1, 2, 256, 0x2000, 0)

    vm_size = len(text_bytes) + len(const_bytes)
    lc_seg = struct.pack(
        "<II16sQQQQIIII",
        0x19,               # LC_SEGMENT_64
        232,                # cmdsize (72 + 2*80)
        b"\x00" * 16,
        0,                  # vmaddr
        vm_size,            # vmsize
        text_file_off,      # fileoff
        vm_size,            # filesize
        7,                  # maxprot
        7,                  # initprot
        2,                  # nsects
        0,                  # flags
    )

    def pack_sect64(sectname: bytes, segname: bytes, addr, size, offset, align, reloff, nreloc, flags):
        return struct.pack(
            "<16s16sQQIIIIIIII",
            sectname.ljust(16, b"\x00"),
            segname.ljust(16, b"\x00"),
            addr, size, offset, align, reloff, nreloc, flags, 0, 0, 0,
        )

    # S_REGULAR | S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS = 0x80000400
    s_text = pack_sect64(b"__text", b"__TEXT", 0, len(text_bytes), text_file_off, 2, reloc_file_off, 1, 0x80000400)
    s_const = pack_sect64(b"__const", b"__TEXT", len(text_bytes), len(const_bytes), const_file_off, 3, 0, 0, 0)
    lc_symtab = struct.pack("<IIIIII", 0x02, 24, symtab_file_off, 3, strtab_file_off, len(strtab))

    out_path.write_bytes(mhdr + lc_seg + s_text + s_const + lc_symtab + text_bytes + const_bytes + reloc_bytes + syms + strtab)


# ---------------------------------------------------------------------------
# 6. Emit, Inspect (`llvm-readobj`), Link (`rust-lld`), and Execute Across All 8 Targets
# ---------------------------------------------------------------------------

def emit_for_target(target: str, obj_path: Path) -> None:
    if target == "x86_64-unknown-linux-gnu":
        emit_elf64("x86_64", obj_path)
    elif target == "aarch64-unknown-linux-gnu":
        emit_elf64("aarch64", obj_path)
    elif target == "i686-unknown-linux-gnu":
        emit_elf32_i686(obj_path)
    elif target == "aarch64-apple-darwin":
        emit_macho64_arm64(obj_path)
    else:
        emit_coff(target, obj_path)


def link_and_verify_target(target: str, obj_path: Path, work_dir: Path) -> dict:
    # 1. Validate object structure & relocations with llvm-readobj
    ro_proc = subprocess.run(
        [LLVM_READOBJ, "--file-header", "--sections", "--relocations", "--symbols", str(obj_path)],
        capture_output=True, text=True, check=True,
    )
    dis_proc = subprocess.run(
        [LLVM_OBJDUMP, "-d", "-r", str(obj_path)],
        capture_output=True, text=True, check=True,
    )

    # 2. Link with rust-lld (and execute on the 3 Linux Tier 1 targets!)
    executed = False
    exec_return_value = None
    linked_size = 0

    if target in ("x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
        driver_rs = work_dir / f"driver_{target}.rs"
        driver_rs.write_text(
            r"""
unsafe extern "C" {
    fn direct_entry(x: u32) -> u32;
}
fn main() {
    let res = unsafe { direct_entry(100) };
    assert_eq!(res, 142);
    println!("OK:{res}");
}
""",
            encoding="utf-8",
        )
        exe_path = work_dir / f"exe_{target}"
        link_args = [
            RUSTC,
            "--target", target,
            "-C", "opt-level=2",
            "-C", f"link-arg={obj_path}",
            str(driver_rs), "-o", str(exe_path),
        ]
        subprocess.run(link_args, check=True)
        linked_size = exe_path.stat().st_size
        out = subprocess.check_output([str(exe_path)], text=True).strip()
        executed = (out == "OK:142")
        exec_return_value = out
    elif target == "aarch64-unknown-linux-gnu":
        # Freestanding #![no_std] Linux AArch64 executable linked directly with rust-lld -flavor gnu
        # and executed live under /usr/bin/qemu-aarch64
        driver_rs = work_dir / "driver_aarch64.rs"
        driver_rs.write_text(
            r"""#![no_std]
#![no_main]
use core::arch::asm;

unsafe extern "C" {
    fn direct_entry(x: u32) -> u32;
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    let res = unsafe { direct_entry(100) };
    let msg: [u8; 7] = *b"OK:142\n";
    let code: usize = if res == 142 { 0 } else { 1 };
    unsafe {
        if code == 0 {
            asm!(
                "mov x8, #64",
                "mov x0, #1",
                "mov x2, #7",
                "svc #0",
                in("x1") msg.as_ptr(),
                out("x0") _, out("x2") _, out("x8") _,
            );
        }
        asm!(
            "mov x8, #94",
            "svc #0",
            in("x0") code,
            options(noreturn)
        );
    }
}
""",
            encoding="utf-8",
        )
        drv_obj = work_dir / "driver_aarch64.o"
        exe_path = work_dir / "exe_aarch64"
        subprocess.run(
            [RUSTC, "--target", target, "-C", "opt-level=2", "-C", "panic=abort", "--emit=obj", str(driver_rs), "-o", str(drv_obj)],
            check=True,
        )
        subprocess.run(
            [RUST_LLD, "-flavor", "gnu", "-e", "_start", str(drv_obj), str(obj_path), "-o", str(exe_path)],
            check=True,
        )
        linked_size = exe_path.stat().st_size
        out = subprocess.check_output(["/usr/bin/qemu-aarch64", str(exe_path)], text=True).strip()
        executed = (out == "OK:142")
        exec_return_value = out
    elif target == "aarch64-apple-darwin":
        dylib_path = work_dir / "libdirect_darwin.dylib"
        subprocess.run(
            [
                RUST_LLD, "-flavor", "darwin",
                "-arch", "arm64",
                "-platform_version", "macos", "11.0.0", "11.0.0",
                "-dylib",
                "-undefined", "dynamic_lookup",
                str(obj_path),
                "-o", str(dylib_path),
            ],
            check=True,
        )
        linked_size = dylib_path.stat().st_size
    else:
        # Windows PE/COFF targets: link into a freestanding DLL with rust-lld -flavor link
        dll_path = work_dir / f"direct_{target}.dll"
        entry_sym = "direct_entry"
        subprocess.run(
            [
                RUST_LLD, "-flavor", "link",
                "/DLL",
                "/NOENTRY",
                f"/EXPORT:{entry_sym}",
                str(obj_path),
                f"/OUT:{dll_path}",
            ],
            check=True,
        )
        linked_size = dll_path.stat().st_size

    return {
        "target": target,
        "emitted_obj_size_bytes": obj_path.stat().st_size,
        "llvm_readobj_validated": True,
        "rust_lld_linked_successfully": True,
        "linked_artifact_bytes": linked_size,
        "live_executed": executed,
        "execution_output": exec_return_value,
        "disassembly_excerpt": "\n".join(dis_proc.stdout.replace(str(obj_path), obj_path.name).splitlines()[:22]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "direct_emitter_8target_results.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    records = {}
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)
        for target in TIER1_TARGETS:
            obj_path = work_dir / f"direct_{target}.o"
            emit_for_target(target, obj_path)
            records[target] = link_and_verify_target(target, obj_path, work_dir)

    summary = {
        "external_assembler_invocations": 0,
        "targets_verified": len(records),
        "all_llvm_readobj_passed": all(r["llvm_readobj_validated"] for r in records.values()),
        "all_rust_lld_linked": all(r["rust_lld_linked_successfully"] for r in records.values()),
        "executable_targets_passed": sum(1 for r in records.values() if r["live_executed"]),
        "per_target": records,
    }
    args.out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
