#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Execute 224 AArch64 scalar, atomic/alignment, trap/constrained-unpredictable,
NEON, and Cryptographic (AES, PMULL, SHA-256, SHA-512, CRC32) vectors on live
qemu-aarch64 11.1.2 (-cpu max and -cpu cortex-a53) and cross-check disassembly
against llvm-mc 21.1.8 and llvm-objdump 21.1.8.

All compilations and QEMU executions run strictly inside
tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import argparse
import json
import struct
import subprocess
import tempfile
from pathlib import Path


def assemble_words(asm_snippets: list[str]) -> list[list[int]]:
    lines = [".text"]
    for idx, snip in enumerate(asm_snippets):
        lines.append(f"__lbl_{idx:03d}:")
        for sub in snip.split(";"):
            lines.append("  " + sub.strip())
    lines.append("__lbl_end:")
    src = "\n".join(lines) + "\n"
    with tempfile.TemporaryDirectory() as td:
        obj = Path(td) / "vecs.o"
        subprocess.run(
            [
                "llvm-mc",
                "--triple=aarch64-unknown-linux-gnu",
                "--mattr=+v8.4a,+aes,+sha2,+sha3,+crc",
                "-filetype=obj",
                "-o",
                str(obj),
            ],
            input=src,
            text=True,
            check=True,
        )
        nm_out = subprocess.check_output(["llvm-nm", "-n", str(obj)], text=True)
        offsets: dict[str, int] = {}
        for ln in nm_out.splitlines():
            parts = ln.split()
            if len(parts) == 3:
                offsets[parts[2]] = int(parts[0], 16)
        bin_p = Path(td) / "vecs.bin"
        subprocess.run(
            ["llvm-objcopy", "-O", "binary", "--only-section=.text", str(obj), str(bin_p)],
            check=True,
        )
        sec_hex = bin_p.read_bytes()
        out: list[list[int]] = []
        for idx in range(len(asm_snippets)):
            s_off = offsets[f"__lbl_{idx:03d}"]
            e_off = offsets["__lbl_end"] if idx + 1 == len(asm_snippets) else offsets[f"__lbl_{idx+1:03d}"]
            chunk = sec_hex[s_off:e_off]
            words = [struct.unpack_from("<I", chunk, k)[0] for k in range(0, len(chunk), 4)]
            out.append(words)
        return out


def build_224_vector_specs() -> list[dict]:
    specs: list[dict] = []

    def add(
        vid: str,
        cat: str,
        desc: str,
        words_or_asm: list[int] | str,
        *,
        expected_model: str = "OK_EXEC",
        x0: int = 0x1122334455667788,
        x1: int = 0x99AABBCCDDEEFF01,
        x2: int = 0x0000000100000002,
        x3: int = 0xFEDCBA9876543210,
        mem_off: int = 0,
        sp_misalign: int = 0,
        nzcv: int = 0,
        mem0: int = 0x0807060504030201,
        mem1: int = 0x100F0E0D0C0B0A09,
        v0: int = 0xFFEEDDCCBBAA99887766554433221100,
        v1: int = 0x0F1E2D3C4B5A69788796A5B4C3D2E1F0,
        v2: int = 0x8040201008040201FF7F3F1F0F070301,
        page_end_adrp: bool = False,
        is_branch_rel: bool = False,
    ) -> None:
        specs.append(
            {
                "id": vid,
                "category": cat,
                "desc": desc,
                "words_or_asm": words_or_asm,
                "expected_model": expected_model,
                "x0": x0,
                "x1": x1,
                "x2": x2,
                "x3": x3,
                "mem_off": mem_off,
                "sp_misalign": sp_misalign,
                "nzcv": nzcv,
                "mem0": mem0,
                "mem1": mem1,
                "v0": v0,
                "v1": v1,
                "v2": v2,
                "page_end_adrp": page_end_adrp,
                "is_branch_rel": is_branch_rel,
            }
        )

    # =========================================================================
    # Category A: 32 Fault, Unallocated & Constrained-Unpredictable Vectors
    # =========================================================================
    udf_unalloc = [
        ("a00_udf_0", [0x00000000], "FAULT_UNDEFINED", "UDF #0 permanently undefined"),
        ("a01_udf_ffff", [0x0000FFFF], "FAULT_UNDEFINED", "UDF #65535 permanently undefined"),
        ("a02_udf_dead", [0x0000DEAD], "FAULT_UNDEFINED", "UDF #0xdead permanently undefined"),
        ("a03_add_ror_resv", [0x0BCA0420], "FAULT_UNDEFINED", "ADD W0,W1,W2,ROR #1 (shift=11 reserved)"),
        ("a04_add_w_sh32", [0x0B028020], "FAULT_UNDEFINED", "ADD W0,W1,W2,LSL #32 (sf=0 imm6>=32)"),
        ("a05_sub_ext_imm5", [0xCB221420], "FAULT_UNDEFINED", "SUB X0,X1,W2,UXTB #5 (imm3>4)"),
        ("a06_movz_w_hw2", [0x52C00020], "FAULT_UNDEFINED", "MOVZ W0,#1,LSL #32 (sf=0 hw=2)"),
        ("a07_movop_opc1", [0x32800000], "FAULT_UNDEFINED", "Move-wide opc=01 unallocated"),
        ("a08_ubfm_sf0_n1", [0x53400020], "FAULT_UNDEFINED", "UBFM sf=0 N=1 unallocated"),
        ("a09_ubfm_w_immr32", [0x53200020], "FAULT_UNDEFINED", "UBFM W0,W1,#32,#0 (sf=0 immr>=32)"),
        ("a10_extr_sf0_n1", [0x13C20020], "FAULT_UNDEFINED", "EXTR sf=0 N=1 unallocated"),
        ("a11_rev_sf0_n1", [0x5AC00C20], "FAULT_UNDEFINED", "REV sf=0 opc=11 mismatched width"),
        ("a12_and_w_n1", [0x12400020], "FAULT_UNDEFINED", "AND W0,W1,bitmask N=1 invalid"),
        ("a13_and_allones", [0x9240FC20], "FAULT_UNDEFINED", "AND X0,X1,imms=111111 all-ones mask"),
        ("a14_rev64_2d", [0x4EE00800], "FAULT_UNDEFINED", "REV64 V0.2D,V0.2D (size=11 undefined)"),
        ("a15_uaddlp_2d", [0x6EE02800], "FAULT_UNDEFINED", "UADDLP V0.2D (size=11 undefined)"),
        ("a16_uaddlv_2s", [0x2EB03800], "FAULT_UNDEFINED", "UADDLV S0,V0.2S (Q=0 size=10)"),
        ("a17_ext_8b_imm8", [0x2E014000], "FAULT_UNDEFINED", "EXT V0.8B,V0.8B,V1.8B,#8 (Q=0 imm4=8)"),
    ]
    for vid, ws, exp, dsc in udf_unalloc:
        add(vid, "A_fault_unalloc", dsc, ws, expected_model=exp)

    cu_overlaps = [
        ("a18_cu_ldp_x0_x0", [0xA9400080], "FAULT_CONSTRAINED_UNPRED", "LDP X0,X0,[X4] (Rt==Rt2)"),
        ("a19_cu_ldp_w1_w1", [0x29400481], "FAULT_CONSTRAINED_UNPRED", "LDP W1,W1,[X4] (Rt==Rt2)"),
        ("a20_cu_ldp_xzr_xzr", [0xA9407C9F], "FAULT_CONSTRAINED_UNPRED", "LDP XZR,XZR,[X4] (Rt==Rt2==31)"),
        ("a21_cu_ldr_post_same", [0xF8408484], "FAULT_CONSTRAINED_UNPRED", "LDR X4,[X4],#8 (writeback Rn==Rt)"),
        ("a22_cu_ldr_pre_same", [0xF8408C84], "FAULT_CONSTRAINED_UNPRED", "LDR X4,[X4,#8]! (writeback Rn==Rt)"),
        ("a23_cu_str_post_same", [0xF8008484], "FAULT_CONSTRAINED_UNPRED", "STR X4,[X4],#8 (writeback Rn==Rt)"),
        ("a24_cu_str_pre_same", [0xF8008C84], "FAULT_CONSTRAINED_UNPRED", "STR X4,[X4,#8]! (writeback Rn==Rt)"),
        ("a25_cu_ldp_wb_rn_rt", [0xA8C10484], "FAULT_CONSTRAINED_UNPRED", "LDP X4,X1,[X4],#16 (writeback Rn==Rt1)"),
        ("a26_cu_stlxr_rs_rt", [0xC800FC80], "FAULT_CONSTRAINED_UNPRED", "STLXR W0,X0,[X4] (Rs==Rt)"),
        ("a27_cu_stlxr_rs_rn", [0xC804FC80], "FAULT_CONSTRAINED_UNPRED", "STLXR W4,X0,[X4] (Rs==Rn)"),
    ]
    for vid, ws, exp, dsc in cu_overlaps:
        add(vid, "A_constrained_unpred", dsc, ws, expected_model=exp)

    sp_faults = [
        ("a28_sp_misalign_ldr", "ldr x0, [sp]", "FAULT_SP_ALIGN", "LDR X0,[SP] with SP%16==8", 24),
        ("a29_sp_misalign_str", "str x0, [sp]", "FAULT_SP_ALIGN", "STR X0,[SP] with SP%16==12", 20),
        ("a30_sp_misalign_ldp", "ldp x0, x1, [sp]", "FAULT_SP_ALIGN", "LDP X0,X1,[SP] with SP%16==8", 24),
        ("a31_sp_misalign_ldar", "ldar x0, [sp]", "FAULT_SP_ALIGN", "LDAR X0,[SP] with SP%16==8", 24),
    ]
    for vid, asm_s, exp, dsc, spm in sp_faults:
        add(vid, "A_sp_align", dsc, asm_s, expected_model=exp, sp_misalign=spm)

    # =========================================================================
    # Category B: 16 Ordered / Exclusive Alignment & Monitor Vectors
    # =========================================================================
    add("b00_ldar_x_aligned", "B_atomic_align", "LDAR X0,[X4] aligned", "ldar x0, [x4]", mem_off=0)
    add("b01_ldar_w_aligned", "B_atomic_align", "LDAR W0,[X4] aligned (W-zeroing)", "ldar w0, [x4]", mem_off=0)
    add("b02_stlr_x_aligned", "B_atomic_align", "STLR X1,[X4] aligned", "stlr x1, [x4]", mem_off=0)
    add("b03_stlr_w_aligned", "B_atomic_align", "STLR W1,[X4] aligned", "stlr w1, [x4]", mem_off=0)
    add("b04_ldar_x_intra16", "B_atomic_align", "LDAR X0,[X4+1] intra-16B (LSE2 OK, v8.0 SIGBUS)", "ldar x0, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=1)
    add("b05_ldar_w_intra16", "B_atomic_align", "LDAR W0,[X4+2] intra-16B (LSE2 OK, v8.0 SIGBUS)", "ldar w0, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=2)
    add("b06_stlr_x_intra16", "B_atomic_align", "STLR X1,[X4+1] intra-16B (LSE2 OK, v8.0 SIGBUS)", "stlr x1, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=1)
    add("b07_stlr_w_intra16", "B_atomic_align", "STLR W1,[X4+2] intra-16B (LSE2 OK, v8.0 SIGBUS)", "stlr w1, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=2)
    add("b08_ldar_x_cross16", "B_atomic_align", "LDAR X0,[X4+12] cross-16B SIGBUS even with LSE2", "ldar x0, [x4]", expected_model="FAULT_ALIGN", mem_off=12)
    add("b09_stlr_x_cross16", "B_atomic_align", "STLR X1,[X4+12] cross-16B SIGBUS even with LSE2", "stlr x1, [x4]", expected_model="FAULT_ALIGN", mem_off=12)
    add("b10_ldaxr_x_misalign1", "B_atomic_align", "LDAXR X0,[X4+1] intra-16B (LSE2 OK, v8.0 SIGBUS)", "ldaxr x0, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=1)
    add("b11_ldaxr_w_misalign2", "B_atomic_align", "LDAXR W0,[X4+2] intra-16B (LSE2 OK, v8.0 SIGBUS)", "ldaxr w0, [x4]", expected_model="SPLIT_LSE2_ALIGN", mem_off=2)
    add("b12_excl_ldaxr_stlxr_ok", "B_atomic_excl", "LDAXR+STLXR paired success (W2=0)", "ldaxr x0, [x4]; stlxr w2, x1, [x4]")
    add("b13_excl_clrex_aborts", "B_atomic_excl", "LDAXR+CLREX+STLXR fails (W2=1, mem preserved)", "ldaxr x0, [x4]; clrex; stlxr w2, x1, [x4]")
    add("b14_excl_unarmed_stlxr", "B_atomic_excl", "Unarmed STLXR fails (W2=1, mem preserved)", "clrex; stlxr w2, x1, [x4]")
    add("b15_excl_store_clears", "B_atomic_excl", "Intervening STR to same address clears monitor (W2=1)", "ldaxr x0, [x4]; str x3, [x4]; stlxr w2, x1, [x4]")

    # =========================================================================
    # Category C: 96 Scalar GP, Flags, W-Zeroing, XZR/SP, ADRP, Branch, Mem, CRC32
    # =========================================================================
    scalar_cases = [
        ("c00_add_imm_x", "add x0, x1, #0x123", {}),
        ("c01_add_imm_sh12", "add x0, x1, #0x45, lsl #12", {}),
        ("c02_add_imm_w_zero", "add w0, w1, #1", {"x0": 0xFFFFFFFF00000000, "x1": 0xAAAAAAAA00000005}),
        ("c03_adds_u64_wrap", "adds x0, x1, #1", {"x1": 0xFFFFFFFFFFFFFFFF}),
        ("c04_adds_s64_ovf", "adds x0, x1, #1", {"x1": 0x7FFFFFFFFFFFFFFF}),
        ("c05_adds_w32_ovf", "adds w0, w1, #1", {"x1": 0x123456787FFFFFFF}),
        ("c06_sub_imm_x", "sub x0, x1, #0xabc", {}),
        ("c07_subs_zero_borrow", "subs x0, x1, #1", {"x1": 0}),
        ("c08_subs_s64_ovf", "subs x0, x1, #1", {"x1": 0x8000000000000000}),
        ("c09_subs_eq_zf", "subs x0, x1, x1", {}),
        ("c10_cmp_xzr_discards", "subs xzr, x1, x2", {"x1": 100, "x2": 100}),
        ("c11_cmn_xzr_discards", "adds xzr, x1, x2", {"x1": 0xFFFFFFFFFFFFFFFF, "x2": 1}),
        ("c12_add_sp_read", "add x1, sp, #16; add x2, sp, #0; sub x0, x1, x2", {}),
        ("c13_add_shift_lsl3", "add x0, x1, x2, lsl #3", {}),
        ("c14_sub_shift_lsr4", "sub x0, x1, x2, lsr #4", {}),
        ("c15_add_shift_asr5", "add x0, x1, x2, asr #5", {"x2": 0x8000000000000040}),
        ("c16_add_ext_uxtb", "add x0, x1, w2, uxtb #2", {"x2": 0xFFFFFFFFFFFFFF81}),
        ("c17_add_ext_sxtw", "add x0, x1, w2, sxtw #3", {"x2": 0x00000000FFFFFFF0}),
        ("c18_adc_cf0", "adc x0, x1, x2", {"nzcv": 0x0}),
        ("c19_adc_cf1", "adc x0, x1, x2", {"nzcv": 0x2}),
        ("c20_adcs_cf1_carry", "adcs x0, x1, x2", {"x1": 0xFFFFFFFFFFFFFFFF, "x2": 0, "nzcv": 0x2}),
        ("c21_sbc_cf0_borrow", "sbc x0, x1, x2", {"x1": 10, "x2": 3, "nzcv": 0x0}),
        ("c22_sbcs_cf1", "sbcs x0, x1, x2", {"x1": 10, "x2": 10, "nzcv": 0x2}),
        ("c23_and_imm_byte", "and x0, x1, #0xff", {}),
        ("c24_ands_imm_zero", "ands x0, x1, #0xf0", {"x1": 0x0F}),
        ("c25_orr_imm_rep", "orr x0, x1, #0x0101010101010101", {"x1": 0}),
        ("c26_eor_imm_w_zero", "eor w0, w1, #0xffff", {"x1": 0xFFFFFFFF12345678}),
        ("c27_and_reg_ror", "and x0, x1, x2, ror #8", {}),
        ("c28_bic_reg", "bic x0, x1, x2", {}),
        ("c29_orr_reg", "orr x0, x1, x2", {}),
        ("c30_orn_reg", "orn x0, x1, x2", {}),
        ("c31_eor_reg", "eor x0, x1, x2", {}),
        ("c32_eon_reg", "eon x0, x1, x2", {}),
        ("c33_bics_reg_nf", "bics x0, x1, x2", {"x1": 0x800000000000000F, "x2": 0x0F}),
        ("c34_movz_lsl32", "movz x0, #0xbeef, lsl #32", {}),
        ("c35_movn_x", "movn x0, #0x0005, lsl #16", {}),
        ("c36_movn_w_zero", "movn w0, #0", {"x0": 0xFFFFFFFFFFFFFFFF}),
        ("c37_movk_insert48", "movk x0, #0xcafe, lsl #48", {}),
        ("c38_ubfm_extract", "ubfm x0, x1, #8, #23", {}),
        ("c39_ubfm_lsl", "ubfm x0, x1, #60, #59", {"x1": 0x123456789ABCDEF0}),
        ("c40_sbfm_asr", "sbfm x0, x1, #8, #63", {"x1": 0xF000000000000100}),
        ("c41_sbfm_sxtb_w", "sbfm w0, w1, #0, #7", {"x1": 0x0000000000000085}),
        ("c42_bfm_bfi", "bfm x0, x1, #56, #7", {"x0": 0xAAAAAAAAAAAAAAAA, "x1": 0x55}),
        ("c43_extr_x", "extr x0, x1, x2, #16", {}),
        ("c44_extr_w_ror", "extr w0, w1, w1, #8", {"x1": 0xFFFFFFFF12345678}),
        ("c45_lslv_mod64", "lslv x0, x1, x2", {"x1": 3, "x2": 65}),
        ("c46_lslv_w_mod32", "lslv w0, w1, w2", {"x1": 3, "x2": 33}),
        ("c47_lsrv_x", "lsrv x0, x1, x2", {"x1": 0x8000000000000000, "x2": 60}),
        ("c48_asrv_neg", "asrv x0, x1, x2", {"x1": 0x8000000000000000, "x2": 4}),
        ("c49_rorv_w", "rorv w0, w1, w2", {"x1": 0x12345678, "x2": 12}),
        ("c50_clz_zero_x", "clz x0, x1", {"x1": 0}),
        ("c51_clz_zero_w", "clz w0, w1", {"x1": 0xFFFFFFFF00000000}),
        ("c52_clz_mid_x", "clz x0, x1", {"x1": 0x0008000000000000}),
        ("c53_rev_x64", "rev x0, x1", {"x1": 0x0102030405060708}),
        ("c54_rev_w32", "rev w0, w1", {"x1": 0xFFFFFFFF01020304}),
        ("c55_madd_x", "madd x0, x1, x2, x3", {"x1": 7, "x2": 9, "x3": 100}),
        ("c56_msub_w", "msub w0, w1, w2, w3", {"x1": 7, "x2": 9, "x3": 100}),
        ("c57_umulh_max", "umulh x0, x1, x2", {"x1": 0xFFFFFFFFFFFFFFFF, "x2": 0xFFFFFFFFFFFFFFFF}),
        ("c58_smulh_neg", "smulh x0, x1, x2", {"x1": 0xFFFFFFFFFFFFFFFE, "x2": 3}),
        ("c59_umaddl", "umaddl x0, w1, w2, x3", {"x1": 0xFFFFFFFF, "x2": 2, "x3": 10}),
        ("c60_umsubl", "umsubl x0, w1, w2, x3", {"x1": 10, "x2": 20, "x3": 500}),
        ("c61_udiv_norm", "udiv x0, x1, x2", {"x1": 1000, "x2": 7}),
        ("c62_udiv_by_zero", "udiv x0, x1, x2", {"x1": 0xDEADBEEF, "x2": 0}),
        ("c63_sdiv_neg", "sdiv x0, x1, x2", {"x1": (-100) & ((1 << 64) - 1), "x2": 7}),
        ("c64_sdiv_by_zero", "sdiv w0, w1, w2", {"x1": 0xDEADBEEF, "x2": 0}),
        ("c65_sdiv_intmin_m1", "sdiv x0, x1, x2", {"x1": 0x8000000000000000, "x2": 0xFFFFFFFFFFFFFFFF}),
        ("c66_csel_eq_true", "csel x0, x1, x2, eq", {"nzcv": 0x4}),
        ("c67_csinc_eq_false", "csinc x0, x1, x2, eq", {"x2": 41, "nzcv": 0x0}),
        ("c68_csinv_lt_false", "csinv x0, x1, x2, lt", {"x2": 0, "nzcv": 0x0}),
        ("c69_csneg_mi_false", "csneg x0, x1, x2, mi", {"x2": 5, "nzcv": 0x0}),
        ("c70_ccmp_eq_true", "ccmp x1, x2, #0, eq", {"x1": 5, "x2": 5, "nzcv": 0x4}),
        ("c71_ccmn_ne_false", "ccmn x1, #3, #0xb, eq", {"x1": 5, "nzcv": 0x0}),
        ("c72_adr_rel_sub", "adr x1, .+8; adr x2, .; sub x0, x1, x2", {}),
        ("c73_adrp_page_end", "adrp x0, #4096", {"page_end_adrp": True}),
        ("c74_b_skip_mov", "b .+8; movz x0, #99; add x0, x0, #1", {"x0": 41, "is_branch_rel": True}),
        ("c75_bl_sets_lr", "bl .+8; movz x0, #99; sub x0, x30, x30", {"is_branch_rel": True}),
        ("c76_bcond_eq_taken", "b.eq .+8; movz x0, #99; add x0, x0, #2", {"x0": 10, "nzcv": 0x4, "is_branch_rel": True}),
        ("c77_cbz_taken", "cbz x1, .+8; movz x0, #99; add x0, x0, #3", {"x0": 10, "x1": 0, "is_branch_rel": True}),
        ("c78_tbz_bit63", "tbz x1, #63, .+8; movz x0, #99; add x0, x0, #4", {"x0": 10, "x1": 0x7FFFFFFFFFFFFFFF, "is_branch_rel": True}),
        ("c79_nop_bti", "nop; bti jc; add x0, x1, #1", {"x1": 7}),
        ("c80_ldr_x_imm", "ldr x0, [x4, #8]", {}),
        ("c81_str_w_imm", "str w1, [x4, #4]", {}),
        ("c82_ldur_neg", "ldur x0, [x4, #-8]", {"mem_off": 8}),
        ("c83_ldr_post_wb", "ldr x0, [x4], #8", {}),
        ("c84_str_pre_wb", "str x1, [x4, #8]!", {}),
        ("c85_ldrb_strb", "strb w1, [x4, #3]; ldrb w0, [x4, #3]", {"x1": 0xAB}),
        ("c86_ldrsb_x64", "ldrsb x0, [x4, #7]", {"mem0": 0x8007060504030201}),
        ("c87_ldrsh_w32", "ldrsh w0, [x4, #6]", {"mem0": 0xFF80060504030201}),
        ("c88_ldp_stp_x", "stp x2, x3, [x4]; ldp x0, x1, [x4]", {}),
        ("c89_stp_same_rt_valid", "stp x1, x1, [x4]; ldp x0, x2, [x4]", {}),
        ("c90_crc32b", "crc32b w0, w1, w2", {"x1": 0xFFFFFFFF, "x2": 0x31}),
        ("c91_crc32h", "crc32h w0, w1, w2", {"x1": 0xFFFFFFFF, "x2": 0x3231}),
        ("c92_crc32w", "crc32w w0, w1, w2", {"x1": 0xFFFFFFFF, "x2": 0x34333231}),
        ("c93_crc32x", "crc32x w0, w1, x2", {"x1": 0xFFFFFFFF, "x2": 0x3837363534333231}),
        ("c94_crc32cb", "crc32cb w0, w1, w2", {"x1": 0xFFFFFFFF, "x2": 0x31}),
        ("c95_crc32cx", "crc32cx w0, w1, x2", {"x1": 0xFFFFFFFF, "x2": 0x3837363534333231}),
    ]
    for vid, asm_s, kw in scalar_cases:
        add(vid, "C_scalar", vid, asm_s, **kw)

    # =========================================================================
    # Category D: 80 NEON (64b/128b, D-zeroing, Shifts, Reductions) & Crypto
    # =========================================================================
    neon_cases = [
        ("d00_movi_2d_zero", "movi v0.2d, #0", {}),
        ("d01_movi_2d_mask", "movi v0.2d, #0x00ff00ff00ff00ff", {}),
        ("d02_movi_16b_5a", "movi v0.16b, #0x5a", {}),
        ("d03_movi_8b_dzero", "movi v0.8b, #0xa5", {}),
        ("d04_movi_4s_lsl8", "movi v0.4s, #0x3c, lsl #8", {}),
        ("d05_dup_16b_w1", "dup v0.16b, w1", {"x1": 0x7B}),
        ("d06_dup_8b_dzero", "dup v0.8b, w1", {"x1": 0x42}),
        ("d07_dup_4s_w1", "dup v0.4s, w1", {"x1": 0xDEADBEEF}),
        ("d08_dup_2d_x1", "dup v0.2d, x1", {}),
        ("d09_fmov_w0_s0", "fmov w0, s0", {"x0": 0xFFFFFFFFFFFFFFFF}),
        ("d10_fmov_x0_d0", "fmov x0, d0", {}),
        ("d11_fmov_s0_w1", "fmov s0, w1", {}),
        ("d12_fmov_d0_x1", "fmov d0, x1", {}),
        ("d13_umov_b3", "umov w0, v0.b[3]", {"x0": 0xFFFFFFFFFFFFFFFF}),
        ("d14_umov_h2", "umov w0, v0.h[2]", {"x0": 0xFFFFFFFFFFFFFFFF}),
        ("d15_umov_s1", "mov w0, v0.s[1]", {"x0": 0xFFFFFFFFFFFFFFFF}),
        ("d16_umov_d1", "mov x0, v0.d[1]", {}),
        ("d17_ins_b5_w1", "mov v0.b[5], w1", {"x1": 0xCC}),
        ("d18_ins_d1_x1", "mov v0.d[1], x1", {}),
        ("d19_ldr_q0_mem", "ldr q0, [x4]", {}),
        ("d20_ldr_d0_dzero", "ldr d0, [x4]", {}),
        ("d21_str_q1_mem", "str q1, [x4]", {}),
        ("d22_ldp_stp_d", "stp d1, d2, [x4]; ldp d0, d1, [x4]", {}),
        ("d23_add_16b", "add v0.16b, v0.16b, v1.16b", {}),
        ("d24_add_8b_dzero", "add v0.8b, v0.8b, v1.8b", {}),
        ("d25_add_4s", "add v0.4s, v0.4s, v1.4s", {}),
        ("d26_add_2d", "add v0.2d, v0.2d, v1.2d", {}),
        ("d27_sub_16b", "sub v0.16b, v0.16b, v1.16b", {}),
        ("d28_sub_8h", "sub v0.8h, v0.8h, v1.8h", {}),
        ("d29_uqadd_16b_sat", "uqadd v0.16b, v0.16b, v1.16b", {"v0": 0xFF00FE01807F1005_FF00FE01807F1005, "v1": 0x05050505909001FF_05050505909001FF}),
        ("d30_uqsub_16b_sat", "uqsub v0.16b, v0.16b, v1.16b", {}),
        ("d31_sqadd_16b_sat", "sqadd v0.16b, v0.16b, v1.16b", {"v0": 0x7F807F8000000000_7F807F8000000000, "v1": 0x01807F8000000000_01807F8000000000}),
        ("d32_sqsub_8h_sat", "sqsub v0.8h, v0.8h, v1.8h", {"v0": 0x80007FFF00000001_80007FFF00000001, "v1": 0x0001800000010002_0001800000010002}),
        ("d33_and_16b", "and v0.16b, v0.16b, v1.16b", {}),
        ("d34_and_8b_dzero", "and v0.8b, v0.8b, v1.8b", {}),
        ("d35_bic_16b", "bic v0.16b, v0.16b, v1.16b", {}),
        ("d36_orr_16b", "orr v0.16b, v0.16b, v1.16b", {}),
        ("d37_eor_16b", "eor v0.16b, v0.16b, v1.16b", {}),
        ("d38_bsl_16b", "bsl v0.16b, v1.16b, v2.16b", {}),
        ("d39_bit_16b", "bit v0.16b, v1.16b, v2.16b", {}),
        ("d40_bif_16b", "bif v0.16b, v1.16b, v2.16b", {}),
        ("d41_cmeq_16b", "cmeq v0.16b, v0.16b, v1.16b", {"v1": 0xFFEEDDCC00009988_7766000033221100}),
        ("d42_cmhi_16b", "cmhi v0.16b, v0.16b, v1.16b", {}),
        ("d43_cmgt_16b", "cmgt v0.16b, v0.16b, v1.16b", {}),
        ("d44_cmge_4s", "cmge v0.4s, v0.4s, v1.4s", {}),
        ("d45_cmeq_zero_16b", "cmeq v0.16b, v0.16b, #0", {"v0": 0x0001000200030004_0005000600070000}),
        ("d46_cmlt_zero_4s", "cmlt v0.4s, v0.4s, #0", {"v0": 0x800000007FFFFFFF_FFFFFFFF00000000}),
        ("d47_shl_4s_7", "shl v0.4s, v0.4s, #7", {}),
        ("d48_ushr_4s_7", "ushr v0.4s, v0.4s, #7", {}),
        ("d49_sshr_4s_7", "sshr v0.4s, v0.4s, #7", {"v0": 0x800000007FFFFFFF_F000000001234567}),
        ("d50_ushl_16b_neg_sat", "ushl v0.16b, v0.16b, v1.16b", {"v0": 0x8484848484848484_8484848484848484, "v1": 0x807F08F802FE01FF_807F08F802FE01FF}),
        ("d51_sshl_16b_neg_sat", "sshl v0.16b, v0.16b, v1.16b", {"v0": 0x848484847F7F8080_848484847F7F8080, "v1": 0x807F08F802FE01FF_807F08F802FE01FF}),
        ("d52_ushl_4s_var", "ushl v0.4s, v0.4s, v1.4s", {"v1": 0x000000FF00000020_000000FC00000004}),
        ("d53_sshl_4s_var", "sshl v0.4s, v0.4s, v1.4s", {"v1": 0x0000008000000020_000000FC00000004}),
        ("d54_addp_16b", "addp v0.16b, v0.16b, v1.16b", {}),
        ("d55_addp_8b_dzero", "addp v0.8b, v0.8b, v1.8b", {}),
        ("d56_uaddlp_16b", "uaddlp v0.8h, v0.16b", {}),
        ("d57_uaddlp_8b_fix", "uaddlp v0.4h, v0.8b", {}),
        ("d58_uaddlv_16b_max", "uaddlv h0, v0.16b", {"v0": 0xFFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF}),
        ("d59_uaddlv_8b", "uaddlv h0, v0.8b", {}),
        ("d60_uaddlv_8h", "uaddlv s0, v0.8h", {}),
        ("d61_addv_16b_mod256", "addv b0, v0.16b", {"v0": 0xFFFFFFFFFFFFFFFF_FFFFFFFFFFFFFFFF}),
        ("d62_umaxv_16b", "umaxv b0, v0.16b", {}),
        ("d63_uminv_16b", "uminv b0, v0.16b", {"v0": 0xFFEEDDCCBBAA9988_7766554433221107}),
        ("d64_rev64_16b", "rev64 v0.16b, v0.16b", {}),
        ("d65_rev64_8b_fix", "rev64 v0.8b, v0.8b", {}),
        ("d66_ext_16b_5", "ext v0.16b, v0.16b, v1.16b, #5", {}),
        ("d67_tbl_16b_oob", "tbl v0.16b, { v0.16b }, v1.16b", {"v1": 0xFF100F0E0D0C0B0A_0908070605040300}),
        ("d68_cnt_16b", "cnt v0.16b, v0.16b", {}),
        ("d69_pmul_16b", "pmul v0.16b, v0.16b, v1.16b", {}),
        ("d70_pmull_8b", "pmull v0.8h, v0.8b, v1.8b", {"v0": 0x0000000000000083, "v1": 0x0000000000000083}),
        ("d71_pmull2_16b", "pmull2 v0.8h, v0.16b, v1.16b", {}),
        ("d72_pmull_1d", "pmull v0.1q, v0.1d, v1.1d", {}),
        ("d73_pmull2_2d", "pmull2 v0.1q, v0.2d, v1.2d", {}),
        ("d74_aese_fips197", "aese v0.16b, v1.16b", {"v0": 0x340737E0A2983131_8D305A88A8F64332, "v1": 0x3C4FCF098815F7AB_A6D2AE2816157E2B}),
        ("d75_aesmc_fips197", "aese v0.16b, v1.16b; aesmc v0.16b, v0.16b", {"v0": 0x340737E0A2983131_8D305A88A8F64332, "v1": 0x3C4FCF098815F7AB_A6D2AE2816157E2B}),
        ("d76_aesd_aesimc_inv", "aese v0.16b, v1.16b; aesmc v0.16b, v0.16b; aesimc v0.16b, v0.16b; aesd v0.16b, v2.16b; eor v0.16b, v0.16b, v1.16b", {"v0": 0x340737E0A2983131_8D305A88A8F64332, "v1": 0x3C4FCF098815F7AB_A6D2AE2816157E2B, "v2": 0x0}),
        ("d77_sha256h_su0", "sha256h q0, q1, v2.4s; sha256su0 v0.4s, v1.4s", {}),
        ("d78_sha512h_r01", "sha512h q0, q1, v2.2d", {"v0": 0x6279DFCD10E527FB_56FA27CE0897FD71, "v1": 0x1F83D9ABFB41BD6B_9B05688C2B3E6C1F, "v2": 0x510E527FADE682D1_A54FF53A5F1D36F1}),
        ("d79_sha512su0_su1", "sha512su0 v0.2d, v1.2d; sha512su1 v0.2d, v1.2d, v2.2d", {}),
    ]
    for vid, asm_s, kw in neon_cases:
        add(vid, "D_neon_crypto", vid, asm_s, **kw)

    assert len(specs) == 224, f"Expected 224 vectors, got {len(specs)}"

    asm_indices = [i for i, sp in enumerate(specs) if isinstance(sp["words_or_asm"], str)]
    assembled = assemble_words([specs[i]["words_or_asm"] for i in asm_indices])
    for idx, ws in zip(asm_indices, assembled):
        specs[idx]["words"] = ws
    for sp in specs:
        if "words" not in sp:
            sp["words"] = list(sp["words_or_asm"])
        del sp["words_or_asm"]
    return specs


def audit_disassemblers(specs: list[dict]) -> dict[str, dict]:
    results: dict[str, dict] = {}
    with tempfile.TemporaryDirectory() as td:
        asm_lines = [".text"]
        for i, sp in enumerate(specs):
            asm_lines.append(f"__v_{i:03d}:")
            for w in sp["words"]:
                asm_lines.append(f"  .inst 0x{w:08x}")
        obj = Path(td) / "all224.o"
        subprocess.run(
            ["llvm-mc", "--triple=aarch64-unknown-linux-gnu", "-filetype=obj", "-o", str(obj)],
            input="\n".join(asm_lines) + "\n",
            text=True,
            check=True,
        )
        od_out = subprocess.check_output(
            ["llvm-objdump", "--mattr=+v8.4a,+aes,+sha2,+sha3,+crc", "-d", str(obj)],
            text=True,
        )
        cur_id = None
        od_map: dict[str, list[str]] = {}
        for ln in od_out.splitlines():
            if "<__v_" in ln and ">:" in ln:
                idx = int(ln.split("<__v_")[1].split(">:")[0])
                cur_id = specs[idx]["id"]
                od_map[cur_id] = []
            elif cur_id is not None and ":" in ln and "\t" in ln:
                od_map[cur_id].append(ln.strip())

        # Batch llvm-mc --disassemble on single-word Category A & B vectors
        for sp in specs:
            vid = sp["id"]
            od_lines = od_map.get(vid, [])
            od_unknown = any("<unknown>" in l or "udf" in l.split()[-2:] for l in od_lines)
            mc_warn = False
            mc_text = ""
            if sp["category"].startswith(("A_", "B_")):
                hex_in = "\n".join(
                    " ".join(f"0x{b:02x}" for b in struct.pack("<I", w))
                    for w in sp["words"]
                )
                r_mc = subprocess.run(
                    [
                        "llvm-mc",
                        "--triple=aarch64",
                        "--mattr=+v8.4a,+aes,+sha2,+sha3,+crc",
                        "--disassemble",
                    ],
                    input=hex_in + "\n",
                    text=True,
                    capture_output=True,
                )
                mc_warn = (
                    r_mc.returncode != 0
                    or "warning" in r_mc.stderr.lower()
                    or "invalid" in r_mc.stderr.lower()
                )
                mc_text = " ; ".join(
                    l.strip() for l in r_mc.stdout.splitlines() if l.strip() and not l.strip().startswith(".")
                )
            results[vid] = {
                "objdump_lines": od_lines,
                "objdump_flagged_unknown": any("<unknown>" in l for l in od_lines),
                "llvm_mc_warn_or_err": mc_warn,
                "llvm_mc_disasm": mc_text,
            }
    return results


def generate_rust_qemu_runner(specs: list[dict], indices: list[int]) -> str:
    fn_defs = []
    call_lines = []

    for k in indices:
        sp = specs[k]
        inst_lines = []
        if sp["page_end_adrp"]:
            # Align to a 4 KiB page and pad 4092 bytes (`1023 * nop`) so `adrp` sits at `PC & 0xfff == 0xffc`!
            inst_lines.append(".balign 4096")
            inst_lines.append(".rept 1023\n nop\n .endr")
            inst_lines.append("991:")
        for w in sp["words"]:
            inst_lines.append(f".inst 0x{w:08x}")
        if sp["page_end_adrp"]:
            # Normalize `x0 := x0 - (991b & ~0xfff)` so output is address-independent (`0x1000`)!
            inst_lines.append("adr x9, 991b")
            inst_lines.append("and x9, x9, #0xfffffffffffff000")
            inst_lines.append("sub x0, x0, x9")

        asm_body = "\n            ".join(f'"{ln}\\n",' for ln in inst_lines)

        fn_defs.append(
            f"""
#[inline(never)]
unsafe fn run_vec_{k:03d}(st: &mut VecState) {{
    asm!(
        "ldp x0, x1, [x10, #0]\\n",
        "ldp x2, x3, [x10, #16]\\n",
        "ldr x4, [x10, #32]\\n",
        "ldr x9, [x10, #40]\\n",
        "msr nzcv, x9\\n",
        "ldr q0, [x10, #48]\\n",
        "ldr q1, [x10, #64]\\n",
        "ldr q2, [x10, #80]\\n",
        "mov x11, sp\\n",
        "ldr x9, [x10, #96]\\n",
        "sub sp, sp, x9\\n",
        {asm_body}
        "mov sp, x11\\n",
        "mrs x9, nzcv\\n",
        "stp x0, x1, [x10, #0]\\n",
        "stp x2, x3, [x10, #16]\\n",
        "str x4, [x10, #32]\\n",
        "str x9, [x10, #40]\\n",
        "str q0, [x10, #48]\\n",
        "str q1, [x10, #64]\\n",
        "str q2, [x10, #80]\\n",
        in("x10") st as *mut VecState,
        out("x0") _, out("x1") _, out("x2") _, out("x3") _, out("x4") _,
        out("x9") _, out("x11") _, out("x30") _,
        out("v0") _, out("v1") _, out("v2") _,
    );
}}
"""
        )

        call_lines.append(
            f"""
    MEM_BUF.0 = [0x{sp['mem0']:016x}u64, 0x{sp['mem1']:016x}u64, 0, 0];
    let base_p = (&raw mut MEM_BUF.0) as *mut u8 as u64;
    let mut st = VecState {{
        x0: 0x{sp['x0']:016x},
        x1: 0x{sp['x1']:016x},
        x2: 0x{sp['x2']:016x},
        x3: 0x{sp['x3']:016x},
        x4: base_p.wrapping_add({sp['mem_off']}),
        nzcv: 0x{(sp['nzcv'] << 28):016x},
        v0: 0x{sp['v0']:032x}u128,
        v1: 0x{sp['v1']:032x}u128,
        v2: 0x{sp['v2']:032x}u128,
        sp_sub: {sp['sp_misalign']},
    }};
    LAST_SIG = 0;
    LAST_CODE = 0;
    run_vec_{k:03d}(&mut st);
    emit_record({k}, LAST_SIG, LAST_CODE, &st, base_p, MEM_BUF.0[0], MEM_BUF.0[1]);
"""
        )

    return (
        r"""#![no_std]
#![no_main]
#![allow(suspicious_runtime_symbol_definitions)]
use core::arch::asm;

#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    unsafe { asm!("mov x8, #94\n svc #0", in("x0") 101usize, options(noreturn)) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(dst: *mut u8, c: i32, n: usize) -> *mut u8 {
    let mut i = 0;
    while i < n { *dst.add(i) = c as u8; i += 1; }
    dst
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memcpy(dst: *mut u8, src: *const u8, n: usize) -> *mut u8 {
    let mut i = 0;
    while i < n { *dst.add(i) = *src.add(i); i += 1; }
    dst
}

#[repr(C, align(16))]
struct AlignedBuf([u64; 4]);

#[repr(C, align(16))]
struct VecState {
    x0: u64,
    x1: u64,
    x2: u64,
    x3: u64,
    x4: u64,
    nzcv: u64,
    v0: u128,
    v1: u128,
    v2: u128,
    sp_sub: u64,
}

#[repr(C)]
struct KernelSigaction {
    sa_handler: usize,
    sa_flags: usize,
    sa_mask: u64,
}

static mut ALTSTACK: [u8; 32768] = [0u8; 32768];
static mut MEM_BUF: AlignedBuf = AlignedBuf([0; 4]);
static mut LAST_SIG: u64 = 0;
static mut LAST_CODE: u64 = 0;

unsafe fn sys_write(buf: &[u8]) {
    asm!(
        "mov x8, #64\n svc #0",
        in("x0") 1usize, in("x1") buf.as_ptr(), in("x2") buf.len(),
        lateout("x0") _, out("x8") _, options(nostack)
    );
}

unsafe fn write_hex64(buf: &mut [u8], pos: usize, val: u64) -> usize {
    let hex = b"0123456789abcdef";
    let mut i = 0;
    while i < 16 {
        buf[pos + i] = hex[((val >> ((15 - i) * 4)) & 0xf) as usize];
        i += 1;
    }
    pos + 16
}

unsafe fn write_hex128(buf: &mut [u8], pos: usize, val: u128) -> usize {
    let p1 = write_hex64(buf, pos, (val >> 64) as u64);
    write_hex64(buf, p1, (val & 0xffff_ffff_ffff_ffff) as u64)
}

unsafe fn emit_record(
    idx: usize, sig: u64, code: u64, st: &VecState, base_p: u64, m0: u64, m1: u64
) {
    let mut line = [b' '; 220];
    let mut p = 0;
    p = write_hex64(&mut line, p, idx as u64); line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, sig);        line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, code);       line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, st.x0);      line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, st.x1);      line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, st.x2);      line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, st.x3);      line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, st.x4.wrapping_sub(base_p)); line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, (st.nzcv >> 28) & 0xf);      line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, m0);         line[p] = b','; p += 1;
    p = write_hex64(&mut line, p, m1);         line[p] = b','; p += 1;
    p = write_hex128(&mut line, p, st.v0);
    line[p] = b'\n';
    sys_write(&line[..p + 1]);
}

unsafe extern "C" fn handler(sig: i32, info: *const u8, uctx: *mut u8) {
    LAST_SIG = sig as u64;
    LAST_CODE = (*(info.add(8) as *const i32)) as u32 as u64;
    let pc_ptr = uctx.add(440) as *mut u64;
    *pc_ptr = (*pc_ptr).wrapping_add(4);
}
"""
        + "\n".join(fn_defs)
        + r"""
#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    #[repr(C)]
    struct StackT { ss_sp: usize, ss_flags: i32, _pad: i32, ss_size: usize }
    let ss = StackT { ss_sp: (&raw mut ALTSTACK) as usize, ss_flags: 0, _pad: 0, ss_size: 32768 };
    asm!("mov x8, #132\n svc #0", in("x0") &ss as *const StackT, in("x1") 0usize, lateout("x0") _, out("x8") _);

    let act = KernelSigaction {
        sa_handler: handler as *const () as usize,
        sa_flags: 0x08000004,
        sa_mask: 0,
    };
    for sig in [4usize, 7usize, 11usize] {
        asm!(
            "mov x8, #134\n svc #0",
            in("x0") sig, in("x1") &act as *const KernelSigaction, in("x2") 0usize, in("x3") 8usize,
            lateout("x0") _, out("x8") _
        );
    }
"""
        + "\n".join(call_lines)
        + r"""
    asm!("mov x8, #93\n svc #0", in("x0") 0usize, options(noreturn));
}
"""
    )


def run_qemu_batch(
    specs: list[dict], indices: list[int], toolchain: str, qemu_bin: str, cpu: str
) -> dict[int, dict]:
    rust_src = generate_rust_qemu_runner(specs, indices)
    with tempfile.TemporaryDirectory() as td:
        rs = Path(td) / "runner.rs"
        exe = Path(td) / "runner"
        rs.write_text(rust_src, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                f"+{toolchain}",
                "--target=aarch64-unknown-linux-gnu",
                "-Ctarget-feature=+neon,+aes,+sha2,+sha3,+crc",
                "-Clinker-flavor=ld.lld",
                "-Clinker=rust-lld",
                "-Crelocation-model=static",
                "-Cpanic=abort",
                "-O",
                str(rs),
                "-o",
                str(exe),
            ],
            check=True,
        )
        r = subprocess.run(
            [qemu_bin, "-cpu", cpu, str(exe)],
            capture_output=True,
            text=True,
            timeout=25,
            check=True,
        )
        parsed: dict[int, dict] = {}
        for ln in r.stdout.strip().splitlines():
            parts = ln.strip().split(",")
            idx = int(parts[0], 16)
            parsed[idx] = {
                "sig": int(parts[1], 16),
                "si_code": int(parts[2], 16),
                "x0": int(parts[3], 16),
                "x1": int(parts[4], 16),
                "x2": int(parts[5], 16),
                "x3": int(parts[6], 16),
                "x4_off": int(parts[7], 16),
                "nzcv": int(parts[8], 16),
                "mem0": int(parts[9], 16),
                "mem1": int(parts[10], 16),
                "v0_hex": parts[11],
            }
        return parsed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc-toolchain", default="1.99.1")
    parser.add_argument("--qemu-bin", default="qemu-aarch64")
    parser.add_argument(
        "--out-json",
        type=Path,
        default=Path(__file__)
        .resolve()
        .with_name("probe_qemu_224_aarch64_vectors_results.json"),
    )
    args = parser.parse_args()

    qemu_ver = subprocess.check_output([args.qemu_bin, "--version"], text=True).splitlines()[0]
    mc_ver = [
        l.strip()
        for l in subprocess.check_output(["llvm-mc", "--version"], text=True).splitlines()
        if "version" in l
    ][0]

    specs = build_224_vector_specs()
    disasm = audit_disassemblers(specs)
    res_max = run_qemu_batch(specs, list(range(224)), args.rustc_toolchain, args.qemu_bin, "max")
    res_a53 = run_qemu_batch(specs, list(range(48)), args.rustc_toolchain, args.qemu_bin, "cortex-a53")

    vectors_out = []
    summary_counts = {
        "total_vectors": len(specs),
        "cat_A_fault_unalloc_and_unpred": 0,
        "cat_B_atomic_align_and_excl": 0,
        "cat_C_scalar_gp_crc": 0,
        "cat_D_neon_and_crypto": 0,
        "qemu_max_sigill_4": 0,
        "qemu_max_sigbus_7": 0,
        "qemu_a53_sigbus_7": 0,
        "lse2_vs_v8_0_sigbus_divergences": 0,
        "objdump_silent_on_constrained_unpred": 0,
        "llvm_mc_silent_on_constrained_unpred": 0,
    }

    for idx, sp in enumerate(specs):
        vid = sp["id"]
        qm = res_max[idx]
        qa = res_a53.get(idx)
        da = disasm[vid]

        if sp["category"].startswith("A_"):
            summary_counts["cat_A_fault_unalloc_and_unpred"] += 1
        elif sp["category"].startswith("B_"):
            summary_counts["cat_B_atomic_align_and_excl"] += 1
        elif sp["category"].startswith("C_"):
            summary_counts["cat_C_scalar_gp_crc"] += 1
        else:
            summary_counts["cat_D_neon_and_crypto"] += 1

        if qm["sig"] == 4:
            summary_counts["qemu_max_sigill_4"] += 1
        if qm["sig"] == 7:
            summary_counts["qemu_max_sigbus_7"] += 1
        if qa is not None and qa["sig"] == 7:
            summary_counts["qemu_a53_sigbus_7"] += 1
        if qa is not None and qm["sig"] != qa["sig"]:
            summary_counts["lse2_vs_v8_0_sigbus_divergences"] += 1
        if sp["category"] == "A_constrained_unpred":
            if not da["objdump_flagged_unknown"]:
                summary_counts["objdump_silent_on_constrained_unpred"] += 1
            if not da["llvm_mc_warn_or_err"]:
                summary_counts["llvm_mc_silent_on_constrained_unpred"] += 1

        vectors_out.append(
            {
                "index": idx,
                "id": vid,
                "category": sp["category"],
                "desc": sp["desc"],
                "words_hex": [f"0x{w:08x}" for w in sp["words"]],
                "expected_model": sp["expected_model"],
                "page_end_adrp": sp["page_end_adrp"],
                "is_branch_rel": sp["is_branch_rel"],
                "input": {
                    "x0": sp["x0"],
                    "x1": sp["x1"],
                    "x2": sp["x2"],
                    "x3": sp["x3"],
                    "mem_off": sp["mem_off"],
                    "sp_misalign": sp["sp_misalign"],
                    "nzcv": sp["nzcv"],
                    "mem0": sp["mem0"],
                    "mem1": sp["mem1"],
                    "v0_hex": f"{sp['v0']:032x}",
                    "v1_hex": f"{sp['v1']:032x}",
                    "v2_hex": f"{sp['v2']:032x}",
                },
                "qemu_max": qm,
                "qemu_cortex_a53": qa,
                "disassembler": da,
            }
        )

    out = {
        "qemu_version": qemu_ver,
        "llvm_mc_version": mc_ver,
        "rustc_toolchain": args.rustc_toolchain,
        "summary": summary_counts,
        "vectors": vectors_out,
    }
    args.out_json.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary_counts, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
