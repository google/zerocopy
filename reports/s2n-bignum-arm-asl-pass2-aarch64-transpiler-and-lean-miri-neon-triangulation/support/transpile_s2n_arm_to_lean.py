#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Deterministic AST parser + Armv8-A/v9-A ASL legality overlay transpiling pinned
awslabs/s2n-bignum@d4518712 (arm/proofs/{instruction,decode,arm,neon_helper,
sha256,sha512}.ml) into sharded, prelude + Init.*-only Lean v4.34.1 Pass-2
reference modules (VendorArm64Ref/{Types,Decode,SemanticsScalar,SemanticsNeon,Machine}.lean).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

PINNED_S2N_COMMIT = "d4518712d040485efe621caba1c723a07fbc549e"

PINNED_S2N_BLOBS = {
    "instruction.ml": {
        "git_blob_sha1": "ef9be01f4e078ed0c58da94861c57335046f803e",
        "path": "arm/proofs/instruction.ml",
        "size_bytes": 181272,
    },
    "decode.ml": {
        "git_blob_sha1": "d71476c172132a05ea5130eee00017e1b5e5dd66",
        "path": "arm/proofs/decode.ml",
        "size_bytes": 111754,
    },
    "arm.ml": {
        "git_blob_sha1": "8084bff141e0b0acd81f7b38705990cb3c6b6cfa",
        "path": "arm/proofs/arm.ml",
        "size_bytes": 67256,
    },
    "neon_helper.ml": {
        "git_blob_sha1": "afa2e916317034cb833026f698356014d8f6f0d9",
        "path": "arm/proofs/neon_helper.ml",
        "size_bytes": 39686,
    },
    "sha256.ml": {
        "git_blob_sha1": "a4a56982f38ca626f23ef4fe7538c3a1e1122307",
        "path": "arm/proofs/sha256.ml",
        "size_bytes": 12501,
    },
    "sha512.ml": {
        "git_blob_sha1": "918a24d3caf47a5cf64a2a24efde0010ee4f03c4",
        "path": "arm/proofs/sha512.ml",
        "size_bytes": 11550,
    },
    "simulator_iclasses.ml": {
        "git_blob_sha1": "281b03c2cc1f571b04663d1ddfc9cd08de2cff3a",
        "path": "arm/proofs/simulator_iclasses.ml",
        "size_bytes": 29160,
    },
    "common_aes.ml": {
        "git_blob_sha1": "520c48a50f87d7669e42cc154d120c1fae024f29",
        "path": "common/aes.ml",
        "size_bytes": 21668,
    },
}

# 82-opcode AArch64 Pass-2 reference slice with upstream s2n-bignum + Arm ASL provenance.
OPCODE_SLICE_SPEC = [
    # Scalar GP Arithmetic & Carry Chains (8)
    {"opcode": "ADD", "group": "gp_alu", "s2n_ctor": "arm_ADD", "s2n_decode": True, "asl_iclass": "addsub_imm_shift_ext"},
    {"opcode": "ADDS", "group": "gp_alu", "s2n_ctor": "arm_ADDS", "s2n_decode": True, "asl_iclass": "addsub_imm_shift_ext"},
    {"opcode": "SUB", "group": "gp_alu", "s2n_ctor": "arm_SUB", "s2n_decode": True, "asl_iclass": "addsub_imm_shift_ext"},
    {"opcode": "SUBS", "group": "gp_alu", "s2n_ctor": "arm_SUBS", "s2n_decode": True, "asl_iclass": "addsub_imm_shift_ext"},
    {"opcode": "ADC", "group": "gp_alu", "s2n_ctor": "arm_ADC", "s2n_decode": True, "asl_iclass": "addsub_carry"},
    {"opcode": "ADCS", "group": "gp_alu", "s2n_ctor": "arm_ADCS", "s2n_decode": True, "asl_iclass": "addsub_carry"},
    {"opcode": "SBC", "group": "gp_alu", "s2n_ctor": "arm_SBC", "s2n_decode": True, "asl_iclass": "addsub_carry"},
    {"opcode": "SBCS", "group": "gp_alu", "s2n_ctor": "arm_SBCS", "s2n_decode": True, "asl_iclass": "addsub_carry"},
    # Scalar Logical, Wide Move, Bitfield & Variable Shifts (19)
    {"opcode": "AND", "group": "gp_bit_shift", "s2n_ctor": "arm_AND", "s2n_decode": True, "asl_iclass": "log_imm_shift"},
    {"opcode": "ANDS", "group": "gp_bit_shift", "s2n_ctor": "arm_ANDS", "s2n_decode": True, "asl_iclass": "log_imm_shift"},
    {"opcode": "ORR", "group": "gp_bit_shift", "s2n_ctor": "arm_ORR", "s2n_decode": True, "asl_iclass": "log_imm_shift"},
    {"opcode": "ORN", "group": "gp_bit_shift", "s2n_ctor": "arm_ORN", "s2n_decode": True, "asl_iclass": "log_shift"},
    {"opcode": "EOR", "group": "gp_bit_shift", "s2n_ctor": "arm_EOR", "s2n_decode": True, "asl_iclass": "log_imm_shift"},
    {"opcode": "EON", "group": "gp_bit_shift", "s2n_ctor": "arm_EON", "s2n_decode": True, "asl_iclass": "log_shift"},
    {"opcode": "BIC", "group": "gp_bit_shift", "s2n_ctor": "arm_BIC", "s2n_decode": True, "asl_iclass": "log_shift"},
    {"opcode": "BICS", "group": "gp_bit_shift", "s2n_ctor": "arm_BICS", "s2n_decode": True, "asl_iclass": "log_shift"},
    {"opcode": "MOVZ", "group": "gp_bit_shift", "s2n_ctor": "arm_MOVZ", "s2n_decode": True, "asl_iclass": "movewide"},
    {"opcode": "MOVN", "group": "gp_bit_shift", "s2n_ctor": "arm_MOVN", "s2n_decode": True, "asl_iclass": "movewide"},
    {"opcode": "MOVK", "group": "gp_bit_shift", "s2n_ctor": "arm_MOVK", "s2n_decode": True, "asl_iclass": "movewide"},
    {"opcode": "UBFM", "group": "gp_bit_shift", "s2n_ctor": "arm_UBFM", "s2n_decode": True, "asl_iclass": "bitfield"},
    {"opcode": "SBFM", "group": "gp_bit_shift", "s2n_ctor": "arm_SBFM", "s2n_decode": True, "asl_iclass": "bitfield"},
    {"opcode": "BFM", "group": "gp_bit_shift", "s2n_ctor": "arm_BFM", "s2n_decode": True, "asl_iclass": "bitfield"},
    {"opcode": "EXTR", "group": "gp_bit_shift", "s2n_ctor": "arm_EXTR", "s2n_decode": True, "asl_iclass": "extract"},
    {"opcode": "LSLV", "group": "gp_bit_shift", "s2n_ctor": "arm_LSLV", "s2n_decode": True, "asl_iclass": "dp_2src"},
    {"opcode": "LSRV", "group": "gp_bit_shift", "s2n_ctor": "arm_LSRV", "s2n_decode": True, "asl_iclass": "dp_2src"},
    {"opcode": "ASRV", "group": "gp_bit_shift", "s2n_ctor": "arm_ASRV", "s2n_decode": True, "asl_iclass": "dp_2src"},
    {"opcode": "RORV", "group": "gp_bit_shift", "s2n_ctor": "arm_RORV", "s2n_decode": True, "asl_iclass": "dp_2src"},
    # Scalar Bit-Count, Multiply, Divide & Conditional (16)
    {"opcode": "CLZ", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CLZ", "s2n_decode": True, "asl_iclass": "dp_1src"},
    {"opcode": "REV", "group": "gp_mul_div_cond", "s2n_ctor": "arm_REV", "s2n_decode": True, "asl_iclass": "dp_1src"},
    {"opcode": "MADD", "group": "gp_mul_div_cond", "s2n_ctor": "arm_MADD", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "MSUB", "group": "gp_mul_div_cond", "s2n_ctor": "arm_MSUB", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "SMULH", "group": "gp_mul_div_cond", "s2n_ctor": "arm_SMULH", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "UMULH", "group": "gp_mul_div_cond", "s2n_ctor": "arm_UMULH", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "UMADDL", "group": "gp_mul_div_cond", "s2n_ctor": "arm_UMADDL", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "UMSUBL", "group": "gp_mul_div_cond", "s2n_ctor": "arm_UMSUBL", "s2n_decode": True, "asl_iclass": "dp_3src"},
    {"opcode": "UDIV", "group": "gp_mul_div_cond", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "dp_2src_div"},
    {"opcode": "SDIV", "group": "gp_mul_div_cond", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "dp_2src_div"},
    {"opcode": "CSEL", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CSEL", "s2n_decode": True, "asl_iclass": "condsel"},
    {"opcode": "CSINC", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CSINC", "s2n_decode": True, "asl_iclass": "condsel"},
    {"opcode": "CSINV", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CSINV", "s2n_decode": True, "asl_iclass": "condsel"},
    {"opcode": "CSNEG", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CSNEG", "s2n_decode": True, "asl_iclass": "condsel"},
    {"opcode": "CCMP", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CCMP", "s2n_decode": True, "asl_iclass": "condcmp"},
    {"opcode": "CCMN", "group": "gp_mul_div_cond", "s2n_ctor": "arm_CCMN", "s2n_decode": True, "asl_iclass": "condcmp"},
    # PC-Relative, Branches, Hints & Undefined Traps (13)
    {"opcode": "ADR", "group": "pc_branch_sys", "s2n_ctor": "arm_ADR", "s2n_decode": True, "asl_iclass": "pcreladdr"},
    {"opcode": "ADRP", "group": "pc_branch_sys", "s2n_ctor": "arm_ADRP", "s2n_decode": True, "asl_iclass": "pcreladdr"},
    {"opcode": "B", "group": "pc_branch_sys", "s2n_ctor": "arm_B", "s2n_decode": True, "asl_iclass": "branch_imm"},
    {"opcode": "BL", "group": "pc_branch_sys", "s2n_ctor": "arm_BL", "s2n_decode": True, "asl_iclass": "branch_imm"},
    {"opcode": "Bcond", "group": "pc_branch_sys", "s2n_ctor": "arm_Bcond", "s2n_decode": True, "asl_iclass": "condbranch"},
    {"opcode": "CBZ", "group": "pc_branch_sys", "s2n_ctor": "arm_CBZ", "s2n_decode": True, "asl_iclass": "compbranch"},
    {"opcode": "CBNZ", "group": "pc_branch_sys", "s2n_ctor": "arm_CBNZ", "s2n_decode": True, "asl_iclass": "compbranch"},
    {"opcode": "TBZ", "group": "pc_branch_sys", "s2n_ctor": "arm_TBZ", "s2n_decode": True, "asl_iclass": "testbranch"},
    {"opcode": "TBNZ", "group": "pc_branch_sys", "s2n_ctor": "arm_TBNZ", "s2n_decode": True, "asl_iclass": "testbranch"},
    {"opcode": "RET", "group": "pc_branch_sys", "s2n_ctor": "arm_RET", "s2n_decode": True, "asl_iclass": "branch_reg"},
    {"opcode": "NOP", "group": "pc_branch_sys", "s2n_ctor": "arm_NOP", "s2n_decode": True, "asl_iclass": "hints"},
    {"opcode": "BTI", "group": "pc_branch_sys", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "hints_bti"},
    {"opcode": "UDF", "group": "pc_branch_sys", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "perm_undef"},
    # Memory Loads/Stores, Pairs, Release-Acquire & Exclusive Monitor (15)
    {"opcode": "LDR", "group": "mem_atomic", "s2n_ctor": "arm_LDR", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "STR", "group": "mem_atomic", "s2n_ctor": "arm_STR", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "LDRB", "group": "mem_atomic", "s2n_ctor": "arm_LDRB", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "STRB", "group": "mem_atomic", "s2n_ctor": "arm_STRB", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "LDRH", "group": "mem_atomic", "s2n_ctor": "arm_LDRH", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "STRH", "group": "mem_atomic", "s2n_ctor": "arm_STRH", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "LDRSB", "group": "mem_atomic", "s2n_ctor": "arm_LDRSB", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "LDRSH", "group": "mem_atomic", "s2n_ctor": "arm_LDRSH", "s2n_decode": True, "asl_iclass": "ldst_imm_reg"},
    {"opcode": "LDP", "group": "mem_atomic", "s2n_ctor": "arm_LDP", "s2n_decode": True, "asl_iclass": "ldstpair"},
    {"opcode": "STP", "group": "mem_atomic", "s2n_ctor": "arm_STP", "s2n_decode": True, "asl_iclass": "ldstpair"},
    {"opcode": "LDAR", "group": "mem_atomic", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "ldstexcl_lar"},
    {"opcode": "STLR", "group": "mem_atomic", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "ldstexcl_slr"},
    {"opcode": "LDAXR", "group": "mem_atomic", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "ldstexcl"},
    {"opcode": "STLXR", "group": "mem_atomic", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "ldstexcl"},
    {"opcode": "CLREX", "group": "mem_atomic", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "barriers_clrex"},
    # CRC32 & CRC32C (2 families covering 8 B/H/W/X forms)
    {"opcode": "CRC32_BHWX", "group": "crc32", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "dp_2src_crc32"},
    {"opcode": "CRC32C_BHWX", "group": "crc32", "s2n_ctor": None, "s2n_decode": False, "asl_iclass": "dp_2src_crc32c"},
    # NEON SIMD + Armv8/v8.2 Crypto (9 multi-form families -> 40 NEON/Crypto mnemonics; 82 slice entries total)
    {"opcode": "MOVI_DUP_FMOV_UMOV_INS", "group": "neon_move", "s2n_ctor": "arm_MOVI", "s2n_decode": True, "asl_iclass": "asimdimm_copy"},
    {"opcode": "LDR_STR_LDP_STP_SIMD", "group": "neon_move", "s2n_ctor": "arm_LDR", "s2n_decode": True, "asl_iclass": "ldst_simd"},
    {"opcode": "ADD_SUB_SAT_VEC", "group": "neon_alu", "s2n_ctor": "arm_ADD_VEC", "s2n_decode": True, "asl_iclass": "asimdsame_arith"},
    {"opcode": "AND_BIC_ORR_EOR_BSL_BIT_BIF_VEC", "group": "neon_alu", "s2n_ctor": "arm_AND_VEC", "s2n_decode": True, "asl_iclass": "asimdsame_logic"},
    {"opcode": "CMEQ_CMGT_CMHI_CMGE_CMLT0_VEC", "group": "neon_cmp", "s2n_ctor": "arm_CMGT_VEC", "s2n_decode": True, "asl_iclass": "asimdsame_cmp"},
    {"opcode": "SHL_USHR_SSHR_USHL_SSHL_VEC", "group": "neon_shift", "s2n_ctor": "arm_USHL_VEC", "s2n_decode": True, "asl_iclass": "asimdshf_var"},
    {"opcode": "REV64_EXT_TBL1_CNT_VEC", "group": "neon_perm", "s2n_ctor": "arm_REV64_VEC", "s2n_decode": True, "asl_iclass": "asimdmisc_perm"},
    {"opcode": "ADDP_UADDLP_UADDLV_ADDV_UMAXV_UMINV", "group": "neon_reduce", "s2n_ctor": "arm_UADDLV", "s2n_decode": True, "asl_iclass": "asimdall"},
    {"opcode": "PMUL_PMULL_AES_SHA256_SHA512", "group": "neon_crypto", "s2n_ctor": "arm_AESE", "s2n_decode": True, "asl_iclass": "crypto_aes_sha"},
]


def git_blob_sha1(raw: bytes) -> str:
    hdr = f"blob {len(raw)}\0".encode("ascii")
    return hashlib.sha1(hdr + raw).hexdigest()


def parse_s2n_arm_sources(s2n_dir: Path) -> dict:
    verified_blobs: dict[str, dict] = {}
    texts: dict[str, str] = {}
    for fname, meta in PINNED_S2N_BLOBS.items():
        fpath = s2n_dir / fname
        raw = fpath.read_bytes()
        actual = git_blob_sha1(raw)
        expected = meta["git_blob_sha1"]
        if actual != expected:
            raise ValueError(
                f"s2n-bignum {fname} blob SHA1 mismatch: {actual} != {expected}"
            )
        verified_blobs[fname] = {
            "upstream_path": meta["path"],
            "size_bytes": len(raw),
            "git_blob_sha1": actual,
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
        texts[fname] = raw.decode("utf-8")

    ins_txt = texts["instruction.ml"]
    dec_txt = texts["decode.ml"]
    arm_txt = texts["arm.ml"]

    bitmatch_arms = re.findall(r"^\s*\|\s*\[([^\]]+)\]\s*->", dec_txt, re.M)
    decode_targets = sorted(set(re.findall(r"\b(arm_[A-Za-z0-9_]+)\b", dec_txt)))

    sem_defs: list[str] = []
    assigns_entirety_defs: list[dict] = []
    pc_sub4_defs: list[dict] = []
    for m in re.finditer(
        r"let\s+(arm_[A-Za-z0-9_]+)\s*=\s*(?:new_definition|define)\s*`(.*?)`\s*;;",
        ins_txt,
        re.S,
    ):
        dname, body = m.group(1), m.group(2)
        line_no = ins_txt[: m.start()].count("\n") + 1
        sem_defs.append(dname)
        if "ASSIGNS entirety" in body:
            assigns_entirety_defs.append({"def": dname, "line": line_no})
        if "word_sub (read PC s) (word 4)" in body or "word_sub pc_incr (word 4)" in body:
            pc_sub4_defs.append({"def": dname, "line": line_no})

    partial_q0_none_lines = []
    for idx, ln in enumerate(dec_txt.splitlines(), 1):
        if "~q then NONE" in ln and "unsupported" in ln:
            partial_q0_none_lines.append({"line": idx, "source": ln.strip()})

    raw_s2n_gaps = {
        "assigns_entirety_on_unpredictable_ldst_count": len(assigns_entirety_defs),
        "assigns_entirety_defs": assigns_entirety_defs,
        "pre_increment_pc_plus_4_in_arm_ml": "PC := word_add (read PC s) (word 4) ,,\n             arm_execute instr"
        in arm_txt,
        "pc_minus_4_compensation_defs": pc_sub4_defs,
        "partial_neon_64bit_q0_rejections": partial_q0_none_lines,
        "umov_rejects_byte_and_half_lanes_line_1494": "else NONE // v.h, v.b are unsupported"
        in dec_txt,
        "omits_cmeq_uqadd_uqsub_sshl_bsl_addp_uminv": all(
            f"arm_{op}" not in decode_targets
            for op in ["CMEQ_VEC", "UQADD_VEC", "UQSUB_VEC", "SSHL_VEC", "BSL", "ADDP", "UMINV"]
        ),
        "omits_ldar_stlr_ldaxr_stlxr_clrex_crc32_udiv_sdiv_udf": all(
            f"arm_{op}" not in decode_targets
            for op in ["LDAR", "STLR", "LDAXR", "STLXR", "CLREX", "CRC32B", "CRC32CX", "UDIV", "SDIV", "UDF"]
        ),
    }

    return {
        "s2n_commit": PINNED_S2N_COMMIT,
        "verified_blobs": verified_blobs,
        "decode_ml_bitmatch_arm_count": len(bitmatch_arms),
        "decode_ml_distinct_arm_target_count": len(decode_targets),
        "instruction_ml_arm_semantic_def_count": len(sem_defs),
        "opcode_slice_entry_count": len(OPCODE_SLICE_SPEC),
        "raw_s2n_source_verified_gaps": raw_s2n_gaps,
    }


LEAN_HEADER = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.
"""

TYPES_LEAN = LEAN_HEADER + r"""
prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic

/-!
# `VendorArm64Ref.Types`

Mechanically emitted AArch64 Pass-2 reference types, architectural state,
register-31 (`XZR` vs `SP`) disambiguation, 32-bit `W`-write upper-32 zeroing,
64-bit NEON `D`-write upper-64 zeroing, Exclusive Monitor state, and fail-closed
fault taxonomy derived from `awslabs/s2n-bignum@d4518712` (`arm/proofs/*.ml`)
with Armv8-A/v9-A ASL decode-legality and alignment overlays.
-/

namespace VendorArm64Ref

abbrev Reg5 := BitVec 5
abbrev Vec5 := BitVec 5

def reg31 : Reg5 := 31#5
def reg30 : Reg5 := 30#5

inductive GpWidth where
  | w32
  | x64
  deriving DecidableEq, Repr

inductive VecWidth where
  | d64
  | q128
  deriving DecidableEq, Repr

inductive ElemSize where
  | e8
  | e16
  | e32
  | e64
  deriving DecidableEq, Repr

def ElemSize.bits : ElemSize → Nat
  | .e8  => 8
  | .e16 => 16
  | .e32 => 32
  | .e64 => 64

inductive ShiftKind where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

inductive ExtendKind where
  | uxtb | uxth | uxtw | uxtx
  | sxtb | sxth | sxtw | sxtx
  deriving DecidableEq, Repr

structure PStateFlags where
  nf : Bool := false
  zf : Bool := false
  cf : Bool := false
  vf : Bool := false
  deriving DecidableEq, Repr

abbrev ByteMem := BitVec 64 → BitVec 8
abbrev CodeMap := BitVec 64 → Option (BitVec 8)
abbrev ExclMonitor := Option (BitVec 64 × Nat)

/-- Architectural fault & constrained-unpredictable rejection taxonomy.
    Replaces `s2n-bignum`'s unsound `ASSIGNS entirety` (`instruction.ml:3064`)
    with fail-closed fault states. -/
inductive ArmFault where
  | unalignedPc
  | unmappedFetch
  | undefinedEncoding
  | constrainedUnpredictable
  | spAlignmentFault
  | alignmentFault
  deriving DecidableEq, Repr

inductive AddrMode where
  | unsignedOff (off : BitVec 64)
  | unscaledOff (off : BitVec 64)
  | preIndex    (off : BitVec 64)
  | postIndex   (off : BitVec 64)
  | regOff      (rm : Reg5) (ext : ExtendKind) (shift : Nat)
  deriving DecidableEq, Repr

inductive MemSize where
  | b8 | h16 | w32 | x64 | sb8_32 | sb8_64 | sh16_32 | sh16_64
  deriving DecidableEq, Repr

inductive AluOp where
  | add | adds | sub | subs
  deriving DecidableEq, Repr

inductive CarryOp where
  | adc | adcs | sbc | sbcs
  deriving DecidableEq, Repr

inductive LogOp where
  | and_ | bic | orr | orn | eor | eon | ands | bics
  deriving DecidableEq, Repr

inductive WideMovOp where
  | movn | movz | movk
  deriving DecidableEq, Repr

inductive BfmKind where
  | sbfm | bfm | ubfm
  deriving DecidableEq, Repr

inductive CondSelOp where
  | csel | csinc | csinv | csneg
  deriving DecidableEq, Repr

inductive NeonLogicOp where
  | and_ | bic | orr | eor | bsl | bit_ | bif_
  deriving DecidableEq, Repr

inductive NeonArithOp where
  | add | sub | uqadd | uqsub | sqadd | sqsub | addp
  deriving DecidableEq, Repr

inductive NeonCmpOp where
  | cmeq | cmgt | cmhi | cmge | cmeqZero | cmltZero
  deriving DecidableEq, Repr

inductive NeonShiftImmOp where
  | shl | ushr | sshr
  deriving DecidableEq, Repr

inductive NeonReduceOp where
  | uaddlv | addv | umaxv | uminv
  deriving DecidableEq, Repr

inductive AesOp where
  | aese | aesmc | aesd | aesimc
  deriving DecidableEq, Repr

inductive ShaOp where
  | h | h2 | su0 | su1
  deriving DecidableEq, Repr

inductive Instr where
  -- Scalar GP ALU
  | aluImm     (w : GpWidth) (op : AluOp) (rd rn : Reg5) (imm : BitVec 64)
  | aluShift   (w : GpWidth) (op : AluOp) (rd rn rm : Reg5) (sh : ShiftKind) (amt : Nat)
  | aluExt     (w : GpWidth) (op : AluOp) (rd rn rm : Reg5) (ext : ExtendKind) (amt : Nat)
  | aluCarry   (w : GpWidth) (op : CarryOp) (rd rn rm : Reg5)
  | logImm     (w : GpWidth) (op : LogOp) (rd rn : Reg5) (mask : BitVec 64)
  | logShift   (w : GpWidth) (op : LogOp) (rd rn rm : Reg5) (sh : ShiftKind) (amt : Nat)
  | moveWide   (w : GpWidth) (op : WideMovOp) (rd : Reg5) (imm16 : BitVec 16) (pos : Nat)
  | bitfield   (w : GpWidth) (op : BfmKind) (rd rn : Reg5) (immr imms : Nat)
  | extr       (w : GpWidth) (rd rn rm : Reg5) (lsb : Nat)
  | shiftVar   (w : GpWidth) (sh : ShiftKind) (rd rn rm : Reg5)
  | clz        (w : GpWidth) (rd rn : Reg5)
  | revBytes   (w : GpWidth) (rd rn : Reg5)
  | madd       (w : GpWidth) (sub : Bool) (rd rn rm ra : Reg5)
  | mulHigh    (signed : Bool) (rd rn rm : Reg5)
  | umaddl     (sub : Bool) (rd rn rm ra : Reg5)
  | divInt     (w : GpWidth) (signed : Bool) (rd rn rm : Reg5)
  | condSel    (w : GpWidth) (op : CondSelOp) (rd rn rm : Reg5) (cond : BitVec 4)
  | condCmp    (w : GpWidth) (sub : Bool) (rn : Reg5) (rmOrImm : Sum Reg5 (BitVec 5)) (nzcv : BitVec 4) (cond : BitVec 4)
  -- PC-relative, Branches & Hints
  | adr        (page : Bool) (rd : Reg5) (off : BitVec 64)
  | branchImm  (link : Bool) (off : BitVec 64)
  | branchCond (cond : BitVec 4) (off : BitVec 64)
  | cbz        (w : GpWidth) (nz : Bool) (rt : Reg5) (off : BitVec 64)
  | tbz        (nz : Bool) (rt : Reg5) (bitIdx : Nat) (off : BitVec 64)
  | ret        (rn : Reg5)
  | hintNop
  -- Memory, Pairs, Atomics & CRC32
  | ldstGp     (load : Bool) (sz : MemSize) (rt rn : Reg5) (mode : AddrMode)
  | ldstPairGp (load : Bool) (w : GpWidth) (rt1 rt2 rn : Reg5) (mode : AddrMode)
  | ldstSimd   (load : Bool) (vw : VecWidth) (vt : Vec5) (rn : Reg5) (mode : AddrMode)
  | ldstPairSimd (load : Bool) (vw : VecWidth) (vt1 vt2 : Vec5) (rn : Reg5) (mode : AddrMode)
  | ldar       (w : GpWidth) (exclusive : Bool) (rt rn : Reg5)
  | stlr       (w : GpWidth) (rt rn : Reg5)
  | stlxr      (w : GpWidth) (rs rt rn : Reg5)
  | clrex
  | crc32      (castagnoli : Bool) (bytes : Nat) (rd rn rm : Reg5)
  -- NEON + Crypto
  | neonMovi   (vw : VecWidth) (vd : Vec5) (imm64 : BitVec 64)
  | neonDupGp  (vw : VecWidth) (es : ElemSize) (vd : Vec5) (rn : Reg5)
  | fmovGpToVec (w : GpWidth) (vd : Vec5) (rn : Reg5)
  | fmovVecToGp (w : GpWidth) (rd : Reg5) (vn : Vec5)
  | neonUmov   (es : ElemSize) (rd : Reg5) (vn : Vec5) (idx : Nat)
  | neonInsGp  (es : ElemSize) (vd : Vec5) (rn : Reg5) (idx : Nat)
  | neonInsElt (es : ElemSize) (vd vn : Vec5) (dstIdx srcIdx : Nat)
  | neonArith  (vw : VecWidth) (es : ElemSize) (op : NeonArithOp) (vd vn vm : Vec5)
  | neonLogic  (vw : VecWidth) (op : NeonLogicOp) (vd vn vm : Vec5)
  | neonCmp    (vw : VecWidth) (es : ElemSize) (op : NeonCmpOp) (vd vn vm : Vec5)
  | neonShiftImm (vw : VecWidth) (es : ElemSize) (op : NeonShiftImmOp) (vd vn : Vec5) (amt : Nat)
  | neonShiftVar (vw : VecWidth) (es : ElemSize) (signed : Bool) (vd vn vm : Vec5)
  | neonUaddlp (vw : VecWidth) (es : ElemSize) (vd vn : Vec5)
  | neonReduce (vw : VecWidth) (es : ElemSize) (op : NeonReduceOp) (vd vn : Vec5)
  | neonRev64  (vw : VecWidth) (es : ElemSize) (vd vn : Vec5)
  | neonExt    (vw : VecWidth) (vd vn vm : Vec5) (imm4 : Nat)
  | neonTbl1   (vw : VecWidth) (vd vn vm : Vec5)
  | neonCnt    (vw : VecWidth) (vd vn : Vec5)
  | neonPmul   (vw : VecWidth) (vd vn vm : Vec5)
  | neonPmull  (high : Bool) (es : ElemSize) (vd vn vm : Vec5)
  | cryptoAes  (op : AesOp) (vd vn : Vec5)
  | cryptoSha256 (op : ShaOp) (vd vn vm : Vec5)
  | cryptoSha512 (op : ShaOp) (vd vn vm : Vec5)
  deriving DecidableEq, Repr

structure MachineState where
  pc     : BitVec 64 := 0#64
  xreg   : Reg5 → BitVec 64 := fun _ => 0#64
  sp     : BitVec 64 := 0#64
  vreg   : Vec5 → BitVec 128 := fun _ => 0#128
  flags  : PStateFlags := {}
  mem    : ByteMem := fun _ => 0#8
  excl   : ExclMonitor := none
  halted : Bool := false
  fault  : Option ArmFault := none

def maskWidth (w : GpWidth) (v : BitVec 64) : BitVec 64 :=
  match w with
  | .x64 => v
  | .w32 => (BitVec.extractLsb' 0 32 v).zeroExtend 64

/-- `XREG` (`instruction.ml:85`) / `WREG` (`instruction.ml:147`):
    register 31 is `XZR`/`WZR` (reads `0`, discards writes); 32-bit writes zero
    bits `[63:32]`. -/
def readXzr (w : GpWidth) (s : MachineState) (r : Reg5) : BitVec 64 :=
  if r == reg31 then 0#64 else maskWidth w (s.xreg r)

def writeXzr (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) : MachineState :=
  if r == reg31 then s
  else
    let v' := maskWidth w v
    { s with xreg := fun r' => if r' == r then v' else s.xreg r' }

/-- `XREG_SP` / `WREG_SP` (`decode.ml:10-11`):
    register 31 accesses architectural `SP` / `WSP` (with 32-bit write zeroing
    `SP[63:32]`). -/
def readSp (w : GpWidth) (s : MachineState) (r : Reg5) : BitVec 64 :=
  if r == reg31 then maskWidth w s.sp else maskWidth w (s.xreg r)

def writeSp (w : GpWidth) (s : MachineState) (r : Reg5) (v : BitVec 64) : MachineState :=
  let v' := maskWidth w v
  if r == reg31 then { s with sp := v' }
  else { s with xreg := fun r' => if r' == r then v' else s.xreg r' }

/-- `QREG` / `DREG` (`instruction.ml:244-246`, `arm.ml:198-231`):
    64-bit NEON (`D`-register / `datasize = 64`) writes zero bits `[127:64]`. -/
def readVec (s : MachineState) (v : Vec5) : BitVec 128 :=
  s.vreg v

def writeVec (vw : VecWidth) (s : MachineState) (v : Vec5) (val : BitVec 128) : MachineState :=
  let val' := match vw with
    | .q128 => val
    | .d64  => (BitVec.extractLsb' 0 64 val).zeroExtend 128
  { s with vreg := fun v' => if v' == v then val' else s.vreg v' }

def readMem8 (m : ByteMem) (a : BitVec 64) : BitVec 8 := m a

def readMem16 (m : ByteMem) (a : BitVec 64) : BitVec 16 :=
  (m (a + 1#64)) ++ (m a)

def readMem32 (m : ByteMem) (a : BitVec 64) : BitVec 32 :=
  (readMem16 m (a + 2#64)) ++ (readMem16 m a)

def readMem64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  (readMem32 m (a + 4#64)) ++ (readMem32 m a)

def readMem128 (m : ByteMem) (a : BitVec 64) : BitVec 128 :=
  (readMem64 m (a + 8#64)) ++ (readMem64 m a)

def writeMem8 (m : ByteMem) (a : BitVec 64) (v : BitVec 8) : ByteMem :=
  fun addr => if addr == a then v else m addr

def writeMem16 (m : ByteMem) (a : BitVec 64) (v : BitVec 16) : ByteMem :=
  let m1 := writeMem8 m a (BitVec.extractLsb' 0 8 v)
  writeMem8 m1 (a + 1#64) (BitVec.extractLsb' 8 8 v)

def writeMem32 (m : ByteMem) (a : BitVec 64) (v : BitVec 32) : ByteMem :=
  let m1 := writeMem16 m a (BitVec.extractLsb' 0 16 v)
  writeMem16 m1 (a + 2#64) (BitVec.extractLsb' 16 16 v)

def writeMem64 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m1 := writeMem32 m a (BitVec.extractLsb' 0 32 v)
  writeMem32 m1 (a + 4#64) (BitVec.extractLsb' 32 32 v)

def writeMem128 (m : ByteMem) (a : BitVec 64) (v : BitVec 128) : ByteMem :=
  let m1 := writeMem64 m a (BitVec.extractLsb' 0 64 v)
  writeMem64 m1 (a + 8#64) (BitVec.extractLsb' 64 64 v)

/-- 4-byte aligned little-endian instruction fetch (`arm.ml:18` `aligned_bytes_loaded`). -/
def fetchWord32 (code : CodeMap) (pc : BitVec 64) : Except ArmFault (BitVec 32) :=
  if (pc &&& 3#64) != 0#64 then
    .error .unalignedPc
  else
    match code pc, code (pc + 1#64), code (pc + 2#64), code (pc + 3#64) with
    | some b0, some b1, some b2, some b3 =>
      .ok (((b3 ++ b2) ++ (b1 ++ b0)))
    | _, _, _, _ => .error .unmappedFetch

end VendorArm64Ref
"""

DECODE_LEAN = LEAN_HEADER + r"""
prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Types

/-!
# `VendorArm64Ref.Decode`

Deterministic 32-bit AArch64 instruction decoder derived from
`awslabs/s2n-bignum@d4518712` (`arm/proofs/decode.ml`) augmented with:
1. Normative Armv8-A/v9-A ASL decode-legality guards rejecting constrained-unpredictable
   register overlaps (`LDP` `Rt == Rt2` including `XZR`, load/store writeback
   `Rn == Rt`, `STLXR` `Rs == Rt` or `Rs == Rn`) that `s2n-bignum` accepts into
   `ASSIGNS entirety`; and
2. The missing scalar/atomic/CRC32/NEON encodings (`UDIV`/`SDIV`, `LDAR`/`STLR`/
   `LDAXR`/`STLXR`/`CLREX`, `CRC32*`, `UDF`, `BTI`, `CMEQ`, `CMLT #0`, `UQADD`,
   `UQSUB`, `SQADD`, `SQSUB`, `SSHL`, `ADDP`, `UMINV`, `BSL`, 64-bit `REV64`/`UADDLP`,
   and `.b`/`.h` `UMOV`) emitted by `rustc -O3`.
-/

namespace VendorArm64Ref

def bits (w : BitVec 32) (lo len : Nat) : BitVec len :=
  BitVec.extractLsb' lo len w

def bit (w : BitVec 32) (idx : Nat) : Bool :=
  w.getLsbD idx

def decodeShift (sty : BitVec 2) : ShiftKind :=
  match sty.toNat with
  | 0 => .lsl
  | 1 => .lsr
  | 2 => .asr
  | _ => .ror

def decodeExtend (opt : BitVec 3) : ExtendKind :=
  match opt.toNat with
  | 0 => .uxtb | 1 => .uxth | 2 => .uxtw | 3 => .uxtx
  | 4 => .sxtb | 5 => .sxth | 6 => .sxtw | _ => .sxtx

/-- `Nat.rec`-total highest-set-bit index for `7`-bit `N:¬imms` (`decode.ml:176`). -/
def highestSetBit7 (v : BitVec 7) : Option Nat :=
  if v.getLsbD 6 then some 6
  else if v.getLsbD 5 then some 5
  else if v.getLsbD 4 then some 4
  else if v.getLsbD 3 then some 3
  else if v.getLsbD 2 then some 2
  else if v.getLsbD 1 then some 1
  else if v.getLsbD 0 then some 0
  else none

/-- Armv8-A `DecodeBitMasks` (`decode.ml:175-183`), implemented via `Nat.rec` (`0` `isPartial`). -/
def buildBitmask64 (esize sVal rVal : Nat) : BitVec 64 :=
  Nat.rec (motive := fun _ => BitVec 64)
    0#64
    (fun i acc =>
      if ((i + rVal) % esize) <= sVal then
        acc ||| (1#64 <<< i)
      else acc)
    64

def decodeBitmask (w : GpWidth) (nBit : Bool) (immr imms : BitVec 6) : Option (BitVec 64) :=
  if w == .w32 && nBit then none
  else
    let top : BitVec 1 := if nBit then 1#1 else 0#1
    let combined : BitVec 7 := top ++ (~~~imms)
    match highestSetBit7 combined with
    | none => none
    | some len =>
      if len < 1 then none
      else
        let esize := 2 ^ len
        let sVal := imms.toNat % esize
        let rVal := immr.toNat % esize
        if sVal == esize - 1 then none
        else
          let mask := buildBitmask64 esize sVal rVal
          some (maskWidth w mask)

def elemSizeOf2 (sz : BitVec 2) : Option ElemSize :=
  match sz.toNat with
  | 0 => some .e8
  | 1 => some .e16
  | 2 => some .e32
  | _ => some .e64

def decodeAluOp (op sBit : Bool) : AluOp :=
  match op, sBit with
  | false, false => .add
  | false, true  => .adds
  | true,  false => .sub
  | true,  true  => .subs

def decodeLogOp (opc : BitVec 2) (nBit : Bool) : LogOp :=
  match opc.toNat, nBit with
  | 0, false => .and_ | 0, true => .bic
  | 1, false => .orr  | 1, true => .orn
  | 2, false => .eor  | 2, true => .eon
  | _, false => .ands | _, true => .bics

def decodeSysBranch (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 1. Permanently UNDEFINED (`UDF #imm16`: `w[31:16] == 0`)
  if bits w 16 16 == 0#16 then
    some (.error .undefinedEncoding)

  -- 2. System hints (`NOP`, `BTI`) & `CLREX` & `RET`
  else if w == 0xd503201f#32 then
    some (.ok .hintNop)
  else if (w &&& 0xffffff3f#32) == 0xd503241f#32 then
    some (.ok .hintNop)
  else if (w &&& 0xfffff0ff#32) == 0xd503305f#32 then
    some (.ok .clrex)
  else if (bits w 10 22 == 0b1101011001011111000000#22) && (rd == 0#5) then
    some (.ok (.ret rn))

  -- 3. PC-relative `ADR` / `ADRP` (`decode.ml:328-331`)
  else if bits w 24 5 == 0b10000#5 then
    let page := bit w 31
    let immlo := bits w 29 2
    let immhi := bits w 5 19
    let imm21 : BitVec 21 := immhi ++ immlo
    let off := if page then (imm21 ++ 0#12).signExtend 64 else imm21.signExtend 64
    some (.ok (.adr page rd off))

  -- 4. Unconditional / Conditional / Compare / Test Branches (`decode.ml:254-266`)
  else if bits w 26 5 == 0b00101#5 then
    let link := bit w 31
    let imm26 := bits w 0 26
    some (.ok (.branchImm link ((imm26 ++ 0#2).signExtend 64)))
  else if (bits w 24 8 == 0b01010100#8) && !(bit w 4) then
    let imm19 := bits w 5 19
    let cond  := bits w 0 4
    some (.ok (.branchCond cond ((imm19 ++ 0#2).signExtend 64)))
  else if bits w 25 6 == 0b011010#6 then
    let nz := bit w 24
    let imm19 := bits w 5 19
    some (.ok (.cbz gpw nz rd ((imm19 ++ 0#2).signExtend 64)))
  else if bits w 25 6 == 0b011011#6 then
    let nz := bit w 24
    let b5 := bit w 31
    let b40 := (bits w 19 5).toNat
    let imm14 := bits w 5 14
    some (.ok (.tbz nz rd ((if b5 then 32 else 0) + b40) ((imm14 ++ 0#2).signExtend 64)))
  else none

def decodeDpImm (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 5. Scalar Add/Sub Immediate (`decode.ml:213-219`)
  if bits w 23 6 == 0b100010#6 then
    let sh := bit w 22
    let imm12 := (bits w 10 12).zeroExtend 64
    let imm := if sh then imm12 <<< 12 else imm12
    some (.ok (.aluImm gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn imm))

  -- 6. Scalar Logical Immediate (`decode.ml:243-253`)
  else if bits w 23 6 == 0b100100#6 then
    let opc := bits w 29 2
    let nBit := bit w 22
    let immr := bits w 16 6
    let imms := bits w 10 6
    some (match decodeBitmask gpw nBit immr imms with
      | some mask => .ok (.logImm gpw (decodeLogOp opc false) rd rn mask)
      | none => .error .undefinedEncoding)

  -- 7. Scalar Move Wide `MOVN`/`MOVZ`/`MOVK` (`decode.ml:285-288`)
  else if bits w 23 6 == 0b100101#6 then
    let opc := bits w 29 2
    let hw := (bits w 21 2).toNat
    let imm16 := bits w 5 16
    some (if !sf && hw >= 2 then .error .undefinedEncoding
      else
        match opc.toNat with
        | 0 => .ok (.moveWide gpw .movn rd imm16 (hw * 16))
        | 2 => .ok (.moveWide gpw .movz rd imm16 (hw * 16))
        | 3 => .ok (.moveWide gpw .movk rd imm16 (hw * 16))
        | _ => .error .undefinedEncoding)

  -- 8. Bitfield `SBFM` / `BFM` / `UBFM` (`decode.ml:297-306`) & `EXTR` (`289-293`)
  else if bits w 23 6 == 0b100110#6 then
    let opc := bits w 29 2
    let nBit := bit w 22
    let immr := (bits w 16 6).toNat
    let imms := (bits w 10 6).toNat
    some (if sf != nBit then .error .undefinedEncoding
      else if !sf && (immr >= 32 || imms >= 32) then .error .undefinedEncoding
      else
        match opc.toNat with
        | 0 => .ok (.bitfield gpw .sbfm rd rn immr imms)
        | 1 => .ok (.bitfield gpw .bfm  rd rn immr imms)
        | 2 => .ok (.bitfield gpw .ubfm rd rn immr imms)
        | _ => .error .undefinedEncoding)
  else if (bits w 23 8 == 0b00100111#8) && !(bit w 21) then
    let nBit := bit w 22
    let imms := (bits w 10 6).toNat
    some (if sf != nBit then .error .undefinedEncoding
      else if !sf && imms >= 32 then .error .undefinedEncoding
      else .ok (.extr gpw rd rn rm imms))
  else none

def decodeDpReg (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  let sf : Bool := bit w 31
  let gpw : GpWidth := if sf then .x64 else .w32

  -- 9. Scalar Add/Sub Shifted & Extended Register (`decode.ml:220-242`)
  if (bits w 24 5 == 0b01011#5) && !(bit w 21) then
    let sty := bits w 22 2
    let sam := (bits w 10 6).toNat
    some (if sty == 3#2 then .error .undefinedEncoding
      else if !sf && sam >= 32 then .error .undefinedEncoding
      else .ok (.aluShift gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn rm (decodeShift sty) sam))
  else if bits w 21 8 == 0b01011001#8 then
    let opt := bits w 13 3
    let imm3 := (bits w 10 3).toNat
    some (if imm3 > 4 then .error .undefinedEncoding
      else .ok (.aluExt gpw (decodeAluOp (bit w 30) (bit w 29)) rd rn rm (decodeExtend opt) imm3))

  -- 10. Scalar Logical Shifted Register (`decode.ml:277-284`)
  else if bits w 24 5 == 0b01010#5 then
    let opc := bits w 29 2
    let sty := bits w 22 2
    let nBit := bit w 21
    let sam := (bits w 10 6).toNat
    some (if !sf && sam >= 32 then .error .undefinedEncoding
      else .ok (.logShift gpw (decodeLogOp opc nBit) rd rn rm (decodeShift sty) sam))

  -- 11. Add/Sub with Carry (`ADC`/`ADCS`/`SBC`/`SBCS`, `decode.ml:210-212`)
  else if (bits w 21 8 == 0b11010000#8) && (bits w 10 6 == 0#6) then
    let cop : CarryOp := match bit w 30, bit w 29 with
      | false, false => .adc | false, true => .adcs
      | true,  false => .sbc | true,  true => .sbcs
    some (.ok (.aluCarry gpw cop rd rn rm))

  -- 12. Conditional Compare (`CCMN`/`CCMP`, `decode.ml:271-276`) & Select (`CSEL`.., `267-270`)
  else if (bits w 21 9 == 0b111010010#9) && !(bit w 4) && !(bit w 10) then
    let sub := bit w 30
    let cond := bits w 12 4
    let nzcv := bits w 0 4
    let isImm := bit w 11
    let rhs := if isImm then Sum.inr (bits w 16 5) else Sum.inl rm
    some (.ok (.condCmp gpw sub rn rhs nzcv cond))
  else if (bits w 21 9 == 0b011010100#9) && !(bit w 11) then
    let cop : CondSelOp := match bit w 30, bit w 10 with
      | false, false => .csel  | false, true => .csinc
      | true,  false => .csinv | true,  true => .csneg
    some (.ok (.condSel gpw cop rd rn rm (bits w 12 4)))

  -- 13. Data-processing 2-source (`UDIV`/`SDIV`, `LSLV`/`LSRV`/`ASRV`/`RORV`, `CRC32*`)
  else if bits w 21 10 == 0b0011010110#10 then
    let opcode2 := bits w 10 6
    some (if opcode2 == 0b000010#6 then .ok (.divInt gpw false rd rn rm)
      else if opcode2 == 0b000011#6 then .ok (.divInt gpw true rd rn rm)
      else if bits w 12 4 == 0b0010#4 then
        let sh := decodeShift (bits w 10 2)
        .ok (.shiftVar gpw sh rd rn rm)
      else if bit w 14 && (bits w 13 3 == 0b010#3) then
        let castagnoli := bit w 12
        let sz := (bits w 10 2).toNat
        if sf && sz != 3 then .error .undefinedEncoding
        else if !sf && sz == 3 then .error .undefinedEncoding
        else .ok (.crc32 castagnoli (2 ^ sz) rd rn rm)
      else .error .undefinedEncoding)

  -- 14. Data-processing 1-source (`CLZ`, `REV`, `decode.ml:307-320`) & 3-source (`MADD`.., `310-327`)
  else if bits w 10 21 == 0b101101011000000000100#21 then
    some (.ok (.clz gpw rd rn))
  else if bits w 11 20 == 0b10110101100000000001#20 then
    some (if sf != bit w 10 then .error .undefinedEncoding
      else .ok (.revBytes gpw rd rn))
  else if bits w 21 10 == 0b0011011000#10 then
    let ra : Reg5 := bits w 10 5
    some (.ok (.madd gpw (bit w 15) rd rn rm ra))
  else if (bits w 21 11 == 0b10011011010#11) && (bits w 10 6 == 0b011111#6) then
    some (.ok (.mulHigh true rd rn rm))
  else if (bits w 21 11 == 0b10011011110#11) && (bits w 10 6 == 0b011111#6) then
    some (.ok (.mulHigh false rd rn rm))
  else if bits w 21 11 == 0b10011011101#11 then
    let ra : Reg5 := bits w 10 5
    some (.ok (.umaddl (bit w 15) rd rn rm ra))
  else none

def decodeLoadsStores (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5

  -- 15. Load-Acquire / Store-Release & Exclusive Monitor (`LDAR`, `STLR`, `LDAXR`, `STLXR`)
  if (bits w 24 6 == 0b001000#6) && bit w 31 then
    let wSz : GpWidth := if bit w 30 then .x64 else .w32
    let o2 := bit w 23
    let lBit := bit w 22
    let o1 := bit w 21
    let rs : Reg5 := bits w 16 5
    let o0 := bit w 15
    let rt2 : Reg5 := bits w 10 5
    some (if o1 || (rt2 != reg31) then .error .undefinedEncoding
      else if o2 && lBit && o0 && (rs == reg31) then
        .ok (.ldar wSz false rd rn)
      else if o2 && !lBit && o0 && (rs == reg31) then
        .ok (.stlr wSz rd rn)
      else if !o2 && lBit && o0 && (rs == reg31) then
        .ok (.ldar wSz true rd rn)
      else if !o2 && !lBit && o0 then
        if (rs == rd) || (rs == rn && rn != reg31) then
          .error .constrainedUnpredictable
        else
          .ok (.stlxr wSz rs rd rn)
      else .error .undefinedEncoding)

  -- 16. Load/Store Pair GP & SIMD (`LDP` / `STP`, `decode.ml:99-105`, `instruction.ml:3069`)
  else if (bits w 27 3 == 0b101#3) && !(bit w 25) then
    let opc := bits w 30 2
    let isSimd := bit w 26
    let idxKind := (bits w 23 2).toNat
    let load := bit w 22
    let imm7 := bits w 15 7
    let rt2 : Reg5 := bits w 10 5
    some (if idxKind == 0 then .error .undefinedEncoding
      else if !isSimd && opc == 0b01#2 then .error .undefinedEncoding
      else if !isSimd && opc == 0b11#2 then .error .undefinedEncoding
      else if isSimd && opc == 0b11#2 then .error .undefinedEncoding
      else
        let scale := if isSimd then (if opc == 0b10#2 then 4 else if opc == 0b01#2 then 3 else 2)
                     else (if opc == 0b10#2 then 3 else 2)
        let off64 : BitVec 64 := (imm7.signExtend 64) <<< scale
        let mode : AddrMode :=
          if idxKind == 1 then .postIndex off64
          else if idxKind == 3 then .preIndex off64
          else .unsignedOff off64
        let wback := (idxKind == 1) || (idxKind == 3)
        if load && (rd == rt2) then
          .error .constrainedUnpredictable
        else if !isSimd && wback && (rn != reg31) && (rn == rd || rn == rt2) then
          .error .constrainedUnpredictable
        else if isSimd then
          if opc == 0b00#2 then .error .undefinedEncoding
          else
            let vw : VecWidth := if opc == 0b10#2 then .q128 else .d64
            .ok (.ldstPairSimd load vw rd rt2 rn mode)
        else
          let pw : GpWidth := if opc == 0b10#2 then .x64 else .w32
          .ok (.ldstPairGp load pw rd rt2 rn mode))

  -- 17. Single-Register Load/Store GP & SIMD (`LDR`/`STR`/`LDRB`/`LDRH`/`LDRSB`/`LDRSH`)
  else if bits w 27 3 == 0b111#3 then
    let sz2 := (bits w 30 2).toNat
    let isSimd := bit w 26
    let isUnsignedImm := bit w 24
    let opc := (bits w 22 2).toNat
    some (if isSimd then
        let qForm := (sz2 == 0) && (opc == 2 || opc == 3)
        let dForm := (sz2 == 3) && (opc == 0 || opc == 1)
        if !qForm && !dForm then .error .undefinedEncoding
        else
          let load := (opc % 2) == 1
          let vw : VecWidth := if qForm then .q128 else .d64
          let scale := if qForm then 4 else 3
          if isUnsignedImm then
            let off := ((bits w 10 12).zeroExtend 64) <<< scale
            .ok (.ldstSimd load vw rd rn (.unsignedOff off))
          else if !(bit w 21) then
            let idx2 := (bits w 10 2).toNat
            let off := (bits w 12 9).signExtend 64
            match idx2 with
            | 0 => .ok (.ldstSimd load vw rd rn (.unscaledOff off))
            | 1 => .ok (.ldstSimd load vw rd rn (.postIndex off))
            | 3 => .ok (.ldstSimd load vw rd rn (.preIndex off))
            | _ => .error .undefinedEncoding
          else .error .undefinedEncoding
      else
        let mszOpt : Option (Bool × MemSize × Nat) :=
          match sz2, opc with
          | 0, 0 => some (false, .b8, 0)
          | 0, 1 => some (true,  .b8, 0)
          | 0, 2 => some (true,  .sb8_64, 0)
          | 0, 3 => some (true,  .sb8_32, 0)
          | 1, 0 => some (false, .h16, 1)
          | 1, 1 => some (true,  .h16, 1)
          | 1, 2 => some (true,  .sh16_64, 1)
          | 1, 3 => some (true,  .sh16_32, 1)
          | 2, 0 => some (false, .w32, 2)
          | 2, 1 => some (true,  .w32, 2)
          | 3, 0 => some (false, .x64, 3)
          | 3, 1 => some (true,  .x64, 3)
          | _, _ => none
        match mszOpt with
        | none => .error .undefinedEncoding
        | some (load, msz, scale) =>
          if isUnsignedImm then
            let off := ((bits w 10 12).zeroExtend 64) <<< scale
            .ok (.ldstGp load msz rd rn (.unsignedOff off))
          else if !(bit w 21) then
            let idx2 := (bits w 10 2).toNat
            let off := (bits w 12 9).signExtend 64
            let wback := (idx2 == 1) || (idx2 == 3)
            if wback && (rn != reg31) && (rn == rd) then
              .error .constrainedUnpredictable
            else
              match idx2 with
              | 0 => .ok (.ldstGp load msz rd rn (.unscaledOff off))
              | 1 => .ok (.ldstGp load msz rd rn (.postIndex off))
              | 3 => .ok (.ldstGp load msz rd rn (.preIndex off))
              | _ => .error .undefinedEncoding
          else if bits w 10 2 == 0b10#2 then
            let opt := bits w 13 3
            let sBit := bit w 12
            if (opt.toNat % 4) == 0 || (opt.toNat % 4) == 1 then .error .undefinedEncoding
            else
              let sh := if sBit then scale else 0
              .ok (.ldstGp load msz rd rn (.regOff rm (decodeExtend opt) sh))
          else .error .undefinedEncoding)

  -- 18. Scalar `FMOV` GP <-> SIMD (`0x1e260000`, `0x1e270000`, `0x9e660000`, `0x9e670000`)
  else if (w &&& 0xfffffc00#32) == 0x1e260000#32 then
    some (.ok (.fmovVecToGp .w32 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x9e660000#32 then
    some (.ok (.fmovVecToGp .x64 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x1e270000#32 then
    some (.ok (.fmovGpToVec .w32 rd rn))
  else if (w &&& 0xfffffc00#32) == 0x9e670000#32 then
    some (.ok (.fmovGpToVec .x64 rd rn))
  else none

def decodeCryptoExt (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  -- 19. Armv8 AES & SHA-256 & SHA-512 Cryptographic Extensions (`decode.ml:1069-1116`)
  if bits w 10 22 == 0b0100111000101000010010#22 then some (.ok (.cryptoAes .aese rd rn))
  else if bits w 10 22 == 0b0100111000101000011010#22 then some (.ok (.cryptoAes .aesmc rd rn))
  else if bits w 10 22 == 0b0100111000101000010110#22 then some (.ok (.cryptoAes .aesd rd rn))
  else if bits w 10 22 == 0b0100111000101000011110#22 then some (.ok (.cryptoAes .aesimc rd rn))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b010000#6) then some (.ok (.cryptoSha256 .h rd rn rm))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b010100#6) then some (.ok (.cryptoSha256 .h2 rd rn rm))
  else if bits w 10 22 == 0b0101111000101000001010#22 then some (.ok (.cryptoSha256 .su0 rd rn 0#5))
  else if (bits w 21 11 == 0b01011110000#11) && (bits w 10 6 == 0b011000#6) then some (.ok (.cryptoSha256 .su1 rd rn rm))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100000#6) then some (.ok (.cryptoSha512 .h rd rn rm))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100001#6) then some (.ok (.cryptoSha512 .h2 rd rn rm))
  else if bits w 10 22 == 0b1100111011000000100000#22 then some (.ok (.cryptoSha512 .su0 rd rn 0#5))
  else if (bits w 21 11 == 0b11001110011#11) && (bits w 10 6 == 0b100010#6) then some (.ok (.cryptoSha512 .su1 rd rn rm))
  else none

def decodeNeon (w : BitVec 32) : Option (Except ArmFault Instr) :=
  let rd : Reg5 := bits w 0 5
  let rn : Reg5 := bits w 5 5
  let rm : Reg5 := bits w 16 5
  -- 20. Advanced SIMD (`NEON`) Instructions (`w[28:25] == 0b0111` and `w[31] == 0`)
  if !(bit w 31) && (bits w 25 4 == 0b0111#4) then
    let q := bit w 30
    let u := bit w 29
    let vw : VecWidth := if q then .q128 else .d64
    let sz2 := bits w 22 2
    some (
      -- 20a. `EXT`
      if u && (bits w 21 8 == 0b01110000#8) && !(bit w 15) && !(bit w 10) then
        let imm4 := (bits w 11 4).toNat
        if !q && imm4 >= 8 then .error .undefinedEncoding
        else .ok (.neonExt vw rd rn rm imm4)
      -- 20b. `TBL` 1-register
      else if !u && (bits w 21 8 == 0b01110000#8) && (bits w 10 6 == 0b000000#6) then
        .ok (.neonTbl1 vw rd rn rm)
      -- 20c. `DUP` general / `UMOV` / `INS` general
      else if (bits w 21 8 == 0b01110000#8) && !(bit w 15) && (bit w 10) then
        let imm5 := bits w 16 5
        let op4  := (bits w 11 4).toNat
        let imm5Nat := imm5.toNat
        let laneInfo : Option (ElemSize × Nat) :=
          if (imm5Nat % 2) == 1 then some (.e8, imm5Nat / 2)
          else if (imm5Nat % 4) == 2 then some (.e16, imm5Nat / 4)
          else if (imm5Nat % 8) == 4 then some (.e32, imm5Nat / 8)
          else if (imm5Nat % 16) == 8 then some (.e64, imm5Nat / 16)
          else none
        match laneInfo with
        | none => .error .undefinedEncoding
        | some (es, idx) =>
          if !u && op4 == 0b0001 then
            if !q && es == .e64 then .error .undefinedEncoding
            else .ok (.neonDupGp vw es rd rn)
          else if !u && op4 == 0b0011 && q then
            .ok (.neonInsGp es rd rn idx)
          else if !u && op4 == 0b0111 then
            if (es == .e64 && !q) || (es != .e64 && q) then .error .undefinedEncoding
            else .ok (.neonUmov es rd rn idx)
          else .error .undefinedEncoding
      -- 20d. `INS` element
      else if q && u && (bits w 21 8 == 0b01110000#8) && !(bit w 15) && (bit w 10) then
        .error .undefinedEncoding
      -- 20e. Shift by immediate & Modified Immediate `MOVI`
      else if bit w 24 then
        let immh := bits w 19 4
        let immb := bits w 16 3
        let op6  := bits w 10 6
        if immh == 0#4 then
          if bits w 10 2 == 0b01#2 then
            let cmode := (bits w 12 4).toNat
            let abcdefgh : BitVec 8 := (bits w 16 3) ++ (bits w 5 5)
            if u && cmode == 0b1110 then
              let b0 : BitVec 8 := if abcdefgh.getLsbD 0 then 0xff#8 else 0#8
              let b1 : BitVec 8 := if abcdefgh.getLsbD 1 then 0xff#8 else 0#8
              let b2 : BitVec 8 := if abcdefgh.getLsbD 2 then 0xff#8 else 0#8
              let b3 : BitVec 8 := if abcdefgh.getLsbD 3 then 0xff#8 else 0#8
              let b4 : BitVec 8 := if abcdefgh.getLsbD 4 then 0xff#8 else 0#8
              let b5 : BitVec 8 := if abcdefgh.getLsbD 5 then 0xff#8 else 0#8
              let b6 : BitVec 8 := if abcdefgh.getLsbD 6 then 0xff#8 else 0#8
              let b7 : BitVec 8 := if abcdefgh.getLsbD 7 then 0xff#8 else 0#8
              let imm64 : BitVec 64 := ((b7 ++ b6) ++ (b5 ++ b4)) ++ ((b3 ++ b2) ++ (b1 ++ b0))
              .ok (.neonMovi vw rd imm64)
            else if !u && cmode == 0b1110 then
              let imm16 : BitVec 16 := abcdefgh ++ abcdefgh
              let imm32 : BitVec 32 := imm16 ++ imm16
              .ok (.neonMovi vw rd (imm32 ++ imm32))
            else if !u && (cmode == 0b0000 || cmode == 0b0010 || cmode == 0b0100 || cmode == 0b0110) then
              let sh := (cmode / 2) * 8
              let imm32 : BitVec 32 := (abcdefgh.zeroExtend 32) <<< sh
              .ok (.neonMovi vw rd (imm32 ++ imm32))
            else .error .undefinedEncoding
          else .error .undefinedEncoding
        else
          if immh.getLsbD 3 && !q then .error .undefinedEncoding
          else
            let (es, esBits) : ElemSize × Nat :=
              if immh.getLsbD 3 then (.e64, 64)
              else if immh.getLsbD 2 then (.e32, 32)
              else if immh.getLsbD 1 then (.e16, 16)
              else (.e8, 8)
            let imm7 := ((immh ++ immb) : BitVec 7).toNat
            if !u && op6 == 0b010101#6 then
              .ok (.neonShiftImm vw es .shl rd rn (imm7 - esBits))
            else if op6 == 0b000001#6 then
              let sop : NeonShiftImmOp := if u then .ushr else .sshr
              .ok (.neonShiftImm vw es sop rd rn (2 * esBits - imm7))
            else .error .undefinedEncoding
      -- 20f..20h. Disjoint dispatch when `bit w 21 == true` (`!(bit w 24)`)
      else if bit w 21 then
        let op6 := bits w 10 6
        let lo2 := bits w 10 2
        if lo2 == 0b00#2 then
          if !u && op6 == 0b111000#6 then
            if sz2 == 0b00#2 then .ok (.neonPmull q .e8 rd rn rm)
            else if sz2 == 0b11#2 then .ok (.neonPmull q .e64 rd rn rm)
            else .error .undefinedEncoding
          else .error .undefinedEncoding
        else if lo2 == 0b10#2 then
          let hi4 := bits w 17 4
          let op5 := (bits w 12 5).toNat
          match elemSizeOf2 sz2 with
          | none => .error .undefinedEncoding
          | some es =>
            if hi4 == 0b0000#4 then
              if !u && op5 == 0b00000 && es != .e64 then
                .ok (.neonRev64 vw es rd rn)
              else if u && op5 == 0b00010 && es != .e64 then
                .ok (.neonUaddlp vw es rd rn)
              else if !u && op5 == 0b00101 && es == .e8 then
                .ok (.neonCnt vw rd rn)
              else if !u && op5 == 0b01001 then
                if es == .e64 && !q then .error .undefinedEncoding
                else .ok (.neonCmp vw es .cmeqZero rd rn 0#5)
              else if !u && op5 == 0b01010 then
                if es == .e64 && !q then .error .undefinedEncoding
                else .ok (.neonCmp vw es .cmltZero rd rn 0#5)
              else .error .undefinedEncoding
            else if hi4 == 0b1000#4 then
              if es == .e64 || (es == .e32 && !q) then .error .undefinedEncoding
              else if u && op5 == 0b00011 then
                .ok (.neonReduce vw es .uaddlv rd rn)
              else if !u && op5 == 0b11011 then
                .ok (.neonReduce vw es .addv rd rn)
              else if u && op5 == 0b01010 then
                .ok (.neonReduce vw es .umaxv rd rn)
              else if u && op5 == 0b11010 then
                .ok (.neonReduce vw es .uminv rd rn)
              else .error .undefinedEncoding
            else .error .undefinedEncoding
        else if op6 == 0b000111#6 then
          match u, sz2.toNat with
          | false, 0 => .ok (.neonLogic vw .and_ rd rn rm)
          | false, 1 => .ok (.neonLogic vw .bic  rd rn rm)
          | false, 2 => .ok (.neonLogic vw .orr  rd rn rm)
          | true,  0 => .ok (.neonLogic vw .eor  rd rn rm)
          | true,  1 => .ok (.neonLogic vw .bsl  rd rn rm)
          | true,  2 => .ok (.neonLogic vw .bit_ rd rn rm)
          | true,  3 => .ok (.neonLogic vw .bif_ rd rn rm)
          | _, _     => .error .undefinedEncoding
        else
          match elemSizeOf2 sz2 with
          | none => .error .undefinedEncoding
          | some es =>
            if es == .e64 && !q then .error .undefinedEncoding
            else if op6 == 0b100001#6 then
              .ok (.neonArith vw es (if u then .sub else .add) rd rn rm)
            else if op6 == 0b000011#6 then
              .ok (.neonArith vw es (if u then .uqadd else .sqadd) rd rn rm)
            else if op6 == 0b001011#6 then
              .ok (.neonArith vw es (if u then .uqsub else .sqsub) rd rn rm)
            else if !u && op6 == 0b101111#6 then
              .ok (.neonArith vw es .addp rd rn rm)
            else if u && op6 == 0b100011#6 then
              .ok (.neonCmp vw es .cmeq rd rn rm)
            else if op6 == 0b001101#6 then
              .ok (.neonCmp vw es (if u then .cmhi else .cmgt) rd rn rm)
            else if !u && op6 == 0b001111#6 then
              .ok (.neonCmp vw es .cmge rd rn rm)
            else if op6 == 0b010001#6 then
              .ok (.neonShiftVar vw es (!u) rd rn rm)
            else if u && op6 == 0b100111#6 && es == .e8 then
              .ok (.neonPmul vw rd rn rm)
            else .error .undefinedEncoding
      else .error .undefinedEncoding)
  else none

def decodeWord32 (w : BitVec 32) : Except ArmFault Instr :=
  match decodeSysBranch w with
  | some r => r
  | none =>
    match decodeDpImm w with
    | some r => r
    | none =>
      match decodeDpReg w with
      | some r => r
      | none =>
        match decodeLoadsStores w with
        | some r => r
        | none =>
          match decodeCryptoExt w with
          | some r => r
          | none =>
            match decodeNeon w with
            | some r => r
            | none => .error .undefinedEncoding

end VendorArm64Ref
"""


SEMANTICS_SCALAR_LEAN = LEAN_HEADER + r"""
prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Types

/-!
# `VendorArm64Ref.SemanticsScalar`

Pure, `Nat.rec`-total (`0` `isPartial`) AArch64 scalar GP ALU, NZCV flags,
bitfield, `ADRP` 4 KiB page-masking, branches, `SP` 16-byte alignment check,
`LDAR`/`STLR`/`LDAXR`/`STLXR`/`CLREX` alignment + `ExclusiveMonitor`, and
CRC32/CRC32C operational semantics.
-/

namespace VendorArm64Ref

def evalCond (f : PStateFlags) (cond : BitVec 4) : Bool :=
  let base := match (cond.toNat / 2) with
    | 0 => f.zf
    | 1 => f.cf
    | 2 => f.nf
    | 3 => f.vf
    | 4 => f.cf && !f.zf
    | 5 => f.nf == f.vf
    | 6 => (f.nf == f.vf) && !f.zf
    | _ => true
  if (cond.toNat % 2) == 1 && cond != 0b1111#4 then !base else base

def addWithCarry32 (x y : BitVec 32) (carryIn : Bool) : BitVec 32 × PStateFlags :=
  let cNat := if carryIn then 1 else 0
  let uSum := x.toNat + y.toNat + cNat
  let sSum := x.toInt + y.toInt + Int.ofNat cNat
  let res  := BitVec.ofNat 32 uSum
  let nf   := res.msb
  let zf   := res == 0#32
  let cf   := decide (uSum >= 2 ^ 32)
  let vf   := decide (res.toInt != sSum)
  (res, { nf := nf, zf := zf, cf := cf, vf := vf })

def addWithCarry64 (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × PStateFlags :=
  let cNat := if carryIn then 1 else 0
  let uSum := x.toNat + y.toNat + cNat
  let sSum := x.toInt + y.toInt + Int.ofNat cNat
  let res  := BitVec.ofNat 64 uSum
  let nf   := res.msb
  let zf   := res == 0#64
  let cf   := decide (uSum >= 2 ^ 64)
  let vf   := decide (res.toInt != sSum)
  (res, { nf := nf, zf := zf, cf := cf, vf := vf })

def addWithCarryW (w : GpWidth) (x y : BitVec 64) (carryIn : Bool) : BitVec 64 × PStateFlags :=
  match w with
  | .x64 => addWithCarry64 x y carryIn
  | .w32 =>
    let (r32, fl) := addWithCarry32 (BitVec.extractLsb' 0 32 x) (BitVec.extractLsb' 0 32 y) carryIn
    (r32.zeroExtend 64, fl)

def shiftValW (w : GpWidth) (sh : ShiftKind) (v : BitVec 64) (amt : Nat) : BitVec 64 :=
  match w with
  | .x64 =>
    let a := amt % 64
    match sh with
    | .lsl => v <<< a
    | .lsr => v >>> a
    | .asr => BitVec.sshiftRight v a
    | .ror => if a == 0 then v else (v >>> a) ||| (v <<< (64 - a))
  | .w32 =>
    let v32 := BitVec.extractLsb' 0 32 v
    let a := amt % 32
    let r32 := match sh with
      | .lsl => v32 <<< a
      | .lsr => v32 >>> a
      | .asr => BitVec.sshiftRight v32 a
      | .ror => if a == 0 then v32 else (v32 >>> a) ||| (v32 <<< (32 - a))
    r32.zeroExtend 64

def extendVal64 (ext : ExtendKind) (v : BitVec 64) (shift : Nat) : BitVec 64 :=
  let base : BitVec 64 := match ext with
    | .uxtb => (BitVec.extractLsb' 0 8  v).zeroExtend 64
    | .uxth => (BitVec.extractLsb' 0 16 v).zeroExtend 64
    | .uxtw => (BitVec.extractLsb' 0 32 v).zeroExtend 64
    | .uxtx => v
    | .sxtb => (BitVec.extractLsb' 0 8  v).signExtend 64
    | .sxth => (BitVec.extractLsb' 0 16 v).signExtend 64
    | .sxtw => (BitVec.extractLsb' 0 32 v).signExtend 64
    | .sxtx => v
  base <<< shift

def clzWidth (width : Nat) (v : BitVec 64) : Nat :=
  Nat.rec (motive := fun _ => Nat × Bool)
    (0, false)
    (fun k (cnt, done) =>
      if done then (cnt, true)
      else
        let bitIdx := width - 1 - k
        if v.getLsbD bitIdx then (cnt, true) else (cnt + 1, false))
    width |>.1

def revBytes32 (v : BitVec 32) : BitVec 32 :=
  let b0 := BitVec.extractLsb' 0  8 v
  let b1 := BitVec.extractLsb' 8  8 v
  let b2 := BitVec.extractLsb' 16 8 v
  let b3 := BitVec.extractLsb' 24 8 v
  ((b0 ++ b1) ++ (b2 ++ b3))

def revBytes64 (v : BitVec 64) : BitVec 64 :=
  let lo := revBytes32 (BitVec.extractLsb' 0  32 v)
  let hi := revBytes32 (BitVec.extractLsb' 32 32 v)
  (lo ++ hi)

/-- `Nat.rec`-total reflected CRC-32 (`0xedb88320`) / CRC-32C (`0x82f63b78`)
    4-bit Sarwate nibble lookup tables (`0` `isPartial`, `O(nibs)` kernel WHNF). -/
def crcNibIeee (i : Nat) : Nat :=
  match i with
  | 0  => 0x00000000 | 1  => 0x1db71064 | 2  => 0x3b6e20c8 | 3  => 0x26d930ac
  | 4  => 0x76dc4190 | 5  => 0x6b6b51f4 | 6  => 0x4db26158 | 7  => 0x5005713c
  | 8  => 0xedb88320 | 9  => 0xf00f9344 | 10 => 0xd6d6a3e8 | 11 => 0xcb61b38c
  | 12 => 0x9b64c2b0 | 13 => 0x86d3d2d4 | 14 => 0xa00ae278 | _  => 0xbdbdf21c

def crcNibCast (i : Nat) : Nat :=
  match i with
  | 0  => 0x00000000 | 1  => 0x105ec76f | 2  => 0x20bd8ede | 3  => 0x30e349b1
  | 4  => 0x417b1dbc | 5  => 0x5125dad3 | 6  => 0x61c69362 | 7  => 0x7198540d
  | 8  => 0x82f63b78 | 9  => 0x92a8fc17 | 10 => 0xa24bb5a6 | 11 => 0xb21572c9
  | 12 => 0xc38d26c4 | 13 => 0xd3d3e1ab | 14 => 0xe330a81a | _  => 0xf36e6f75

def crc32StepNib (castagnoli : Bool) (nib : Nat) (c : Nat) : Nat :=
  let idx := Nat.land (Nat.xor c nib) 15
  let tbl := if castagnoli then crcNibCast idx else crcNibIeee idx
  Nat.xor (Nat.shiftRight c 4) tbl

def crc32Multi (castagnoli : Bool) (bytes : Nat) (crc : BitVec 32) (val : BitVec 64) : BitVec 32 :=
  let nibs := bytes * 2
  let vNat := val.toNat
  let res := Nat.rec (motive := fun _ => Nat)
    crc.toNat
    (fun k acc => crc32StepNib castagnoli (Nat.land (Nat.shiftRight vNat (k * 4)) 15) acc)
    nibs
  BitVec.ofNat 32 res

def execAluCore (w : GpWidth) (op : AluOp) (s : MachineState) (nextPc : BitVec 64)
    (useSpRd : Bool) (rd : Reg5) (lhs rhs : BitVec 64) : MachineState :=
  let (res, fl) := match op with
    | .add  => addWithCarryW w lhs rhs false
    | .adds => addWithCarryW w lhs rhs false
    | .sub  => addWithCarryW w lhs (~~~rhs) true
    | .subs => addWithCarryW w lhs (~~~rhs) true
  let setsFlags := (op == .adds) || (op == .subs)
  let s1 := if useSpRd && !setsFlags then writeSp w s rd res else writeXzr w s rd res
  let s2 := if setsFlags then { s1 with flags := fl } else s1
  { s2 with pc := nextPc }

def execBitfield (w : GpWidth) (op : BfmKind) (rd rn : Reg5) (immr imms : Nat)
    (s : MachineState) (nextPc : BitVec 64) : MachineState :=
  let width := match w with | .x64 => 64 | .w32 => 32
  let src := readXzr w s rn
  let dst := readXzr w s rd
  let res : BitVec 64 :=
    if imms >= immr then
      let len := imms - immr + 1
      let mask : BitVec 64 := (1#64 <<< len) - 1#64
      let extracted := (src >>> immr) &&& mask
      match op with
      | .ubfm => extracted
      | .bfm  => (dst &&& (~~~mask)) ||| extracted
      | .sbfm =>
        let signBit := src.getLsbD imms
        if signBit && len < 64 then extracted ||| ((~~~0#64) <<< len) else extracted
    else
      let pos := width - immr
      let len := imms + 1
      let maskLow : BitVec 64 := (1#64 <<< len) - 1#64
      let shifted := (src &&& maskLow) <<< pos
      let dstMask : BitVec 64 := maskLow <<< pos
      match op with
      | .ubfm => maskWidth w shifted
      | .bfm  => maskWidth w ((dst &&& (~~~dstMask)) ||| shifted)
      | .sbfm =>
        let signBit := src.getLsbD imms
        let topFill : BitVec 64 :=
          if signBit && (pos + len) < 64 then (~~~0#64) <<< (pos + len) else 0#64
        maskWidth w (shifted ||| topFill)
  let s1 := writeXzr w s rd res
  { s1 with pc := nextPc }

/-- Compute effective address + optional writeback value, enforcing Armv8-A
    `CheckSPAlignment()` (`SP % 16 == 0`) whenever `Rn == 31`. -/
def evalAddrMode (s : MachineState) (rn : Reg5) (mode : AddrMode)
    : Except ArmFault (BitVec 64 × Option (BitVec 64)) :=
  if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
    .error .spAlignmentFault
  else
    let base := readSp .x64 s rn
    match mode with
    | .unsignedOff off => .ok (base + off, none)
    | .unscaledOff off => .ok (base + off, none)
    | .preIndex off    => let ea := base + off; .ok (ea, some ea)
    | .postIndex off   => .ok (base, some (base + off))
    | .regOff rm ext sh =>
      let idx := extendVal64 ext (readXzr .x64 s rm) sh
      .ok (base + idx, none)

/-- Check `LDAR`/`STLR`/`LDAXR`/`STLXR` alignment (`AArch64.CheckAlignment` for
    `AccType_ORDERED` and `AccType_ATOMIC`):
    - Under baseline Armv8.0-A (`lse2Align16B == false`, e.g. `cortex-a53`), `ea`
      must be naturally aligned (`ea % szBytes == 0`), else `.alignmentFault` (`SIGBUS`).
    - Under Armv8.4-A `FEAT_LSE2` (`lse2Align16B == true`, e.g. `qemu-aarch64 -cpu max`),
      accesses whose bytes lie wholly within a single 16-byte aligned block
      (`(ea % 16) + szBytes <= 16`) succeed, while cross-16B accesses raise `.alignmentFault`. -/
def checkOrderedAlign (lse2Align16B : Bool) (_isExcl : Bool) (szBytes : Nat) (ea : BitVec 64) : Bool :=
  let mask := BitVec.ofNat 64 (szBytes - 1)
  if (ea &&& mask) == 0#64 then true
  else if lse2Align16B then
    ((ea.toNat % 16) + szBytes) <= 16
  else false

def execScalarInstr (exclSpuriousFail : Bool) (lse2Align16B : Bool) (ins : Instr)
    (s : MachineState) : Option MachineState :=
  let nextPc := s.pc + 4#64
  match ins with
  | .hintNop => some { s with pc := nextPc }
  | .clrex   => some { s with pc := nextPc, excl := none }
  | .ret rn  => some { s with pc := readXzr .x64 s rn }

  -- Reconciles `arm.ml:140` + `instruction.ml:750-758`: uses true `s.pc` (never `nextPc`)!
  | .adr page rd off =>
    let base := if page then (s.pc &&& 0xfffffffffffff000#64) else s.pc
    let s1 := writeXzr .x64 s rd (base + off)
    some { s1 with pc := nextPc }

  | .branchImm link off =>
    let s1 := if link then writeXzr .x64 s reg30 nextPc else s
    some { s1 with pc := s.pc + off }

  | .branchCond cond off =>
    let target := if evalCond s.flags cond then s.pc + off else nextPc
    some { s with pc := target }

  | .cbz w nz rt off =>
    let v := readXzr w s rt
    let isZero := v == 0#64
    let take := if nz then !isZero else isZero
    some { s with pc := if take then s.pc + off else nextPc }

  | .tbz nz rt bitIdx off =>
    let v := readXzr .x64 s rt
    let bSet := v.getLsbD bitIdx
    let take := if nz then bSet else !bSet
    some { s with pc := if take then s.pc + off else nextPc }

  | .aluImm w op rd rn imm =>
    some (execAluCore w op s nextPc true rd (readSp w s rn) imm)

  | .aluShift w op rd rn rm sh amt =>
    let rhs := shiftValW w sh (readXzr w s rm) amt
    some (execAluCore w op s nextPc false rd (readXzr w s rn) rhs)

  | .aluExt w op rd rn rm ext amt =>
    let rhs := maskWidth w (extendVal64 ext (readXzr .x64 s rm) amt)
    some (execAluCore w op s nextPc true rd (readSp w s rn) rhs)

  | .aluCarry w op rd rn rm =>
    let lhs := readXzr w s rn
    let rhs := readXzr w s rm
    let (res, fl) := match op with
      | .adc  => addWithCarryW w lhs rhs s.flags.cf
      | .adcs => addWithCarryW w lhs rhs s.flags.cf
      | .sbc  => addWithCarryW w lhs (~~~rhs) s.flags.cf
      | .sbcs => addWithCarryW w lhs (~~~rhs) s.flags.cf
    let setsFlags := (op == .adcs) || (op == .sbcs)
    let s1 := writeXzr w s rd res
    let s2 := if setsFlags then { s1 with flags := fl } else s1
    some { s2 with pc := nextPc }

  | .logImm w op rd rn mask =>
    let lhs := readXzr w s rn
    let res := maskWidth w (match op with
      | .and_ | .ands => lhs &&& mask
      | .orr          => lhs ||| mask
      | .eor          => lhs ^^^ mask
      | _             => lhs &&& mask)
    let setsFlags := op == .ands
    let s1 := if setsFlags then writeXzr w s rd res else writeSp w s rd res
    let nf := match w with | .x64 => res.msb | .w32 => res.getLsbD 31
    let s2 := if setsFlags then
      { s1 with flags := { nf := nf, zf := res == 0#64, cf := false, vf := false } }
    else s1
    some { s2 with pc := nextPc }

  | .logShift w op rd rn rm sh amt =>
    let lhs := readXzr w s rn
    let rhs := shiftValW w sh (readXzr w s rm) amt
    let res := maskWidth w (match op with
      | .and_ | .ands => lhs &&& rhs
      | .bic  | .bics => lhs &&& (~~~rhs)
      | .orr          => lhs ||| rhs
      | .orn          => lhs ||| (~~~rhs)
      | .eor          => lhs ^^^ rhs
      | .eon          => lhs ^^^ (~~~rhs))
    let setsFlags := (op == .ands) || (op == .bics)
    let s1 := writeXzr w s rd res
    let nf := match w with | .x64 => res.msb | .w32 => res.getLsbD 31
    let s2 := if setsFlags then
      { s1 with flags := { nf := nf, zf := res == 0#64, cf := false, vf := false } }
    else s1
    some { s2 with pc := nextPc }

  | .moveWide w op rd imm16 pos =>
    let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< pos
    let res : BitVec 64 := match op with
      | .movz => shifted
      | .movn => maskWidth w (~~~shifted)
      | .movk =>
        let clrMask : BitVec 64 := ~~~((0xffff#64) <<< pos)
        (readXzr w s rd &&& clrMask) ||| shifted
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .bitfield w op rd rn immr imms =>
    some (execBitfield w op rd rn immr imms s nextPc)

  | .extr w rd rn rm lsb =>
    let hi := readXzr w s rn
    let lo := readXzr w s rm
    let res : BitVec 64 := match w with
      | .x64 =>
        let pair128 : BitVec 128 := hi ++ lo
        BitVec.extractLsb' lsb 64 pair128
      | .w32 =>
        let pair64 : BitVec 64 := (BitVec.extractLsb' 0 32 hi) ++ (BitVec.extractLsb' 0 32 lo)
        (BitVec.extractLsb' lsb 32 pair64).zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .shiftVar w sh rd rn rm =>
    let amt := (readXzr w s rm).toNat
    let res := shiftValW w sh (readXzr w s rn) amt
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .clz w rd rn =>
    let cnt := clzWidth (match w with | .x64 => 64 | .w32 => 32) (readXzr w s rn)
    let s1 := writeXzr w s rd (BitVec.ofNat 64 cnt)
    some { s1 with pc := nextPc }

  | .revBytes w rd rn =>
    let v := readXzr w s rn
    let res := match w with
      | .x64 => revBytes64 v
      | .w32 => (revBytes32 (BitVec.extractLsb' 0 32 v)).zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .madd w sub rd rn rm ra =>
    let n := readXzr w s rn
    let m := readXzr w s rm
    let a := readXzr w s ra
    let prod := n * m
    let res := maskWidth w (if sub then a - prod else a + prod)
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .mulHigh signed rd rn rm =>
    let n := readXzr .x64 s rn
    let m := readXzr .x64 s rm
    let res : BitVec 64 :=
      if signed then
        let prod128 : BitVec 128 := BitVec.ofInt 128 (n.toInt * m.toInt)
        BitVec.extractLsb' 64 64 prod128
      else
        let prod128 : BitVec 128 := BitVec.ofNat 128 (n.toNat * m.toNat)
        BitVec.extractLsb' 64 64 prod128
    let s1 := writeXzr .x64 s rd res
    some { s1 with pc := nextPc }

  | .umaddl sub rd rn rm ra =>
    let n := (BitVec.extractLsb' 0 32 (readXzr .w32 s rn)).toNat
    let m := (BitVec.extractLsb' 0 32 (readXzr .w32 s rm)).toNat
    let a := readXzr .x64 s ra
    let prod := BitVec.ofNat 64 (n * m)
    let res := if sub then a - prod else a + prod
    let s1 := writeXzr .x64 s rd res
    some { s1 with pc := nextPc }

  -- Armv8-A total integer division: division by `0` returns `0` (never traps!) and
  -- signed `INT_MIN / -1` wraps to `INT_MIN`.
  | .divInt w signed rd rn rm =>
    let lhs := readXzr w s rn
    let rhs := readXzr w s rm
    let res : BitVec 64 :=
      if rhs == 0#64 then 0#64
      else
        match w, signed with
        | .x64, false => BitVec.ofNat 64 (lhs.toNat / rhs.toNat)
        | .w32, false => BitVec.ofNat 64 ((BitVec.extractLsb' 0 32 lhs).toNat / (BitVec.extractLsb' 0 32 rhs).toNat)
        | .x64, true  => BitVec.ofInt 64 (Int.tdiv lhs.toInt rhs.toInt)
        | .w32, true  =>
          let q32 := BitVec.ofInt 32 (Int.tdiv (BitVec.extractLsb' 0 32 lhs).toInt (BitVec.extractLsb' 0 32 rhs).toInt)
          q32.zeroExtend 64
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .condSel w op rd rn rm cond =>
    let res : BitVec 64 :=
      if evalCond s.flags cond then readXzr w s rn
      else
        let m := readXzr w s rm
        match op with
        | .csel  => m
        | .csinc => maskWidth w (m + 1#64)
        | .csinv => maskWidth w (~~~m)
        | .csneg => maskWidth w (0#64 - m)
    let s1 := writeXzr w s rd res
    some { s1 with pc := nextPc }

  | .condCmp w sub rn rmOrImm nzcv cond =>
    let fl : PStateFlags :=
      if evalCond s.flags cond then
        let lhs := readXzr w s rn
        let rhs := match rmOrImm with
          | .inl rm   => readXzr w s rm
          | .inr imm5 => imm5.zeroExtend 64
        if sub then (addWithCarryW w lhs (~~~rhs) true).2
        else (addWithCarryW w lhs rhs false).2
      else
        { nf := nzcv.getLsbD 3, zf := nzcv.getLsbD 2, cf := nzcv.getLsbD 1, vf := nzcv.getLsbD 0 }
    some { s with pc := nextPc, flags := fl }

  | .crc32 castagnoli bytes rd rn rm =>
    let accIn := BitVec.extractLsb' 0 32 (readXzr .w32 s rn)
    let valIn := readXzr (if bytes == 8 then .x64 else .w32) s rm
    let out32 := crc32Multi castagnoli bytes accIn valIn
    let s1 := writeXzr .w32 s rd (out32.zeroExtend 64)
    some { s1 with pc := nextPc }

  | .ldstGp load msz rt rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let sAfterMem : MachineState :=
        if load then
          match msz with
          | .b8      => writeXzr .w32 s rt ((readMem8  s.mem ea).zeroExtend 64)
          | .h16     => writeXzr .w32 s rt ((readMem16 s.mem ea).zeroExtend 64)
          | .w32     => writeXzr .w32 s rt ((readMem32 s.mem ea).zeroExtend 64)
          | .x64     => writeXzr .x64 s rt (readMem64  s.mem ea)
          | .sb8_32  => writeXzr .w32 s rt (((readMem8  s.mem ea).signExtend 32).zeroExtend 64)
          | .sb8_64  => writeXzr .x64 s rt ((readMem8  s.mem ea).signExtend 64)
          | .sh16_32 => writeXzr .w32 s rt (((readMem16 s.mem ea).signExtend 32).zeroExtend 64)
          | .sh16_64 => writeXzr .x64 s rt ((readMem16 s.mem ea).signExtend 64)
        else
          let v := readXzr .x64 s rt
          let m' := match msz with
            | .b8  => writeMem8  s.mem ea (BitVec.extractLsb' 0 8  v)
            | .h16 => writeMem16 s.mem ea (BitVec.extractLsb' 0 16 v)
            | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
            | _    => writeMem64 s.mem ea v
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldstPairGp load w rt1 rt2 rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let stepBytes : BitVec 64 := match w with | .x64 => 8#64 | .w32 => 4#64
      let sAfterMem : MachineState :=
        if load then
          let v1 := match w with
            | .x64 => readMem64 s.mem ea
            | .w32 => (readMem32 s.mem ea).zeroExtend 64
          let v2 := match w with
            | .x64 => readMem64 s.mem (ea + stepBytes)
            | .w32 => (readMem32 s.mem (ea + stepBytes)).zeroExtend 64
          let s1 := writeXzr w s rt1 v1
          writeXzr w s1 rt2 v2
        else
          let v1 := readXzr w s rt1
          let v2 := readXzr w s rt2
          let m' := match w with
            | .x64 => writeMem64 (writeMem64 s.mem ea v1) (ea + stepBytes) v2
            | .w32 => writeMem32 (writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v1))
                                 (ea + stepBytes) (BitVec.extractLsb' 0 32 v2)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldar w exclusive rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B exclusive szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let val := match w with
          | .x64 => readMem64 s.mem ea
          | .w32 => (readMem32 s.mem ea).zeroExtend 64
        let s1 := writeXzr w s rt val
        let ex' := if exclusive then some (ea, szBytes) else s1.excl
        some { s1 with pc := nextPc, excl := ex' }

  | .stlr w rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B false szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let v := readXzr w s rt
        let m' := match w with
          | .x64 => writeMem64 s.mem ea v
          | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
        some { s with pc := nextPc, mem := m', excl := none }

  | .stlxr w rs rt rn =>
    if rn == reg31 && ((s.sp &&& 15#64) != 0#64) then
      some { s with fault := some .spAlignmentFault }
    else
      let ea := readSp .x64 s rn
      let szBytes := match w with | .x64 => 8 | .w32 => 4
      if !checkOrderedAlign lse2Align16B true szBytes ea then
        some { s with fault := some .alignmentFault }
      else
        let monitorHit := match s.excl with
          | some (monAddr, monSz) => (monAddr == ea) && (monSz == szBytes)
          | none => false
        if monitorHit && !exclSpuriousFail then
          let v := readXzr w s rt
          let m' := match w with
            | .x64 => writeMem64 s.mem ea v
            | .w32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v)
          let s1 := writeXzr .w32 { s with mem := m', excl := none } rs 0#64
          some { s1 with pc := nextPc }
        else
          let s1 := writeXzr .w32 { s with excl := none } rs 1#64
          some { s1 with pc := nextPc }

  | _ => none

end VendorArm64Ref
"""

SEMANTICS_NEON_LEAN = LEAN_HEADER + r"""
prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Types
import VendorArm64Ref.SemanticsScalar

/-!
# `VendorArm64Ref.SemanticsNeon`

Pure, `Nat.rec`-total (`0` `isPartial`) Advanced SIMD (`NEON`) + Armv8/v8.2
Cryptographic (`AES`, `PMUL`/`PMULL`, `SHA-256`, `SHA-512`) operational semantics
with 64-bit `D`-register upper-64 zeroing (`V[127:64] = 0`) and scalar reduction
zero-extension (`UADDLV`, `ADDV`, `UMAXV`, `UMINV`).
-/

namespace VendorArm64Ref

def getByte128 (v : BitVec 128) (i : Nat) : BitVec 8 :=
  BitVec.extractLsb' (i * 8) 8 v

def getHalf128 (v : BitVec 128) (i : Nat) : BitVec 16 :=
  BitVec.extractLsb' (i * 16) 16 v

def getWord128 (v : BitVec 128) (i : Nat) : BitVec 32 :=
  BitVec.extractLsb' (i * 32) 32 v

def getDword128 (v : BitVec 128) (i : Nat) : BitVec 64 :=
  BitVec.extractLsb' (i * 64) 64 v

def packBytes128 (f : Nat → BitVec 8) : BitVec 128 :=
  ((f 15 ++ (f 14 ++ (f 13 ++ f 12))) ++ (f 11 ++ (f 10 ++ (f 9 ++ f 8)))) ++
  ((f 7  ++ (f 6  ++ (f 5  ++ f 4)))  ++ (f 3  ++ (f 2  ++ (f 1 ++ f 0))))

def packHalfs128 (f : Nat → BitVec 16) : BitVec 128 :=
  ((f 7 ++ f 6) ++ (f 5 ++ f 4)) ++ ((f 3 ++ f 2) ++ (f 1 ++ f 0))

def packWords128 (f : Nat → BitVec 32) : BitVec 128 :=
  (f 3 ++ f 2) ++ (f 1 ++ f 0)

def packDwords128 (hi lo : BitVec 64) : BitVec 128 :=
  hi ++ lo

def uqaddW (w : Nat) (a b : BitVec w) : BitVec w :=
  let s := a.toNat + b.toNat
  let mx := (2 ^ w) - 1
  BitVec.ofNat w (if s > mx then mx else s)

def uqsubW (w : Nat) (a b : BitVec w) : BitVec w :=
  if a.toNat >= b.toNat then BitVec.ofNat w (a.toNat - b.toNat) else 0#w

def sqaddW (w : Nat) (a b : BitVec w) : BitVec w :=
  let s := a.toInt + b.toInt
  let hi : Int := Int.ofNat (2 ^ (w - 1)) - 1
  let lo : Int := -(Int.ofNat (2 ^ (w - 1)))
  BitVec.ofInt w (if s > hi then hi else if s < lo then lo else s)

def sqsubW (w : Nat) (a b : BitVec w) : BitVec w :=
  let d := a.toInt - b.toInt
  let hi : Int := Int.ofNat (2 ^ (w - 1)) - 1
  let lo : Int := -(Int.ofNat (2 ^ (w - 1)))
  BitVec.ofInt w (if d > hi then hi else if d < lo then lo else d)

def neonUshlLane (w : Nat) (x : BitVec w) (shByte : BitVec 8) : BitVec w :=
  if shByte.msb then
    let rsh := (0#8 - shByte).toNat
    if rsh >= w then 0#w else x >>> rsh
  else
    let lsh := shByte.toNat
    if lsh >= w then 0#w else x <<< lsh

def neonSshlLane (w : Nat) (x : BitVec w) (shByte : BitVec 8) : BitVec w :=
  if shByte.msb then
    let rsh := (0#8 - shByte).toNat
    let clamped := if rsh >= w then w - 1 else rsh
    BitVec.sshiftRight x clamped
  else
    let lsh := shByte.toNat
    if lsh >= w then 0#w else x <<< lsh

def popcntByte (b : BitVec 8) : BitVec 8 :=
  Nat.rec (motive := fun _ => BitVec 8)
    0#8
    (fun k acc => if b.getLsbD k then acc + 1#8 else acc)
    8

def pmullByte (a b : BitVec 8) : BitVec 16 :=
  let b16 := b.zeroExtend 16
  Nat.rec (motive := fun _ => BitVec 16)
    0#16
    (fun k acc => if a.getLsbD k then acc ^^^ (b16 <<< k) else acc)
    8

def pmulByte (a b : BitVec 8) : BitVec 8 :=
  BitVec.extractLsb' 0 8 (pmullByte a b)

def pmull64 (a b : BitVec 64) : BitVec 128 :=
  let b128 := b.zeroExtend 128
  Nat.rec (motive := fun _ => BitVec 128)
    0#128
    (fun k acc => if a.getLsbD k then acc ^^^ (b128 <<< k) else acc)
    64

def uaddlvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun k acc => acc + (BitVec.extractLsb' (k * esize) esize v).toNat)
    lanes

def umaxvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun k acc =>
      let cur := (BitVec.extractLsb' (k * esize) esize v).toNat
      if cur > acc then cur else acc)
    lanes

def uminvLoop (lanes esize : Nat) (v : BitVec 128) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    ((2 ^ esize) - 1)
    (fun k acc =>
      let cur := (BitVec.extractLsb' (k * esize) esize v).toNat
      if cur < acc then cur else acc)
    lanes

/-- AES forward/inverse S-box & MixColumns matching Armv8 Cryptography Extension. -/
def aesSbox (b : BitVec 8) : BitVec 8 :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  match hi with
  | 0 => match lo with
    | 0 => 0x63#8 | 1 => 0x7c#8 | 2 => 0x77#8 | 3 => 0x7b#8
    | 4 => 0xf2#8 | 5 => 0x6b#8 | 6 => 0x6f#8 | 7 => 0xc5#8
    | 8 => 0x30#8 | 9 => 0x01#8 | 10 => 0x67#8 | 11 => 0x2b#8
    | 12 => 0xfe#8 | 13 => 0xd7#8 | 14 => 0xab#8 | _ => 0x76#8
  | 1 => match lo with
    | 0 => 0xca#8 | 1 => 0x82#8 | 2 => 0xc9#8 | 3 => 0x7d#8
    | 4 => 0xfa#8 | 5 => 0x59#8 | 6 => 0x47#8 | 7 => 0xf0#8
    | 8 => 0xad#8 | 9 => 0xd4#8 | 10 => 0xa2#8 | 11 => 0xaf#8
    | 12 => 0x9c#8 | 13 => 0xa4#8 | 14 => 0x72#8 | _ => 0xc0#8
  | 2 => match lo with
    | 0 => 0xb7#8 | 1 => 0xfd#8 | 2 => 0x93#8 | 3 => 0x26#8
    | 4 => 0x36#8 | 5 => 0x3f#8 | 6 => 0xf7#8 | 7 => 0xcc#8
    | 8 => 0x34#8 | 9 => 0xa5#8 | 10 => 0xe5#8 | 11 => 0xf1#8
    | 12 => 0x71#8 | 13 => 0xd8#8 | 14 => 0x31#8 | _ => 0x15#8
  | 3 => match lo with
    | 0 => 0x04#8 | 1 => 0xc7#8 | 2 => 0x23#8 | 3 => 0xc3#8
    | 4 => 0x18#8 | 5 => 0x96#8 | 6 => 0x05#8 | 7 => 0x9a#8
    | 8 => 0x07#8 | 9 => 0x12#8 | 10 => 0x80#8 | 11 => 0xe2#8
    | 12 => 0xeb#8 | 13 => 0x27#8 | 14 => 0xb2#8 | _ => 0x75#8
  | 4 => match lo with
    | 0 => 0x09#8 | 1 => 0x83#8 | 2 => 0x2c#8 | 3 => 0x1a#8
    | 4 => 0x1b#8 | 5 => 0x6e#8 | 6 => 0x5a#8 | 7 => 0xa0#8
    | 8 => 0x52#8 | 9 => 0x3b#8 | 10 => 0xd6#8 | 11 => 0xb3#8
    | 12 => 0x29#8 | 13 => 0xe3#8 | 14 => 0x2f#8 | _ => 0x84#8
  | 5 => match lo with
    | 0 => 0x53#8 | 1 => 0xd1#8 | 2 => 0x00#8 | 3 => 0xed#8
    | 4 => 0x20#8 | 5 => 0xfc#8 | 6 => 0xb1#8 | 7 => 0x5b#8
    | 8 => 0x6a#8 | 9 => 0xcb#8 | 10 => 0xbe#8 | 11 => 0x39#8
    | 12 => 0x4a#8 | 13 => 0x4c#8 | 14 => 0x58#8 | _ => 0xcf#8
  | 6 => match lo with
    | 0 => 0xd0#8 | 1 => 0xef#8 | 2 => 0xaa#8 | 3 => 0xfb#8
    | 4 => 0x43#8 | 5 => 0x4d#8 | 6 => 0x33#8 | 7 => 0x85#8
    | 8 => 0x45#8 | 9 => 0xf9#8 | 10 => 0x02#8 | 11 => 0x7f#8
    | 12 => 0x50#8 | 13 => 0x3c#8 | 14 => 0x9f#8 | _ => 0xa8#8
  | 7 => match lo with
    | 0 => 0x51#8 | 1 => 0xa3#8 | 2 => 0x40#8 | 3 => 0x8f#8
    | 4 => 0x92#8 | 5 => 0x9d#8 | 6 => 0x38#8 | 7 => 0xf5#8
    | 8 => 0xbc#8 | 9 => 0xb6#8 | 10 => 0xda#8 | 11 => 0x21#8
    | 12 => 0x10#8 | 13 => 0xff#8 | 14 => 0xf3#8 | _ => 0xd2#8
  | 8 => match lo with
    | 0 => 0xcd#8 | 1 => 0x0c#8 | 2 => 0x13#8 | 3 => 0xec#8
    | 4 => 0x5f#8 | 5 => 0x97#8 | 6 => 0x44#8 | 7 => 0x17#8
    | 8 => 0xc4#8 | 9 => 0xa7#8 | 10 => 0x7e#8 | 11 => 0x3d#8
    | 12 => 0x64#8 | 13 => 0x5d#8 | 14 => 0x19#8 | _ => 0x73#8
  | 9 => match lo with
    | 0 => 0x60#8 | 1 => 0x81#8 | 2 => 0x4f#8 | 3 => 0xdc#8
    | 4 => 0x22#8 | 5 => 0x2a#8 | 6 => 0x90#8 | 7 => 0x88#8
    | 8 => 0x46#8 | 9 => 0xee#8 | 10 => 0xb8#8 | 11 => 0x14#8
    | 12 => 0xde#8 | 13 => 0x5e#8 | 14 => 0x0b#8 | _ => 0xdb#8
  | 10 => match lo with
    | 0 => 0xe0#8 | 1 => 0x32#8 | 2 => 0x3a#8 | 3 => 0x0a#8
    | 4 => 0x49#8 | 5 => 0x06#8 | 6 => 0x24#8 | 7 => 0x5c#8
    | 8 => 0xc2#8 | 9 => 0xd3#8 | 10 => 0xac#8 | 11 => 0x62#8
    | 12 => 0x91#8 | 13 => 0x95#8 | 14 => 0xe4#8 | _ => 0x79#8
  | 11 => match lo with
    | 0 => 0xe7#8 | 1 => 0xc8#8 | 2 => 0x37#8 | 3 => 0x6d#8
    | 4 => 0x8d#8 | 5 => 0xd5#8 | 6 => 0x4e#8 | 7 => 0xa9#8
    | 8 => 0x6c#8 | 9 => 0x56#8 | 10 => 0xf4#8 | 11 => 0xea#8
    | 12 => 0x65#8 | 13 => 0x7a#8 | 14 => 0xae#8 | _ => 0x08#8
  | 12 => match lo with
    | 0 => 0xba#8 | 1 => 0x78#8 | 2 => 0x25#8 | 3 => 0x2e#8
    | 4 => 0x1c#8 | 5 => 0xa6#8 | 6 => 0xb4#8 | 7 => 0xc6#8
    | 8 => 0xe8#8 | 9 => 0xdd#8 | 10 => 0x74#8 | 11 => 0x1f#8
    | 12 => 0x4b#8 | 13 => 0xbd#8 | 14 => 0x8b#8 | _ => 0x8a#8
  | 13 => match lo with
    | 0 => 0x70#8 | 1 => 0x3e#8 | 2 => 0xb5#8 | 3 => 0x66#8
    | 4 => 0x48#8 | 5 => 0x03#8 | 6 => 0xf6#8 | 7 => 0x0e#8
    | 8 => 0x61#8 | 9 => 0x35#8 | 10 => 0x57#8 | 11 => 0xb9#8
    | 12 => 0x86#8 | 13 => 0xc1#8 | 14 => 0x1d#8 | _ => 0x9e#8
  | 14 => match lo with
    | 0 => 0xe1#8 | 1 => 0xf8#8 | 2 => 0x98#8 | 3 => 0x11#8
    | 4 => 0x69#8 | 5 => 0xd9#8 | 6 => 0x8e#8 | 7 => 0x94#8
    | 8 => 0x9b#8 | 9 => 0x1e#8 | 10 => 0x87#8 | 11 => 0xe9#8
    | 12 => 0xce#8 | 13 => 0x55#8 | 14 => 0x28#8 | _ => 0xdf#8
  | _ => match lo with
    | 0 => 0x8c#8 | 1 => 0xa1#8 | 2 => 0x89#8 | 3 => 0x0d#8
    | 4 => 0xbf#8 | 5 => 0xe6#8 | 6 => 0x42#8 | 7 => 0x68#8
    | 8 => 0x41#8 | 9 => 0x99#8 | 10 => 0x2d#8 | 11 => 0x0f#8
    | 12 => 0xb0#8 | 13 => 0x54#8 | 14 => 0xbb#8 | _ => 0x16#8

def aesInvSbox (b : BitVec 8) : BitVec 8 :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  match hi with
  | 0 => match lo with
    | 0 => 0x52#8 | 1 => 0x09#8 | 2 => 0x6a#8 | 3 => 0xd5#8
    | 4 => 0x30#8 | 5 => 0x36#8 | 6 => 0xa5#8 | 7 => 0x38#8
    | 8 => 0xbf#8 | 9 => 0x40#8 | 10 => 0xa3#8 | 11 => 0x9e#8
    | 12 => 0x81#8 | 13 => 0xf3#8 | 14 => 0xd7#8 | _ => 0xfb#8
  | 1 => match lo with
    | 0 => 0x7c#8 | 1 => 0xe3#8 | 2 => 0x39#8 | 3 => 0x82#8
    | 4 => 0x9b#8 | 5 => 0x2f#8 | 6 => 0xff#8 | 7 => 0x87#8
    | 8 => 0x34#8 | 9 => 0x8e#8 | 10 => 0x43#8 | 11 => 0x44#8
    | 12 => 0xc4#8 | 13 => 0xde#8 | 14 => 0xe9#8 | _ => 0xcb#8
  | 2 => match lo with
    | 0 => 0x54#8 | 1 => 0x7b#8 | 2 => 0x94#8 | 3 => 0x32#8
    | 4 => 0xa6#8 | 5 => 0xc2#8 | 6 => 0x23#8 | 7 => 0x3d#8
    | 8 => 0xee#8 | 9 => 0x4c#8 | 10 => 0x95#8 | 11 => 0x0b#8
    | 12 => 0x42#8 | 13 => 0xfa#8 | 14 => 0xc3#8 | _ => 0x4e#8
  | 3 => match lo with
    | 0 => 0x08#8 | 1 => 0x2e#8 | 2 => 0xa1#8 | 3 => 0x66#8
    | 4 => 0x28#8 | 5 => 0xd9#8 | 6 => 0x24#8 | 7 => 0xb2#8
    | 8 => 0x76#8 | 9 => 0x5b#8 | 10 => 0xa2#8 | 11 => 0x49#8
    | 12 => 0x6d#8 | 13 => 0x8b#8 | 14 => 0xd1#8 | _ => 0x25#8
  | 4 => match lo with
    | 0 => 0x72#8 | 1 => 0xf8#8 | 2 => 0xf6#8 | 3 => 0x64#8
    | 4 => 0x86#8 | 5 => 0x68#8 | 6 => 0x98#8 | 7 => 0x16#8
    | 8 => 0xd4#8 | 9 => 0xa4#8 | 10 => 0x5c#8 | 11 => 0xcc#8
    | 12 => 0x5d#8 | 13 => 0x65#8 | 14 => 0xb6#8 | _ => 0x92#8
  | 5 => match lo with
    | 0 => 0x6c#8 | 1 => 0x70#8 | 2 => 0x48#8 | 3 => 0x50#8
    | 4 => 0xfd#8 | 5 => 0xed#8 | 6 => 0xb9#8 | 7 => 0xda#8
    | 8 => 0x5e#8 | 9 => 0x15#8 | 10 => 0x46#8 | 11 => 0x57#8
    | 12 => 0xa7#8 | 13 => 0x8d#8 | 14 => 0x9d#8 | _ => 0x84#8
  | 6 => match lo with
    | 0 => 0x90#8 | 1 => 0xd8#8 | 2 => 0xab#8 | 3 => 0x00#8
    | 4 => 0x8c#8 | 5 => 0xbc#8 | 6 => 0xd3#8 | 7 => 0x0a#8
    | 8 => 0xf7#8 | 9 => 0xe4#8 | 10 => 0x58#8 | 11 => 0x05#8
    | 12 => 0xb8#8 | 13 => 0xb3#8 | 14 => 0x45#8 | _ => 0x06#8
  | 7 => match lo with
    | 0 => 0xd0#8 | 1 => 0x2c#8 | 2 => 0x1e#8 | 3 => 0x8f#8
    | 4 => 0xca#8 | 5 => 0x3f#8 | 6 => 0x0f#8 | 7 => 0x02#8
    | 8 => 0xc1#8 | 9 => 0xaf#8 | 10 => 0xbd#8 | 11 => 0x03#8
    | 12 => 0x01#8 | 13 => 0x13#8 | 14 => 0x8a#8 | _ => 0x6b#8
  | 8 => match lo with
    | 0 => 0x3a#8 | 1 => 0x91#8 | 2 => 0x11#8 | 3 => 0x41#8
    | 4 => 0x4f#8 | 5 => 0x67#8 | 6 => 0xdc#8 | 7 => 0xea#8
    | 8 => 0x97#8 | 9 => 0xf2#8 | 10 => 0xcf#8 | 11 => 0xce#8
    | 12 => 0xf0#8 | 13 => 0xb4#8 | 14 => 0xe6#8 | _ => 0x73#8
  | 9 => match lo with
    | 0 => 0x96#8 | 1 => 0xac#8 | 2 => 0x74#8 | 3 => 0x22#8
    | 4 => 0xe7#8 | 5 => 0xad#8 | 6 => 0x35#8 | 7 => 0x85#8
    | 8 => 0xe2#8 | 9 => 0xf9#8 | 10 => 0x37#8 | 11 => 0xe8#8
    | 12 => 0x1c#8 | 13 => 0x75#8 | 14 => 0xdf#8 | _ => 0x6e#8
  | 10 => match lo with
    | 0 => 0x47#8 | 1 => 0xf1#8 | 2 => 0x1a#8 | 3 => 0x71#8
    | 4 => 0x1d#8 | 5 => 0x29#8 | 6 => 0xc5#8 | 7 => 0x89#8
    | 8 => 0x6f#8 | 9 => 0xb7#8 | 10 => 0x62#8 | 11 => 0x0e#8
    | 12 => 0xaa#8 | 13 => 0x18#8 | 14 => 0xbe#8 | _ => 0x1b#8
  | 11 => match lo with
    | 0 => 0xfc#8 | 1 => 0x56#8 | 2 => 0x3e#8 | 3 => 0x4b#8
    | 4 => 0xc6#8 | 5 => 0xd2#8 | 6 => 0x79#8 | 7 => 0x20#8
    | 8 => 0x9a#8 | 9 => 0xdb#8 | 10 => 0xc0#8 | 11 => 0xfe#8
    | 12 => 0x78#8 | 13 => 0xcd#8 | 14 => 0x5a#8 | _ => 0xf4#8
  | 12 => match lo with
    | 0 => 0x1f#8 | 1 => 0xdd#8 | 2 => 0xa8#8 | 3 => 0x33#8
    | 4 => 0x88#8 | 5 => 0x07#8 | 6 => 0xc7#8 | 7 => 0x31#8
    | 8 => 0xb1#8 | 9 => 0x12#8 | 10 => 0x10#8 | 11 => 0x59#8
    | 12 => 0x27#8 | 13 => 0x80#8 | 14 => 0xec#8 | _ => 0x5f#8
  | 13 => match lo with
    | 0 => 0x60#8 | 1 => 0x51#8 | 2 => 0x7f#8 | 3 => 0xa9#8
    | 4 => 0x19#8 | 5 => 0xb5#8 | 6 => 0x4a#8 | 7 => 0x0d#8
    | 8 => 0x2d#8 | 9 => 0xe5#8 | 10 => 0x7a#8 | 11 => 0x9f#8
    | 12 => 0x93#8 | 13 => 0xc9#8 | 14 => 0x9c#8 | _ => 0xef#8
  | 14 => match lo with
    | 0 => 0xa0#8 | 1 => 0xe0#8 | 2 => 0x3b#8 | 3 => 0x4d#8
    | 4 => 0xae#8 | 5 => 0x2a#8 | 6 => 0xf5#8 | 7 => 0xb0#8
    | 8 => 0xc8#8 | 9 => 0xeb#8 | 10 => 0xbb#8 | 11 => 0x3c#8
    | 12 => 0x83#8 | 13 => 0x53#8 | 14 => 0x99#8 | _ => 0x61#8
  | _ => match lo with
    | 0 => 0x17#8 | 1 => 0x2b#8 | 2 => 0x04#8 | 3 => 0x7e#8
    | 4 => 0xba#8 | 5 => 0x77#8 | 6 => 0xd6#8 | 7 => 0x26#8
    | 8 => 0xe1#8 | 9 => 0x69#8 | 10 => 0x14#8 | 11 => 0x63#8
    | 12 => 0x55#8 | 13 => 0x21#8 | 14 => 0x0c#8 | _ => 0x7d#8

def gfMul2 (b : BitVec 8) : BitVec 8 :=
  let shifted := b <<< 1
  if b.msb then shifted ^^^ 0x1b#8 else shifted

def gfMul3  (b : BitVec 8) : BitVec 8 := gfMul2 b ^^^ b

def gfXtimeNat (n : Nat) : Nat :=
  let s := Nat.land (n * 2) 0xff
  if Nat.ble 128 n then Nat.xor s 0x1b else s

def gfMul9  (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  BitVec.ofNat 8 (Nat.xor (gfXtimeNat (gfXtimeNat (gfXtimeNat n))) n)
def gfMul11 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n2 := gfXtimeNat n
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat (gfXtimeNat n2)) n2) n)
def gfMul13 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n4 := gfXtimeNat (gfXtimeNat n)
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat n4) n4) n)
def gfMul14 (b : BitVec 8) : BitVec 8 :=
  let n := b.toNat
  let n2 := gfXtimeNat n
  let n4 := gfXtimeNat n2
  BitVec.ofNat 8 (Nat.xor (Nat.xor (gfXtimeNat n4) n4) n2)

def aesShiftRows128 (s : BitVec 128) : BitVec 128 :=
  let b := getByte128 s
  ((b 11 ++ (b 6  ++ (b 1  ++ b 12))) ++ (b 7  ++ (b 2  ++ (b 13 ++ b 8)))) ++
  ((b 3  ++ (b 14 ++ (b 9  ++ b 4)))  ++ (b 15 ++ (b 10 ++ (b 5  ++ b 0))))

def aesInvShiftRows128 (s : BitVec 128) : BitVec 128 :=
  let b := getByte128 s
  ((b 3  ++ (b 6  ++ (b 9  ++ b 12))) ++ (b 15 ++ (b 2  ++ (b 5  ++ b 8)))) ++
  ((b 11 ++ (b 14 ++ (b 1  ++ b 4)))  ++ (b 7  ++ (b 10 ++ (b 13 ++ b 0))))

def aesSubBytes128 (s : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => aesSbox (getByte128 s i)

def aesInvSubBytes128 (s : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => aesInvSbox (getByte128 s i)

def aesMixCol32 (col : BitVec 32) : BitVec 32 :=
  let s0 := BitVec.extractLsb' 0  8 col
  let s1 := BitVec.extractLsb' 8  8 col
  let s2 := BitVec.extractLsb' 16 8 col
  let s3 := BitVec.extractLsb' 24 8 col
  let r0 := gfMul2 s0 ^^^ gfMul3 s1 ^^^ s2 ^^^ s3
  let r1 := s0 ^^^ gfMul2 s1 ^^^ gfMul3 s2 ^^^ s3
  let r2 := s0 ^^^ s1 ^^^ gfMul2 s2 ^^^ gfMul3 s3
  let r3 := gfMul3 s0 ^^^ s1 ^^^ s2 ^^^ gfMul2 s3
  (r3 ++ r2) ++ (r1 ++ r0)

def aesInvMixCol32 (col : BitVec 32) : BitVec 32 :=
  let s0 := BitVec.extractLsb' 0  8 col
  let s1 := BitVec.extractLsb' 8  8 col
  let s2 := BitVec.extractLsb' 16 8 col
  let s3 := BitVec.extractLsb' 24 8 col
  let r0 := gfMul14 s0 ^^^ gfMul11 s1 ^^^ gfMul13 s2 ^^^ gfMul9  s3
  let r1 := gfMul9  s0 ^^^ gfMul14 s1 ^^^ gfMul11 s2 ^^^ gfMul13 s3
  let r2 := gfMul13 s0 ^^^ gfMul9  s1 ^^^ gfMul14 s2 ^^^ gfMul11 s3
  let r3 := gfMul11 s0 ^^^ gfMul13 s1 ^^^ gfMul9  s2 ^^^ gfMul14 s3
  (r3 ++ r2) ++ (r1 ++ r0)

def aeseVec (data key : BitVec 128) : BitVec 128 :=
  aesSubBytes128 (aesShiftRows128 (data ^^^ key))

def aesmcVec (data : BitVec 128) : BitVec 128 :=
  packWords128 fun c => aesMixCol32 (getWord128 data c)

def aesdVec (data key : BitVec 128) : BitVec 128 :=
  aesInvSubBytes128 (aesInvShiftRows128 (data ^^^ key))

def aesimcVec (data : BitVec 128) : BitVec 128 :=
  packWords128 fun c => aesInvMixCol32 (getWord128 data c)

/-- SHA-256 (`sha256.ml:62-215`) & SHA-512 (`sha512.ml:41-210`) Crypto Extensions. -/
def rotr32 (x : BitVec 32) (n : Nat) : BitVec 32 :=
  (x >>> n) ||| (x <<< (32 - n))

def sha256HashStep (x y : BitVec 128) (wk : BitVec 32) : BitVec 128 × BitVec 128 :=
  let x0 := getWord128 x 0; let x1 := getWord128 x 1; let x2 := getWord128 x 2; let x3 := getWord128 x 3
  let y0 := getWord128 y 0; let y1 := getWord128 y 1; let y2 := getWord128 y 2; let y3 := getWord128 y 3
  let chs := ((y1 ^^^ y2) &&& y0) ^^^ y2
  let maj := (x0 &&& x1) ||| ((x0 ||| x1) &&& x2)
  let sig1 := rotr32 y0 6 ^^^ rotr32 y0 11 ^^^ rotr32 y0 25
  let sig0 := rotr32 x0 2 ^^^ rotr32 x0 13 ^^^ rotr32 x0 22
  let t := y3 + sig1 + chs + wk
  let xUp := t + x3
  let yUp := t + sig0 + maj
  -- `<Y, X> = ROL(Y : X, 32)` (`sha256.ml:75-78`)
  let x' := ((x2 ++ x1) ++ (x0 ++ yUp))
  let y' := ((y2 ++ y1) ++ (y0 ++ xUp))
  (x', y')

def sha256Hash4 (x y w : BitVec 128) (part1 : Bool) : BitVec 128 :=
  let (x1, y1) := sha256HashStep x  y  (getWord128 w 0)
  let (x2, y2) := sha256HashStep x1 y1 (getWord128 w 1)
  let (x3, y3) := sha256HashStep x2 y2 (getWord128 w 2)
  let (x4, y4) := sha256HashStep x3 y3 (getWord128 w 3)
  if part1 then x4 else y4

def sha256su0Vec (d n : BitVec 128) : BitVec 128 :=
  let t : BitVec 128 := (getWord128 n 0) ++ (BitVec.extractLsb' 32 96 d)
  packWords128 fun e =>
    let elt := getWord128 t e
    let s0 := rotr32 elt 7 ^^^ rotr32 elt 18 ^^^ (elt >>> 3)
    s0 + getWord128 d e

def sha256su1Vec (d n m : BitVec 128) : BitVec 128 :=
  let t0 : BitVec 128 := (getWord128 m 0) ++ (BitVec.extractLsb' 32 96 n)
  let s1 (elt : BitVec 32) : BitVec 32 := rotr32 elt 17 ^^^ rotr32 elt 19 ^^^ (elt >>> 10)
  let r0 := s1 (getWord128 m 2) + getWord128 d 0 + getWord128 t0 0
  let r1 := s1 (getWord128 m 3) + getWord128 d 1 + getWord128 t0 1
  let r2 := s1 r0               + getWord128 d 2 + getWord128 t0 2
  let r3 := s1 r1               + getWord128 d 3 + getWord128 t0 3
  ((r3 ++ r2) ++ (r1 ++ r0))

def rotr64 (x : BitVec 64) (n : Nat) : BitVec 64 :=
  (x >>> n) ||| (x <<< (64 - n))

def sha512SumSigma0 (x : BitVec 64) : BitVec 64 := rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39
def sha512SumSigma1 (x : BitVec 64) : BitVec 64 := rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41
def sha512SchedSigma0 (x : BitVec 64) : BitVec 64 := rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)
def sha512SchedSigma1 (x : BitVec 64) : BitVec 64 := rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

def sha512hVec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0; let x1 := getDword128 x 1
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  let vtmp1 := ((y1 &&& x0) ^^^ ((~~~y1) &&& x1)) + sha512SumSigma1 y1 + w1
  let tmp   := vtmp1 + y0
  let vtmp0 := ((tmp &&& y1) ^^^ ((~~~tmp) &&& x0)) + sha512SumSigma1 tmp + w0
  packDwords128 vtmp1 vtmp0

def sha512h2Vec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  let vtmp1 := ((x0 &&& y1) ^^^ (x0 &&& y0) ^^^ (y1 &&& y0)) + sha512SumSigma0 y0 + w1
  let vtmp0 := ((vtmp1 &&& y0) ^^^ (vtmp1 &&& y1) ^^^ (y1 &&& y0)) + sha512SumSigma0 vtmp1 + w0
  packDwords128 vtmp1 vtmp0

def sha512su0Vec (w x : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1; let x0 := getDword128 x 0
  packDwords128 (w1 + sha512SchedSigma0 x0) (w0 + sha512SchedSigma0 w1)

def sha512su1Vec (w x y : BitVec 128) : BitVec 128 :=
  let w0 := getDword128 w 0; let w1 := getDword128 w 1
  let x0 := getDword128 x 0; let x1 := getDword128 x 1
  let y0 := getDword128 y 0; let y1 := getDword128 y 1
  packDwords128 (w1 + sha512SchedSigma1 x1 + y1) (w0 + sha512SchedSigma1 x0 + y0)

def execNeonInstr (ins : Instr) (s : MachineState) : Option MachineState :=
  let nextPc := s.pc + 4#64
  match ins with
  | .ldstSimd load vw vt rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let sAfterMem : MachineState :=
        if load then
          let val := match vw with
            | .q128 => readMem128 s.mem ea
            | .d64  => (readMem64 s.mem ea).zeroExtend 128
          writeVec vw s vt val
        else
          let v := readVec s vt
          let m' := match vw with
            | .q128 => writeMem128 s.mem ea v
            | .d64  => writeMem64  s.mem ea (BitVec.extractLsb' 0 64 v)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .ldstPairSimd load vw vt1 vt2 rn mode =>
    match evalAddrMode s rn mode with
    | .error f => some { s with fault := some f }
    | .ok (ea, wbOpt) =>
      let stepBytes : BitVec 64 := match vw with | .q128 => 16#64 | .d64 => 8#64
      let sAfterMem : MachineState :=
        if load then
          let v1 := match vw with
            | .q128 => readMem128 s.mem ea
            | .d64  => (readMem64  s.mem ea).zeroExtend 128
          let v2 := match vw with
            | .q128 => readMem128 s.mem (ea + stepBytes)
            | .d64  => (readMem64  s.mem (ea + stepBytes)).zeroExtend 128
          let s1 := writeVec vw s vt1 v1
          writeVec vw s1 vt2 v2
        else
          let v1 := readVec s vt1
          let v2 := readVec s vt2
          let m' := match vw with
            | .q128 => writeMem128 (writeMem128 s.mem ea v1) (ea + stepBytes) v2
            | .d64  => writeMem64  (writeMem64  s.mem ea (BitVec.extractLsb' 0 64 v1))
                                   (ea + stepBytes) (BitVec.extractLsb' 0 64 v2)
          { s with mem := m', excl := none }
      let sWb := match wbOpt with
        | some wbVal => writeSp .x64 sAfterMem rn wbVal
        | none       => sAfterMem
      some { sWb with pc := nextPc }

  | .neonMovi vw vd imm64 =>
    let val128 : BitVec 128 := imm64 ++ imm64
    let s1 := writeVec vw s vd val128
    some { s1 with pc := nextPc }

  | .neonDupGp vw es vd rn =>
    let g := readXzr .x64 s rn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun _ => BitVec.extractLsb' 0 8  g
      | .e16 => packHalfs128 fun _ => BitVec.extractLsb' 0 16 g
      | .e32 => packWords128 fun _ => BitVec.extractLsb' 0 32 g
      | .e64 => g ++ g
    let s1 := writeVec vw s vd val128
    some { s1 with pc := nextPc }

  -- `FMOV Sd, Wn` / `FMOV Dd, Xn`: zeroes upper `[127:32]` or `[127:64]`!
  | .fmovGpToVec w vd rn =>
    let g := readXzr w s rn
    let val128 : BitVec 128 := match w with
      | .w32 => (BitVec.extractLsb' 0 32 g).zeroExtend 128
      | .x64 => g.zeroExtend 128
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  -- `FMOV Wd, Sn` / `FMOV Xd, Dn`: zeroes `X[d][63:32]` on 32-bit `Wd`!
  | .fmovVecToGp w rd vn =>
    let v := readVec s vn
    let val64 : BitVec 64 := match w with
      | .w32 => (BitVec.extractLsb' 0 32 v).zeroExtend 64
      | .x64 => BitVec.extractLsb' 0 64 v
    let s1 := writeXzr w s rd val64
    some { s1 with pc := nextPc }

  | .neonUmov es rd vn idx =>
    let v := readVec s vn
    let (gpw, val64) : GpWidth × BitVec 64 := match es with
      | .e8  => (.w32, (getByte128  v (idx % 16)).zeroExtend 64)
      | .e16 => (.w32, (getHalf128  v (idx % 8)).zeroExtend 64)
      | .e32 => (.w32, (getWord128  v (idx % 4)).zeroExtend 64)
      | .e64 => (.x64, getDword128 v (idx % 2))
    let s1 := writeXzr gpw s rd val64
    some { s1 with pc := nextPc }

  | .neonInsGp es vd rn idx =>
    let cur := readVec s vd
    let g   := readXzr .x64 s rn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => if i == (idx % 16) then BitVec.extractLsb' 0 8  g else getByte128 cur i
      | .e16 => packHalfs128 fun i => if i == (idx % 8)  then BitVec.extractLsb' 0 16 g else getHalf128 cur i
      | .e32 => packWords128 fun i => if i == (idx % 4)  then BitVec.extractLsb' 0 32 g else getWord128 cur i
      | .e64 =>
        if (idx % 2) == 0 then packDwords128 (getDword128 cur 1) g
        else packDwords128 g (getDword128 cur 0)
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  | .neonInsElt es vd vn dstIdx srcIdx =>
    let cur := readVec s vd
    let src := readVec s vn
    let val128 : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => if i == (dstIdx % 16) then getByte128 src (srcIdx % 16) else getByte128 cur i
      | .e16 => packHalfs128 fun i => if i == (dstIdx % 8)  then getHalf128 src (srcIdx % 8)  else getHalf128 cur i
      | .e32 => packWords128 fun i => if i == (dstIdx % 4)  then getWord128 src (srcIdx % 4)  else getWord128 cur i
      | .e64 =>
        let el := getDword128 src (srcIdx % 2)
        if (dstIdx % 2) == 0 then packDwords128 (getDword128 cur 1) el
        else packDwords128 el (getDword128 cur 0)
    let s1 := writeVec .q128 s vd val128
    some { s1 with pc := nextPc }

  | .neonLogic vw op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match op with
      | .and_ => n &&& m
      | .bic  => n &&& (~~~m)
      | .orr  => n ||| m
      | .eor  => n ^^^ m
      | .bsl  => (n &&& d) ||| (m &&& (~~~d))
      | .bit_ => (n &&& m) ||| (d &&& (~~~m))
      | .bif_ => (d &&& m) ||| (n &&& (~~~m))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonArith vw es op vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match op, es with
      | .add,   .e8  => packBytes128 fun i => getByte128 n i + getByte128 m i
      | .add,   .e16 => packHalfs128 fun i => getHalf128 n i + getHalf128 m i
      | .add,   .e32 => packWords128 fun i => getWord128 n i + getWord128 m i
      | .add,   .e64 => packDwords128 (getDword128 n 1 + getDword128 m 1) (getDword128 n 0 + getDword128 m 0)
      | .sub,   .e8  => packBytes128 fun i => getByte128 n i - getByte128 m i
      | .sub,   .e16 => packHalfs128 fun i => getHalf128 n i - getHalf128 m i
      | .sub,   .e32 => packWords128 fun i => getWord128 n i - getWord128 m i
      | .sub,   .e64 => packDwords128 (getDword128 n 1 - getDword128 m 1) (getDword128 n 0 - getDword128 m 0)
      | .uqadd, .e8  => packBytes128 fun i => uqaddW 8  (getByte128 n i) (getByte128 m i)
      | .uqadd, .e16 => packHalfs128 fun i => uqaddW 16 (getHalf128 n i) (getHalf128 m i)
      | .uqadd, .e32 => packWords128 fun i => uqaddW 32 (getWord128 n i) (getWord128 m i)
      | .uqadd, .e64 => packDwords128 (uqaddW 64 (getDword128 n 1) (getDword128 m 1)) (uqaddW 64 (getDword128 n 0) (getDword128 m 0))
      | .uqsub, .e8  => packBytes128 fun i => uqsubW 8  (getByte128 n i) (getByte128 m i)
      | .uqsub, .e16 => packHalfs128 fun i => uqsubW 16 (getHalf128 n i) (getHalf128 m i)
      | .uqsub, .e32 => packWords128 fun i => uqsubW 32 (getWord128 n i) (getWord128 m i)
      | .uqsub, .e64 => packDwords128 (uqsubW 64 (getDword128 n 1) (getDword128 m 1)) (uqsubW 64 (getDword128 n 0) (getDword128 m 0))
      | .sqadd, .e8  => packBytes128 fun i => sqaddW 8  (getByte128 n i) (getByte128 m i)
      | .sqadd, .e16 => packHalfs128 fun i => sqaddW 16 (getHalf128 n i) (getHalf128 m i)
      | .sqadd, .e32 => packWords128 fun i => sqaddW 32 (getWord128 n i) (getWord128 m i)
      | .sqadd, .e64 => packDwords128 (sqaddW 64 (getDword128 n 1) (getDword128 m 1)) (sqaddW 64 (getDword128 n 0) (getDword128 m 0))
      | .sqsub, .e8  => packBytes128 fun i => sqsubW 8  (getByte128 n i) (getByte128 m i)
      | .sqsub, .e16 => packHalfs128 fun i => sqsubW 16 (getHalf128 n i) (getHalf128 m i)
      | .sqsub, .e32 => packWords128 fun i => sqsubW 32 (getWord128 n i) (getWord128 m i)
      | .sqsub, .e64 => packDwords128 (sqsubW 64 (getDword128 n 1) (getDword128 m 1)) (sqsubW 64 (getDword128 n 0) (getDword128 m 0))
      | .addp,  .e8  =>
        match vw with
        | .q128 => packBytes128 fun i =>
          if i < 8 then getByte128 n (2 * i) + getByte128 n (2 * i + 1)
          else getByte128 m (2 * (i - 8)) + getByte128 m (2 * (i - 8) + 1)
        | .d64  => packBytes128 fun i =>
          if i < 4 then getByte128 n (2 * i) + getByte128 n (2 * i + 1)
          else if i < 8 then getByte128 m (2 * (i - 4)) + getByte128 m (2 * (i - 4) + 1)
          else 0#8
      | .addp,  .e16 =>
        match vw with
        | .q128 => packHalfs128 fun i =>
          if i < 4 then getHalf128 n (2 * i) + getHalf128 n (2 * i + 1)
          else getHalf128 m (2 * (i - 4)) + getHalf128 m (2 * (i - 4) + 1)
        | .d64  => packHalfs128 fun i =>
          if i < 2 then getHalf128 n (2 * i) + getHalf128 n (2 * i + 1)
          else if i < 4 then getHalf128 m (2 * (i - 2)) + getHalf128 m (2 * (i - 2) + 1)
          else 0#16
      | .addp,  .e32 =>
        match vw with
        | .q128 => packWords128 fun i =>
          if i < 2 then getWord128 n (2 * i) + getWord128 n (2 * i + 1)
          else getWord128 m (2 * (i - 2)) + getWord128 m (2 * (i - 2) + 1)
        | .d64  => packWords128 fun i =>
          if i == 0 then getWord128 n 0 + getWord128 n 1
          else if i == 1 then getWord128 m 0 + getWord128 m 1
          else 0#32
      | .addp,  .e64 =>
        packDwords128 (getDword128 m 0 + getDword128 m 1) (getDword128 n 0 + getDword128 n 1)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonCmp vw es op vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let mask8  (p : Bool) : BitVec 8  := if p then 0xff#8 else 0#8
    let mask16 (p : Bool) : BitVec 16 := if p then 0xffff#16 else 0#16
    let mask32 (p : Bool) : BitVec 32 := if p then 0xffffffff#32 else 0#32
    let mask64 (p : Bool) : BitVec 64 := if p then 0xffffffffffffffff#64 else 0#64
    let cmpW {k : Nat} (x y : BitVec k) : Bool :=
      match op with
      | .cmeq     => x == y
      | .cmgt     => decide (x.toInt > y.toInt)
      | .cmhi     => decide (x.toNat > y.toNat)
      | .cmge     => decide (x.toInt >= y.toInt)
      | .cmeqZero => x == 0#k
      | .cmltZero => x.msb
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => mask8  (cmpW (getByte128 n i) (getByte128 m i))
      | .e16 => packHalfs128 fun i => mask16 (cmpW (getHalf128 n i) (getHalf128 m i))
      | .e32 => packWords128 fun i => mask32 (cmpW (getWord128 n i) (getWord128 m i))
      | .e64 => packDwords128 (mask64 (cmpW (getDword128 n 1) (getDword128 m 1)))
                              (mask64 (cmpW (getDword128 n 0) (getDword128 m 0)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonShiftImm vw es op vd vn amt =>
    let n := readVec s vn
    let shW (k : Nat) (x : BitVec k) : BitVec k :=
      match op with
      | .shl  => if amt >= k then 0#k else x <<< amt
      | .ushr => if amt >= k then 0#k else x >>> amt
      | .sshr => BitVec.sshiftRight x (if amt >= k then k - 1 else amt)
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => shW 8  (getByte128 n i)
      | .e16 => packHalfs128 fun i => shW 16 (getHalf128 n i)
      | .e32 => packWords128 fun i => shW 32 (getWord128 n i)
      | .e64 => packDwords128 (shW 64 (getDword128 n 1)) (shW 64 (getDword128 n 0))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonShiftVar vw es signed vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let fnW (k : Nat) (x : BitVec k) (sh : BitVec 8) : BitVec k :=
      if signed then neonSshlLane k x sh else neonUshlLane k x sh
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => fnW 8  (getByte128 n i) (getByte128 m i)
      | .e16 => packHalfs128 fun i => fnW 16 (getHalf128 n i) (BitVec.extractLsb' 0 8 (getHalf128 m i))
      | .e32 => packWords128 fun i => fnW 32 (getWord128 n i) (BitVec.extractLsb' 0 8 (getWord128 m i))
      | .e64 => packDwords128 (fnW 64 (getDword128 n 1) (BitVec.extractLsb' 0 8 (getDword128 m 1)))
                              (fnW 64 (getDword128 n 0) (BitVec.extractLsb' 0 8 (getDword128 m 0)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonUaddlp vw es vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := match es with
      | .e8  => packHalfs128 fun i => (getByte128 n (2 * i)).zeroExtend 16 + (getByte128 n (2 * i + 1)).zeroExtend 16
      | .e16 => packWords128 fun i => (getHalf128 n (2 * i)).zeroExtend 32 + (getHalf128 n (2 * i + 1)).zeroExtend 32
      | _    => packDwords128 ((getWord128 n 2).zeroExtend 64 + (getWord128 n 3).zeroExtend 64)
                              ((getWord128 n 0).zeroExtend 64 + (getWord128 n 1).zeroExtend 64)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  -- Across-vector scalar reductions (`instruction.ml:1872, 1922, 2625`):
  -- writes zero-extended result into `V[Rd][127:0]`, zeroing all upper bits!
  | .neonReduce vw es op vd vn =>
    let n := readVec s vn
    let datasize := match vw with | .q128 => 128 | .d64 => 64
    let esBits := es.bits
    let lanes := datasize / esBits
    let res128 : BitVec 128 := match op with
      | .uaddlv => (BitVec.ofNat (2 * esBits) (uaddlvLoop lanes esBits n)).zeroExtend 128
      | .addv   => (BitVec.ofNat esBits       (uaddlvLoop lanes esBits n)).zeroExtend 128
      | .umaxv  => (BitVec.ofNat esBits       (umaxvLoop  lanes esBits n)).zeroExtend 128
      | .uminv  => (BitVec.ofNat esBits       (uminvLoop  lanes esBits n)).zeroExtend 128
    let s1 := writeVec .q128 s vd res128
    some { s1 with pc := nextPc }

  | .neonRev64 vw es vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := match es with
      | .e8  => packBytes128 fun i => getByte128 n ((i / 8) * 8 + (7 - (i % 8)))
      | .e16 => packHalfs128 fun i => getHalf128 n ((i / 4) * 4 + (3 - (i % 4)))
      | _    => packWords128 fun i => getWord128 n ((i / 2) * 2 + (1 - (i % 2)))
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonExt vw vd vn vm imm4 =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match vw with
      | .q128 => packBytes128 fun i =>
        let k := i + imm4
        if k < 16 then getByte128 n k else getByte128 m (k - 16)
      | .d64  => packBytes128 fun i =>
        if i >= 8 then 0#8
        else
          let k := i + imm4
          if k < 8 then getByte128 n k else getByte128 m (k - 8)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonTbl1 vw vd vn vm =>
    let tbl := readVec s vn
    let idx := readVec s vm
    let res : BitVec 128 := packBytes128 fun i =>
      let b := (getByte128 idx i).toNat
      if b < 16 then getByte128 tbl b else 0#8
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonCnt vw vd vn =>
    let n := readVec s vn
    let res : BitVec 128 := packBytes128 fun i => popcntByte (getByte128 n i)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonPmul vw vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := packBytes128 fun i => pmulByte (getByte128 n i) (getByte128 m i)
    let s1 := writeVec vw s vd res
    some { s1 with pc := nextPc }

  | .neonPmull high es vd vn vm =>
    let n := readVec s vn
    let m := readVec s vm
    let res : BitVec 128 := match es with
      | .e8  =>
        let off := if high then 8 else 0
        packHalfs128 fun i => pmullByte (getByte128 n (off + i)) (getByte128 m (off + i))
      | _    =>
        let lane := if high then 1 else 0
        pmull64 (getDword128 n lane) (getDword128 m lane)
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoAes op vd vn =>
    let d := readVec s vd
    let n := readVec s vn
    let res := match op with
      | .aese   => aeseVec d n
      | .aesmc  => aesmcVec n
      | .aesd   => aesdVec d n
      | .aesimc => aesimcVec n
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoSha256 op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res := match op with
      | .h   => sha256Hash4 d n m true
      | .h2  => sha256Hash4 n d m false
      | .su0 => sha256su0Vec d n
      | .su1 => sha256su1Vec d n m
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | .cryptoSha512 op vd vn vm =>
    let d := readVec s vd
    let n := readVec s vn
    let m := readVec s vm
    let res := match op with
      | .h   => sha512hVec d n m
      | .h2  => sha512h2Vec d n m
      | .su0 => sha512su0Vec d n
      | .su1 => sha512su1Vec d n m
    let s1 := writeVec .q128 s vd res
    some { s1 with pc := nextPc }

  | _ => none

end VendorArm64Ref
"""

MACHINE_LEAN = LEAN_HEADER + r"""
prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import VendorArm64Ref.Decode
import VendorArm64Ref.SemanticsScalar
import VendorArm64Ref.SemanticsNeon

/-!
# `VendorArm64Ref.Machine`

Top-level AArch64 Pass-2 single-step and `N`-step operational machine
(`execStep`, `execStepsN`, `Step`, `StepsN`, and `execStepsN_implies_stepsN`).
-/

namespace VendorArm64Ref

def execInstr (exclSpuriousFail : Bool) (lse2Align16B : Bool) (ins : Instr)
    (s : MachineState) : MachineState :=
  match execScalarInstr exclSpuriousFail lse2Align16B ins s with
  | some s' => s'
  | none =>
    match execNeonInstr ins s with
    | some s' => s'
    | none => { s with fault := some .undefinedEncoding }

def execStep (code : CodeMap) (exclSpuriousFail : Bool) (lse2Align16B : Bool)
    (s : MachineState) : MachineState :=
  if s.halted || s.fault.isSome then s
  else
    match fetchWord32 code s.pc with
    | .error f => { s with fault := some f }
    | .ok w =>
      match decodeWord32 w with
      | .error f => { s with fault := some f }
      | .ok ins  => execInstr exclSpuriousFail lse2Align16B ins s

def execStepsN (code : CodeMap) (exclSpuriousFail : Bool) (lse2Align16B : Bool)
    (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec (motive := fun _ => MachineState → MachineState)
    (fun st => st)
    (fun _ ih st => ih (execStep code exclSpuriousFail lse2Align16B st))
    n s

/-- Normative Pass-2 relational single-step transition (`Step`):
    quantifies over demonic `ExclusiveMonitorsPass` spurious clear (`exclSpuriousFail : Bool`). -/
def Step (code : CodeMap) (lse2Align16B : Bool) (s s' : MachineState) : Prop :=
  ∃ exclSpuriousFail : Bool, execStep code exclSpuriousFail lse2Align16B s = s'

inductive StepsN (code : CodeMap) (lse2Align16B : Bool) : Nat → MachineState → MachineState → Prop where
  | zero (s : MachineState) : StepsN code lse2Align16B 0 s s
  | step {n : Nat} {s s1 s2 : MachineState} :
      Step code lse2Align16B s s1 →
      StepsN code lse2Align16B n s1 s2 →
      StepsN code lse2Align16B (n + 1) s s2

theorem execStepsN_implies_stepsN (code : CodeMap) (exclSpuriousFail : Bool)
    (lse2Align16B : Bool) (n : Nat) (s : MachineState) :
    StepsN code lse2Align16B n s (execStepsN code exclSpuriousFail lse2Align16B n s) :=
  Nat.rec (motive := fun k => ∀ st, StepsN code lse2Align16B k st (execStepsN code exclSpuriousFail lse2Align16B k st))
    (fun st => StepsN.zero st)
    (fun _ ih st =>
      StepsN.step ⟨exclSpuriousFail, rfl⟩ (ih (execStep code exclSpuriousFail lse2Align16B st)))
    n s

/-- Computable, kernel-reducible `Nat.rec` list lookup (`0` `isPartial`, instant WHNF on concrete lists). -/
def listGetOpt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  let tail := Nat.rec (motive := fun _ => List α)
    xs
    (fun _ cur => match cur with | [] => [] | _ :: tl => tl)
    idx
  match tail with
  | hd :: _ => some hd
  | []      => none

def loadWordsAt (base : BitVec 64) (words : List (BitVec 32)) : CodeMap :=
  fun addr =>
    let off := (addr - base).toNat
    let wIdx := off / 4
    let bIdx := off % 4
    if addr == base + BitVec.ofNat 64 off then
      match listGetOpt words wIdx with
      | some w => some (BitVec.extractLsb' (bIdx * 8) 8 w)
      | none   => none
    else none

end VendorArm64Ref
"""


def emit_vendor_arm64_lean(out_dir: Path) -> dict[str, dict]:
    pkg_dir = out_dir / "VendorArm64Ref"
    pkg_dir.mkdir(parents=True, exist_ok=True)
    files = {
        "VendorArm64Ref/Types.lean": TYPES_LEAN.lstrip("\n"),
        "VendorArm64Ref/Decode.lean": DECODE_LEAN.lstrip("\n"),
        "VendorArm64Ref/SemanticsScalar.lean": SEMANTICS_SCALAR_LEAN.lstrip("\n"),
        "VendorArm64Ref/SemanticsNeon.lean": SEMANTICS_NEON_LEAN.lstrip("\n"),
        "VendorArm64Ref/Machine.lean": MACHINE_LEAN.lstrip("\n"),
    }
    stats: dict[str, dict] = {}
    for rel, content in files.items():
        fp = out_dir / rel
        raw = content.encode("utf-8")
        fp.write_bytes(raw)
        stats[rel] = {
            "bytes": len(raw),
            "lines": len(content.splitlines()),
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
    return stats


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--s2n-dir", type=Path, default=None)
    parser.add_argument("--emit-lean-dir", type=Path, required=True)
    parser.add_argument("--audit-json", type=Path, default=None)
    args = parser.parse_args()

    emitted = emit_vendor_arm64_lean(args.emit_lean_dir)
    if args.s2n_dir is not None:
        parsed = parse_s2n_arm_sources(args.s2n_dir)
        report = {
            "upstream": parsed,
            "opcode_slice": OPCODE_SLICE_SPEC,
            "emitted_lean_modules": emitted,
        }
        if args.audit_json is not None:
            args.audit_json.write_text(
                json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
        print(json.dumps({"emitted": emitted, "upstream_summary": {
            k: v for k, v in parsed.items() if k != "verified_blobs"
        }}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
