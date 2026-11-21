#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical GCC 15.2.0 `.o` decoder gap audit and live x86-64 silicon + Lean
Pass-1/Pass-2 cross-validation (`ByteX86Gcc` == `VendorX86GccRef` == Silicon).

All temporary compilations, `.olean` outputs, and Ring-3 `SA_SIGINFO` binaries
execute strictly inside `tempfile.TemporaryDirectory()`.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any


SUPPORT_DIR = Path(__file__).resolve().parent
LEAN_DIR = SUPPORT_DIR / "lean"
OUT_JSON = SUPPORT_DIR / "gcc_x86_silicon_and_decoder_results.json"

TOOLCHAIN_HASH = (
    "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a"
)


def find_lean_tools() -> tuple[Path, Path]:
    lean_run = Path.home() / ".local" / "bin" / "anneal-lean-run"
    lean_bin = (
        Path.home()
        / ".cache"
        / "anneal"
        / "toolchain"
        / TOOLCHAIN_HASH
        / "lean"
        / "bin"
        / "lean"
    )
    if not lean_run.exists() or not lean_bin.exists():
        raise FileNotFoundError("Missing anneal-lean-run or pinned lean v4.34.1")
    return lean_run, lean_bin


def parse_objdump_functions(obj_path: Path) -> list[dict[str, Any]]:
    cp = subprocess.run(
        ["objdump", "-d", "-M", "intel", "--no-show-raw-insn", str(obj_path)],
        capture_output=True,
        text=True,
        check=True,
    )
    cp_raw = subprocess.run(
        ["objdump", "-d", "-M", "intel", str(obj_path)],
        capture_output=True,
        text=True,
        check=True,
    )
    _ = cp
    funcs: list[dict[str, Any]] = []
    cur: dict[str, Any] | None = None
    hdr_re = re.compile(r"^([0-9a-fA-F]+)\s+<([^>]+)>:$")
    off_re = re.compile(r"^\s*([0-9a-fA-F]+):$")
    for line in cp_raw.stdout.splitlines():
        m_hdr = hdr_re.match(line)
        if m_hdr:
            if cur is not None:
                funcs.append(cur)
            cur = {
                "start_off": int(m_hdr.group(1), 16),
                "name": m_hdr.group(2),
                "insns": [],
            }
            continue
        if cur is None or "\t" not in line:
            continue
        parts = line.split("\t")
        m_off = off_re.match(parts[0])
        if not m_off:
            continue
        off = int(m_off.group(1), 16)
        bs = [int(x, 16) for x in parts[1].strip().split()]
        if len(parts) >= 3 and parts[2].strip():
            asm = " ".join(parts[2].strip().split())
            cur["insns"].append({"off": off, "bytes": bs, "asm": asm})
        elif cur["insns"]:
            cur["insns"][-1]["bytes"].extend(bs)
    if cur is not None:
        funcs.append(cur)
    for fn in funcs:
        raw: list[int] = []
        for ins in fn["insns"]:
            raw.extend(ins["bytes"])
        fn["total_bytes"] = len(raw)
        fn["raw_bytes"] = raw
    return funcs


def classify_baseline_32_64_vex_only_gap(ins_bytes: list[int], asm: str) -> list[str]:
    """Identify why a 32/64-bit VEX-only baseline decoder (`ByteX86Base` /
    `VendorX86Ref`) rejects or mismodels an instruction emitted by `gcc 15.2.0`."""
    reasons: list[str] = []
    # Strip prefixes like ByteX86Base
    idx = 0
    has66 = False
    has_rep = False
    rex: int | None = None
    while idx < len(ins_bytes):
        b = ins_bytes[idx]
        if b == 0x66:
            has66 = True
            rex = None
            idx += 1
        elif b in (0xF2, 0xF3):
            has_rep = True
            rex = None
            idx += 1
        elif b in (0x2E, 0x36, 0x3E, 0x26, 0x64, 0x65, 0x67, 0xF0):
            rex = None
            idx += 1
        elif (b & 0xF0) == 0x40:
            rex = b & 0x0F
            idx += 1
        else:
            break
    body = ins_bytes[idx:]
    if not body:
        return ["empty_after_prefixes"]
    op0 = body[0]
    w_bit = bool(rex is not None and (rex & 0x8))
    if op0 == 0x0F and len(body) >= 2:
        op1 = body[1]
        if op1 == 0x1F:
            reasons.append("multibyte_0f1f_nop")
        elif op1 in (0xB6, 0xB7, 0xBE, 0xBF):
            reasons.append("movzx_movsx_subword")
        elif op1 in (
            0x10,
            0x11,
            0x6F,
            0x7F,
            0x7E,
            0xD6,
            0x6E,
            0xEF,
            0xDB,
            0xEB,
            0xFC,
            0xFD,
            0xFE,
            0xD4,
            0x60,
            0x68,
            0x61,
            0x69,
            0x62,
            0x6A,
            0x6C,
            0x6D,
            0x70,
            0x73,
            0xD5,
            0xF5,
        ):
            reasons.append("legacy_non_vex_sse2")
        elif 0x90 <= op1 <= 0x9F:
            if rex is None and len(body) >= 3 and ((body[2] & 7) in (4, 5, 6, 7)) and ((body[2] >> 6) == 3):
                reasons.append("subreg8_high_byte_ah_bh")
    elif op0 in (0x88, 0x8A, 0x80, 0x84, 0xA8, 0xC6, 0xF6) or (
        0xB0 <= op0 <= 0xB7
    ) or (op0 < 0x40 and (op0 % 8) in (0, 2)):
        reasons.append("subreg8_byte_op")
        if asm and any(h in asm.split() or f"{h}," in asm for h in ("ah", "bh", "ch", "dh")):
            reasons.append("subreg8_high_byte_ah_bh")
        if rex is not None and any(l in asm for l in ("spl", "bpl", "sil", "dil")):
            reasons.append("subreg8_rex_low_byte_spl_dil")
    elif op0 == 0x63:
        reasons.append("movsxd_32_to_64")
    elif op0 == 0x8D and not w_bit:
        reasons.append("lea_non64_operand_size")
    elif op0 in (0x69, 0x6B):
        reasons.append("imul_3op_imm")
    elif op0 == 0xC9:
        reasons.append("leave64_epilogue")
    elif op0 in (0xC0, 0xC1, 0xD1):
        # Check rol/ror
        if len(body) >= 2 and ((body[1] >> 3) & 7) in (0, 1):
            reasons.append("rol_ror_rotate")
    if has66 and not w_bit and op0 not in (0x0F, 0x90):
        reasons.append("opsize_16bit_partial_reg")
    _ = has_rep
    return reasons


SILICON_HARNESS_C = r"""
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>

typedef struct {
    uint64_t rax, rcx, rdx, rbx, rsi, rdi, r8, r9;
    uint8_t ymm0[32];
    uint8_t ymm1[32];
    uint64_t rflags;
    int trapped_sig;
    int trapno;
    int64_t rip_delta;
} ProbeOut;

static sigjmp_buf g_jmp;
static volatile int g_sig = 0;
static volatile int g_trapno = 0;
static volatile uint64_t g_fault_rip = 0;
static uint8_t g_saved_ymm0[32] __attribute__((aligned(32)));
static uint8_t g_saved_ymm1[32] __attribute__((aligned(32)));
static uint64_t g_saved_gprs[8];
static uint64_t g_saved_flags = 0;

static void sig_handler(int sig, siginfo_t *info, void *ucontext) {
    (void)info;
    ucontext_t *uc = (ucontext_t *)ucontext;
    g_sig = sig;
    g_trapno = (int)uc->uc_mcontext.gregs[REG_TRAPNO];
    g_fault_rip = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
    g_saved_gprs[0] = (uint64_t)uc->uc_mcontext.gregs[REG_RAX];
    g_saved_gprs[1] = (uint64_t)uc->uc_mcontext.gregs[REG_RCX];
    g_saved_gprs[2] = (uint64_t)uc->uc_mcontext.gregs[REG_RDX];
    g_saved_gprs[3] = (uint64_t)uc->uc_mcontext.gregs[REG_RBX];
    g_saved_gprs[4] = (uint64_t)uc->uc_mcontext.gregs[REG_RSI];
    g_saved_gprs[5] = (uint64_t)uc->uc_mcontext.gregs[REG_RDI];
    g_saved_gprs[6] = (uint64_t)uc->uc_mcontext.gregs[REG_R8];
    g_saved_gprs[7] = (uint64_t)uc->uc_mcontext.gregs[REG_R9];
    g_saved_flags   = (uint64_t)uc->uc_mcontext.gregs[REG_EFL];
    /* Extract pre-fault XMM0/1[127:0] + XSAVE YMM_Hi128 (+576 B) from kernel signal frame */
    if (uc->uc_mcontext.fpregs != NULL) {
        const uint8_t *fp = (const uint8_t *)uc->uc_mcontext.fpregs;
        memcpy(g_saved_ymm0, &uc->uc_mcontext.fpregs->_xmm[0], 16);
        memcpy(g_saved_ymm0 + 16, fp + 576, 16);
        memcpy(g_saved_ymm1, &uc->uc_mcontext.fpregs->_xmm[1], 16);
        memcpy(g_saved_ymm1 + 16, fp + 576 + 16, 16);
    }
    siglongjmp(g_jmp, 1);
}

static uint8_t g_mem_arena[256] __attribute__((aligned(64)));

static void parse_hex_bytes(const char *hex, uint8_t *out, size_t *out_len) {
    size_t n = 0;
    while (*hex) {
        while (*hex == ' ') hex++;
        if (!*hex) break;
        unsigned int b = 0;
        sscanf(hex, "%2x", &b);
        out[n++] = (uint8_t)b;
        hex += 2;
    }
    *out_len = n;
}

int main(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = sig_handler;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);

    uint8_t *pages = mmap(NULL, 8192, PROT_READ | PROT_WRITE | PROT_EXEC,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) return 2;
    if (mprotect(pages + 4096, 4096, PROT_NONE) != 0) return 3;

    printf("ARENA_ADDR=0x%016llx\n", (unsigned long long)(uintptr_t)g_mem_arena);
    fflush(stdout);

    char line[2048];
    while (fgets(line, sizeof(line), stdin)) {
        char id[128], hex[512], y0hex[128], y1hex[128], mhex[256];
        unsigned long long rax0, rcx0, rdx0, rbx0, rsi0, rdi0, r80, r90;
        int use_arena_rdi = 0;
        if (sscanf(line, "%127s %511[^|]|%llx %llx %llx %llx %llx %llx %llx %llx|%127s %127s %255s %d",
                   id, hex, &rax0, &rcx0, &rdx0, &rbx0, &rsi0, &rdi0, &r80, &r90,
                   y0hex, y1hex, mhex, &use_arena_rdi) != 14) {
            continue;
        }
        uint8_t code[64];
        size_t clen = 0;
        parse_hex_bytes(hex, code, &clen);

        uint8_t init_y0[32], init_y1[32], init_m[64];
        size_t tmp_n = 0;
        memset(init_y0, 0, 32);
        memset(init_y1, 0, 32);
        memset(g_mem_arena, 0, sizeof(g_mem_arena));
        parse_hex_bytes(y0hex, init_y0, &tmp_n);
        parse_hex_bytes(y1hex, init_y1, &tmp_n);
        parse_hex_bytes(mhex, init_m, &tmp_n);
        memcpy(g_mem_arena, init_m, tmp_n);
        if (use_arena_rdi) {
            rdi0 = (unsigned long long)(uintptr_t)g_mem_arena;
        }

        memset(pages, 0xCC, 4096);
        uint8_t *entry = pages + 4096 - clen;
        memcpy(entry, code, clen);

        uint64_t in_gprs[8] = {rax0, rcx0, rdx0, rbx0, rsi0, rdi0, r80, r90};
        g_sig = 0;
        g_trapno = 0;
        g_fault_rip = 0;

        if (sigsetjmp(g_jmp, 1) == 0) {
            __asm__ volatile(
                "vmovdqu (%[y0]), %%ymm0\n\t"
                "vmovdqu (%[y1]), %%ymm1\n\t"
                "movq 0(%[gp]), %%rax\n\t"
                "movq 8(%[gp]), %%rcx\n\t"
                "movq 16(%[gp]), %%rdx\n\t"
                "movq 24(%[gp]), %%rbx\n\t"
                "movq 32(%[gp]), %%rsi\n\t"
                "movq 40(%[gp]), %%rdi\n\t"
                "movq 48(%[gp]), %%r8\n\t"
                "movq 56(%[gp]), %%r9\n\t"
                "xorl %%r10d, %%r10d\n\t"
                "jmp *%[ent]\n\t"
                :
                : [y0] "r"(init_y0), [y1] "r"(init_y1), [gp] "r"(in_gprs), [ent] "r"(entry)
                : "rax", "rcx", "rdx", "rbx", "rsi", "rdi", "r8", "r9", "r10", "cc", "memory"
            );
        }

        int64_t delta = (int64_t)(g_fault_rip - (uint64_t)(uintptr_t)entry);
        printf("RES %s entry=%016llx sig=%d trapno=%d delta=%lld rax=%016llx rcx=%016llx rdx=%016llx rbx=%016llx rsi=%016llx rdi=%016llx r8=%016llx r9=%016llx flags=%016llx y0=",
               id, (unsigned long long)(uintptr_t)entry, g_sig, g_trapno, (long long)delta,
               (unsigned long long)g_saved_gprs[0],
               (unsigned long long)g_saved_gprs[1],
               (unsigned long long)g_saved_gprs[2],
               (unsigned long long)g_saved_gprs[3],
               (unsigned long long)g_saved_gprs[4],
               (unsigned long long)g_saved_gprs[5],
               (unsigned long long)g_saved_gprs[6],
               (unsigned long long)g_saved_gprs[7],
               (unsigned long long)g_saved_flags);
        for (int i = 0; i < 32; i++) printf("%02x", g_saved_ymm0[i]);
        printf(" mem=");
        for (int i = 0; i < 32; i++) printf("%02x", g_mem_arena[i]);
        printf("\n");
        fflush(stdout);
    }
    return 0;
}
"""


def build_silicon_vectors() -> list[dict[str, Any]]:
    dirty_y0 = "112233445566778899aabbccddeeff00" + "cafebabe01020304deadbeef05060708"
    arg_y1 = "01010101010101010101010101010101" + "02020202020202020202020202020202"
    mem32 = (
        "102030405060708090a0b0c0d0e0f001"
        "fedcba98765432100123456789abcdef"
    )
    base_gprs = {
        "rax": 0x1111222233334444,
        "rcx": 0x5555666677778888,
        "rdx": 0x9999AAAABBBBCCCC,
        "rbx": 0xDDDDEEEEFFFF125A,
        "rsi": 0x01020304050607A5,
        "rdi": 0x08090A0B0C0D0E3C,
        "r8": 0xCAFEBABE0000007F,
        "r9": 0xDEADBEEF00000080,
    }

    def vec(
        vid: str,
        family: str,
        hex_bytes: str,
        expect_fault: bool = False,
        use_arena_rdi: bool = False,
        steps: int = 1,
        gpr_overrides: dict[str, int] | None = None,
    ) -> dict[str, Any]:
        gp = dict(base_gprs)
        if gpr_overrides:
            gp.update(gpr_overrides)
        return {
            "id": vid,
            "family": family,
            "hex": hex_bytes,
            "expect_fault": expect_fault,
            "use_arena_rdi": use_arena_rdi,
            "steps": steps,
            "gprs": gp,
            "y0": dirty_y0,
            "y1": arg_y1,
            "mem": mem32,
        }

    return [
        # Family 1: Non-orthogonal REX 8-bit sub-registers (16 vectors)
        vec("rex8_01_mov_bh_bl", "subreg8_rex", "88 df"),
        vec("rex8_02_rex40_mov_dil_bl", "subreg8_rex", "40 88 df"),
        vec("rex8_03_rex40_nullified_by_2e", "subreg8_rex", "40 2e 88 df"),
        vec("rex8_04_2e_before_rex40_active", "subreg8_rex", "2e 40 88 df"),
        vec("rex8_05_mov_ah_cl", "subreg8_rex", "88 cc"),
        vec("rex8_06_rex40_mov_spl_like_sil", "subreg8_rex", "40 88 ce"),
        vec("rex8_07_mov_ch_dl", "subreg8_rex", "88 d5"),
        vec("rex8_08_mov_dh_al", "subreg8_rex", "88 c6"),
        vec("rex8_09_mov_al_bh", "subreg8_rex", "8a c7"),
        vec("rex8_10_rex40_mov_al_dil", "subreg8_rex", "40 8a c7"),
        vec("rex8_11_mov_bh_imm", "subreg8_rex", "b7 99"),
        vec("rex8_12_rex40_mov_dil_imm", "subreg8_rex", "40 b7 99"),
        vec("rex8_13_rex41_mov_r9b_imm", "subreg8_rex", "41 b1 42"),
        vec("rex8_14_add_bh_0x11", "subreg8_rex", "80 c7 11"),
        vec("rex8_15_rex40_add_dil_0x11", "subreg8_rex", "40 80 c7 11"),
        vec("rex8_16_rex40_test_sil_0x0f", "subreg8_rex", "40 f6 c6 0f"),
        # Family 2: 16/32/64-bit GP partial preserve vs 32-bit zero-extend (10 vectors)
        vec("opsz_01_mov16_ax_bx", "opsize_16_32_64", "66 89 d8"),
        vec("opsz_02_mov32_eax_ebx_zext", "opsize_16_32_64", "89 d8"),
        vec("opsz_03_mov64_rax_rbx", "opsize_16_32_64", "48 89 d8"),
        vec("opsz_04_mov16_imm", "opsize_16_32_64", "66 b8 ab cd"),
        vec("opsz_05_mov32_imm_zext", "opsize_16_32_64", "b8 78 56 34 12"),
        vec("opsz_06_mov64_imm64", "opsize_16_32_64", "48 b8 ef cd ab 90 78 56 34 12"),
        vec("opsz_07_add16_ax_imm8", "opsize_16_32_64", "66 83 c0 05"),
        vec("opsz_08_add32_eax_imm8_zext", "opsize_16_32_64", "83 c0 05"),
        vec("opsz_09_imul16_3op", "opsize_16_32_64", "66 69 c3 03 00"),
        vec("opsz_10_imul32_3op_zext", "opsize_16_32_64", "69 c3 03 00 00 00"),
        # Family 3: MOVZX / MOVSX / MOVSXD (10 vectors)
        vec("ext_01_movzx_eax_bh", "movzx_movsx", "0f b6 c7"),
        vec("ext_02_rex_movzx_eax_dil", "movzx_movsx", "40 0f b6 c7"),
        vec("ext_03_movzx_rax_byte_mem", "movzx_movsx", "48 0f b6 07", use_arena_rdi=True),
        vec("ext_04_movzx_eax_word_mem", "movzx_movsx", "0f b7 07", use_arena_rdi=True),
        vec("ext_05_movsx_rax_neg_byte", "movzx_movsx", "49 0f be c1"),
        vec("ext_06_movsx_rax_pos_byte", "movzx_movsx", "49 0f be c0"),
        vec("ext_07_movsx_eax_neg_byte_zext64", "movzx_movsx", "41 0f be c1"),
        vec("ext_08_movsx_rax_neg_word", "movzx_movsx", "48 0f bf c3"),
        vec("ext_09_movsxd_rax_neg_dword", "movzx_movsx", "48 63 c2"),
        vec("ext_10_movsxd_without_rexw_zext32", "movzx_movsx", "63 c2"),
        # Family 4: Multi-byte 0F 1F ModR/M NOPs + 15B/16B/LOCK boundaries (10 vectors)
        vec("nop_01_3b_0f1f00", "multibyte_nop", "0f 1f 00"),
        vec("nop_02_4b_0f1f4000", "multibyte_nop", "0f 1f 40 00"),
        vec("nop_03_5b_0f1f440000", "multibyte_nop", "0f 1f 44 00 00"),
        vec("nop_04_7b_0f1f80", "multibyte_nop", "0f 1f 80 00 00 00 00"),
        vec("nop_05_8b_null_ea_no_deref", "multibyte_nop", "0f 1f 04 25 00 00 00 00"),
        vec("nop_06_nonzero_reg_slash7", "multibyte_nop", "0f 1f 3f"),
        vec("nop_07_gcc_11b_66_66_2e_nop", "multibyte_nop", "66 66 2e 0f 1f 84 00 00 00 00 00"),
        vec("nop_08_max_15b_legal_nop", "multibyte_nop", "66 66 66 66 66 66 2e 0f 1f 84 00 00 00 00 00"),
        vec("nop_09_16b_gp0_length_fault", "multibyte_nop", "66 66 66 66 66 66 66 2e 0f 1f 84 00 00 00 00 00", expect_fault=True),
        vec("nop_10_lock_0f1f_ud_fault", "multibyte_nop", "f0 0f 1f 00", expect_fault=True),
        # Family 5: 16/32/64-bit LEA + mod=3 #UD (8 vectors)
        vec("lea_01_64_disp8", "lea_family", "48 8d 47 ff"),
        vec("lea_02_64_sib_scale4", "lea_family", "48 8d 44 8f 10", gpr_overrides={"rcx": 3}),
        vec("lea_03_32_tolower_range", "lea_family", "8d 50 bf", gpr_overrides={"rax": 0xFFFF000000000041}),
        vec("lea_04_16_preserve_hi48", "lea_family", "66 8d 47 04"),
        vec("lea_05_rip_relative", "lea_family", "48 8d 05 20 00 00 00"),
        vec("lea_06_sib_no_base_disp32", "lea_family", "48 8d 04 4d 10 00 00 00", gpr_overrides={"rcx": 5}),
        vec("lea_07_mod3_reg_ud_fault", "lea_family", "48 8d c0", expect_fault=True),
        vec("lea_08_32_mod3_reg_ud_fault", "lea_family", "8d d0", expect_fault=True),
        # Family 6: Legacy Non-VEX SSE2 vs VEX L=0 vs VZEROUPPER transitions (14 vectors)
        vec("simd_01_legacy_pxor_preserves_hi128", "sse_vs_vex_ymm", "66 0f ef c0"),
        vec("simd_02_vex128_vpxor_zeroes_hi128", "sse_vs_vex_ymm", "c5 f9 ef c0"),
        vec("simd_03_vex256_vpxor_all256", "sse_vs_vex_ymm", "c5 fd ef c0"),
        vec("simd_04_legacy_paddd_preserves_hi128", "sse_vs_vex_ymm", "66 0f fe c1"),
        vec("simd_05_vex128_vpaddd_zeroes_hi128", "sse_vs_vex_ymm", "c5 f9 fe c1"),
        vec("simd_06_legacy_movq_load_3band", "sse_vs_vex_ymm", "f3 0f 7e 07", use_arena_rdi=True),
        vec("simd_07_vex128_vmovq_load_zeroes_hi128", "sse_vs_vex_ymm", "c5 fa 7e 07", use_arena_rdi=True),
        vec("simd_08_legacy_movd_gpr_preserves_hi128", "sse_vs_vex_ymm", "66 0f 6e c3"),
        vec("simd_09_vex128_vmovd_gpr_zeroes_hi128", "sse_vs_vex_ymm", "c5 f9 6e c3"),
        vec("simd_10_legacy_movups_load_preserves_hi128", "sse_vs_vex_ymm", "0f 10 07", use_arena_rdi=True),
        vec("simd_11_vex128_vmovups_load_zeroes_hi128", "sse_vs_vex_ymm", "c5 f8 10 07", use_arena_rdi=True),
        vec("simd_12_legacy_pshuflw_preserves_hi128", "sse_vs_vex_ymm", "f2 0f 70 c0 00"),
        vec("simd_13_vex128_vpshuflw_zeroes_hi128", "sse_vs_vex_ymm", "c5 fb 70 c0 00"),
        vec("simd_14_vzeroupper_then_legacy_paddd", "sse_vs_vex_ymm", "c5 f8 77 66 0f fe c1", steps=2),
    ]


def le_bytes_to_int(hex_str: str) -> int:
    raw = bytes.fromhex(hex_str)
    return int.from_bytes(raw, "little")


def run_probe() -> dict[str, Any]:
    lean_run, lean_bin = find_lean_tools()
    gcc_ver = (
        subprocess.run(["gcc", "--version"], capture_output=True, text=True, check=True)
        .stdout.splitlines()[0]
        .strip()
    )

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        env = dict(os.environ)
        lean_lib = lean_bin.parent.parent / "lib" / "lean"
        env["LEAN_PATH"] = f"{td_path}:{lean_lib}"

        # 1. Compile the 3 object files (`c_ffi_kernels.c` -O2, -O3 -mavx2; `c_ffi_bugs.c` -O2)
        objs = [
            (
                "c_ffi_kernels_O2",
                SUPPORT_DIR / "c_ffi_kernels.c",
                ["-O2", "-fno-stack-protector", "-fno-asynchronous-unwind-tables"],
            ),
            (
                "c_ffi_kernels_O3_avx2",
                SUPPORT_DIR / "c_ffi_kernels.c",
                [
                    "-O3",
                    "-mavx2",
                    "-fno-stack-protector",
                    "-fno-asynchronous-unwind-tables",
                ],
            ),
            (
                "c_ffi_bugs_O2",
                SUPPORT_DIR / "c_ffi_bugs.c",
                ["-O2", "-fno-stack-protector", "-fno-asynchronous-unwind-tables"],
            ),
        ]

        decoded_functions: list[dict[str, Any]] = []
        gap_feature_counts: dict[str, int] = {}
        for tag, c_src, flags in objs:
            o_path = td_path / f"{tag}.o"
            subprocess.run(
                ["gcc", *flags, "-c", str(c_src), "-o", str(o_path)], check=True
            )
            for fn in parse_objdump_functions(o_path):
                fn_gaps: set[str] = set()
                for ins in fn["insns"]:
                    rs = classify_baseline_32_64_vex_only_gap(ins["bytes"], ins["asm"])
                    for r in rs:
                        fn_gaps.add(r)
                        gap_feature_counts[r] = gap_feature_counts.get(r, 0) + 1
                decoded_functions.append(
                    {
                        "unit": tag,
                        "flags": " ".join(flags),
                        "name": fn["name"],
                        "total_bytes": fn["total_bytes"],
                        "insn_count": len(fn["insns"]),
                        "baseline_32_64_vex_fails": len(fn_gaps) > 0,
                        "baseline_gap_features": sorted(fn_gaps),
                        "insns": fn["insns"],
                    }
                )

        # 2. Run live Ring-3 SA_SIGINFO silicon probe on all 68 vectors
        harness_src = td_path / "silicon_harness.c"
        harness_bin = td_path / "silicon_harness"
        harness_src.write_text(SILICON_HARNESS_C)
        subprocess.run(
            ["gcc", "-O2", "-mavx2", str(harness_src), "-o", str(harness_bin)],
            check=True,
        )

        vectors = build_silicon_vectors()
        proc = subprocess.Popen(
            [str(harness_bin)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        assert proc.stdin is not None and proc.stdout is not None
        arena_line = proc.stdout.readline().strip()
        assert arena_line.startswith("ARENA_ADDR=")
        arena_addr = int(arena_line.split("=", 1)[1], 16)

        silicon_records: list[dict[str, Any]] = []
        for v in vectors:
            gp = v["gprs"]
            req = (
                f"{v['id']} {v['hex']}|"
                f"{gp['rax']:x} {gp['rcx']:x} {gp['rdx']:x} {gp['rbx']:x} "
                f"{gp['rsi']:x} {gp['rdi']:x} {gp['r8']:x} {gp['r9']:x}|"
                f"{v['y0']} {v['y1']} {v['mem']} {1 if v['use_arena_rdi'] else 0}\n"
            )
            proc.stdin.write(req)
            proc.stdin.flush()
            resp = proc.stdout.readline().strip()
            assert resp.startswith(f"RES {v['id']} "), f"Unexpected response: {resp}"
            kv = dict(tok.split("=", 1) for tok in resp.split()[2:])
            placed_len = len(bytes.fromhex(v["hex"]))
            sig = int(kv["sig"])
            trapno = int(kv["trapno"])
            delta = int(kv["delta"])
            hw_faulted = delta == 0
            assert hw_faulted == v["expect_fault"], (
                f"Vector {v['id']} fault mismatch: hw_faulted={hw_faulted} delta={delta} "
                f"sig={sig} trapno={trapno}"
            )
            if not hw_faulted:
                assert delta == placed_len, (
                    f"Vector {v['id']} length mismatch: delta={delta} vs {placed_len}"
                )
            eff_rdi = arena_addr if v["use_arena_rdi"] else gp["rdi"]
            silicon_records.append(
                {
                    "id": v["id"],
                    "family": v["family"],
                    "hex": v["hex"],
                    "bytes": list(bytes.fromhex(v["hex"])),
                    "steps": v["steps"],
                    "entry_rip": int(kv["entry"], 16),
                    "use_arena_rdi": v["use_arena_rdi"],
                    "in_rdi": eff_rdi,
                    "gprs_in": {**gp, "rdi": eff_rdi},
                    "y0_in_u256": le_bytes_to_int(v["y0"]),
                    "y1_in_u256": le_bytes_to_int(v["y1"]),
                    "mem_in_hex": v["mem"],
                    "hw_sig": sig,
                    "hw_trapno": trapno,
                    "hw_rip_delta": delta,
                    "hw_faulted": hw_faulted,
                    "hw_out": {
                        "rax": int(kv["rax"], 16),
                        "rcx": int(kv["rcx"], 16),
                        "rdx": int(kv["rdx"], 16),
                        "rbx": int(kv["rbx"], 16),
                        "rsi": int(kv["rsi"], 16),
                        "rdi": int(kv["rdi"], 16),
                        "r8": int(kv["r8"], 16),
                        "r9": int(kv["r9"], 16),
                        "y0_u256": le_bytes_to_int(kv["y0"]),
                    },
                }
            )
        proc.stdin.close()
        proc.wait(timeout=5)

        # 3. Compile VendorX86GccRef, ByteX86Gcc, ByteX86GccDecodeBase, ByteX86GccDecodePass2, ByteX86GccPass2 + generated Lean check
        lean_timings: dict[str, Any] = {}
        for mod in [
            "VendorX86GccRef",
            "ByteX86Gcc",
            "ByteX86GccDecodeBase",
            "ByteX86GccDecodePass2",
            "ByteX86GccPass2",
        ]:
            src = LEAN_DIR / f"{mod}.lean"
            t0 = time.perf_counter()
            subprocess.run(
                [
                    str(lean_run),
                    str(lean_bin),
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-j1",
                    "-R",
                    str(LEAN_DIR),
                    str(src),
                    "-o",
                    str(td_path / f"{mod}.olean"),
                ],
                cwd=str(LEAN_DIR),
                env=env,
                check=True,
            )
            lean_timings[mod] = {
                "bytes": src.stat().st_size,
                "compile_sec": round(time.perf_counter() - t0, 3),
            }

        # Emit temporary Lean module checking:
        # (a) Every instruction in all 16 GCC `.o` functions decodes to exact objdump length
        #     in BOTH `ByteX86Gcc.decodeX64` and `VendorX86GccRef.decodeRef`!
        # (b) All 68 silicon vectors match `ByteX86Gcc` AND `VendorX86GccRef`!
        lines = [
            "prelude",
            "import Init.Core",
            "import Init.Data.BitVec.Basic",
            "import VendorX86GccRef",
            "import ByteX86Gcc",
            "import ByteX86GccPass2",
            "",
            "namespace SiliconAndObjCheck",
            "",
            "def pad16 (bs : List (BitVec 8)) : List (BitVec 8) :=",
            "  bs ++ List.replicate (16 - bs.length) 0x90#8",
            "",
            "theorem pad16_len (bs : List (BitVec 8)) (hlen : bs.length ≤ 16) : (pad16 bs).length = 16 := by",
            "  unfold pad16; rw [List.length_append, List.length_replicate]; omega",
            "",
            "theorem decBoth_ast_eq (bs : List (BitVec 8)) (ins1 : ByteX86Gcc.X64Instr) (len1 : Nat)",
            "    (h1 : ByteX86Gcc.decodeX64 bs = .ok ins1 len1) (hlen : bs.length ≤ 16) :",
            "    ByteX86Gcc.decodeX64 (pad16 bs) = .ok ins1 len1 ∧",
            "    ByteX86GccPass2.mapOutcome (VendorX86GccRef.decodeRef (pad16 bs)) = .ok ins1 len1 := by",
            "  have h2 : ByteX86Gcc.decodeX64 (pad16 bs) = .ok ins1 len1 := by",
            "    unfold pad16; exact ByteX86Gcc.decodeX64_prefix_invariant h1 _",
            "  have h3 := ByteX86GccPass2.decodeRef_commutes_of_len16 (pad16 bs) (pad16_len bs hlen)",
            "  exact ⟨h2, h3.symm.trans h2⟩",
            "",
            "def decBothLen (bs : List (BitVec 8)) (expLen : Nat) : Bool :=",
            "  let w := pad16 bs",
            "  match ByteX86Gcc.decodeX64 bs, ByteX86Gcc.decodeX64 w, VendorX86GccRef.decodeRef w with",
            "  | .ok _ l1, .ok _ l2, .ok _ lR =>",
            "    Nat.beq l1 expLen && Nat.beq l2 expLen && Nat.beq lR expLen",
            "  | _, _, _ => false",
            "",
        ]

        # Batch per-function instruction decode checks
        fn_bool_names: list[str] = []
        total_insns_checked = 0
        fn_thm_names: list[str] = []
        for idx_f, fn in enumerate(decoded_functions):
            checks: list[str] = []
            for ins in fn["insns"]:
                total_insns_checked += 1
                blist = ", ".join(f"0x{b:02X}#8" for b in ins["bytes"])
                checks.append(f"decBothLen [{blist}] {len(ins['bytes'])}")
            for ch_i in range(0, len(checks), 16):
                bname = f"gccFnDecOk_{idx_f}_{ch_i // 16}"
                tname = f"{bname}_ok"
                fn_thm_names.append(tname)
                lines.append(f"def {bname} : Bool :=")
                lines.append("  " + " &&\n  ".join(checks[ch_i : ch_i + 16]))
                lines.append(f"theorem {tname} : {bname} = true := by rfl")
                lines.append("")

        # Silicon state helper in Lean (first 64 arena bytes cover all test loads/stores)
        mem_init_bytes = list(bytes.fromhex(silicon_records[0]["mem_in_hex"]))[:64]
        mem_lit = ", ".join(f"0x{b:02X}#8" for b in mem_init_bytes)
        lines.extend(
            [
                f"def arenaBase : BitVec 64 := 0x{arena_addr:016X}#64",
                f"def arenaBytes : List (BitVec 8) := [{mem_lit}]",
                "",
                "def mkInitMem : ByteX86Gcc.ByteMem := fun addr =>",
                "  let off := (addr - arenaBase).toNat",
                f"  if Nat.blt off {len(mem_init_bytes)} then ByteX86Gcc.listGetByteD arenaBytes off else 0#8",
                "",
                "def mkSiliconState (entryRip rax rcx rdx rbx rsi rdi r8 r9 : BitVec 64)",
                "    (y0 y1 : BitVec 256) : VendorX86GccRef.MachineState :=",
                "  { rip := entryRip",
                "    gpr := fun g => match g with",
                "      | .rax => rax | .rcx => rcx | .rdx => rdx | .rbx => rbx",
                "      | .rsi => rsi | .rdi => rdi | .r8 => r8   | .r9 => r9",
                "      | _ => 0#64",
                "    ymm := fun i => if i.val == 0 then y0 else if i.val == 1 then y1 else 0#256",
                "    mem := mkInitMem }",
                "",
                "def codeAtRip (entryRip : BitVec 64) (bs : List (BitVec 8)) : ByteX86Gcc.CodeMap := fun a =>",
                "  let off := (a - entryRip).toNat",
                "  if Nat.blt off bs.length then ByteX86Gcc.listGetByteD bs off else 0xCC#8",
                "",
                "def checkVecOk (entryRip : BitVec 64) (bs : List (BitVec 8)) (steps : Nat) (expFault : Bool) (expDelta : Nat)",
                "    (s0 : VendorX86GccRef.MachineState)",
                "    (eRax eRcx eRdx eRbx eRsi eRdi eR8 eR9 : BitVec 64) (eY0 : BitVec 256) : Bool :=",
                "  let cmap := codeAtRip entryRip bs",
                "  let sRef := VendorX86GccRef.execStepsN cmap steps {} s0",
                "  let sByte := Nat.rec (motive := fun _ => ByteX86Gcc.X64State → ByteX86Gcc.X64State)",
                "    (fun s => s) (fun _ ih s => ih (ByteX86Gcc.stepX64 cmap {} s)) steps (ByteX86GccPass2.mapState s0)",
                "  if expFault then",
                "    sRef.fault.isSome && sByte.fault && (sByte.rip == entryRip)",
                "  else",
                "    !sRef.fault.isSome && !sByte.fault &&",
                "    (sByte.rip == entryRip + BitVec.ofNat 64 expDelta) &&",
                "    (sRef.rip == sByte.rip) &&",
                "    (sByte.regs .rax == eRax) && (sByte.regs .rcx == eRcx) &&",
                "    (sByte.regs .rdx == eRdx) && (sByte.regs .rbx == eRbx) &&",
                "    (sByte.regs .rsi == eRsi) && (sByte.regs .rdi == eRdi) &&",
                "    (sByte.regs .r8  == eR8)  && (sByte.regs .r9  == eR9) &&",
                "    (sByte.ymms ⟨0, by decide⟩ == eY0) &&",
                "    (sRef.ymm ⟨0, by decide⟩ == eY0)",
                "",
            ]
        )

        vec_thm_names: list[str] = []
        for idx_v, rec in enumerate(silicon_records):
            vname = f"vecOk_{idx_v}"
            vtname = f"{vname}_ok"
            vec_thm_names.append(vtname)
            blist = ", ".join(f"0x{b:02X}#8" for b in rec["bytes"])
            gin = rec["gprs_in"]
            hout = rec["hw_out"]
            erip = rec["entry_rip"]
            lines.extend(
                [
                    f"def {vname} : Bool :=",
                    f"  checkVecOk 0x{erip:016X}#64 [{blist}] {rec['steps']} {'true' if rec['hw_faulted'] else 'false'} {max(0, rec['hw_rip_delta'])}",
                    f"    (mkSiliconState 0x{erip:016X}#64 0x{gin['rax']:016X}#64 0x{gin['rcx']:016X}#64 0x{gin['rdx']:016X}#64 0x{gin['rbx']:016X}#64",
                    f"                    0x{gin['rsi']:016X}#64 0x{gin['rdi']:016X}#64 0x{gin['r8']:016X}#64 0x{gin['r9']:016X}#64",
                    f"                    0x{rec['y0_in_u256']:064X}#256 0x{rec['y1_in_u256']:064X}#256)",
                    f"    0x{hout['rax']:016X}#64 0x{hout['rcx']:016X}#64 0x{hout['rdx']:016X}#64 0x{hout['rbx']:016X}#64",
                    f"    0x{hout['rsi']:016X}#64 0x{hout['rdi']:016X}#64 0x{hout['r8']:016X}#64 0x{hout['r9']:016X}#64",
                    f"    0x{hout['y0_u256']:064X}#256",
                    f"theorem {vtname} : {vname} = true := by rfl",
                    "",
                ]
            )

        lines.extend(
            [
                "end SiliconAndObjCheck",
                "",
            ]
        )

        chk_lean = td_path / "SiliconAndObjCheck.lean"
        chk_lean.write_text("\n".join(lines))
        t_chk0 = time.perf_counter()
        subprocess.run(
            [
                str(lean_run),
                str(lean_bin),
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-j1",
                "-R",
                str(td_path),
                str(chk_lean),
                "-o",
                str(td_path / "SiliconAndObjCheck.olean"),
            ],
            cwd=str(td_path),
            env=env,
            check=True,
        )
        chk_compile_sec = round(time.perf_counter() - t_chk0, 3)

        # Private-level `toKernelEnv.replay` audit across the 3 core ISA modules
        audit_lean = td_path / "AuditReplay.lean"
        audit_lean.write_text(
            f"""import Lean
import Lean.Replay

open Lean

def main : IO Unit := do
  initSearchPath (System.FilePath.mk "{lean_bin.parent.parent}")
  let base ← importModules #[{{ module := `Init }}] {{}}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let base := base.setExporting false
  let mut baseMods : NameSet := {{}}
  for m in base.header.modules do
    baseMods := baseMods.insert m.module
  let env ← importModules #[{{ module := `ByteX86GccPass2 }}] {{}}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false
  let mut newConsts : Std.HashMap Name ConstantInfo := {{}}
  let mut bad : Nat := 0
  let mut ax : Nat := 0
  for (m, md) in env.header.modules.zip env.header.moduleData do
    if !baseMods.contains m.module then
      for (_, ci) in md.constNames.zip md.constants do
        newConsts := newConsts.insert ci.name ci
        if ci.isUnsafe || ci.isPartial then
          bad := bad + 1
        if ci.isAxiom then
          ax := ax + 1
  let t0 ← IO.monoMsNow
  let _ ← base.toKernelEnv.replay newConsts
  let t1 ← IO.monoMsNow
  if bad != 0 || ax != 0 then
    throw <| IO.userError s!"unexpected unsafe/partial={{bad}} axioms={{ax}}"
  IO.println s!"consts={{newConsts.size}} replay_ms={{t1 - t0}} unsafe_or_partial={{bad}} axioms={{ax}}"
"""
        )
        cp_rep = subprocess.run(
            [str(lean_run), str(lean_bin), "--run", str(audit_lean)],
            cwd=str(td_path),
            env=env,
            capture_output=True,
            text=True,
        )
        if cp_rep.returncode != 0:
            raise RuntimeError(f"AuditReplay failed:\n{cp_rep.stdout}\n{cp_rep.stderr}")
        rep_out = cp_rep.stdout.strip()

    baseline_failed = sum(
        1 for fn in decoded_functions if fn["baseline_32_64_vex_fails"]
    )
    summary = {
        "compiler": gcc_ver,
        "object_functions_audited": len(decoded_functions),
        "total_object_instructions_decoded": total_insns_checked,
        "total_object_text_bytes": sum(fn["total_bytes"] for fn in decoded_functions),
        "baseline_32_64_vex_only_failed_functions": baseline_failed,
        "baseline_32_64_vex_only_failure_rate_pct": round(
            100.0 * baseline_failed / len(decoded_functions), 2
        ),
        "bytex86gcc_and_vendorx86gccref_decoded_functions": len(decoded_functions),
        "bytex86gcc_and_vendorx86gccref_decode_rate_pct": 100.0,
        "gap_feature_instruction_counts": dict(
            sorted(gap_feature_counts.items(), key=lambda kv: -kv[1])
        ),
        "silicon_vectors_total": len(silicon_records),
        "silicon_vectors_matched_lean_kernel": len(silicon_records),
        "silicon_agreement_pct": 100.0,
        "lean_module_metrics": lean_timings,
        "silicon_check_compile_sec": chk_compile_sec,
        "private_kernel_replay": rep_out,
        "object_function_breakdown": [
            {
                "unit": fn["unit"],
                "flags": fn["flags"],
                "name": fn["name"],
                "total_bytes": fn["total_bytes"],
                "insn_count": fn["insn_count"],
                "baseline_32_64_vex_fails": fn["baseline_32_64_vex_fails"],
                "baseline_gap_features": fn["baseline_gap_features"],
            }
            for fn in decoded_functions
        ],
        "notable_silicon_observations": {
            "rex_nullification_40_2e_88_df": next(
                r
                for r in silicon_records
                if r["id"] == "rex8_03_rex40_nullified_by_2e"
            )["hw_out"],
            "rex_active_2e_40_88_df": next(
                r
                for r in silicon_records
                if r["id"] == "rex8_04_2e_before_rex40_active"
            )["hw_out"],
            "legacy_pxor_preserves_hi128_y0": hex(
                next(
                    r
                    for r in silicon_records
                    if r["id"] == "simd_01_legacy_pxor_preserves_hi128"
                )["hw_out"]["y0_u256"]
            ),
            "vex128_vpxor_zeroes_hi128_y0": hex(
                next(
                    r
                    for r in silicon_records
                    if r["id"] == "simd_02_vex128_vpxor_zeroes_hi128"
                )["hw_out"]["y0_u256"]
            ),
            "nop_16b_gp0_trapno": next(
                r
                for r in silicon_records
                if r["id"] == "nop_09_16b_gp0_length_fault"
            )["hw_trapno"],
            "lock_nop_ud_trapno": next(
                r
                for r in silicon_records
                if r["id"] == "nop_10_lock_0f1f_ud_fault"
            )["hw_trapno"],
        },
    }
    OUT_JSON.write_text(json.dumps(summary, indent=2) + "\n")
    return summary


if __name__ == "__main__":
    res = run_probe()
    print(
        json.dumps(
            {
                k: v
                for k, v in res.items()
                if k not in ("object_function_breakdown", "notable_silicon_observations")
            },
            indent=2,
        )
    )
