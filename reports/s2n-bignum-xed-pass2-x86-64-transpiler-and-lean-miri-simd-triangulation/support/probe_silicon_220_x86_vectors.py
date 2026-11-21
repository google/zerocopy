#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Execute 224 controlled x86-64 encoding, page-boundary trap (#UD / #GP(0)),
RFLAGS, LOCK atomic, BMI1/2/ADX, and VEX/EVEX 128/256-bit SIMD/AES/PCLMUL test
vectors on live Intel Xeon Ice Lake-SP AVX-512 silicon, and compare against
llvm-mc and GNU objdump inside tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

C_SILICON_HARNESS = r"""
#define _GNU_SOURCE
#include <errno.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>

static sigjmp_buf g_jmp;
static volatile int g_sig = 0;
static volatile uint64_t g_trapno = 0;
static volatile uint64_t g_err = 0;
static volatile uint64_t g_rip = 0;
static volatile uint64_t g_efl = 0;
static volatile uint64_t g_rax = 0;
static volatile uint64_t g_rcx = 0;
static volatile uint64_t g_rdx = 0;

static uint8_t g_ymm0_out[32] __attribute__((aligned(32)));
static uint64_t g_mem_arena[16] __attribute__((aligned(64)));

static void trap_handler(int sig, siginfo_t *si, void *uap) {
    (void)si;
    ucontext_t *uc = (ucontext_t *)uap;
    g_sig = sig;
    g_trapno = (uint64_t)uc->uc_mcontext.gregs[REG_TRAPNO];
    g_err = (uint64_t)uc->uc_mcontext.gregs[REG_ERR];
    g_rip = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
    g_efl = (uint64_t)uc->uc_mcontext.gregs[REG_EFL];
    g_rax = (uint64_t)uc->uc_mcontext.gregs[REG_RAX];
    g_rcx = (uint64_t)uc->uc_mcontext.gregs[REG_RCX];
    g_rdx = (uint64_t)uc->uc_mcontext.gregs[REG_RDX];
    siglongjmp(g_jmp, 1);
}

/* Save YMM0 inside normal completion stub placed right after tested instruction */
extern void save_ymm0_and_trap(void);
__asm__(
    ".text\n"
    ".globl save_ymm0_and_trap\n"
    "save_ymm0_and_trap:\n"
    "  vmovdqu (%r11), %ymm15\n" /* dummy read check */
    "  int3\n"
);

typedef struct {
    uint64_t rax_in, rcx_in, rdx_in, rsi_in, r8_in, efl_in, mem0_in, mem1_in;
    uint8_t ymm0_in[32];
    uint8_t ymm1_in[32];
    uint8_t ymm2_in[32];
    int measure_page_len;
} ExecInput;

static void run_at(uint8_t *start, const ExecInput *in) {
    g_mem_arena[0] = in->mem0_in;
    g_mem_arena[1] = in->mem1_in;
    g_mem_arena[2] = 0xCAFEBABE11223344ULL;
    g_mem_arena[3] = 0x5566778899AABBCCULL;
    memset(g_ymm0_out, 0, 32);

    if (sigsetjmp(g_jmp, 1) == 0) {
        uint64_t flags_clean = (in->efl_in & 0x8D5ULL) | 0x202ULL;
        struct {
            uint64_t rax, rcx, rdx, rsi, rdi, r8, r11, efl, tgt;
            const void *y0, *y1, *y2;
        } ctx = {
            in->rax_in, in->rcx_in, in->rdx_in, in->rsi_in,
            (uint64_t)g_mem_arena, in->r8_in, (uint64_t)g_ymm0_out,
            flags_clean, (uint64_t)start,
            in->ymm0_in, in->ymm1_in, in->ymm2_in
        };
        __asm__ volatile (
            "mov 72(%[c]), %%r9\n\t"
            "vmovdqu (%%r9), %%ymm0\n\t"
            "mov 80(%[c]), %%r9\n\t"
            "vmovdqu (%%r9), %%ymm1\n\t"
            "mov 88(%[c]), %%r9\n\t"
            "vmovdqu (%%r9), %%ymm2\n\t"
            "mov 0(%[c]),  %%rax\n\t"
            "mov 8(%[c]),  %%rcx\n\t"
            "mov 16(%[c]), %%rdx\n\t"
            "mov 24(%[c]), %%rsi\n\t"
            "mov 32(%[c]), %%rdi\n\t"
            "mov 40(%[c]), %%r8\n\t"
            "mov 48(%[c]), %%r11\n\t"
            "pushq 56(%[c])\n\t"
            "popfq\n\t"
            "mov 64(%[c]), %%r9\n\t"
            "jmp *%%r9\n\t"
            :
            : [c] "r"(&ctx)
            : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r11",
              "cc", "memory", "ymm0", "ymm1", "ymm2"
        );
    }
}

int main(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = trap_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGTRAP, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);

    uint8_t *pages = mmap(NULL, 8192, PROT_READ | PROT_WRITE | PROT_EXEC,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) return 2;
    if (mprotect(pages + 4096, 4096, PROT_NONE) != 0) return 3;
    uint8_t *page_end = pages + 4096;

    /* Epilogue bytes: `vmovdqu [r11], ymm0` (`c4 c1 7e 7f 03`) + `int3` (`cc`) = 6 bytes */
    const uint8_t epilogue[6] = {0xc4, 0xc1, 0x7e, 0x7f, 0x03, 0xcc};

    char line[4096];
    while (fgets(line, sizeof(line), stdin)) {
        /* Format: id|hexbytes|measure_len|rax|rcx|rdx|rsi|r8|efl|mem0|mem1|ymm0_hex|ymm1_hex|ymm2_hex */
        char id[128], hex[256], y0h[128], y1h[128], y2h[128];
        ExecInput in;
        memset(&in, 0, sizeof(in));
        int mlen = 0;
        if (sscanf(line, "%127[^|]|%255[^|]|%d|%lx|%lx|%lx|%lx|%lx|%lx|%lx|%lx|%127[^|]|%127[^|]|%127s",
                   id, hex, &mlen, &in.rax_in, &in.rcx_in, &in.rdx_in, &in.rsi_in,
                   &in.r8_in, &in.efl_in, &in.mem0_in, &in.mem1_in, y0h, y1h, y2h) != 14) {
            continue;
        }
        in.measure_page_len = mlen;
        uint8_t code[32];
        int clen = (int)strlen(hex) / 2;
        for (int i = 0; i < clen && i < 32; i++) {
            unsigned int b = 0;
            sscanf(hex + 2 * i, "%02x", &b);
            code[i] = (uint8_t)b;
        }
        for (int i = 0; i < 32; i++) {
            unsigned int b0 = 0, b1 = 0, b2 = 0;
            sscanf(y0h + 2 * i, "%02x", &b0);
            sscanf(y1h + 2 * i, "%02x", &b1);
            sscanf(y2h + 2 * i, "%02x", &b2);
            in.ymm0_in[i] = (uint8_t)b0;
            in.ymm1_in[i] = (uint8_t)b1;
            in.ymm2_in[i] = (uint8_t)b2;
        }

        const char *verdict = "UNKNOWN";
        int obs_len = 0;
        uint64_t obs_trap = 0;

        if (mlen) {
            /* Sweep L = 1 .. 17 from page_end - L to determine exact hardware ILD length & fault */
            for (int L = 1; L <= 17; L++) {
                uint8_t *start = page_end - L;
                memset(start, 0xcc, (size_t)L);
                int copy_n = clen < L ? clen : L;
                memcpy(start, code, (size_t)copy_n);
                if (L > clen) {
                    int rem = L - clen;
                    if (rem >= 6) {
                        memcpy(start + clen, epilogue, 6);
                    } else {
                        start[clen] = 0xcc;
                    }
                }
                g_sig = 0; g_trapno = 0;
                run_at(start, &in);
                if (g_trapno == 14 && g_rip == (uint64_t)start) {
                    /* Instruction itself truncated across page boundary */
                    continue;
                }
                if (g_trapno == 14 && g_rip == (uint64_t)page_end) {
                    /* Instruction completed cleanly and faulted fetching next byte at page_end! */
                    verdict = "OK_EXEC";
                    obs_len = L;
                    obs_trap = 0;
                    /* Re-run with room for epilogue so we also capture YMM0 + post GPRs cleanly */
                    uint8_t *buf = pages + 2048;
                    memcpy(buf, code, (size_t)clen);
                    memcpy(buf + clen, epilogue, 6);
                    run_at(buf, &in);
                    break;
                }
                if (g_trapno == 3) {
                    verdict = "OK_EXEC";
                    /* Subtract 6 if epilogue ran, else 1 for int3 */
                    int ran_epilogue = (L - clen >= 6);
                    obs_len = (int)(g_rip - (uint64_t)start) - (ran_epilogue ? 6 : 1);
                    obs_trap = 0;
                    break;
                }
                if (g_trapno == 6) {
                    verdict = "FAULT_UD";
                    obs_len = L;
                    obs_trap = 6;
                    break;
                }
                if (g_trapno == 13) {
                    verdict = "FAULT_GP0";
                    obs_len = L;
                    obs_trap = 13;
                    break;
                }
            }
        } else {
            uint8_t *buf = pages + 2048;
            memcpy(buf, code, (size_t)clen);
            memcpy(buf + clen, epilogue, 6);
            run_at(buf, &in);
            if (g_trapno == 3) {
                verdict = "OK_EXEC";
                obs_len = (int)(g_rip - (uint64_t)buf) - 6;
                obs_trap = 0;
            } else if (g_trapno == 6) {
                verdict = "FAULT_UD";
                obs_len = clen;
                obs_trap = 6;
            } else if (g_trapno == 13) {
                verdict = "FAULT_GP0";
                obs_len = clen;
                obs_trap = 13;
            }
        }

        char yout_hex[65];
        for (int i = 0; i < 32; i++) sprintf(yout_hex + 2 * i, "%02x", g_ymm0_out[i]);
        yout_hex[64] = '\0';

        printf("%s|%s|%d|%lu|%lx|%lx|%lx|%lx|%lx|%lx|%s\n",
               id, verdict, obs_len, (unsigned long)obs_trap,
               (unsigned long)g_rax, (unsigned long)g_rcx, (unsigned long)g_rdx,
               (unsigned long)(g_efl & 0x8D5ULL),
               (unsigned long)g_mem_arena[0], (unsigned long)g_mem_arena[1],
               yout_hex);
    }
    return 0;
}
"""


def u256_to_le_hex(val: int) -> str:
    return val.to_bytes(32, "little").hex()


def pack_lanes(vals: list[int], bits: int) -> str:
    acc = 0
    mask = (1 << bits) - 1
    for i, v in enumerate(vals):
        acc |= (v & mask) << (i * bits)
    return u256_to_le_hex(acc)


def build_224_vectors() -> list[dict]:
    vecs: list[dict] = []
    z256 = "00" * 32
    dirty_hi = ("00" * 16) + ("ff" * 16)  # low 128 = 0, high 128 = all 1s

    def add(
        vid: str,
        cat: str,
        hex_b: str,
        mlen: int = 1,
        rax: int = 0x1111111122222222,
        rcx: int = 0x3,
        rdx: int = 0x7777777788888888,
        rsi: int = 0x5,
        r8: int = 0x99999999AAAAAAAA,
        efl: int = 0,
        mem0: int = 0x10,
        mem1: int = 0x20,
        y0: str = z256,
        y1: str = z256,
        y2: str = z256,
        note: str = "",
    ) -> None:
        vecs.append({
            "id": vid,
            "category": cat,
            "hex": hex_b.replace(" ", "").lower(),
            "measure_len": mlen,
            "rax": rax, "rcx": rcx, "rdx": rdx, "rsi": rsi, "r8": r8,
            "efl": efl, "mem0": mem0, "mem1": mem1,
            "y0": y0, "y1": y1, "y2": y2, "note": note,
        })

    # === Category 1: Length-limit & Prefix Precedence (32 vectors) ===
    for k in range(15):
        add(f"len_nop_{k+1:02d}b", "length_and_prefixes", ("66" * k) + "90", mlen=1, note=f"{k}x0x66 + nop ({k+1}B)")
    add("len_exceed_16b_66_nop", "length_and_prefixes", ("66" * 15) + "90", mlen=1, note="15x0x66 + nop (16B -> #GP(0))")
    add("len_exceed_16b_2e_nop", "length_and_prefixes", ("2e" * 15) + "90", mlen=1, note="15x0x2E + nop (16B -> #GP(0))")
    add("len_exceed_16b_f3_nop", "length_and_prefixes", ("f3" * 15) + "90", mlen=1, note="15x0xF3 + nop (16B -> #GP(0))")
    add("len_exceed_16b_66_add64", "length_and_prefixes", ("66" * 13) + "4801f0", mlen=1, note="13x0x66 + add rax,rsi (16B -> #GP(0))")
    add("pfx_rex_nullified_41_66_90", "length_and_prefixes", "416690", rax=0x1111111122222222, r8=0x7777777788888888, note="REX.B before 0x66 nullified -> nop")
    add("pfx_66_41_90_xchg16", "length_and_prefixes", "664190", rax=0x1111111122222222, r8=0x7777777788888888, note="0x66 before REX.B -> xchg ax, r8w")
    add("pfx_41_90_xchg32", "length_and_prefixes", "4190", rax=0x1111111122222222, r8=0x7777777788888888, note="REX.B + 0x90 -> xchg eax, r8d")
    add("pfx_49_90_xchg64", "length_and_prefixes", "4990", rax=0x1111111122222222, r8=0x7777777788888888, note="REX.WB + 0x90 -> xchg rax, r8")
    add("pfx_rex_last_wins_41_40_90", "length_and_prefixes", "414090", rax=0x1111111122222222, r8=0x7777777788888888, note="consecutive REX 41 40 -> 40 wins (nop)")
    add("pfx_rex_last_wins_40_41_90", "length_and_prefixes", "404190", rax=0x1111111122222222, r8=0x7777777788888888, note="consecutive REX 40 41 -> 41 wins (xchg32)")
    add("pfx_rex_nullified_48_67_01_f0", "length_and_prefixes", "486701f0", rax=0x300000002, rsi=3, note="REX.W before 0x67 nullified -> 32b add")
    add("pfx_67_48_01_f0_add64", "length_and_prefixes", "674801f0", rax=0x300000002, rsi=3, note="0x67 before REX.W -> 64b add")
    add("cet_endbr64", "length_and_prefixes", "f30f1efa", note="endbr64 (4B)")
    add("hint_nop_0f1efa", "length_and_prefixes", "0f1efa", note="hintable 3B nop (llvm-mc misparses as cli)")
    add("gcc_11b_align_nop", "length_and_prefixes", "66662e0f1f840000000000", note="GCC 11B multi-66 CS SIB disp32 nop")
    add("ring3_cli_gp0", "length_and_prefixes", "fa", note="Ring-3 cli -> #GP(0)")
    add("explicit_ud2", "length_and_prefixes", "0f0b", note="ud2 -> #UD")

    # === Category 2: LOCK (#UD) & VEX Legality Matrix (32 vectors) ===
    add("lock_ok_add_mem_reg", "lock_and_vex_legality", "f0480137", rsi=7, mem0=35, note="lock add [rdi], rsi")
    add("lock_ok_add_mem_imm8", "lock_and_vex_legality", "f048830705", mem0=37, note="lock add qword [rdi], 5")
    add("lock_ok_sub_mem_reg", "lock_and_vex_legality", "f0482937", rsi=12, mem0=50, note="lock sub [rdi], rsi")
    add("lock_ok_xor_mem_reg", "lock_and_vex_legality", "f0483137", rsi=0xFF, mem0=0xAA, note="lock xor [rdi], rsi")
    add("lock_ok_and_mem_reg", "lock_and_vex_legality", "f0482137", rsi=0x0F, mem0=0xAB, note="lock and [rdi], rsi")
    add("lock_ok_or_mem_reg", "lock_and_vex_legality", "f0480937", rsi=0xF0, mem0=0x0A, note="lock or [rdi], rsi")
    add("lock_ok_xadd_mem_reg", "lock_and_vex_legality", "f0480fc137", rsi=9, mem0=33, note="lock xadd [rdi], rsi")
    add("lock_ok_cmpxchg_hit", "lock_and_vex_legality", "f0480fb137", rax=42, rsi=99, mem0=42, note="lock cmpxchg [rdi], rsi (hit)")
    add("lock_ok_cmpxchg_miss", "lock_and_vex_legality", "f0480fb137", rax=41, rsi=99, mem0=42, note="lock cmpxchg [rdi], rsi (miss)")
    add("lock_ok_inc_mem", "lock_and_vex_legality", "f048ff07", mem0=99, note="lock inc qword [rdi]")

    add("lock_ud_nop", "lock_and_vex_legality", "f090", note="lock nop -> #UD")
    add("lock_ud_add_reg", "lock_and_vex_legality", "f04801f0", note="lock add rax, rsi -> #UD")
    add("lock_ud_mov_load", "lock_and_vex_legality", "f0488b07", note="lock mov rax, [rdi] -> #UD")
    add("lock_ud_mov_store", "lock_and_vex_legality", "f0488907", note="lock mov [rdi], rax -> #UD")
    add("lock_ud_lea", "lock_and_vex_legality", "f0488d07", note="lock lea rax, [rdi] -> #UD")
    add("lock_ud_cmp_mem", "lock_and_vex_legality", "f0483937", note="lock cmp [rdi], rsi -> #UD")
    add("lock_ud_test_mem", "lock_and_vex_legality", "f0488537", note="lock test [rdi], rsi -> #UD")
    add("lock_ud_xchg_reg", "lock_and_vex_legality", "f04887f0", note="lock xchg rax, rsi -> #UD")
    add("lock_ud_imul_mem", "lock_and_vex_legality", "f0480faf07", note="lock imul rax, [rdi] -> #UD")
    add("lock_ud_vzeroupper", "lock_and_vex_legality", "f0c5f877", note="lock + VEX vzeroupper -> #UD")

    add("vex_ok_cs_vzeroupper", "lock_and_vex_legality", "2ec5f877", y0=dirty_hi, note="CS + VEX vzeroupper -> legal")
    add("vex_ok_67_vzeroupper", "lock_and_vex_legality", "67c5f877", y0=dirty_hi, note="0x67 + VEX vzeroupper -> legal")
    add("vex_ud_66_vzeroupper", "lock_and_vex_legality", "66c5f877", note="0x66 + VEX -> #UD")
    add("vex_ud_f2_vzeroupper", "lock_and_vex_legality", "f2c5f877", note="0xF2 + VEX -> #UD")
    add("vex_ud_f3_vzeroupper", "lock_and_vex_legality", "f3c5f877", note="0xF3 + VEX -> #UD")
    add("vex_ud_rex_vzeroupper", "lock_and_vex_legality", "48c5f877", note="REX + VEX -> #UD")
    add("vex_ud_vzeroupper_vvvv_nonzero", "lock_and_vex_legality", "c5f077", note="vzeroupper with vvvv!=0 -> #UD")
    add("vex_ud_bzhi_L1", "lock_and_vex_legality", "c4e2ecf5c6", note="bzhi with L=1 (256b) -> #UD")
    add("vex_ud_vpmovmskb_vvvv_nonzero", "lock_and_vex_legality", "c5f5d7c0", note="vpmovmskb with vvvv!=0 -> #UD")
    add("vex_ud_vmovdqu_vvvv_nonzero", "lock_and_vex_legality", "c5f66fc0", note="vmovdqu with vvvv!=0 -> #UD")
    add("vex_ud_vpermd_L0", "lock_and_vex_legality", "c4e27936c1", note="vpermd with L=0 (128b) -> #UD")
    add("vex_ud_mulx_L1", "lock_and_vex_legality", "c4e2f7f6c1", note="mulx with L=1 (256b) -> #UD")

    # === Category 3: Scalar GP ALU, Flags, Shifts, Multiply, BMI1/2, ADX, CMOVcc, Addressing (96 vectors) ===
    # Arithmetic & flags (24)
    add("alu_add64_basic", "scalar_gp_bmi_adx", "4801f0", rax=10, rsi=32)
    add("alu_add64_cf", "scalar_gp_bmi_adx", "4801f0", rax=0xFFFFFFFFFFFFFFFF, rsi=1)
    add("alu_add64_of_pos", "scalar_gp_bmi_adx", "4801f0", rax=0x7FFFFFFFFFFFFFFF, rsi=1)
    add("alu_add64_of_neg", "scalar_gp_bmi_adx", "4801f0", rax=0x8000000000000000, rsi=0x8000000000000000)
    add("alu_add32_zext", "scalar_gp_bmi_adx", "01f0", rax=0xFFFFFFFFFFFFFFFF, rsi=2)
    add("alu_adc64_cf0", "scalar_gp_bmi_adx", "4811f0", rax=10, rsi=20, efl=0)
    add("alu_adc64_cf1", "scalar_gp_bmi_adx", "4811f0", rax=0xFFFFFFFFFFFFFFFF, rsi=0, efl=1)
    add("alu_sub64_basic", "scalar_gp_bmi_adx", "4829f0", rax=50, rsi=8)
    add("alu_sub64_borrow", "scalar_gp_bmi_adx", "4829f0", rax=0, rsi=1)
    add("alu_sub64_of", "scalar_gp_bmi_adx", "4829f0", rax=0x8000000000000000, rsi=1)
    add("alu_sbb64_cf1", "scalar_gp_bmi_adx", "4819f0", rax=10, rsi=10, efl=1)
    add("alu_and64", "scalar_gp_bmi_adx", "4821f0", rax=0xF0F0F0F00F0F0F0F, rsi=0xFF00FF00FF00FF00, efl=0x801)
    add("alu_or64", "scalar_gp_bmi_adx", "4809f0", rax=0x8000000000000000, rsi=3, efl=0x801)
    add("alu_xor64_zero", "scalar_gp_bmi_adx", "4831c0", rax=0xDEADBEEFCAFEBABE, efl=0x801)
    add("alu_cmp64_lt", "scalar_gp_bmi_adx", "4839f0", rax=5, rsi=10)
    add("alu_cmp64_eq", "scalar_gp_bmi_adx", "4839f0", rax=10, rsi=10)
    add("alu_test64_zero", "scalar_gp_bmi_adx", "4885f0", rax=0xF0F0, rsi=0x0F0F, efl=0x801)
    add("alu_inc64_preserves_cf1", "scalar_gp_bmi_adx", "48ffc0", rax=0x7FFFFFFFFFFFFFFF, efl=1)
    add("alu_dec64_preserves_cf1", "scalar_gp_bmi_adx", "48ffc8", rax=1, efl=1)
    add("alu_neg64_zero", "scalar_gp_bmi_adx", "48f7d8", rax=0)
    add("alu_neg64_min", "scalar_gp_bmi_adx", "48f7d8", rax=0x8000000000000000)
    add("alu_not64_preserves_flags", "scalar_gp_bmi_adx", "48f7d0", rax=0, efl=0x8D5)
    add("alu_bswap64", "scalar_gp_bmi_adx", "480fc8", rax=0x0102030405060708)
    add("alu_bswap32_zext", "scalar_gp_bmi_adx", "0fc8", rax=0xFFFFFFFF01020304)

    # Shifts, rotates, multiplies (20)
    add("shl64_imm0_noop_flags", "scalar_gp_bmi_adx", "48c1e000", rax=0x1234, efl=0x8D5)
    add("shl64_imm1_of1", "scalar_gp_bmi_adx", "48d1e0", rax=0x4000000000000001)
    add("shl64_imm1_of0", "scalar_gp_bmi_adx", "48d1e0", rax=0xC000000000000001)
    add("shl64_cl_mod64", "scalar_gp_bmi_adx", "48d3e0", rax=5, rcx=65)
    add("shr64_imm1_of_msb", "scalar_gp_bmi_adx", "48d1e8", rax=0x8000000000000002)
    add("shr64_imm4", "scalar_gp_bmi_adx", "48c1e804", rax=0xF0)
    add("sar64_imm1_neg", "scalar_gp_bmi_adx", "48d1f8", rax=0x8000000000000003)
    add("sar64_imm8_neg", "scalar_gp_bmi_adx", "48c1f808", rax=0xFFFFFFFFFFFFFF00)
    add("rol64_imm1", "scalar_gp_bmi_adx", "48d1c0", rax=0x8000000000000001)
    add("ror64_imm1", "scalar_gp_bmi_adx", "48d1c8", rax=0x8000000000000001)
    add("imul64_zero_undef_zf", "scalar_gp_bmi_adx", "480fafc6", rax=0, rsi=7)
    add("imul64_no_ovf", "scalar_gp_bmi_adx", "480fafc6", rax=6, rsi=7)
    add("imul64_ovf", "scalar_gp_bmi_adx", "480fafc6", rax=0x4000000000000000, rsi=4)
    add("imul64_imm8", "scalar_gp_bmi_adx", "486bc6fd", rsi=10, note="imul rax, rsi, -3")
    add("mul64_no_ovf", "scalar_gp_bmi_adx", "48f7e6", rax=100, rsi=200)
    add("mul64_ovf", "scalar_gp_bmi_adx", "48f7e6", rax=0x8000000000000000, rsi=4)
    add("mulx64_preserves_flags", "scalar_gp_bmi_adx", "c4e2f3f6c6", rdx=0x8000000000000003, rsi=4, efl=0x8D5, note="mulx rax, rcx, rsi")
    add("mulx64_alias_dst", "scalar_gp_bmi_adx", "c4e2fbf6c6", rdx=0x8000000000000003, rsi=4, note="mulx rax, rax, rsi -> high half wins")
    add("adcx64_preserves_of", "scalar_gp_bmi_adx", "66480f38f6c6", rax=0xFFFFFFFFFFFFFFFF, rsi=1, efl=0x801, note="adcx rax, rsi (CF=1, OF=1 preserved)")
    add("adox64_preserves_cf", "scalar_gp_bmi_adx", "f3480f38f6c6", rax=0xFFFFFFFFFFFFFFFF, rsi=1, efl=0x801, note="adox rax, rsi (OF=1, CF=1 preserved)")

    # BMI1/BMI2 & bit-scan (18)
    add("bsf64_nonzero", "scalar_gp_bmi_adx", "480fbcc6", rax=0x999, rsi=0x8000)
    add("bsf64_zero", "scalar_gp_bmi_adx", "480fbcc6", rax=0x123456789ABCDEF0, rsi=0)
    add("bsr64_nonzero", "scalar_gp_bmi_adx", "480fbdc6", rax=0, rsi=0x8010)
    add("tzcnt64_nonzero", "scalar_gp_bmi_adx", "f3480fbcc6", rax=0, rsi=0x8000)
    add("tzcnt64_zero", "scalar_gp_bmi_adx", "f3480fbcc6", rax=0, rsi=0)
    add("tzcnt32_zero_zext", "scalar_gp_bmi_adx", "f30fbcc6", rax=0xFFFFFFFF00000000, rsi=0)
    add("lzcnt64_nonzero", "scalar_gp_bmi_adx", "f3480fbdc6", rax=0, rsi=0x00FF000000000000)
    add("lzcnt64_zero", "scalar_gp_bmi_adx", "f3480fbdc6", rax=0, rsi=0)
    add("popcnt64_val", "scalar_gp_bmi_adx", "f3480fb8c6", rax=0, rsi=0x800000000000000F, efl=0x8D5)
    add("popcnt64_zero", "scalar_gp_bmi_adx", "f3480fb8c6", rax=99, rsi=0, efl=0x8D5)
    add("shrx64_preserves_flags", "scalar_gp_bmi_adx", "c4e2ebf7c6", rsi=0xF00, rdx=4, efl=0x8D5, note="shrx rax, rsi, rdx")
    add("shlx64_mod64", "scalar_gp_bmi_adx", "c4e2e9f7c6", rsi=3, rdx=66, efl=0x8D5, note="shlx rax, rsi, rdx")
    add("sarx64_neg", "scalar_gp_bmi_adx", "c4e2eaf7c6", rsi=0xFFFFFFFFFFFFFF00, rdx=4, efl=0x8D5, note="sarx rax, rsi, rdx")
    add("bzhi64_idx12", "scalar_gp_bmi_adx", "c4e2e8f5c6", rsi=0xFFFFFFFFFFFFFFFF, rdx=12, note="bzhi rax, rsi, rdx")
    add("bzhi64_idx0", "scalar_gp_bmi_adx", "c4e2e8f5c6", rsi=0xFFFFFFFFFFFFFFFF, rdx=0, note="bzhi idx=0 -> 0, ZF=1, CF=0")
    add("bzhi64_idx64_cf1", "scalar_gp_bmi_adx", "c4e2e8f5c6", rsi=0x123456789ABCDEF0, rdx=64, note="bzhi idx=64 -> unchanged, CF=1")
    add("bzhi64_idx200_cf1", "scalar_gp_bmi_adx", "c4e2e8f5c6", rsi=0, rdx=200, note="bzhi idx=200 on 0 -> 0, ZF=1, CF=1")
    add("pext64_mask", "scalar_gp_bmi_adx", "c4e2f3f5c2", rcx=0xABCD12345678EF90, rdx=0x00FF00FF00FF00FF, note="pext rax, rcx, rdx")

    # CMOVcc (all 16 condition codes) + SETcc + MOV/LEA/SIB/disp (34)
    cmov_cases = [
        ("o", 0x40, 0x800), ("no", 0x41, 0x000), ("b", 0x42, 0x001), ("ae", 0x43, 0x000),
        ("e", 0x44, 0x040), ("ne", 0x45, 0x000), ("be", 0x46, 0x040), ("a", 0x47, 0x000),
        ("s", 0x48, 0x080), ("ns", 0x49, 0x000), ("p", 0x4A, 0x004), ("np", 0x4B, 0x000),
        ("l", 0x4C, 0x080), ("ge", 0x4D, 0x880), ("le", 0x4E, 0x040), ("g", 0x4F, 0x880),
    ]
    for cname, opc, fl in cmov_cases:
        add(f"cmov64_{cname}_taken", "scalar_gp_bmi_adx", f"480f{opc:02x}c6", rax=11, rsi=99, efl=fl)
    add("cmov32_false_still_zexts", "scalar_gp_bmi_adx", "0f44c6", rax=0xFFFFFFFF00000011, rsi=99, efl=0,
        note="32b cmove false STILL zero-extends upper 32 bits of rax!")
    add("sete_true", "scalar_gp_bmi_adx", "0f94c0", rax=0x12345600, efl=0x040)
    add("sete_false", "scalar_gp_bmi_adx", "0f94c0", rax=0x123456FF, efl=0x000)
    add("setb_true", "scalar_gp_bmi_adx", "0f92c0", rax=0, efl=0x001)
    add("mov64_rr_dir0", "scalar_gp_bmi_adx", "4889f0", rax=0, rsi=0xCAFEBABE12345678)
    add("mov64_rr_dir1", "scalar_gp_bmi_adx", "488bc6", rax=0, rsi=0xCAFEBABE12345678)
    add("mov32_imm_zext", "scalar_gp_bmi_adx", "b878563412", rax=0xFFFFFFFFFFFFFFFF)
    add("movabs64_imm", "scalar_gp_bmi_adx", "48b8efcdab8967452301", rax=0)
    add("mov64_load_base", "scalar_gp_bmi_adx", "488b07", mem0=0xDEADBEEF11223344)
    add("mov64_load_disp8", "scalar_gp_bmi_adx", "488b4708", mem1=0x8877665544332211)
    add("mov64_store_disp8", "scalar_gp_bmi_adx", "48897708", rsi=0xA1B2C3D4E5F60718, mem1=0)
    add("movsxd_neg", "scalar_gp_bmi_adx", "486307", mem0=0x00000000FFFFFF80)
    add("movzx_byte", "scalar_gp_bmi_adx", "480fb607", rax=0xFFFFFFFFFFFFFFFF, mem0=0xFFAB)
    add("movzx_word", "scalar_gp_bmi_adx", "480fb707", rax=0xFFFFFFFFFFFFFFFF, mem0=0xFFFF1234)
    add("lea64_sib_scale8_disp8", "scalar_gp_bmi_adx", "488d44ce10", rcx=100, rsi=5, note="lea rax, [rcx + rsi*8 + 16]")
    add("lea32_zext", "scalar_gp_bmi_adx", "8d4605", rax=0xFFFFFFFF00000000, rsi=0xFFFFFFFE, note="32b operand-size lea eax, [rsi+5] zero-extends!")
    add("xchg64_rax_rsi", "scalar_gp_bmi_adx", "4896", rax=111, rsi=222)
    add("push_pop_roundtrip", "scalar_gp_bmi_adx", "5658", rax=0, rsi=0x76543210FEDCBA98, mlen=0, note="push rsi; pop rax (2 insns)")

    # === Category 4: VEX 128/256 & EVEX SIMD + AES + PCLMUL (64 vectors) ===
    v_seq_a = pack_lanes([i + 1 for i in range(32)], 8)
    v_seq_b = pack_lanes([(i * 3) & 0xFF for i in range(32)], 8)
    v_ones_b = "ff" * 32

    add("simd_vmovdqu128_zext_upper", "simd_vex_evex", "c5f96fc1", y0=dirty_hi, y1="aa" * 32,
        note="128b vmovdqa xmm0, xmm1 zeroes upper 128 bits of ymm0!")
    add("simd_vmovdqu256_reg", "simd_vex_evex", "c5fe6fc1", y0=z256, y1=v_seq_a)
    add("simd_vmovdqu128_load", "simd_vex_evex", "c5fa6f07", mem0=0x0807060504030201, mem1=0x100F0E0D0C0B0A09, y0=dirty_hi)
    add("simd_vmovdqa128_load", "simd_vex_evex", "c5f96f07", mem0=0x1122334455667788, mem1=0x99AABBCCDDEEFF00, y0=dirty_hi)
    add("simd_vmovq_xmm_gpr", "simd_vex_evex", "c4e1f96ec6", rsi=0xCAFEBABEDEADBEEF, y0=dirty_hi)
    add("simd_vmovd_xmm_gpr", "simd_vex_evex", "c5f96ec6", rsi=0xCAFEBABEDEADBEEF, y0=dirty_hi)

    add("simd_vpaddb_128", "simd_vex_evex", "c5f1fcc1", y0=dirty_hi, y1=v_seq_a)
    add("simd_vpaddb_256", "simd_vex_evex", "c5fdfcc1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vpaddw_256", "simd_vex_evex", "c5fdfdc1", y0=pack_lanes([0x7FFF, 1] * 8, 16), y1=pack_lanes([1, 0xFFFF] * 8, 16))
    add("simd_vpaddd_256", "simd_vex_evex", "c5fdfec1", y0=pack_lanes([0xFFFFFFFF, 10] * 4, 32), y1=pack_lanes([2, 20] * 4, 32))
    add("simd_vpaddq_256", "simd_vex_evex", "c5fdd4c1", y0=pack_lanes([0xFFFFFFFFFFFFFFFF, 5, 6, 7], 64), y1=pack_lanes([1, 10, 20, 30], 64))
    add("simd_vpsubb_256", "simd_vex_evex", "c5fdf8c1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vpsubw_256", "simd_vex_evex", "c5fdf9c1", y0=pack_lanes([10, 0] * 8, 16), y1=pack_lanes([3, 1] * 8, 16))
    add("simd_vpsubd_256", "simd_vex_evex", "c5fdfac1", y0=pack_lanes([100, 0] * 4, 32), y1=pack_lanes([30, 1] * 4, 32))
    add("simd_vpsubq_256", "simd_vex_evex", "c5fdfbc1", y0=pack_lanes([0, 50, 100, 200], 64), y1=pack_lanes([1, 25, 100, 50], 64))

    add("simd_vpaddsw_pos_sat", "simd_vex_evex", "c5fdedc1",
        y0=pack_lanes([30000, -30000, 100, -100] * 4, 16),
        y1=pack_lanes([10000, -10000, 50, -50] * 4, 16), note="vpaddsw +32767 and -32768 saturation")
    add("simd_vpaddsw_128", "simd_vex_evex", "c5f9edc1",
        y0=pack_lanes([32767, -32768] * 8, 16), y1=pack_lanes([1, -1] * 8, 16))
    add("simd_vpsubusb_256", "simd_vex_evex", "c5fdd8c1",
        y0=pack_lanes([10, 200, 0, 255] * 8, 8), y1=pack_lanes([20, 50, 1, 255] * 8, 8))
    add("simd_vpsubusb_128", "simd_vex_evex", "c5f9d8c1",
        y0=pack_lanes([5, 100] * 16, 8), y1=pack_lanes([10, 30] * 16, 8))

    add("simd_vpand_256", "simd_vex_evex", "c5fddbc1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vandps_256", "simd_vex_evex", "c5fc54c1", y0=v_seq_a, y1=v_seq_b, note="rustc -O3 emits vandps for simd_and!")
    add("simd_vpor_256", "simd_vex_evex", "c5fdebc1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vorps_256", "simd_vex_evex", "c5fc56c1", y0=v_seq_a, y1=v_seq_b, note="rustc -O3 emits vorps for simd_or!")
    add("simd_vpxor_256", "simd_vex_evex", "c5fdefc1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vxorps_256", "simd_vex_evex", "c5fc57c1", y0=v_seq_a, y1=v_seq_b, note="rustc -O3 emits vxorps for simd_xor!")
    add("simd_vxorps_128_zero256", "simd_vex_evex", "c5f857c0", y0=v_ones_b, note="vxorps xmm0,xmm0,xmm0 zeroes all 256 bits!")
    add("simd_vpandn_256", "simd_vex_evex", "c5fddfc1", y0=v_seq_a, y1=v_ones_b)

    add("simd_vpcmpeqb_256", "simd_vex_evex", "c5fd74c1", y0=v_seq_a, y1=v_seq_b)
    add("simd_vpcmpeqb_128", "simd_vex_evex", "c5f974c1", y0=v_seq_a, y1=v_seq_a)
    add("simd_vpcmpeqw_256", "simd_vex_evex", "c5fd75c1", y0=pack_lanes([1, 2, 3, 4] * 4, 16), y1=pack_lanes([1, 9, 3, 8] * 4, 16))
    add("simd_vpcmpgtb_256", "simd_vex_evex", "c5fd64c1", y0=pack_lanes([0x7F, 0x80, 0, 1] * 8, 8), y1=pack_lanes([0, 0, 0xFF, 1] * 8, 8))
    add("simd_vpcmpgtb_128", "simd_vex_evex", "c5f964c1", y0=pack_lanes([5, -5] * 16, 8), y1=pack_lanes([-1, 0] * 16, 8))
    add("simd_vpcmpgtd_256", "simd_vex_evex", "c5fd66c1", y0=pack_lanes([10, -10, 0x7FFFFFFF, -2147483648] * 2, 32), y1=z256)

    add("simd_vpmovmskb_128_L0", "simd_vex_evex", "c5f9d7c0", rax=0xFFFFFFFF00000000,
        y0=pack_lanes([0x80 if i % 2 == 0 else 0x7F for i in range(32)], 8),
        note="128b VPMOVMSKB L=0 (false-rejected by raw s2n-bignum decode.ml:1334!)")
    add("simd_vpmovmskb_256_L1", "simd_vex_evex", "c5fdd7c0", rax=0xFFFFFFFF00000000,
        y0=pack_lanes([0x80 if (i % 3 == 0) else 0x7F for i in range(32)], 8))

    add("simd_vpshufb_256_bit7_zero", "simd_vex_evex", "c4e27d00c1",
        y0=v_seq_a, y1=pack_lanes([0x80 if i % 4 == 0 else (15 - (i % 16)) | 0x30 for i in range(32)], 8))
    add("simd_vpshufb_128", "simd_vex_evex", "c4e27900c1",
        y0=v_seq_a, y1=pack_lanes([15 - (i % 16) for i in range(32)], 8))
    add("simd_vpshufd_256_4e", "simd_vex_evex", "c5fd70c04e",
        y0=pack_lanes([10, 20, 30, 40, 50, 60, 70, 80], 32))

    add("simd_vpmaddubsw_sat", "simd_vex_evex", "c4e27d04c1",
        y0=pack_lanes([255, 255, 255, 255, 10, 20, 0, 100] * 4, 8),
        y1=pack_lanes([-128, -128, 127, 127, -3, 4, 50, -1] * 4, 8))
    add("simd_vpmaddwd_wrap", "simd_vex_evex", "c5fdf5c1",
        y0=pack_lanes([-32768, -32768, 300, -200] * 4, 16),
        y1=pack_lanes([-32768, -32768, 5, 7] * 4, 16))
    add("simd_vpsadbw_256", "simd_vex_evex", "c5fdf6c1", y0=v_seq_a, y1=v_seq_b)

    add("simd_vpslld_imm7", "simd_vex_evex", "c5fd72f007", y0=pack_lanes([0x12345678] * 8, 32))
    add("simd_vpslld_imm32_zero", "simd_vex_evex", "c5fd72f020", y0=v_ones_b, note="imm8=32 saturates to 0")
    add("simd_vpsrld_imm7", "simd_vex_evex", "c5fd72d007", y0=pack_lanes([0x800000FF] * 8, 32))
    add("simd_vpsrld_imm40_zero", "simd_vex_evex", "c5fd72d028", y0=v_ones_b, note="imm8=40 saturates to 0")
    add("simd_vpsrad_imm7", "simd_vex_evex", "c5fd72e007", y0=pack_lanes([0x80000000, 0x7FFFFFFF] * 4, 32))
    add("simd_vpsrad_imm40_clamp", "simd_vex_evex", "c5fd72e028", y0=pack_lanes([0x80000000, 0x7FFFFFFF] * 4, 32))
    add("simd_vpslld_xmm_hi32_count", "simd_vex_evex", "c5fdf2c1",
        y0=v_ones_b, y1=pack_lanes([1, 1, 0, 0, 0, 0, 0, 0], 32),
        note="64-bit xmm count = 0x1_0000_0001 >= 32 -> zeroes all lanes!")
    add("simd_vpsllvd_var", "simd_vex_evex", "c4e27d47c1",
        y0=pack_lanes([0x80000001, 0x7FFFFFFF, 0x12345679, 1, 0xFFFFFFFF, 42, 0, 0xDEADBEEF], 32),
        y1=pack_lanes([0, 1, 31, 32, 33, 64, 255, 7], 32))
    add("simd_vpsrlvd_var", "simd_vex_evex", "c4e27d45c1",
        y0=pack_lanes([0x80000001, 0xFFFFFFFF, 0x80000000, 0xFFFFFFFF, 1, 2, 3, 0xFF00], 32),
        y1=pack_lanes([0, 1, 31, 32, 0, 1, 2, 4], 32))

    add("simd_vpermd_256", "simd_vex_evex", "c4e27536c0",
        y0=pack_lanes([10, 20, 30, 40, 50, 60, 70, 80], 32),
        y1=pack_lanes([7, 6, 5, 4, 3, 2, 1, 0], 32))
    add("simd_vpermps_256", "simd_vex_evex", "c4e27516c0",
        y0=pack_lanes([10, 20, 30, 40, 50, 60, 70, 80], 32),
        y1=pack_lanes([7, 6, 5, 4, 3, 2, 1, 0], 32))
    add("simd_vpermq_256", "simd_vex_evex", "c4e3fd00c01b",
        y0=pack_lanes([111, 222, 333, 444], 64))
    add("simd_vperm2i128_21", "simd_vex_evex", "c4e37d46c121",
        y0=pack_lanes([11, 22], 128), y1=pack_lanes([33, 44], 128))
    add("simd_vperm2f128_21", "simd_vex_evex", "c4e37d06c121",
        y0=pack_lanes([11, 22], 128), y1=pack_lanes([33, 44], 128))
    add("simd_vperm2f128_81_zero", "simd_vex_evex", "c4e37d06c181",
        y0=pack_lanes([11, 22], 128), y1=pack_lanes([33, 44], 128))
    add("simd_vextractf128_hi", "simd_vex_evex", "c4e37d19c001",
        y0=pack_lanes([0x1111, 0x2222], 128))
    add("simd_vpextrq_lane1", "simd_vex_evex", "c4e3f916c001", rax=0,
        y0=pack_lanes([0x1111111122222222, 0xCAFEBABEDEADBEEF, 0, 0], 64))

    add("simd_vpclmulqdq_0x10", "simd_vex_evex", "c4e37944c110",
        y0=pack_lanes([0x8000000000000001, 0xDEADBEEFCAFEBABE, 0, 0], 64),
        y1=pack_lanes([0x1111222233334444, 0x8000000000000001, 0, 0], 64))
    add("simd_vaesenc_fips197", "simd_vex_evex", "c4e279dcc1",
        y0=u256_to_le_hex(0x0848f8e92a8dc69a2be2f4a0bee33d19),
        y1=u256_to_le_hex(0x05766c2a3939a323b12c548817fefaa0))
    add("simd_vptest_zf1", "simd_vex_evex", "c4e27d17c1", efl=0x8D5,
        y0=pack_lanes([0xF0F0F0F0] * 8, 32), y1=pack_lanes([0x0F0F0F0F] * 8, 32))
    add("simd_evex_vpternlogd_96", "simd_vex_evex", "62f3752825c296",
        y0=pack_lanes([0x12345678] * 8, 32), y1=pack_lanes([0x0F0F0F0F] * 8, 32), y2=pack_lanes([0xA5A55A5A] * 8, 32))
    add("simd_evex_vprolvd", "simd_vex_evex", "62f27d2815c1",
        y0=pack_lanes([0x80000001] * 8, 32), y1=pack_lanes([1, 7, 31, 32, 33, 0, 16, 63], 32))
    add("simd_vzeroupper", "simd_vex_evex", "c5f877",
        y0=pack_lanes([0x112233445566778899AABBCCDDEEFF00, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF], 128))

    assert len(vecs) == 224, f"Expected 224 vectors, got {len(vecs)}"
    return vecs


def check_disassemblers_on_faults(fault_vecs: list[dict], td_path: Path) -> dict:
    llvm_false_accepts = 0
    objdump_false_accepts = 0
    details = []
    for v in fault_vecs:
        if v["id"] == "explicit_ud2" or v["id"] == "ring3_cli_gp0":
            # ud2 and cli are genuine Ring-0/explicit trap mnemonics, not decode-legality traps
            continue
        raw = bytes.fromhex(v["hex"])
        mc_in = " ".join(f"0x{b:02x}" for b in raw)
        p_mc = subprocess.run(
            ["llvm-mc", "--disassemble", "--triple=x86_64-unknown-linux-gnu"],
            input=mc_in, capture_output=True, text=True,
        )
        mc_accepted = (p_mc.returncode == 0 and "warning: invalid instruction" not in p_mc.stderr.lower())
        if mc_accepted:
            llvm_false_accepts += 1

        bin_p = td_path / f"f_{v['id']}.bin"
        bin_p.write_bytes(raw)
        p_od = subprocess.run(
            ["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel", str(bin_p)],
            capture_output=True, text=True,
        )
        od_bad = ("(bad)" in p_od.stdout or "internal disassembler error" in p_od.stderr)
        if p_od.returncode == 0 and not od_bad:
            objdump_false_accepts += 1

        details.append({
            "id": v["id"],
            "hex": v["hex"],
            "silicon_verdict": v["silicon_verdict"],
            "llvm_mc_false_accept": mc_accepted,
            "llvm_mc_stdout": p_mc.stdout.strip().replace("\n", " | "),
            "objdump_false_accept": (p_od.returncode == 0 and not od_bad),
        })
    return {
        "decode_legality_trap_specimens": len(details),
        "llvm_mc_false_accepts": llvm_false_accepts,
        "objdump_false_accepts": objdump_false_accepts,
        "details": details,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-json", required=True, type=Path)
    args = ap.parse_args()

    vecs = build_224_vectors()
    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        c_file = td_path / "harness.c"
        bin_file = td_path / "harness"
        c_file.write_text(C_SILICON_HARNESS)
        subprocess.run(["gcc", "-O2", "-mavx2", str(c_file), "-o", str(bin_file)], check=True)

        stdin_lines = []
        for v in vecs:
            stdin_lines.append(
                f"{v['id']}|{v['hex']}|{v['measure_len']}|"
                f"{v['rax']:x}|{v['rcx']:x}|{v['rdx']:x}|{v['rsi']:x}|{v['r8']:x}|"
                f"{v['efl']:x}|{v['mem0']:x}|{v['mem1']:x}|"
                f"{v['y0']}|{v['y1']}|{v['y2']}"
            )
        proc = subprocess.run(
            [str(bin_file)],
            input="\n".join(stdin_lines) + "\n",
            capture_output=True,
            text=True,
            check=True,
        )
        by_id = {v["id"]: v for v in vecs}
        for line in proc.stdout.strip().splitlines():
            vid, verdict, olen, otrap, orax, orcx, ordx, oefl, om0, om1, oy0 = line.split("|")
            v = by_id[vid]
            v["silicon_verdict"] = verdict
            v["silicon_len"] = int(olen)
            v["silicon_trapno"] = int(otrap)
            v["silicon_rax"] = int(orax, 16)
            v["silicon_rcx"] = int(orcx, 16)
            v["silicon_rdx"] = int(ordx, 16)
            v["silicon_efl6"] = int(oefl, 16)
            v["silicon_mem0"] = int(om0, 16)
            v["silicon_mem1"] = int(om1, 16)
            v["silicon_ymm0_hex"] = oy0

        fault_vecs = [v for v in vecs if v["silicon_verdict"] != "OK_EXEC"]
        disasm_audit = check_disassemblers_on_faults(fault_vecs, td_path)

    counts_by_verdict: dict[str, int] = {}
    counts_by_cat: dict[str, int] = {}
    for v in vecs:
        counts_by_verdict[v["silicon_verdict"]] = counts_by_verdict.get(v["silicon_verdict"], 0) + 1
        counts_by_cat[v["category"]] = counts_by_cat.get(v["category"], 0) + 1

    cpu_model = "unknown"
    for line in Path("/proc/cpuinfo").read_text().splitlines():
        if line.startswith("model name"):
            cpu_model = line.split(":", 1)[1].strip()
            break

    summary = {
        "total_vectors": len(vecs),
        "cpu_model": cpu_model,
        "counts_by_verdict": counts_by_verdict,
        "counts_by_category": counts_by_cat,
        "disassembler_fault_audit": {
            "decode_legality_trap_specimens": disasm_audit["decode_legality_trap_specimens"],
            "llvm_mc_false_accepts": disasm_audit["llvm_mc_false_accepts"],
            "objdump_false_accepts": disasm_audit["objdump_false_accepts"],
        },
    }
    out_obj = {
        "summary": summary,
        "disassembler_fault_details": disasm_audit["details"],
        "vectors": vecs,
    }
    args.out_json.parent.mkdir(parents=True, exist_ok=True)
    args.out_json.write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
