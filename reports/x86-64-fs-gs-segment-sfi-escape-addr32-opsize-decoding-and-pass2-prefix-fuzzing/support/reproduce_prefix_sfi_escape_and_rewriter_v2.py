#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
Live hardware reproducer and SFI rewriter v2 verifier on Intel Xeon Ice Lake-SP:
  1. Reproduces the `0x64` (`FS:`) and `0x65` (`GS:`) binary SFI escapes
     (`64 4F 89 04 2E` = `mov %r8, %fs:(%r14,%r13,1)` and `65 4F 89 04 2E`)
     overwriting host pages outside `[arenaBase - 64 KiB, arenaBase + 4 GiB + 64 KiB)`
     with `sig = 0`.
  2. Reproduces `0x67` (`addr32`) effective-address 32-bit truncation on
     `67 48 8B 07` (`mov (%edi), %rax`), `67 F0 48 0F B1 0F` (`addr32 lock cmpxchg`),
     `67 48 8D 07` (`addr32 lea`), `67 48 8B 05 disp32` (`[eip + disp32]`), and
     `64 67 48 8B 07` (`fsBase + ZeroExtend64(edi)`).
  3. Reproduces `0x66` (`op16`) stack misalignment (`66 50`, `48 66 50`, `66 41 50`,
     `66 58`, `66 C9` -> `rsp +- 2`) vs `REX.W` override (`66 48 50`, `66 49 50`,
     `66 48 58`, `66 48 C9` -> `rsp +- 8`), `66 B8 imm16` 4-byte immediate fetch,
     and `66` near-branch/return fetch lengths (`66 C3`, `66 E9`, `66 E8`,
     `66 0F 84`, `66 EB`) on guard-page silicon vs `llvm-mc` and `objdump`.
  4. Compiles stock `gcc 15.2.0 -O2 -fPIC -fstack-protector-strong` multi-function
     C code (with `%fs:40` stack canaries, 8-way PIC jump table, LZ4/RLE
     decompression, and `extern "C-unwind"` callback) through `sfi_gcc_rewriter_v2.py`,
     verifies `PROT_READ` canary-page tamper protection (`SIGSEGV`, `SEGV_ACCERR=2`)
     and deterministic intra-sandbox stack-overflow abort (`0xBADCA028DEAD0001`),
     benchmarks `128 MiB` sustained throughput, and exports the `2,048`-byte
     `.text.sfi` image + `.o` stack-protector specimens for Lean `v4.34.1`
     kernel verification.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sfi_gcc_rewriter_v2 as rw2  # noqa: E402


SILICON_PREFIX_ESCAPES_C = r"""
#define _GNU_SOURCE
#include <asm/prctl.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <ucontext.h>
#include <unistd.h>

static sigjmp_buf g_jmp;
static volatile int g_sig = 0;
static volatile int g_si_code = 0;
static volatile uint64_t g_trapno = 0, g_err = 0, g_rip = 0, g_rsp = 0, g_rax = 0;

static void trap_handler(int sig, siginfo_t *si, void *uap) {
    ucontext_t *uc = (ucontext_t *)uap;
    g_sig = sig;
    g_si_code = si ? si->si_code : 0;
    g_trapno = (uint64_t)uc->uc_mcontext.gregs[REG_TRAPNO];
    g_err = (uint64_t)uc->uc_mcontext.gregs[REG_ERR];
    g_rip = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
    g_rsp = (uint64_t)uc->uc_mcontext.gregs[REG_RSP];
    g_rax = (uint64_t)uc->uc_mcontext.gregs[REG_RAX];
    siglongjmp(g_jmp, 1);
}

static void run_at(uint8_t *code_ptr, uint64_t rsp_in, uint64_t rax_in, uint64_t rdi_in) {
    g_sig = 0; g_si_code = 0; g_trapno = 0; g_err = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
        struct { uint64_t code, rsp, rax, rdi; } ctx = {
            (uint64_t)code_ptr, rsp_in, rax_in, rdi_in
        };
        uint64_t saved_rsp = 0;
        __asm__ volatile(
            "mov %%rsp, %[srsp]\n\t"
            "mov 8(%[c]), %%rsp\n\t"
            "mov 16(%[c]), %%rax\n\t"
            "mov 24(%[c]), %%rdi\n\t"
            "mov $0x1122334455667788, %%r8\n\t"
            "mov 0(%[c]), %%r11\n\t"
            "jmp *%%r11\n\t"
            : [srsp] "=m"(saved_rsp)
            : [c] "r"(&ctx)
            : "rax", "rdi", "r8", "r11", "memory"
        );
    }
}

int main(void) {
    setbuf(stdout, NULL);
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = trap_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGTRAP, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);

    uint64_t orig_fs = 0, orig_gs = 0;
    syscall(SYS_arch_prctl, ARCH_GET_FS, &orig_fs);
    syscall(SYS_arch_prctl, ARCH_GET_GS, &orig_gs);

    g_sig = 0;
    uint64_t rdfs_val = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
        __asm__ volatile("rdfsbase %0" : "=r"(rdfs_val));
    }
    int fsgsbase_ring3 = (g_sig == 0 && rdfs_val == orig_fs) ? 1 : 0;

    /* 1. Live SFI FS: (`64 4F 89 04 2E`) & GS: (`65 4F 89 04 2E`) Arena Escape */
    size_t sfi_span = 65536ULL + (1ULL << 32) + 65536ULL;
    uint8_t *sfi_env = mmap((void *)0x0000001000000000ULL, sfi_span, PROT_NONE,
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | MAP_FIXED_NOREPLACE, -1, 0);
    if (sfi_env == MAP_FAILED) return 10;
    uint8_t *arena_base = sfi_env + 65536ULL;
    if (mprotect(arena_base, 0x100000, PROT_READ | PROT_WRITE) != 0) return 11;

    uint64_t guest_sp = 0x2000ULL;
    uint64_t fs_escape_va = orig_fs + (uint64_t)arena_base + guest_sp;
    uint64_t fs_escape_page = fs_escape_va & ~0xFFFULL;
    void *fs_victim = mmap((void *)fs_escape_page, 4096, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (fs_victim == MAP_FAILED) return 12;

    uint64_t gs_custom_base = 0x0000002000000000ULL;
    uint64_t gs_escape_va = gs_custom_base + (uint64_t)arena_base + guest_sp;
    uint64_t gs_escape_page = gs_escape_va & ~0xFFFULL;
    void *gs_victim = mmap((void *)gs_escape_page, 4096, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (gs_victim == MAP_FAILED) return 13;

    /* Build real 96-byte (3-bundle) PIC Portal SFI image:
       Bundle 0 (0x00): c3 + 31x90 (Portal 0 exit)
       Bundle 1 (0x20): eb fe + 30x90 (Portal 1 stub)
       Bundle 2 (0x40): 64 4f 89 04 2e (`mov %r8, %fs:(%r14,%r13,1)`) + e9 b6 ff ff ff (`jmp 0x00`) + 22x90 */
    uint8_t *sfi_code = mmap(NULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    memset(sfi_code, 0x90, 96);
    sfi_code[0] = 0xc3;
    sfi_code[32] = 0xeb; sfi_code[33] = 0xfe;
    uint8_t fs_bundle_insns[] = {0x64, 0x4f, 0x89, 0x04, 0x2e, 0xe9, 0xb6, 0xff, 0xff, 0xff};
    memcpy(sfi_code + 64, fs_bundle_insns, sizeof(fs_bundle_insns));

    *(uint64_t *)fs_escape_va = 0xCAFEBABE12345678ULL;
    *(uint64_t *)(arena_base + guest_sp) = 0xAAAAAAAAAAAAAAAAULL;
    g_sig = 0;
    __asm__ volatile(
        "mov %[cb], %%r15\n\t"
        "mov %[ab], %%r14\n\t"
        "mov %[gsp], %%r13\n\t"
        "mov $0xDEADBEEFCAFE0001, %%r8\n\t"
        "call *%[entry]\n\t"
        :
        : [cb] "r"(sfi_code), [ab] "r"(arena_base), [gsp] "r"(guest_sp), [entry] "r"(sfi_code + 64)
        : "r8", "r13", "r14", "r15", "memory"
    );
    int fs_sig = g_sig;
    uint64_t fs_victim_after = *(uint64_t *)fs_escape_va;
    uint64_t fs_arena_slot_after = *(uint64_t *)(arena_base + guest_sp);

    /* GS escape (`65 4F 89 04 2E`) */
    sfi_code[64] = 0x65;
    *(uint64_t *)gs_escape_va = 0xCAFEBABE87654321ULL;
    g_sig = 0;
    __asm__ volatile(
        "rdgsbase %%r10\n\t"
        "wrgsbase %[gsb]\n\t"
        "mov %[cb], %%r15\n\t"
        "mov %[ab], %%r14\n\t"
        "mov %[gsp], %%r13\n\t"
        "mov $0xDEADBEEFCAFE0002, %%r8\n\t"
        "call *%[entry]\n\t"
        "wrgsbase %%r10\n\t"
        :
        : [gsb] "r"(gs_custom_base), [cb] "r"(sfi_code), [ab] "r"(arena_base),
          [gsp] "r"(guest_sp), [entry] "r"(sfi_code + 64)
        : "r8", "r10", "r13", "r14", "r15", "memory"
    );
    int gs_sig = g_sig;
    uint64_t gs_victim_after = *(uint64_t *)gs_escape_va;

    /* 2. Prefix Group 2 (`0x26/0x2E/0x36/0x3E` null prefixes DO NOT clear `0x64/0x65`) + `LEA` ignores `FS:` */
    uint8_t *arena3 = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    uint64_t *flat_p = (uint64_t *)(arena3 + 0x1000);
    uint64_t *fs_p   = (uint64_t *)(arena3 + 0x2000);
    uint64_t *gs_p   = (uint64_t *)(arena3 + 0x3000);
    *flat_p = 0xF1A700000000F1A7ULL;
    *fs_p   = 0xF5F500000000F5F5ULL;
    *gs_p   = 0x6565000000006565ULL;

    uint8_t *scratch_exec = sfi_code + 512;
    struct { const char *k; uint8_t b[12]; int n; uint64_t res; } seg_cases[] = {
        {"fs_only_64",    {0x64, 0x48, 0x8b, 0x07, 0xc3}, 5, 0},
        {"fs_then_gs",    {0x64, 0x65, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"gs_then_fs",    {0x65, 0x64, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"fs_then_cs_2e", {0x64, 0x2e, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"fs_then_ds_3e", {0x64, 0x3e, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"fs_then_es_26", {0x64, 0x26, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"fs_then_ss_36", {0x64, 0x36, 0x48, 0x8b, 0x07, 0xc3}, 6, 0},
        {"fs_lea_ignores",{0x64, 0x48, 0x8d, 0x07, 0xc3}, 5, 0},
    };
    for (int i = 0; i < 8; i++) {
        memcpy(scratch_exec, seg_cases[i].b, (size_t)seg_cases[i].n);
        uint64_t out = 0, tfs = 0x1000ULL, tgs = 0x2000ULL;
        __asm__ volatile(
            "rdfsbase %%r12\n\t"
            "rdgsbase %%r13\n\t"
            "wrfsbase %[tfs]\n\t"
            "wrgsbase %[tgs]\n\t"
            "mov %[ptr], %%rdi\n\t"
            "call *%[fn]\n\t"
            "wrfsbase %%r12\n\t"
            "wrgsbase %%r13\n\t"
            "mov %%rax, %[out]\n\t"
            : [out] "=r"(out)
            : [tfs] "r"(tfs), [tgs] "r"(tgs), [ptr] "r"(flat_p), [fn] "r"(scratch_exec)
            : "rax", "rdi", "r12", "r13", "memory"
        );
        seg_cases[i].res = out;
    }

    /* 3. `0x67` (`addr32`) truncation tests */
    void *lo32 = mmap((void *)0x40001000ULL, 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    void *hi64 = mmap((void *)0x0000000140001000ULL, 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    *(uint64_t *)lo32 = 0xAAAABBBBCCCCDDDDULL;
    *(uint64_t *)hi64 = 0x1111222233334444ULL;

    uint8_t c_load32[] = {0x67, 0x48, 0x8b, 0x07, 0xc3};
    memcpy(scratch_exec, c_load32, sizeof(c_load32));
    uint64_t a32_load = ((uint64_t (*)(void *))scratch_exec)(hi64);

    uint8_t c_lea64[] = {0x67, 0x48, 0x8d, 0x07, 0xc3};
    memcpy(scratch_exec, c_lea64, sizeof(c_lea64));
    uint64_t a32_lea = ((uint64_t (*)(void *))scratch_exec)(hi64);

    uint8_t c_cmpx[] = {0x67, 0xf0, 0x48, 0x0f, 0xb1, 0x0f, 0xc3};
    memcpy(scratch_exec, c_cmpx, sizeof(c_cmpx));
    uint64_t cmpx_rax = 0xAAAABBBBCCCCDDDDULL;
    __asm__ volatile(
        "call *%[fn]"
        : "+a"(cmpx_rax)
        : "c"(0x9999888877776666ULL), "D"(hi64), [fn] "r"(scratch_exec)
        : "cc", "memory"
    );
    uint64_t a32_cmpx_lo = *(uint64_t *)lo32;
    uint64_t a32_cmpx_hi = *(uint64_t *)hi64;

    uint8_t *hi_code = mmap((void *)0x0000000240002000ULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC,
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    uint8_t *lo_data = mmap((void *)0x40002000ULL, 4096, PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    *(uint64_t *)(hi_code + 0x10) = 0x6464646464646464ULL;
    *(uint64_t *)(lo_data + 0x10) = 0x3232323232323232ULL;
    uint8_t c_rip32[] = {0x67, 0x48, 0x8b, 0x05, 0x08, 0x00, 0x00, 0x00, 0xc3};
    memcpy(hi_code, c_rip32, sizeof(c_rip32));
    uint64_t a32_riprel = ((uint64_t (*)(void))hi_code)();

    /* `64 67 48 8B 07`: fs_base (64-bit > 4 GiB) + ZeroExtend64(edi) */
    uint8_t *fs_a32_page = mmap((void *)0x0000000540001000ULL, 4096, PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    *(uint64_t *)fs_a32_page = 0x7777666655554444ULL;
    uint8_t c_fs_a32[] = {0x64, 0x67, 0x48, 0x8b, 0x07, 0xc3};
    memcpy(scratch_exec, c_fs_a32, sizeof(c_fs_a32));
    uint64_t fs_a32_out = 0;
    __asm__ volatile(
        "rdfsbase %%r11\n\t"
        "wrfsbase %[f]\n\t"
        "call *%[fn]\n\t"
        "wrfsbase %%r11\n\t"
        : "=a"(fs_a32_out)
        : "D"(0x0000000940001000ULL), [f] "r"(0x0000000500000000ULL), [fn] "r"(scratch_exec)
        : "r11", "memory"
    );

    /* 4. `0x66` (`op16`) stack misalignment (`+-2`) vs `REX.W` override (`+-8`) & branch fetch lengths */
    uint8_t *guard_pages = mmap(NULL, 8192, PROT_READ | PROT_WRITE | PROT_EXEC,
                                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    mprotect(guard_pages + 4096, 4096, PROT_NONE);
    uint8_t *page_end = guard_pages + 4096;
    uint8_t *stk_pages = mmap(NULL, 16384, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    uint64_t stk_top = (uint64_t)(stk_pages + 8192);

    struct { const char *k; uint8_t b[8]; int n; int len; long rspd; uint64_t rax_out; uint64_t mem_top; } stk_cases[] = {
        {"push_50",       {0x50, 0xcc}, 2, 0, 0, 0, 0},
        {"push_66_50",    {0x66, 0x50, 0xcc}, 3, 0, 0, 0, 0},
        {"push_48_66_50", {0x48, 0x66, 0x50, 0xcc}, 4, 0, 0, 0, 0},
        {"push_66_41_50", {0x66, 0x41, 0x50, 0xcc}, 4, 0, 0, 0, 0},
        {"push_66_48_50", {0x66, 0x48, 0x50, 0xcc}, 4, 0, 0, 0, 0},
        {"push_66_49_50", {0x66, 0x49, 0x50, 0xcc}, 4, 0, 0, 0, 0},
        {"pop_58",        {0x58, 0xcc}, 2, 0, 0, 0, 0},
        {"pop_66_58",     {0x66, 0x58, 0xcc}, 3, 0, 0, 0, 0},
        {"pop_48_66_58",  {0x48, 0x66, 0x58, 0xcc}, 4, 0, 0, 0, 0},
        {"pop_66_48_58",  {0x66, 0x48, 0x58, 0xcc}, 4, 0, 0, 0, 0},
    };
    for (int i = 0; i < 10; i++) {
        memset(stk_pages, 0xAA, 16384);
        *(uint64_t *)stk_top = 0xCAFEBABEDEADBEEFULL;
        uint8_t *buf = guard_pages + 1024;
        memcpy(buf, stk_cases[i].b, (size_t)stk_cases[i].n);
        run_at(buf, stk_top, 0x0102030405060708ULL, stk_top);
        stk_cases[i].len = (int)(g_rip - (uint64_t)buf) - 1;
        stk_cases[i].rspd = (long)g_rsp - (long)stk_top;
        stk_cases[i].rax_out = g_rax;
        stk_cases[i].mem_top = *(uint64_t *)g_rsp;
    }

    struct { const char *k; uint8_t b[12]; int n; int fetch_len; long rspd; } br_cases[] = {
        {"ret_66_c3",    {0x66, 0xc3}, 2, 0, 0},
        {"jmp_66_e9",    {0x66, 0xe9, 0x00, 0x00, 0x00, 0x00}, 6, 0, 0},
        {"call_66_e8",   {0x66, 0xe8, 0x00, 0x00, 0x00, 0x00}, 6, 0, 0},
        {"jcc_66_0f84",  {0x66, 0x0f, 0x84, 0x00, 0x00, 0x00, 0x00}, 7, 0, 0},
        {"jmp_66_eb",    {0x66, 0xeb, 0x00}, 3, 0, 0},
        {"mov_66_b8",    {0x66, 0xb8, 0x11, 0x22}, 4, 0, 0},
    };
    for (int i = 0; i < 6; i++) {
        for (int L = 1; L <= 8; L++) {
            uint8_t *start = page_end - L;
            memset(start, 0x00, (size_t)L);
            int cn = br_cases[i].n < L ? br_cases[i].n : L;
            memcpy(start, br_cases[i].b, (size_t)cn);
            uint8_t *ret_landing = guard_pages + 512;
            ret_landing[0] = 0xcc;
            *(uint64_t *)stk_top = (uint64_t)ret_landing;
            run_at(start, stk_top, 0, 0);
            if (g_trapno == 14 && g_rip == (uint64_t)start) continue;
            br_cases[i].fetch_len = L;
            br_cases[i].rspd = (long)g_rsp - (long)stk_top;
            break;
        }
    }

    printf("{\n");
    printf("  \"fsgsbase_ring3_enabled\": %s,\n", fsgsbase_ring3 ? "true" : "false");
    printf("  \"sfi_fs_gs_escape\": {\n");
    printf("    \"orig_fs_base\": \"0x%016lx\",\n", orig_fs);
    printf("    \"arena_base\": \"0x%016lx\",\n", (uint64_t)arena_base);
    printf("    \"arena_guarded_span_lo\": \"0x%016lx\",\n", (uint64_t)sfi_env);
    printf("    \"arena_guarded_span_hi\": \"0x%016lx\",\n", (uint64_t)sfi_env + sfi_span);
    printf("    \"fs_escape_bundle_hex\": \"644f89042ee9b6ffffff\",\n");
    printf("    \"fs_escape_va\": \"0x%016lx\",\n", fs_escape_va);
    printf("    \"fs_outside_arena_envelope\": %s,\n",
           (fs_escape_va >= (uint64_t)sfi_env + sfi_span) ? "true" : "false");
    printf("    \"fs_sig\": %d,\n", fs_sig);
    printf("    \"fs_victim_after\": \"0x%016lx\",\n", fs_victim_after);
    printf("    \"fs_arena_slot_after\": \"0x%016lx\",\n", fs_arena_slot_after);
    printf("    \"gs_escape_va\": \"0x%016lx\",\n", gs_escape_va);
    printf("    \"gs_sig\": %d,\n", gs_sig);
    printf("    \"gs_victim_after\": \"0x%016lx\"\n", gs_victim_after);
    printf("  },\n");
    printf("  \"prefix_group2_and_lea\": {\n");
    for (int i = 0; i < 8; i++) {
        printf("    \"%s\": \"0x%016lx\"%s\n", seg_cases[i].k, seg_cases[i].res, i + 1 < 8 ? "," : "");
    }
    printf("  },\n");
    printf("  \"addr32_truncation\": {\n");
    printf("    \"rdi_input\": \"0x0000000140001000\",\n");
    printf("    \"load64_67_48_8b_07\": \"0x%016lx\",\n", a32_load);
    printf("    \"lea64_67_48_8d_07\": \"0x%016lx\",\n", a32_lea);
    printf("    \"lock_cmpxchg_67_lo32_after\": \"0x%016lx\",\n", a32_cmpx_lo);
    printf("    \"lock_cmpxchg_67_hi64_after\": \"0x%016lx\",\n", a32_cmpx_hi);
    printf("    \"rip_rel_67_at_0x240002000\": \"0x%016lx\",\n", a32_riprel);
    printf("    \"fs_plus_addr32_64_67_48_8b_07\": \"0x%016lx\"\n", fs_a32_out);
    printf("  },\n");
    printf("  \"op16_stack_and_rexw\": {\n");
    for (int i = 0; i < 10; i++) {
        printf("    \"%s\": {\"len\": %d, \"rsp_delta\": %ld, \"rax_out\": \"0x%016lx\", \"stack_top\": \"0x%016lx\"}%s\n",
               stk_cases[i].k, stk_cases[i].len, stk_cases[i].rspd, stk_cases[i].rax_out, stk_cases[i].mem_top,
               i + 1 < 10 ? "," : "");
    }
    printf("  },\n");
    printf("  \"op16_guard_page_fetch_lengths\": {\n");
    for (int i = 0; i < 6; i++) {
        printf("    \"%s\": {\"fetch_len\": %d, \"rsp_delta\": %ld}%s\n",
               br_cases[i].k, br_cases[i].fetch_len, br_cases[i].rspd, i + 1 < 6 ? "," : "");
    }
    printf("  }\n");
    printf("}\n");
    return 0;
}
"""


WORKLOAD_CANARY_C = r"""
#include <stdint.h>

#ifdef NATIVE_MODE
#define ARENA_PTR(base, off) ((uint64_t *)((uintptr_t)(base) + (uint32_t)(off)))
extern uint64_t native_hostcall(uint64_t tag, uint64_t a0, uint64_t a1);
#else
#define ARENA_PTR(base, off) ((uint64_t *)(uintptr_t)(uint32_t)(off))
extern uint64_t sfi_hostcall(uint64_t tag, uint64_t a0, uint64_t a1);
#endif

__attribute__((noinline))
uint64_t FUNC(opcode_mix)(uint64_t op, uint64_t x, uint64_t y) {
    switch (op & 7) {
        case 0: return (x + y) ^ 0x9e3779b97f4a7c15ULL;
        case 1: return (x * 0x517cc1b727220a95ULL) + y;
        case 2: return (x << 13) | (y >> 7);
        case 3: return (x ^ y) * 33ULL;
        case 4: return (x - y) + (x >> 3);
        case 5: return (x & 0xff00ff00ff00ff00ULL) | (y & 0x00ff00ff00ff00ffULL);
        case 6: return (x + (y << 5)) ^ (x >> 11);
        default: return x ^ (y * 7ULL);
    }
}

/* Stack-buffer-using frame that triggers `-fstack-protector-strong` `%fs:40` canary! */
__attribute__((noinline))
uint64_t FUNC(frame_window_fold)(uint64_t seed, uint64_t a, uint64_t b, uint64_t smash_idx, uint64_t smash_val) {
    volatile uint64_t win[4];
    win[0] = seed ^ a;
    win[1] = a + 0x123456789ABCDEF0ULL;
    win[2] = b ^ 0x0FEDCBA987654321ULL;
    win[3] = (seed << 7) ^ b;
    if (smash_idx != 0) {
        win[smash_idx] = smash_val;
    }
    return (win[0] + win[1]) ^ (win[2] + win[3]);
}

__attribute__((noinline))
uint64_t FUNC(checksum64)(
#ifdef NATIVE_MODE
    uint8_t *arena_base,
#endif
    uint32_t words_off, uint64_t count, uint64_t seed
) {
    const uint64_t *words = ARENA_PTR(arena_base, words_off);
    uint64_t acc = seed;
    for (uint64_t i = 0; i < count; i++) {
        uint64_t w = words[i];
        acc = (acc ^ w) * 0x2545F4914F6CDD1DULL;
        acc ^= (acc >> 27);
    }
    return acc;
}

__attribute__((noinline))
uint64_t FUNC(rle64_decompress_and_stream)(
#ifdef NATIVE_MODE
    uint8_t *arena_base,
#endif
    uint32_t src_off, uint64_t src_words,
    uint32_t dst_off, uint64_t dst_cap_words,
    uint64_t cb_tag
) {
    const uint64_t *src = ARENA_PTR(arena_base, src_off);
    uint64_t *dst = ARENA_PTR(arena_base, dst_off);
    uint64_t si = 0, di = 0;
    while (si + 2 <= src_words) {
        uint64_t ctrl = src[si++];
        uint64_t val_or_off = src[si++];
        uint64_t tag = ctrl >> 32;
        uint64_t count = ctrl & 0xffffffffULL;
        if (di + count > dst_cap_words) break;
        if (tag == 0) {
            for (uint64_t k = 0; k < count; k++) {
                dst[di++] = val_or_off;
            }
        } else {
            if (val_or_off == 0 || val_or_off > di) break;
            uint64_t back = di - val_or_off;
            for (uint64_t k = 0; k < count; k++) {
                dst[di++] = dst[back + k];
            }
        }
    }
#ifdef NATIVE_MODE
    uint64_t csum = FUNC(checksum64)(arena_base, dst_off, di, 0xcbf29ce484222325ULL);
    uint64_t folded = FUNC(frame_window_fold)(csum, di, src_words, 0, 0);
    uint64_t mixed = FUNC(opcode_mix)(di, folded, src_words);
    uint64_t cb_res = native_hostcall(cb_tag, di, mixed);
#else
    uint64_t csum = FUNC(checksum64)(dst_off, di, 0xcbf29ce484222325ULL);
    uint64_t folded = FUNC(frame_window_fold)(csum, di, src_words, 0, 0);
    uint64_t mixed = FUNC(opcode_mix)(di, folded, src_words);
    uint64_t cb_res = sfi_hostcall(cb_tag, di, mixed);
#endif
    return mixed ^ cb_res;
}

#ifndef NATIVE_MODE
__attribute__((noinline))
uint64_t sfi_attempt_forge_canary_page(uint32_t canary_off, uint64_t fake) {
    volatile uint64_t *p = (volatile uint64_t *)(uintptr_t)canary_off;
    *p = fake;
    return *p;
}
#endif
"""


SFI_DRIVER_C = r"""
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <ucontext.h>

extern const uint8_t __sfi_text_start[];
extern const uint8_t __sfi_text_used_end[];
extern const uint8_t __sfi_text_end[];
extern const uint8_t __sfi_rodata_start[];
extern const uint8_t __sfi_rodata_end[];

extern const uint8_t sfi_rle64_decompress_and_stream[];
extern const uint8_t sfi_frame_window_fold[];
extern const uint8_t sfi_attempt_forge_canary_page[];

extern uint64_t native_rle64_decompress_and_stream(
    uint8_t *arena_base, uint32_t src_off, uint64_t src_words,
    uint32_t dst_off, uint64_t dst_cap_words, uint64_t cb_tag);

typedef struct {
    uint8_t *code_base;
    uint8_t *arena_base;
    uint64_t (*hostcall_fn)(uint64_t, uint64_t, uint64_t);
    uint32_t guest_sp;
    uint32_t _pad;
} SfiContext;

extern uint64_t sfi_enter_trampoline(
    SfiContext *ctx, uint64_t entry_off,
    uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4);

__asm__(
    ".text\n"
    ".globl sfi_enter_trampoline\n"
    "sfi_enter_trampoline:\n"
    "  pushq %rbp\n"
    "  pushq %rbx\n"
    "  pushq %r12\n"
    "  pushq %r13\n"
    "  pushq %r14\n"
    "  pushq %r15\n"
    "  subq $8, %rsp\n"
    "  movq %rdi, %r12\n"
    "  movq 0(%r12), %r15\n"
    "  movq 8(%r12), %r14\n"
    "  movl 24(%r12), %r13d\n"
    "  movq $0, (%r14,%r13,1)\n"
    "  leaq (%r15,%rsi,1), %rax\n"
    "  movq %rdx, %rdi\n"
    "  movq %rcx, %rsi\n"
    "  movq %r8, %rdx\n"
    "  movq %r9, %rcx\n"
    "  movq 64(%rsp), %r8\n"
    "  call *%rax\n"
    ".Lsfi_after_guest:\n"
    "  addq $8, %rsp\n"
    "  popq %r15\n"
    "  popq %r14\n"
    "  popq %r13\n"
    "  popq %r12\n"
    "  popq %rbx\n"
    "  popq %rbp\n"
    "  ret\n"
    "\n"
    ".globl sfi_hostcall_trampoline\n"
    "sfi_hostcall_trampoline:\n"
    "  pushq %r13\n"
    "  movl %r13d, %eax\n"
    "  subl $4096, %eax\n"
    "  andl $-16, %eax\n"
    "  movl %eax, 24(%r12)\n"
    "  movq 16(%r12), %rax\n"
    "  call *%rax\n"
    "  popq %r13\n"
    "  movl %r13d, %r13d\n"
    "  movq 0(%r12), %r15\n"
    "  movq 8(%r12), %r14\n"
    "  movl (%r14,%r13,1), %r11d\n"
    "  addl $8, %r13d\n"
    "  andl $2016, %r11d\n"
    "  leaq (%r15,%r11,1), %r11\n"
    "  jmp *%r11\n"
);

static uint64_t g_cb_acc = 0;
uint64_t native_hostcall(uint64_t tag, uint64_t a0, uint64_t a1) {
    uint64_t v = (tag * 31ULL) ^ (a0 + (a1 >> 11));
    g_cb_acc ^= v;
    return v;
}

static sigjmp_buf g_ProtJmp;
static volatile int g_ProtSig = 0, g_ProtCode = 0;
static void prot_handler(int sig, siginfo_t *si, void *uap) {
    (void)uap;
    g_ProtSig = sig;
    g_ProtCode = si ? si->si_code : 0;
    siglongjmp(g_ProtJmp, 1);
}

static uint64_t mono_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(void) {
    size_t sfi_span = 65536ULL + (1ULL << 32) + 65536ULL;
    uint8_t *env = mmap(NULL, sfi_span, PROT_NONE,
                        MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (env == MAP_FAILED) return 2;
    uint8_t *arena = env + 65536ULL;
    /* Map [0 .. 0xF000) RW, [0xF000 .. 0x10000) PROT_READ canary page, [0x10000 .. 0x200000) RW */
    if (mprotect(arena, 0x200000, PROT_READ | PROT_WRITE) != 0) return 3;
    *(uint64_t *)(arena + 0xFE28) = 0x5EC0CACAA9876543ULL;
    if (mprotect(arena + 0xF000, 0x1000, PROT_READ) != 0) return 4;

    size_t ro_len = (size_t)(__sfi_rodata_end - __sfi_rodata_start);
    if (ro_len > 0) {
        memcpy(arena + 0x10000, __sfi_rodata_start, ro_len);
    }

    /* Prepare 64 KiB (8,192-word) RLE + LZ4 back-reference payload at 0x20000 -> dst 0x40000 */
    uint64_t *src = (uint64_t *)(arena + 0x20000);
    size_t si = 0, produced = 0;
    uint64_t seed = 0x123456789ABCDEF0ULL;
    while (produced < 8192) {
        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
        if (produced >= 64 && (seed & 3ULL) != 0) {
            uint64_t cnt = 16;
            if (produced + cnt > 8192) cnt = 8192 - produced;
            src[si++] = (1ULL << 32) | cnt;
            src[si++] = 32ULL;
            produced += cnt;
        } else {
            uint64_t cnt = 8;
            if (produced + cnt > 8192) cnt = 8192 - produced;
            src[si++] = (0ULL << 32) | cnt;
            src[si++] = seed;
            produced += cnt;
        }
    }

    SfiContext ctx = {
        .code_base = (uint8_t *)__sfi_text_start,
        .arena_base = arena,
        .hostcall_fn = native_hostcall,
        .guest_sp = 0xF0000,
        ._pad = 0,
    };

    uint64_t entry_rle = (uint64_t)(sfi_rle64_decompress_and_stream - __sfi_text_start);
    uint64_t entry_fold = (uint64_t)(sfi_frame_window_fold - __sfi_text_start);
    uint64_t entry_forge = (uint64_t)(sfi_attempt_forge_canary_page - __sfi_text_start);

    uint64_t r_nat = native_rle64_decompress_and_stream(arena, 0x20000, si, 0x40000, 8192, 7);
    uint64_t r_sfi = sfi_enter_trampoline(&ctx, entry_rle, 0x20000, si, 0x60000, 8192, 7);
    int eq_out = (r_nat == r_sfi) && (memcmp(arena + 0x40000, arena + 0x60000, 8192 * 8) == 0);

    /* Benchmark 2,000 iterations = 128 MiB */
    const int iters = 2000;
    uint64_t t0 = mono_ns();
    uint64_t sink_nat = 0;
    for (int i = 0; i < iters; i++) {
        sink_nat ^= native_rle64_decompress_and_stream(arena, 0x20000, si, 0x40000, 8192, (uint64_t)i);
    }
    uint64_t t1 = mono_ns();
    uint64_t sink_sfi = 0;
    for (int i = 0; i < iters; i++) {
        ctx.guest_sp = 0xF0000;
        sink_sfi ^= sfi_enter_trampoline(&ctx, entry_rle, 0x20000, si, 0x60000, 8192, (uint64_t)i);
    }
    uint64_t t2 = mono_ns();

    /* Test 1: Normal canary-protected frame call (`smash_idx = 0`) */
    ctx.guest_sp = 0xF0000;
    uint64_t fold_clean = sfi_enter_trampoline(&ctx, entry_fold, 0x1111, 0x2222, 0x3333, 0, 0);

    /* Test 2: Intra-sandbox stack overflow (`smash_idx = 5` overwrites saved canary slot at `40(%rsp)`!) */
    ctx.guest_sp = 0xF0000;
    uint64_t fold_smashed = sfi_enter_trampoline(&ctx, entry_fold, 0x1111, 0x2222, 0x3333, 5, 0xDEADC0DEULL);

    /* Test 3: Attempt to forge `PROT_READ` reference canary at `0xFE28` traps with `SIGSEGV` (`SEGV_ACCERR = 2`) */
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = prot_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER;
    sigaction(SIGSEGV, &sa, NULL);
    g_ProtSig = 0; g_ProtCode = 0;
    if (sigsetjmp(g_ProtJmp, 1) == 0) {
        ctx.guest_sp = 0xF0000;
        (void)sfi_enter_trampoline(&ctx, entry_forge, 0xFE28, 0xDEADC0DEULL, 0, 0, 0);
    }
    uint64_t canary_ref_after = *(uint64_t *)(arena + 0xFE28);

    double nat_ns = (double)(t1 - t0) / (double)iters;
    double sfi_ns = (double)(t2 - t1) / (double)iters;
    double nat_mib_s = (128.0 * 1e9) / (double)(t1 - t0);
    double sfi_mib_s = (128.0 * 1e9) / (double)(t2 - t1);

    printf("{\n");
    printf("  \"outputs_equal\": %s,\n", (eq_out && sink_nat == sink_sfi) ? "true" : "false");
    printf("  \"active_sfi_bytes\": %zu,\n", (size_t)(__sfi_text_used_end - __sfi_text_start));
    printf("  \"total_sfi_bytes\": %zu,\n", (size_t)(__sfi_text_end - __sfi_text_start));
    printf("  \"native_ns_per_64kib\": %.2f,\n", nat_ns);
    printf("  \"sfi_v2_canary_ns_per_64kib\": %.2f,\n", sfi_ns);
    printf("  \"overhead_pct\": %.2f,\n", ((sfi_ns - nat_ns) / nat_ns) * 100.0);
    printf("  \"native_mib_per_s\": %.2f,\n", nat_mib_s);
    printf("  \"sfi_v2_canary_mib_per_s\": %.2f,\n", sfi_mib_s);
    printf("  \"canary_clean_ret\": \"0x%016lx\",\n", fold_clean);
    printf("  \"canary_smashed_ret\": \"0x%016lx\",\n", fold_smashed);
    printf("  \"canary_forge_sig\": %d,\n", g_ProtSig);
    printf("  \"canary_forge_si_code\": %d,\n", g_ProtCode);
    printf("  \"canary_ref_intact\": %s\n", (canary_ref_after == 0x5EC0CACAA9876543ULL) ? "true" : "false");
    printf("}\n");
    return 0;
}
"""


GCC_LIFT_SPECIMEN_C = r"""
#include <stdint.h>
uint64_t gcc_hash2_canary(uint64_t x, uint64_t y) {
    uint64_t buf[2];
    buf[0] = x + 0x12345678ULL;
    buf[1] = y ^ 0x87654321ULL;
    __asm__ volatile("" : "+m"(buf));
    return (buf[0] * 5ULL) ^ buf[1];
}
"""

RUST_LIFT_SPECIMEN_RS = r"""#![no_std]
#[no_mangle]
pub extern "C" fn rust_unexposed_canary(x: u64, y: u64) -> u64 {
    let mut a: u64 = 0;
    let mut b: u64 = 0;
    unsafe {
        core::ptr::write_volatile(&mut a, x.wrapping_add(0x12345678));
        core::ptr::write_volatile(&mut b, y ^ 0x87654321);
        let r0 = core::ptr::read_volatile(&a);
        let r1 = core::ptr::read_volatile(&b);
        r0.wrapping_mul(0x9E3779B97F4A7C15) ^ r1
    }
}
"""


def extract_section_bytes(obj_path: Path, sec_name: str, td: Path) -> bytes:
    raw_path = td / f"{obj_path.stem}_{sec_name.lstrip('.')}.bin"
    subprocess.run(
        ["objcopy", "-O", "binary", f"--only-section={sec_name}", str(obj_path), str(raw_path)],
        check=True,
    )
    return raw_path.read_bytes()


def disasm_comparison(hex_str: str, td: Path) -> dict[str, object]:
    mc_in = " ".join("0x" + b for b in hex_str.split())
    r_mc = subprocess.run(
        ["llvm-mc", "--disassemble", "--triple=x86_64-unknown-linux-gnu"],
        input=mc_in,
        text=True,
        capture_output=True,
        check=False,
    )
    bin_p = td / "snip.bin"
    bin_p.write_bytes(bytes.fromhex(hex_str))
    r_obj = subprocess.run(
        ["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", str(bin_p)],
        text=True,
        capture_output=True,
        check=False,
    )
    return {
        "llvm_mc_rc": r_mc.returncode,
        "llvm_mc_lines": [
            ln.strip() for ln in r_mc.stdout.splitlines() if ln.strip() and not ln.strip().startswith(".")
        ],
        "objdump_rc": r_obj.returncode,
        "objdump_lines": [ln.strip() for ln in r_obj.stdout.splitlines() if "\t" in ln],
    }


def main() -> None:
    out_json = HERE / "prefix_sfi_escape_and_rewriter_v2_results.json"
    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)

        # 1. Run live silicon prefix escape + addr32 + op16 probe
        esc_c = td / "silicon_prefix_escapes.c"
        esc_bin = td / "silicon_prefix_escapes"
        esc_c.write_text(SILICON_PREFIX_ESCAPES_C)
        subprocess.run(
            ["gcc", "-O2", "-fno-stack-protector", str(esc_c), "-o", str(esc_bin)],
            check=True,
            cwd=td,
        )
        esc_out = subprocess.run([str(esc_bin)], capture_output=True, text=True, check=True, cwd=td).stdout
        silicon_res = json.loads(esc_out)

        assert silicon_res["sfi_fs_gs_escape"]["fs_sig"] == 0
        assert silicon_res["sfi_fs_gs_escape"]["fs_victim_after"] == "0xdeadbeefcafe0001"
        assert silicon_res["sfi_fs_gs_escape"]["gs_sig"] == 0
        assert silicon_res["sfi_fs_gs_escape"]["gs_victim_after"] == "0xdeadbeefcafe0002"
        assert silicon_res["addr32_truncation"]["load64_67_48_8b_07"] == "0xaaaabbbbccccdddd"
        assert silicon_res["addr32_truncation"]["lock_cmpxchg_67_lo32_after"] == "0x9999888877776666"
        assert silicon_res["addr32_truncation"]["lock_cmpxchg_67_hi64_after"] == "0x1111222233334444"
        assert silicon_res["op16_stack_and_rexw"]["push_66_50"]["rsp_delta"] == -2
        assert silicon_res["op16_stack_and_rexw"]["push_48_66_50"]["rsp_delta"] == -2
        assert silicon_res["op16_stack_and_rexw"]["push_66_48_50"]["rsp_delta"] == -8

        # 2. Disassembler comparison on 0x66 control-flow desynchronization
        disasm_66 = {}
        for k, hx in [
            ("ret_66_c3", "66 c3"),
            ("jmp_66_e9", "66 e9 01 00 00 00"),
            ("call_66_e8", "66 e8 01 00 00 00"),
            ("jcc_66_0f84", "66 0f 84 01 00 00 00"),
            ("push_66_48_50", "66 48 50"),
            ("push_48_66_50", "48 66 50"),
        ]:
            disasm_66[k] = disasm_comparison(hx, td)

        # 3. Compile multi-function C workload with `-fstack-protector-strong` & rewrite via `sfi_gcc_rewriter_v2.py`
        nat_c = td / "workload_nat.c"
        sfi_c = td / "workload_sfi.c"
        nat_c.write_text("#define NATIVE_MODE 1\n#define FUNC(x) native_##x\n" + WORKLOAD_CANARY_C)
        sfi_c.write_text("#define FUNC(x) sfi_##x\n" + WORKLOAD_CANARY_C)

        nat_o = td / "workload_nat.o"
        subprocess.run(
            ["gcc", "-O2", "-fPIC", "-fstack-protector-strong", "-c", str(nat_c), "-o", str(nat_o)],
            check=True,
            cwd=td,
        )

        sfi_raw_s = td / "workload_sfi_raw.s"
        subprocess.run(
            [
                "gcc", "-O2", "-fPIC", "-fvisibility=hidden", "-fno-tree-vectorize",
                "-ffixed-rbp", "-ffixed-rbx", "-ffixed-r11", "-ffixed-r12",
                "-ffixed-r13", "-ffixed-r14", "-ffixed-r15",
                "-mno-red-zone", "-fstack-protector-strong",
                "-fno-unwind-tables", "-fno-asynchronous-unwind-tables",
                "-fcf-protection=none", "-S", str(sfi_c), "-o", str(sfi_raw_s),
            ],
            check=True,
            cwd=td,
        )
        raw_asm_txt = sfi_raw_s.read_text()
        assert "%fs:40" in raw_asm_txt, "expected -fstack-protector-strong to emit %fs:40"

        rewritten_s = rw2.rewrite_gcc_att_to_sfi_v2(
            raw_asm_txt, rw2.RewriteConfigV2(code_size_pow2=2048, canary_mode="arena_guarded")
        )
        assert "%fs:" not in rewritten_s and "%gs:" not in rewritten_s
        sfi_s_path = td / "workload_sfi_v2.s"
        sfi_o_path = td / "workload_sfi_v2.o"
        sfi_s_path.write_text(rewritten_s)
        subprocess.run(["gcc", "-c", str(sfi_s_path), "-o", str(sfi_o_path)], check=True, cwd=td)

        # Inspect relocations in `.text.sfi`: only Portal 1 at 0x21 is allowed
        rel_out = subprocess.run(
            ["readelf", "-r", "-W", str(sfi_o_path)], capture_output=True, text=True, check=True, cwd=td
        ).stdout
        untrusted_relocs = []
        in_text_rela = False
        for ln in rel_out.splitlines():
            if ln.startswith("Relocation section"):
                in_text_rela = ".rela.text.sfi" in ln
                continue
            if in_text_rela and ln and ln[0] in "0123456789abcdef":
                off = int(ln.split()[0], 16)
                if off >= 0x40:
                    untrusted_relocs.append(ln.strip())
        assert len(untrusted_relocs) == 0, f"unexpected untrusted relocs: {untrusted_relocs}"

        sfi_text_bytes = extract_section_bytes(sfi_o_path, ".text.sfi", td)
        assert len(sfi_text_bytes) == 2048

        drv_c = td / "driver.c"
        drv_bin = td / "driver"
        drv_c.write_text(SFI_DRIVER_C)
        subprocess.run(
            ["gcc", "-O2", str(drv_c), str(nat_o), str(sfi_o_path), "-o", str(drv_bin)],
            check=True,
            cwd=td,
        )
        bench_out = subprocess.run([str(drv_bin)], capture_output=True, text=True, check=True, cwd=td).stdout
        bench_res = json.loads(bench_out)

        assert bench_res["outputs_equal"] is True
        assert bench_res["canary_smashed_ret"] == "0xbadca028dead0001"
        assert bench_res["canary_forge_sig"] == 11  # SIGSEGV
        assert bench_res["canary_forge_si_code"] == 2  # SEGV_ACCERR
        assert bench_res["canary_ref_intact"] is True

        # 4. Also verify fail-closed rejection in `sfi_gcc_rewriter_v2.py` on rogue `%fs:0x30`, `%gs:0x0`, `(%edi)`, `pushw`
        rejected_inputs = {}
        for bad_name, bad_line in [
            ("rogue_fs", "movq %fs:48, %rax"),
            ("rogue_gs", "movq %gs:0, %rax"),
            ("addr32_mnem", "addr32 movq (%rdi), %rax"),
            ("addr32_sib", "movq (%edi,%eax,8), %rax"),
            ("op16_pushw", "pushw %ax"),
        ]:
            try:
                rw2.rewrite_gcc_att_to_sfi_v2(f".text\nfoo:\n    {bad_line}\n    ret\n")
                raise AssertionError(f"expected {bad_name} to fail closed")
            except ValueError as exc:
                rejected_inputs[bad_name] = str(exc)

        # 5. Extract real `.o` `.text` bytes for `gcc 15.2.0 -O2 -fstack-protector-strong` and `rustc +nightly -Z stack-protector=all`
        gcc_sp_c = td / "gcc_lift_sp.c"
        gcc_sp_o = td / "gcc_lift_sp.o"
        gcc_sp_c.write_text(GCC_LIFT_SPECIMEN_C)
        subprocess.run(
            ["gcc", "-O2", "-fstack-protector-all", "-fcf-protection=none", "-c", str(gcc_sp_c), "-o", str(gcc_sp_o)],
            check=True,
            cwd=td,
        )
        gcc_sp_bytes = extract_section_bytes(gcc_sp_o, ".text", td)

        rs_sp_src = td / "rust_lift_sp.rs"
        rs_sp_o = td / "rust_lift_sp.o"
        rs_sp_src.write_text(RUST_LIFT_SPECIMEN_RS)
        subprocess.run(
            [
                "rustc", "+nightly", "--crate-type=lib", "--emit=obj",
                "-C", "opt-level=2", "-Z", "stack-protector=all",
                "-Z", "allow-partial-mitigations=stack-protector",
                str(rs_sp_src), "-o", str(rs_sp_o),
            ],
            check=True,
            cwd=td,
        )
        rs_sp_bytes = extract_section_bytes(rs_sp_o, ".text.rust_unexposed_canary", td)

        final_doc = {
            "silicon_prefix_and_escape_probes": silicon_res,
            "disassembler_0x66_branch_desync": disasm_66,
            "sfi_gcc_rewriter_v2_benchmark_and_canary": {
                **bench_res,
                "untrusted_bundle_relocations": len(untrusted_relocs),
                "sfi_v2_canary_text_sha256": hashlib.sha256(sfi_text_bytes).hexdigest(),
                "sfi_v2_canary_text_hex_2048b": sfi_text_bytes.hex(),
                "rewriter_v2_fail_closed_rejections": rejected_inputs,
            },
            "compiler_stack_protector_obj_specimens": {
                "gcc_15_2_0_hash2_canary": {
                    "len_bytes": len(gcc_sp_bytes),
                    "sha256": hashlib.sha256(gcc_sp_bytes).hexdigest(),
                    "hex_bytes": gcc_sp_bytes.hex(),
                },
                "rustc_nightly_unexposed_canary": {
                    "len_bytes": len(rs_sp_bytes),
                    "sha256": hashlib.sha256(rs_sp_bytes).hexdigest(),
                    "hex_bytes": rs_sp_bytes.hex(),
                },
            },
        }
        out_json.write_text(json.dumps(final_doc, indent=2, sort_keys=True) + "\n")
        print("ALL_PREFIX_SFI_ESCAPE_AND_REWRITER_V2_CHECKS_PASSED")


if __name__ == "__main__":
    main()
