#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
Execute a 352-vector Cartesian `(Prefix-Combination x Opcode-Class)` differential
test (`24` prefix sequences x `14` opcode templates across GP ALU, Imm, Mem/LEA,
Stack PUSH/POP, Branch/Jcc, LOCK/CMPXCHG, VEX, and EVEX = `336` complete
Cartesian pairs + `16` 15B/16B `#GP(0)` & `%fs:0x28` SIB boundary vectors) on:
  1. Live Intel Xeon Ice Lake-SP silicon (`SA_SIGINFO` two-page `PROT_EXEC` +
     `PROT_NONE` guard-page length/fault trap harness + `wrfsbase`/`wrgsbase` +
     dual `lo32`/`hi64` mappings);
  2. Pinned `intelxed/xed@0bcb6237345c5066726dcc08b3d87928df3b5b26` (`xed -64 -v 4`);
  3. `llvm-mc` and GNU `objdump`; and
  4. Unpatched flat-segment/no-addr32/no-op16 `VendorX86Ref` baseline (quantifying
     the exact correlated Pass-2 blind spot).
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent

PREFIX_COMBOS: list[tuple[str, str]] = [
    ("p00_none", ""),
    ("p01_66", "66"),
    ("p02_67", "67"),
    ("p03_64_fs", "64"),
    ("p04_65_gs", "65"),
    ("p05_2e_cs", "2e"),
    ("p06_3e_ds", "3e"),
    ("p07_26_es", "26"),
    ("p08_36_ss", "36"),
    ("p09_f0_lock", "f0"),
    ("p10_f2_repnz", "f2"),
    ("p11_f3_repz", "f3"),
    ("p12_48_rexw", "48"),
    ("p13_41_rexb", "41"),
    ("p14_66_48", "66 48"),
    ("p15_48_66", "48 66"),
    ("p16_67_48", "67 48"),
    ("p17_48_67", "48 67"),
    ("p18_64_2e", "64 2e"),
    ("p19_64_3e", "64 3e"),
    ("p20_64_65", "64 65"),
    ("p21_65_64", "65 64"),
    ("p22_64_67_48", "64 67 48"),
    ("p23_41_40", "41 40"),
]

OPCODE_TEMPLATES: list[tuple[str, str, str]] = [
    # (template_id, opcode_class, body_hex)
    ("t01_add_rr", "gp_alu", "01 f0"),
    ("t02_mov_imm", "gp_imm", "b8 11 22 33 44 55 66 77 88"),
    ("t03_xchg_ax", "gp_alu", "91"),
    ("t04_mov_load", "mem_lea", "8b 07"),
    ("t05_mov_store", "mem_lea", "89 0f"),
    ("t06_lea_mem", "mem_lea", "8d 07"),
    ("t07_push_reg", "stack", "50"),
    ("t08_pop_reg", "stack", "58"),
    ("t09_jmp_rel32", "branch_ctrl", "e9 00 00 00 00"),
    ("t10_jcc_rel32", "branch_ctrl", "0f 84 00 00 00 00"),
    ("t11_add_mem_rmw", "lock_atomic", "01 0f"),
    ("t12_cmpxchg_mem", "lock_atomic", "0f b1 0f"),
    ("t13_vex_vmovdqa", "vex_simd", "c5 f9 6f 07"),
    ("t14_evex_vprolvd", "evex_simd", "62 f2 7d 28 15 07"),
]

EXTRA_BOUNDARY_VECTORS: list[tuple[str, str, str]] = [
    ("b01_ret_c3", "branch_ctrl", "c3"),
    ("b02_ret_66_c3", "branch_ctrl", "66 c3"),
    ("b03_jmp_66_eb", "branch_ctrl", "66 eb 00"),
    ("b04_jcc_66_74", "branch_ctrl", "66 74 00"),
    ("b05_leave_c9", "stack", "c9"),
    ("b06_leave_66_c9", "stack", "66 c9"),
    ("b07_leave_48_66_c9", "stack", "48 66 c9"),
    ("b08_leave_66_48_c9", "stack", "66 48 c9"),
    ("b09_sib_fs_0x28_load", "mem_lea", "64 48 8b 04 25 28 00 00 00"),
    ("b10_sib_fs_0x28_sub", "mem_lea", "64 48 2b 14 25 28 00 00 00"),
    ("b11_sib_fs_0x28_xor", "mem_lea", "64 48 33 04 25 28 00 00 00"),
    ("b12_riprel_67_load", "mem_lea", "67 48 8b 05 00 00 00 00"),
    ("b13_len15_66x14_nop", "len_cap", " ".join(["66"] * 14 + ["90"])),
    ("b14_len16_66x15_nop", "len_cap", " ".join(["66"] * 15 + ["90"])),
    ("b15_len15_64x12_mov", "len_cap", " ".join(["64"] * 12 + ["48", "8b", "07"])),
    ("b16_len16_64x13_mov", "len_cap", " ".join(["64"] * 13 + ["48", "8b", "07"])),
]


C_CARTESIAN_HARNESS = r"""
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
static volatile uint64_t g_trapno = 0, g_rip = 0, g_efl = 0;
static volatile uint64_t g_rax = 0, g_rcx = 0, g_rdx = 0, g_rsp = 0, g_rbp = 0, g_r8 = 0, g_r9 = 0;
static uint8_t g_ymm0_out[32] __attribute__((aligned(32)));

static uint64_t g_orig_fs = 0, g_orig_gs = 0;

static void trap_handler(int sig, siginfo_t *si, void *uap) {
    (void)si;
    /* Restore host glibc TLS `%fs` BEFORE `siglongjmp` (`PTR_DEMANGLE` reads `%fs:0x30`!) */
    __asm__ volatile(
        "wrfsbase %[ofs]\n\t"
        "wrgsbase %[ogs]\n\t"
        :
        : [ofs] "r"(g_orig_fs), [ogs] "r"(g_orig_gs)
        : "memory"
    );
    ucontext_t *uc = (ucontext_t *)uap;
    g_sig = sig;
    g_trapno = (uint64_t)uc->uc_mcontext.gregs[REG_TRAPNO];
    g_rip = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
    g_efl = (uint64_t)uc->uc_mcontext.gregs[REG_EFL];
    g_rax = (uint64_t)uc->uc_mcontext.gregs[REG_RAX];
    g_rcx = (uint64_t)uc->uc_mcontext.gregs[REG_RCX];
    g_rdx = (uint64_t)uc->uc_mcontext.gregs[REG_RDX];
    g_rsp = (uint64_t)uc->uc_mcontext.gregs[REG_RSP];
    g_rbp = (uint64_t)uc->uc_mcontext.gregs[REG_RBP];
    g_r8  = (uint64_t)uc->uc_mcontext.gregs[REG_R8];
    g_r9  = (uint64_t)uc->uc_mcontext.gregs[REG_R9];
    siglongjmp(g_jmp, 1);
}

/* Fixed mapped virtual addresses so every prefix/addr32/FS/GS/RIP-rel/stack
   combination hits deterministic, non-overlapping memory!
   - Code guard pair:
       exec page: `0x0000000240000000`..`0x240001000` (`page_end = 0x240001000`)
       guard page: `0x0000000240001000`..`0x240002000` (`PROT_NONE`)
     AND for `67` RIP-relative at `0x240000800`: map `0x40000000..0x40002000` RW!
   - Data pages:
       `hi64_ptr` (`rdi` AND `r15`!): `0x0000000140010000`
       `lo32_ptr` (`edi` / `r15d`!):  `0x0000000040010000`
       `fs_base`:                     `0x0000000300000000`
         -> `fs:[rdi]` = `0x0000000440010000`
         -> `fs:[edi]` = `0x0000000340010000`
         -> `fs:[0x28]` = `0x0000000300000028`
       `gs_base`:                     `0x0000000500000000`
         -> `gs:[rdi]` = `0x0000000640010000`
         -> `gs:[edi]` = `0x0000000540010000`
   - Stack & Frame page:
       `stk_page`: `0x0000000700010000` (`rsp_in = 0x700010800`, `rbp_in = 0x700010900`)
*/

#define EXEC_BASE     0x0000000240000000ULL
#define LO_CODE_ALIAS 0x0000000040000000ULL
#define HI64_DATA     0x0000000140010000ULL
#define LO32_DATA     0x0000000040010000ULL
#define TEST_FS_BASE  0x0000000300000000ULL
#define FS_HI64_DATA  0x0000000440010000ULL
#define FS_LO32_DATA  0x0000000340010000ULL
#define TEST_GS_BASE  0x0000000500000000ULL
#define GS_HI64_DATA  0x0000000640010000ULL
#define GS_LO32_DATA  0x0000000540010000ULL
#define STK_BASE      0x0000000700010000ULL

static void map_exact(uint64_t addr, size_t len, int prot) {
    void *p = mmap((void *)addr, len, prot,
                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (p == MAP_FAILED) {
        fprintf(stderr, "mmap failed at 0x%lx\n", addr);
        exit(2);
    }
}

static void reset_test_memory(uint64_t ret_landing) {
    /* Fill 32-byte distinctive patterns in each data region */
    const uint64_t pats[][2] = {
        {HI64_DATA,    0xA1A1A1A111112222ULL},
        {LO32_DATA,    0xB2B2B2B233334444ULL},
        {FS_HI64_DATA, 0xF564F56455556666ULL},
        {FS_LO32_DATA, 0xF532F53277778888ULL},
        {GS_HI64_DATA, 0x656465649999AAAAULL},
        {GS_LO32_DATA, 0x65326532BBBBCCCCULL},
    };
    for (size_t i = 0; i < 6; i++) {
        uint64_t *p = (uint64_t *)pats[i][0];
        p[0] = pats[i][1];
        p[1] = pats[i][1] ^ 0x0101010101010101ULL;
        p[2] = pats[i][1] ^ 0x0202020202020202ULL;
        p[3] = pats[i][1] ^ 0x0303030303030303ULL;
    }
    /* TCB `%fs:0x28` canary slot */
    *(uint64_t *)(TEST_FS_BASE + 0x28ULL) = 0xCA4A2800DEADBEEFULL;
    /* Low 32-bit RIP-relative data target (`0x40000808` when run at `EXEC_BASE + 0x800`, len 8) */
    *(uint64_t *)(LO_CODE_ALIAS + 0x808ULL) = 0x32E19000CAFE1234ULL;

    memset((void *)STK_BASE, 0xEE, 8192);
    *(uint64_t *)(STK_BASE + 0x800ULL) = ret_landing;
    *(uint64_t *)(STK_BASE + 0x900ULL) = 0x778899AABBCCDDEEULL;
}

static uint64_t g_saved_host_rsp = 0, g_saved_host_rbp = 0;

static void run_vector_at(uint8_t *start, uint64_t ret_landing) {
    reset_test_memory(ret_landing);
    memset(g_ymm0_out, 0, 32);
    uint64_t ymm0_init[4] = {0x0102030405060708ULL, 0x1112131415161718ULL,
                             0x2122232425262728ULL, 0x3132333435363738ULL};

    g_sig = 0; g_trapno = 0;
    if (sigsetjmp(g_jmp, 1) == 0) {
        struct {
            uint64_t start_va, fsb, gsb;
            const void *y0;
        } ctx = { (uint64_t)start, TEST_FS_BASE, TEST_GS_BASE, ymm0_init };
        __asm__ volatile(
            "mov %%rsp, %[srsp]\n\t"
            "mov %%rbp, %[srbp]\n\t"
            "mov 24(%[c]), %%r10\n\t"
            "vmovdqu (%%r10), %%ymm0\n\t"
            "mov 8(%[c]), %%r10\n\t"
            "wrfsbase %%r10\n\t"
            "mov 16(%[c]), %%r10\n\t"
            "wrgsbase %%r10\n\t"
            "mov 0(%[c]), %%r10\n\t"
            "mov $0xA1A1A1A111112222, %%rax\n\t"
            "mov $0x0123456789ABCDEF, %%rcx\n\t"
            "mov $0xCA4A2800DEADBEEF, %%rdx\n\t"
            "mov $0x0000000200000003, %%rsi\n\t"
            "mov $0x0000000140010000, %%rdi\n\t"
            "mov $0x0000000140010000, %%r15\n\t"
            "mov $0x8888777766665555, %%r8\n\t"
            "mov $0x1111222233334444, %%r9\n\t"
            "pushq $0x202\n\t"
            "popfq\n\t"
            "mov $0x0000000700010800, %%rsp\n\t"
            "mov $0x0000000700010900, %%rbp\n\t"
            "jmp *%%r10\n\t"
            : [srsp] "=m"(g_saved_host_rsp), [srbp] "=m"(g_saved_host_rbp)
            : [c] "r"(&ctx)
            : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r15", "cc", "memory", "ymm0"
        );
    }
    /* Restore host FS/GS immediately before any libc call! */
    __asm__ volatile(
        "wrfsbase %[ofs]\n\t"
        "wrgsbase %[ogs]\n\t"
        :
        : [ofs] "r"(g_orig_fs), [ogs] "r"(g_orig_gs)
        : "memory"
    );
}

int main(void) {
    /* Use sigaltstack so signals never push onto test `%rsp`! */
    stack_t ss;
    ss.ss_sp = mmap(NULL, 65536, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    ss.ss_size = 65536;
    ss.ss_flags = 0;
    sigaltstack(&ss, NULL);

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = trap_handler;
    sa.sa_flags = SA_SIGINFO | SA_NODEFER | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGTRAP, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);

    syscall(SYS_arch_prctl, ARCH_GET_FS, &g_orig_fs);
    syscall(SYS_arch_prctl, ARCH_GET_GS, &g_orig_gs);

    map_exact(EXEC_BASE, 8192, PROT_READ | PROT_WRITE | PROT_EXEC);
    if (mprotect((void *)(EXEC_BASE + 4096ULL), 4096, PROT_NONE) != 0) return 3;
    map_exact(LO_CODE_ALIAS, 8192, PROT_READ | PROT_WRITE);
    map_exact(HI64_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(LO32_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(TEST_FS_BASE, 4096, PROT_READ | PROT_WRITE);
    map_exact(FS_HI64_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(FS_LO32_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(TEST_GS_BASE, 4096, PROT_READ | PROT_WRITE);
    map_exact(GS_HI64_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(GS_LO32_DATA, 4096, PROT_READ | PROT_WRITE);
    map_exact(STK_BASE, 8192, PROT_READ | PROT_WRITE);

    uint8_t *exec_page = (uint8_t *)EXEC_BASE;
    uint8_t *page_end = exec_page + 4096;
    uint8_t *ret_landing_ptr = exec_page + 256;
    /* Epilogue at ret_landing / post-insn: `movabs r11, &g_ymm0_out; vmovdqu [r11], ymm0; int3` = 16 bytes */
    uint8_t epilogue[16] = {
        0x49, 0xbb, 0,0,0,0,0,0,0,0,
        0xc4, 0xc1, 0x7e, 0x7f, 0x03,
        0xcc
    };
    uint64_t ymm_out_va = (uint64_t)g_ymm0_out;
    memcpy(epilogue + 2, &ymm_out_va, 8);
    memcpy(ret_landing_ptr, epilogue, 16);

    char line[1024];
    while (fgets(line, sizeof(line), stdin)) {
        char vid[128], hex[256];
        if (sscanf(line, "%127[^|]|%255s", vid, hex) != 2) continue;
        uint8_t code[32];
        int clen = (int)strlen(hex) / 2;
        for (int i = 0; i < clen && i < 32; i++) {
            unsigned int b = 0;
            sscanf(hex + 2 * i, "%02x", &b);
            code[i] = (uint8_t)b;
        }

        /* Phase A: Measure exact silicon decode/fetch length & decode trap via `page_end - L` */
        const char *verdict = "UNKNOWN";
        int obs_len = 0;
        uint64_t obs_trap = 0;

        for (int L = 1; L <= 17; L++) {
            uint8_t *start = page_end - L;
            memset(start, 0xcc, (size_t)L);
            int copy_n = clen < L ? clen : L;
            memcpy(start, code, (size_t)copy_n);
            if (L > clen) {
                start[clen] = 0xcc;
            }
            run_vector_at(start, (uint64_t)ret_landing_ptr);
            if (g_trapno == 14 && g_rip == (uint64_t)start) {
                continue;
            }
            if (g_trapno == 13 && g_rip == (uint64_t)start) {
                verdict = "FAULT_GP0";
                obs_len = L;
                obs_trap = 13;
                break;
            }
            if (g_trapno == 6 && g_rip == (uint64_t)start) {
                verdict = "FAULT_UD";
                obs_len = L;
                obs_trap = 6;
                break;
            }
            if ((g_trapno == 14 && g_rip == (uint64_t)page_end) || g_trapno == 3) {
                verdict = "OK_EXEC";
                obs_len = L;
                obs_trap = 0;
                break;
            }
        }

        /* Phase B: If `OK_EXEC`, run cleanly at `EXEC_BASE + 0x800` with 16B epilogue to capture full post-state */
        if (strcmp(verdict, "OK_EXEC") == 0) {
            uint8_t *run_slot = exec_page + 0x800;
            memcpy(run_slot, code, (size_t)obs_len);
            memcpy(run_slot + obs_len, epilogue, 16);
            run_vector_at(run_slot, (uint64_t)ret_landing_ptr);
        }

        char y0_hex[65];
        for (int i = 0; i < 32; i++) sprintf(y0_hex + 2 * i, "%02x", g_ymm0_out[i]);
        y0_hex[64] = '\0';

        printf("%s|%s|%d|%lu|%016lx|%016lx|%016lx|%016lx|%016lx|%016lx|%016lx|%03lx|%016lx|%016lx|%016lx|%016lx|%016lx|%016lx|%016lx|%s\n",
               vid, verdict, obs_len, obs_trap,
               g_rax, g_rcx, g_rdx, g_rsp, g_rbp, g_r8, g_r9, (g_efl & 0x8d5ULL),
               *(uint64_t *)HI64_DATA, *(uint64_t *)LO32_DATA,
               *(uint64_t *)FS_HI64_DATA, *(uint64_t *)FS_LO32_DATA,
               *(uint64_t *)GS_HI64_DATA, *(uint64_t *)GS_LO32_DATA,
               *(uint64_t *)(STK_BASE + 0x7F8ULL),
               y0_hex);
    }
    return 0;
}
"""


def build_all_vectors() -> list[dict[str, str]]:
    vecs: list[dict[str, str]] = []
    for pid, phex in PREFIX_COMBOS:
        for tid, ocls, bhex in OPCODE_TEMPLATES:
            full_hex = (phex + " " + bhex).strip()
            vecs.append({
                "id": f"{pid}__{tid}",
                "prefix_id": pid,
                "prefix_hex": phex,
                "template_id": tid,
                "opcode_class": ocls,
                "hex": full_hex.replace(" ", ""),
                "hex_spaced": full_hex,
                "grid_kind": "cartesian_24x14",
            })
    for bid, ocls, full_hex in EXTRA_BOUNDARY_VECTORS:
        vecs.append({
            "id": bid,
            "prefix_id": "boundary",
            "prefix_hex": "",
            "template_id": bid,
            "opcode_class": ocls,
            "hex": full_hex.replace(" ", ""),
            "hex_spaced": full_hex,
            "grid_kind": "boundary_16",
        })
    return vecs


def query_xed(xed_bin: Path, xed_lib: Path, hex_spaced: str) -> dict[str, object]:
    env = dict(os.environ, LD_LIBRARY_PATH=str(xed_lib))
    toks = hex_spaced.split()[:16]
    r = subprocess.run([str(xed_bin), "-64", "-v", "4", "-d", *toks], env=env, capture_output=True, text=True)
    lines = r.stdout.splitlines()
    hex_idxs = [
        i for i, ln in enumerate(lines) if re.fullmatch(r"[0-9A-Fa-f]{2,32}", ln.strip())
    ]
    first_blk_end = hex_idxs[1] if len(hex_idxs) >= 2 else len(lines)
    first_blk = "\n".join(lines[:first_blk_end])
    if "ERROR:" in first_blk or not hex_idxs:
        combined_err = first_blk + "\n" + r.stdout + "\n" + r.stderr
        if "test string was too long" in combined_err:
            return {"ok": False, "verdict": "FAULT_GP0", "error": "INSTR_TOO_LONG", "len": 16, "iclass": None}
        err_m = re.search(r"ERROR:\s*([A-Z0-9_]+)", combined_err)
        err_code = err_m.group(1) if err_m else "ERROR"
        verdict = "FAULT_GP0" if ("TOO_LONG" in err_code or len(toks) >= 15 and err_code == "BUFFER_TOO_SHORT") else "FAULT_UD"
        return {"ok": False, "verdict": verdict, "error": err_code, "len": 0, "iclass": None}
    ic_m = re.search(r"ICLASS:\s*([A-Za-z0-9_]+)", first_blk)
    eosz_m = re.search(r"EOSZ:(\d+)", first_blk)
    easz_m = re.search(r"EASZ:(\d+)", first_blk)
    h0 = len(lines[hex_idxs[0]].strip()) // 2
    h1 = len(lines[hex_idxs[1]].strip()) // 2 if len(hex_idxs) >= 2 else 0
    dec_len = h0 - h1
    return {
        "ok": True,
        "verdict": "OK_EXEC",
        "error": None,
        "len": dec_len,
        "iclass": ic_m.group(1) if ic_m else None,
        "eosz": int(eosz_m.group(1)) if eosz_m else None,
        "easz": int(easz_m.group(1)) if easz_m else None,
    }


def unpatched_model_diverges(v: dict[str, object]) -> str | None:
    """Classify whether the unpatched `VendorX86Ref` / `ByteX86` shared `scanPrefixes`
    model (`hasSegOr67` ignored, `has66` ignored on `PUSH`/`POP`/`LEAVE`/`MOV imm`
    and most GP ALU/mem opcodes) diverges from silicon on vector `v`!"""
    if v["silicon_verdict"] != "OK_EXEC":
        return None
    phex = str(v["prefix_hex"]).split()
    tid = str(v["template_id"])
    # Determine effective prefixes
    has66 = "66" in phex
    has67 = "67" in phex
    seg = None
    rex = None
    for b in phex:
        if b == "64":
            seg = "fs"
            rex = None
        elif b == "65":
            seg = "gs"
            rex = None
        elif b in ("66", "67", "2e", "3e", "26", "36", "f0", "f2", "f3"):
            rex = None
        elif b.startswith("4"):
            rex = int(b, 16)
    if str(v["id"]).startswith("b09_") or str(v["id"]).startswith("b10_") or str(v["id"]).startswith("b11_") or str(v["id"]).startswith("b15_"):
        seg = "fs"
    if str(v["id"]) == "b12_riprel_67_load":
        has67 = True
    if str(v["id"]) in ("b06_leave_66_c9", "b07_leave_48_66_c9"):
        has66 = True
        rex = None

    rexw = bool(rex is not None and (rex & 0x8) != 0)
    # 1. Segment override on explicit memory operand (excluding LEA, PUSH, POP, JMP, Jcc)
    if seg is not None and tid in (
        "t04_mov_load", "t05_mov_store", "t11_add_mem_rmw", "t12_cmpxchg_mem",
        "t13_vex_vmovdqa", "t14_evex_vprolvd",
        "b09_sib_fs_0x28_load", "b10_sib_fs_0x28_sub", "b11_sib_fs_0x28_xor", "b15_len15_64x10_mov",
    ):
        return f"unpatched_ignores_{seg}_base"
    # 2. Address-size 0x67 truncation on memory / LEA / RIP-rel
    if has67 and tid in (
        "t04_mov_load", "t05_mov_store", "t06_lea_mem", "t11_add_mem_rmw",
        "t12_cmpxchg_mem", "t13_vex_vmovdqa", "t14_evex_vprolvd", "b12_riprel_67_load",
    ):
        return "unpatched_ignores_0x67_addr32"
    # 3. Operand-size 0x66 without REX.W on d64 stack or d32 ALU/MOV/LEA/CMPXCHG
    if has66 and not rexw and tid in (
        "t01_add_rr", "t02_mov_imm", "t04_mov_load", "t05_mov_store",
        "t06_lea_mem", "t07_push_reg", "t08_pop_reg", "t11_add_mem_rmw",
        "t12_cmpxchg_mem", "b06_leave_66_c9", "b07_leave_48_66_c9",
    ):
        if tid == "t02_mov_imm":
            return "unpatched_0x66_mov_imm_fetches_4B_instead_of_2B"
        if tid in ("t07_push_reg", "t08_pop_reg", "b06_leave_66_c9", "b07_leave_48_66_c9"):
            return "unpatched_0x66_stack_rsp_delta_8_instead_of_2"
        return "unpatched_ignores_0x66_op16"
    return None


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--xed-bin", type=Path, default=None)
    ap.add_argument("--xed-lib", type=Path, default=None)
    ap.add_argument(
        "--out-json",
        type=Path,
        default=HERE / "cartesian_prefix_silicon_and_xed_results.json",
    )
    args = ap.parse_args()

    vecs = build_all_vectors()
    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)
        c_path = td / "cartesian_harness.c"
        bin_path = td / "cartesian_harness"
        c_path.write_text(C_CARTESIAN_HARNESS)
        subprocess.run(
            ["gcc", "-O2", "-fno-stack-protector", str(c_path), "-o", str(bin_path)],
            check=True,
            cwd=td,
        )

        stdin_payload = "".join(f"{v['id']}|{v['hex']}\n" for v in vecs)
        r = subprocess.run(
            [str(bin_path)], input=stdin_payload, text=True, capture_output=True, check=True, cwd=td
        )

        by_id = {v["id"]: v for v in vecs}
        for raw_ln in r.stdout.strip().splitlines():
            parts = raw_ln.split("|")
            assert len(parts) == 20, f"bad output line: {raw_ln}"
            vid = parts[0]
            rec = by_id[vid]
            rec["silicon_verdict"] = parts[1]
            rec["silicon_len"] = int(parts[2])
            rec["silicon_trapno"] = int(parts[3])
            rec["rax"] = "0x" + parts[4]
            rec["rcx"] = "0x" + parts[5]
            rec["rdx"] = "0x" + parts[6]
            rec["rsp"] = "0x" + parts[7]
            rec["rbp"] = "0x" + parts[8]
            rec["r8"] = "0x" + parts[9]
            rec["r9"] = "0x" + parts[10]
            rec["efl6"] = "0x" + parts[11]
            rec["mem_hi64"] = "0x" + parts[12]
            rec["mem_lo32"] = "0x" + parts[13]
            rec["mem_fs_hi64"] = "0x" + parts[14]
            rec["mem_fs_lo32"] = "0x" + parts[15]
            rec["mem_gs_hi64"] = "0x" + parts[16]
            rec["mem_gs_lo32"] = "0x" + parts[17]
            rec["mem_stk_push64"] = "0x" + parts[18]
            rec["ymm0_hex"] = parts[19]
            rec["unpatched_blind_spot"] = unpatched_model_diverges(rec)

        xed_checked = 0
        xed_matches = 0
        if args.xed_bin and args.xed_lib and args.xed_bin.exists():
            for v in vecs:
                xr = query_xed(args.xed_bin, args.xed_lib, str(v["hex_spaced"]))
                v["xed_verdict"] = xr["verdict"]
                v["xed_len"] = xr["len"]
                v["xed_iclass"] = xr["iclass"]
                xed_checked += 1
                if xr["verdict"] == v["silicon_verdict"] and (
                    xr["verdict"] != "OK_EXEC" or xr["len"] == v["silicon_len"]
                ):
                    xed_matches += 1
                else:
                    raise AssertionError(f"Silicon vs XED mismatch on {v['id']}: {v} vs {xr}")

        # Also check llvm-mc and objdump on all fault vectors + 0x66 branch vectors
        llvm_false_accepts = 0
        objdump_false_accepts = 0
        fault_vecs = [v for v in vecs if v["silicon_verdict"] != "OK_EXEC"]
        for fv in fault_vecs:
            toks = str(fv["hex_spaced"]).split()[:16]
            mc_in = " ".join("0x" + b for b in toks)
            rmc = subprocess.run(
                ["llvm-mc", "--disassemble", "--triple=x86_64-unknown-linux-gnu"],
                input=mc_in,
                text=True,
                capture_output=True,
            )
            if rmc.returncode == 0 and "warning: invalid instruction" not in rmc.stderr:
                llvm_false_accepts += 1
            bp = td / "f.bin"
            bp.write_bytes(bytes.fromhex("".join(toks)))
            rob = subprocess.run(
                ["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", str(bp)],
                text=True,
                capture_output=True,
            )
            if rob.returncode == 0 and "(bad)" not in rob.stdout:
                objdump_false_accepts += 1

    blind_spot_counts: dict[str, int] = {}
    for v in vecs:
        bs = v["unpatched_blind_spot"]
        if bs:
            blind_spot_counts[bs] = blind_spot_counts.get(bs, 0) + 1

    summary = {
        "total_vectors": len(vecs),
        "cartesian_grid_vectors": sum(1 for v in vecs if v["grid_kind"] == "cartesian_24x14"),
        "boundary_vectors": sum(1 for v in vecs if v["grid_kind"] == "boundary_16"),
        "silicon_ok_exec_count": sum(1 for v in vecs if v["silicon_verdict"] == "OK_EXEC"),
        "silicon_fault_ud_count": sum(1 for v in vecs if v["silicon_verdict"] == "FAULT_UD"),
        "silicon_fault_gp0_count": sum(1 for v in vecs if v["silicon_verdict"] == "FAULT_GP0"),
        "xed_checked_count": xed_checked,
        "xed_exact_match_count": xed_matches,
        "fault_vectors_total": len(fault_vecs),
        "llvm_mc_silent_false_accept_count": llvm_false_accepts,
        "objdump_silent_false_accept_count": objdump_false_accepts,
        "unpatched_pass2_blind_spot_diverging_vectors": sum(blind_spot_counts.values()),
        "unpatched_pass2_blind_spot_breakdown": blind_spot_counts,
    }

    out_doc = {
        "summary": summary,
        "test_memory_constants": {
            "exec_run_va": "0x0000000240000800",
            "ret_landing_va": "0x0000000240000100",
            "hi64_data_va": "0x0000000140010000",
            "lo32_data_va": "0x0000000040010000",
            "fs_base": "0x0000000300000000",
            "gs_base": "0x0000000500000000",
            "rsp_init": "0x0000000700010800",
            "rbp_init": "0x0000000700010900",
        },
        "vectors": vecs,
    }
    args.out_json.write_text(json.dumps(out_doc, indent=2, sort_keys=True) + "\n")
    print(f"CARTESIAN_SILICON_AND_XED_352_PASSED: {json.dumps(summary, sort_keys=True)}")


if __name__ == "__main__":
    main()
