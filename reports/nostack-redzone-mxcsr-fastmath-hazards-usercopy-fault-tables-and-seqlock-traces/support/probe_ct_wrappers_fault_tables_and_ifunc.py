#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Standalone empirical probes for Seams 3 & 4:
1. `core::hint::black_box` lowering from `Runtime(PostCleanup)` MIR through optimized MIR and
   LLVM IR to x86-64 machine code across `rustc 1.99.1` and `1.102.0-nightly`.
2. Non-naked constant-time wrapper leaks around constant-time `asm!` (`black_box` + `&&`
   branch induction, LLVM `X86CmovConversion` loop branch conversion, and red-zone secret
   spilling) vs `#[unsafe(naked)]` `naked_asm!`.
3. Live Linux x86-64 `usercopy` PC-range fault overlays (both Fuchsia Starnix `[start, end)`
   sentinel bounds and Linux kernel `.pushsection __ex_table` PC-relative entries) across
   a `PROT_NONE` page boundary via `SA_SIGINFO` `ucontext_t` `REG_RIP` fixup, demonstrating
   partial destination writes prior to synchronous fault.
4. `gcc 15.2.0` `__attribute__((target_clones("default","avx2","avx512f")))` `STT_GNU_IFUNC` +
   `R_X86_64_IRELATIVE` + `__cpu_indicator_init` `xgetbv` (`XCR0`) OS-XSAVE gating.
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys
import tempfile


TOOLCHAINS = [
    ("1.99.1", "+1.99.1"),
    ("1.102.0-nightly", "+nightly"),
]


def run_cmd(cmd: list[str], cwd: pathlib.Path | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    cp = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if check and cp.returncode != 0:
        raise RuntimeError(f"Command {cmd} failed (rc={cp.returncode}):\nSTDOUT:\n{cp.stdout}\nSTDERR:\n{cp.stderr}")
    return cp


def extract_asm_fn(asm_text: str, sym_name: str) -> str:
    m = re.search(rf"(^{re.escape(sym_name)}:\n(?:.*\n){{1,60}}?)\s*\.size\s+{re.escape(sym_name)},", asm_text, re.MULTILINE)
    return m.group(1).strip() if m else "NOT_FOUND"


def count_cond_jumps(fn_asm: str) -> list[str]:
    jumps = []
    for line in fn_asm.splitlines():
        s = line.strip()
        if not s or s.startswith(".") or s.startswith("#") or s.endswith(":"):
            continue
        mnem = s.split()[0]
        if mnem.startswith("j") and mnem != "jmp" and mnem != "jmpq":
            jumps.append(s)
    return jumps


def probe_3_ct_wrappers_and_black_box() -> dict:
    src_code = r'''
use core::arch::{asm, naked_asm};
use core::hint::black_box;

#[unsafe(no_mangle)]
#[inline(never)]
pub fn inspect_black_box_u8(secret: u8) -> u8 {
    black_box(secret)
}

// 1. Plain short-circuit `&&` without black_box: LLVM fuses `c1 & c2` branchlessly!
#[unsafe(no_mangle)]
#[inline(never)]
pub fn ct_wrapper_plain_and(c1: bool, c2: bool, a: u64, b: u64) -> u64 {
    let cond = (c1 && c2) as u64;
    let mut out = a;
    unsafe {
        asm!(
            "test {cond}, {cond}",
            "cmovne {out}, {b}",
            cond = in(reg) cond,
            out = inout(reg) out,
            b = in(reg) b,
            options(nomem, nostack),
        );
    }
    out
}

// 2. `black_box(c1) && black_box(c2)` feeding a verified constant-time `asm!` block:
// Because `black_box(c2)` lowers to `asm sideeffect "", "r,~{memory}"`, LLVM is FORBIDDEN
// from executing `black_box(c2)` speculatively when `c1 == false`, forcing a secret-dependent
// `testb` + `je` branch AND two red-zone stack spills `-1(%rsp)` / `-2(%rsp)` OUTSIDE `asm!`!
#[unsafe(no_mangle)]
#[inline(never)]
pub fn ct_wrapper_blackbox_and_leak(c1: bool, c2: bool, a: u64, b: u64) -> u64 {
    let cond = (black_box(c1) && black_box(c2)) as u64;
    let mut out = a;
    unsafe {
        asm!(
            "test {cond}, {cond}",
            "cmovne {out}, {b}",
            cond = in(reg) cond,
            out = inout(reg) out,
            b = in(reg) b,
            options(nomem, nostack),
        );
    }
    out
}

// 3. `subtle::Choice`-style `read_volatile` barrier wrapper: no branch, but spills secret
// choice byte to `-1(%rsp)` in the un-erased red zone!
#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct Choice(u8);

#[inline(never)]
fn volatile_barrier_u8(x: u8) -> u8 {
    unsafe { core::ptr::read_volatile(&x) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn ct_wrapper_volatile_choice(c: Choice, a: u64, b: u64) -> u64 {
    let mask = volatile_barrier_u8(c.0) as u64;
    let mut out = a;
    unsafe {
        asm!(
            "test {m}, {m}",
            "cmovne {out}, {b}",
            m = in(reg) mask,
            out = inout(reg) out,
            b = in(reg) b,
            options(nomem, nostack),
        );
    }
    out
}

// 4. Innermost loop: LLVM `X86CmovConversion` converts high-depth-cost pure-Rust branchless
// select into a secret-dependent `je`/`jne` conditional jump, whereas `asm!` `cmovne` resists it!
#[unsafe(no_mangle)]
#[inline(never)]
pub fn loop_rust_select_cmov_converted(choices: &[u8], a: &[u64], b: &[u64]) -> u64 {
    let n = choices.len().min(a.len()).min(b.len());
    let mut acc = 0u64;
    for i in 0..n {
        let c = choices[i];
        // Expensive latency chain on one arm triggers X86CmovConversion in innermost loop
        let heavy = acc
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add(a[i])
            .rotate_left(17)
            .wrapping_mul(0xbf58_476d_1ce4_e5b9)
            .rotate_right(31)
            .wrapping_mul(0x94d0_49bb_1331_11eb);
        let light = acc.wrapping_add(b[i]);
        acc = if c != 0 { heavy } else { light };
    }
    acc
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn loop_asm_cmov_preserved(choices: &[u8], a: &[u64], b: &[u64]) -> u64 {
    let n = choices.len().min(a.len()).min(b.len());
    let mut acc = 0u64;
    for i in 0..n {
        let c = choices[i] as u64;
        let mut heavy = acc
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add(a[i])
            .rotate_left(17)
            .wrapping_mul(0xbf58_476d_1ce4_e5b9)
            .rotate_right(31)
            .wrapping_mul(0x94d0_49bb_1331_11eb);
        let light = acc.wrapping_add(b[i]);
        unsafe {
            asm!(
                "test {c}, {c}",
                "cmove {h}, {l}",
                c = in(reg) c,
                h = inout(reg) heavy,
                l = in(reg) light,
                options(nomem, nostack),
            );
        }
        acc = heavy;
    }
    acc
}

// 5. Fully `#[unsafe(naked)]` constant-time function: zero prologue, zero stack spills, zero branches.
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ct_select_naked(cond: u64, a: u64, b: u64) -> u64 {
    naked_asm!(
        "mov rax, rsi",
        "test rdi, rdi",
        "cmovne rax, rdx",
        "ret",
    )
}

// Runtime red-zone residue detector: scrubs `[rsp - 32, rsp)` before call, calls target,
// then inspects `[rsp - 32, rsp)` to see if secret `0x5a` leaked onto stack memory!
#[inline(never)]
fn detect_stack_residue_blackbox(secret: u8) -> bool {
    let leaked: u64;
    unsafe {
        asm!(
            "mov qword ptr [rsp - 8], 0",
            "mov qword ptr [rsp - 16], 0",
            "mov qword ptr [rsp - 24], 0",
            "call inspect_black_box_u8",
            // `call` pushed 8-byte return address to `[rsp - 8]`, and inside `inspect_black_box_u8`
            // `black_box` spilled `secret` to `[callee_rsp - 1]` == `[caller_rsp - 9]`!
            "movzx eax, byte ptr [rsp - 9]",
            in("rdi") secret as u64,
            lateout("rax") leaked,
            clobber_abi("C"),
        );
    }
    leaked == (secret as u64)
}

#[inline(never)]
fn detect_stack_residue_naked(secret: u8) -> bool {
    let leaked: u64;
    unsafe {
        asm!(
            "mov qword ptr [rsp - 8], 0",
            "mov qword ptr [rsp - 16], 0",
            "mov qword ptr [rsp - 24], 0",
            "call ct_select_naked",
            "movzx eax, byte ptr [rsp - 9]",
            in("rdi") secret as u64,
            in("rsi") 0x1111u64,
            in("rdx") 0x2222u64,
            lateout("rax") leaked,
            clobber_abi("C"),
        );
    }
    leaked == (secret as u64)
}

fn main() {
    let bb_leaked = detect_stack_residue_blackbox(0x5au8);
    let naked_leaked = detect_stack_residue_naked(0x5au8);
    let r1 = ct_wrapper_plain_and(true, false, 10, 20);
    let r2 = ct_wrapper_blackbox_and_leak(true, true, 10, 20);
    let r3 = unsafe { ct_select_naked(1, 10, 20) };
    println!(
        "{{\"blackbox_redzone_secret_leaked_at_rsp_minus_9\":{},\"naked_redzone_secret_leaked\":{},\"sanity\":[{},{},{}]}}",
        bb_leaked, naked_leaked, r1, r2, r3
    );
}
'''
    results = {}
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)
        src = tdp / "ct_probe.rs"
        src.write_text(src_code)

        # Dump Runtime(PostCleanup) MIR on nightly for `inspect_black_box_u8`
        mir_dump_dir = tdp / "mir_dump"
        mir_dump_dir.mkdir()
        run_cmd([
            "rustc", "+nightly", "--edition=2024", "-C", "opt-level=3",
            f"-Zdump-mir=runtime-post-cleanup",
            f"-Zdump-mir-dir={mir_dump_dir}",
            str(src), "-o", str(tdp / "ct_nightly_mir_bin")
        ])
        post_cleanup_bb = "NOT_FOUND"
        for mf in sorted(mir_dump_dir.glob("*inspect_black_box_u8*runtime-post-cleanup.after.mir")):
            post_cleanup_bb = mf.read_text().strip()
            break
        results["nightly_runtime_post_cleanup_mir_black_box"] = post_cleanup_bb

        for tc_label, tc_arg in TOOLCHAINS:
            bin_p = tdp / f"ct_{tc_label}"
            asm_p = tdp / f"ct_{tc_label}.s"
            ir_p = tdp / f"ct_{tc_label}.ll"
            mir_p = tdp / f"ct_{tc_label}.mir"
            run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", str(src), "-o", str(bin_p)])
            run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", "--emit=asm", str(src), "-o", str(asm_p)])
            run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", "--emit=llvm-ir", str(src), "-o", str(ir_p)])
            run_cmd(["rustc", tc_arg, "--edition=2024", "-C", "opt-level=3", "--emit=mir", str(src), "-o", str(mir_p)])

            rt = json.loads(run_cmd([str(bin_p)]).stdout.strip())
            asm_txt = asm_p.read_text()
            ir_txt = ir_p.read_text()
            mir_txt = mir_p.read_text()

            # Extract optimized MIR for inspect_black_box_u8
            m_mir = re.search(r"(fn inspect_black_box_u8\([^{]*\{\n(?:.*\n){1,20}?^\})", mir_txt, re.MULTILINE)
            opt_mir_bb = m_mir.group(1).strip() if m_mir else "NOT_FOUND"

            # Extract LLVM IR for inspect_black_box_u8
            m_ir = re.search(r"(define [^\n]*@inspect_black_box_u8\([^\n]*\{\n(?:.*\n){1,20}?^\})", ir_txt, re.MULTILINE)
            ir_bb = m_ir.group(1).strip() if m_ir else "NOT_FOUND"

            fns = {}
            for fn_name in [
                "inspect_black_box_u8",
                "ct_wrapper_plain_and",
                "ct_wrapper_blackbox_and_leak",
                "ct_wrapper_volatile_choice",
                "loop_rust_select_cmov_converted",
                "loop_asm_cmov_preserved",
                "ct_select_naked",
            ]:
                body = extract_asm_fn(asm_txt, fn_name)
                fns[fn_name] = {
                    "cond_jumps": count_cond_jumps(body),
                    "has_rsp_mem_access": ("%rsp)" in body),
                    "asm": body,
                }
            results[tc_label] = {
                "runtime": rt,
                "optimized_mir_black_box": opt_mir_bb,
                "llvm_ir_black_box": ir_bb,
                "functions": fns,
            }
    return results


def probe_4_usercopy_fault_tables_and_ifunc() -> dict:
    c_src = r'''
#define _GNU_SOURCE
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>

/* 1. Fuchsia Starnix-style sentinel PC-range usercopy:
 *    Any fault with RIP in [starnix_usercopy_start, starnix_usercopy_end)
 *    is redirected to starnix_usercopy_fault, returning residual uncopied bytes (%rdx).
 */
extern size_t starnix_usercopy(void *dst, const void *src, size_t len);
extern const char starnix_usercopy_start[];
extern const char starnix_usercopy_end[];
extern const char starnix_usercopy_fault[];

__asm__(
    ".text\n"
    ".globl starnix_usercopy\n"
    ".globl starnix_usercopy_start\n"
    ".globl starnix_usercopy_end\n"
    ".globl starnix_usercopy_fault\n"
    ".type starnix_usercopy, @function\n"
    "starnix_usercopy:\n"
    "  testq %rdx, %rdx\n"
    "  jz .Lstarnix_done\n"
    "starnix_usercopy_start:\n"
    ".Lstarnix_loop:\n"
    "  movb (%rsi), %al\n"
    "  movb %al, (%rdi)\n"
    "  incq %rsi\n"
    "  incq %rdi\n"
    "  decq %rdx\n"
    "  jnz .Lstarnix_loop\n"
    "starnix_usercopy_end:\n"
    ".Lstarnix_done:\n"
    "  xorl %eax, %eax\n"
    "  retq\n"
    "starnix_usercopy_fault:\n"
    "  movq %rdx, %rax\n"
    "  retq\n"
    ".size starnix_usercopy, .-starnix_usercopy\n"
);

/* 2. Linux-kernel-style `.pushsection __ex_table` PC-relative fault table:
 *    `rep movsb` updates %rdi, %rsi, %rcx architecturally per byte; on #PF/SIGSEGV,
 *    %rcx holds the exact residual uncopied byte count and dst[0..copied] is already mutated!
 */
struct ex_table_entry {
    int32_t insn;
    int32_t fixup;
    int32_t type;
};

extern const struct ex_table_entry __start___ex_table[];
extern const struct ex_table_entry __stop___ex_table[];
extern size_t extable_rep_usercopy(void *dst, const void *src, size_t len);

__asm__(
    ".text\n"
    ".globl extable_rep_usercopy\n"
    ".type extable_rep_usercopy, @function\n"
    "extable_rep_usercopy:\n"
    "  movq %rdx, %rcx\n"
    "1:\n"
    "  rep movsb\n"
    "  xorl %eax, %eax\n"
    "  retq\n"
    "2:\n"
    "  movq %rcx, %rax\n"
    "  retq\n"
    ".size extable_rep_usercopy, .-extable_rep_usercopy\n"
    ".pushsection __ex_table, \"a\", @progbits\n"
    ".balign 4\n"
    ".long 1b - .\n"
    ".long 2b - .\n"
    ".long 1\n"
    ".popsection\n"
);

static volatile uintptr_t last_fault_rip = 0;
static volatile uintptr_t last_fault_addr = 0;
static volatile int fault_overlay_kind = 0; /* 1 = starnix range, 2 = __ex_table */

static void segv_handler(int sig, siginfo_t *info, void *uctx_void) {
    (void)sig;
    ucontext_t *uc = (ucontext_t *)uctx_void;
    uintptr_t rip = (uintptr_t)uc->uc_mcontext.gregs[REG_RIP];
    last_fault_rip = rip;
    last_fault_addr = (uintptr_t)info->si_addr;

    /* Check 1: Starnix half-open PC range [start, end) */
    if (rip >= (uintptr_t)starnix_usercopy_start && rip < (uintptr_t)starnix_usercopy_end) {
        fault_overlay_kind = 1;
        uc->uc_mcontext.gregs[REG_RIP] = (greg_t)(uintptr_t)starnix_usercopy_fault;
        return;
    }

    /* Check 2: Linux __ex_table PC-relative lookup */
    for (const struct ex_table_entry *e = __start___ex_table; e < __stop___ex_table; ++e) {
        uintptr_t insn_pc = (uintptr_t)&e->insn + (intptr_t)e->insn;
        uintptr_t fixup_pc = (uintptr_t)&e->fixup + (intptr_t)e->fixup;
        if (rip == insn_pc) {
            fault_overlay_kind = 2;
            uc->uc_mcontext.gregs[REG_RIP] = (greg_t)fixup_pc;
            return;
        }
    }
    _exit(127);
}

/* 3. GCC target_clones IFUNC multi-versioning */
__attribute__((target_clones("default", "avx2", "avx512f")))
uint32_t sum_u32_clones(const uint32_t *buf, size_t n) {
    uint32_t s = 0;
    for (size_t i = 0; i < n; ++i) {
        s += buf[i];
    }
    return s;
}

int main(void) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = segv_handler;
    sa.sa_flags = SA_SIGINFO;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGSEGV, &sa, NULL) != 0) return 2;

    long psize = sysconf(_SC_PAGESIZE);
    uint8_t *arena = mmap(NULL, (size_t)psize * 2, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (arena == MAP_FAILED) return 3;
    if (mprotect(arena + psize, (size_t)psize, PROT_NONE) != 0) return 4;

    /* Place 19 valid bytes [1..=19] immediately before the PROT_NONE page boundary */
    size_t valid_bytes = 19;
    size_t req_bytes = 32;
    uint8_t *src = arena + psize - valid_bytes;
    for (size_t i = 0; i < valid_bytes; ++i) {
        src[i] = (uint8_t)(i + 1);
    }

    uint8_t dst1[32];
    memset(dst1, 0xaa, sizeof(dst1));
    fault_overlay_kind = 0;
    size_t rem1 = starnix_usercopy(dst1, src, req_bytes);
    int kind1 = fault_overlay_kind;
    int prefix1_ok = 1;
    int tail1_untouched = 1;
    for (size_t i = 0; i < valid_bytes; ++i) if (dst1[i] != (uint8_t)(i + 1)) prefix1_ok = 0;
    for (size_t i = valid_bytes; i < req_bytes; ++i) if (dst1[i] != 0xaa) tail1_untouched = 0;
    uintptr_t addr_diff1 = last_fault_addr - (uintptr_t)(arena + psize);

    uint8_t dst2[32];
    memset(dst2, 0xaa, sizeof(dst2));
    fault_overlay_kind = 0;
    size_t rem2 = extable_rep_usercopy(dst2, src, req_bytes);
    int kind2 = fault_overlay_kind;
    int prefix2_ok = 1;
    int tail2_untouched = 1;
    for (size_t i = 0; i < valid_bytes; ++i) if (dst2[i] != (uint8_t)(i + 1)) prefix2_ok = 0;
    for (size_t i = valid_bytes; i < req_bytes; ++i) if (dst2[i] != 0xaa) tail2_untouched = 0;
    uintptr_t addr_diff2 = last_fault_addr - (uintptr_t)(arena + psize);

    uint32_t arr[16];
    for (int i = 0; i < 16; ++i) arr[i] = (uint32_t)(i + 1);
    uint32_t clone_sum = sum_u32_clones(arr, 16);

    munmap(arena, (size_t)psize * 2);

    printf(
        "{\"starnix_range\":{\"req\":%zu,\"valid\":%zu,\"rem\":%zu,\"overlay_kind\":%d,\"prefix_written_exact\":%s,\"tail_untouched\":%s,\"fault_at_guard_page_offset\":%lu},"
        "\"linux_ex_table\":{\"req\":%zu,\"valid\":%zu,\"rem\":%zu,\"overlay_kind\":%d,\"prefix_written_exact\":%s,\"tail_untouched\":%s,\"fault_at_guard_page_offset\":%lu,\"ex_table_entries\":%ld},"
        "\"target_clones_sum\":%u}\n",
        req_bytes, valid_bytes, rem1, kind1, prefix1_ok ? "true" : "false", tail1_untouched ? "true" : "false", (unsigned long)addr_diff1,
        req_bytes, valid_bytes, rem2, kind2, prefix2_ok ? "true" : "false", tail2_untouched ? "true" : "false", (unsigned long)addr_diff2,
        (long)(__stop___ex_table - __start___ex_table),
        clone_sum
    );
    return 0;
}
'''
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)
        c_file = tdp / "overlay_ifunc.c"
        bin_file = tdp / "overlay_ifunc"
        c_file.write_text(c_src)
        run_cmd(["gcc", "-O2", "-Wall", "-Wextra", str(c_file), "-o", str(bin_file)])

        runtime = json.loads(run_cmd([str(bin_file)]).stdout.strip())
        syms = run_cmd(["readelf", "-sW", str(bin_file)]).stdout
        relocs = run_cmd(["readelf", "-rW", str(bin_file)]).stdout
        disasm = run_cmd(["objdump", "-d", str(bin_file)]).stdout

        ifunc_syms = [l.strip() for l in syms.splitlines() if "sum_u32_clones" in l or "__cpu_indicator_init" in l]
        irelative_relocs = [l.strip() for l in relocs.splitlines() if "IRELATIVE" in l]

        resolver_asm = run_cmd(["objdump", "-d", "--disassemble=sum_u32_clones.resolver", str(bin_file)]).stdout.strip()
        cpu_dis = run_cmd(["objdump", "-d", "--disassemble=__cpu_indicator_init", str(bin_file)]).stdout.splitlines()
        cpu_init_xgetbv_lines = []
        for idx, ln in enumerate(cpu_dis):
            if "xgetbv" in ln:
                start = max(0, idx - 3)
                end = min(len(cpu_dis), idx + 14)
                cpu_init_xgetbv_lines = [x.strip() for x in cpu_dis[start:end]]
                break

        return {
            "runtime": runtime,
            "ifunc_symbols": ifunc_syms,
            "irelative_relocations": irelative_relocs,
            "resolver_disasm": resolver_asm,
            "cpu_indicator_init_xgetbv_slice": cpu_init_xgetbv_lines,
        }


def main() -> None:
    all_res = {
        "seam3_ct_wrappers_and_black_box": probe_3_ct_wrappers_and_black_box(),
        "seam4_usercopy_fault_tables_and_ifunc": probe_4_usercopy_fault_tables_and_ifunc(),
    }
    out_path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rendered = json.dumps(all_res, indent=2)
    if out_path:
        out_path.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
