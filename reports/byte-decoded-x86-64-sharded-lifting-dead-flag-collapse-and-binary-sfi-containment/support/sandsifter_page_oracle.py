#!/usr/bin/env python3
"""
Sandsifter-style Linux x86-64 silicon page-boundary instruction-length,
fault-class (#UD vs. #GP(0) vs. #PF), prefix-precedence, and RFLAGS oracle.

Maps an executable page (`PROT_READ | PROT_EXEC`) immediately followed by an
unmapped guard page (`PROT_NONE`), sweeps candidate byte sequences across
`PAGE_END - L` for `L = 1..17` with trailing `0xcc` (`int3`), and captures
`SIGSEGV` / `SIGILL` / `SIGTRAP` architectural state (`REG_TRAPNO`, `REG_ERR`,
`REG_RIP`, `si_addr`, GPRs, and `REG_EFL`) via `SA_SIGINFO` + `rt_sigreturn`
on an isolated `sigaltstack`. Cross-checks physical silicon against
`llvm-mc` and GNU `objdump`.

All temporary C sources and binaries execute inside `tempfile.TemporaryDirectory()`
so zero artifacts remain in `/tmp` on exit.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def find_lean_cmd() -> list[str]:
    wrapper = shutil.which("anneal-lean-run") or str(Path.home() / ".local" / "bin" / "anneal-lean-run")
    lean_bin = str(
        Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean"
    )
    if not Path(lean_bin).exists():
        lean_bin = shutil.which("lean") or "lean"
    if Path(wrapper).exists():
        return [wrapper, lean_bin]
    return [lean_bin]

C_HARNESS = r"""
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>

static volatile int got_sig = 0;
static volatile int got_si_code = 0;
static volatile uintptr_t got_si_addr = 0;
static volatile uint64_t got_rip = 0;
static volatile uint64_t got_trapno = 0;
static volatile uint64_t got_err = 0;
static volatile uint64_t got_efl = 0;
static volatile uint64_t got_rax = 0;
static volatile uint64_t got_rcx = 0;
static volatile uint64_t got_rdx = 0;
static volatile uint64_t got_rsi = 0;
static volatile uint64_t got_rdi = 0;
static volatile uint64_t got_r8  = 0;

static uint64_t host_regs[8];

static void trap_handler(int sig, siginfo_t *si, void *uctx_void) {
    ucontext_t *uc = (ucontext_t *)uctx_void;
    got_sig     = sig;
    got_si_code = si ? si->si_code : 0;
    got_si_addr = si ? (uintptr_t)si->si_addr : 0;
    got_rip     = (uint64_t)uc->uc_mcontext.gregs[REG_RIP];
    got_trapno  = (uint64_t)uc->uc_mcontext.gregs[REG_TRAPNO];
    got_err     = (uint64_t)uc->uc_mcontext.gregs[REG_ERR];
    got_efl     = (uint64_t)uc->uc_mcontext.gregs[REG_EFL];
    got_rax     = (uint64_t)uc->uc_mcontext.gregs[REG_RAX];
    got_rcx     = (uint64_t)uc->uc_mcontext.gregs[REG_RCX];
    got_rdx     = (uint64_t)uc->uc_mcontext.gregs[REG_RDX];
    got_rsi     = (uint64_t)uc->uc_mcontext.gregs[REG_RSI];
    got_rdi     = (uint64_t)uc->uc_mcontext.gregs[REG_RDI];
    got_r8      = (uint64_t)uc->uc_mcontext.gregs[REG_R8];

    uc->uc_mcontext.gregs[REG_RSP] = (greg_t)host_regs[0];
    uc->uc_mcontext.gregs[REG_RBP] = (greg_t)host_regs[1];
    uc->uc_mcontext.gregs[REG_RBX] = (greg_t)host_regs[2];
    uc->uc_mcontext.gregs[REG_R12] = (greg_t)host_regs[3];
    uc->uc_mcontext.gregs[REG_R13] = (greg_t)host_regs[4];
    uc->uc_mcontext.gregs[REG_R14] = (greg_t)host_regs[5];
    uc->uc_mcontext.gregs[REG_R15] = (greg_t)host_regs[6];
    uc->uc_mcontext.gregs[REG_RIP] = (greg_t)host_regs[7];
    uc->uc_mcontext.gregs[REG_EFL] &= ~((greg_t)0x500);
}

__attribute__((noinline))
static void run_probe(void *target, void *scratch_mem,
                      uint64_t in_rax, uint64_t in_rcx, uint64_t in_rdx,
                      uint64_t in_rsi, uint64_t in_r8,  uint64_t in_fl) {
    uint64_t args[8] = {
        (uint64_t)(uintptr_t)target,
        (uint64_t)(uintptr_t)scratch_mem,
        in_rax, in_rcx, in_rdx, in_rsi, in_r8, in_fl
    };
    __asm__ volatile(
        "movq %%rsp, 0(%[h])\n\t"
        "movq %%rbp, 8(%[h])\n\t"
        "movq %%rbx, 16(%[h])\n\t"
        "movq %%r12, 24(%[h])\n\t"
        "movq %%r13, 32(%[h])\n\t"
        "movq %%r14, 40(%[h])\n\t"
        "movq %%r15, 48(%[h])\n\t"
        "leaq 1f(%%rip), %%r11\n\t"
        "movq %%r11, 56(%[h])\n\t"

        "movq %[a], %%r10\n\t"
        "pushfq\n\t"
        "popq %%r11\n\t"
        "andq $~0x8d5, %%r11\n\t"
        "orq  56(%%r10), %%r11\n\t"
        "pushq %%r11\n\t"
        "popfq\n\t"

        "movq 0(%%r10),  %%r11\n\t"
        "movq 8(%%r10),  %%rdi\n\t"
        "movq 16(%%r10), %%rax\n\t"
        "movq 24(%%r10), %%rcx\n\t"
        "movq 32(%%r10), %%rdx\n\t"
        "movq 40(%%r10), %%rsi\n\t"
        "movq 48(%%r10), %%r8\n\t"
        "leaq 512(%%rdi), %%rsp\n\t"
        "jmp *%%r11\n\t"
        "1:\n\t"
        :
        : [h] "r"(host_regs), [a] "r"(args)
        : "rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "cc", "memory"
    );
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    const size_t pagesz = 4096;
    uint8_t *arena = mmap(NULL, pagesz * 2, PROT_NONE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    uint8_t *scratch = mmap(NULL, pagesz * 2, PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    uint8_t *altstk_mem = mmap(NULL, 65536, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (arena == MAP_FAILED || scratch == MAP_FAILED || altstk_mem == MAP_FAILED) {
        perror("mmap");
        return 1;
    }

    stack_t ss = { .ss_sp = altstk_mem, .ss_size = 65536, .ss_flags = 0 };
    if (sigaltstack(&ss, NULL) != 0) { perror("sigaltstack"); return 1; }

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = trap_handler;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGILL,  &sa, NULL);
    sigaction(SIGTRAP, &sa, NULL);
    sigaction(SIGFPE,  &sa, NULL);
    sigaction(SIGBUS,  &sa, NULL);

    const char *hex = argv[1];
    int rax_is_rel_target = (argc > 8) ? atoi(argv[8]) : 0;
    size_t blen = strlen(hex) / 2;
    uint8_t buf[32];
    for (size_t i = 0; i < blen && i < 32; i++) {
        unsigned int v = 0;
        sscanf(hex + 2 * i, "%02x", &v);
        buf[i] = (uint8_t)v;
    }
    uint64_t in_rax = argc > 2 ? strtoull(argv[2], NULL, 0) : 0x1111111122222222ULL;
    uint64_t in_rcx = argc > 3 ? strtoull(argv[3], NULL, 0) : 0x0ULL;
    uint64_t in_rdx = argc > 4 ? strtoull(argv[4], NULL, 0) : 0x3333333344444444ULL;
    uint64_t in_rsi = argc > 5 ? strtoull(argv[5], NULL, 0) : 0x5ULL;
    uint64_t in_r8  = argc > 6 ? strtoull(argv[6], NULL, 0) : 0x7777777788888888ULL;
    uint64_t in_fl  = argc > 7 ? strtoull(argv[7], NULL, 0) : 0x0ULL;

    printf("{\"sweeps\":[");
    for (int L = 1; L <= 17; L++) {
        if (mprotect(arena, pagesz, PROT_READ | PROT_WRITE) != 0) { perror("mprotect rw"); return 1; }
        memset(arena, 0xcc, pagesz);
        uint8_t *start = arena + pagesz - L;
        size_t copy_n = blen < (size_t)L ? blen : (size_t)L;
        memcpy(start, buf, copy_n);
        if (mprotect(arena, pagesz, PROT_READ | PROT_EXEC) != 0) { perror("mprotect rx"); return 1; }
        memset(scratch, 0, pagesz);
        *(uint64_t *)(scratch + 256) = 0x100ULL;

        uint64_t use_rax = rax_is_rel_target ? (uint64_t)(uintptr_t)(start + in_rax) : in_rax;
        got_sig = 0;
        run_probe(start, scratch + 256, use_rax, in_rcx, in_rdx, in_rsi, in_r8, in_fl);

        long rip_delta = (long)(got_rip - (uintptr_t)start);
        long addr_delta = (long)(got_si_addr - (uintptr_t)(arena + pagesz));
        uint64_t mem0 = *(uint64_t *)(scratch + 256);
        printf("%s{\"L\":%d,\"sig\":%d,\"si_code\":%d,\"trapno\":%llu,\"err\":%llu,"
               "\"rip_delta\":%ld,\"si_addr_minus_end\":%ld,"
               "\"rax\":\"0x%llx\",\"rdx\":\"0x%llx\",\"r8\":\"0x%llx\","
               "\"mem0\":\"0x%llx\",\"efl6\":\"0x%03llx\"}",
               (L > 1 ? "," : ""), L, got_sig, got_si_code,
               (unsigned long long)got_trapno, (unsigned long long)got_err,
               rip_delta, addr_delta,
               (unsigned long long)got_rax, (unsigned long long)got_rdx,
               (unsigned long long)got_r8, (unsigned long long)mem0,
               (unsigned long long)(got_efl & 0x8d5ULL));
    }
    printf("]}\n");
    return 0;
}
"""


def cpu_identity() -> dict[str, str]:
    info: dict[str, str] = {"kernel": platform.platform()}
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8").splitlines():
            if ":" not in line:
                continue
            k, v = [p.strip() for p in line.split(":", 1)]
            if k in ("vendor_id", "cpu family", "model", "model name", "stepping") and k not in info:
                info[k.replace(" ", "_")] = v
            elif k == "flags" and "key_isa_flags" not in info:
                present = set(v.split())
                tracked = ["sse2", "avx", "avx2", "avx512f", "bmi1", "bmi2", "abm", "fsgsbase", "ibrs_enhanced"]
                info["key_isa_flags"] = " ".join(f for f in tracked if f in present)
    except OSError:
        pass
    return info


def disasm_llvm_mc(bs: bytes) -> dict[str, object]:
    hex_in = " ".join(f"0x{b:02x}" for b in bs)
    r = subprocess.run(
        ["llvm-mc", "--disassemble", "--triple=x86_64-unknown-linux-gnu"],
        input=hex_in,
        text=True,
        capture_output=True,
        timeout=5,
    )
    insns = [
        ln.strip()
        for ln in r.stdout.splitlines()
        if ln.strip() and not ln.strip().startswith(".text")
    ]
    warns = [
        ln.strip()
        for ln in r.stderr.splitlines()
        if "warning:" in ln or "error:" in ln
    ]
    return {"rc": r.returncode, "insns": insns, "diagnostics": warns}


def disasm_objdump(bs: bytes, td: Path) -> dict[str, object]:
    bf = td / "specimen.bin"
    bf.write_bytes(bs)
    r = subprocess.run(
        ["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel", str(bf)],
        text=True,
        capture_output=True,
        timeout=5,
    )
    insns = []
    for ln in r.stdout.splitlines():
        s = ln.strip()
        if s and s[0].isdigit() and ":" in s:
            parts = s.split("\t")
            insns.append(parts[-1].strip() if len(parts) >= 3 else s)
    return {"rc": r.returncode, "insns": insns}


def eval_lean_decode_batch(specimens: list[tuple[str, str, str, list[str]]], td: Path) -> dict[str, dict[str, object]]:
    """Evaluate `ByteX86.decodeX64` in Lean 4.34.1 on the exact 16-byte page window of every specimen."""
    lean_cmd = find_lean_cmd()
    env = dict(os.environ)
    # Build ByteX86Base.olean inside TemporaryDirectory if not already alongside ByteX86Base.lean
    olean_dir = td / "olean"
    olean_dir.mkdir(exist_ok=True)
    base_src = HERE / "ByteX86Base.lean"
    local_olean = HERE / "ByteX86Base.olean"
    if local_olean.exists():
        env["LEAN_PATH"] = str(HERE)
    else:
        subprocess.run(
            lean_cmd + ["-R", str(HERE), "-DElab.async=false", "-Ddebug.skipKernelTC=false",
                        "-o", str(olean_dir / "ByteX86Base.olean"), str(base_src)],
            check=True,
            env=env,
            timeout=300,
        )
        env["LEAN_PATH"] = str(olean_dir)

    lines = [
        "import Init.System.IO",
        "import ByteX86Base",
        "open ByteX86",
        "def classifyOut (nm : String) (bs : List UInt8) : String := ",
        "  match decodeX64 bs with",
        "  | .ok ins len => s!\"{nm}|OK_EXEC|{len}|{reprStr ins}\"",
        "  | .fault .gpLenExceeded => s!\"{nm}|FAULT_GP0|16|gpLenExceeded\"",
        "  | .fault .gpRing3Priv   => s!\"{nm}|FAULT_GP0|1|gpRing3Priv\"",
        "  | .fault .udIllegalLock => s!\"{nm}|FAULT_UD|0|udIllegalLock\"",
        "  | .fault .udIllegalVexPrefix => s!\"{nm}|FAULT_UD|0|udIllegalVexPrefix\"",
        "  | .fault .udExplicit    => s!\"{nm}|FAULT_UD|0|udExplicit\"",
        "  | .fault f              => s!\"{nm}|UNSUPPORTED|0|{reprStr f}\"",
        "def main : IO Unit := do",
    ]
    for name, _cat, hx, _extra in specimens:
        raw = bytes.fromhex(hx)
        # Match the C harness executable page fill (`memset(arena, 0xcc, pagesz)`) over a 16-byte window:
        win16 = raw + (b"\xcc" * max(0, 16 - len(raw)))
        byte_list = ", ".join(f"0x{b:02X}" for b in win16[:16])
        lines.append(f'  IO.println (classifyOut "{name}" [{byte_list}])')

    probe_lean = td / "DecodeOracleCheck.lean"
    probe_lean.write_text("\n".join(lines) + "\n", encoding="utf-8")
    out = subprocess.check_output(
        lean_cmd + ["--run", str(probe_lean)],
        text=True,
        env=env,
        timeout=300,
    )
    res: dict[str, dict[str, object]] = {}
    for ln in out.splitlines():
        if "|" not in ln:
            continue
        nm, verd, ln_s, detail = ln.split("|", 3)
        res[nm] = {
            "verdict": verd,
            "decode_len": int(ln_s),
            "detail": detail,
        }
    return res


def classify_silicon(sweeps: list[dict[str, object]]) -> dict[str, object]:
    first_resolved = None
    for s in sweeps:
        is_fetch_pf = (
            s["trapno"] == 14
            and s["rip_delta"] == 0
            and s["si_addr_minus_end"] == 0
        )
        if not is_fetch_pf:
            first_resolved = s
            break
    s17 = sweeps[-1]
    assert first_resolved is not None
    trap = first_resolved["trapno"]
    if trap == 6:
        verdict = "FAULT_UD"
        hw_len = first_resolved["L"]
    elif trap == 13 and first_resolved["rip_delta"] == 0:
        verdict = "FAULT_GP0"
        hw_len = first_resolved["L"]
    elif s17["trapno"] == 3 and s17["rip_delta"] >= 2:
        verdict = "OK_EXEC"
        hw_len = int(s17["rip_delta"]) - 1
    else:
        verdict = f"TRAP_{trap}"
        hw_len = first_resolved["L"]
    return {
        "verdict": verdict,
        "hw_decode_len": hw_len,
        "boundary_L": first_resolved["L"],
        "boundary_trapno": first_resolved["trapno"],
        "boundary_err": first_resolved["err"],
        "boundary_rip_delta": first_resolved["rip_delta"],
        "exec_L17_trapno": s17["trapno"],
        "exec_L17_rip_delta": s17["rip_delta"],
        "post_rax": s17["rax"],
        "post_rdx": s17["rdx"],
        "post_r8": s17["r8"],
        "post_mem0": s17["mem0"],
        "post_efl6": s17["efl6"],
    }


SPECIMENS = [
    # Category 1: Instruction length limit (1..16 bytes) & page-boundary fetch priority
    ("len_1b_nop", "length_limit", "90", []),
    ("len_3b_nop", "length_limit", "0f1f00", []),
    ("len_7b_nop", "length_limit", "0f1f8000000000", []),
    ("len_11b_gcc_align_nop", "length_limit", "66662e0f1f840000000000", []),
    ("len_15b_max_legal_nop", "length_limit", "66" * 14 + "90", []),
    ("len_16b_overlong_nop_gp0", "length_limit", "66" * 15 + "90", []),
    ("len_15pfx_plus_int3_gp0", "length_limit", "66" * 15, []),

    # Category 2: CET / Hintable NOP space (0F 1E /r) vs Ring-3 privileged CLI
    ("cet_endbr64", "cet_hint_nop", "f30f1efa", []),
    ("cet_endbr32", "cet_hint_nop", "f30f1efb", []),
    ("hint_nop_0f1efa_not_cli", "cet_hint_nop", "0f1efa", []),
    ("priv_cli_ring3_gp0", "cet_hint_nop", "fa", []),
    ("cet_notrack_jmp_rax", "cet_hint_nop", "3effe0", ["3", "0", "0", "0", "0", "0", "1"]),

    # Category 3: LOCK (0xF0) legality & post-ILD #UD
    ("lock_add_mem_legal", "lock_legality", "f0480107", ["0x2a", "0", "0", "0", "0", "0"]),
    ("lock_add_imm_mem_legal", "lock_legality", "f048830705", []),
    ("lock_cmpxchg_mem_legal", "lock_legality", "f0480fb137", ["0x100", "0", "0", "0x777", "0", "0"]),
    ("lock_nop_illegal_ud", "lock_legality", "f090", []),
    ("lock_add_reg_dst_ud", "lock_legality", "f04801f0", []),
    ("lock_mov_load_ud", "lock_legality", "f0488b07", []),
    ("lock_mov_store_ud", "lock_legality", "f0488907", []),

    # Category 4: REX nullification, consecutive REX precedence, and 0x90 REX.B
    ("rex_40_nop", "rex_precedence", "4090", []),
    ("rex_48_nop", "rex_precedence", "4890", []),
    ("rex_41_xchg_eax_r8d", "rex_precedence", "4190", []),
    ("rex_49_xchg_rax_r8", "rex_precedence", "4990", []),
    ("rex_41_40_last_rex_wins_nop", "rex_precedence", "414090", []),
    ("rex_40_41_last_rex_wins_xchg", "rex_precedence", "404190", []),
    ("rex_41_66_nullified_by_legacy", "rex_precedence", "416690", []),
    ("rex_66_41_xchg_ax_r8w", "rex_precedence", "664190", []),
    ("rex_48_67_nullified_add32", "rex_precedence", "486701f0", ["0x100000002", "0", "0", "0x200000003", "0", "0"]),
    ("rex_67_48_active_add64", "rex_precedence", "674801f0", ["0x100000002", "0", "0", "0x200000003", "0", "0"]),

    # Category 5: VEX prefix exclusion rules (#UD on 66/F2/F3/F0/REX before VEX)
    ("vex_bare_vzeroupper_ok", "vex_prefix_ud", "c5f877", []),
    ("vex_cs_2e_prefix_ok", "vex_prefix_ud", "2ec5f877", []),
    ("vex_addr32_67_prefix_ok", "vex_prefix_ud", "67c5f877", []),
    ("vex_66_prefix_ud", "vex_prefix_ud", "66c5f877", []),
    ("vex_f2_prefix_ud", "vex_prefix_ud", "f2c5f877", []),
    ("vex_f3_prefix_ud", "vex_prefix_ud", "f3c5f877", []),
    ("vex_rex_48_prefix_ud", "vex_prefix_ud", "48c5f877", []),
    ("vex_lock_f0_prefix_ud", "vex_prefix_ud", "f0c5f877", []),

    # Category 6: BSF vs TZCNT & architecturally undefined RFLAGS on silicon
    ("bsf_zero_fl0", "flags_and_bmi", "480fbcd1", ["0x11", "0x0", "0xdeadbeefcafebabe", "0x0", "0x0", "0x000"]),
    ("bsf_zero_fl1", "flags_and_bmi", "480fbcd1", ["0x11", "0x0", "0xdeadbeefcafebabe", "0x0", "0x0", "0x8d5"]),
    ("tzcnt_zero_fl0", "flags_and_bmi", "f3480fbcd1", ["0x11", "0x0", "0xdeadbeefcafebabe", "0x0", "0x0", "0x000"]),
    ("tzcnt_zero_fl1", "flags_and_bmi", "f3480fbcd1", ["0x11", "0x0", "0xdeadbeefcafebabe", "0x0", "0x0", "0x8d5"]),
    ("bsf_bit7_nonzero", "flags_and_bmi", "480fbcd1", ["0x11", "0x80", "0xdeadbeefcafebabe", "0x0", "0x0", "0x8d5"]),
    ("tzcnt_bit7_nonzero", "flags_and_bmi", "f3480fbcd1", ["0x11", "0x80", "0xdeadbeefcafebabe", "0x0", "0x0", "0x8d5"]),
    ("imul_zero_result_zf0_pf1", "flags_and_bmi", "480fafc6", ["0x0", "0x0", "0x0", "0x7", "0x0", "0x000"]),
    ("imul_overflow_cf1_of1", "flags_and_bmi", "480fafc6", ["0x4000000000000000", "0x0", "0x0", "0x4", "0x0", "0x000"]),
    ("xor_zero_clears_af", "flags_and_bmi", "4831f0", ["0x3", "0x0", "0x0", "0x3", "0x0", "0x8d5"]),
    ("shl_cnt2_of_cf", "flags_and_bmi", "48c1e002", ["0x4000000000000001", "0x0", "0x0", "0x0", "0x0", "0x000"]),

    # Category 7: SFI 32-bit zero-extension idiom
    ("sfi_movl_eax_eax_zext32", "sfi_zext", "89c0", ["0xdeadbeef00000028", "0x0", "0x0", "0x0", "0x0", "0x000"]),
]


def main() -> int:
    with tempfile.TemporaryDirectory() as td_raw:
        td = Path(td_raw)
        c_path = td / "sandsifter_oracle.c"
        bin_path = td / "sandsifter_oracle"
        c_path.write_text(C_HARNESS, encoding="utf-8")
        subprocess.run(
            ["gcc", "-O2", "-Wall", "-Wextra", str(c_path), "-o", str(bin_path)],
            check=True,
            timeout=30,
        )

        gcc_ver = subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0]
        llvm_ver = " ".join(
            ln.strip()
            for ln in subprocess.check_output(["llvm-mc", "--version"], text=True).splitlines()[:2]
        )
        objdump_ver = subprocess.check_output(["objdump", "--version"], text=True).splitlines()[0]

        lean_ver = subprocess.check_output(
            find_lean_cmd() + ["--version"], text=True, timeout=300
        ).splitlines()[0]
        lean_decodes = eval_lean_decode_batch(SPECIMENS, td)

        records = []
        for name, cat, hx, extra in SPECIMENS:
            raw_bytes = bytes.fromhex(hx)
            out = subprocess.check_output(
                [str(bin_path), hx] + extra, text=True, timeout=5
            )
            sweeps = json.loads(out)["sweeps"]
            sil = classify_silicon(sweeps)
            mc = disasm_llvm_mc(raw_bytes)
            od = disasm_objdump(raw_bytes, td)
            ld = lean_decodes[name]

            # Distinguish unconditional architectural decode faults (#UD / >15B #GP(0))
            # from Ring-3 privilege traps on valid system instructions (0xfa `cli`).
            is_ring3_priv_trap = (name == "priv_cli_ring3_gp0")
            is_arch_decode_fault = sil["verdict"] in ("FAULT_UD", "FAULT_GP0") and not is_ring3_priv_trap

            mc_silent_accept = is_arch_decode_fault and mc["rc"] == 0 and len(mc["diagnostics"]) == 0
            od_silent_accept = is_arch_decode_fault and od["rc"] == 0 and not any(
                "bad" in x.lower() for x in od["insns"]
            )
            lean_matches_silicon = (
                ld["verdict"] == sil["verdict"]
                and (ld["verdict"] != "OK_EXEC" or ld["decode_len"] == sil["hw_decode_len"])
            )
            records.append({
                "name": name,
                "category": cat,
                "hex": hx,
                "byte_len": len(raw_bytes),
                "silicon": sil,
                "lean_decodeX64": ld,
                "lean_matches_silicon": lean_matches_silicon,
                "is_arch_decode_fault": is_arch_decode_fault,
                "is_ring3_priv_trap": is_ring3_priv_trap,
                "llvm_mc": mc,
                "objdump": od,
                "llvm_mc_silent_false_accept": mc_silent_accept,
                "objdump_silent_false_accept": od_silent_accept,
            })

    arch_decode_faults = sum(1 for r in records if r["is_arch_decode_fault"])
    summary = {
        "total_specimens": len(records),
        "silicon_ok_exec": sum(1 for r in records if r["silicon"]["verdict"] == "OK_EXEC"),
        "silicon_fault_ud": sum(1 for r in records if r["silicon"]["verdict"] == "FAULT_UD"),
        "silicon_fault_gp0_overlong": sum(
            1 for r in records if r["silicon"]["verdict"] == "FAULT_GP0" and r["is_arch_decode_fault"]
        ),
        "silicon_fault_gp0_ring3_priv": sum(
            1 for r in records if r["silicon"]["verdict"] == "FAULT_GP0" and r["is_ring3_priv_trap"]
        ),
        "arch_decode_fault_specimens": arch_decode_faults,
        "lean_decodeX64_exact_matches": sum(1 for r in records if r["lean_matches_silicon"]),
        "llvm_mc_arch_decode_fault_false_accepts": sum(1 for r in records if r["llvm_mc_silent_false_accept"]),
        "objdump_arch_decode_fault_false_accepts": sum(1 for r in records if r["objdump_silent_false_accept"]),
    }
    payload = {
        "host_cpu": cpu_identity(),
        "toolchains": {
            "gcc": gcc_ver,
            "llvm_mc": llvm_ver,
            "objdump": objdump_ver,
            "lean": lean_ver,
        },
        "summary": summary,
        "specimens": records,
    }
    out_json = HERE / "sandsifter_page_oracle_results.json"
    out_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    digest = hashlib.sha256(out_json.read_bytes()).hexdigest()
    print(f"Wrote {out_json.name} (sha256={digest[:16]}...): {json.dumps(summary)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
