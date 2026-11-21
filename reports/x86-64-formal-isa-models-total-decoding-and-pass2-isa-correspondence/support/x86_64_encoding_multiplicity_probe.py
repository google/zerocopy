#!/usr/bin/env python3
"""Empirical x86-64 encoding multiplicity and decoding-hazard probe.

Exercises two independent real-world binary tools (`gcc -O2` + GNU `objdump`,
and `llvm-mc --disassemble`) on:
  (A) Real compiler-emitted `.o` machine code (`gcc -O2 -fcf-protection=full -mavx2`),
      demonstrating non-canonical/multi-form encodings actually emitted in practice
      (CET `endbr64`, multi-byte alignment NOPs, mandatory SIB/disp8, short/long
      immediate forms, `lock cmpxchg`/`lock xadd`, `bsf`/`shl`/`mul`, VEX2/VEX3).
  (B) An 18-case controlled encoding-multiplicity and architectural-legality matrix
      cross-checked across `llvm-mc` and GNU `objdump` to distinguish:
      - true semantic multiplicity (multiple distinct byte strings -> same AST),
      - prefix precedence & REX nullification hazards,
      - `REX.B` + `0x90` (`nop` vs `xchg r8d, eax`),
      - `LOCK` (`0xF0`) `#UD` legality traps, and
      - the 15-byte `#GP(0)` architectural instruction-length limit.

All temporary build files are cleaned up automatically via TemporaryDirectory.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

C_SOURCE = r"""
#include <stdint.h>
#include <immintrin.h>

uint64_t add_forms(uint64_t a, uint64_t b) {
    uint64_t x = a + b;
    x += 1;
    x += 0x1234567;
    return x;
}

uint64_t addr_modes(const uint64_t *p, uint64_t idx) {
    volatile uint64_t stack_slot = idx;
    return p[0] + p[1] + p[32] + stack_slot;
}

int atomic_cas_and_fetch_add(uint64_t *slot, uint64_t expected, uint64_t desired, uint64_t *ctr) {
    __atomic_fetch_add(ctr, 1, __ATOMIC_SEQ_CST);
    return __atomic_compare_exchange_n(slot, &expected, desired, 0, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
}

uint64_t loop_with_align_nops(const uint64_t *arr, uint64_t n) {
    uint64_t acc = 0;
    for (uint64_t i = 0; i < n; i++) {
        acc = (acc << (i & 7)) ^ arr[i];
        if (arr[i]) acc += (uint64_t)__builtin_ctzll(arr[i]);
    }
    return acc;
}

__m256i vex2_vs_vex3(__m256i a, __m256i b, __m256i c) {
    __m256i x = _mm256_xor_si256(a, b);
    return _mm256_shuffle_epi8(x, c);
}
"""


def run_cmd(cmd: list[str], stdin_data: str | None = None) -> tuple[int, str, str]:
    proc = subprocess.run(
        cmd,
        input=stdin_data,
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.returncode, proc.stdout, proc.stderr


def disasm_llvm_mc(hex_bytes: str) -> dict[str, object]:
    tokens = " ".join(f"0x{b}" for b in hex_bytes.split())
    rc, out, err = run_cmd(
        ["llvm-mc", "--disassemble", "-triple=x86_64", "-x86-asm-syntax=intel"],
        stdin_data=tokens + "\n",
    )
    insts = [l.strip() for l in out.splitlines() if l.strip() and not l.strip().startswith(".")]
    return {"rc": rc, "insts": insts, "stderr": err.strip()}


def parse_objdump_lines(out: str) -> list[dict[str, str]]:
    lines: list[dict[str, str]] = []
    for l in out.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\s+([0-9a-f ]+?)\t(.*)$", l)
        if m:
            lines.append(
                {
                    "offset": m.group(1),
                    "bytes": " ".join(m.group(2).split()),
                    "asm": " ".join(m.group(3).split()),
                }
            )
            continue
        # Continuation line for >7-byte x86-64 instructions in GNU objdump
        mc = re.match(r"^\s*[0-9a-f]+:\s+([0-9a-f ]+?)\s*$", l)
        if mc and lines:
            extra = " ".join(mc.group(1).split())
            if extra:
                lines[-1]["bytes"] = lines[-1]["bytes"] + " " + extra
    return lines


def disasm_objdump(hex_bytes: str) -> dict[str, object]:
    raw = bytes.fromhex(hex_bytes)
    with tempfile.TemporaryDirectory() as td:
        bin_path = Path(td) / "snippet.bin"
        bin_path.write_bytes(raw)
        rc, out, err = run_cmd(
            ["objdump", "-D", "-b", "binary", "-m", "i386:x86-64", "-M", "intel", str(bin_path)]
        )
    lines = [{"bytes": x["bytes"], "asm": x["asm"]} for x in parse_objdump_lines(out)]
    return {"rc": rc, "insts": lines, "stderr": err.strip()}


def compile_and_disasm_gcc() -> dict[str, object]:
    with tempfile.TemporaryDirectory() as td:
        src = Path(td) / "probe.c"
        obj = Path(td) / "probe.o"
        src.write_text(C_SOURCE)
        cmd = ["gcc", "-O2", "-fcf-protection=full", "-mavx2", "-c", str(src), "-o", str(obj)]
        rc, out, err = run_cmd(cmd)
        if rc != 0:
            raise RuntimeError(f"gcc failed: {err}")
        rc2, dis, err2 = run_cmd(["objdump", "-d", "-M", "intel", str(obj)])
        if rc2 != 0:
            raise RuntimeError(f"objdump failed: {err2}")

    funcs: dict[str, list[dict[str, str]]] = {}
    cur_fn = None
    for line in dis.splitlines():
        mf = re.match(r"^[0-9a-f]+ <([^>]+)>:$", line)
        if mf:
            cur_fn = mf.group(1)
            funcs[cur_fn] = []
            continue
        if cur_fn is None:
            continue
        mi = re.match(r"^\s*([0-9a-f]+):\s+([0-9a-f ]+?)\t(.*)$", line)
        if mi:
            funcs[cur_fn].append(
                {
                    "offset": mi.group(1),
                    "bytes": " ".join(mi.group(2).split()),
                    "asm": " ".join(mi.group(3).split()),
                }
            )
            continue
        mc = re.match(r"^\s*[0-9a-f]+:\s+([0-9a-f ]+?)\s*$", line)
        if mc and funcs[cur_fn]:
            extra = " ".join(mc.group(1).split())
            if extra:
                funcs[cur_fn][-1]["bytes"] += " " + extra
    # Extract notable real-compiler phenomena
    notable = {
        "endbr64": [],
        "multi_byte_nops": [],
        "lock_atomics": [],
        "vex2_c5_vs_vex3_c4": [],
        "imm_forms_add": [],
        "sib_or_disp_forms": [],
        "undef_flag_ops": [],
    }
    for fn, insns in funcs.items():
        for ins in insns:
            b = ins["bytes"]
            a = ins["asm"]
            entry = {"fn": fn, **ins}
            if a.startswith("endbr64"):
                notable["endbr64"].append(entry)
            if re.match(r"^(?:data16\s+|cs\s+)*nop\b", a) and len(b.split()) > 1:
                notable["multi_byte_nops"].append(entry)
            if a.startswith("lock "):
                notable["lock_atomics"].append(entry)
            if b.startswith("c5 ") or b.startswith("c4 "):
                notable["vex2_c5_vs_vex3_c4"].append(entry)
            if a.startswith("add ") and any(k in b.split() for k in ("05", "81", "83")):
                notable["imm_forms_add"].append(entry)
            if "[rsp" in a or "+0x100]" in a or "[rdi+0x8]" in a:
                notable["sib_or_disp_forms"].append(entry)
            if any(a.startswith(op) for op in ("bsf ", "tzcnt ", "shl ", "sal ", "mul ")):
                notable["undef_flag_ops"].append(entry)
    return {"functions": funcs, "notable": notable}


CASES = [
    # 1. Direction-bit alternate opcodes (0x01 vs 0x03)
    ("dir_bit_01_add_rax_rsi", "48 01 f0", "add rax, rsi via opcode 0x01 (MR)"),
    ("dir_bit_03_add_rax_rsi", "48 03 c6", "add rax, rsi via opcode 0x03 (RM)"),
    # 2. Immediate-form multiplicity (0x05 vs 0x81 /0 vs 0x83 /0)
    ("imm_05_rax_short_add1", "48 05 01 00 00 00", "add rax, 1 via opcode 0x05 (RAX imm32 short form, 6B)"),
    ("imm_81_modrm_imm32_add1", "48 81 c0 01 00 00 00", "add rax, 1 via opcode 0x81 /0 (imm32, 7B)"),
    ("imm_83_modrm_imm8_add1", "48 83 c0 01", "add rax, 1 via opcode 0x83 /0 (sign-extended imm8, 4B)"),
    # 3. ModRM displacement & SIB multiplicity for mov rax, [rdi]
    ("ea_mod00_base_rdi", "48 8b 07", "mov rax, [rdi] via Mod=00 RM=7 (3B)"),
    ("ea_mod01_disp8_zero", "48 8b 47 00", "mov rax, [rdi+0] via Mod=01 disp8=0 (4B)"),
    ("ea_mod10_disp32_zero", "48 8b 87 00 00 00 00", "mov rax, [rdi+0] via Mod=10 disp32=0 (7B)"),
    ("ea_mod00_sib_no_index", "48 8b 04 27", "mov rax, [rdi] via SIB scale=1 idx=none(4) base=rdi (4B)"),
    # 4. NOP multiplicity vs REX.B soundness trap
    ("nop_90", "90", "1B canonical nop"),
    ("nop_66_90", "66 90", "2B operand-size-prefixed nop"),
    ("nop_48_90_rexw", "48 90", "2B REX.W + 0x90 (still nop, REX.B=0)"),
    ("nop_40_90_rex0", "40 90", "2B bare REX=0x40 + 0x90 (still nop)"),
    ("trap_41_90_rexb_xchg32", "41 90", "SOUNDNESS TRAP: REX.B=1 turns 0x90 into xchg r8d, eax (zeroes upper 32 bits!)"),
    ("trap_49_90_rexwb_xchg64", "49 90", "SOUNDNESS TRAP: REX.W+REX.B turns 0x90 into xchg r8, rax"),
    ("nop_0f1f_6b", "66 0f 1f 44 00 00", "6B Intel recommended multi-byte nop"),
    # 5. REX placement / nullification by subsequent legacy prefix
    ("rex_nullified_before_67", "48 67 01 00", "REX 0x48 before legacy 0x67 is IGNORED -> 32-bit add dword ptr [eax], eax"),
    ("rex_effective_after_67", "67 48 01 00", "REX 0x48 after legacy 0x67 is ACTIVE -> 64-bit add qword ptr [eax], rax"),
    # 6. Mandatory prefix precedence (66 vs F2 vs F3) & ENDBR64
    ("pfx_66_f3_addss", "66 f3 0f 58 c1", "F3 overrides 66 -> addss xmm0, xmm1"),
    ("pfx_f3_66_addss", "f3 66 0f 58 c1", "F3 overrides 66 regardless of order -> addss xmm0, xmm1"),
    ("pfx_f2_f3_last_wins_addss", "f2 f3 0f 58 c1", "Within Group 1 {F2,F3}, last wins -> addss"),
    ("pfx_f3_f2_last_wins_addsd", "f3 f2 0f 58 c1", "Within Group 1 {F2,F3}, last wins -> addsd"),
    ("pfx_endbr64_f3", "f3 0f 1e fa", "F3 0F 1E FA -> endbr64 (CET-IBT landing pad)"),
    ("pfx_nop_0f1e_no_f3", "0f 1e fa", "0F 1E FA without F3 -> hintable NOP (llvm-mc fails and resyncs on 0xFA=cli!)"),
    ("pfx_f3_tzcnt_vs_bsf", "f3 48 0f bc d1", "F3 48 0F BC D1 -> tzcnt rdx, rcx (BMI1) vs bsf rdx, rcx (pre-BMI1 CPUID!)"),
    ("pfx_bsf_no_f3", "48 0f bc d1", "48 0F BC D1 -> bsf rdx, rcx (dest/CF/OF/SF/PF/AF undefined on 0)"),
    # 7. REX.W vs 0x66 precedence
    ("pfx_66_rexw_add64", "66 48 01 f0", "REX.W overrides 0x66 -> 64-bit add rax, rsi"),
    # 8. LOCK prefix legality (legal mem dst vs architectural #UD reg dst / non-lockable op)
    ("lock_legal_mem_add", "f0 48 01 07", "Legal: lock add qword ptr [rdi], rax"),
    ("lock_ud_reg_dst_add", "f0 48 01 f0", "Architectural #UD: LOCK on register destination (add rax, rsi)"),
    ("lock_ud_nonlockable_mov", "f0 48 8b 07", "Architectural #UD: LOCK on non-lockable MOV"),
    # 9. 15-byte architectural instruction length limit (#GP(0) at 16 bytes)
    ("len_15_legal_nop", " ".join(["66"] * 14 + ["90"]), "Legal 15-byte instruction (14x 0x66 + 0x90)"),
    ("len_16_gp_fault", " ".join(["66"] * 15 + ["90"]), "Architectural #GP(0): 16-byte instruction exceeds 15B limit"),
    # 10. VEX2 (C5) vs VEX3 (C4) encoding multiplicity
    ("vex2_vpxor_ymm0", "c5 f5 ef c0", "4B VEX2 encoding of vpxor ymm0, ymm1, ymm0"),
    ("vex3_vpxor_ymm0", "c4 e1 75 ef c0", "5B VEX3 encoding of vpxor ymm0, ymm1, ymm0"),
]


def main() -> int:
    versions = {}
    for tool, args in [
        ("gcc", ["gcc", "--version"]),
        ("llvm-mc", ["llvm-mc", "--version"]),
        ("objdump", ["objdump", "--version"]),
    ]:
        _, out, _ = run_cmd(args)
        versions[tool] = out.splitlines()[0].strip() if out else "unknown"

    gcc_res = compile_and_disasm_gcc()
    matrix = []
    for name, hex_bytes, note in CASES:
        matrix.append(
            {
                "case": name,
                "bytes": hex_bytes,
                "len": len(hex_bytes.split()),
                "note": note,
                "llvm_mc": disasm_llvm_mc(hex_bytes),
                "objdump": disasm_objdump(hex_bytes),
            }
        )

    report = {
        "tool_versions": versions,
        "gcc_o2_notable": gcc_res["notable"],
        "gcc_o2_function_counts": {k: len(v) for k, v in gcc_res["functions"].items()},
        "multiplicity_matrix": matrix,
    }

    out_path = Path(__file__).with_name("x86_64_encoding_multiplicity_results.json")
    out_path.write_text(json.dumps(report, indent=2) + "\n")

    print("=== Tool versions ===")
    for k, v in versions.items():
        print(f"  {k}: {v}")
    print("\n=== GCC -O2 -fcf-protection=full -mavx2 notable emitted encodings ===")
    for cat, items in gcc_res["notable"].items():
        print(f"  [{cat}] ({len(items)} hits):")
        for it in items[:4]:
            print(f"    {it['fn']}+{it['offset']}: {it['bytes']:32s}  {it['asm']}")
    print(f"\n=== Controlled Encoding-Multiplicity & Legality Matrix ({len(matrix)} cases) ===")
    for row in matrix:
        lm = " | ".join(row["llvm_mc"]["insts"])
        if row["llvm_mc"]["stderr"]:
            lm = f"{lm} [WARN: {row['llvm_mc']['stderr'].splitlines()[0]}]"
        od = " | ".join(f"{x['bytes']}: {x['asm']}" for x in row["objdump"]["insts"])
        print(f"  {row['case']:28s} ({row['len']:2d}B) | llvm-mc: {lm:50s} | objdump: {od}")
    print(f"\nWrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
