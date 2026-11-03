#!/usr/bin/env python3
"""Empirical instruction-encoding and code-size probe for SFI and Ring-0 Wasm kernels.

Assembles and disassembles exact machine code sequences using llvm-mc for:
1. NaCl x86-64 (2009-2010): 32-byte bundle alignment, %r15 sandbox base,
   explicit 32-bit zero-extension (`movl %eX, %eX`), and masked indirect
   branches (`andl $0xffffffe0, %eax; addq %r15, %rax; jmpq *%rax`).
2. LFI x86-64 (2024-2026):
   - Base-register (`%r14`) sandboxing: `movq (%r14, %rax), %rcx` (with 32-bit zero-ext)
   - Segue `%gs` + `addr32` (`0x65 0x67`) sandboxing: `movq %gs:(%eax), %rcx`
   - Post-link segment-prefix padding (`0x2e` CS prefix absorption vs trailing NOPs)
   - Bundle-aligned indirect branch vs bundle-free direct branch
3. LFI AArch64 (2024 `lfi-research` x21/x18/x22 and 2025-2026 `lfi-verifier` x27/x28/x26):
   - Single-instruction `uxtw` load/store: `ldr x0, [x21, w1, uxtw]`
   - Addressed `uxtw` + immediate offset: `add x18, x21, w1, uxtw; ldr x0, [x18, #16]`
   - Bundle-free indirect branch: `add x18, x21, w1, uxtw; br x18` (and metered `bic` variant)
   - Bundle-free runtime call trampoline via `[x21]`: `mov w22, w30; ldr x30, [x21]; blr x30; add x30, x21, w22, uxtw`
4. Ring-0 Wasm 4 GiB + Guard-Page Addressing (Nebulet / Cranelift x86-64 & AArch64):
   - Elided bounds check via 32-bit zero-extended index + static offset
"""

import json
from pathlib import Path
import subprocess

LLVM_MC = "/usr/bin/llvm-mc"


def assemble_snippets(triple: str, asm_lines: list[str], mattr: str = "") -> list[dict]:
    cmd = [LLVM_MC, f"--triple={triple}", "--show-encoding", "--show-inst"]
    if mattr:
        cmd.append(f"--mattr={mattr}")
    inp = "\n".join(asm_lines) + "\n"
    proc = subprocess.run(cmd, input=inp, text=True, capture_output=True, check=True)
    results = []
    for line in proc.stdout.splitlines():
        s = line.strip()
        marker = "# encoding:" if "# encoding:" in s else ("// encoding:" if "// encoding:" in s else None)
        if marker:
            code_part, rest = s.split(marker, 1)
            asm_text = code_part.strip()
            enc_str = rest.strip()
            if "[" in enc_str and "]" in enc_str:
                hex_list = enc_str[enc_str.index("[") + 1 : enc_str.index("]")].split(",")
                raw_bytes = [int(h.strip(), 16) for h in hex_list if h.strip()]
            else:
                raw_bytes = []
            current_inst = {
                "asm": asm_text,
                "bytes": [f"{b:02x}" for b in raw_bytes],
                "len": len(raw_bytes),
            }
            results.append(current_inst)
    return results


def analyze_sequence(name: str, triple: str, asm_lines: list[str]) -> dict:
    insts = assemble_snippets(triple, asm_lines)
    total_bytes = sum(i["len"] for i in insts)
    return {
        "name": name,
        "triple": triple,
        "instruction_count": len(insts),
        "total_bytes": total_bytes,
        "instructions": insts,
    }


def main():
    sequences = [
        # 1. Memory Load with 32-bit sandboxed address (no immediate offset)
        analyze_sequence(
            "Baseline_x86_64_Unsandboxed_Load",
            "x86_64-unknown-linux-gnu",
            ["movq (%rax), %rcx"],
        ),
        analyze_sequence(
            "NaCl_or_LFI_BaseReg_x86_64_Load",
            "x86_64-unknown-linux-gnu",
            [
                "movl %eax, %eax",
                "movq (%r14, %rax), %rcx",
            ],
        ),
        analyze_sequence(
            "LFI_Segue_GS_Addr32_x86_64_Load",
            "x86_64-unknown-linux-gnu",
            [
                "movq %gs:(%eax), %rcx",
            ],
        ),
        analyze_sequence(
            "Baseline_AArch64_Unsandboxed_Load",
            "aarch64-unknown-linux-gnu",
            ["ldr x0, [x1]"],
        ),
        analyze_sequence(
            "LFI_AArch64_Uxtw_SingleInst_Load_2024_x21",
            "aarch64-unknown-linux-gnu",
            ["ldr x0, [x21, w1, uxtw]"],
        ),
        analyze_sequence(
            "LFI_AArch64_Uxtw_SingleInst_Load_2025_x27",
            "aarch64-unknown-linux-gnu",
            ["ldr x0, [x27, w1, uxtw]"],
        ),
        # 2. Memory Load with Immediate Displacement (e.g. struct field [ptr + 16])
        analyze_sequence(
            "LFI_x86_64_Segue_Load_ImmDisp",
            "x86_64-unknown-linux-gnu",
            ["movq %gs:16(%eax), %rcx"],
        ),
        analyze_sequence(
            "LFI_AArch64_AddrReg_Load_ImmDisp_2024_x18",
            "aarch64-unknown-linux-gnu",
            [
                "add x18, x21, w1, uxtw",
                "ldr x0, [x18, #16]",
            ],
        ),
        analyze_sequence(
            "LFI_AArch64_AddrReg_Load_ImmDisp_2025_x28",
            "aarch64-unknown-linux-gnu",
            [
                "add x28, x27, w1, uxtw",
                "ldr x0, [x28, #16]",
            ],
        ),
        # 3. Indirect Branch / Return Sandboxing
        analyze_sequence(
            "NaCl_x86_64_32B_Bundle_Indirect_Jump",
            "x86_64-unknown-linux-gnu",
            [
                "andl $0xffffffe0, %eax",
                "addq %r15, %rax",
                "jmpq *%rax",
            ],
        ),
        analyze_sequence(
            "LFI_x86_64_Macroinst_Indirect_Jump",
            "x86_64-unknown-linux-gnu",
            [
                "andl $0xffffffe0, %eax",
                "leaq (%r14, %rax), %r11",
                "jmpq *%r11",
            ],
        ),
        analyze_sequence(
            "LFI_AArch64_BundleFree_Indirect_Jump_x21_x18",
            "aarch64-unknown-linux-gnu",
            [
                "add x18, x21, w1, uxtw",
                "br x18",
            ],
        ),
        analyze_sequence(
            "LFI_AArch64_BundleFree_Return_x27_x30",
            "aarch64-unknown-linux-gnu",
            [
                "add x30, x27, w30, uxtw",
                "ret",
            ],
        ),
        analyze_sequence(
            "LFI_AArch64_Metered_16B_Bundle_Indirect_Jump",
            "aarch64-unknown-linux-gnu",
            [
                "add x18, x21, w1, uxtw",
                "bic x24, x18, #0xf",
                "br x24",
            ],
        ),
        # 4. Runtime Call Trampoline (Exiting sandbox to host kernel/runtime)
        analyze_sequence(
            "LFI_AArch64_RuntimeCall_Trampoline_2024_x21",
            "aarch64-unknown-linux-gnu",
            [
                "mov w22, w30",
                "ldr x30, [x21]",
                "blr x30",
                "add x30, x21, w22, uxtw",
            ],
        ),
        analyze_sequence(
            "LFI_AArch64_RuntimeCall_Trampoline_2025_x27",
            "aarch64-unknown-linux-gnu",
            [
                "mov w26, w30",
                "ldr x30, [x27]",
                "blr x30",
                "add x30, x27, w26, uxtw",
            ],
        ),
        analyze_sequence(
            "LFI_x86_64_RuntimeCall_Trampoline",
            "x86_64-unknown-linux-gnu",
            [
                "callq *(%r14)",
                ".byte 0x0f, 0x1f, 0x44, 0x00, 0x00",
                ".byte 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
                ".byte 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
                ".byte 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00",
            ],
        ),
        # 5. Post-Link Segment Prefix Padding vs Multi-byte NOPs on x86-64
        analyze_sequence(
            "LFI_x86_64_Postlink_CS_Prefix_Padding_Example",
            "x86_64-unknown-linux-gnu",
            [
                "addq $8, %rax",
                ".byte 0x2e, 0x2e, 0x2e, 0x2e, 0x48, 0x83, 0xc0, 0x08",
            ],
        ),
        # 6. Ring-0 Wasm Guard-Page Linear Memory Access (Nebulet / Cranelift)
        analyze_sequence(
            "Nebulet_Ring0_Wasm_GuardPage_Load_x86_64",
            "x86_64-unknown-linux-gnu",
            [
                "movl %eax, %eax",
                "movq 16(%rdi, %rax), %rcx",
            ],
        ),
        analyze_sequence(
            "BranchChecked_Software_BoundsCheck_With_LFENCE_x86_64",
            "x86_64-unknown-linux-gnu",
            [
                "movl %eax, %eax",
                "cmpq %rsi, %rax",
                "jae 1f",
                "lfence",
                "movq (%rdi, %rax), %rcx",
                "1: ud2",
            ],
        ),
    ]

    output_path = Path(__file__).with_name("sfi_encoding_probe_results.json")
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(sequences, f, indent=2)

    print(f"Wrote {len(sequences)} analyzed sequences to {output_path.name}\n")
    print(f"{'Sequence Name':<52} | {'Arch':<7} | {'Insts':<5} | {'Bytes':<5} | {'Encoding'}")
    print("-" * 120)
    for seq in sequences:
        arch = "x86-64" if "x86_64" in seq["triple"] else "aarch64"
        enc = " ; ".join(" ".join(i["bytes"]) for i in seq["instructions"])
        print(f"{seq['name']:<52} | {arch:<7} | {seq['instruction_count']:<5} | {seq['total_bytes']:<5} | {enc}")


if __name__ == "__main__":
    main()
