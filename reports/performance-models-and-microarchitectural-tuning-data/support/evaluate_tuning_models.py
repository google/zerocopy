#!/usr/bin/env python3
"""Reproducible probe for microarchitectural tuning models and llvm-mca vs BHive."""
import json
import os
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SUMMARY = HERE / "tuning_models_summary.json"

X86_KERNELS = """
# LLVM-MCA-BEGIN k1_indep_alu
addq %rcx, %rax
addq %rsi, %rdx
addq %r9, %r8
addq %r11, %r10
# LLVM-MCA-END
# LLVM-MCA-BEGIN k2_dep_alu_chain
addq %rbx, %rax
addq %rcx, %rax
addq %rdx, %rax
addq %rsi, %rax
# LLVM-MCA-END
# LLVM-MCA-BEGIN k3_zero_idiom_xor
xorl %eax, %eax
addq %rbx, %rax
# LLVM-MCA-END
# LLVM-MCA-BEGIN k4_false_dep_mov0
movl $0, %eax
addq %rbx, %rax
# LLVM-MCA-END
# LLVM-MCA-BEGIN k5_simd_fma_dep
vfmadd213ps %xmm1, %xmm2, %xmm0
vfmadd213ps %xmm1, %xmm2, %xmm0
# LLVM-MCA-END
# LLVM-MCA-BEGIN k6_idiv64
xorl %edx, %edx
idivq %rcx
# LLVM-MCA-END
"""

AARCH64_KERNELS = """
// LLVM-MCA-BEGIN k1_indep_alu
add x0, x0, x1
add x2, x2, x3
add x4, x4, x5
add x6, x6, x7
// LLVM-MCA-END
// LLVM-MCA-BEGIN k2_dep_alu_chain
add x0, x0, x1
add x0, x0, x2
add x0, x0, x3
add x0, x0, x4
// LLVM-MCA-END
// LLVM-MCA-BEGIN k3_mov_zero
mov x0, #0
add x0, x0, x1
// LLVM-MCA-END
// LLVM-MCA-BEGIN k4_simd_fmla_dep
fmla v0.4s, v1.4s, v2.4s
fmla v0.4s, v1.4s, v2.4s
// LLVM-MCA-END
// LLVM-MCA-BEGIN k5_sdiv64
sdiv x0, x1, x2
// LLVM-MCA-END
"""


def main() -> int:
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["x86_sched_files_count"] == 22, data["x86_sched_files_count"]
    assert data["aarch64_sched_files_count"] == 37, data["aarch64_sched_files_count"]
    print(f"Verified TableGen summary: {data['x86_sched_files_count']} X86 files ({data['x86_sched_total_lines']} lines), "
          f"{data['aarch64_sched_files_count']} AArch64 files ({data['aarch64_sched_total_lines']} lines)")
    for cpu, stats in data["bhive_600_sample_llvm_mca_evaluation"].items():
        print(f"BHive 600-block sample ({cpu}): overall MAPE={stats['mape_pct']}%, "
              f"non-aliasing MAPE={stats['non_may_alias_mape_pct']}%, Kendall tau={stats['kendall_tau']}")
    mca = "/usr/bin/llvm-mca"
    if os.path.exists(mca):
        apple_outputs = {}
        for cpu in ["apple-a7", "apple-m1", "apple-m2", "apple-m3", "apple-m4"]:
            res = subprocess.run(
                [mca, "-mtriple=aarch64-unknown-linux-gnu", f"-mcpu={cpu}", "-iterations=100", "--json"],
                input=AARCH64_KERNELS, capture_output=True, text=True, check=True
            )
            j = json.loads(res.stdout)
            apple_outputs[cpu] = [r["SummaryView"]["TotalCycles"] for r in j["CodeRegions"]]
        assert len({tuple(v) for v in apple_outputs.values()}) == 1, apple_outputs
        print("Confirmed CycloneModel identity across apple-a7..apple-m4:", apple_outputs["apple-m1"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
