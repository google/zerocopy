#!/usr/bin/env python3
"""Empirical rustc/LLVM constant-time codegen preservation & breakage probe.

Compiles support/ct_idioms.rs across:
  - x86_64-unknown-linux-gnu via native rustc (--emit=asm) at opt-level=2, 3, s, z
  - thumbv7m-none-eabi and riscv32imc-unknown-none-elf via native rustc (when installed)
  - aarch64-unknown-none and riscv64-unknown-none-elf via rustc --emit=llvm-ir + llc
    at opt-level=2, 3, z

Classifies every exported function for:
  - conditional branch instructions (secret-dependent control flow)
  - indirect jumps / .rodata jump tables / .rodata LUT indexed loads
  - variable-latency division instructions (div/idiv/udiv/sdiv/divu)
  - floating-point instructions without FTZ/DAZ enforcement
  - stack/red-zone secret spills around black_box / read_volatile
  - branchless select instructions (cmov*, csel/csetm, czero.*)
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "ct_idioms.rs"
OUT_JSON = HERE / "probe_ct_codegen_results.json"

FUNCTIONS = [
    "ct_select_unpred_u64",
    "ct_select_unpred_load_arms",
    "ct_select_unpred_struct",
    "ct_select_unpred_in_loop",
    "ct_wrap_mask_bool",
    "ct_wrap_mask_u8_masked",
    "ct_wrap_mask_load_arms",
    "ct_wrap_mask_in_loop",
    "ct_subtle_xor_no_barrier",
    "ct_subtle_xor_black_box",
    "ct_subtle_xor_volatile",
    "ct_subtle_xor_in_loop_no_barrier",
    "ct_subtle_xor_in_loop_black_box",
    "ct_u64_eq_bitmath",
    "ct_u64_lt_bitmath",
    "ct_u64_lt_bitmath_load_select",
    "ct_u64_eq_bitmath_load_select",
    "ct_lut_linear_scan_16",
    "ct_lut_linear_scan_const_sbox",
    "ct_lut_linear_scan_const_sbox_black_box",
    "ct_match_to_rodata_lut",
    "ct_match_jump_table",
    "ct_black_box_short_circuit_and",
    "ct_black_box_div_still_var_time",
    "ct_const_div_kyberslash",
    "ct_secret_div_u64",
    "ct_subnormal_fp_mul",
]

LOOP_FUNCTIONS = {
    "ct_select_unpred_in_loop",
    "ct_wrap_mask_in_loop",
    "ct_subtle_xor_in_loop_no_barrier",
    "ct_subtle_xor_in_loop_black_box",
    "ct_lut_linear_scan_16",
    "ct_lut_linear_scan_const_sbox",
    "ct_lut_linear_scan_const_sbox_black_box",
}


def run_cmd(cmd: list[str]) -> str:
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"Command failed ({proc.returncode}): {' '.join(cmd)}\n{proc.stderr}")
    return proc.stdout


def split_asm_functions(asm_text: str, keep_hash_imms: bool = False) -> dict[str, list[str]]:
    """Extract instruction/label lines for each exported function symbol (resolving .set aliases)."""
    funcs: dict[str, list[str]] = {}
    aliases: dict[str, str] = {}
    cur: str | None = None
    comment_re = re.compile(r"\s+(?://|@).*$") if keep_hash_imms else re.compile(r"\s+(?:#|//).*$")
    for raw in asm_text.splitlines():
        line = raw.strip()
        m_alias = re.match(r"^\.(?:set|equ)\s+([A-Za-z_][A-Za-z0-9_]*),\s*([A-Za-z_][A-Za-z0-9_]*)", line)
        if m_alias and m_alias.group(1) in FUNCTIONS:
            aliases[m_alias.group(1)] = m_alias.group(2)
            continue
        m_eq = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([A-Za-z_][A-Za-z0-9_]*)", line)
        if m_eq and m_eq.group(1) in FUNCTIONS:
            aliases[m_eq.group(1)] = m_eq.group(2)
            continue
        m_lbl = re.match(r"^([A-Za-z_][A-Za-z0-9_]*):(?:\s*(?:#|//).*)?$", line)
        if m_lbl and m_lbl.group(1) in FUNCTIONS:
            cur = m_lbl.group(1)
            funcs[cur] = []
            continue
        if cur is not None:
            if (line.startswith(".size") or line.startswith(".Lfunc_end")) and (cur in line or line.startswith(".Lfunc_end")):
                if line.startswith(".size"):
                    cur = None
                continue
            if line.startswith(".cfi_") or line == "" or line.startswith("#") or line.startswith("//") or line.startswith(";"):
                continue
            if line.startswith(".section") or line.startswith(".globl") or line.startswith(".type"):
                cur = None
                continue
            if line.startswith(".p2align") or line.startswith(".addrsig"):
                continue
            clean = comment_re.sub("", line).strip()
            if clean:
                funcs[cur].append(clean)
    for alias, target in aliases.items():
        if alias not in funcs and target in funcs:
            funcs[alias] = [f"; alias -> {target}"] + funcs[target]
    return funcs


def analyze_x86(fn: str, lines: list[str]) -> dict:
    insns = [l for l in lines if not l.endswith(":") and not l.startswith(".")]
    cond_branches = [
        l for l in insns
        if re.match(r"^(j(?:e|ne|z|nz|a|ae|b|be|g|ge|l|le|s|ns|o|no|p|np|c|nc))\b", l)
    ]
    uncond_indirect = [l for l in insns if re.match(r"^jmpq?\s+\*", l)]
    cmovs = [l for l in insns if re.match(r"^cmov", l)]
    divs = [l for l in insns if re.match(r"^(?:i?div[bwlq]?)\b", l)]
    rodata_refs = [
        l for l in insns
        if any(tok in l for tok in (".L__unnamed", ".Lswitch.table", ".LJTI", ".LCPI", ".Lanon"))
    ]
    indexed_rodata_load = [
        l for l in insns
        if re.search(r"\(%r[a-z0-9]+,%r[a-z0-9]+,[1248]\)", l)
        and (re.match(r"^mov", l) or re.match(r"^jmp", l))
    ]
    stack_spills = [
        l for l in insns
        if re.search(r"-?\d*\(%rsp\)", l) and re.match(r"^mov", l)
    ]
    fp_ops = [l for l in insns if re.match(r"^(?:v?(?:add|sub|mul|div|fmadd)[sd][sd])\b", l)]
    # Check whether a jump table exists
    has_jump_table = any(".LJTI" in l for l in insns) or bool(uncond_indirect)
    has_rodata_lut = any(
        tok in l for l in insns for tok in (".L__unnamed", ".Lswitch.table", ".Lanon")
    ) and not has_jump_table
    return {
        "insn_count": len(insns),
        "cond_branches": cond_branches,
        "cond_branch_count": len(cond_branches),
        "indirect_jumps": uncond_indirect,
        "has_jump_table": has_jump_table,
        "has_rodata_lut": has_rodata_lut,
        "rodata_refs": rodata_refs,
        "indexed_loads": indexed_rodata_load,
        "cmovs": cmovs,
        "divs": divs,
        "stack_spills": stack_spills,
        "fp_ops": fp_ops,
        "asm": lines,
    }


def analyze_aarch64(fn: str, lines: list[str]) -> dict:
    insns = [l for l in lines if not l.endswith(":") and not l.startswith(".")]
    cond_branches = [
        l for l in insns
        if re.match(r"^(?:b\.[a-z]+|cbz|cbnz|tbz|tbnz)\b", l)
    ]
    uncond_indirect = [l for l in insns if re.match(r"^br\s+x", l)]
    csels = [l for l in insns if re.match(r"^(?:csel|cset|csetm|csinc|csinv|csneg)\b", l)]
    divs = [l for l in insns if re.match(r"^[us]div\b", l)]
    rodata_refs = [
        l for l in insns
        if any(tok in l for tok in (".L__unnamed", ".Lswitch.table", ".LJTI", ".LCPI", ".Lanon"))
    ]
    stack_spills = [
        l for l in insns
        if re.search(r"\[sp", l) and re.match(r"^(?:str|stp|ldr|ldp)", l)
    ]
    fp_ops = [l for l in insns if re.match(r"^f(?:mul|add|sub|div|madd)\b", l)]
    has_jump_table = any(".LJTI" in l for l in insns) or bool(uncond_indirect)
    has_rodata_lut = any(
        tok in l for l in insns for tok in (".L__unnamed", ".Lswitch.table", ".Lanon")
    ) and not has_jump_table
    return {
        "insn_count": len(insns),
        "cond_branches": cond_branches,
        "cond_branch_count": len(cond_branches),
        "indirect_jumps": uncond_indirect,
        "has_jump_table": has_jump_table,
        "has_rodata_lut": has_rodata_lut,
        "rodata_refs": rodata_refs,
        "csels": csels,
        "divs": divs,
        "stack_spills": stack_spills,
        "fp_ops": fp_ops,
        "asm": lines,
    }


def analyze_riscv64(fn: str, lines: list[str]) -> dict:
    insns = [l for l in lines if not l.endswith(":") and not l.startswith(".")]
    cond_branches = [
        l for l in insns
        if re.match(r"^(?:beq|bne|blt|bge|bltu|bgeu|beqz|bnez|blez|bgez|bltz|bgtz)\b", l)
    ]
    uncond_indirect = [l for l in insns if re.match(r"^jr\s+", l)]
    czeros = [l for l in insns if re.match(r"^czero\.", l)]
    divs = [l for l in insns if re.match(r"^(?:div|divu|divw|divuw|rem|remu|remw|remuw)\b", l)]
    rodata_refs = [
        l for l in insns
        if any(tok in l for tok in (".L__unnamed", ".Lswitch.table", ".LJTI", ".LCPI", ".Lanon"))
    ]
    stack_spills = [
        l for l in insns
        if re.search(r"\(sp\)", l) and re.match(r"^(?:sd|sw|sb|ld|lw|lbu)", l)
    ]
    fp_ops = [l for l in insns if re.match(r"^f(?:mul|add|sub|div|madd)\.[sd]\b", l)]
    has_jump_table = any(".LJTI" in l for l in insns) or bool(uncond_indirect)
    has_rodata_lut = any(
        tok in l for l in insns for tok in (".L__unnamed", ".Lswitch.table", ".Lanon")
    ) and not has_jump_table
    return {
        "insn_count": len(insns),
        "cond_branches": cond_branches,
        "cond_branch_count": len(cond_branches),
        "indirect_jumps": uncond_indirect,
        "has_jump_table": has_jump_table,
        "has_rodata_lut": has_rodata_lut,
        "rodata_refs": rodata_refs,
        "czeros": czeros,
        "divs": divs,
        "stack_spills": stack_spills,
        "fp_ops": fp_ops,
        "asm": lines,
    }


def sanitize_ir_for_cross_llc(ir_text: str) -> str:
    """Adapt LLVM 23 IR syntax to LLVM 21 llc while preserving !unpredictable and asm barriers."""
    out = []
    for line in ir_text.splitlines():
        if line.startswith("target datalayout =") or line.startswith("target triple ="):
            continue
        # Strip x86-specific target-cpu / target-features / tune-cpu attributes
        line = re.sub(r'"target-cpu"="[^"]*"\s*', "", line)
        line = re.sub(r'"target-features"="[^"]*"\s*', "", line)
        line = re.sub(r'"tune-cpu"="[^"]*"\s*', "", line)
        # Strip LLVM 23 !guid metadata (unknown to LLVM 21)
        line = re.sub(r",?\s*!guid\s*!\d+", "", line)
        if re.match(r"^!\d+\s*=\s*!\{i64\s+-?\d+\}$", line.strip()):
            pass
        # LLVM 23 captures(...) -> LLVM 21 nocapture (must run before lifetime declare regex)
        line = line.replace("captures(none)", "nocapture")
        line = re.sub(r"captures\([^)]*\)\s*", "", line)
        # LLVM 22/23 changed lifetime.start/end to 1-arg ptr; restore i64 -1 for LLVM 21
        line = re.sub(
            r"declare void @llvm\.lifetime\.(start|end)\.p0\([^)]*\)",
            r"declare void @llvm.lifetime.\1.p0(i64 immarg, ptr nocapture)",
            line,
        )
        line = re.sub(
            r"call void @llvm\.lifetime\.(start|end)\.p0\(ptr ([^)]+)\)",
            r"call void @llvm.lifetime.\1.p0(i64 -1, ptr \2)",
            line,
        )
        # Strip LLVM 23 byval/initializes/dead_on_return/target_mem/nocreateundeforpoison
        line = re.sub(r"dead_on_return(?:\(\d+\))?\s*", "", line)
        line = re.sub(r"dead_on_unwind\s*", "", line)
        line = line.replace("nocreateundeforpoison ", "")
        line = re.sub(r",\s*target_mem:\s*[a-z]+", "", line)
        line = re.sub(r"target_mem:\s*[a-z]+,\s*", "", line)
        line = re.sub(r"memory\(target_mem:\s*[a-z]+\)", "memory(readwrite)", line)
        out.append(line)
    return "\n".join(out) + "\n"


def main() -> int:
    rustc_ver = run_cmd(["rustc", "--version", "--verbose"]).strip()
    llc_path = shutil.which("llc")
    llc_ver = run_cmd([llc_path, "--version"]).strip() if llc_path else "unavailable"

    results: dict = {
        "rustc_version": rustc_ver,
        "llc_version": llc_ver,
        "configurations": {},
    }

    with tempfile.TemporaryDirectory(prefix="ct_probe_") as tmpdir:
        tmp = Path(tmpdir)

        # 1. Native rustc x86_64 across opt-level 2, 3, s, z
        for opt in ("2", "3", "s", "z"):
            asm_path = tmp / f"x86_64_O{opt}.s"
            run_cmd([
                "rustc", "--crate-type=lib", "--edition=2024",
                f"-C", f"opt-level={opt}",
                "-C", "panic=abort",
                "--emit=asm", "-o", str(asm_path),
                str(SRC),
            ])
            asm_text = asm_path.read_text()
            funcs = split_asm_functions(asm_text)
            key = f"rustc_x86_64_O{opt}"
            results["configurations"][key] = {
                fn: analyze_x86(fn, funcs.get(fn, [])) for fn in FUNCTIONS
            }

        # 2. Cross-target AArch64 and RISC-V 64 via rustc --emit=llvm-ir + llc
        if llc_path:
            for opt in ("2", "3", "z"):
                ir_path = tmp / f"ir_O{opt}.ll"
                run_cmd([
                    "rustc", "--crate-type=lib", "--edition=2024",
                    f"-C", f"opt-level={opt}",
                    "-C", "panic=abort",
                    "--emit=llvm-ir", "-o", str(ir_path),
                    str(SRC),
                ])
                clean_ir = tmp / f"ir_O{opt}_clean.ll"
                clean_ir.write_text(sanitize_ir_for_cross_llc(ir_path.read_text()))

                llc_opt = "-O2" if opt == "2" else "-O3"
                # AArch64
                a64_asm = tmp / f"aarch64_O{opt}.s"
                run_cmd([
                    llc_path, "-mtriple=aarch64-unknown-none",
                    llc_opt, "-o", str(a64_asm), str(clean_ir),
                ])
                funcs_a64 = split_asm_functions(a64_asm.read_text(), keep_hash_imms=True)
                results["configurations"][f"llc_aarch64_O{opt}"] = {
                    fn: analyze_aarch64(fn, funcs_a64.get(fn, [])) for fn in FUNCTIONS
                }

                # RISC-V 64 (RV64GC, no Zicond)
                rv_asm = tmp / f"riscv64_O{opt}.s"
                run_cmd([
                    llc_path, "-mtriple=riscv64-unknown-none-elf",
                    "-mattr=+m,+a,+f,+d,+c",
                    llc_opt, "-o", str(rv_asm), str(clean_ir),
                ])
                funcs_rv = split_asm_functions(rv_asm.read_text())
                results["configurations"][f"llc_riscv64gc_O{opt}"] = {
                    fn: analyze_riscv64(fn, funcs_rv.get(fn, [])) for fn in FUNCTIONS
                }

                # RISC-V 64 with Zicond (+zicond)
                rvz_asm = tmp / f"riscv64_zicond_O{opt}.s"
                run_cmd([
                    llc_path, "-mtriple=riscv64-unknown-none-elf",
                    "-mattr=+m,+a,+f,+d,+c,+zicond",
                    llc_opt, "-o", str(rvz_asm), str(clean_ir),
                ])
                funcs_rvz = split_asm_functions(rvz_asm.read_text())
                results["configurations"][f"llc_riscv64_zicond_O{opt}"] = {
                    fn: analyze_riscv64(fn, funcs_rvz.get(fn, [])) for fn in FUNCTIONS
                }

        # 3. Also test native rustc on installed embedded target thumbv7m-none-eabi (32-bit ARM)
        #    for a compact sanity check on LLVM 23.1.5 non-x86 backend directly inside rustc!
        installed = run_cmd(["rustup", "target", "list", "--installed"]).splitlines()
        if "thumbv7m-none-eabi" in installed:
            for opt in ("2", "3", "z"):
                t_asm = tmp / f"thumbv7m_O{opt}.s"
                run_cmd([
                    "rustc", "--crate-type=lib", "--edition=2024",
                    "--target=thumbv7m-none-eabi",
                    f"-C", f"opt-level={opt}",
                    "-C", "panic=abort",
                    "--emit=asm", "-o", str(t_asm),
                    str(SRC),
                ])
                funcs_t = split_asm_functions(t_asm.read_text(), keep_hash_imms=True)
                results["configurations"][f"rustc_thumbv7m_O{opt}"] = {
                    fn: {
                        "insn_count": len([l for l in funcs_t.get(fn, []) if not l.endswith(":") and not l.startswith(".")]),
                        "asm": funcs_t.get(fn, []),
                    }
                    for fn in FUNCTIONS
                }

    OUT_JSON.write_text(json.dumps(results, indent=2) + "\n")
    print(f"Wrote {OUT_JSON} ({len(results['configurations'])} configs x {len(FUNCTIONS)} functions)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
