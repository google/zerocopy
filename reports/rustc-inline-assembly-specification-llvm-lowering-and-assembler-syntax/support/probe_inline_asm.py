#!/usr/bin/env python3
"""M5 Probe: Extract complete inline assembly register classes, modifiers, clobber_abi, reserved registers, options, and LLVM lowering from rustc 1.99.1 and LLVM 23.1.1."""

import json
import re
from pathlib import Path

S1991 = Path("/tmp/rust-1.99.1")
N1112 = Path("/tmp/rust-nightly-2026-11-12")
LLVM_DIR = Path("/tmp/probe_out")
DATA_DIR = Path("/tmp/probe_out")
DATA_DIR.mkdir(parents=True, exist_ok=True)


def parse_asm_arch_file(path: Path):
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    # Extract enum <Arch>InlineAsmRegClass variants
    reg_classes = []
    m_rc = re.search(r"pub enum \w+InlineAsmRegClass \{([^}]+)\}", text)
    if m_rc:
        for line in m_rc.group(1).splitlines():
            s = line.strip().rstrip(",")
            if s and not s.startswith("//") and not s.startswith("#"):
                reg_classes.append(s)

    # Extract supported_types match arms
    supported_types_section = ""
    m_st = re.search(r"fn supported_types\([\s\S]+?\n    \}", text)
    if m_st:
        supported_types_section = m_st.group(0)

    # Extract def_reg_class / Regs definitions
    regs_enum_section = ""
    m_re = re.search(r"pub enum \w+InlineAsmReg \{[\s\S]+?\n\}", text)
    if m_re:
        regs_enum_section = m_re.group(0)

    # Count explicit registers and reserved registers
    explicit_regs = re.findall(r'^\s+([a-zA-Z0-9_]+):\s*\[', regs_enum_section, re.M)
    reserved_reasons = re.findall(r'#\[error\s*=\s*"([^"]+)"\]', regs_enum_section)

    return {
        "file": str(path.relative_to(S1991)),
        "lines": len(lines),
        "reg_classes": reg_classes,
        "explicit_reg_count": len(explicit_regs),
        "explicit_regs": explicit_regs,
        "reserved_reasons": sorted(set(reserved_reasons)),
        "supported_types_source": supported_types_section,
    }


def parse_asm_mod():
    mod_path = S1991 / "compiler/rustc_target/src/asm/mod.rs"
    text = mod_path.read_text(encoding="utf-8")
    arches = re.findall(r"pub enum InlineAsmArch \{([^}]+)\}", text)
    arch_list = []
    if arches:
        for l in arches[0].splitlines():
            s = l.strip().rstrip(",")
            if s and not s.startswith("//") and not s.startswith("#"):
                arch_list.append(s)

    clobber_section = ""
    m_clob = re.search(r"pub fn clobber_abi\([\s\S]+?\n    \}", text)
    if m_clob:
        clobber_section = m_clob.group(0)

    return {
        "inline_asm_arches": arch_list,
        "clobber_abi_source": clobber_section,
    }


def parse_llvm_asm_directives():
    generic_cpp = (LLVM_DIR / "llvm__lib__MC__MCParser__AsmParser.cpp").read_text(encoding="utf-8")
    x86_cpp = (LLVM_DIR / "llvm__lib__Target__X86__AsmParser__X86AsmParser.cpp").read_text(encoding="utf-8")
    a64_cpp = (LLVM_DIR / "llvm__lib__Target__AArch64__AsmParser__AArch64AsmParser.cpp").read_text(encoding="utf-8")

    gen_dirs = sorted(set(re.findall(r'"(\.[a-z0-9_]+)"', generic_cpp)))
    x86_dirs = sorted(set(re.findall(r'"(\.[a-z0-9_]+)"', x86_cpp)))
    a64_dirs = sorted(set(re.findall(r'"(\.[a-z0-9_]+)"', a64_cpp)))

    return {
        "generic_mc_directives_count": len(gen_dirs),
        "generic_mc_directives": gen_dirs,
        "x86_specific_directives_count": len(x86_dirs),
        "x86_specific_directives": x86_dirs,
        "aarch64_specific_directives_count": len(a64_dirs),
        "aarch64_specific_directives": a64_dirs,
    }


def main():
    asm_dir = S1991 / "compiler/rustc_target/src/asm"
    x86_info = parse_asm_arch_file(asm_dir / "x86.rs")
    a64_info = parse_asm_arch_file(asm_dir / "aarch64.rs")
    arm_info = parse_asm_arch_file(asm_dir / "arm.rs")
    rv_info = parse_asm_arch_file(asm_dir / "riscv.rs")
    mod_info = parse_asm_mod()
    mc_info = parse_llvm_asm_directives()

    res = {
        "asm_mod": mod_info,
        "x86": x86_info,
        "aarch64": a64_info,
        "arm": arm_info,
        "riscv": rv_info,
        "llvm_mc_directives": mc_info,
    }
    (DATA_DIR / "m5_inline_asm_spec.json").write_text(json.dumps(res, indent=2), encoding="utf-8")
    print("InlineAsmArch count:", len(mod_info["inline_asm_arches"]), mod_info["inline_asm_arches"])
    print("x86 reg classes:", x86_info["reg_classes"])
    print("x86 explicit regs:", x86_info["explicit_reg_count"], "reserved reasons:", x86_info["reserved_reasons"])
    print("aarch64 reg classes:", a64_info["reg_classes"])
    print("aarch64 explicit regs:", a64_info["explicit_reg_count"], "reserved reasons:", a64_info["reserved_reasons"])
    print("LLVM MC directives counts:", mc_info["generic_mc_directives_count"], mc_info["x86_specific_directives_count"], mc_info["aarch64_specific_directives_count"])


if __name__ == "__main__":
    main()
