#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Exhaustive census of asm!, naked_asm!, and global_asm! across rustc 1.99.1 library/{core,alloc,std,unwind,stdarch} and compiler/rustc_builtin_macros."""

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_RUST_SRC = Path(
    os.environ.get("RUST_SRC_ROOT", os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust"))
)

ASM_MACRO_RE = re.compile(
    r"\b(?:core::arch::|std::arch::)?(asm|naked_asm|global_asm)!\s*\(",
    re.MULTILINE,
)

CFG_ARCH_RE = re.compile(
    r'target_arch\s*=\s*"([^"]+)"'
)

OPTIONS_RE = re.compile(
    r"\boptions\s*\(([^)]+)\)"
)

OPERAND_SPEC_RE = re.compile(
    r"\b(inlateout|lateout|inout|in|out|sym|const|label|clobber_abi)\s*(?:\(\s*([^)]*)\s*\))?"
)

PLACEHOLDER_MOD_RE = re.compile(
    r"\{([a-zA-Z0-9_]*)(?::([a-zA-Z0-9_]+))?\}"
)

STRING_LIT_RE = re.compile(
    r'(?:r#*".*?"#*|"(?:\\.|[^"\\])*")',
    re.DOTALL,
)

KNOWN_DIRECTIVES = {
    ".byte", ".2byte", ".short", ".4byte", ".long", ".8byte", ".quad",
    ".ascii", ".asciz", ".string", ".balign", ".p2align", ".align",
    ".section", ".pushsection", ".popsection", ".text", ".data", ".rodata",
    ".globl", ".global", ".local", ".hidden", ".weak", ".private_extern",
    ".type", ".size", ".cfi_startproc", ".cfi_endproc", ".cfi_def_cfa",
    ".cfi_def_cfa_offset", ".cfi_def_cfa_register", ".cfi_adjust_cfa_offset",
    ".cfi_offset", ".cfi_restore", ".cfi_undefined", ".cfi_escape",
    ".cfi_personality", ".cfi_lsda", ".seh_proc", ".seh_endproc",
    ".seh_pushreg", ".seh_savereg", ".seh_stackalloc", ".seh_endprologue",
    ".inst", ".insn", ".arch", ".cpu", ".fpu", ".syntax", ".thumb", ".code",
    ".set", ".equ", ".macro", ".endm", ".ifdef", ".ifndef", ".else", ".endif",
}

TIER1_ARCHES = {"x86_64", "x86", "aarch64"}


def extract_balanced_call(text: str, open_paren_idx: int) -> str:
    depth = 0
    in_str = False
    escape = False
    i = open_paren_idx
    n = len(text)
    while i < n:
        ch = text[i]
        if in_str:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    return text[open_paren_idx + 1 : i]
        i += 1
    return text[open_paren_idx + 1 :]


def infer_file_arches(rel_path: str, file_text: str) -> list[str]:
    arches = set()
    low = rel_path.lower()
    for a in ("x86_64", "x86", "aarch64", "arm", "riscv", "loongarch", "powerpc", "s390x", "mips", "wasm", "hexagon", "nvptx", "avr", "msp430", "sparc", "csky", "m68k"):
        if f"/{a}" in low or f"_{a}" in low or f"{a}.rs" in low:
            arches.add(a)
    for m in CFG_ARCH_RE.finditer(file_text):
        arches.add(m.group(1))
    if not arches:
        return ["multi_or_generic"]
    return sorted(arches)


def parse_asm_lines(body: str) -> tuple[list[str], list[str], list[str], list[str]]:
    mnemonics = []
    directives = []
    modifiers = []
    local_labels = []
    # Extract string literals before the first operand specifier
    first_op = OPERAND_SPEC_RE.search(body)
    tmpl_region = body[: first_op.start()] if first_op else body
    for lit_m in STRING_LIT_RE.finditer(tmpl_region):
        raw = lit_m.group(0)
        if raw.startswith("r"):
            hashes = len(raw) - len(raw.lstrip("r#")) - 1
            content = raw[1 + hashes + 1 : -(hashes + 1)]
        else:
            content = raw[1:-1]
        for pm in PLACEHOLDER_MOD_RE.finditer(content):
            if pm.group(2):
                modifiers.append(f":{pm.group(2)}")
        # Split into lines / semicolon statements
        content_clean = content.replace("\\n", "\n").replace("\\t", " ")
        for raw_line in re.split(r"[\n;]", content_clean):
            line = raw_line.strip()
            if not line or line.startswith(("//", "#", "/*", "*")):
                continue
            # Check for label prefix `0:`, `1:`, `.Lfoo:`
            lbl_m = re.match(r"^([0-9]+:|\.[a-zA-Z0-9_.$]+:|[a-zA-Z0-9_.$]+:)\s*(.*)$", line)
            if lbl_m:
                local_labels.append(lbl_m.group(1).rstrip(":"))
                line = lbl_m.group(2).strip()
                if not line:
                    continue
            tok = line.split()[0].lower().rstrip(",")
            if tok.startswith("."):
                directives.append(tok)
            elif re.match(r"^[a-z][a-z0-9._]*$", tok):
                mnemonics.append(tok)
    return mnemonics, directives, modifiers, local_labels


def scan_repository(rust_src: Path) -> dict:
    search_roots = [
        rust_src / "library" / "core",
        rust_src / "library" / "alloc",
        rust_src / "library" / "std",
        rust_src / "library" / "unwind",
        rust_src / "library" / "panic_unwind",
        rust_src / "library" / "backtrace",
        rust_src / "library" / "portable-simd",
        rust_src / "library" / "stdarch",
        rust_src / "library" / "std_detect",
        rust_src / "library" / "compiler-builtins",
        rust_src / "library" / "rtstartup",
    ]
    macro_counts = Counter()
    by_subcrate = defaultdict(lambda: Counter())
    by_arch = defaultdict(lambda: Counter())
    option_counts = Counter()
    operand_kind_counts = Counter()
    reg_class_counts = Counter()
    modifier_counts = Counter()
    directive_counts = Counter()
    mnemonic_counts = Counter()
    tier1_mnemonic_counts = defaultdict(lambda: Counter())
    local_label_kinds = Counter()
    sites = []

    for root in search_roots:
        if not root.exists():
            continue
        subcrate = root.name
        for rs_file in sorted(root.rglob("*.rs")):
            rel = str(rs_file.relative_to(rust_src))
            if "/tests/" in rel or "/benches/" in rel:
                continue
            try:
                text = rs_file.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            file_arches = infer_file_arches(rel, text)
            for m in ASM_MACRO_RE.finditer(text):
                macro_kind = m.group(1)
                open_paren = m.end() - 1
                body = extract_balanced_call(text, open_paren)
                line_no = text.count("\n", 0, m.start()) + 1

                macro_counts[macro_kind] += 1
                by_subcrate[subcrate][macro_kind] += 1
                for a in file_arches:
                    by_arch[a][macro_kind] += 1

                opts = []
                for om in OPTIONS_RE.finditer(body):
                    for tok in om.group(1).split(","):
                        t = tok.strip()
                        if t:
                            opts.append(t)
                            option_counts[t] += 1

                for opm in OPERAND_SPEC_RE.finditer(body):
                    op_kind = opm.group(1)
                    operand_kind_counts[op_kind] += 1
                    reg_arg = (opm.group(2) or "").strip()
                    if reg_arg and op_kind in ("in", "out", "inout", "lateout", "inlateout", "clobber_abi"):
                        reg_class_counts[reg_arg] += 1

                mnems, dirs, mods, lbls = parse_asm_lines(body)
                for mn in mnems:
                    mnemonic_counts[mn] += 1
                    for a in file_arches:
                        if a in TIER1_ARCHES or a == "multi_or_generic":
                            tier1_mnemonic_counts[a][mn] += 1
                for d in dirs:
                    directive_counts[d] += 1
                for md in mods:
                    modifier_counts[md] += 1
                for lb in lbls:
                    if lb.isdigit():
                        local_label_kinds["numeric_local_label"] += 1
                    elif lb.startswith(".L"):
                        local_label_kinds["dot_L_local_label"] += 1
                    else:
                        local_label_kinds["named_symbol_label"] += 1

                if any(a in TIER1_ARCHES or a == "multi_or_generic" for a in file_arches):
                    sites.append({
                        "file": rel,
                        "line": line_no,
                        "macro": f"{macro_kind}!",
                        "arches": file_arches,
                        "options": opts,
                        "mnemonics": mnems[:8],
                        "directives": dirs[:8],
                        "modifiers": mods[:6],
                    })

    return {
        "rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "rustc_version": "1.99.1",
        "total_asm_macro_invocations": sum(macro_counts.values()),
        "macro_kind_counts": dict(macro_counts),
        "by_subcrate": {k: dict(v) for k, v in sorted(by_subcrate.items())},
        "by_target_arch": {k: dict(v) for k, v in sorted(by_arch.items())},
        "options_frequency": dict(option_counts.most_common()),
        "operand_specifier_frequency": dict(operand_kind_counts.most_common()),
        "register_class_and_explicit_reg_frequency": dict(reg_class_counts.most_common(30)),
        "template_modifier_frequency": dict(modifier_counts.most_common()),
        "assembler_directive_frequency": dict(directive_counts.most_common()),
        "top_mnemonics_overall": dict(mnemonic_counts.most_common(45)),
        "tier1_arch_mnemonics": {
            k: dict(v.most_common(35)) for k, v in sorted(tier1_mnemonic_counts.items())
        },
        "label_kind_counts": dict(local_label_kinds),
        "tier1_relevant_sites_count": len(sites),
        "sample_tier1_sites": sites[:40],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-src", type=Path, default=DEFAULT_RUST_SRC)
    parser.add_argument("--out", type=Path, default=HERE / "sysroot_inline_asm_census.json")
    args = parser.parse_args()

    res = scan_repository(args.rust_src)
    args.out.write_text(json.dumps(res, indent=2) + "\n", encoding="utf-8")
    print(
        f"Scanned {res['total_asm_macro_invocations']} inline-asm sites "
        f"({res['tier1_relevant_sites_count']} Tier-1 relevant); wrote {args.out}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
