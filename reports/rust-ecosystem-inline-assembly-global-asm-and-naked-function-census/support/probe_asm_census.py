#!/usr/bin/env python3
"""M6 Probe: Empirical census of inline assembly (asm!, naked_asm!, global_asm!), #[unsafe(naked)] functions, and external cc-built .S/.s/.asm files across Rust 1.99.1 stdlib, compiler-builtins, and the crates.io corpus."""

import json
import os
import re
from collections import Counter, defaultdict
from pathlib import Path

S1991 = Path("/tmp/rust-1.99.1")
W_RUST = Path("/usr/local/google/home/joshlf/workspace/rust")
CRATES_MANIFEST = Path("/tmp/probe_out")
CARGO_SRC = Path(os.path.expanduser("~/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f"))
DATA_DIR = Path("/tmp/probe_out")
DATA_DIR.mkdir(parents=True, exist_ok=True)

ASM_CALL_RE = re.compile(r"\b(asm|naked_asm|global_asm)\s*!\s*\(")
NAKED_ATTR_RE = re.compile(r"#\s*\[\s*(?:unsafe\s*\(\s*naked\s*\)|naked)\s*\]")
OPTION_WORDS = [
    "pure", "nomem", "readonly", "preserves_flags", "noreturn",
    "nostack", "may_unwind", "att_syntax", "raw",
]
OPERAND_KINDS = [
    ("inlateout", r"\binlateout\s*\("),
    ("inout", r"\binout\s*\("),
    ("lateout", r"\blateout\s*\("),
    ("out", r"\bout\s*\("),
    ("in", r"\bin\s*\("),
    ("sym", r"\bsym\s+[a-zA-Z0-9_:]+"),
    ("const", r"\bconst\s+"),
    ("label", r"\blabel\s*\{"),
    ("clobber_abi", r"\bclobber_abi\s*\("),
]
REG_CLASSES = [
    "reg", "reg_abcd", "reg_byte", "xmm_reg", "ymm_reg", "zmm_reg",
    "kreg", "vreg", "vreg_low16", "preg", "sreg", "dreg", "qreg", "freg",
]
PRIVILEGED_MNEMONICS = {
    "mrs", "msr", "svc", "hvc", "smc", "eret", "wfi", "wfe", "isb", "dsb", "dmb", "dc", "ic", "tlbi", "at",
    "syscall", "sysenter", "sysexit", "sysret", "int", "iret", "iretd", "iretq", "cli", "sti", "hlt",
    "in", "out", "insb", "insw", "insd", "outsb", "outsw", "outsd",
    "rdmsr", "wrmsr", "rdtsc", "rdtscp", "rdpmc", "cpuid", "xgetbv", "xsetbv",
    "lgdt", "sgdt", "lidt", "sidt", "lldt", "sldt", "ltr", "str", "invlpg", "invpcid", "wbinvd", "clts", "swapgs", "wrfsbase", "rdfsbase", "wrgsbase", "rdgsbase",
    "csrr", "csrw", "csrs", "csrc", "csrrw", "csrrs", "csrrc", "csrrwi", "csrrsi", "csrrci", "ecall", "ebreak", "mret", "sret", "sfence.vma",
}


def extract_macro_invocations(text: str):
    """Find balanced asm!(...), naked_asm!(...), global_asm!(...) blocks."""
    results = []
    for m in ASM_CALL_RE.finditer(text):
        kind = m.group(1)
        start = m.end()
        depth = 1
        i = start
        in_str = False
        escape = False
        while i < len(text) and depth > 0:
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
                elif ch in "([{":
                    depth += 1
                elif ch in ")]}":
                    depth -= 1
            i += 1
        body = text[start : i - 1]
        line_no = text.count("\n", 0, m.start()) + 1
        results.append((kind, line_no, body))
    return results


def analyze_asm_body(body: str):
    options = []
    for m_opt in re.finditer(r"\boptions\s*\(([^)]*)\)", body):
        opt_str = m_opt.group(1)
        for w in OPTION_WORDS:
            if re.search(rf"\b{w}\b", opt_str):
                options.append(w)

    operands = Counter()
    for name, pat in OPERAND_KINDS:
        c = len(re.findall(pat, body))
        if c:
            operands[name] += c

    reg_classes = Counter()
    for rc in REG_CLASSES:
        c = len(re.findall(rf"\(\s*{rc}\s*\)", body))
        if c:
            reg_classes[rc] += c

    explicit_regs = re.findall(r'\b(?:in|out|inout|lateout|inlateout)\s*\(\s*"([^"]+)"\s*\)', body)

    # Extract string literals at the start (template strings) before first operand/options
    # Approximate by taking string literals not preceded by `(` or `=`
    strings = re.findall(r'"((?:[^"\\]|\\.)*)"', body)
    mnemonics = Counter()
    directives = Counter()
    priv_mnemonics = Counter()
    for s in strings:
        if s in explicit_regs or s in {"C", "system", "efiapi", "win64", "sysv64", "aapcs"}:
            continue
        for raw_line in re.split(r"\\n|\n|;", s):
            line = raw_line.strip()
            if not line or line.startswith("//") or line.startswith("#") or line.startswith("/*"):
                continue
            # Strip numeric or named label prefix `1:` or `foo:`
            line = re.sub(r"^[0-9a-zA-Z_.]+:\s*", "", line).strip()
            if not line:
                continue
            tok = line.split()[0].lower().rstrip(",")
            if tok.startswith("."):
                directives[tok] += 1
            elif re.match(r"^[a-z][a-z0-9.]*$", tok) and tok not in OPTION_WORDS and tok not in {"in", "out", "inout", "lateout", "sym", "const", "options"}:
                mnemonics[tok] += 1
                if tok in PRIVILEGED_MNEMONICS:
                    priv_mnemonics[tok] += 1

    return {
        "options": options,
        "operands": dict(operands),
        "reg_classes": dict(reg_classes),
        "explicit_regs": explicit_regs,
        "mnemonics": dict(mnemonics),
        "directives": dict(directives),
        "priv_mnemonics": dict(priv_mnemonics),
    }


def scan_rust_tree(root_dir: Path, skip_tests: bool = False):
    macro_counts = Counter()
    naked_fn_count = 0
    files_with_asm = []
    option_counts = Counter()
    operand_counts = Counter()
    reg_class_counts = Counter()
    explicit_reg_counts = Counter()
    mnemonic_counts = Counter()
    directive_counts = Counter()
    priv_counts = Counter()
    ext_asm_files = []

    for p in sorted(root_dir.rglob("*")):
        if not p.is_file():
            continue
        rel = str(p.relative_to(root_dir))
        if skip_tests and ("/tests/" in rel or "/benches/" in rel or rel.startswith("tests/")):
            continue
        if p.suffix in {".s", ".S", ".asm"}:
            ext_asm_files.append(rel)
            continue
        if p.suffix != ".rs":
            continue
        try:
            text = p.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue

        n_naked = len(NAKED_ATTR_RE.findall(text))
        invocs = extract_macro_invocations(text)
        if not invocs and not n_naked:
            continue

        naked_fn_count += n_naked
        files_with_asm.append({
            "file": rel,
            "asm": sum(1 for k, _, _ in invocs if k == "asm"),
            "naked_asm": sum(1 for k, _, _ in invocs if k == "naked_asm"),
            "global_asm": sum(1 for k, _, _ in invocs if k == "global_asm"),
            "naked_attrs": n_naked,
        })
        for kind, _line, body in invocs:
            macro_counts[kind] += 1
            info = analyze_asm_body(body)
            for o in info["options"]:
                option_counts[o] += 1
            for k, v in info["operands"].items():
                operand_counts[k] += v
            for k, v in info["reg_classes"].items():
                reg_class_counts[k] += v
            for r in info["explicit_regs"]:
                explicit_reg_counts[r] += 1
            for k, v in info["mnemonics"].items():
                mnemonic_counts[k] += v
            for k, v in info["directives"].items():
                directive_counts[k] += v
            for k, v in info["priv_mnemonics"].items():
                priv_counts[k] += v

    return {
        "files_with_asm_count": len(files_with_asm),
        "files_with_asm": files_with_asm,
        "macro_counts": dict(macro_counts),
        "naked_fn_attributes": naked_fn_count,
        "external_asm_files_count": len(ext_asm_files),
        "external_asm_files": ext_asm_files[:50],
        "option_counts": dict(option_counts.most_common()),
        "operand_counts": dict(operand_counts.most_common()),
        "reg_class_counts": dict(reg_class_counts.most_common()),
        "explicit_reg_counts": dict(explicit_reg_counts.most_common(30)),
        "top_40_mnemonics": dict(mnemonic_counts.most_common(40)),
        "directives": dict(directive_counts.most_common(30)),
        "privileged_mnemonics": dict(priv_counts.most_common(30)),
    }


def scan_crates_corpus():
    manifest = json.loads(CRATES_MANIFEST.read_text(encoding="utf-8"))
    top100 = manifest.get("top_100_by_recent_downloads", [])
    dl_map = {c["name"]: c.get("recent_downloads", 0) for c in top100}

    # Scan top-100 unpacked crates in CARGO_SRC, plus all unpacked crates in CARGO_SRC
    all_crate_dirs = sorted([d for d in CARGO_SRC.iterdir() if d.is_dir()])

    # Deduplicate by crate name (pick latest version dir in CARGO_SRC)
    latest_by_name = {}
    for d in all_crate_dirs:
        m = re.match(r"^([a-zA-Z0-9_-]+)-(\d+\..*)$", d.name)
        if m:
            latest_by_name[m.group(1)] = d

    top100_results = {}
    ecosystem_with_rust_asm = []
    ecosystem_with_ext_asm = []
    agg_macros = Counter()
    agg_options = Counter()
    agg_operands = Counter()
    agg_reg_classes = Counter()
    agg_mnemonics = Counter()
    agg_directives = Counter()
    agg_priv = Counter()
    weighted_macros = Counter()

    for cname, cdir in sorted(latest_by_name.items()):
        res = scan_rust_tree(cdir, skip_tests=True)
        total_macros = sum(res["macro_counts"].values())
        dl = dl_map.get(cname, 1)
        if cname in dl_map:
            top100_results[cname] = {
                "dir": cdir.name,
                "recent_downloads": dl,
                "macro_counts": res["macro_counts"],
                "naked_fn_attributes": res["naked_fn_attributes"],
                "external_asm_files_count": res["external_asm_files_count"],
                "files_with_asm_count": res["files_with_asm_count"],
            }
        if total_macros > 0 or res["naked_fn_attributes"] > 0:
            ecosystem_with_rust_asm.append({
                "crate": cname,
                "dir": cdir.name,
                "in_top_100": cname in dl_map,
                "recent_downloads": dl_map.get(cname, 0),
                "macro_counts": res["macro_counts"],
                "naked_fn_attributes": res["naked_fn_attributes"],
                "external_asm_files_count": res["external_asm_files_count"],
                "top_mnemonics": list(res["top_40_mnemonics"].items())[:10],
            })
            for k, v in res["macro_counts"].items():
                agg_macros[k] += v
                weighted_macros[k] += v * dl
            for k, v in res["option_counts"].items():
                agg_options[k] += v
            for k, v in res["operand_counts"].items():
                agg_operands[k] += v
            for k, v in res["reg_class_counts"].items():
                agg_reg_classes[k] += v
            for k, v in res["top_40_mnemonics"].items():
                agg_mnemonics[k] += v
            for k, v in res["directives"].items():
                agg_directives[k] += v
            for k, v in res["privileged_mnemonics"].items():
                agg_priv[k] += v
        if res["external_asm_files_count"] > 0:
            ecosystem_with_ext_asm.append({
                "crate": cname,
                "dir": cdir.name,
                "in_top_100": cname in dl_map,
                "external_asm_files_count": res["external_asm_files_count"],
                "sample_files": res["external_asm_files"][:5],
            })

    ecosystem_with_rust_asm.sort(key=lambda x: (x["recent_downloads"], sum(x["macro_counts"].values())), reverse=True)
    ecosystem_with_ext_asm.sort(key=lambda x: x["external_asm_files_count"], reverse=True)

    return {
        "total_unique_crates_scanned_in_cache": len(latest_by_name),
        "top_100_crates_matched": len(top100_results),
        "top_100_with_rust_asm": [k for k, v in top100_results.items() if sum(v["macro_counts"].values()) > 0 or v["naked_fn_attributes"] > 0],
        "top_100_with_external_asm": [k for k, v in top100_results.items() if v["external_asm_files_count"] > 0],
        "crates_with_rust_asm_count": len(ecosystem_with_rust_asm),
        "crates_with_external_cc_asm_count": len(ecosystem_with_ext_asm),
        "aggregate_macro_counts": dict(agg_macros),
        "download_weighted_macro_counts": dict(weighted_macros),
        "aggregate_option_counts": dict(agg_options.most_common()),
        "aggregate_operand_counts": dict(agg_operands.most_common()),
        "aggregate_reg_class_counts": dict(agg_reg_classes.most_common()),
        "aggregate_top_40_mnemonics": dict(agg_mnemonics.most_common(40)),
        "aggregate_directives": dict(agg_directives.most_common(30)),
        "aggregate_privileged_mnemonics": dict(agg_priv.most_common(30)),
        "top_40_crates_with_rust_asm": ecosystem_with_rust_asm[:40],
        "top_30_crates_with_external_cc_asm": ecosystem_with_ext_asm[:30],
    }


def main():
    std_res = scan_rust_tree(S1991 / "library/std/src")
    core_res = scan_rust_tree(S1991 / "library/core/src")
    stdarch_res = scan_rust_tree(S1991 / "library/stdarch/crates/core_arch/src")
    panic_unwind_res = scan_rust_tree(S1991 / "library/panic_unwind/src")
    compiler_builtins_res = scan_rust_tree(W_RUST / "library/compiler-builtins/compiler-builtins/src")
    corpus_res = scan_crates_corpus()

    out = {
        "rust_1991_std": std_res,
        "rust_1991_core": core_res,
        "rust_1991_stdarch_core_arch": stdarch_res,
        "rust_1991_panic_unwind": panic_unwind_res,
        "compiler_builtins": compiler_builtins_res,
        "crates_io_corpus": corpus_res,
    }
    (DATA_DIR / "m6_asm_census.json").write_text(json.dumps(out, indent=2), encoding="utf-8")
    for k in ["rust_1991_std", "rust_1991_core", "rust_1991_stdarch_core_arch", "compiler_builtins"]:
        r = out[k]
        print(f"=== {k} === files={r['files_with_asm_count']} macros={r['macro_counts']} naked_attrs={r['naked_fn_attributes']} ext_asm={r['external_asm_files_count']}")
        print(f"  options={r['option_counts']} operands={r['operand_counts']}")
    c = out["crates_io_corpus"]
    print(f"=== crates_io_corpus ({c['total_unique_crates_scanned_in_cache']} unique crates) ===")
    print(f"  crates with rust asm: {c['crates_with_rust_asm_count']} | crates with ext .S/.asm: {c['crates_with_external_cc_asm_count']}")
    print(f"  top100 with rust asm: {c['top_100_with_rust_asm']}")
    print(f"  macro_counts: {c['aggregate_macro_counts']}")
    print(f"  options: {c['aggregate_option_counts']}")
    print(f"  operands: {c['aggregate_operand_counts']}")


if __name__ == "__main__":
    main()
