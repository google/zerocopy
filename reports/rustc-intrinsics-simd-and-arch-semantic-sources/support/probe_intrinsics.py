#!/usr/bin/env python3
"""M1 Probe: Complete inventory of #[rustc_intrinsic], simd_*, and core::arch llvm.* bindings."""

import json
import re
from pathlib import Path
from collections import Counter, defaultdict

S1991 = Path("/tmp/rust-1.99.1")
S1100 = Path("/tmp/rust-1.100.0")
N1112 = Path("/tmp/rust-nightly-2026-11-12")
OUT_DIR = Path("/tmp/probe_out")
OUT_DIR.mkdir(parents=True, exist_ok=True)


def parse_rustc_intrinsics(repo: Path):
    """Find all #[rustc_intrinsic] declarations in library/core and library/alloc."""
    search_dirs = [repo / "library" / "core" / "src", repo / "library" / "alloc" / "src"]
    intrinsics = []
    for sdir in search_dirs:
        for path in sorted(sdir.rglob("*.rs")):
            rel_path = str(path.relative_to(repo))
            lines = path.read_text(encoding="utf-8").splitlines()
            i = 0
            while i < len(lines):
                if "#[rustc_intrinsic]" in lines[i]:
                    start = i
                    while start > 0 and (
                        lines[start - 1].strip().startswith("#[")
                        or lines[start - 1].strip().startswith("///")
                        or lines[start - 1].strip().startswith("//!")
                        or lines[start - 1].strip() == ""
                    ):
                        if lines[start - 1].strip() == "" and start >= 2 and not (
                            lines[start - 2].strip().startswith("///") or lines[start - 2].strip().startswith("#[")
                        ):
                            break
                        start -= 1
                    end = i
                    fn_name = None
                    is_unsafe = False
                    is_const = False
                    has_body = False
                    found_sig_end = False
                    while end < len(lines):
                        line = lines[end]
                        if fn_name is None:
                            m = re.search(r"\bfn\s+([a-zA-Z0-9_]+)\b", line)
                            if m:
                                fn_name = m.group(1)
                                prefix = line[:m.start()]
                                if "unsafe" in prefix or any("unsafe" in lines[k] for k in range(i, end)):
                                    is_unsafe = True
                                if "const " in prefix or any("const fn" in lines[k] for k in range(i, end + 1)):
                                    is_const = True
                        if fn_name is not None and not found_sig_end:
                            stripped = line.split("//")[0].strip()
                            if stripped.endswith(";"):
                                has_body = False
                                found_sig_end = True
                                break
                            elif "{" in stripped:
                                has_body = True
                                found_sig_end = True
                                break
                        end += 1
                    block_lines = lines[start : end + 1]
                    attrs = [l.strip() for l in block_lines if l.strip().startswith("#[")]
                    docs = [l.strip()[3:].strip() for l in block_lines if l.strip().startswith("///")]
                    must_override = any("rustc_intrinsic_must_be_overridden" in a for a in attrs)
                    nounwind = any("rustc_nounwind" in a for a in attrs)
                    const_stable = any("rustc_const_stable" in a for a in attrs)
                    const_unstable = any("rustc_const_unstable" in a for a in attrs)
                    safety_doc = any("# Safety" in d or "UB" in d or "undefined behavior" in d.lower() for d in docs)
                    intrinsics.append({
                        "name": fn_name,
                        "file": rel_path,
                        "line": i + 1,
                        "is_unsafe_fn": is_unsafe,
                        "is_const_fn": is_const,
                        "has_fallback_body": has_body,
                        "must_be_overridden": must_override,
                        "nounwind": nounwind,
                        "const_stable": const_stable,
                        "const_unstable": const_unstable,
                        "has_safety_or_ub_doc": safety_doc,
                        "doc_first_line": docs[0] if docs else "",
                    })
                i += 1
    return intrinsics


def scan_sym_matches(file_path: Path):
    if not file_path.exists():
        return set(), set()
    text = file_path.read_text(encoding="utf-8")
    syms = set(re.findall(r"\bsym::([a-zA-Z0-9_]+)\b", text))
    strs = set(re.findall(r'"([a-zA-Z0-9_.]+)"', text))
    return syms, strs


def collect_backend_support(repo: Path, intrinsics: list):
    lower_intr_syms, lower_intr_strs = scan_sym_matches(repo / "compiler/rustc_mir_transform/src/lower_intrinsics.rs")
    instsimp_syms, instsimp_strs = scan_sym_matches(repo / "compiler/rustc_mir_transform/src/instsimplify.rs")
    gvn_syms, gvn_strs = scan_sym_matches(repo / "compiler/rustc_mir_transform/src/gvn.rs")

    ctfe_syms, ctfe_strs = set(), set()
    for p in [
        repo / "compiler/rustc_const_eval/src/interpret/intrinsics.rs",
        repo / "compiler/rustc_const_eval/src/interpret/intrinsics/atomic.rs",
        repo / "compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs",
        repo / "compiler/rustc_const_eval/src/interpret/step.rs",
    ]:
        s1, s2 = scan_sym_matches(p)
        ctfe_syms |= s1
        ctfe_strs |= s2

    miri_syms, miri_strs = set(), set()
    for p in (repo / "src/tools/miri/src/intrinsics").rglob("*.rs"):
        s1, s2 = scan_sym_matches(p)
        miri_syms |= s1
        miri_strs |= s2

    ssa_syms, ssa_strs = scan_sym_matches(repo / "compiler/rustc_codegen_ssa/src/mir/intrinsic.rs")
    ssa_blk_syms, ssa_blk_strs = scan_sym_matches(repo / "compiler/rustc_codegen_ssa/src/mir/block.rs")
    ssa_syms |= ssa_blk_syms
    ssa_strs |= ssa_blk_strs

    llvm_syms, llvm_strs = scan_sym_matches(repo / "compiler/rustc_codegen_llvm/src/intrinsic.rs")
    llvm_bx_syms, llvm_bx_strs = scan_sym_matches(repo / "compiler/rustc_codegen_llvm/src/builder.rs")
    llvm_syms |= llvm_bx_syms
    llvm_strs |= llvm_bx_strs

    clif_syms, clif_strs = set(), set()
    for p in (repo / "compiler/rustc_codegen_cranelift/src/intrinsics").rglob("*.rs"):
        s1, s2 = scan_sym_matches(p)
        clif_syms |= s1
        clif_strs |= s2

    gcc_syms, gcc_strs = set(), set()
    for p in (repo / "compiler/rustc_codegen_gcc/src/intrinsic").rglob("*.rs"):
        s1, s2 = scan_sym_matches(p)
        gcc_syms |= s1
        gcc_strs |= s2

    def has_intr(name, syms, strs, strip_simd=False):
        if name in syms or name in strs:
            return True
        if strip_simd and name.startswith("simd_"):
            short = name[len("simd_"):]
            if short in syms or short in strs:
                return True
        for prefix in [
            "atomic_cxchg", "atomic_cxchgweak", "atomic_load", "atomic_store",
            "atomic_xchg", "atomic_xadd", "atomic_xsub", "atomic_and",
            "atomic_nand", "atomic_or", "atomic_xor", "atomic_max",
            "atomic_min", "atomic_umax", "atomic_umin", "atomic_fence",
            "atomic_singlethreadfence",
        ]:
            if name.startswith(prefix) and (prefix in syms or prefix in strs or "atomic_" in strs):
                return True
        return False

    for intr in intrinsics:
        name = intr["name"]
        intr["mir_lower_intrinsics"] = has_intr(name, lower_intr_syms, lower_intr_strs)
        intr["mir_instsimplify_or_gvn"] = has_intr(name, instsimp_syms | gvn_syms, instsimp_strs | gvn_strs)
        intr["ctfe_const_eval"] = has_intr(name, ctfe_syms, ctfe_strs, strip_simd=True) or intr["mir_lower_intrinsics"]
        intr["miri"] = has_intr(name, miri_syms, miri_strs, strip_simd=True) or intr["ctfe_const_eval"]
        intr["codegen_ssa"] = has_intr(name, ssa_syms, ssa_strs) or intr["mir_lower_intrinsics"]
        intr["codegen_llvm"] = has_intr(name, llvm_syms, llvm_strs) or intr["codegen_ssa"] or intr["has_fallback_body"]
        intr["codegen_cranelift"] = has_intr(name, clif_syms, clif_strs, strip_simd=True) or intr["mir_lower_intrinsics"] or intr["has_fallback_body"]
        intr["codegen_gcc"] = has_intr(name, gcc_syms, gcc_strs, strip_simd=True) or intr["mir_lower_intrinsics"] or intr["has_fallback_body"]


def parse_stdarch_llvm_links(repo: Path):
    """Extract all link_name = "llvm.*" declarations across core_arch (including cfg_attr)."""
    core_arch_dir = repo / "library/stdarch/crates/core_arch/src"
    links = []
    link_re = re.compile(r'link_name\s*=\s*"(llvm\.[^"]+)"')
    for path in sorted(core_arch_dir.rglob("*.rs")):
        rel = str(path.relative_to(core_arch_dir))
        arch_group = rel.split("/")[0]
        text = path.read_text(encoding="utf-8")
        for m in link_re.finditer(text):
            llvm_name = m.group(1)
            links.append({
                "arch_group": arch_group,
                "file": rel,
                "llvm_intrinsic": llvm_name,
            })
    return links


def classify_llvm_intrinsic(llvm_name: str):
    parts = llvm_name.split(".")
    if len(parts) >= 2 and parts[1] in {
        "x86", "aarch64", "arm", "wasm", "riscv", "ppc", "mips",
        "nvvm", "amdgcn", "loongarch", "s390", "hexagon", "avr"
    }:
        return "target_specific", parts[1]
    base_parts = []
    for p in parts:
        if re.match(r"^(v\d+[if]\d+|nxv\d+[if]\d+|[if]\d+|p\d+)$", p):
            break
        base_parts.append(p)
    return "target_independent", ".".join(base_parts)


def extract_miri_llvm_intrinsics(repo: Path):
    """Reconstruct exact llvm.* intrinsic names supported by Miri."""
    supported = set()
    intr_dir = repo / "src/tools/miri/src/intrinsics"
    for p in sorted(intr_dir.rglob("*.rs")):
        text = p.read_text(encoding="utf-8")
        m_pref = re.search(r'strip_prefix\("(llvm\.[^"]+)"\)', text)
        if m_pref:
            prefix = m_pref.group(1)
            # Extract all string literals in match arms
            for lit in re.findall(r'"([a-zA-Z0-9_.]+)"', text):
                if not lit.startswith("llvm.") and "." in lit or lit in {"pause", "vzeroupper", "xgetbv", "rdtsc", "rdtscp", "CpuidCount"}:
                    supported.add(prefix + lit)
        for lit in re.findall(r'"(llvm\.[^"]+)"', text):
            if not lit.endswith("."):
                supported.add(lit)
    return supported


def extract_cranelift_llvm_intrinsics(repo: Path, all_unique_llvm: set):
    """Determine which llvm.* intrinsics from stdarch are matched by Cranelift."""
    clif_dir = repo / "compiler/rustc_codegen_cranelift/src/intrinsics"
    exact_matches = set()
    prefix_matches = set()
    for p in [clif_dir / "llvm.rs", clif_dir / "llvm_aarch64.rs", clif_dir / "llvm_x86.rs"]:
        text = p.read_text(encoding="utf-8")
        for lit in re.findall(r'"(llvm\.[^"]+)"', text):
            if lit in {"llvm.aarch64", "llvm.x86"}:
                continue
            exact_matches.add(lit)
        for pref in re.findall(r'starts_with\("(llvm\.[^"]+)"\)', text):
            if pref in {"llvm.aarch64", "llvm.x86"}:
                continue
            prefix_matches.add(pref)

    supported = set()
    for name in all_unique_llvm:
        if name in exact_matches or any(name.startswith(pref) for pref in prefix_matches):
            supported.add(name)
    return supported, exact_matches, prefix_matches


def extract_gcc_llvm_intrinsics(repo: Path, all_unique_llvm: set):
    gcc_dir = repo / "compiler/rustc_codegen_gcc/src/intrinsic"
    gcc_strs = set()
    for p in gcc_dir.rglob("*.rs"):
        text = p.read_text(encoding="utf-8")
        for lit in re.findall(r'"(llvm\.[^"]+)"', text):
            gcc_strs.add(lit)
    return {name for name in all_unique_llvm if name in gcc_strs}, gcc_strs


def main():
    intr_1991 = parse_rustc_intrinsics(S1991)
    collect_backend_support(S1991, intr_1991)

    intr_1100 = parse_rustc_intrinsics(S1100)
    intr_n1112 = parse_rustc_intrinsics(N1112)

    names_1991 = {x["name"] for x in intr_1991}
    names_1100 = {x["name"] for x in intr_1100}
    names_n1112 = {x["name"] for x in intr_n1112}

    by_file = Counter(x["file"] for x in intr_1991)
    simd_intr = [x for x in intr_1991 if "simd" in x["file"]]
    core_main_intr = [x for x in intr_1991 if "simd" not in x["file"]]

    links = parse_stdarch_llvm_links(S1991)
    links_by_arch = Counter(x["arch_group"] for x in links)
    unique_llvm_by_arch = defaultdict(set)
    target_indep_by_arch = defaultdict(set)
    target_spec_by_arch = defaultdict(set)
    generic_families = Counter()
    target_spec_prefixes = Counter()

    for x in links:
        ag = x["arch_group"]
        ln = x["llvm_intrinsic"]
        unique_llvm_by_arch[ag].add(ln)
        kind, fam = classify_llvm_intrinsic(ln)
        if kind == "target_independent":
            target_indep_by_arch[ag].add(ln)
            generic_families[fam] += 1
        else:
            target_spec_by_arch[ag].add(ln)
            target_spec_prefixes[fam] += 1

    all_unique_llvm = {x["llvm_intrinsic"] for x in links}
    miri_supp = extract_miri_llvm_intrinsics(S1991)
    clif_supp, clif_exact, clif_pref = extract_cranelift_llvm_intrinsics(S1991, all_unique_llvm)
    gcc_supp, gcc_all_strs = extract_gcc_llvm_intrinsics(S1991, all_unique_llvm)

    arch_summary = {}
    for ag in sorted(links_by_arch.keys()):
        u_all = unique_llvm_by_arch[ag]
        u_ind = target_indep_by_arch[ag]
        u_spec = target_spec_by_arch[ag]
        miri_cnt = sum(1 for n in u_all if n in miri_supp)
        clif_cnt = sum(1 for n in u_all if n in clif_supp)
        gcc_cnt = sum(1 for n in u_all if n in gcc_supp)
        arch_summary[ag] = {
            "total_link_bindings": links_by_arch[ag],
            "unique_llvm_intrinsics": len(u_all),
            "target_independent_unique": len(u_ind),
            "target_specific_unique": len(u_spec),
            "miri_supported_unique": miri_cnt,
            "cranelift_supported_unique": clif_cnt,
            "gcc_supported_unique": gcc_cnt,
        }

    summary = {
        "rustc_1991_total_rustc_intrinsics": len(intr_1991),
        "rustc_1991_unique_names": len(names_1991),
        "by_file": dict(by_file),
        "counts_by_category": {
            "core_and_alloc_intrinsics": len(core_main_intr),
            "portable_simd_intrinsics": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs")),
            "scalable_simd_intrinsics": sum(1 for x in simd_intr if x["file"].endswith("simd/scalable.rs")),
        },
        "safety_and_constness": {
            "safe_fn": sum(1 for x in intr_1991 if not x["is_unsafe_fn"]),
            "unsafe_fn": sum(1 for x in intr_1991 if x["is_unsafe_fn"]),
            "const_fn": sum(1 for x in intr_1991 if x["is_const_fn"]),
            "const_stable": sum(1 for x in intr_1991 if x["const_stable"]),
            "const_unstable": sum(1 for x in intr_1991 if x["const_unstable"]),
            "nounwind": sum(1 for x in intr_1991 if x["nounwind"]),
        },
        "fallback_bodies": {
            "has_default_mir_body": sum(1 for x in intr_1991 if x["has_fallback_body"]),
            "declaration_only_no_body": sum(1 for x in intr_1991 if not x["has_fallback_body"]),
        },
        "stage_and_backend_coverage_all_317": {
            "mir_lower_intrinsics": sum(1 for x in intr_1991 if x["mir_lower_intrinsics"]),
            "mir_instsimplify_or_gvn": sum(1 for x in intr_1991 if x["mir_instsimplify_or_gvn"]),
            "ctfe_const_eval": sum(1 for x in intr_1991 if x["ctfe_const_eval"]),
            "miri": sum(1 for x in intr_1991 if x["miri"]),
            "codegen_ssa_generic": sum(1 for x in intr_1991 if x["codegen_ssa"]),
            "codegen_llvm": sum(1 for x in intr_1991 if x["codegen_llvm"]),
            "codegen_cranelift": sum(1 for x in intr_1991 if x["codegen_cranelift"]),
            "codegen_gcc": sum(1 for x in intr_1991 if x["codegen_gcc"]),
        },
        "portable_simd_75_coverage": {
            "ctfe_const_eval": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs") and x["ctfe_const_eval"]),
            "miri": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs") and x["miri"]),
            "codegen_llvm": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs") and x["codegen_llvm"]),
            "codegen_cranelift": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs") and x["codegen_cranelift"]),
            "codegen_gcc": sum(1 for x in simd_intr if x["file"].endswith("simd/mod.rs") and x["codegen_gcc"]),
        },
        "version_diffs": {
            "added_in_1_100_0": sorted(names_1100 - names_1991),
            "removed_in_1_100_0": sorted(names_1991 - names_1100),
            "added_in_nightly_2026_11_12": sorted(names_n1112 - names_1991),
            "removed_in_nightly_2026_11_12": sorted(names_1991 - names_n1112),
        },
        "stdarch_llvm_links": {
            "total_link_name_declarations": len(links),
            "total_unique_llvm_intrinsics": len(all_unique_llvm),
            "total_target_independent_unique": sum(1 for n in all_unique_llvm if classify_llvm_intrinsic(n)[0] == "target_independent"),
            "total_target_specific_unique": sum(1 for n in all_unique_llvm if classify_llvm_intrinsic(n)[0] == "target_specific"),
            "miri_total_extracted_llvm_shims": len(miri_supp),
            "miri_matched_in_stdarch": sum(1 for n in all_unique_llvm if n in miri_supp),
            "cranelift_exact_and_prefix_patterns": len(clif_exact) + len(clif_pref),
            "cranelift_matched_in_stdarch": len(clif_supp),
            "gcc_total_llvm_strings": len(gcc_all_strs),
            "gcc_matched_in_stdarch": len(gcc_supp),
            "target_independent_families": dict(generic_families.most_common()),
            "target_specific_llvm_prefixes": dict(target_spec_prefixes.most_common()),
            "by_arch_group": arch_summary,
        },
    }

    (OUT_DIR / "m1_summary.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    (OUT_DIR / "m1_intrinsics_inventory.json").write_text(
        json.dumps(
            {
                "summary": summary,
                "rustc_intrinsics": intr_1991,
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
