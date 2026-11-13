#!/usr/bin/env python3
"""
Extract and analyze C6: Language and library features with code-generation impact in Rust 1.99.1.
1. Parse compiler/rustc_feature/src/{accepted.rs, unstable.rs, removed.rs, builtin_attrs.rs}.
2. Scan compiler/{rustc_mir_build, rustc_mir_transform, rustc_ty_utils, rustc_abi, rustc_codegen_ssa, rustc_codegen_llvm, rustc_codegen_cranelift, rustc_codegen_gcc, rustc_sanitizers}
   for references to sym::* feature gates and attributes (`tcx.features().*`, `has_attr(..., sym::rustc_*)`).
3. Scan library/{core, alloc, std, portable-simd, stdarch, proc_macro, panic_unwind, panic_abort, compiler-builtins} for `#![feature(...)]` and `#[rustc_*]` attribute usage.
4. Scan tests/{ui, codegen-llvm, assembly-llvm, mir-opt} for `//~` or `#![feature(...)]` coverage of each codegen-relevant feature.
5. Scan E2 top-100 crates (from crates_manifest.json / local cargo cache) for `#![feature(...)]` or cfg-gated nightly features.
"""
import json
import os
import re
from pathlib import Path

RUST_S1991 = Path("./rust-1.99.1")
OUT_DIR = Path("/tmp/reval")
OUT_DIR.mkdir(parents=True, exist_ok=True)

def parse_feature_lists():
    f_dir = RUST_S1991 / "compiler/rustc_feature/src"
    res = {"accepted": [], "unstable": [], "removed": [], "builtin_attrs": []}

    # accepted.rs: (accepted, feature_name, "1.xx.0", Some(issue))
    acc_text = (f_dir / "accepted.rs").read_text()
    for m in re.finditer(r'\(\s*accepted\s*,\s*([a-z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\d+\)|None)', acc_text):
        res["accepted"].append({
            "name": m.group(1),
            "since": m.group(2),
            "issue": m.group(3),
            "line": acc_text[:m.start()].count("\n") + 1,
        })

    # unstable.rs: (unstable|incomplete|internal, feature_name, "1.xx.0", Some(issue))
    unst_text = (f_dir / "unstable.rs").read_text()
    for m in re.finditer(r'\(\s*(unstable|incomplete|internal)\s*,\s*([a-z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\d+\)|None)', unst_text):
        res["unstable"].append({
            "status": m.group(1),
            "name": m.group(2),
            "since": m.group(3),
            "issue": m.group(4),
            "line": unst_text[:m.start()].count("\n") + 1,
        })

    # removed.rs
    rem_text = (f_dir / "removed.rs").read_text()
    for m in re.finditer(r'\(\s*removed\s*,\s*([a-z0-9_]+)\s*,\s*"([^"]+)"\s*,\s*(Some\(\d+\)|None)', rem_text):
        res["removed"].append({
            "name": m.group(1),
            "since": m.group(2),
            "issue": m.group(3),
            "line": rem_text[:m.start()].count("\n") + 1,
        })

    # builtin_attrs.rs
    ba_text = (f_dir / "builtin_attrs.rs").read_text()
    for m in re.finditer(r'(?:rustc_attr!|ungated!|gated!)\s*\(\s*([a-z0-9_]+)\s*,', ba_text):
        res["builtin_attrs"].append({
            "name": m.group(1),
            "line": ba_text[:m.start()].count("\n") + 1,
        })
    # Also scan for sym::rustc_* inside builtin_attrs.rs
    rustc_attrs = sorted(set(re.findall(r'\b(rustc_[a-z0-9_]+)\b', ba_text)))
    res["rustc_internal_attrs"] = rustc_attrs
    return res

def scan_backend_and_mir_feature_checks():
    crates = [
        "rustc_mir_build", "rustc_mir_transform", "rustc_const_eval",
        "rustc_ty_utils", "rustc_abi", "rustc_middle",
        "rustc_codegen_ssa", "rustc_codegen_llvm",
        "rustc_codegen_cranelift", "rustc_codegen_gcc", "rustc_sanitizers"
    ]
    feature_refs = {}
    attr_refs = {}
    for c in crates:
        cdir = RUST_S1991 / "compiler" / c
        if not cdir.exists():
            continue
        for root, _, files in os.walk(cdir):
            for fn in files:
                if not fn.endswith(".rs"):
                    continue
                p = Path(root) / fn
                rel = str(p.relative_to(RUST_S1991))
                t = p.read_text(errors="ignore")
                for m in re.finditer(r'features(?:\(\))?\.([a-z0-9_]+)\(\)', t):
                    feat = m.group(1)
                    ln = t[:m.start()].count("\n") + 1
                    feature_refs.setdefault(feat, {}).setdefault(c, []).append(f"{rel}:{ln}")
                for m in re.finditer(r'sym::(rustc_[a-z0-9_]+|naked|cold|inline|used|link_section|linkage|thread_local|track_caller|no_mangle|export_name|repr|target_feature|sanitize|ffi_const|ffi_pure|patchable_function_entry|objc_class|objc_selector)', t):
                    attr = m.group(1)
                    ln = t[:m.start()].count("\n") + 1
                    attr_refs.setdefault(attr, {}).setdefault(c, []).append(f"{rel}:{ln}")
    return feature_refs, attr_refs

def scan_stdlib_features_and_attrs():
    libs = [
        "library/core", "library/alloc", "library/std",
        "library/portable-simd", "library/stdarch", "library/proc_macro",
        "library/panic_unwind", "library/panic_abort", "library/compiler-builtins"
    ]
    stdlib_features = {}
    stdlib_rustc_attrs = {}
    for lib in libs:
        ldir = RUST_S1991 / lib
        if not ldir.exists():
            continue
        feats = set()
        attrs = {}
        for root, _, files in os.walk(ldir):
            for fn in files:
                if not fn.endswith(".rs"):
                    continue
                p = Path(root) / fn
                t = p.read_text(errors="ignore")
                for m in re.finditer(r'#!\[\s*feature\(([^)]+)\)\s*\]', t):
                    for tok in m.group(1).split(","):
                        tok = tok.strip()
                        if re.match(r'^[a-z0-9_]+$', tok):
                            feats.add(tok)
                for m in re.finditer(r'#\[\s*(rustc_[a-z0-9_]+)', t):
                    a = m.group(1)
                    attrs[a] = attrs.get(a, 0) + 1
        stdlib_features[lib] = sorted(feats)
        stdlib_rustc_attrs[lib] = attrs
    return stdlib_features, stdlib_rustc_attrs

def scan_tests_feature_usage():
    test_suites = ["tests/codegen-llvm", "tests/assembly-llvm", "tests/mir-opt", "tests/ui"]
    suite_counts = {}
    for ts in test_suites:
        tdir = RUST_S1991 / ts
        if not tdir.exists():
            continue
        counts = {}
        for root, _, files in os.walk(tdir):
            for fn in files:
                if not fn.endswith(".rs"):
                    continue
                p = Path(root) / fn
                t = p.read_text(errors="ignore")
                for m in re.finditer(r'#!\[\s*feature\(([^)]+)\)\s*\]', t):
                    for tok in m.group(1).split(","):
                        tok = tok.strip()
                        if re.match(r'^[a-z0-9_]+$', tok):
                            counts[tok] = counts.get(tok, 0) + 1
        suite_counts[ts] = counts
    return suite_counts

if __name__ == "__main__":
    flists = parse_feature_lists()
    feat_refs, attr_refs = scan_backend_and_mir_feature_checks()
    stdlib_feats, stdlib_attrs = scan_stdlib_features_and_attrs()
    test_counts = scan_tests_feature_usage()

    out = {
        "counts": {
            "accepted": len(flists["accepted"]),
            "unstable": len(flists["unstable"]),
            "removed": len(flists["removed"]),
            "rustc_internal_attrs": len(flists["rustc_internal_attrs"]),
        },
        "feature_lists": flists,
        "compiler_feature_refs": feat_refs,
        "compiler_attr_refs": attr_refs,
        "stdlib_features": stdlib_feats,
        "stdlib_rustc_attrs": stdlib_attrs,
        "test_suite_feature_counts": test_counts,
    }
    (OUT_DIR / "c6_extracted.json").write_text(json.dumps(out, indent=2))
    print(f"C6 extraction complete: {out['counts']}")
