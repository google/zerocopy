#!/usr/bin/env python3
"""
Extract and analyze C5: Known soundness holes, miscompilations, and backend bugs at Rust 1.99.1.
1. Scan all test files in rust-worktrees/s1991/tests/ for `//@ known-bug:` directives (~292 files).
2. Classify each `known-bug` test by subdirectory, issue number/URL, failure mode, and compiler stage.
3. Diff `tests/` and `compiler/` between `1.98.1`, `1.99.1`, `1.100.0`, and `nightly-2026-11-12` for
   fixes to `I-unsound`, `A-codegen`, `A-LLVM`, `A-MIR-opt`, and miscompilation issues (e.g., #163911, etc.).
4. Inspect `src/llvm-project` git log between `1.98.1`, `1.99.1`, and `1.100.0` for miscompilation fixes.
"""
import json
import os
import re
import subprocess
from pathlib import Path

RUST_S1991 = Path("./rust-1.99.1")
RUST_S1100 = Path("./rust-1.100.0")
RUST_N1112 = Path("./rust-nightly")
LLVM_REPO = Path("/tmp/reval")
OUT_DIR = Path("/tmp/reval")
OUT_DIR.mkdir(parents=True, exist_ok=True)

def classify_known_bug(rel_path: str, content: str, bug_ref: str) -> dict:
    p_low = rel_path.lower()
    c_low = content.lower()
    # Determine origin category
    if "mir-opt/" in p_low or "mir_opt" in p_low or "-zmir-opt-level" in c_low or "gvn" in p_low or "jump_threading" in p_low or "dataflow" in p_low:
        origin = "mir_optimization"
        verified_effect = "fixes"
    elif "codegen" in p_low or "assembly" in p_low or "abi/" in p_low or "simd" in p_low or "repr_simd" in c_low or "extern \"c\"" in c_low and "transmute" in c_low:
        origin = "codegen_lowering_or_llvm"
        verified_effect = "fixes"
    elif "borrowck" in p_low or "nll/" in p_low or "polonius" in p_low or "lifetimes" in p_low or "hrtb" in p_low or "variance" in p_low or "coherence" in p_low or "wf/" in p_low or "trait-system" in p_low or "next-solver" in p_low or "associated-types" in p_low or "gat" in p_low or "const-generics" in p_low or "type-alias-impl-trait" in p_low or "impl-trait" in p_low or "unsized" in p_low or "coercion" in p_low or "auto-traits" in p_low or "opaque" in p_low:
        origin = "type_or_borrow_checking"
        verified_effect = "untouched_frontend"
    elif "consts/" in p_low or "ctfe" in p_low or "const_eval" in p_low or "const-eval" in p_low:
        origin = "const_eval_or_mir_construction"
        verified_effect = "catches_if_lowered_to_mir"
    elif "pattern" in p_low or "exhaustiveness" in p_low or "match" in p_low or "drop" in p_low or "coroutine" in p_low or "async" in p_low:
        origin = "mir_construction"
        verified_effect = "catches_at_mir_semantics_if_checked"
    else:
        # Inspect content for error-pattern or check-pass
        if "//@ check-pass" in c_low or "//@ build-pass" in c_low or "//@ run-pass" in c_low or "//@ run-fail" in c_low:
            origin = "type_or_borrow_checking"
            verified_effect = "untouched_frontend"
        else:
            origin = "type_or_borrow_checking"
            verified_effect = "untouched_frontend"

    # Extract URL if issue number
    m_num = re.search(r'#(\d+)', bug_ref)
    url = f"https://github.com/rust-lang/rust/issues/{m_num.group(1)}" if m_num else bug_ref

    return {
        "file": rel_path,
        "bug_ref": bug_ref,
        "issue_url": url,
        "origin": origin,
        "verified_mir_to_asm_effect": verified_effect,
        "has_check_pass": "//@ check-pass" in content,
        "has_run_pass": "//@ run-pass" in content or "//@ run-fail" in content,
    }

def scan_known_bugs(worktree: Path):
    results = []
    tests_dir = worktree / "tests"
    for root, _, files in os.walk(tests_dir):
        for fn in sorted(files):
            if not fn.endswith(".rs"):
                continue
            p = Path(root) / fn
            t = p.read_text(errors="ignore")
            for m in re.finditer(r'//@\s*(?:\[[^\]]+\]\s*)?known-bug:\s*([^\n]+)', t):
                rel = str(p.relative_to(worktree))
                bug_ref = m.group(1).strip()
                results.append(classify_known_bug(rel, t, bug_ref))
    return results

def scan_git_commits_for_bugs():
    # Commits between 1.98.1 and nightly-2026-11-12 mentioning unsound, miscompil, rustlantis, alive2, codegen, etc.
    cmd = [
        "git", "-C", str(RUST_N1112), "log", "--oneline", "--no-merges",
        "48a229ceaefd4985c50990b14116b6d856af0985..3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
        "--grep=unsound\\|miscompil\\|codegen\\|MIR\\|LLVM\\|rustlantis\\|ABI\\|soundness\\|ICE", "-i"
    ]
    p = subprocess.run(cmd, capture_output=True, text=True)
    lines = p.stdout.strip().splitlines()
    return lines[:300]

if __name__ == "__main__":
    kb_s1991 = scan_known_bugs(RUST_S1991)
    kb_s1100 = scan_known_bugs(RUST_S1100)
    kb_n1112 = scan_known_bugs(RUST_N1112)

    s1991_files = {x["file"]: x for x in kb_s1991}
    s1100_files = {x["file"]: x for x in kb_s1100}
    n1112_files = {x["file"]: x for x in kb_n1112}

    fixed_in_1100 = sorted(set(s1991_files.keys()) - set(s1100_files.keys()))
    fixed_in_n1112 = sorted(set(s1991_files.keys()) - set(n1112_files.keys()))
    added_after_1991 = sorted(set(n1112_files.keys()) - set(s1991_files.keys()))

    by_origin = {}
    for item in kb_s1991:
        by_origin[item["origin"]] = by_origin.get(item["origin"], 0) + 1

    commits = scan_git_commits_for_bugs()

    out = {
        "s1991_known_bug_count": len(kb_s1991),
        "s1100_known_bug_count": len(kb_s1100),
        "n1112_known_bug_count": len(kb_n1112),
        "by_origin": by_origin,
        "fixed_in_1100": [s1991_files[f] for f in fixed_in_1100],
        "fixed_in_n1112": [s1991_files[f] for f in fixed_in_n1112],
        "added_after_1991": [n1112_files[f] for f in added_after_1991],
        "s1991_known_bugs": kb_s1991,
        "recent_bug_commits_sample": commits,
    }
    (OUT_DIR / "c5_extracted.json").write_text(json.dumps(out, indent=2))
    print(f"C5 extraction complete: s1991={len(kb_s1991)}, s1100={len(kb_s1100)}, n1112={len(kb_n1112)}, by_origin={by_origin}")
