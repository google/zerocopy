#!/usr/bin/env python3
"""Count Lean-4 trust-relevant constructs per repository (read-only).

Usage: python3 -B count_constructs.py <label>=<root>[:<subdir>] ...
Counts are regex matches on source lines outside block/line comments
(approximate: a simple comment stripper; string literals not stripped).
"""
import re, sys, os, json
from pathlib import Path

PATTERNS = {
    "partial def": r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*partial\s+def\b",
    "unsafe": r"\bunsafe\b",
    "@[implemented_by": r"implemented_by",
    "@[extern": r"@\[\s*extern\b|\bextern\b\s*\"",
    "opaque": r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*opaque\b",
    "axiom": r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)*axiom\b",
    "noncomputable": r"\bnoncomputable\b",
    "noncomputable section": r"\bnoncomputable\s+section\b",
    "decreasing_by": r"\bdecreasing_by\b",
    "termination_by": r"\btermination_by\b",
    "sorry": r"\bsorry\b",
    "native_decide": r"\bnative_decide\b",
    "set_option": r"^\s*set_option\b",
    "macro/syntax/elab": r"^\s*(?:@\[[^\]]*\]\s*)?(?:local\s+|scoped\s+)?(?:macro|syntax|elab|macro_rules|elab_rules)\b",
    "initialize": r"^\s*(?:builtin_)?initialize\b",
    "#eval/run_cmd": r"^\s*(?:#eval|run_cmd|#reduce)\b",
    "instance": r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*instance\b",
}

def strip_comments(text):
    # remove nested block comments /- ... -/ (including doc comments) and -- line comments
    out = []
    i = 0; depth = 0; n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth > 0:
            if text[i] == "\n": out.append("\n")
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: break
            i = j; continue
        out.append(text[i]); i += 1
    return "".join(out)

def scan(root, sub):
    base = Path(root) / sub if sub else Path(root)
    files = sorted(p for p in base.rglob("*.lean") if ".lake" not in p.parts)
    tot = {k: 0 for k in PATTERNS}
    where = {k: {} for k in PATTERNS}
    lines = 0
    for p in files:
        raw = p.read_text(errors="replace")
        lines += raw.count("\n")
        t = strip_comments(raw)
        for k, pat in PATTERNS.items():
            c = len(re.findall(pat, t, flags=re.M))
            if c:
                tot[k] += c
                where[k][str(p.relative_to(root))] = c
    return len(files), lines, tot, where

res = {}
for arg in sys.argv[1:]:
    label, spec = arg.split("=", 1)
    root, _, sub = spec.partition(":")
    nf, nl, tot, where = scan(root, sub)
    res[label] = {"files": nf, "lines": nl, "counts": tot, "where": where}
    print(f"== {label} ({root}{'/'+sub if sub else ''}): {nf} files, {nl} lines")
    for k, v in tot.items():
        if v:
            top = sorted(where[k].items(), key=lambda kv: -kv[1])[:6]
            print(f"  {k:24s} {v:6d}  e.g. {top}")
json.dump(res, open(os.environ.get("OUT", "counts.json"), "w"), indent=1)
