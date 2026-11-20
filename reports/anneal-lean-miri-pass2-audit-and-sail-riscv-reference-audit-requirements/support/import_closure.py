#!/usr/bin/env python3
"""Module import graph + transitive closure + LOC for a Lean source tree.

Usage: python3 -B import_closure.py <srcroot> <root-module>[,<root-module>...] [--prefix P]
Prints closure size, LOC, and the closure module list (in-tree only).
"""
import re, sys
from pathlib import Path

root = Path(sys.argv[1])
roots = sys.argv[2].split(",")
prefix = None
if "--prefix" in sys.argv:
    prefix = sys.argv[sys.argv.index("--prefix") + 1]

mods = {}
for p in root.rglob("*.lean"):
    if ".lake" in p.parts:
        continue
    m = ".".join(p.relative_to(root).with_suffix("").parts)
    mods[m] = p

imp_re = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([\w.«»]+)", re.M)
graph = {}
for m, p in mods.items():
    t = p.read_text(errors="replace")
    # imports must precede first non-import command; good enough to scan header region
    head = t[: 20000]
    graph[m] = [x for x in imp_re.findall(head)]

def closure(rs):
    seen = set(); stack = list(rs)
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m)
        for d in graph.get(m, []):
            if d in mods: stack.append(d)
    return seen

c = closure(roots)
loc = sum(mods[m].read_text(errors="replace").count("\n") for m in c)
ext = sorted({d for m in c for d in graph[m] if d not in mods})
print(f"roots={roots} closure_modules={len(c)} of {len(mods)} in-tree; LOC={loc}")
print("external imports:", ext)
if "--list" in sys.argv:
    for m in sorted(c, key=lambda m: -mods[m].read_text(errors='replace').count("\n")):
        print(f"  {mods[m].read_text(errors='replace').count(chr(10)):7d} {m}")
