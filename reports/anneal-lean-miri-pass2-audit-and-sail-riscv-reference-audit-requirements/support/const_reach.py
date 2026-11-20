#!/usr/bin/env python3
"""Approximate constant-level reachability over Sail-generated Lean (textual).

Splits each .lean file into top-level declaration chunks at lines starting with
[noncomputable|private|@[..]] def/abbrev/theorem/instance/axiom/structure/inductive.
Each chunk's body tokens (identifiers) are matched against the set of declared
short names; reachability is computed from given roots. Approximate: ignores
namespaces/overloading, treats every same-named decl as referenced.

Usage: python3 -B const_reach.py <dir> <root1,root2,...> [--axioms-only] [--files]
"""
import re, sys
from pathlib import Path
from collections import defaultdict

d = Path(sys.argv[1]); roots = sys.argv[2].split(",")
decl_re = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*"
                     r"(def|abbrev|theorem|instance|axiom|structure|inductive|opaque)\s+([^\s:({\[]+)", re.M)
tok_re = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")

decls = {}          # name -> (kind, file, body)
kinds = {}
by_file_lines = {}
for p in sorted(d.rglob("*.lean")):
    t = p.read_text(errors="replace")
    ms = list(decl_re.finditer(t))
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(t)
        name = m.group(2).split(".")[-1]
        body = t[m.end():end]
        key = name
        if key in decls:
            # merge bodies for duplicate short names (constructor-ish overloads)
            k0, f0, b0 = decls[key]
            decls[key] = (k0, f0, b0 + "\n" + body)
        else:
            decls[key] = (m.group(1), p.name, body)

refs = {}
names = set(decls)
for n, (k, f, b) in decls.items():
    s = set()
    b = re.sub(r'"(?:[^"\\]|\\.)*"', '""', b)   # strip string literals
    b = re.sub(r'--[^\n]*', '', b)                  # strip line comments
    for tok in tok_re.findall(b):
        for part in tok.split("."):
            if part in names and part != n:
                s.add(part)
    refs[n] = s

seen = set(); stack = [r for r in roots if r in decls]
missing = [r for r in roots if r not in decls]
while stack:
    n = stack.pop()
    if n in seen: continue
    seen.add(n)
    stack.extend(refs.get(n, ()))
axs = sorted(n for n in seen if decls[n][0] == "axiom")
files = defaultdict(int)
for n in seen: files[decls[n][2 - 1]] += 0
loc_by_file = defaultdict(int)
for n in seen:
    k, f, b = decls[n]
    loc_by_file[f] += b.count("\n")
print(f"roots={roots} missing={missing} reachable_decls={len(seen)} of {len(decls)} decls")
print(f"reachable body LOC ~ {sum(loc_by_file.values())} across {len(loc_by_file)} files")
print(f"reachable axioms ({len(axs)}): {axs}")
if "--files" in sys.argv:
    for f, l in sorted(loc_by_file.items(), key=lambda kv: -kv[1])[:25]:
        print(f"  {l:7d} {f}")

if "--path" in sys.argv:
    target = sys.argv[sys.argv.index("--path") + 1]
    from collections import deque
    par = {r: None for r in roots if r in decls}; q = deque(par)
    while q:
        n = q.popleft()
        if n == target: break
        for m in sorted(refs.get(n, ())):
            if m not in par:
                par[m] = n; q.append(m)
    path = []; n = target
    while n is not None and n in par:
        path.append(f"{n}[{decls[n][1]}]"); n = par[n]
    print("path:", " <- ".join(path))
