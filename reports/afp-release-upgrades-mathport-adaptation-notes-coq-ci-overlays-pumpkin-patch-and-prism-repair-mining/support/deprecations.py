#!/usr/bin/env python3
"""Count `@[deprecated ...]` attributes and `set_option backward.*` uses in a Mathlib tree.

Usage: python3 deprecations.py <mathlib-root>
"""
import collections, pathlib, re, sys
root = pathlib.Path(sys.argv[1]) / "Mathlib"
dep = re.compile(r"@\[\s*deprecated\b([^\]]*)\]")
since = re.compile(r'since\s*:=\s*"(\d{4})-(\d{2})-\d{2}"')
back = re.compile(r"^\s*set_option\s+(backward\.[\w.]+)", re.M)
mods = re.compile(r"^deprecated_module\b", re.M)
n = 0; yrs = collections.Counter(); nosince = 0; b = collections.Counter(); dm = 0
for p in root.rglob("*.lean"):
    t = p.read_text(encoding="utf-8", errors="replace")
    for m in dep.finditer(t):
        n += 1
        s = since.search(m.group(1))
        if s: yrs[s.group(1)] += 1
        else: nosince += 1
    for m in back.finditer(t): b[m.group(1)] += 1
    dm += len(mods.findall(t))
print("deprecated_attributes", n)
print("deprecated_by_since_year", dict(sorted(yrs.items())), "without_since", nosince)
print("deprecated_module_commands", dm)
print("set_option_backward_total", sum(b.values()), dict(b.most_common(8)))
