#!/usr/bin/env python3
"""Compile the generated flag-form C graphs with clang and gcc at several
duplication thresholds and record whether each compiler duplicated the
shared tail (static body() call sites > t) or kept the join with flag tests.

Usage: python3 compile_owed.py <clang> <gcc> <workdir>
"""
import re, subprocess, sys, pathlib, itertools
sys.path.insert(0, str(pathlib.Path(__file__).parent))
import gen_owed

CLANG, GCC, WD = sys.argv[1], sys.argv[2], pathlib.Path(sys.argv[3])
OUT = WD / "out"
OUT.mkdir(parents=True, exist_ok=True)

CONFIGS = [
    ("clang", "-O2", []),
    ("clang", "-O2", ["-mllvm", "-jump-threading-threshold=0"]),
    ("clang", "-O2", ["-mllvm", "-jump-threading-threshold=50"]),
    ("clang", "-O3", []),
    ("clang", "-Os", []),
    ("gcc", "-O2", []),
    ("gcc", "-O2", ["--param", "max-jump-thread-duplication-stmts=0"]),
    ("gcc", "-O2", ["--param", "max-jump-thread-duplication-stmts=100"]),
    ("gcc", "-O3", []),
    ("gcc", "-Os", []),
]


def measure(obj):
    dis = subprocess.run(["objdump", "-d", "-r", "--no-show-raw-insn", str(obj)], capture_output=True, text=True, check=True).stdout
    body = len(re.findall(r"R_X86_64_PLT32\s+body", dis))
    rel = len(re.findall(r"R_X86_64_PLT32\s+release", dis))
    jcc = len(re.findall(r"\sj(?:e|ne|a|b|g|l|s|ns|ae|be|ge|le)\s", dis))
    nm = subprocess.run(["nm", "-S", str(obj)], capture_output=True, text=True, check=True).stdout
    size = sum(int(p[1], 16) for p in (l.split() for l in nm.splitlines()) if len(p) == 4 and p[2] == "T")
    return body, rel, jcc, size


print("compiler\tlevel\textra\tmode\tk\tt\tbody_sites\ttail_copies\trelease_sites\tjcc\ttext_bytes")
for mode, k, t in itertools.product(("indep", "nested"), (1, 2, 3, 4, 6), (1, 2, 4)):
    src = OUT / f"g_{mode}_{k}_{t}.c"
    src.write_text(gen_owed.c_source(k, mode, t) + "\n")
    for comp, lvl, extra in CONFIGS:
        cc = CLANG if comp == "clang" else GCC
        obj = OUT / f"g_{mode}_{k}_{t}_{comp}{lvl}_{len(extra) and extra[-1].split('=')[-1] or 'def'}.o"
        subprocess.run([cc, lvl, *extra, "-c", "-o", str(obj), str(src)], check=True, timeout=60)
        body, rel, jcc, size = measure(obj)
        print("\t".join(map(str, [comp, lvl, " ".join(extra) or "default", mode, k, t, body, body // t, rel, jcc, size])))
