#!/usr/bin/env python3
"""Measure flag slots, flag stores, flag tests and code size for the
conditional-cleanup probe (cond_cleanup.cpp) at several optimization levels.

Usage: python3 measure_clang.py <clang++> <workdir>
Outputs a TSV table on stdout. Requires clang++, nm and objdump on PATH.
"""
import re, subprocess, sys, pathlib, collections

CXX = sys.argv[1]
WD = pathlib.Path(sys.argv[2])
SRC = WD / "cond_cleanup.cpp"
FUNCS = ["t_cond", "t_and", "t_two", "t_ext", "t_ext2", "t_arr", "t_new", "t_base", "t_cond_dup"]
LEVELS = ["-O0", "-O1", "-O2", "-O3", "-Os"]
EH = {"eh": ["-fexceptions"], "noeh": ["-fno-exceptions"]}

def run(cmd):
    subprocess.run(cmd, check=True, timeout=60)

def mangled_to_func(name):
    for f in FUNCS:
        if re.match(r"_Z%d%s" % (len(f), f), name):
            return f
    return None

def ir_counts(ll):
    """Per function: flag allocas, flag stores, flag loads (named by clang),
    plus generic i1 allocas and i1 phis that survive optimization."""
    out = {}
    cur = None
    for line in ll.splitlines():
        m = re.match(r"define .*@(_Z\w+)\(", line)
        if m:
            cur = mangled_to_func(m.group(1))
            if cur:
                out[cur] = collections.Counter()
            continue
        if line.startswith("}"):
            cur = None
            continue
        if not cur:
            continue
        c = out[cur]
        if re.search(r"%cleanup\.(cond|isactive)[0-9]* = alloca i1", line):
            c["flag_alloca"] += 1
        if re.search(r"store i1 (true|false), ptr %cleanup\.(cond|isactive)", line):
            c["flag_store"] += 1
        if re.search(r"load i1, ptr %cleanup\.(cond|isactive)", line):
            c["flag_load"] += 1
        if re.search(r"= alloca i1\b", line):
            c["i1_alloca"] += 1
        if re.search(r"= phi i1\b", line):
            c["i1_phi"] += 1
        if re.search(r"%arrayinit\.endOfInit[0-9]* = alloca ptr", line):
            c["endofinit_alloca"] += 1
    return out

def obj_counts(obj):
    sizes = {}
    nm = subprocess.run(["nm", "-S", "--defined-only", str(obj)], capture_output=True, text=True, check=True).stdout
    for line in nm.splitlines():
        parts = line.split()
        if len(parts) == 4 and parts[2] in ("T", "t", "W"):
            f = mangled_to_func(parts[3])
            if f:
                sizes[f] = int(parts[1], 16)
    dis = subprocess.run(["objdump", "-d", "-r", "--no-show-raw-insn", str(obj)], capture_output=True, text=True, check=True).stdout
    counts = {f: collections.Counter() for f in FUNCS}
    cur = None
    for line in dis.splitlines():
        m = re.match(r"[0-9a-f]+ <(_Z\w+)>:", line)
        if m:
            cur = mangled_to_func(m.group(1))
            continue
        if not cur or ":" not in line:
            continue
        ins = line.split(":", 1)[1].strip()
        op = ins.split()[0] if ins else ""
        if re.fullmatch(r"j(?!mp)[a-z]+", op):
            counts[cur]["jcc"] += 1
        if op.startswith("R_X86_64") and "_ZN1SD" in ins:
            counts[cur]["dtor_calls"] += 1  # static call/jmp sites of S::~S
        if op == "movb" and re.match(r"movb\s+\$0x[01],-?0x[0-9a-f]+\(%rbp\)", ins):
            counts[cur]["stack_byte_flag_stores"] += 1
        if op == "testb" and "(%rbp)" in ins:
            counts[cur]["stack_byte_tests"] += 1
    return sizes, counts

print("\t".join(["eh", "level", "func", "flag_alloca", "flag_store", "flag_load", "i1_alloca", "i1_phi",
                 "endofinit_alloca", "text_bytes", "jcc", "dtor_calls", "stack_byte_flag_stores", "stack_byte_tests"]))
for eh, ehflags in EH.items():
    for lvl in LEVELS:
        tag = f"{eh}{lvl}"
        ll = WD / f"out/{tag}.ll"
        obj = WD / f"out/{tag}.o"
        base = [CXX, "-std=c++17", lvl, "-fno-discard-value-names", *ehflags, str(SRC)]
        run(base + ["-S", "-emit-llvm", "-o", str(ll)])
        run(base + ["-c", "-o", str(obj)])
        irc = ir_counts(ll.read_text())
        sizes, oc = obj_counts(obj)
        for f in FUNCS:
            c = irc.get(f, collections.Counter())
            o = oc.get(f, collections.Counter())
            print("\t".join(map(str, [eh, lvl, f, c["flag_alloca"], c["flag_store"], c["flag_load"], c["i1_alloca"],
                                       c["i1_phi"], c["endofinit_alloca"], sizes.get(f, "-"), o["jcc"], o["dtor_calls"],
                                       o["stack_byte_flag_stores"], o["stack_byte_tests"]])))
