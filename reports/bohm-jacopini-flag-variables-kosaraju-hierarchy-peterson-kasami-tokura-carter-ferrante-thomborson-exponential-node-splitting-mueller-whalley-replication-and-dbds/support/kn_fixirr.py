#!/usr/bin/env python3
"""Generate LLVM IR for the complete directed flow graph K_n (each node calls
@node(i) then may jump to any node or exit, chosen by an opaque @next()),
run LLVM's FixIrreducible pass, and report block/instruction counts and the
number of guard predicates it introduces. Compares against the 2^(n-1)
node lower bound that Carter-Ferrante-Thomborson prove for any equivalent
reducible graph obtained without added predicate variables.

Usage: python3 kn_fixirr.py <opt> <llc> <workdir>
"""
import re, subprocess, sys, pathlib

OPT, LLC, WD = sys.argv[1], sys.argv[2], pathlib.Path(sys.argv[3])
OUT = WD / "out"
OUT.mkdir(parents=True, exist_ok=True)


def kn_ir(n):
    L = ["declare void @node(i32)", "declare i32 @next()", "", "define void @kn() {", "entry:", "  br label %n0"]
    for i in range(n):
        L.append(f"n{i}:")
        L.append(f"  call void @node(i32 {i})")
        L.append(f"  %c{i} = call i32 @next()")
        cases = " ".join(f"i32 {j}, label %n{j}" for j in range(n))
        L.append(f"  switch i32 %c{i}, label %exit [ {cases} ]")
    L += ["exit:", "  ret void", "}"]
    return "\n".join(L) + "\n"


def count(ll):
    body = ll[ll.index("define void @kn"):]
    blocks = len(re.findall(r"(?m)^[\w.]+:", body))
    insts = len([l for l in body.splitlines() if l.startswith("  ") and not l.strip().startswith(";")])
    phis_i1 = len(re.findall(r"= phi i1 ", body))
    guards = len(re.findall(r"(?m)^irr\.guard[\w.]*:", body))
    switches = body.count("switch ")
    return blocks, insts, phis_i1, guards, switches


print("n\tblocks_before\tinsts_before\tblocks_after\tinsts_after\tguard_blocks\ti1_phis\tswitches_after\ttext_bytes_before\ttext_bytes_after\tcft_lower_bound_nodes_2^(n-1)")
for n in range(3, 11):
    src = OUT / f"k{n}.ll"
    src.write_text(kn_ir(n))
    fixed = OUT / f"k{n}.fixirr.ll"
    subprocess.run([OPT, "-S", "-passes=lower-switch,fix-irreducible", "-o", str(fixed), str(src)], check=True, timeout=60)
    low = OUT / f"k{n}.low.ll"
    subprocess.run([OPT, "-S", "-passes=lower-switch", "-o", str(low), str(src)], check=True, timeout=60)
    b0 = count(low.read_text())
    b1 = count(fixed.read_text())
    sizes = []
    for f in (low, fixed):
        obj = f.with_suffix(".o")
        subprocess.run([LLC, "-O2", "-filetype=obj", "-o", str(obj), str(f)], check=True, timeout=60)
        nm = subprocess.run(["nm", "-S", str(obj)], capture_output=True, text=True, check=True).stdout
        sizes.append(sum(int(p[1], 16) for p in (l.split() for l in nm.splitlines()) if len(p) == 4 and p[2] == "T"))
    print("\t".join(map(str, [n, b0[0], b0[1], b1[0], b1[1], b1[3], b1[2], b1[4], sizes[0], sizes[1], 2 ** (n - 1)])))
