#!/usr/bin/env python3
"""Differential check: Lean lowering tables vs. measured rustc assembly.

`RustAtomicLoweringSoundness.lean` prints one `TABLE|<config>|<function>|<tokens>`
line per (configuration, probe function) pair: the shared-memory instruction
skeleton its lowering table predicts. This script reduces each measured
assembly body to the same token vocabulary and compares the two, for

  * the preserved 13-configuration measurement
    (`atomic_lowering_13_config_measurements.json`), and
  * the live probe (`live_probe_results.json`, written by `run_live_probe.py`).

It also checks the optimization canaries, checks that the measured code is not
what the three lowering mutants of the Lean development would emit, plants one
fault in the table to confirm that the comparison detects it, and reports how
much of the preserved assembly text the live toolchain reproduces verbatim.
Standard library only.

    python3 check_lowering_model.py            # uses the files next to this script
    python3 check_lowering_model.py --lean-table /tmp/table.txt

Exit status is non-zero when any compared cell or canary check fails.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# measurement configuration -> Lean configuration (None: not comparable, with reason)
PRESERVED_CONFIGS = {
    "x86_64_1.99.1_O3": "x86_64.redzone",
    "x86_64_1.99.1_O3_no_redzone": "x86_64.no_redzone",
    "x86_64_1.99.1_O0": None,  # wrappers call un-inlined core::sync::atomic methods
    "x86_64_1.100.0_O3": "x86_64.redzone",
    "x86_64_nightly_O3": "x86_64.redzone",
    "aarch64_v80_default_outline_1.99.1_O3": "aarch64.v80_outlined",
    "aarch64_v80_no_outline_1.99.1_O3": "aarch64.v80_inline",
    "aarch64_lse_1.99.1_O3": "aarch64.lse",
    "aarch64_lse_rcpc_1.99.1_O3": "aarch64.lse_rcpc",
    "aarch64_lse_rcpc3_1.99.1_O3": "aarch64.lse_rcpc",
    "i686_default_sse2_1.99.1_O3": "i686.sse2",
    "i686_nosse2_1.99.1_O3": "i686.x87_only",
    "s390x_nightly_O3": "s390x.z10",
}
LIVE_CONFIGS = {
    "x86_64_O3": "x86_64.redzone",
    "x86_64_O3_no_redzone": "x86_64.no_redzone",
    "x86_64_O0": None,
    "aarch64_v80_default_outline_O3": "aarch64.v80_outlined",
    "aarch64_v80_no_outline_O3": "aarch64.v80_inline",
    "aarch64_lse_O3": "aarch64.lse",
    "aarch64_lse_rcpc_O3": "aarch64.lse_rcpc",
    "aarch64_lse_rcpc3_O3": "aarch64.lse_rcpc",
    "i686_default_sse2_O3": "i686.sse2",
    "i686_nosse2_O3": "i686.x87_only",
    "i686_sse1_only_O3": "i686.sse1_only",
    "s390x_O3": "s390x.z10",
}

MEM_X86 = re.compile(r"(-?\d+)?\((%[a-z0-9]+)[^)]*\)")


def x86_tokens(lines: list[str]) -> list[str]:
    out = []
    for raw in lines:
        parts = raw.replace(",", " ").split()
        if not parts:
            continue
        locked = parts[0] == "lock"
        if locked:
            parts = parts[1:]
        if not parts:
            continue
        mn, ops = parts[0], raw.split(None, 2 if locked else 1)[-1] if len(parts) > 1 else ""
        operands = [o.strip() for o in ops.split(",")] if ops else []
        mems = [(i, MEM_X86.search(o)) for i, o in enumerate(operands)]
        mems = [(i, m) for i, m in mems if m]
        on_stack = any(m.group(2) in ("%rsp", "%esp") for _, m in mems)
        rip = any(m.group(2) == "%rip" for _, m in mems)
        if mn == "mfence":
            out.append("mfence")
        elif locked and mn.startswith("or") and on_stack:
            disp = mems[0][1].group(1) or "0"
            out.append(f"lock-or-sp({int(disp)})")
        elif locked and mn.startswith("xadd"):
            out.append("lock-xadd")
        elif locked and mn.startswith("cmpxchg8b"):
            out.append("lock-cmpxchg8b")
        elif locked and mn.startswith("cmpxchg"):
            out.append("lock-cmpxchg")
        elif not mems or on_stack or rip:
            continue
        elif mn.startswith("xchg"):
            out.append("xchg")
        elif mn == "fildll":
            out.append("x87-load64")
        elif mn == "fistpll":
            out.append("x87-store64")
        elif mn in ("movq", "movlps", "movsd", "movss", "movaps", "movups") and "%xmm" in ops:
            out.append("sse-load64" if mems[0][0] == 0 else "sse-store64")
        elif mn.startswith("mov"):
            # AT&T order: source first, destination last.
            out.append("mov-load" if mems[0][0] == 0 and len(operands) > 1 else "mov-store")
    return out


A64_PLAIN = re.compile(r"^(ldaxr|ldxr|stlxr|stxr|ldar|ldapr|stlr|ldr|str)(b|h)?$")
A64_LSE = re.compile(r"^(cas|swp|ldadd|ldclr)(al|a|l)?(b|h)?$")
A64_HELPER = re.compile(r"^__aarch64_(cas|swp|ldadd|ldclr)\d+_(relax|acq_rel|acq|rel)$")


def a64_tokens(lines: list[str]) -> list[str]:
    out = []
    for raw in lines:
        parts = raw.replace(",", " ").split()
        if not parts:
            continue
        mn = parts[0]
        if mn == "dmb" and len(parts) > 1:
            out.append("dmb-" + parts[1])
        elif mn == "clrex":
            out.append("clrex")
        elif mn == "bl" and len(parts) > 1 and A64_HELPER.match(parts[1]):
            m = A64_HELPER.match(parts[1])
            out.append(f"bl:__aarch64_{m.group(1)}_{m.group(2)}")
        elif "[sp" in raw or ":got" in raw:
            continue  # frame and GOT accesses
        elif A64_PLAIN.match(mn):
            out.append(A64_PLAIN.match(mn).group(1))
        elif A64_LSE.match(mn):
            m = A64_LSE.match(mn)
            out.append(m.group(1) + (m.group(2) or ""))
    return out


S390_LOAD = {"l", "lg", "ly", "lgf", "llgf", "llgc", "llc", "lt", "ltg"}
S390_STORE = {"st", "stg", "sty", "stc", "mvhi", "mvghi", "mvi"}
S390_CS = {"cs", "csg", "csy"}


def s390_tokens(lines: list[str]) -> list[str]:
    out = []
    for raw in lines:
        parts = raw.replace(",", " ").split()
        if not parts:
            continue
        mn = parts[0]
        if mn == "bcr" and parts[1:3] == ["15", "%r0"]:
            out.append("bcr15")
        elif mn in S390_CS:
            out.append("cs")
        elif mn in S390_LOAD:
            out.append("load")
        elif mn in S390_STORE:
            out.append("store")
    return out


def tokens_for(lean_cfg: str, lines: list[str]) -> list[str]:
    if lean_cfg.startswith("aarch64"):
        return a64_tokens(lines)
    if lean_cfg.startswith("s390x"):
        return s390_tokens(lines)
    return x86_tokens(lines)


def load_lean_table(path: str) -> dict[str, dict[str, list[str]]]:
    table: dict[str, dict[str, list[str]]] = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            if not line.startswith("TABLE|"):
                continue
            _, cfg, fn, toks = line.rstrip("\n").split("|", 3)
            table.setdefault(cfg, {})[fn] = [t for t in toks.split(";") if t]
    return table


def compare(label, configs, mapping, get_asm, table, report):
    for name in sorted(configs):
        lean_cfg = mapping.get(name)
        rec = {"lean_config": lean_cfg, "compared": 0, "matched": 0, "mismatches": []}
        report[f"{label}:{name}"] = rec
        if lean_cfg is None:
            rec["skipped"] = "not inlined at opt-level=0 or not mapped"
            continue
        bodies = get_asm(configs[name])
        if bodies is None:
            rec["skipped"] = "configuration did not compile"
            continue
        for fn, expected in sorted(table[lean_cfg].items()):
            if fn not in bodies or bodies[fn] is None:
                continue
            got = tokens_for(lean_cfg, bodies[fn])
            rec["compared"] += 1
            if got == expected:
                rec["matched"] += 1
            else:
                rec["mismatches"].append({"function": fn, "lean": expected, "measured": got})


def count(tokens, kinds):
    return sum(1 for t in tokens if t in kinds)


LOADS = {"mov-load", "ldr", "load"}
STORES = {"mov-store", "str", "store"}


def canary_checks(label, name, lean_cfg, bodies, irs, checks):
    def tk(fn):
        return tokens_for(lean_cfg, bodies[fn])

    def add(desc, ok, detail=None):
        checks.append({"where": f"{label}:{name}", "check": desc, "ok": bool(ok), "detail": detail})

    add("dead relaxed load is still emitted (1 load)",
        count(tk("canary_dead_relaxed_load"), LOADS) == 1, tk("canary_dead_relaxed_load"))
    add("adjacent relaxed stores are not merged (2 stores)",
        count(tk("canary_adjacent_relaxed_stores"), STORES) == 2,
        tk("canary_adjacent_relaxed_stores"))
    with_f, without_f = tk("canary_cfence_blocks_store_hoist"), tk("canary_no_cfence_store_forwarding")
    add("compiler fences change nothing in the &mut canary (same skeleton, 2 stores, 0 loads)",
        with_f == without_f and count(with_f, STORES) == 2 and count(with_f, LOADS) == 0, with_f)
    ir = irs.get("canary_cfence_blocks_store_hoist") or []
    add("both singlethread fences survive in LLVM IR",
        sum('fence syncscope("singlethread")' in l for l in ir) == 2, ir)
    if "canary_publish_then_overwrite_with_cfence" in bodies:
        a = tk("canary_publish_then_overwrite_with_cfence")
        b = tk("canary_publish_then_overwrite_without_cfence")
        add("with the compiler fence all 3 stores are emitted", count(a, STORES) == 3, a)
        add("without it the pre-publication store is eliminated (2 stores)",
            count(b, STORES) == 2, b)


# What the three lowering mutants of the Lean development would emit, per Lean
# configuration: (function, mutant token list). The real compiler must differ.
MUTANTS = {
    "aarch64.lse_rcpc": [("at_u32_load_seqcst", ["ldapr"])],            # CE1
    "x86_64.no_redzone": [("at_fence_seqcst", ["lock-or-sp(-64)"])],    # CE2
    "x86_64.redzone": [("at_u32_store_seqcst", ["mov-store"]),          # CE4
                       ("at_fence_seqcst", [])],
    "i686.sse2": [("at_u64_store_seqcst", ["sse-store64"]), ("at_fence_seqcst", [])],
    "i686.x87_only": [("at_u64_store_seqcst", ["x87-store64"]), ("at_fence_seqcst", [])],
    "s390x.z10": [("at_u32_store_seqcst", ["store"]), ("at_fence_seqcst", [])],
}


def mutant_exclusion(label, name, lean_cfg, bodies, checks):
    for fn, mutant in MUTANTS.get(lean_cfg, []):
        got = tokens_for(lean_cfg, bodies[fn])
        checks.append({"where": f"{label}:{name}",
                       "check": f"measured {fn} is not the mutant sequence {mutant}",
                       "ok": got != mutant, "detail": got})


def planted_fault_is_detected(table, preserved) -> bool:
    """Sanity check of the comparison itself: corrupt one table cell in memory."""
    bad = {cfg: dict(fns) for cfg, fns in table.items()}
    bad["aarch64.lse_rcpc"]["at_u32_load_seqcst"] = ["ldapr"]
    report: dict = {}
    compare("selftest", preserved, PRESERVED_CONFIGS, lambda c: c["asm"], bad, report)
    return sum(len(r["mismatches"]) for r in report.values()) == 2


# Configurations present in both data sets (preserved name, live name).
SHARED = [
    ("x86_64_1.99.1_O3", "x86_64_O3"),
    ("x86_64_1.99.1_O3_no_redzone", "x86_64_O3_no_redzone"),
    ("aarch64_v80_default_outline_1.99.1_O3", "aarch64_v80_default_outline_O3"),
    ("aarch64_v80_no_outline_1.99.1_O3", "aarch64_v80_no_outline_O3"),
    ("aarch64_lse_1.99.1_O3", "aarch64_lse_O3"),
    ("aarch64_lse_rcpc_1.99.1_O3", "aarch64_lse_rcpc_O3"),
    ("aarch64_lse_rcpc3_1.99.1_O3", "aarch64_lse_rcpc3_O3"),
    ("i686_default_sse2_1.99.1_O3", "i686_default_sse2_O3"),
    ("i686_nosse2_1.99.1_O3", "i686_nosse2_O3"),
]
ATOMIC_IR = re.compile(r"load atomic|store atomic|atomicrmw|cmpxchg|fence")


def raw_reproduction(preserved, live) -> dict:
    """Does the live toolchain emit the same assembly text as the preserved one?

    The preserved lines were cut at the first '#', so the live lines are cut the
    same way; branch-label numbers depend on function order and are ignored.
    """
    def norm(lines):
        return [re.sub(r"\.LBB\d+_\d+", ".LBB", l.split("#", 1)[0].rstrip()) for l in lines]

    asm_total = asm_same = ir_total = ir_same = 0
    differing = []
    for pname, lname in SHARED:
        if live.get(lname, {}).get("returncode") != 0:
            continue
        for fn, body in sorted(preserved[pname]["asm"].items()):
            lf = live[lname]["functions"][fn]
            asm_total += 1
            if norm(body) == norm(lf["asm"]):
                asm_same += 1
            else:
                differing.append(f"asm {pname} {fn}")
            a = [l for l in preserved[pname]["llvm_ir"][fn] if ATOMIC_IR.search(l) and not l.startswith("define")]
            b = [l for l in lf["llvm_ir"] if ATOMIC_IR.search(l)]
            ir_total += 1
            if a == b:
                ir_same += 1
            else:
                differing.append(f"ir {pname} {fn}: {a} vs {b}")
    return {"assembly_bodies_compared": asm_total, "assembly_bodies_identical": asm_same,
            "atomic_ir_line_sets_compared": ir_total, "atomic_ir_line_sets_identical": ir_same,
            "differing": differing}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean-table", default=os.path.join(HERE, "lean_lowering_table.txt"))
    ap.add_argument("--preserved",
                    default=os.path.join(HERE, "atomic_lowering_13_config_measurements.json"))
    ap.add_argument("--live", default=os.path.join(HERE, "live_probe_results.json"))
    ap.add_argument("--out", default=None, help="write the JSON summary here")
    args = ap.parse_args()

    table = load_lean_table(args.lean_table)
    report: dict = {}
    checks: list = []

    with open(args.preserved, encoding="utf-8") as f:
        preserved = json.load(f)["configs"]
    compare("preserved", preserved, PRESERVED_CONFIGS, lambda c: c["asm"], table, report)
    for name, cfg in sorted(preserved.items()):
        lean_cfg = PRESERVED_CONFIGS.get(name)
        if lean_cfg:
            canary_checks("preserved", name, lean_cfg, cfg["asm"], cfg["llvm_ir"], checks)
            mutant_exclusion("preserved", name, lean_cfg, cfg["asm"], checks)

    live_meta = None
    reproduction = None
    if os.path.exists(args.live):
        with open(args.live, encoding="utf-8") as f:
            live_doc = json.load(f)
        live_meta = {k: live_doc.get(k) for k in ("rustc_version_line", "rustc_commit_hash", "llvm_version")}
        live = live_doc["configs"]

        def live_asm(c):
            if c.get("returncode") != 0:
                return None
            return {fn: v["asm"] for fn, v in c["functions"].items()}

        reproduction = raw_reproduction(preserved, live)
        compare("live", live, LIVE_CONFIGS, live_asm, table, report)
        for name, cfg in sorted(live.items()):
            lean_cfg = LIVE_CONFIGS.get(name)
            if lean_cfg and cfg.get("returncode") == 0:
                bodies = live_asm(cfg)
                irs = {fn: v["llvm_ir"] for fn, v in cfg["functions"].items()}
                canary_checks("live", name, lean_cfg, bodies, irs, checks)
                mutant_exclusion("live", name, lean_cfg, bodies, checks)

    selftest = planted_fault_is_detected(table, preserved)
    compared = sum(r["compared"] for r in report.values())
    matched = sum(r["matched"] for r in report.values())
    canary_ok = sum(c["ok"] for c in checks)
    summary = {
        "lean_table_cells": sum(len(v) for v in table.values()),
        "live_toolchain": live_meta,
        "cells_compared": compared,
        "cells_matched": matched,
        "canary_and_mutant_checks": len(checks),
        "canary_and_mutant_checks_ok": canary_ok,
        "planted_table_fault_detected": selftest,
        "live_reproduces_preserved": reproduction,
        "per_configuration": report,
        "failed_canary_checks": [c for c in checks if not c["ok"]],
        "checks": checks,
    }
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=1, sort_keys=True)
            f.write("\n")
    for key in sorted(report):
        r = report[key]
        note = r.get("skipped") or f'{r["matched"]}/{r["compared"]}'
        print(f"{key:55s} -> {str(r['lean_config']):22s} {note}")
        for m in r["mismatches"]:
            print(f"    MISMATCH {m['function']}: lean={m['lean']} measured={m['measured']}")
    print(f"cells: {matched}/{compared} matched; canary and mutant-exclusion checks: "
          f"{canary_ok}/{len(checks)} ok; planted table fault detected: {selftest}")
    for c in summary["failed_canary_checks"]:
        print("    CHECK FAIL", c)
    if reproduction:
        print(f"live vs preserved raw text: {reproduction['assembly_bodies_identical']}/"
              f"{reproduction['assembly_bodies_compared']} assembly bodies, "
              f"{reproduction['atomic_ir_line_sets_identical']}/"
              f"{reproduction['atomic_ir_line_sets_compared']} atomic IR line sets identical")
        for d in reproduction["differing"]:
            print("    DIFFERS", d)
    return 0 if (matched == compared and canary_ok == len(checks) and selftest) else 1


if __name__ == "__main__":
    sys.exit(main())
