#!/usr/bin/env python3
"""Generator of control-flow graphs with conditionally owed releases, and two
lowerings of each graph: (F) one flag bit per conditional obligation, tested
at the release point, and (D) duplication of the code after each join until
every copy statically knows which releases it owes.

This is a TOY MODEL: costs are counted in abstract IR instructions under the
cost table below, not measured on any compiler. It also emits a C
translation of each graph (flag form) so real compilers can be probed.

Graph family (parameters k, t, mode):
  entry
  for i in 1..k:   if (c_i) { acquire(i) }        # diamond i, join J_i
  body: t opaque instructions                     # shared tail
  exit: release(i) for every i acquired           # owed on some paths
mode = "indep": the k conditions are independent (2^k obligation sets)
mode = "nested": acquire(i) happens only inside the then-arm of i-1, so the
       reachable obligation sets are prefixes {1..j} (k+1 sets)

Usage:
  python3 gen_owed.py table            # toy-model table
  python3 gen_owed.py c <k> <mode> <t> # print C translation (flag form)
"""
import math, sys

COST = dict(branch=1, acquire=1, release=1, body=1, flag_init=1, flag_set=1, flag_test=1)


def obligation_sets(k, mode):
    if mode == "indep":
        return 2 ** k
    if mode == "nested":
        return k + 1
    raise ValueError(mode)


def paths(k, mode):
    # number of entry-to-exit paths in the DAG
    return 2 ** k if mode == "indep" else k + 1


def lower_flags(k, t, mode):
    """Static size, flag bits, and mean executed instructions (uniform
    branch probabilities 1/2) for the flag lowering."""
    size = k * COST["branch"] + k * COST["acquire"] + t * COST["body"]
    size += k * (COST["flag_init"] + COST["flag_set"] + COST["flag_test"] + COST["release"])
    bits = k
    if mode == "indep":
        mean_taken = k / 2.0  # expected number of acquired obligations
        mean_branches = k
    else:
        # nested: branch i executes only if branches 1..i-1 were taken
        mean_branches = sum(0.5 ** i for i in range(k))
        mean_taken = sum(0.5 ** i for i in range(1, k + 1))
    executed = (mean_branches * COST["branch"] + mean_taken * (COST["acquire"] + COST["flag_set"] + COST["release"])
                + t * COST["body"] + k * (COST["flag_init"] + COST["flag_test"]))
    return size, bits, executed


def lower_dup(k, t, mode):
    """Full duplication: every copy of the code after a join is specialised
    on the obligation set reaching it."""
    if mode == "indep":
        # after diamond i there are 2^i copies; diamond i+1 is replicated 2^i times
        size = sum((2 ** i) * (COST["branch"] + COST["acquire"]) for i in range(k))
        copies = 2 ** k
        size += copies * t * COST["body"]
        # each copy releases exactly its own set: sum over sets of |set| = k*2^(k-1)
        size += k * 2 ** (k - 1) * COST["release"] if k else 0
        mean_branches = k
        mean_taken = k / 2.0
    else:
        # nested chain: no join until the end; the only joins are where the
        # else-arms rejoin, so copies = k+1 and branch i appears once
        size = k * (COST["branch"] + COST["acquire"])
        copies = k + 1
        size += copies * t * COST["body"]
        size += sum(range(k + 1)) * COST["release"]
        mean_branches = sum(0.5 ** i for i in range(k))
        mean_taken = sum(0.5 ** i for i in range(1, k + 1))
    executed = mean_branches * COST["branch"] + mean_taken * (COST["acquire"] + COST["release"]) + t * COST["body"]
    return size, 0, executed, copies


def lower_counter(k, t, mode):
    """Counter lowering (valid only for prefix-shaped obligation sets): one
    integer records how many obligations are pending; the exit dispatches
    into a reverse release sequence (as an Ada compiler does for records)."""
    if mode != "nested":
        return None
    size = k * (COST["branch"] + COST["acquire"]) + t * COST["body"]
    size += 1 + k * COST["flag_set"] + 1 + k * COST["release"]  # init, k increments, one dispatch, k releases
    bits = max(1, math.ceil(math.log2(k + 1))) if k else 0
    mean_branches = sum(0.5 ** i for i in range(k))
    mean_taken = sum(0.5 ** i for i in range(1, k + 1))
    executed = mean_branches + mean_taken * (COST["acquire"] + COST["flag_set"] + COST["release"]) + t + 2
    return size, bits, executed


def c_source(k, mode, t):
    lines = ["/* generated: k=%d mode=%s t=%d (flag form) */" % (k, mode, t),
             "void acquire(int); void release(int); void body(int);",
             "void f(%s) {" % ", ".join("int c%d" % i for i in range(1, k + 1))]
    for i in range(1, k + 1):
        lines.append("  int f%d = 0;" % i)
    if mode == "indep":
        for i in range(1, k + 1):
            lines.append("  if (c%d) { acquire(%d); f%d = 1; }" % (i, i, i))
    else:
        indent = "  "
        for i in range(1, k + 1):
            lines.append(indent + "if (c%d) { acquire(%d); f%d = 1;" % (i, i, i))
            indent += "  "
        lines.append("  " + "}" * k)
    for j in range(t):
        lines.append("  body(%d);" % j)
    for i in range(k, 0, -1):
        lines.append("  if (f%d) release(%d);" % (i, i))
    lines.append("}")
    return "\n".join(lines)


if __name__ == "__main__":
    if sys.argv[1] == "table":
        print("mode\tk\tt\tpaths\tobligation_sets\tmin_bits\tF_size\tF_bits\tF_exec\tD_size\tD_copies\tD_exec\tC_size\tC_bits\tC_exec")
        for mode in ("indep", "nested"):
            for k in (1, 2, 3, 4, 6, 8):
                for t in (1, 4, 16):
                    s = obligation_sets(k, mode)
                    fs, fb, fe = lower_flags(k, t, mode)
                    ds, _, de, dc = lower_dup(k, t, mode)
                    c = lower_counter(k, t, mode)
                    cs, cb, ce = c if c else ("-", "-", "-")
                    print("\t".join(map(str, [mode, k, t, paths(k, mode), s, math.ceil(math.log2(s)), fs, fb,
                                               round(fe, 2), ds, dc, round(de, 2), cs, cb,
                                               round(ce, 2) if c else "-"])))
    elif sys.argv[1] == "c":
        print(c_source(int(sys.argv[2]), sys.argv[3], int(sys.argv[4])))
