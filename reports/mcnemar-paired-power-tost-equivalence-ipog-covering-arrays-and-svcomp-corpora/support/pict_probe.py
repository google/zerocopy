#!/usr/bin/env python3
"""Covering-array probes against a locally built microsoft/pict binary.

What is PICT's behaviour and what is this script's own measurement:
  * PICT (the subject) produces the arrays: row counts and wall times below are
    PICT's.  The script only invokes it.
  * Everything else -- the enumeration of valid t-tuples, coverage checking,
    random-split loss, two-array overlap, filter-after-generation loss and the
    reference IPOG implementation -- is this script's own code, independent of
    PICT.  The constraint predicate `valid_row` is a hand transcription of the
    PICT constraints in MODEL_CONSTRAINTS and is cross-checked against PICT's
    own exhaustive (/o:4) output.

Usage: python3 pict_probe.py /path/to/pict  [outdir]
"""
import itertools
import os
import random
import statistics
import subprocess
import sys
import time

PARAMS = [
    ("Construct", ["loop", "recursion", "pointer_arith", "array_index", "bitfield", "union_pun", "closure"]),
    ("Rule", ["bounds", "null_deref", "int_overflow", "uninit_read", "alias"]),
    ("Fault", ["none", "off_by_one", "missing_guard", "wrong_width", "use_after_free"]),
    ("Context", ["straight_line", "nested_branch", "callee", "generic"]),
]

MODEL_CONSTRAINTS = """
IF [Fault] = "use_after_free" THEN [Rule] IN {"alias", "null_deref"};
IF [Fault] = "wrong_width" THEN [Rule] IN {"int_overflow", "bounds"};
IF [Construct] = "bitfield" THEN [Fault] <> "use_after_free" AND [Rule] <> "alias";
IF [Construct] = "closure" THEN [Context] <> "straight_line";
IF [Fault] = "off_by_one" THEN [Construct] IN {"loop", "array_index", "pointer_arith", "recursion"};
"""


def valid_row(r):
    """Python transcription of MODEL_CONSTRAINTS (r is a dict name->value)."""
    if r["Fault"] == "use_after_free" and r["Rule"] not in ("alias", "null_deref"):
        return False
    if r["Fault"] == "wrong_width" and r["Rule"] not in ("int_overflow", "bounds"):
        return False
    if r["Construct"] == "bitfield" and not (r["Fault"] != "use_after_free" and r["Rule"] != "alias"):
        return False
    if r["Construct"] == "closure" and r["Context"] == "straight_line":
        return False
    if r["Fault"] == "off_by_one" and r["Construct"] not in ("loop", "array_index", "pointer_arith", "recursion"):
        return False
    return True


def model_text(constrained, extra_params=()):
    lines = ["%s: %s" % (n, ", ".join(v)) for n, v in list(PARAMS) + list(extra_params)]
    txt = "\n".join(lines) + "\n"
    if constrained:
        txt += MODEL_CONSTRAINTS
    return txt


def run_pict(pict, model_path, args, reps=1):
    times, out = [], None
    for _ in range(reps):
        t0 = time.perf_counter()
        p = subprocess.run([pict, model_path] + args, capture_output=True, text=True, check=True)
        times.append(time.perf_counter() - t0)
        out = p.stdout
    lines = [l for l in out.splitlines() if l.strip()]
    header = lines[0].split("\t")
    rows = [dict(zip(header, l.split("\t"))) for l in lines[1:]]
    return rows, statistics.median(times), out


def all_rows(constrained, params=PARAMS):
    names = [n for n, _ in params]
    res = []
    for combo in itertools.product(*[v for _, v in params]):
        r = dict(zip(names, combo))
        if not constrained or valid_row(r):
            res.append(r)
    return res


def tuples_of(rows, t, names):
    s = set()
    for r in rows:
        for sub in itertools.combinations(names, t):
            s.add(tuple((n, r[n]) for n in sub))
    return s


def required_tuples(t, constrained):
    """Valid t-tuples = t-projections of valid full rows (exact, by enumeration)."""
    names = [n for n, _ in PARAMS]
    return tuples_of(all_rows(constrained), t, names)


def ipog(t, params):
    """Unconstrained IPOG-Test (Lei et al., ECBS 2007, Fig. 2), straightforward
    transcription: exhaustive first t params, then horizontal growth (greedy value
    choice) and vertical growth (fill don't-cares or add a row) per parameter.
    Tie-breaking: first value / first row.  Returns list of dicts."""
    names = [n for n, _ in params]
    dom = dict(params)
    ts = [dict(zip(names[:t], c)) for c in itertools.product(*[dom[n] for n in names[:t]])]
    for i in range(t, len(names)):
        pi_name = names[i]
        prev = names[:i]
        pi_set = set()
        for sub in itertools.combinations(prev, t - 1):
            for vals in itertools.product(*[dom[n] for n in sub]):
                for v in dom[pi_name]:
                    pi_set.add(tuple(zip(sub, vals)) + ((pi_name, v),))
        # horizontal growth
        for row in ts:
            best_v, best_cov = None, -1
            for v in dom[pi_name]:
                cov = 0
                for sub in itertools.combinations(prev, t - 1):
                    if any(row.get(n) is None for n in sub):
                        continue
                    if tuple((n, row[n]) for n in sub) + ((pi_name, v),) in pi_set:
                        cov += 1
                if cov > best_cov:
                    best_v, best_cov = v, cov
            row[pi_name] = best_v
            for sub in itertools.combinations(prev, t - 1):
                if any(row.get(n) is None for n in sub):
                    continue
                pi_set.discard(tuple((n, row[n]) for n in sub) + ((pi_name, best_v),))
        # vertical growth
        for sigma in sorted(pi_set):
            placed = False
            for row in ts:
                if all(row.get(n) is None or row.get(n) == v for n, v in sigma):
                    for n, v in sigma:
                        row[n] = v
                    placed = True
                    break
            if not placed:
                nr = {n: None for n in names[: i + 1]}
                for n, v in sigma:
                    nr[n] = v
                ts.append(nr)
    for row in ts:  # fill remaining don't-cares
        for n in names:
            if row.get(n) is None:
                row[n] = dom[n][0]
    return ts


def main():
    pict = sys.argv[1]
    outdir = sys.argv[2] if len(sys.argv) > 2 else "/tmp/pict_probe_out"
    os.makedirs(outdir, exist_ok=True)
    names = [n for n, _ in PARAMS]
    mu = os.path.join(outdir, "model_unconstrained.txt")
    mc = os.path.join(outdir, "model_constrained.txt")
    open(mu, "w").write(model_text(False))
    open(mc, "w").write(model_text(True))
    full_u, full_c = all_rows(False), all_rows(True)
    print("model: %s; |cartesian|=%d valid=%d" % (
        " x ".join(str(len(v)) for _, v in PARAMS), len(full_u), len(full_c)))

    # 0. cross-check the Python predicate against PICT exhaustive output
    ex_rows, _, _ = run_pict(pict, mc, ["/o:max"])
    ex_set = {tuple(r[n] for n in names) for r in ex_rows}
    py_set = {tuple(r[n] for n in names) for r in full_c}
    print("[0] PICT /o:max rows=%d  python-valid rows=%d  sets equal=%s" % (len(ex_set), len(py_set), ex_set == py_set))

    # 1. sizes, times, coverage
    print("[1] t, constrained, threads -> rows, median wall s (5 reps), required t-tuples, covered, invalid rows emitted")
    arrays = {}
    for t in (2, 3):
        for cons, path in ((False, mu), (True, mc)):
            req = required_tuples(t, cons)
            for thr in ("/t:1", None):
                args = ["/o:%d" % t] + ([thr] if thr else [])
                rows, med, out = run_pict(pict, path, args, reps=5)
                cov = tuples_of(rows, t, names)
                bad = sum(1 for r in rows if cons and not valid_row(r))
                print("    t=%d cons=%-5s %-8s rows=%3d  wall=%.4f  required=%4d covered=%4d missing=%d  invalid_rows=%d" % (
                    t, cons, thr or "/t:auto", len(rows), med, len(req), len(req & cov), len(req - cov), bad))
                arrays[(t, cons)] = rows
                open(os.path.join(outdir, "array_t%d_%s.tsv" % (t, "c" if cons else "u")), "w").write(out)

    # 2. random 50/50 split of one array
    print("[2] random 50/50 split of ONE PICT array, 10000 splits (python RNG seed 12345)")
    rng = random.Random(12345)
    for t in (2, 3):
        for cons in (False, True):
            rows = arrays[(t, cons)]
            req = required_tuples(t, cons)
            fracs_min, both_full = [], 0
            lost = []
            for _ in range(10000):
                idx = list(range(len(rows)))
                rng.shuffle(idx)
                h = len(rows) // 2
                A = [rows[i] for i in idx[:h]]
                B = [rows[i] for i in idx[h:]]
                ca = len(req & tuples_of(A, t, names)) / len(req)
                cb = len(req & tuples_of(B, t, names)) / len(req)
                fracs_min.append(min(ca, cb))
                lost.append((1 - ca + 1 - cb) / 2)
                if ca == 1.0 and cb == 1.0:
                    both_full += 1
            print("    t=%d cons=%-5s rows=%3d  mean lost/side=%.3f  min-side coverage: mean=%.3f min=%.3f max=%.3f  P(both sides complete)=%d/10000" % (
                t, cons, len(rows), statistics.mean(lost), statistics.mean(fracs_min), min(fracs_min), max(fracs_min), both_full))

    # 3. two arrays with different randomisation values
    print("[3] two independent PICT arrays (/r:N), each checked for full coverage; overlap and novelty")
    for t in (2, 3):
        for cons, path in ((False, mu), (True, mc)):
            req = required_tuples(t, cons)
            for (ra, rb) in ((1, 2), (101, 202)):
                A, _, _ = run_pict(pict, path, ["/o:%d" % t, "/r:%d" % ra])
                B, _, _ = run_pict(pict, path, ["/o:%d" % t, "/r:%d" % rb])
                ca = req <= tuples_of(A, t, names)
                cb = req <= tuples_of(B, t, names)
                sa = {tuple(r[n] for n in names) for r in A}
                sb = {tuple(r[n] for n in names) for r in B}
                req_up = required_tuples(t + 1, cons) if t + 1 <= len(names) else set()
                up_a = tuples_of(A, t + 1, names) & req_up
                up_b = tuples_of(B, t + 1, names) & req_up
                print("    t=%d cons=%-5s /r:%d,/r:%d rows=%d,%d  A complete=%s B complete=%s  identical rows shared=%d  (t+1)-tuples in B not in A=%d of %d in B" % (
                    t, cons, ra, rb, len(A), len(B), ca, cb, len(sa & sb), len(up_b - up_a), len(up_b)))

    # 4. split as an extra parameter at strength t+1
    print("[4] Split parameter {design, heldout} added, generated at /o:t+1")
    for t in (2,):
        for cons in (False, True):
            path = os.path.join(outdir, "model_split_%s.txt" % ("c" if cons else "u"))
            open(path, "w").write(model_text(cons, extra_params=[("Split", ["design", "heldout"])]))
            rows, med, _ = run_pict(pict, path, ["/o:%d" % (t + 1)], reps=3)
            req = required_tuples(t, cons)
            A = [r for r in rows if r["Split"] == "design"]
            B = [r for r in rows if r["Split"] == "heldout"]
            print("    t=%d cons=%-5s rows=%d (design %d, heldout %d) wall=%.4f  design covers all %d-tuples=%s heldout=%s" % (
                t, cons, len(rows), len(A), len(B), med, t, req <= tuples_of(A, t, names), req <= tuples_of(B, t, names)))

    # 4b. split parameter outside a sub-model of order t, global order 2
    print("[4b] Split outside sub-model { Construct, Rule, Fault, Context } @ t, global /o:2")
    for t in (2, 3):
        for cons in (False, True):
            path = os.path.join(outdir, "model_split_sub%d_%s.txt" % (t, "c" if cons else "u"))
            txt = "\n".join("%s: %s" % (n, ", ".join(v)) for n, v in list(PARAMS) + [("Split", ["design", "heldout"])]) + "\n"
            txt += "{ Construct, Rule, Fault, Context } @ %d\n" % t
            if cons:
                txt += MODEL_CONSTRAINTS
            open(path, "w").write(txt)
            rows, med, _ = run_pict(pict, path, ["/o:2"], reps=3)
            req = required_tuples(t, cons)
            A = [r for r in rows if r["Split"] == "design"]
            B = [r for r in rows if r["Split"] == "heldout"]
            sa = {tuple(r[n] for n in names) for r in A}
            sb = {tuple(r[n] for n in names) for r in B}
            print("    t=%d cons=%-5s rows=%d (design %d, heldout %d) wall=%.4f  design complete=%s heldout complete=%s  identical configs on both sides=%d" % (
                t, cons, len(rows), len(A), len(B), med, req <= tuples_of(A, t, names), req <= tuples_of(B, t, names), len(sa & sb)))

    # 5. filter-after-generation loss
    print("[5] generate WITHOUT constraints, then delete rows violating constraints")
    for t in (2, 3):
        rows = arrays[(t, False)]
        kept = [r for r in rows if valid_row(r)]
        req = required_tuples(t, True)
        cov = tuples_of(kept, t, names) & req
        print("    t=%d rows=%d kept=%d  valid t-tuples=%d covered after filtering=%d lost=%d (%.1f%%)" % (
            t, len(rows), len(kept), len(req), len(cov), len(req - cov), 100.0 * len(req - cov) / len(req)))

    # 6. reference IPOG (this script) vs PICT, unconstrained
    print("[6] reference IPOG (python, unconstrained, params in declared order and in descending domain size)")
    for t in (2, 3):
        for order_name, params in (("declared", PARAMS), ("desc-domain", sorted(PARAMS, key=lambda p: -len(p[1])))):
            t0 = time.perf_counter()
            rows = ipog(t, params)
            el = time.perf_counter() - t0
            req = required_tuples(t, False)
            cov = tuples_of(rows, t, names)
            print("    t=%d order=%-11s IPOG rows=%3d  missing=%d  python wall=%.3fs   (PICT rows=%d)" % (
                t, order_name, len(rows), len(req - cov), el, len(arrays[(t, False)])))
            if order_name == "declared":
                with open(os.path.join(outdir, "ipog_t%d_u.tsv" % t), "w") as f:
                    f.write("\t".join(names) + "\n")
                    for r in rows:
                        f.write("\t".join(r[n] for n in names) + "\n")
    # lower bound: product of the two (t) largest domains
    doms = sorted((len(v) for _, v in PARAMS), reverse=True)
    print("    trivial lower bounds: t=2 >= %d, t=3 >= %d" % (doms[0] * doms[1], doms[0] * doms[1] * doms[2]))

    # 7. a larger model for generation latency
    print("[7] latency on a larger synthetic model (10 params x 5 values, unconstrained)")
    big = os.path.join(outdir, "model_big.txt")
    open(big, "w").write("".join("P%d: a, b, c, d, e\n" % i for i in range(10)))
    for t in (2, 3, 4):
        for thr in ("/t:1", None):
            args = ["/o:%d" % t] + ([thr] if thr else [])
            reps = 3
            rows, med, _ = run_pict(pict, big, args, reps=reps)
            print("    t=%d %-8s rows=%d median wall=%.3fs" % (t, thr or "/t:auto", len(rows), med))


if __name__ == "__main__":
    main()
