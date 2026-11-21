"""Toy mutation-sensitivity experiment for tolerance-based assertions.

This is a TOY MODEL written for illustration. It is not Descartes, PIT, or any
study's subject code; its numbers characterise only this 20-line integrator and
this hand-written test, and must not be read as properties of real projects.

Subject: composite Simpson integration plus an a-posteriori error estimate.
Test:    integrate exp on [0, 1] and compare against e - 1 under a relative
         tolerance tau (several oracles are compared, see ORACLES below).
Mutants: generated from the AST of SUBJECT:
  AOR  - swap + <-> -, * <-> / in every BinOp
  CRP  - every numeric constant c -> c+1, c-1, 0, and c*(1+d) for d in 1e-2..1e-10
  RNG  - range(lo, hi) bound shifts by +-1
  EXT  - extreme mutation: replace a whole function body by `return 0.0`
         (Descartes-style "pseudo-tested method" probe)

Run: python3 tolerance_mutation.py
"""
import ast
import copy
import math
import sys
import time

SUBJECT = '''
def simpson(f, a, b, n):
    if n % 2:
        n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        x = a + i * h
        if i % 2:
            s += 4 * f(x)
        else:
            s += 2 * f(x)
    return s * h / 3


def error_estimate(f, a, b, n):
    return abs(simpson(f, a, b, 2 * n) - simpson(f, a, b, n)) / 15.0


def integrate(f, a, b, n=16):
    val = simpson(f, a, b, n)
    est = error_estimate(f, a, b, n)
    return val, est
'''

EXACT = math.e - 1.0
TAUS = [1e-12, 1e-9, 1e-7, 1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 1e-1]
DELTAS = [1e-2, 1e-4, 1e-6, 1e-8, 1e-10]


def load(src):
    ns = {"abs": abs}
    exec(compile(src, "<subject>", "exec"), ns)
    return ns


def run_value(ns):
    """Return (val, est) or the exception class name if the mutant crashes."""
    try:
        val, est = ns["integrate"](math.exp, 0.0, 1.0)  # the test unpacks the pair
        return float(val), float(est)
    except Exception as e:  # crash counts as a kill for every oracle
        return type(e).__name__


class Points(ast.NodeVisitor):
    def __init__(self):
        self.binops, self.consts, self.ranges, self.funcs = [], [], [], []

    def visit_BinOp(self, node):
        if isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)):
            self.binops.append(node)
        self.generic_visit(node)

    def visit_Constant(self, node):
        if isinstance(node.value, (int, float)) and not isinstance(node.value, bool):
            self.consts.append(node)

    def visit_Call(self, node):
        if isinstance(node.func, ast.Name) and node.func.id == "range":
            self.ranges.append(node)
        self.generic_visit(node)

    def visit_FunctionDef(self, node):
        self.funcs.append(node)
        self.generic_visit(node)


SWAP = {ast.Add: ast.Sub, ast.Sub: ast.Add, ast.Mult: ast.Div, ast.Div: ast.Mult}


def mutants():
    tree = ast.parse(SUBJECT)
    p = Points()
    p.visit(tree)
    out = []

    def emit(kind, desc, mutate):
        t = copy.deepcopy(tree)
        q = Points()
        q.visit(t)
        mutate(q)
        ast.fix_missing_locations(t)
        out.append((kind, desc, ast.unparse(t)))

    for i, n in enumerate(p.binops):
        emit("AOR", f"binop#{i} line {n.lineno}: {type(n.op).__name__}->{SWAP[type(n.op)].__name__}",
             lambda q, i=i: setattr(q.binops[i], "op", SWAP[type(q.binops[i].op)]()))
    for i, n in enumerate(p.consts):
        c = n.value
        repl = [("c+1", c + 1), ("c-1", c - 1), ("0", 0)]
        if c != 0:
            repl += [(f"c*(1+{d:g})", c * (1 + d)) for d in DELTAS]
        for name, v in repl:
            if v == c:
                continue
            emit("CRP", f"const#{i} line {n.lineno} ({c!r}) -> {name}",
                 lambda q, i=i, v=v: setattr(q.consts[i], "value", v))
    for i, n in enumerate(p.ranges):
        for argi in range(len(n.args)):
            for dv in (+1, -1):
                def m(q, i=i, argi=argi, dv=dv):
                    a = q.ranges[i].args[argi]
                    q.ranges[i].args[argi] = ast.BinOp(left=a, op=ast.Add(), right=ast.Constant(dv))
                emit("RNG", f"range#{i} arg{argi} {dv:+d}", m)
    for i, fn in enumerate(p.funcs):
        def m(q, i=i):
            q.funcs[i].body = [ast.Return(value=ast.Constant(0.0))]
        emit("EXT", f"extreme: body of {fn.name}() -> return 0.0", m)
    return out


def relerr(v):
    return abs(v - EXACT) / abs(EXACT)


def line_coverage():
    """Statement coverage of SUBJECT under the test, via sys.settrace."""
    ns = load(SUBJECT)
    hit = set()

    def tracer(frame, event, arg):
        if frame.f_code.co_filename == "<subject>" and event == "line":
            hit.add(frame.f_lineno)
        return tracer

    sys.settrace(tracer)
    try:
        ns["integrate"](math.exp, 0.0, 1.0)
    finally:
        sys.settrace(None)
    stmt_lines = {n.lineno for n in ast.walk(ast.parse(SUBJECT)) if isinstance(n, ast.stmt)
                  and not isinstance(n, ast.FunctionDef)}
    return len(hit & stmt_lines), len(stmt_lines), sorted(stmt_lines - hit)


def order_oracle(ns):
    """Observed order of accuracy from n = 8, 16, 32; Simpson's theoretical order is 4."""
    try:
        e = [abs(ns["simpson"](math.exp, 0.0, 1.0, n) - EXACT) for n in (8, 16, 32)]
        if min(e) == 0:
            return False
        p1 = math.log2(e[0] / e[1])
        p2 = math.log2(e[1] / e[2])
        return 3.5 <= p1 <= 4.5 and 3.5 <= p2 <= 4.5
    except Exception:
        return False


def main():
    t0 = time.perf_counter()
    orig = run_value(load(SUBJECT))
    print(f"python {sys.version.split()[0]}")
    print(f"original: value={orig[0]!r} est={orig[1]!r} relerr={relerr(orig[0]):.3e}")
    covered, total, missed = line_coverage()
    print(f"statement coverage of subject under the test: {covered}/{total} (missed lines {missed})")
    min_pass = min(t for t in TAUS if relerr(orig[0]) <= t)
    print(f"smallest tau in grid that the ORIGINAL passes: {min_pass:g}")
    ms = mutants()
    kinds = sorted({k for k, _, _ in ms})
    results = []
    for kind, desc, src in ms:
        ns = load(src)
        r = run_value(ns)
        if isinstance(r, str):
            row = dict(kind=kind, desc=desc, crash=r, identical=False, re=float("inf"), order=False)
        else:
            row = dict(kind=kind, desc=desc, crash=None, identical=(r[0] == orig[0] and r[1] == orig[1]),
                       val_identical=(r[0] == orig[0]), re=relerr(r[0]), order=order_oracle(ns))
        results.append(row)
    n = len(results)
    print(f"mutants: {n} ({', '.join(f'{k}={sum(1 for r in results if r['kind']==k)}' for k in kinds)})")
    print(f"  crashing mutants: {sum(1 for r in results if r['crash'])}")
    print(f"  mutants whose (value, estimate) is bit-identical to original on the test input: {sum(1 for r in results if r['identical'])}")
    print(f"  mutants whose value is bit-identical but estimate differs: {sum(1 for r in results if not r['crash'] and r['val_identical'] and not r['identical'])}")
    print()
    print("Oracle A: |val - (e-1)| <= tau*|e-1|  (analytic reference, relative tolerance)")
    print("  tau        original  killed/total  killed%   (by kind)")
    for tau in TAUS:
        killed = [r for r in results if r["crash"] or r["re"] > tau]
        ok_orig = "pass" if relerr(orig[0]) <= tau else "FAIL"
        bykind = ", ".join(f"{k} {sum(1 for r in killed if r['kind']==k)}/{sum(1 for r in results if r['kind']==k)}" for k in kinds)
        print(f"  {tau:<9g}  {ok_orig:<8}  {len(killed):>3}/{n:<3}      {100*len(killed)/n:5.1f}%   ({bykind})")
    print()
    print("Oracle B: tautological - expected value recomputed by the code under test at test time")
    taut = [r for r in results if r["crash"]]
    print(f"  killed {len(taut)}/{n} (only crashes; a value-comparison against itself always passes)")
    print("Oracle C: golden master - exact equality with the value recorded from the original version")
    gm = [r for r in results if r["crash"] or not r["val_identical"]]
    print(f"  killed {len(gm)}/{n}")
    print("Oracle D: observed order of accuracy in [3.5, 4.5] for n = 8, 16, 32 (no reference tolerance)")
    od = [r for r in results if r["crash"] or not r["order"]]
    print(f"  killed {len(od)}/{n}; original passes: {order_oracle(load(SUBJECT))}")
    tau_def = 1e-6
    surv_a = {id(r) for r in results if not (r["crash"] or r["re"] > tau_def)}
    od_extra = [r for r in results if id(r) in surv_a and not r["order"]]
    print(f"  of the {len(surv_a)} mutants surviving Oracle A at tau=1e-6, Oracle D kills {len(od_extra)}")
    print()
    print("Extreme (Descartes-style) mutants:")
    for r in results:
        if r["kind"] == "EXT":
            verdict_a = "killed" if (r["crash"] or r["re"] > tau_def) else "SURVIVES (pseudo-tested at tau=1e-6)"
            print(f"  {r['desc']}: relerr={r['re']:.3g} crash={r['crash']} -> Oracle A tau=1e-6: {verdict_a}")
    print()
    print("Constant-perturbation (CRP c*(1+d)) kill threshold under Oracle A:")
    for d in DELTAS:
        sel = [r for r in results if r["kind"] == "CRP" and r["desc"].endswith(f"c*(1+{d:g})")]
        line = ", ".join(f"tau={t:g}:{sum(1 for r in sel if r['crash'] or r['re'] > t)}/{len(sel)}" for t in (1e-9, 1e-7, 1e-6, 1e-5, 1e-3))
        print(f"  d={d:g}: {line}")
    print()
    print("Surviving mutants at tau=1e-6 (Oracle A):")
    for r in results:
        if not (r["crash"] or r["re"] > tau_def):
            print(f"  [{r['kind']}] {r['desc']}: relerr={r['re']:.3e} value-identical={r.get('val_identical')} order-ok={r['order']}")
    print(f"\nwall time: {time.perf_counter()-t0:.3f} s")


if __name__ == "__main__":
    main()
