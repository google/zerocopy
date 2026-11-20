#!/usr/bin/env python3
"""
Toy model of condition-level structural coverage (MC/DC) and fault detection.

This is a self-contained TOY MODEL. It does not measure any real avionics or
automotive program, coverage tool, or test generator. It enumerates, exactly,
which test sets satisfy several MC/DC variants for small Boolean programs and
which semantically defined mutants those test sets are guaranteed to detect.

Criteria (per decision d with atomic conditions c_1..c_k, all atoms evaluated
without side effects so short-circuit evaluation does not change atom values):
  DC   decision coverage: d takes both outcomes.
  UC   unique-cause MC/DC: for every c_i, two tests in the set differ in c_i,
       agree on every other c_j of d, and give different outcomes of d.
  MASK masking MC/DC: for every c_i, two tests in the set differ in c_i, give
       different outcomes of d, and in each of the two tests c_i alone
       determines d (flipping c_i with the other c_j fixed flips d).
  OBS  observable masking MC/DC: MASK, and additionally in each of the two
       tests flipping c_i at d (and only there) changes the program output.
       (Toy analogue of the observability requirement of OMC/DC; real OMC/DC
       is defined over dataflow paths in Lustre/Simulink models.)
A test set is adequate for a program if it meets the criterion for every
decision of that program. Mutants are alternative implementations of the
same function; a test set kills a mutant if some test's output differs from
the specification output.

Run:  python3 mcdc_toy.py            (deterministic; prints tables)
"""
import itertools, sys
from collections import Counter

# ---------------------------------------------------------------------------
# Program representation: a program maps an input dict to an output and a list
# of decision records. A decision record is (decision_id, atoms, formula) where
# atoms is a tuple of atom values and formula maps an atom tuple to an outcome.
# `force` = (decision_id, atom_index) flips that atom at that decision only.
# ---------------------------------------------------------------------------

def run(prog, inp, force=None):
    trace = []
    def decide(did, atoms, formula):
        atoms = list(atoms)
        if force is not None and force[0] == did:
            atoms[force[1]] = not atoms[force[1]]
        atoms = tuple(atoms)
        out = formula(atoms)
        trace.append((did, atoms, formula))
        return out
    out = prog(inp, decide)
    return out, trace

AND = lambda xs: all(xs)
OR = lambda xs: any(xs)

# --- Program family 1: n-ary conjunction t = a&b&c&d feeding out = t | ovr ---
def p_single(i, decide):
    t = decide('D', (i['a'], i['b'], i['c'], i['d']), AND)
    return decide('O', (t, i['ovr']), OR)

def p_nested(i, decide):
    t = False
    if decide('Ia', (i['a'],), AND):
        if decide('Ib', (i['b'],), AND):
            if decide('Ic', (i['c'],), AND):
                if decide('Id', (i['d'],), AND):
                    t = True
    return decide('O', (t, i['ovr']), OR)

def p_fold(i, decide):
    t1 = decide('F1', (i['a'], i['b']), AND)
    t2 = decide('F2', (t1, i['c']), AND)
    t = decide('F3', (t2, i['d']), AND)
    return decide('O', (t, i['ovr']), OR)

def spec1(i):
    return (i['a'] and i['b'] and i['c'] and i['d']) or i['ovr']

VARS1 = ['a', 'b', 'c', 'd', 'ovr']
INPUTS1 = [dict(zip(VARS1, bits)) for bits in itertools.product([False, True], repeat=5)]

def mutants1():
    """Semantic mutants of the conjunction (ovr path unchanged)."""
    ms = {}
    core = ['a', 'b', 'c', 'd']
    for v in core:
        ms[f'negate {v}'] = (lambda v: lambda i: (all((not i[x]) if x == v else i[x] for x in core)) or i['ovr'])(v)
        ms[f'{v} stuck-at-1'] = (lambda v: lambda i: (all(True if x == v else i[x] for x in core)) or i['ovr'])(v)
        ms[f'{v} stuck-at-0'] = (lambda v: lambda i: (all(False if x == v else i[x] for x in core)) or i['ovr'])(v)
    # operator replacement at each fold position: ((a?b)?c)?d
    ops = {'and': lambda x, y: x and y, 'or': lambda x, y: x or y}
    for pos in range(3):
        def m(i, pos=pos):
            seq = [i['a'], i['b'], i['c'], i['d']]
            acc = seq[0]
            for k in range(3):
                acc = ops['or' if k == pos else 'and'](acc, seq[k + 1])
            return acc or i['ovr']
        ms[f'&&->|| at fold position {pos + 1}'] = m
    for v, w in [('a', 'b'), ('c', 'd'), ('d', 'a')]:
        ms[f'variable {v} replaced by {w}'] = (lambda v, w: lambda i: (all(i[w] if x == v else i[x] for x in core)) or i['ovr'])(v, w)
    ms['override path dropped'] = lambda i: (i['a'] and i['b'] and i['c'] and i['d'])
    return ms

# --- Program family 2: n-ary "all distinct" implemented as a pairwise chain ---
def make_alldistinct(domain):
    vars_ = ['x', 'y', 'z']
    inputs = [dict(zip(vars_, v)) for v in itertools.product(range(domain), repeat=3)]
    def impl_chain(i, decide):   # x != y && y != z   (missing x != z)
        return decide('C', (i['x'] != i['y'], i['y'] != i['z']), AND)
    def spec_formula(i, decide):  # x != y && y != z && x != z
        return decide('S', (i['x'] != i['y'], i['y'] != i['z'], i['x'] != i['z']), AND)
    def spec(i):
        return len({i['x'], i['y'], i['z']}) == 3
    return inputs, impl_chain, spec_formula, spec

# ---------------------------------------------------------------------------
# Obligations and adequacy
# ---------------------------------------------------------------------------

def obligations(prog, inputs, crit):
    """Return list of obligations; each obligation is a list of bitmasks over
    test indices (single tests for DC, pairs otherwise) any of which satisfies it."""
    traces = [run(prog, inp)[1] for inp in inputs]
    outs = [run(prog, inp)[0] for inp in inputs]
    dec = {}
    for ti, tr in enumerate(traces):
        for (did, atoms, formula) in tr:
            dec.setdefault(did, []).append((ti, atoms, formula))
    obls = []
    for did, recs in sorted(dec.items()):
        k = len(recs[0][1])
        formula = recs[0][2]
        if crit == 'DC':
            for want in (False, True):
                obls.append([1 << ti for (ti, atoms, f) in recs if f(atoms) == want])
            continue
        for ci in range(k):
            sat = []
            for (t1, a1, f), (t2, a2, _) in itertools.combinations(recs, 2):
                if a1[ci] == a2[ci] or f(a1) == f(a2):
                    continue
                if crit == 'UC':
                    if any(a1[j] != a2[j] for j in range(k) if j != ci):
                        continue
                else:
                    def determines(a):
                        b = list(a); b[ci] = not b[ci]
                        return f(tuple(b)) != f(a)
                    if not (determines(a1) and determines(a2)):
                        continue
                    if crit == 'OBS':
                        def observable(ti):
                            return run(prog, inputs[ti], force=(did, ci))[0] != outs[ti]
                        if not (observable(t1) and observable(t2)):
                            continue
                sat.append((1 << t1) | (1 << t2))
            obls.append(sat)
    return obls

def adequate(mask, obls):
    return all(any((p & mask) == p for p in ob) for ob in obls)

def minimum_sets(obls, n, kmax=8):
    if any(len(ob) == 0 for ob in obls):
        return None, []          # some obligation is infeasible
    for k in range(1, kmax + 1):
        found = []
        for combo in itertools.combinations(range(n), k):
            m = 0
            for c in combo:
                m |= 1 << c
            if adequate(m, obls):
                found.append(m)
        if found:
            return k, found
    return None, []

def kills(mask, inputs, spec, mut):
    return any(mut(inputs[t]) != spec(inputs[t]) for t in range(len(inputs)) if mask >> t & 1)

# ---------------------------------------------------------------------------

def family1():
    print('== Family 1: t = a&&b&&c&&d ; out = t || ovr  (32 input vectors) ==')
    print('Mutants: 4 negations, 8 stuck-at, 3 operator replacements, 3 variable replacements, 1 dropped override path = 19')
    ms = mutants1()
    # equivalent mutants (never differ from spec on any input) are excluded
    live = {k: m for k, m in ms.items() if any(m(i) != spec1(i) for i in INPUTS1)}
    print(f'non-equivalent mutants: {len(live)} of {len(ms)}')
    print(f"{'structure':10s} {'crit':5s} {'min |T|':>7s} {'#min sets':>9s} {'guaranteed kill':>15s} {'mean kill':>9s} {'worst kill':>10s}")
    rows = []
    for sname, prog in [('single', p_single), ('nested', p_nested), ('fold', p_fold)]:
        for crit in ['DC', 'UC', 'MASK', 'OBS']:
            obls = obligations(prog, INPUTS1, crit)
            k, sets = minimum_sets(obls, len(INPUTS1))
            if k is None:
                print(f'{sname:10s} {crit:5s}  infeasible'); continue
            per_set = [sum(kills(s, INPUTS1, spec1, m) for m in live.values()) for s in sets]
            guaranteed = sum(all(kills(s, INPUTS1, spec1, m) for s in sets) for m in live.values())
            mean = sum(per_set) / len(per_set)
            rows.append((sname, crit, k, len(sets), guaranteed, mean, min(per_set)))
            print(f'{sname:10s} {crit:5s} {k:7d} {len(sets):9d} {guaranteed:>9d}/{len(live):<5d} {mean:9.2f} {min(per_set):10d}')
    return rows

def family2():
    print()
    print('== Family 2: spec allDistinct(x,y,z); implementation x!=y && y!=z (pairwise chain, x!=z omitted) ==')
    for domain in (3, 4):
        inputs, impl, spec_formula, spec = make_alldistinct(domain)
        revealing = [t for t, i in enumerate(inputs) if run(impl, i)[0] != spec(i)]
        print(f'domain {{0..{domain - 1}}}^3: {len(inputs)} vectors, {len(revealing)} fault-revealing (x==z, x!=y)')
        mut_impl = lambda i: run(impl, i)[0]
        for label, prog in [('coverage measured on implementation', impl), ('coverage measured on requirement formula', spec_formula)]:
            for crit in ['DC', 'UC', 'MASK']:
                obls = obligations(prog, inputs, crit)
                k, sets = minimum_sets(obls, len(inputs), kmax=5)
                if k is None:
                    print(f'  {label:40s} {crit:5s} infeasible within size 5'); continue
                det = sum(kills(s, inputs, spec, mut_impl) for s in sets)
                print(f'  {label:40s} {crit:5s} min |T|={k}  min sets={len(sets):6d}  sets revealing the omission={det:6d} ({100.0 * det / len(sets):5.1f}%)')

if __name__ == '__main__':
    family1()
    family2()
