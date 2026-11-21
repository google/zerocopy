#!/usr/bin/env python3
"""Toy model: does a translation preserve contextual equivalence when
exhausting a bounded resource is an observable outcome?

This is a TOY MODEL written for this report. It is not a model of any
published calculus, compiler, or runtime; it only makes one generic
argument concrete and exhaustively checkable on a tiny language.

Language (both source and target):
    p ::= skip | out(n) | seq(p, p) | cell(p) | val(p)
`cell(p)` allocates one cell for the dynamic extent of `p` (lexical release).
`val(p)`  binds one value for the dynamic extent of `p`.
The target grammar omits `val`; the translation t maps val(p) to cell(t p)
and is homomorphic elsewhere.

Cost policies (what one budget unit pays for):
    arena    : cells cost 1, vals cost 0      (source charges less than target)
    combined : cells cost 1, vals cost 1      (source charges what target charges)
Target always charges cells 1.

Observation at budget B: run left to right; entering cell/val whose cost would
make live cost exceed B stops the run with outcome "oom"; otherwise "done".
Observation = (tuple of outputs so far, outcome).

Contextual equivalence at a fixed budget set: p ~ q iff for every context C
(drawn from the bounded context set) and every budget B in 0..BMAX,
Obs(C[p], B) == Obs(C[q], B). All quantification is BOUNDED (program size,
context size, budgets), so every "equivalent" verdict is a bounded-search
verdict, not a proof; every "distinguished" verdict is a concrete witness.
"""
import itertools
import sys

BMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
PROG_SIZE = int(sys.argv[2]) if len(sys.argv) > 2 else 4
CTX_SIZE = int(sys.argv[3]) if len(sys.argv) > 3 else 4


def progs(size, with_val):
    """All programs with exactly `size` constructors (out uses n in {1})."""
    if size == 1:
        yield ("skip",)
        yield ("out", 1)
        return
    for k in range(1, size - 1):
        for a in progs(k, with_val):
            for b in progs(size - 1 - k, with_val):
                yield ("seq", a, b)
    for a in progs(size - 1, with_val):
        yield ("cell", a)
        if with_val:
            yield ("val", a)


def all_progs(max_size, with_val):
    out = []
    for s in range(1, max_size + 1):
        out.extend(progs(s, with_val))
    return out


HOLE = ("hole",)


def ctxs(size, with_val, fillers):
    """Contexts with exactly `size` constructors besides the hole."""
    if size == 0:
        yield HOLE
        return
    for c in ctxs(size - 1, with_val, fillers):
        yield ("cell", c)
        if with_val:
            yield ("val", c)
    for k in range(0, size):
        for c in ctxs(k, with_val, fillers):
            for f in fillers.get(size - 1 - k, []):
                yield ("seq", c, f)
                yield ("seq", f, c)


def plug(c, p):
    if c == HOLE:
        return p
    tag = c[0]
    if tag in ("cell", "val"):
        return (tag, plug(c[1], p))
    if tag == "seq":
        return ("seq", plug(c[1], p), plug(c[2], p))
    return c


def translate(p):
    tag = p[0]
    if tag == "val":
        return ("cell", translate(p[1]))
    if tag == "cell":
        return ("cell", translate(p[1]))
    if tag == "seq":
        return ("seq", translate(p[1]), translate(p[2]))
    return p


class OOM(Exception):
    pass


def run(p, budget, val_cost):
    outs = []

    def go(q, live):
        tag = q[0]
        if tag == "skip":
            return
        if tag == "out":
            outs.append(q[1])
            return
        if tag == "seq":
            go(q[1], live)
            go(q[2], live)
            return
        cost = 1 if tag == "cell" else val_cost
        if live + cost > budget:
            raise OOM()
        go(q[1], live + cost)

    try:
        go(p, 0)
        return (tuple(outs), "done")
    except OOM:
        return (tuple(outs), "oom")


def obs_vector(p, contexts, val_cost):
    return tuple(run(plug(c, p), b, val_cost) for c in contexts for b in range(BMAX + 1))


def main():
    src = all_progs(PROG_SIZE, with_val=True)
    tgt_fillers = {s: list(progs(s, False)) for s in range(1, CTX_SIZE)}
    src_fillers = {s: list(progs(s, True)) for s in range(1, CTX_SIZE)}
    src_ctx = [c for s in range(CTX_SIZE + 1) for c in ctxs(s, True, src_fillers)]
    tgt_ctx = [c for s in range(CTX_SIZE + 1) for c in ctxs(s, False, tgt_fillers)]
    print(f"programs={len(src)} source_contexts={len(src_ctx)} target_contexts={len(tgt_ctx)} budgets=0..{BMAX}")
    for policy, vcost in (("arena", 0), ("combined", 1)):
        classes = {}
        for p in src:
            classes.setdefault(obs_vector(p, src_ctx, vcost), []).append(p)
        tclasses = {}
        for p in src:
            tclasses.setdefault(obs_vector(translate(p), tgt_ctx, 1), []).append(p)
        tclass_of = {}
        for k, members in tclasses.items():
            for m in members:
                tclass_of[m] = k
        broken = []
        for members in classes.values():
            for a, b in itertools.combinations(members, 2):
                if tclass_of[a] != tclass_of[b]:
                    broken.append((a, b))
        reflect_broken = 0
        sclass_of = {}
        for k, members in classes.items():
            for m in members:
                sclass_of[m] = k
        for members in tclasses.values():
            for a, b in itertools.combinations(members, 2):
                if sclass_of[a] != sclass_of[b]:
                    reflect_broken += 1
        print(f"[{policy}] source classes={len(classes)} target classes={len(tclasses)} "
              f"source-equivalent pairs separated by target contexts={len(broken)} "
              f"target-equivalent pairs separated in source={reflect_broken}")
        if broken:
            # Report the witness with the largest distinguishing budget, to show
            # that a context which pre-allocates cells exposes the difference
            # even when the budget is not tiny.
            best = None
            for a, b in broken:
                for c in tgt_ctx:
                    for bud in range(BMAX + 1):
                        oa = run(plug(c, translate(a)), bud, 1)
                        ob = run(plug(c, translate(b)), bud, 1)
                        if oa != ob and (best is None or bud > best[0]):
                            best = (bud, a, b, c, oa, ob)
            bud, a, b, c, oa, ob = best
            print(f"  witness: p={a} q={b} (equivalent in source under '{policy}')")
            print(f"    target context={c} budget={bud}: t(p)->{oa}  t(q)->{ob}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
