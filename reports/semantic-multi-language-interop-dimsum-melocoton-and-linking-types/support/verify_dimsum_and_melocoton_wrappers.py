#!/usr/bin/env python3
"""Bounded executable models for four multi-language interoperability claims.

Standalone probe (Python 3.10+, standard library only, deterministic, no I/O
besides stdout).  It checks, by exhaustive enumeration over small finite
models, the following statements that the accompanying REPORT.md attributes to
primary sources:

  Part A  Dual (demonic/angelic) non-determinism and the branching-sensitive
          simulation of DimSum (Sammler et al., POPL 2023, sections 3.1-3.2):
          UB is the top and NB the bottom of the refinement order, the
          admissible and inadmissible quantifier-commuting laws, and
          "simulation implies trace inclusion" on a finite family of acyclic
          Spec terms.

  Part B  A Melocoton-style OCaml-runtime wrapper (Gueneau et al., OOPSLA
          2023; logsem/melocoton theories/interop/{basics,lang}.v): tagged
          values (2n+1 versus block address), a logical block store that never
          moves, a demonically re-chosen address map at every GC point,
          registered roots, and C glue code that is explored under *every*
          admissible GC outcome.  Unrooted C locals are shown to become stale
          across an allocation and across a foreign callback; the rooted
          variants are shown to be correct for every GC outcome.

  Part C  A full-abstraction / robust-safety counterexample: a component whose
          source-level safety property relies on well-bracketed control flow is
          attacked by a target context that returns through an old return
          continuation; four wrapper disciplines are compared and only a
          one-shot, LIFO-ordered return-token check restores the property.

  Part D  The compilation chain used in the proof of Theorem 5.2 of Abate et
          al. (CSF 2019): it preserves trace equivalence and is correct on
          source-like inputs, yet it does not preserve a robustly satisfied
          safety property.

A passing run establishes only these bounded facts about these models; it is
not a mechanised proof about DimSum, Melocoton, OCaml, or any compiler.

Exit status: 0 when every check holds, 1 otherwise.
"""

from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass
from functools import lru_cache
from typing import Callable, Iterable, Optional

CHECKS: list[tuple[str, bool, str]] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    CHECKS.append((name, bool(ok), detail))
    status = "PASS" if ok else "FAIL"
    line = f"  [{status}] {name}"
    if detail:
        line += f" -- {detail}"
    print(line)


# ---------------------------------------------------------------------------
# Part A: DimSum-style modules with demonic and angelic non-determinism
# ---------------------------------------------------------------------------
#
# A module is (S, ->, s0) with  ->  a subset of  S x (E + {tau}) x P(S).
# Several transitions out of one state are a *demonic* choice; the states
# inside one target set are an *angelic* choice (the module is "in all of
# them").  Finite, acyclic Spec terms are used as states:
#
#   ("vis", e, p)      emit visible event e, continue as p
#   ("ex",  (p...))    demonic choice   (exists x; p(x))   one step per branch
#   ("all", (p...))    angelic choice   (forall x; p(x))   one step to the set
#
# NB (no behaviour) is the empty demonic choice: no transition at all.
# UB (undefined behaviour / "any") is the empty angelic choice: one tau
# transition to the empty set.

Term = tuple
TAU = None
NB: Term = ("ex", ())
UB: Term = ("all", ())


def vis(e: str, p: Term) -> Term:
    return ("vis", e, p)


def ex(*ps: Term) -> Term:
    return ("ex", tuple(ps))


def al(*ps: Term) -> Term:
    return ("all", tuple(ps))


def transitions(s: Term) -> list[tuple[Optional[str], frozenset]]:
    kind = s[0]
    if kind == "vis":
        return [(s[1], frozenset([s[2]]))]
    if kind == "ex":
        return [(TAU, frozenset([p])) for p in s[1]]
    if kind == "all":
        return [(TAU, frozenset(s[1]))]
    raise ValueError(kind)


@lru_cache(maxsize=None)
def _reach(s2: Term, a: Optional[str], impl_succ: frozenset) -> bool:
    """exists Sigma2. s2 ==a==>* Sigma2  and every state of Sigma2 is simulated
    by some state of impl_succ.  `a is None` means no visible event is left."""
    if a is None and any(sim(t1, s2) for t1 in impl_succ):
        return True
    for (b, succ) in transitions(s2):
        if b is TAU:
            rest = a
        elif b == a:
            rest = None
        else:
            continue
        if all(_reach(t, rest, impl_succ) for t in succ):
            return True
    return False


@lru_cache(maxsize=None)
def sim(s1: Term, s2: Term) -> bool:
    """DimSum refinement  s1 <= s2  (implementation s1, specification s2).

    For acyclic terms the coinductive definition coincides with this
    well-founded recursion on s1."""
    for (a, succ1) in transitions(s1):
        if not _reach(s2, a, succ1):
            return False
    return True


@lru_cache(maxsize=None)
def has_trace(s: Term, kappa: tuple) -> bool:
    """kappa in T(M): the multi-step relation of the paper with the full state
    set as target, so the empty trace is always present."""
    if not kappa:
        return True
    for (b, succ) in transitions(s):
        if b is TAU:
            if all(has_trace(t, kappa) for t in succ):
                return True
        elif b == kappa[0]:
            if all(has_trace(t, kappa[1:]) for t in succ):
                return True
    return False


def part_a() -> None:
    print("Part A: dual non-determinism and branching-sensitive simulation")
    alphabet = ("a", "b")
    base = [NB, UB] + [vis(e, t) for e in alphabet for t in (NB, UB)]
    small = list(base)
    for p, q in itertools.combinations_with_replacement(base, 2):
        small.append(ex(p, q))
        small.append(al(p, q))
    family = list(small)
    for e in alphabet:
        for t in small[len(base):]:
            family.append(vis(e, t))
    family = list(dict.fromkeys(family))

    check("A1 UB is top: M <= UB for every M", all(sim(p, UB) for p in family),
          f"{len(family)} terms")
    check("A2 NB is bottom: NB <= M for every M", all(sim(NB, p) for p in family))
    check("A3 UB is not below a module with defined behaviour",
          not sim(UB, vis("a", NB)) and not sim(UB, NB))
    check("A4 reflexivity", all(sim(p, p) for p in family))
    trans_ok = True
    triples = 0
    for p in small:
        for q in small:
            if not sim(p, q):
                continue
            for r in small:
                triples += 1
                if sim(q, r) and not sim(p, r):
                    trans_ok = False
    check("A5 transitivity on the small family", trans_ok,
          f"{len(small)} terms, {triples} (p<=q, r) instances")

    # Quantifier-commuting laws with p(x, y) = vis(c_xy); NB, all c_xy distinct.
    P = {(x, y): vis(f"c{x}{y}", NB) for x in (0, 1) for y in (0, 1)}
    all_all = al(al(P[0, 0], P[0, 1]), al(P[1, 0], P[1, 1]))
    all_all_sw = al(al(P[0, 0], P[1, 0]), al(P[0, 1], P[1, 1]))
    ex_ex = ex(ex(P[0, 0], P[0, 1]), ex(P[1, 0], P[1, 1]))
    ex_ex_sw = ex(ex(P[0, 0], P[1, 0]), ex(P[0, 1], P[1, 1]))
    ex_all = ex(al(P[0, 0], P[0, 1]), al(P[1, 0], P[1, 1]))      # ex x; all y
    all_ex = al(ex(P[0, 0], P[1, 0]), ex(P[0, 1], P[1, 1]))      # all y; ex x
    check("A6 all/all commute (both directions)",
          sim(all_all, all_all_sw) and sim(all_all_sw, all_all))
    check("A7 ex/ex commute (both directions)",
          sim(ex_ex, ex_ex_sw) and sim(ex_ex_sw, ex_ex))
    check("A8 [ex x; all y; p] <= [all y; ex x; p]", sim(ex_all, all_ex))
    check("A9 [all y; ex x; p] is NOT <= [ex x; all y; p]", not sim(all_ex, ex_all))

    q0, q1 = vis("c0", NB), vis("c1", NB)
    ex_vis = ex(vis("e", q0), vis("e", q1))
    vis_ex = vis("e", ex(q0, q1))
    vis_all = vis("e", al(q0, q1))
    all_vis = al(vis("e", q0), vis("e", q1))
    check("A10 [ex x; vis e; p] <= [vis e; ex x; p]", sim(ex_vis, vis_ex))
    check("A11 [vis e; ex x; p] is NOT <= [ex x; vis e; p]", not sim(vis_ex, ex_vis))
    check("A12 [vis e; all x; p] <= [all x; vis e; p]", sim(vis_all, all_vis))
    check("A13 [all x; vis e; p] is NOT <= [vis e; all x; p]", not sim(all_vis, vis_all))

    # Simulation implies trace inclusion; the converse fails (branching).
    events = sorted({e for t in family for e in _events(t)} | {"c0", "c1", "e"})
    traces = [()] + [(x,) for x in events] + [(x, y) for x in events for y in events]
    incl_ok = True
    pairs = 0
    for p in family:
        for q in family:
            if sim(p, q):
                pairs += 1
                if any(has_trace(p, k) and not has_trace(q, k) for k in traces):
                    incl_ok = False
    check("A14 simulation implies trace inclusion (traces up to length 2)", incl_ok,
          f"{pairs} related pairs")
    same_traces = all(has_trace(vis_ex, k) == has_trace(ex_vis, k)
                      for k in traces + [("e", "c0"), ("e", "c1")])
    check("A15 trace-equal modules need not be simulation-related",
          same_traces and not sim(vis_ex, ex_vis))
    # Rely/guarantee reading: an assumption is an angelic choice, an assertion
    # a demonic one;  assume(False) = UB  and  assert(False) = NB.
    assume_false = al()
    assert_false = ex()
    check("A16 assume(False);p refines-to anything, assert(False);p refines anything",
          all(sim(p, assume_false) and sim(assert_false, p) for p in small))


def _events(t: Term) -> set:
    if t[0] == "vis":
        return {t[1]} | _events(t[2])
    out: set = set()
    for p in t[1]:
        out |= _events(p)
    return out


# ---------------------------------------------------------------------------
# Part B: Melocoton-style runtime wrapper, moving GC, roots, and C glue code
# ---------------------------------------------------------------------------

class Stuck(Exception):
    """No rule of the wrapper semantics applies: undefined behaviour."""


def code_int(z: int) -> int:
    return 2 * z + 1


def is_immediate(w: int) -> bool:
    return (w & 1) == 1


TAG_DEFAULT, TAG_INJRV, TAG_CLOSURE, TAG_FOREIGN = 0, 1, 247, 255


@dataclass(frozen=True)
class Block:
    kind: str            # "vblock" | "foreign" | "closure"
    mutable: bool
    tag: int
    fields: tuple        # tuple of lvals: ("int", z) | ("loc", gamma)
    payload: object = None   # C word for foreign blocks, ML body for closures


class Chooser:
    """Replays a prefix of demonic choices and extends it with choice 0."""

    def __init__(self, prefix: list[int]):
        self.prefix = list(prefix)
        self.trace: list[int] = []
        self.arity: list[int] = []

    def choose(self, n: int) -> int:
        if n <= 0:
            raise AssertionError("empty demonic choice")
        i = len(self.trace)
        c = self.prefix[i] if i < len(self.prefix) else 0
        self.trace.append(c)
        self.arity.append(n)
        return c


class Runtime:
    """Wrapper state in C mode: block store zeta, address map theta, root set,
    and the C memory.  Block contents are reachable only through primitives,
    as in the Melocoton model."""

    HEAP_BASE = 0x1000
    CELL_BASE = 0x9000

    def __init__(self, chooser: Chooser, reuse_addresses: bool):
        self.chooser = chooser
        self.reuse = reuse_addresses
        self.zeta: dict[int, Block] = {}
        self.theta: dict[int, int] = {}
        self.roots: set[int] = set()
        self.mem: dict[int, int] = {}
        self._next_gamma = 0
        self._next_heap = self.HEAP_BASE
        self._next_cell = self.CELL_BASE
        self.gc_points = 0
        self.ml_log: list[int] = []

    # -- value representation ------------------------------------------------
    def repr_lval(self, lv: tuple) -> int:
        if lv[0] == "int":
            return code_int(lv[1])
        if lv[1] not in self.theta:
            raise Stuck(f"block g{lv[1]} has no address in the current address map")
        return self.theta[lv[1]]

    def decode(self, w: int) -> tuple:
        if is_immediate(w):
            return ("int", (w - 1) // 2)
        for g, a in self.theta.items():
            if a == w:
                return ("loc", g)
        raise Stuck(f"word {w:#x} is not the address of any live block (stale pointer)")

    def decode_block(self, w: int) -> int:
        lv = self.decode(w)
        if lv[0] != "loc":
            raise Stuck("expected a block pointer, got an immediate")
        return lv[1]

    # -- invariants ----------------------------------------------------------
    def reachable(self, start: Iterable[int]) -> set[int]:
        seen: set[int] = set()
        todo = list(start)
        while todo:
            g = todo.pop()
            if g in seen:
                continue
            seen.add(g)
            for lv in self.zeta[g].fields:
                if lv[0] == "loc":
                    todo.append(lv[1])
        return seen

    def assert_invariants(self) -> None:
        addrs = list(self.theta.values())
        assert len(addrs) == len(set(addrs)), "address map must be injective"
        assert all(a % 2 == 0 for a in addrs), "block addresses are even"
        for g in self.theta:
            for lv in self.zeta[g].fields:
                if lv[0] == "loc":
                    assert lv[1] in self.theta, "GC_correct: live blocks point to live blocks"

    # -- the garbage collector as a demonic choice ---------------------------
    def _fresh_gamma(self) -> int:
        g = self._next_gamma
        self._next_gamma += 1
        return g

    def gc_point(self, must_live: Iterable[int] = ()) -> None:
        """Re-choose the address map.  Every root cell must hold the
        representation of a value under the *current* map (repr_mem); the new
        map must be injective, closed under reachability, and contain every
        rooted block.  All such outcomes are explored."""
        self.gc_points += 1
        root_vals: dict[int, tuple] = {}
        for a in sorted(self.roots):
            if a not in self.mem:
                raise Stuck(f"registered root cell {a:#x} was freed")
            root_vals[a] = self.decode(self.mem[a])
        required = self.reachable(
            [lv[1] for lv in root_vals.values() if lv[0] == "loc"] + list(must_live))
        optional = sorted(set(self.zeta) - required)
        live_sets = []
        for k in range(len(optional) + 1):
            for extra in itertools.combinations(optional, k):
                cand = required | set(extra)
                if self.reachable(cand) == cand:
                    live_sets.append(sorted(cand))
        old = dict(self.theta)
        outcomes = []
        for live in live_sets:
            fresh = {g: self._next_heap + 16 * i for i, g in enumerate(live)}
            options = []
            for g in live:
                opts = [fresh[g]]
                if g in old:
                    opts.append(old[g])
                if self.reuse:
                    opts.extend(a for h, a in sorted(old.items()) if h != g)
                options.append(list(dict.fromkeys(opts)))
            for assignment in itertools.product(*options):
                if len(set(assignment)) == len(assignment):
                    outcomes.append(dict(zip(live, assignment)))
        pick = outcomes[self.chooser.choose(len(outcomes))]
        self._next_heap += 16 * (len(self.zeta) + 1)
        self.theta = pick
        for a, lv in root_vals.items():
            self.mem[a] = self.repr_lval(lv)       # roots are updated by the GC
        self.assert_invariants()

    # -- C memory ------------------------------------------------------------
    def malloc(self) -> int:
        a = self._next_cell
        self._next_cell += 8
        self.mem[a] = code_int(0)
        return a

    def load(self, a: int) -> int:
        if a not in self.mem:
            raise Stuck("load from unallocated C cell")
        return self.mem[a]

    def store(self, a: int, w: int) -> None:
        if a not in self.mem:
            raise Stuck("store to unallocated C cell")
        self.mem[a] = w

    def free(self, a: int) -> None:
        if a not in self.mem:
            raise Stuck("double free")
        del self.mem[a]

    # -- runtime primitives (names follow the Melocoton development) ---------
    def int2val(self, z: int) -> int:
        return code_int(z)

    def val2int(self, w: int) -> int:
        lv = self.decode(w)
        if lv[0] != "int":
            raise Stuck("val2int on a block pointer")
        return lv[1]

    def isblock(self, w: int) -> int:
        return 1 if self.decode(w)[0] == "loc" else 0

    def registerroot(self, a: int) -> None:
        if a in self.roots:
            raise Stuck("root registered twice")
        self.roots.add(a)

    def unregisterroot(self, a: int) -> None:
        if a not in self.roots:
            raise Stuck("unregistering a cell that is not a root")
        self.roots.remove(a)

    def alloc(self, tag: int, size: int) -> int:
        if tag not in (TAG_DEFAULT, TAG_INJRV) or size < 0:
            raise Stuck("alloc: tag must be a value-block tag and size non-negative")
        g = self._fresh_gamma()
        self.zeta[g] = Block("vblock", True, tag, tuple(("int", 0) for _ in range(size)))
        self.gc_point(must_live=[g])
        return self.theta[g]

    def alloc_foreign(self) -> int:
        g = self._fresh_gamma()
        self.zeta[g] = Block("foreign", True, TAG_FOREIGN, (), None)
        self.gc_point(must_live=[g])
        return self.theta[g]

    def modify(self, w: int, i: int, w2: int) -> None:
        g = self.decode_block(w)
        blk = self.zeta[g]
        if blk.kind != "vblock" or not blk.mutable:
            raise Stuck("modify on an immutable or non-value block")
        if not 0 <= i < len(blk.fields):
            raise Stuck("modify out of bounds")
        lv = self.decode(w2)
        fields = blk.fields[:i] + (lv,) + blk.fields[i + 1:]
        self.zeta[g] = Block(blk.kind, blk.mutable, blk.tag, fields)

    def readfield(self, w: int, i: int) -> int:
        blk = self.zeta[self.decode_block(w)]
        if blk.kind != "vblock" or not 0 <= i < len(blk.fields):
            raise Stuck("readfield on a non-value block or out of bounds")
        return self.repr_lval(blk.fields[i])

    def read_tag(self, w: int) -> int:
        return self.zeta[self.decode_block(w)].tag

    def length(self, w: int) -> int:
        blk = self.zeta[self.decode_block(w)]
        if blk.kind != "vblock":
            raise Stuck("length of a non-value block")
        return len(blk.fields)

    def write_foreign(self, w: int, cword: int) -> None:
        g = self.decode_block(w)
        blk = self.zeta[g]
        if blk.kind != "foreign" or not blk.mutable:
            raise Stuck("write_foreign on a non-foreign block")
        self.zeta[g] = Block("foreign", True, TAG_FOREIGN, (), cword)

    def read_foreign(self, w: int) -> int:
        blk = self.zeta[self.decode_block(w)]
        if blk.kind != "foreign" or blk.payload is None:
            raise Stuck("read_foreign on a non-foreign or uninitialised block")
        return blk.payload

    def callback(self, wf: int, warg: int) -> int:
        """Run an ML closure.  ML code may allocate; on return to C the
        address map is re-chosen (one GC point subsumes any number of
        collections that happened while ML was running)."""
        g = self.decode_block(wf)
        blk = self.zeta[g]
        if blk.kind != "closure":
            raise Stuck("callback on a non-closure block")
        arg = self.decode(warg)
        result = blk.payload(self, arg)
        must = [result[1]] if result[0] == "loc" else []
        self.gc_point(must_live=must)
        return self.repr_lval(result)

    # -- ML-side helpers (used to build initial heaps and callback bodies) ----
    def ml_block(self, fields: tuple, tag: int = TAG_DEFAULT, mutable: bool = False) -> int:
        g = self._fresh_gamma()
        self.zeta[g] = Block("vblock", mutable, tag, tuple(fields))
        return g

    def ml_closure(self, body: Callable) -> int:
        g = self._fresh_gamma()
        self.zeta[g] = Block("closure", False, TAG_CLOSURE, (), body)
        return g

    def enter_c(self, live: Iterable[int]) -> None:
        """ML calls C: arguments (and what they reach) get addresses."""
        for i, g in enumerate(sorted(self.reachable(live))):
            self.theta[g] = self.HEAP_BASE - 16 * (i + 1)
        self.assert_invariants()


# C glue code under test ------------------------------------------------------

def caml_local(rt: Runtime) -> int:
    """Melocoton's CAMLlocal: malloc a cell, store Val_int(0), register it."""
    cell = rt.malloc()
    rt.store(cell, rt.int2val(0))
    rt.registerroot(cell)
    return cell


def caml_unregister(rt: Runtime, cell: int) -> None:
    rt.unregisterroot(cell)
    rt.free(cell)


def wrap_unrooted(rt: Runtime, x: int) -> int:
    v = rt.readfield(x, 0)          # C local holding a block address
    r = rt.alloc(TAG_DEFAULT, 1)    # GC point: v may now be stale
    rt.modify(r, 0, v)
    return r


def wrap_rooted(rt: Runtime, x: int) -> int:
    cell = caml_local(rt)
    rt.store(cell, rt.readfield(x, 0))
    r = rt.alloc(TAG_DEFAULT, 1)
    rt.modify(r, 0, rt.load(cell))  # re-read the root after the GC point
    caml_unregister(rt, cell)
    return r


def wrap_rooted_stale_copy(rt: Runtime, x: int) -> int:
    cell = caml_local(rt)
    rt.store(cell, rt.readfield(x, 0))
    v = rt.load(cell)               # copy taken before the GC point
    r = rt.alloc(TAG_DEFAULT, 1)
    rt.modify(r, 0, v)              # the root was updated, the copy was not
    caml_unregister(rt, cell)
    return r


def pair_after_callback_unrooted(rt: Runtime, f: int, x: int) -> int:
    v = rt.readfield(x, 0)
    res = rt.callback(f, rt.int2val(7))   # GC point (ML allocates)
    r = rt.alloc(TAG_DEFAULT, 2)          # GC point
    rt.modify(r, 0, v)
    rt.modify(r, 1, res)
    return r


def pair_after_callback_half_rooted(rt: Runtime, f: int, x: int) -> int:
    cv = caml_local(rt)
    rt.store(cv, rt.readfield(x, 0))
    res = rt.callback(f, rt.int2val(7))   # result kept in an unrooted local
    r = rt.alloc(TAG_DEFAULT, 2)
    rt.modify(r, 0, rt.load(cv))
    rt.modify(r, 1, res)
    caml_unregister(rt, cv)
    return r


def pair_after_callback_rooted(rt: Runtime, f: int, x: int) -> int:
    cv = caml_local(rt)
    rt.store(cv, rt.readfield(x, 0))
    cres = caml_local(rt)
    rt.store(cres, rt.callback(f, rt.int2val(7)))
    r = rt.alloc(TAG_DEFAULT, 2)
    rt.modify(r, 0, rt.load(cv))
    rt.modify(r, 1, rt.load(cres))
    caml_unregister(rt, cres)
    caml_unregister(rt, cv)
    return r


def ml_make_pair(rt: Runtime, arg: tuple) -> tuple:
    """ML callback body: allocates a fresh immutable pair (arg, arg + 1)."""
    g = rt.ml_block((arg, ("int", arg[1] + 1)))
    rt.ml_log.append(g)
    return ("loc", g)


def run_scenario(glue: Callable, with_callback: bool, reuse: bool, prefix: list[int]):
    chooser = Chooser(prefix)
    rt = Runtime(chooser, reuse)
    gy = rt.ml_block((("int", 5),))
    gx = rt.ml_block((("loc", gy),))
    gf = rt.ml_closure(ml_make_pair) if with_callback else None
    rt.enter_c([gx] + ([gf] if gf is not None else []))
    try:
        if with_callback:
            w = glue(rt, rt.theta[gf], rt.theta[gx])
        else:
            w = glue(rt, rt.theta[gx])
        # Returning to ML: the result word is interpreted under the address
        # map that is current at the return (no further GC point in C mode).
        blk = rt.zeta[rt.decode_block(w)]
        expected = (("loc", gy),)
        if with_callback:
            expected = (("loc", gy), ("loc", rt.ml_log[0]))
        leaked_root = bool(rt.roots)
        outcome = "ok" if blk.fields == expected and not leaked_root else "wrong"
    except Stuck:
        outcome = "stuck"
    return chooser, outcome, rt.gc_points


def explore(glue: Callable, with_callback: bool, reuse: bool) -> dict:
    counts = {"ok": 0, "stuck": 0, "wrong": 0, "runs": 0, "gc_points": 0}
    todo: list[list[int]] = [[]]
    while todo:
        prefix = todo.pop()
        chooser, outcome, gcs = run_scenario(glue, with_callback, reuse, prefix)
        counts[outcome] += 1
        counts["runs"] += 1
        counts["gc_points"] = max(counts["gc_points"], gcs)
        for i in range(len(prefix), len(chooser.trace)):
            for alt in range(1, chooser.arity[i]):
                todo.append(chooser.trace[:i] + [alt])
    return counts


def part_b() -> None:
    print("Part B: tagged values, moving GC, registered roots, and C glue code")
    samples = list(range(-70, 71)) + [2 ** 62 - 1, -(2 ** 62), 12345678901234567]
    check("B1 integer tagging 2n+1 is odd and round-trips",
          all(is_immediate(code_int(z)) and (code_int(z) - 1) // 2 == z for z in samples),
          f"{len(samples)} samples")

    def val_long_c(x: int) -> int:        # ((intnat)(((uintnat)x << 1)) + 1), 64 bit
        u = ((x & (2 ** 64 - 1)) << 1) & (2 ** 64 - 1)
        v = (u + 1) & (2 ** 64 - 1)
        return v - 2 ** 64 if v >= 2 ** 63 else v

    max_long, min_long = 2 ** 62 - 1, -(2 ** 62)
    in_range = [z for z in samples if min_long <= z <= max_long]
    check("B2 64-bit Val_long/Long_val agree with 2n+1 exactly on [-2^62, 2^62-1]",
          all(val_long_c(z) == code_int(z) and (val_long_c(z) >> 1) == z for z in in_range)
          and (val_long_c(max_long + 1) >> 1) != max_long + 1,
          "2^62 itself wraps")

    rt = Runtime(Chooser([]), False)
    gy = rt.ml_block((("int", 5),))
    gx = rt.ml_block((("loc", gy),), tag=TAG_INJRV)
    gf = rt.ml_closure(ml_make_pair)
    rt.enter_c([gx, gf])
    ok = (rt.isblock(rt.theta[gx]) == 1 and rt.isblock(code_int(3)) == 0
          and rt.read_tag(rt.theta[gx]) == 1 and rt.read_tag(rt.theta[gf]) == 247
          and rt.length(rt.theta[gx]) == 1 and rt.val2int(rt.readfield(rt.theta[gy], 0)) == 5)
    fb = rt.alloc_foreign()
    ok = ok and rt.read_tag(fb) == 255
    rt.write_foreign(fb, 0xBEEF0)
    ok = ok and rt.read_foreign(fb) == 0xBEEF0
    check("B3 block tags and accessors (0, 1, 247 closure, 255 foreign/custom)", ok)

    stuck_cases = 0
    for action in ("modify_immutable", "val2int_block", "stale_isblock", "double_root",
                   "freed_root"):
        rt = Runtime(Chooser([]), False)
        gy = rt.ml_block((("int", 5),))
        rt.enter_c([gy])
        try:
            if action == "modify_immutable":
                rt.modify(rt.theta[gy], 0, code_int(1))
            elif action == "val2int_block":
                rt.val2int(rt.theta[gy])
            elif action == "stale_isblock":
                rt.isblock(0x7777770)
            elif action == "double_root":
                c = rt.malloc()
                rt.registerroot(c)
                rt.registerroot(c)
            elif action == "freed_root":
                c = caml_local(rt)
                rt.free(c)
                rt.alloc(TAG_DEFAULT, 1)
        except Stuck:
            stuck_cases += 1
    check("B4 misuse is stuck (immutable write, untagging a pointer, stale pointer test,"
          " double registration, freed root at a GC point)", stuck_cases == 5)

    table = [
        ("wrap_unrooted", wrap_unrooted, False),
        ("wrap_rooted", wrap_rooted, False),
        ("wrap_rooted_stale_copy", wrap_rooted_stale_copy, False),
        ("pair_after_callback_unrooted", pair_after_callback_unrooted, True),
        ("pair_after_callback_half_rooted", pair_after_callback_half_rooted, True),
        ("pair_after_callback_rooted", pair_after_callback_rooted, True),
    ]
    # Address reuse (a moved block may take an address vacated by another
    # block) is explored only for the callback-free scenarios; with a callback
    # the number of GC outcomes is too large for an exhaustive run.
    results = {}
    for reuse in (False, True):
        for name, glue, cb in table:
            if reuse and cb:
                continue
            results[name, reuse] = explore(glue, cb, reuse)
            r = results[name, reuse]
            print(f"    {name:<32} reuse={str(reuse):<5} runs={r['runs']:<6} ok={r['ok']:<6}"
                  f" stuck={r['stuck']:<6} wrong={r['wrong']:<5} gc_points={r['gc_points']}")

    def bad(name: str, reuse: bool) -> int:
        return results[name, reuse]["stuck"] + results[name, reuse]["wrong"]

    for reuse in (False, True):
        tagname = "with address reuse" if reuse else "fresh addresses only"
        check(f"B5 rooted glue is correct under every GC outcome ({tagname})",
              bad("wrap_rooted", reuse) == 0 and results["wrap_rooted", reuse]["ok"] > 1,
              f"{results['wrap_rooted', reuse]['ok']} executions")
        check(f"B6 unrooted local across an allocation is caught ({tagname})",
              bad("wrap_unrooted", reuse) > 0,
              f"{bad('wrap_unrooted', reuse)} of {results['wrap_unrooted', reuse]['runs']} executions")
        check(f"B7 rooting the cell does not protect a copy taken earlier ({tagname})",
              bad("wrap_rooted_stale_copy", reuse) > 0)
    check("B8 rooted glue around a foreign callback is correct under every GC outcome",
          bad("pair_after_callback_rooted", False) == 0
          and results["pair_after_callback_rooted", False]["ok"] > 1,
          f"{results['pair_after_callback_rooted', False]['ok']} executions")
    check("B9 unrooted and half-rooted locals across a foreign callback are caught",
          bad("pair_after_callback_unrooted", False) > 0
          and bad("pair_after_callback_half_rooted", False) > 0)
    check("B10 the unrooted bug is schedule dependent (some GC outcomes are benign)",
          results["wrap_unrooted", False]["ok"] > 0 and results["wrap_unrooted", False]["stuck"] > 0)
    check("B11 without address reuse a stale pointer is always stuck, never silently wrong",
          all(r["wrong"] == 0 for (_, reuse), r in results.items() if not reuse))
    check("B12 with address reuse a stale pointer can silently denote another block",
          results["wrap_unrooted", True]["wrong"] > 0,
          f"{results['wrap_unrooted', True]['wrong']} silently wrong executions")


# ---------------------------------------------------------------------------
# Part C: well-bracketed control flow, a target-level attack, return tokens
# ---------------------------------------------------------------------------
#
# Trusted component with one private cell x and one entry point:
#
#     g(cb):  x := 0;  cb();  x := 1;  cb();  return RESULT
#
# RESULT is  x  for the "stateful" variant and the constant 1 for the
# "constant" variant.  Under well-bracketed calls and returns the two are
# indistinguishable and g never returns 0.  A context that can return through
# an older return continuation makes the stateful variant return 0.

@dataclass(frozen=True)
class Kont:
    fid: int      # activation the continuation belongs to
    pc: int       # 1: resume after the first callback, 2: after the second
    depth: int    # stack depth (index of the frame) at capture time
    token: int    # one-shot token minted for this callback


@dataclass(frozen=True)
class CState:
    x: int
    stack: tuple                 # tuple of (fid, pc, token) for pending callbacks
    konts: tuple                 # every continuation ever handed to the context
    next_id: int
    events: tuple
    halted: bool = False


DISCIPLINES = ("source", "target_naive", "target_issued_token", "target_live_frame",
               "target_lifo_one_shot")


def c_call(st: CState) -> CState:
    fid = st.next_id
    k = Kont(fid, 1, len(st.stack), st.next_id + 1)
    return CState(0, st.stack + ((fid, 1, k.token),), st.konts + (k,), st.next_id + 2, st.events)


def c_resume(st: CState, k: Kont, variant: str) -> CState:
    """Resume activation k.fid at k.pc with the stack cut back to k.depth."""
    stack = st.stack[:k.depth]
    if k.pc == 1:
        k2 = Kont(k.fid, 2, len(stack), st.next_id)
        return CState(1, stack + ((k.fid, 2, k2.token),), st.konts + (k2,), st.next_id + 1,
                      st.events)
    result = st.x if variant == "stateful" else 1
    return CState(st.x, stack, st.konts, st.next_id, st.events + (("ret", result),))


def c_actions(st: CState, discipline: str, variant: str, max_depth: int):
    """Enabled context moves as (label, successor) pairs."""
    out = []
    if len(st.stack) < max_depth:
        out.append(("call", c_call(st)))
    top = st.stack[-1] if st.stack else None
    for k in st.konts:
        is_top = top is not None and (k.fid, k.pc, k.token) == top
        label = f"ret(f{k.fid}.{k.pc})"
        if discipline == "source":
            if is_top:
                out.append((label, c_resume(st, k, variant)))
            continue
        if discipline == "target_naive":
            accept = True
        elif discipline == "target_issued_token":
            accept = True                                   # any token ever issued
        elif discipline == "target_live_frame":
            accept = (k.fid, k.pc, k.token) in st.stack     # frame still pending there
        else:
            accept = is_top                                 # LIFO; popping makes it one-shot
        if accept:
            out.append((label, c_resume(st, k, variant)))
        else:
            out.append((label + "!", CState(st.x, st.stack, st.konts, st.next_id,
                                            st.events, True)))
    if discipline not in ("source", "target_naive"):
        out.append(("forge!", CState(st.x, st.stack, st.konts, st.next_id, st.events, True)))
    return out


def c_explore(discipline: str, variant: str, max_actions: int = 6, max_depth: int = 3):
    """Map every context action sequence to the event trace it produces."""
    init = CState(0, (), (), 0, ())
    behaviours: dict[tuple, tuple] = {(): ()}
    rejected = 0
    frontier = [((), init)]
    for _ in range(max_actions):
        nxt = []
        for labels, st in frontier:
            for label, st2 in c_actions(st, discipline, variant, max_depth):
                seq = labels + (label,)
                behaviours[seq] = st2.events
                if st2.halted:
                    rejected += 1
                else:
                    nxt.append((seq, st2))
        frontier = nxt
    return behaviours, rejected


def prefix_closure(traces: Iterable[tuple]) -> set:
    out = set()
    for t in traces:
        for i in range(len(t) + 1):
            out.add(t[:i])
    return out


def part_c() -> None:
    print("Part C: well-bracketed control flow versus an out-of-order-return target context")
    beh = {(d, v): c_explore(d, v) for d in DISCIPLINES for v in ("stateful", "constant")}
    bad_event = ("ret", 0)

    def violates(d: str) -> list:
        return sorted((seq for seq, ev in beh[d, "stateful"][0].items() if bad_event in ev),
                      key=lambda s: (len(s), s))

    def distinguishable(d: str) -> bool:
        a, b = beh[d, "stateful"][0], beh[d, "constant"][0]
        return any(a[seq] != b.get(seq) for seq in a)

    src_traces = prefix_closure(beh["source", "stateful"][0].values())
    check("C1 source contexts: g never returns 0 (robustly satisfied safety property)",
          not violates("source"), f"{len(beh['source', 'stateful'][0])} context behaviours")
    check("C2 source contexts cannot distinguish the stateful and constant variants",
          not distinguishable("source"))
    attacks = violates("target_naive")
    check("C3 naive target: some context makes g return 0", bool(attacks),
          "shortest attack: " + " ; ".join(attacks[0]) if attacks else "")
    check("C4 naive target: the two source-equivalent variants become distinguishable",
          distinguishable("target_naive"))
    tgt_naive = prefix_closure(beh["target_naive", "stateful"][0].values())
    witness = sorted(tgt_naive - src_traces, key=lambda t: (len(t), t))
    check("C5 naive target violates the robustly-safe-compilation shape:"
          " a finite target trace prefix has no source context",
          bool(witness), f"witness prefix {witness[0]}" if witness else "")
    check("C6 unforgeable tokens alone do not help (any issued token accepted)",
          bool(violates("target_issued_token")))
    check("C7 'token of a still-pending frame' is still not enough",
          bool(violates("target_live_frame")))
    check("C8 one-shot LIFO return tokens: g never returns 0",
          not violates("target_lifo_one_shot"))
    check("C9 one-shot LIFO return tokens: variants indistinguishable again",
          not distinguishable("target_lifo_one_shot"))
    tgt_lifo = prefix_closure(beh["target_lifo_one_shot", "stateful"][0].values())
    check("C10 one-shot LIFO return tokens: every target trace prefix is a source trace prefix",
          tgt_lifo <= src_traces)
    rejected = beh["target_lifo_one_shot", "stateful"][1]
    check("C11 the wrapper pays with fail-stop rejections of out-of-order returns",
          rejected > 0, f"{rejected} rejected context moves within the bound")


# ---------------------------------------------------------------------------
# Part D: trace-equivalence preservation does not imply robust safety
# ---------------------------------------------------------------------------
#
# Source: f(x : Bool) |-> e, where e outputs one natural number.  A program is
# the pair (output on true, output on false).  Target: naturals only; true is
# compiled to 0 and false to 1, and
#
#   compile(f) = f(x : Nat) |-> if x < 2 then e  else if x < 3 then f(x)  else 42
#
# so input 2 diverges silently and inputs >= 3 output 42.

def d_source_behaviour(prog: tuple) -> dict:
    return {True: (prog[0],), False: (prog[1],)}


def d_target_behaviour(prog: tuple, inputs: range) -> dict:
    out = {}
    for n in inputs:
        if n == 0:
            out[n] = (prog[0],)
        elif n == 1:
            out[n] = (prog[1],)
        elif n == 2:
            out[n] = ("diverge",)
        else:
            out[n] = (42,)
    return out


def part_d() -> None:
    print("Part D: trace-equivalence preservation without robust safety preservation")
    outputs = (0, 1, 7)
    programs = [(a, b) for a in outputs for b in outputs]
    inputs = range(0, 6)
    rtep = all(d_target_behaviour(p, inputs) == d_target_behaviour(q, inputs)
               for p in programs for q in programs
               if d_source_behaviour(p) == d_source_behaviour(q))
    reflect = all(d_source_behaviour(p) == d_source_behaviour(q)
                  for p in programs for q in programs
                  if d_target_behaviour(p, inputs) == d_target_behaviour(q, inputs))
    check("D1 equal source behaviour implies equal target behaviour (and conversely)",
          rtep and reflect, f"{len(programs)} programs, target inputs 0..5")
    correct = all(d_target_behaviour(p, inputs)[0] == d_source_behaviour(p)[True]
                  and d_target_behaviour(p, inputs)[1] == d_source_behaviour(p)[False]
                  for p in programs)
    check("D2 the compiled program agrees with the source on source-like inputs", correct)
    p0 = (0, 0)
    src_safe = all(42 not in t for t in d_source_behaviour(p0).values())
    tgt_unsafe = [n for n, t in d_target_behaviour(p0, inputs).items() if 42 in t]
    check("D3 'never output 42' holds robustly in the source but not after compilation",
          src_safe and bool(tgt_unsafe), f"target contexts {tgt_unsafe} output 42")
    src_prefixes = prefix_closure(d_source_behaviour(p0).values())
    check("D4 the bad target prefix has no source context (robustly safe compilation fails)",
          (42,) not in src_prefixes)


def main() -> int:
    part_a()
    part_b()
    part_c()
    part_d()
    failed = [name for name, ok, _ in CHECKS if not ok]
    print(f"SUMMARY: {len(CHECKS) - len(failed)} of {len(CHECKS)} checks passed")
    if failed:
        for name in failed:
            print(f"FAILED: {name}")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
