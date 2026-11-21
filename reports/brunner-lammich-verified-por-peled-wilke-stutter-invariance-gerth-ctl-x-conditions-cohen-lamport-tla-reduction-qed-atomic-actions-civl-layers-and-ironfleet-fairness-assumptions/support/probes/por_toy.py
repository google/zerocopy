#!/usr/bin/env python3
"""Toy explicit-state models illustrating why partial-order reduction (POR)
conditions depend on the property class.

This is a TOY MODEL written for illustration. It is not any real model checker,
and its results are statements about these hand-built transition systems only.

Each system is a product of independent processes. A global state is a tuple of
local states plus a set of atomic propositions derived from it. Actions of
different processes are independent (they commute and do not disable each
other); actions of the same process are dependent. An action is *visible* if it
can change the valuation of an atomic proposition.

For each case we compute the full state graph and a reduced graph obtained by
expanding only a chosen ample set at selected states, check the classical ample
conditions C0 (non-empty), C1 (no dependent action can occur before an ample
action on any path that avoids the ample set), C2 (proper ample sets are
invisible), C3 (cycle proviso: no cycle consists only of states whose ample set
is proper), and the extra branching-time condition C4 (a proper ample set is a
singleton), then evaluate a property on both graphs.

Run: python3 por_toy.py      (Python 3.8+, standard library only)
"""
from itertools import product


class System:
    def __init__(self, procs, props):
        # procs: list of dicts  local_state -> list of (action_name, next_local_state)
        # props: function global_state -> frozenset of atomic propositions
        self.procs = procs
        self.props = props
        self.owner = {}
        for i, p in enumerate(procs):
            for ls, outs in p.items():
                for a, _ in outs:
                    self.owner[a] = i

    def enabled(self, s):
        out = []
        for i, ls in enumerate(s):
            for a, nls in self.procs[i].get(ls, []):
                out.append((a, s[:i] + (nls,) + s[i + 1:]))
        return out

    def dependent(self, a, b):
        return self.owner[a] == self.owner[b]

    def visible(self, a):
        # visible iff some occurrence of a changes the proposition valuation
        for s in self.reachable(self.init):
            for b, t in self.enabled(s):
                if b == a and self.props(s) != self.props(t):
                    return True
        return False

    def reachable(self, s0, ample=None):
        seen, stack = {s0}, [s0]
        while stack:
            s = stack.pop()
            for a, t in self.successors(s, ample):
                if t not in seen:
                    seen.add(t)
                    stack.append(t)
        return seen

    def successors(self, s, ample=None):
        en = self.enabled(s)
        if ample and s in ample:
            return [(a, t) for a, t in en if a in ample[s]]
        return en


def check_conditions(sysm, ample):
    """Check C0-C4 for an ample-set map {state: set(actions)} over the full graph."""
    res = {"C0": True, "C1": True, "C2": True, "C3": True, "C4": True}
    full = sysm.reachable(sysm.init)
    for s, A in ample.items():
        if s not in full:
            continue
        en = {a for a, _ in sysm.enabled(s)}
        proper = A < en
        if not A and en:
            res["C0"] = False
        if proper and any(sysm.visible(a) for a in A):
            res["C2"] = False
        if proper and len(A) != 1:
            res["C4"] = False
        # C1: explore paths from s using only non-ample actions; no action dependent on A may fire
        seen, stack = {s}, [s]
        while stack and proper:
            u = stack.pop()
            for b, v in sysm.enabled(u):
                if b in A:
                    continue
                if any(sysm.dependent(b, a) for a in A):
                    res["C1"] = False
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
    # C3: every cycle of the reduced graph must contain a fully expanded state
    red = sysm.reachable(sysm.init, ample)
    proper_states = {s for s in red if s in ample and ample[s] < {a for a, _ in sysm.enabled(s)}}
    # search for a cycle inside proper_states
    color = {}

    def dfs(u):
        color[u] = 1
        for _, v in sysm.successors(u, ample):
            if v not in proper_states:
                continue
            if color.get(v) == 1:
                return True
            if v not in color and dfs(v):
                return True
        color[u] = 2
        return False

    for s in proper_states:
        if s not in color and dfs(s):
            res["C3"] = False
            break
    return res


def ef(sysm, ample, target):
    """States satisfying EF target (least fixed point) on the (reduced) graph."""
    states = sysm.reachable(sysm.init, ample)
    sat = {s for s in states if target(s)}
    changed = True
    while changed:
        changed = False
        for s in states:
            if s not in sat and any(t in sat for _, t in sysm.successors(s, ample)):
                sat.add(s)
                changed = True
    return sat


def case_ignoring():
    # P0 spins forever on an invisible local action; P1 can once make p true.
    P0 = {"x": [("spin", "x")]}
    P1 = {"u": [("set_p", "v")], "v": []}
    sysm = System([P0, P1], lambda s: frozenset({"p"}) if s[1] == "v" else frozenset())
    sysm.init = ("x", "u")
    ample = {("x", "u"): {"spin"}}  # same proper ample set every time we revisit the state
    cond = check_conditions(sysm, ample)
    full_p = any("p" in sysm.props(s) for s in sysm.reachable(sysm.init))
    red_p = any("p" in sysm.props(s) for s in sysm.reachable(sysm.init, ample))
    print("Case 1 (ignoring problem):", cond)
    print("  G !p holds in full graph:   ", not full_p)
    print("  G !p holds in reduced graph:", not red_p, " <- wrong verdict when C3 is violated")


def case_next():
    # P0 has an invisible step; P1 makes p true.  Property:  !X p  (p is false at position 1)
    P0 = {"a0": [("tau", "a1")], "a1": []}
    P1 = {"b0": [("set_p", "b1")], "b1": []}
    sysm = System([P0, P1], lambda s: frozenset({"p"}) if s[1] == "b1" else frozenset())
    sysm.init = ("a0", "b0")
    ample = {("a0", "b0"): {"tau"}}
    cond = check_conditions(sysm, ample)
    # A run violates !X p iff some successor of the initial state satisfies p.
    full_viol = any("p" in sysm.props(t) for _, t in sysm.successors(sysm.init))
    red_viol = any("p" in sysm.props(t) for _, t in sysm.successors(sysm.init, ample))
    print("Case 2 (next-time operator):", cond)
    print("  A(!X p) holds in full graph:   ", not full_viol)
    print("  A(!X p) holds in reduced graph:", not red_viol, " <- C0-C3 hold, but !X p is not stutter-invariant")


def case_branching():
    # P0 chooses invisibly between two branches that later become visibly different (r1 / r2).
    # P1 independently makes p true.  Property (CTL without next): EF(p & EF r1 & EF r2)
    P0 = {"s": [("a1", "t1"), ("a2", "t2")], "t1": [("c1", "d1")], "t2": [("c2", "d2")], "d1": [], "d2": []}
    P1 = {"u": [("set_p", "v")], "v": []}

    def props(s):
        out = set()
        if s[1] == "v":
            out.add("p")
        if s[0] == "d1":
            out.add("r1")
        if s[0] == "d2":
            out.add("r2")
        return frozenset(out)

    sysm = System([P0, P1], props)
    sysm.init = ("s", "u")
    ample = {("s", "u"): {"a1", "a2"}}
    cond = check_conditions(sysm, ample)
    print("Case 3 (branching time):", cond, " <- C0-C3 hold; C4 (singleton) fails")
    for label, amp in (("full", None), ("reduced", ample)):
        r1 = ef(sysm, amp, lambda s: "r1" in sysm.props(s))
        r2 = ef(sysm, amp, lambda s: "r2" in sysm.props(s))
        goal = ef(sysm, amp, lambda s: "p" in sysm.props(s) and s in r1 and s in r2)
        print(f"  EF(p & EF r1 & EF r2) at initial state, {label:7s} graph:", sysm.init in goal)
    # LTL-X view: compare the sets of stutter-free visible traces
    def traces(amp):
        out = set()

        def walk(s, tr):
            succ = sysm.successors(s, amp)
            if not succ:
                out.add(tuple(tr))
                return
            for _, t in succ:
                walk(t, tr if sysm.props(t) == tr[-1] else tr + [sysm.props(t)])

        walk(sysm.init, [sysm.props(sysm.init)])
        return {tuple(tuple(sorted(x)) for x in t) for t in out}

    print("  stutter-free visible traces equal (LTL-X view):", traces(None) == traces(ample))


if __name__ == "__main__":
    case_ignoring()
    case_next()
    case_branching()
