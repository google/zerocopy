#!/usr/bin/env python3
"""Toy models of space accounting under sharing (standard library only).

These are TOY MODELS written to illustrate published typing rules; they are
not the published systems and not their implementations.

Part A  In-place heap model of an LFPL-like first-order language (cell
        identity semantics: matching a cons cell yields its location as the
        "diamond"; cons(d,h,t) overwrites location d).  Shows (1) zero fresh
        allocation for in-place reverse/append, (2) the circular list produced
        by a program that uses one diamond twice, (3) a usage-aspect style let
        check that accepts cons(d,sumlist(l),reverse(l)) and rejects
        cons(d,nth_tail(2,l),cons(d',reverse(l),nil)), and the divergence of
        the in-place result from the functional result for the rejected term.
Part B  Reference-counted heap (frees a cell as soon as it is unreachable;
        for acyclic data this coincides with an ideal collector) running
        appTwice l = (append(l,[]), append(l,[])) to compare total allocation
        with peak live heap above the input, and the minimal per-element
        potential obtained from two sharing disciplines.
"""
import itertools, sys

# ---------------------------------------------------------------- Part A
class InPlaceHeap:
    def __init__(self):
        self.cells, self.next = {}, 0
    def build(self, xs):                      # input list, allocated up front
        l = None
        for x in reversed(xs):
            loc = self.next; self.next += 1
            self.cells[loc] = (x, l); l = loc
        return l
    def match(self, l):                       # cons(d,h,t) pattern: d = l
        h, t = self.cells[l]
        return l, h, t
    def cons(self, d, h, t):                  # overwrite the cell at d
        self.cells[d] = (h, t)
        return d
    def read(self, l, limit=12):
        out, seen = [], set()
        while l is not None and len(out) < limit:
            if l in seen:                     # revisiting a cell => cycle
                return out, True
            seen.add(l)
            h, l = self.cells[l]
            out.append(h)
        return out, False                     # (elements, cyclic?)

def reverse(H, l):
    acc = None
    while l is not None:
        d, h, t = H.match(l)
        acc = H.cons(d, h, acc); l = t
    return acc

def sumlist(H, l):
    s = 0
    while l is not None:
        _, h, l = H.match(l)
        s += h
    return s

def nth_tail(H, n, l):
    while n > 0 and l is not None:
        _, _, l = H.match(l); n -= 1
    return l

def twice(H, l):                              # uses diamond d twice
    if l is None:
        return None
    d, h, t = H.match(l)
    r = twice(H, t)
    return H.cons(d, 0, H.cons(d, 0, r))

def part_a():
    print("== Part A: in-place (diamond = cell location) toy model ==")
    H = InPlaceHeap(); l = H.build([1, 2, 3, 4, 5]); n0 = len(H.cells)
    r = reverse(H, l)
    print("reverse [1..5] ->", H.read(r)[0], "| cells before/after:", n0, len(H.cells))

    H = InPlaceHeap(); l = H.build([1, 2])
    r = twice(H, l)
    pre, cyc = H.read(r, limit=8)
    print("twice [1,2]: functional [0,0,0,0]; in-place reads", pre,
          "then revisits a cell (cyclic)" if cyc else "(acyclic)")

    # cons(d, sumlist(l), reverse(l)) with left-to-right evaluation
    H = InPlaceHeap(); l = H.build([1, 2, 3]); d = H.build([-1])
    s = sumlist(H, l); rv = reverse(H, l)
    print("cons(d,sumlist(l),reverse(l)): functional (6,[3,2,1]); in-place",
          (s, H.read(rv)[0]))

    # cons(d, nth_tail(2,l), cons(d', reverse(l), nil))
    H = InPlaceHeap(); l = H.build([1, 2, 3])
    nt = nth_tail(H, 2, l); rv = reverse(H, l)
    print("cons(d,nth_tail(2,l),cons(d',reverse(l),nil)): functional [[3],[3,2,1]]; "
          "in-place", [H.read(nt)[0], H.read(rv)[0]])

    # Usage-aspect let check (prose form of the let side condition):
    #   for a variable z common to e1 and e2 in  let x = e1 in e2 :
    #   aspect1(z)=1 rejected; =3 accepted; =2 accepted iff i!=1 and aspect2(z)!=1
    #   where i is the aspect of x in e2.
    SIG = {"reverse": [1], "sumlist": [3], "nth_tail": [3, 2], "cons": [1, 2, 2]}
    def ok_let(asp1, asp2, i):
        if asp1 == 1: return False
        if asp1 == 3: return True
        return i != 1 and asp2 != 1
    # e = let s = sumlist(l) in (... reverse(l) ...): l common, aspect1 = 3
    acc1 = ok_let(SIG["sumlist"][0], SIG["reverse"][0], i=SIG["cons"][1])
    # e = let n = nth_tail(2,l) in (... reverse(l) ...): l common, aspect1 = 2
    acc2 = ok_let(SIG["nth_tail"][1], SIG["reverse"][0], i=SIG["cons"][1])
    print("aspect check: sumlist-then-reverse accepted =", acc1,
          "| nth_tail-then-reverse accepted =", acc2)

# ---------------------------------------------------------------- Part B
class RCHeap:
    def __init__(self):
        self.cells, self.rc, self.next = {}, {}, 0
        self.live = self.peak = self.total = 0
    def cons(self, h, t):                     # takes ownership of t
        loc = self.next; self.next += 1
        self.cells[loc] = (h, t); self.rc[loc] = 1
        self.live += 1; self.total += 1; self.peak = max(self.peak, self.live)
        return loc
    def inc(self, l):
        if l is not None: self.rc[l] += 1
    def dec(self, l):
        while l is not None:
            self.rc[l] -= 1
            if self.rc[l] > 0: return
            _, t = self.cells.pop(l); del self.rc[l]; self.live -= 1
            l = t

def rc_append(H, l1, l2):                     # consumes references l1, l2
    if l1 is None: return l2
    h, t = H.cells[l1]; H.inc(t); H.dec(l1)  # match: keep tail, drop cell ref
    return H.cons(h, rc_append(H, t, l2))

def part_b(ms=(1, 10, 100, 500)):
    print("== Part B: refcount heap, appTwice l = (append(l,[]), append(l,[])) ==")
    print(" m  total_alloc  peak_live_minus_input")
    for m in ms:
        H = RCHeap(); l = None
        for x in range(m): l = H.cons(x, l)
        H.total = 0; base = H.live; H.peak = H.live
        H.inc(l)                              # share l as l1, l2
        a = rc_append(H, l, None); b = rc_append(H, l, None)
        print(f"{m:4d} {H.total:11d} {H.peak - base:22d}")
    # Minimal per-element potential under two sharing rules (output potential 0):
    #   heap metric:   share p = p1 + p2, each append needs p_i >= 1   (p >= 2)
    #   copy-on-share: additionally pay 1 per shared cell, but matched cells
    #                  return potential, so append needs p_i >= 0       (p >= 1)
    best = {}
    for name, need, extra in (("allocation metric", 1, 0), ("GC metric + copy-on-share", 0, 1)):
        sols = [p for p, p1, p2 in itertools.product(range(5), repeat=3)
                if p == p1 + p2 + extra and p1 >= need and p2 >= need]
        best[name] = min(sols)
    print("minimal per-element potential p:", best)

if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    part_a(); part_b()
