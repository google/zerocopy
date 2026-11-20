#!/usr/bin/env python3
"""Toy model (not any real compiler): static slot assignment for runtime handles.

Model. A thread is a straight-line list of atomic steps 0..n-1. A handle h of a thread is
allocated by step d_h and released by step l_h (d_h < l_h). After a thread has executed s
steps (a quiescent point), h is live iff d_h <= s-1 < l_h. Two threads A and B run in
parallel; an execution is an interleaving of their steps. Two handles conflict if some
interleaving reaches a quiescent point where both are live. A slot assignment is valid iff
conflicting handles receive different slots.

The script enumerates every interleaving exhaustively, derives the may-conflict relation,
computes the minimum number of slots by brute-force colouring, and compares it with:
  * no barrier:  maxlive(A) + maxlive(B)
  * one barrier that both threads reach before either continues, with every handle confined
    to one phase:  max over phases p of maxlive(A_p) + maxlive(B_p)
It also counts programs for which the slot assignment that is optimal for ONE schedule
(A runs to completion, then B) is invalid for some other interleaving.
"""
import itertools, random, sys

def interleavings(n, m):
    for pos in itertools.combinations(range(n + m), n):
        s = [1] * (n + m)
        for p in pos:
            s[p] = 0
        yield s

def live_at(handles, s):
    return {h for h, (d, l) in handles.items() if d <= s - 1 < l}

def respects_barrier(sched, bA, bB):
    ia = ib = 0
    for t in sched:
        if t == 0:
            if ia >= bA and ib < bB:
                return False
            ia += 1
        else:
            if ib >= bB and ia < bA:
                return False
            ib += 1
    return True

def conflicts(A, B, sched):
    ia = ib = 0
    conf = set()
    for t in sched:
        if t == 0: ia += 1
        else: ib += 1
        cur = sorted(live_at(A, ia) | live_at(B, ib))
        conf.update(itertools.combinations(cur, 2))
    return conf

def min_colors(nodes, edges):
    nodes = sorted(nodes)
    adj = {v: set() for v in nodes}
    for x, y in edges:
        adj[x].add(y); adj[y].add(x)
    for k in range(1, len(nodes) + 1):
        col = {}
        def bt(i):
            if i == len(nodes): return True
            v = nodes[i]
            for c in range(k):
                if all(col.get(u) != c for u in adj[v]):
                    col[v] = c
                    if bt(i + 1): return True
                    del col[v]
            return False
        if bt(0):
            return k, dict(col)
    return 0, {}

def maxlive(handles, s_lo, s_hi):
    return max([len(live_at(handles, s)) for s in range(s_lo, s_hi + 1)] + [0])

def rand_handles(prefix, k, lo, hi, rng):
    # steps lo..hi-1 are available; need d < l, both in that range
    hs = {}
    for j in range(k):
        d = rng.randrange(lo, hi - 1)
        l = rng.randrange(d + 1, hi)
        hs[f"{prefix}{j}"] = (d, l)
    return hs

def main(seed=1, trials=300):
    rng = random.Random(seed)
    ok_nobar = ok_bar = unsound_single = 0
    for _ in range(trials):
        nA, nB = rng.randint(2, 6), rng.randint(2, 6)
        A = rand_handles("a", rng.randint(1, 3), 0, nA, rng)
        B = rand_handles("b", rng.randint(1, 3), 0, nB, rng)
        allconf = set()
        for s in interleavings(nA, nB):
            allconf |= conflicts(A, B, s)
        k, _ = min_colors(set(A) | set(B), allconf)
        ok_nobar += k == maxlive(A, 0, nA) + maxlive(B, 0, nB)
        seq = [0] * nA + [1] * nB
        _, colseq = min_colors(set(A) | set(B), conflicts(A, B, seq))
        unsound_single += any(colseq[x] == colseq[y] for x, y in allconf)

        nA2, nB2 = rng.randint(4, 6), rng.randint(4, 6)
        bA, bB = rng.randint(2, nA2 - 2), rng.randint(2, nB2 - 2)
        A2 = {**rand_handles("a", 2, 0, bA, rng), **rand_handles("ax", 2, bA, nA2, rng)}
        B2 = {**rand_handles("b", 2, 0, bB, rng), **rand_handles("bx", 2, bB, nB2, rng)}
        allconf2 = set()
        for s in interleavings(nA2, nB2):
            if respects_barrier(s, bA, bB):
                allconf2 |= conflicts(A2, B2, s)
        k2, _ = min_colors(set(A2) | set(B2), allconf2)
        pred = max(maxlive(A2, 0, bA) + maxlive(B2, 0, bB), maxlive(A2, bA, nA2) + maxlive(B2, bB, nB2))
        ok_bar += k2 == pred
    print(f"seed={seed} trials={trials}")
    print(f"no barrier: min slots == maxlive(A)+maxlive(B) in {ok_nobar}/{trials}")
    print(f"one barrier, handles confined to a phase: min slots == max_p(maxlive(A_p)+maxlive(B_p)) in {ok_bar}/{trials}")
    print(f"slot assignment optimal for the single schedule 'A then B' is invalid under some interleaving in {unsound_single}/{trials}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1, int(sys.argv[2]) if len(sys.argv) > 2 else 300)
