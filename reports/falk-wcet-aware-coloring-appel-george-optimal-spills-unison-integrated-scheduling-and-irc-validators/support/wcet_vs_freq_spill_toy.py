#!/usr/bin/env python3
"""wcet_vs_freq_spill_toy.py -- TOY MODEL (not any real allocator or target).

Question probed: when a spill decision is driven by a frequency-weighted
(average-case) cost, how far can the resulting worst-case path bound be from
the best achievable bound, and how often do the two criteria disagree?

Model (deliberately minimal):
  * One loop with a fixed bound N. Each iteration takes exactly one of two
    paths, A or B (an if/else), with estimated probabilities pA and 1 - pA.
  * n virtual registers are live across the whole loop; only k physical
    registers are available, so exactly n - k of them must be spilled.
  * Virtual register v is used useA[v] times on path A and useB[v] times on
    path B. If v is spilled, every use costs an extra L cycles (one reload);
    spill stores are hoisted out of the loop and ignored.
  * Path base costs are cA and cB cycles.

Two criteria:
  freq : minimise  N * sum_v spilled(v) * L * (pA*useA[v] + (1-pA)*useB[v])
         (the shape of a block-frequency-weighted spill weight; ties broken by
         register index). This is the expected (average-case) spill overhead.
  wcet : minimise  N * max(cA + L*sum_spilled useA, cB + L*sum_spilled useB)
         (the loop's longest-path bound, i.e. an IPET bound for this CFG).
Both are solved exactly by enumerating all C(n, n-k) spill sets.

Usage: python3 wcet_vs_freq_spill_toy.py [instances] [seed]
"""
import itertools
import random
import statistics
import sys


def evaluate(spill, useA, useB, cA, cB, L, N, pA):
    sa = sum(useA[v] for v in spill)
    sb = sum(useB[v] for v in spill)
    wcet = N * max(cA + L * sa, cB + L * sb)
    acet = N * (pA * (cA + L * sa) + (1 - pA) * (cB + L * sb))
    wcep = "A" if cA + L * sa >= cB + L * sb else "B"
    return wcet, acet, wcep


def solve(useA, useB, cA, cB, L, N, pA, n, k):
    sets = list(itertools.combinations(range(n), n - k))
    by_freq = min(sets, key=lambda s: (sum(pA * useA[v] + (1 - pA) * useB[v] for v in s), s))
    by_wcet = min(sets, key=lambda s: (evaluate(s, useA, useB, cA, cB, L, N, pA)[0], s))
    return by_freq, by_wcet


def worked_example():
    # Path A is hot (pA = 0.9) and short; path B is cold and long.
    n, k, L, N, pA = 2, 1, 4, 100, 0.9
    cA, cB = 20, 30
    useA = [1, 6]   # v0 rarely used on A, v1 heavily used on A
    useB = [5, 0]   # v0 heavily used on B (the long path), v1 unused on B
    f, w = solve(useA, useB, cA, cB, L, N, pA, n, k)
    print("worked example: n=2 k=1 L=4 N=100 pA=0.9 cA=20 cB=30 useA=[1,6] useB=[5,0]")
    for name, s in (("freq", f), ("wcet", w)):
        wc, ac, ep = evaluate(s, useA, useB, cA, cB, L, N, pA)
        print(f"  {name}: spill v{list(s)}  WCET bound={wc:.0f}  expected time={ac:.1f}  worst path={ep}")
    base = evaluate((), useA, useB, cA, cB, L, N, pA)
    print(f"  (no spill, infeasible with k=1): WCET={base[0]:.0f} worst path={base[2]}")


def campaign(instances, seed):
    rng = random.Random(seed)
    disagree = 0
    penalties = []
    acet_gain = []
    for _ in range(instances):
        n = rng.randint(3, 6)
        k = rng.randint(1, n - 1)
        L = rng.choice([2, 3, 4, 5, 8])
        N = 100
        pA = rng.choice([0.5, 0.7, 0.9, 0.95, 0.99])
        cA = rng.randint(5, 40)
        cB = rng.randint(5, 40)
        useA = [rng.randint(0, 6) for _ in range(n)]
        useB = [rng.randint(0, 6) for _ in range(n)]
        f, w = solve(useA, useB, cA, cB, L, N, pA, n, k)
        wf, af, _ = evaluate(f, useA, useB, cA, cB, L, N, pA)
        ww, aw, _ = evaluate(w, useA, useB, cA, cB, L, N, pA)
        if wf > ww:
            disagree += 1
            penalties.append(wf / ww - 1.0)
            acet_gain.append(1.0 - af / aw if aw else 0.0)
    print(f"campaign: instances={instances} seed={seed}")
    print(f"  freq-optimal spill set has a strictly larger WCET bound than the wcet-optimal set in "
          f"{disagree}/{instances} instances ({100.0 * disagree / instances:.1f}%)")
    if penalties:
        q = statistics.quantiles(penalties, n=10)
        print(f"  WCET-bound increase in those instances: median {100 * statistics.median(penalties):.1f}%  "
              f"p90 {100 * q[8]:.1f}%  max {100 * max(penalties):.1f}%")
        print(f"  expected-time advantage of the freq choice in those instances: median "
              f"{100 * statistics.median(acet_gain):.1f}%  max {100 * max(acet_gain):.1f}%")


if __name__ == "__main__":
    instances = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    worked_example()
    campaign(instances, seed)
