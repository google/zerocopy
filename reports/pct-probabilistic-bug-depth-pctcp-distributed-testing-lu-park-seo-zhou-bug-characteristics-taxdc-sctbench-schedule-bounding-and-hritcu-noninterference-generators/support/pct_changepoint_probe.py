#!/usr/bin/env python3
"""Exact-enumeration probe of the change-point selection used by two PCT implementations.

Part A transliterates the `Shuffle` loop of Coyote's interleaving PrioritizationStrategy
(microsoft/coyote @ 0c51dc58cc34cdefa24dcfabf3439e5e0ec77309,
Source/Core/Testing/Interleaving/PrioritizationStrategy.cs lines 192-204):

    var result = new List<int>(range);
    for (int idx = result.Count - 1; idx >= 1; idx--)
    {
        int point = this.RandomValueGenerator.Next(result.Count);
        (swap result[idx] and result[point])
    }

and the caller (lines 70-75) which keeps the first `priorityChanges` elements, where
priorityChanges = Next(MaxPriorityChangesPerIteration) + 1.  RandomValueGenerator.Next(n)
is System.Random.Next(n), i.e. uniform on [0, n) (Source/Core/Random/RandomValueGenerator.cs
line 55).  Every one of the L^(L-1) equally likely sequences of Next() results is enumerated,
so the reported probabilities are exact for this transliteration (not sampled).  The textbook
Fisher-Yates loop draws `point` from [0, idx] instead; it is enumerated for comparison.

Part B transliterates the new-task priority insertion of Shuttle's PctScheduler
(awslabs/shuttle @ 72bdbdb612c2311905c84bbc73d59f12a5b17e43, shuttle-schedulers/src/pct.rs
lines 116-132): target = gen_range(0..len) + 1; if target == new id the new task gets the
lowest priority, otherwise it takes target's priority and target gets the lowest.  Starting
from every permutation of N existing tasks (uniform), it computes exactly the probability that
the new task ranks above task 0, and compares with uniform insertion (1/2).

Usage: python3 pct_changepoint_probe.py <Lmax>
"""
import itertools, sys
from fractions import Fraction
from collections import Counter

def coyote_shuffle(L, draws):
    """The swap loop shared by both variants; only the range of each draw differs."""
    r = list(range(L))
    for j, idx in enumerate(range(L - 1, 0, -1)):
        p = draws[j]
        r[idx], r[p] = r[p], r[idx]
    return r

def part_a(L, c):
    """Distribution of the set of the first c elements after shuffling range(L)."""
    out = {}
    for name, ranges in (('coyote', [range(L)] * (L - 1)),
                         ('fisher_yates', [range(idx + 1) for idx in range(L - 1, 0, -1)])):
        cnt = Counter()
        total = 0
        for draws in itertools.product(*ranges):
            r = coyote_shuffle(L, draws)
            cnt[frozenset(r[:c])] += 1
            total += 1
        probs = {s: Fraction(v, total) for s, v in cnt.items()}
        nsets = len(list(itertools.combinations(range(L), c)))
        uniform = Fraction(1, nsets)
        pmin = min(probs.get(frozenset(s), Fraction(0)) for s in itertools.combinations(range(L), c))
        pmax = max(probs.values())
        argmin = min(itertools.combinations(range(L), c), key=lambda s: probs.get(frozenset(s), Fraction(0)))
        argmax = max(probs, key=lambda s: probs[s])
        out[name] = (total, uniform, pmin, pmax, sorted(argmin), sorted(argmax))
    return out

def part_b(N):
    """Exact P(new task ranks above task 0) for Shuttle's swap insertion vs uniform insertion."""
    above = Fraction(0)
    perms = list(itertools.permutations(range(N)))  # perm[t] = priority value (lower runs first)
    for perm in perms:
        pri = {t: perm[t] for t in range(N)}
        nxt = N
        for target in range(1, N + 1):  # gen_range(0..N) + 1, each w.p. 1/N
            p = dict(pri)
            if target == N:
                p[N] = nxt
            else:
                p[N] = p[target]; p[target] = nxt
            if p[N] < p[0]:
                above += Fraction(1, N * len(perms))
    return above

def main():
    Lmax = int(sys.argv[1])
    print('# Part A: change-point set selection, exact over all RNG draw sequences')
    print('L\tc\tvariant\tsequences\tuniform_p\tmin_p\tmax_p\tmin/uniform\tmax/uniform\targmin_set\targmax_set')
    for L in range(3, Lmax + 1):
        for c in (1, 2):
            res = part_a(L, c)
            for name, (total, u, pmin, pmax, amin, amax) in res.items():
                print(f'{L}\t{c}\t{name}\t{total}\t{float(u):.6f}\t{float(pmin):.6f}\t{float(pmax):.6f}\t'
                      f'{float(pmin/u):.4f}\t{float(pmax/u):.4f}\t{amin}\t{amax}')
    print('# Part B: Shuttle new-task insertion, exact P(new task above task 0); uniform insertion gives 0.5')
    for N in range(2, 7):
        p = part_b(N)
        print(f'N={N}\tP={p}\t={float(p):.4f}\tclosed_form_(N-1)/(2N)={float(Fraction(N-1, 2*N)):.4f}')

if __name__ == '__main__':
    main()
