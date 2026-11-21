#!/usr/bin/env python3
"""Toy-model probe: planted ordering chains of increasing depth vs. four schedule-search strategies.

This is a TOY MODEL written for this report. It is not Shuttle, Coyote, or any
other upstream tool. Program model: n threads, each executing m unit steps, all
steps always enabled (no locks, no blocking). A schedule is an interleaving of
the k = n*m steps. A planted behaviour of depth d is a chain of d+1 events
(thread, step) that must occur in the given temporal order; consecutive chain
events alternate between thread 0 and thread 1, so every constraint forces a
context switch. Threads 2..n-1 are bystanders that only add steps and choices.
By construction each chain is guaranteed by a PCT directive with d ordering
constraints, so its PCT depth is <= d (minimality is not proved here).

Strategies:
  dfs     - lexicographic depth-first enumeration (lowest thread id first), budget-limited
  rw      - uniform random walk: at each step pick an enabled thread uniformly
  uni     - uniform sampling over interleavings (random permutation of the step multiset)
  pct(D)  - Burckhardt et al. 2010 RandS(n, k, D): random initial priorities
            D..D+n-1, D-1 change points drawn i.i.d. uniform from {1..k}; after the
            schedule length equals k_i the running thread's priority becomes D-i.

Usage: python3 pct_depth_probe.py <n> <m> <samples> <dfs_budget> <seed>
"""
import itertools, math, random, sys, time

def gen_chain(rng, m, d, tight):
    """Alternating chain over threads 0/1 with d constraints (d+1 events)."""
    while True:
        first = rng.randrange(2)
        last_step = {0: 0, 1: 0}  # last used step per thread (1-based), 0 = none
        chain = []
        ok = True
        for i in range(d + 1):
            t = first if i % 2 == 0 else 1 - first
            lo = last_step[t] + 1
            if lo > m:
                ok = False; break
            if tight and last_step[t] > 0:
                s = lo  # precisely timed: the very next step of this thread
            else:
                # leave room for the remaining events of this thread
                remaining_same = len([j for j in range(i + 2, d + 1, 2)])
                hi = m - remaining_same
                if hi < lo:
                    ok = False; break
                s = rng.randint(lo, hi)
            last_step[t] = s
            chain.append((t, s))
        if ok:
            return chain

def r2c_chain(m):
    """Run-to-completion behaviour: thread 1 finishes all m steps before thread 0 takes its first."""
    return [(1, m), (0, 1)]

def satisfied(pos, chain):
    prev = -1
    for (t, s) in chain:
        p = pos[t][s]
        if p <= prev:
            return False
        prev = p
    return True

def positions(sched, n, m):
    pos = [[0] * (m + 1) for _ in range(n)]
    cnt = [0] * n
    for i, t in enumerate(sched):
        cnt[t] += 1
        pos[t][cnt[t]] = i
    return pos

def dfs_schedules(n, m, budget):
    """Lexicographic enumeration of interleavings (lowest thread first)."""
    out = []
    rem = [m] * n
    sched = []
    def rec():
        if len(out) >= budget:
            return
        if len(sched) == n * m:
            out.append(tuple(sched)); return
        for t in range(n):
            if rem[t]:
                rem[t] -= 1; sched.append(t)
                rec()
                sched.pop(); rem[t] += 1
                if len(out) >= budget:
                    return
    rec()
    return out

def sample_rw(rng, n, m):
    rem = [m] * n
    s = []
    for _ in range(n * m):
        en = [t for t in range(n) if rem[t]]
        t = en[rng.randrange(len(en))]
        rem[t] -= 1; s.append(t)
    return s

def sample_uni(rng, n, m):
    s = [t for t in range(n) for _ in range(m)]
    rng.shuffle(s)
    return s

def sample_pct(rng, n, m, D):
    k = n * m
    perm = list(range(n)); rng.shuffle(perm)
    p = [D + perm[t] for t in range(n)]          # D .. D+n-1
    cps = [rng.randint(1, k) for _ in range(D - 1)]  # i.i.d. uniform in {1..k}
    rem = [m] * n
    s = []
    while len(s) < k:
        t = max((u for u in range(n) if rem[u]), key=lambda u: p[u])
        rem[t] -= 1; s.append(t)
        L = len(s)
        for i, ki in enumerate(cps, start=1):
            if L == ki:
                p[t] = D - i
    return s

def main():
    n, m, N, budget, seed = map(int, sys.argv[1:6])
    rng = random.Random(seed)
    k = n * m
    t0 = time.time()
    chains = []  # (label, depth, chain)
    for d in range(1, 6):
        for tight in (False, True):
            for _ in range(8):
                chains.append((('tight' if tight else 'loose'), d, gen_chain(rng, m, d, tight)))
    chains.append(('r2c', 1, r2c_chain(m)))
    total_interleavings = math.factorial(k) // (math.factorial(m) ** n)
    print(f'# config n={n} m={m} k={k} samples={N} dfs_budget={budget} seed={seed} interleavings={total_interleavings}')
    # DFS: first-hit index per chain
    dfs = dfs_schedules(n, m, budget)
    first_hit = [None] * len(chains)
    hits_dfs = [0] * len(chains)
    for idx, s in enumerate(dfs):
        pos = positions(s, n, m)
        for ci, (_, _, ch) in enumerate(chains):
            if satisfied(pos, ch):
                hits_dfs[ci] += 1
                if first_hit[ci] is None:
                    first_hit[ci] = idx + 1
    exhaustive = len(dfs) == total_interleavings
    # Monte Carlo strategies
    strategies = [('rw', lambda: sample_rw(rng, n, m)), ('uni', lambda: sample_uni(rng, n, m))]
    for D in range(1, 6):
        strategies.append((f'pct{D}', (lambda D=D: sample_pct(rng, n, m, D))))
    hits = {name: [0] * len(chains) for name, _ in strategies}
    for name, f in strategies:
        for _ in range(N):
            pos = positions(f(), n, m)
            for ci, (_, _, ch) in enumerate(chains):
                if satisfied(pos, ch):
                    hits[name][ci] += 1
    # Report per chain
    print('# per-chain: label depth chain | dfs_first_hit exact_uniform_p(if exhaustive) | p_hat per strategy')
    names = [nm for nm, _ in strategies]
    print('label\td\tchain\tdfs_first\tuni_exact\t' + '\t'.join(names))
    for ci, (lab, d, ch) in enumerate(chains):
        ue = f'{hits_dfs[ci]/total_interleavings:.3e}' if exhaustive else 'n/a'
        row = [lab, str(d), ' '.join(f'T{t}.{s}' for t, s in ch), str(first_hit[ci]), ue]
        row += [f'{hits[nm][ci]/N:.4f}' for nm in names]
        print('\t'.join(row))
    # Aggregates per (label, depth)
    print('# aggregate: group | min p_hat per strategy (0 => < 1/N) | fraction of chains with dfs hit within budgets 10/100/1000 | PCT bound 1/(n k^(d-1))')
    for lab in ('loose', 'tight', 'r2c'):
        for d in range(1, 6):
            idxs = [ci for ci, (l, dd, _) in enumerate(chains) if l == lab and dd == d]
            if not idxs:
                continue
            mins = {nm: min(hits[nm][ci] for ci in idxs) / N for nm in names}
            means = {nm: sum(hits[nm][ci] for ci in idxs) / N / len(idxs) for nm in names}
            fr = []
            for B in (10, 100, 1000):
                fr.append(sum(1 for ci in idxs if first_hit[ci] is not None and first_hit[ci] <= B) / len(idxs))
            bound = 1.0 / (n * k ** (d - 1))
            pctd = f'pct{d}'
            # Bound check: a chain is flagged only if its estimate is significantly below the
            # bound (one-sided z > 3.29, i.e. p < 0.0005 under a binomial normal approximation).
            # If N*bound < 5 the sample cannot resolve the bound and the check is 'unresolved'.
            if N * bound < 5:
                verdict = 'unresolved(N*bound<5)'
            else:
                se = math.sqrt(bound * (1 - bound) / N)
                below = [ci for ci in idxs if hits[pctd][ci] / N + 3.29 * se < bound]
                verdict = 'consistent' if not below else f'significantly_below_in_{len(below)}'
            print(f'{lab}\td={d}\tchains={len(idxs)}\t' +
                  ' '.join(f'{nm}:min={mins[nm]:.4f},mean={means[nm]:.4f}' for nm in names) +
                  f'\tdfs_within_10/100/1000={fr[0]:.2f}/{fr[1]:.2f}/{fr[2]:.2f}' +
                  f'\tbound={bound:.3e}\tpct{d}_vs_bound:{verdict}')
    print(f'# exhaustive_dfs={exhaustive} dfs_enumerated={len(dfs)} elapsed_s={time.time()-t0:.1f}')

if __name__ == '__main__':
    main()
