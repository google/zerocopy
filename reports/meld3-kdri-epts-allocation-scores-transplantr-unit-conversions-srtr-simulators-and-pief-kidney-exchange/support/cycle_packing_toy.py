#!/usr/bin/env python3
"""Exact max-weight cycle packing on small kidney-exchange instances, by memoised search.

This is an independent toy re-implementation of the *cycle formulation* objective
(maximise total edge score of vertex-disjoint cycles of length <= K; no chains). It is not
kidney_solver and uses no IP solver. It reads kidney_solver's `.input` format
(first line "<n_vertices> <n_edges>", then "src tgt score" lines, terminated by "-1 -1 -1").

It reports: the optimum, the number of distinct optimal cycle sets (ties), and how many
vertices are matched in some but not all optimal solutions. A tie means two equally optimal
answers exist and a solver's internal path, not the stated objective, decides between them.
"""
import sys
from functools import lru_cache

def read_input(path):
    with open(path) as f:
        rows = [l.split() for l in f if l.strip()]
    n, m = int(rows[0][0]), int(rows[0][1])
    edges = {}
    for r in rows[1:]:
        s, t, w = int(r[0]), int(r[1]), float(r[2])
        if s == -1:
            break
        edges[(s, t)] = w
    assert len(edges) == m, (len(edges), m)
    return n, edges

def cycles_upto(n, edges, K):
    out = {v: [] for v in range(n)}
    succ = {v: [] for v in range(n)}
    for (s, t) in edges:
        succ[s].append(t)
    found = []
    def dfs(start, path):
        last = path[-1]
        for t in succ[last]:
            if t == start and len(path) >= 2:
                found.append(tuple(path))
            elif t > start and t not in path and len(path) < K:
                dfs(start, path + [t])
    for v in range(n):
        dfs(v, [v])        # each cycle is found once, rooted at its smallest vertex
    cyc = []
    for c in found:
        w = sum(edges[(c[i], c[(i + 1) % len(c)])] for i in range(len(c)))
        mask = 0
        for v in c:
            mask |= 1 << v
        cyc.append((c, w, mask))
    for i, (c, w, mask) in enumerate(cyc):
        out[min(c)].append(i)
    return cyc, out

def solve(n, cyc, by_min):
    sys.setrecursionlimit(10000)
    def best(v, used):
        # Only vertices >= v can still matter, so memoise on the shifted mask.
        return _best(v, used >> v)

    @lru_cache(maxsize=None)
    def _best(v, rel):
        used = rel << v
        # optimum over cycles whose smallest vertex is >= v, avoiding `used`
        if v >= n:
            return (0.0, 1)                     # (value, number of optimal completions)
        val, cnt = best(v + 1, used)            # vertex v is not the root of a chosen cycle
        for i in by_min[v]:
            c, w, mask = cyc[i]
            if mask & used:
                continue
            sub, subcnt = best(v + 1, used | mask)
            cand = sub + w
            if cand > val + 1e-9:
                val, cnt = cand, subcnt
            elif abs(cand - val) <= 1e-9:
                cnt += subcnt
        return (val, cnt)
    opt, count = best(0, 0)
    # recover per-vertex coverage across all optimal solutions
    always, sometimes = None, 0
    def enum(v, used, acc, chosen, out, limit=2000):
        if len(out) >= limit:
            return
        if v >= n:
            out.append(chosen)
            return
        target = best(v, used)[0]
        if abs(best(v + 1, used)[0] - target) <= 1e-9:
            enum(v + 1, used, acc, chosen, out, limit)
        for i in by_min[v]:
            c, w, mask = cyc[i]
            if mask & used:
                continue
            if abs(best(v + 1, used | mask)[0] + w - target) <= 1e-9:
                enum(v + 1, used | mask, acc + w, chosen + [c], out, limit)
    sols = []
    enum(0, 0, 0.0, [], sols)
    return opt, count, sols

def main():
    path, K = sys.argv[1], int(sys.argv[2])
    n, edges = read_input(path)
    if len(sys.argv) > 3:                     # optional: induced subgraph on vertices 0..N-1
        n = int(sys.argv[3])
        edges = {(s, t): w for (s, t), w in edges.items() if s < n and t < n}
    cyc, by_min = cycles_upto(n, edges, K)
    opt, count, sols = solve(n, cyc, by_min)
    cover = [set(v for c in s for v in c) for s in sols]
    in_all = set.intersection(*cover) if cover else set()
    in_any = set.union(*cover) if cover else set()
    print(f"instance={path.split('/')[-1]}{' (induced on first %d vertices)' % n if len(sys.argv) > 3 else ''} vertices={n} edges={len(edges)} cycle_cap={K} cycles={len(cyc)}")
    print(f"optimum={opt:g} distinct_optimal_cycle_sets={count} enumerated={len(sols)}")
    print(f"vertices matched in every enumerated optimum={len(in_all)}; in at least one={len(in_any)}; "
          f"tie-dependent={len(in_any - in_all)}")

if __name__ == "__main__":
    main()
