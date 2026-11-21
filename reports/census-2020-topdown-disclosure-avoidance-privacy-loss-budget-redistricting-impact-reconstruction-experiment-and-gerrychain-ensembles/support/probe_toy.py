#!/usr/bin/env python3
"""TOY MODELS (not the production DAS optimizer, not real census geography).

Part A - post-processing bias toy: true small-area counts under a parent with an
invariant total; add discrete Gaussian noise drawn by the DAS release's own
sampler (discrete_gaussian_utility.RationalSimpleDiscreteGaussian, seeded
stand-in RNG); then post-process three ways and measure signed error by
true-count class:
  raw    : noisy integers, no post-processing (unbiased by construction)
  clamp  : max(y, 0) per cell, total not enforced
  l2proj : Euclidean projection onto {x >= 0, sum x = T} followed by
           largest-remainder rounding to integers that sum to T (a one-level,
           one-query caricature of NNLS + controlled rounding)

Part B - ensemble toy: GerryChain ReCom (mggg/GerryChain, installed from the
pinned tree) on a 20x20 grid with heterogeneous node populations, run with
node populations taken from TRUE, RAW (noise only) and PP (noise + l2proj
post-processing, state-like total held invariant), and evaluate every sampled
plan against the TRUE populations.

Usage: python3 probe_toy.py <path-to-source/programs/engine> [steps]
"""
import math
import random
import statistics
import sys
import time
from fractions import Fraction as Fr
from functools import partial

ENGINE = sys.argv[1]
STEPS = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
sys.path.insert(0, ENGINE)
import discrete_gaussian_utility as dgu  # noqa: E402

SIGMA_SQ_BLOCK_DETAILED = 1 / (Fr(3945, 4097) * Fr(165, 4099) / Fr(339, 542) ** 2)  # ~10.0928, production value


class SeededIntegers:
    def __init__(self, seed):
        self._r = random.Random(seed)

    def integers(self, low=0, high=0):
        return self._r.randrange(low, high)


def project_simplex(y, total):
    """Euclidean projection of real vector y onto {x >= 0, sum(x) = total} (sort-based)."""
    u = sorted(y, reverse=True)
    css = 0.0
    theta = 0.0
    for j, uj in enumerate(u, start=1):
        css += uj
        t = (css - total) / j
        if uj - t > 0:
            theta = t
    return [max(v - theta, 0.0) for v in y]


def round_preserving_total(x, total):
    fl = [math.floor(v) for v in x]
    short = total - sum(fl)
    order = sorted(range(len(x)), key=lambda i: x[i] - fl[i], reverse=True)
    for i in order[:short]:
        fl[i] += 1
    return fl


def l2proj(y, total):
    return round_preserving_total(project_simplex([float(v) for v in y], total), total)


def part_a(sigma_sq, trials=4000, seed=7):
    r = random.Random(seed)
    true = [0] * 40 + [r.randint(1, 5) for _ in range(30)] + [r.randint(6, 30) for _ in range(20)] + [r.randint(100, 500) for _ in range(10)]
    T = sum(true)
    classes = {"0": [i for i, v in enumerate(true) if v == 0], "1-5": [i for i, v in enumerate(true) if 1 <= v <= 5],
               "6-30": [i for i, v in enumerate(true) if 6 <= v <= 30], "100-500": [i for i, v in enumerate(true) if v >= 100]}
    rng = SeededIntegers(seed + 1)
    acc = {m: {c: [] for c in classes} for m in ("raw", "clamp", "l2proj")}
    totals = {m: [] for m in acc}
    t0 = time.perf_counter()
    for _ in range(trials):
        noise = dgu.RationalSimpleDiscreteGaussian(sigma_sq=sigma_sq, size=len(true), rng=rng)
        y = [t + e for t, e in zip(true, noise)]
        outs = {"raw": y, "clamp": [max(v, 0) for v in y], "l2proj": l2proj(y, T)}
        for m, out in outs.items():
            totals[m].append(sum(out) - T)
            for c, idx in classes.items():
                acc[m][c].append(statistics.fmean(out[i] - true[i] for i in idx))
    secs = time.perf_counter() - t0
    print(f"PART A (toy): K={len(true)} cells, T={T}, sigma^2={float(sigma_sq):.4f}, trials={trials}, seed={seed}, wall={secs:.1f}s")
    for m in acc:
        cells = "; ".join(f"class {c} (n={len(classes[c])}): mean signed err/cell {statistics.fmean(v):+.3f} (+/-{1.96 * statistics.stdev(v) / math.sqrt(trials):.3f})" for c, v in acc[m].items())
        print(f"  {m:6s}: total err mean {statistics.fmean(totals[m]):+.2f}; {cells}")
    return true


def part_b(sigma_sq, steps, seeds=(11, 12)):
    import networkx as nx
    from gerrychain import Graph, MarkovChain, Partition
    from gerrychain.accept import always_accept
    from gerrychain.constraints import contiguous, within_percent_of_ideal_population
    from gerrychain.proposals import recom
    from gerrychain.updaters import Tally, cut_edges

    side, k, tol = 20, 4, 0.02
    r = random.Random(2026)
    nxg = nx.convert_node_labels_to_integers(nx.grid_graph(dim=[side, side]), label_attribute="xy")
    true = {}
    for n in nxg.nodes:
        true[n] = 0 if r.random() < 0.10 else int(r.lognormvariate(3.5, 1.0))
    T = sum(true.values())
    rng = SeededIntegers(99)
    noise = dgu.RationalSimpleDiscreteGaussian(sigma_sq=sigma_sq, size=len(true), rng=rng)
    nodes = sorted(true)
    raw = {n: true[n] + e for n, e in zip(nodes, noise)}
    pp_list = l2proj([raw[n] for n in nodes], T)
    pp = dict(zip(nodes, pp_list))
    for n in nxg.nodes:
        x, y = nxg.nodes[n]["xy"]
        pA = min(max(0.35 + 0.30 * (y / (side - 1)) + r.uniform(-0.1, 0.1), 0.0), 1.0)
        a = round(true[n] * pA)
        nxg.nodes[n].update(TRUE=true[n], RAW=raw[n], PP=pp[n], VA=a, VB=true[n] - a)
    neg = sum(1 for v in raw.values() if v < 0)
    print(f"PART B (toy): {side}x{side} grid, k={k}, ReCom epsilon={tol}, steps={steps}, sigma^2={float(sigma_sq):.4f}; "
          f"T_true={T}, T_raw={sum(raw.values())}, T_pp={sum(pp.values())}; raw<0 nodes={neg}; "
          f"node |RAW-TRUE| mean {statistics.fmean(abs(raw[n]-true[n]) for n in nodes):.2f}, |PP-TRUE| mean {statistics.fmean(abs(pp[n]-true[n]) for n in nodes):.2f}; "
          f"PP-TRUE on TRUE==0 nodes mean {statistics.fmean(pp[n]-true[n] for n in nodes if true[n]==0):+.2f}")
    graph = Graph.from_networkx(nxg)
    ideal_true = T / k
    for col in ("TRUE", "RAW", "PP"):
        for seed in seeds:
            updaters = {"pop": Tally(col, alias="pop"), "true_pop": Tally("TRUE", alias="true_pop"),
                        "va": Tally("VA", alias="va"), "vb": Tally("VB", alias="vb"), "cut_edges": cut_edges}
            init = Partition.from_random_assignment(graph, n_parts=k, epsilon=tol / 2, pop_col=col, updaters=updaters, rng=seed)
            ideal = sum(init["pop"].values()) / k
            chain = MarkovChain(partial(recom, pop_col=col, pop_target=ideal, epsilon=tol),
                                [contiguous, within_percent_of_ideal_population(init, tol, pop_key="pop")],
                                always_accept, init, steps, rng=seed)
            devs, seats, viol, cuts = [], [], 0, []
            t0 = time.perf_counter()
            for part in chain:
                d = max(abs(v - ideal_true) / ideal_true for v in part["true_pop"].values())
                devs.append(d)
                viol += d > tol
                seats.append(sum(1 for p in part.parts if part["va"][p] > part["vb"][p]))
                cuts.append(len(part["cut_edges"]))
            secs = time.perf_counter() - t0
            q = statistics.quantiles(devs, n=20)
            dist = {s: seats.count(s) / len(seats) for s in range(k + 1)}
            print(f"  pop={col:4s} seed={seed}: plans={len(devs)}; TRUE-pop max-dev mean {statistics.fmean(devs):.4%}, "
                  f"p95 {q[18]:.4%}, max {max(devs):.4%}; frac plans > {tol:.0%} under TRUE {viol / len(devs):.3f}; "
                  f"A-seats mean {statistics.fmean(seats):.3f} dist {{{', '.join(f'{s}:{v:.3f}' for s, v in dist.items())}}}; "
                  f"cut edges mean {statistics.fmean(cuts):.1f}; wall {secs:.1f}s ({len(devs) / secs:.0f} steps/s)")


def main():
    print(f"python {sys.version.split()[0]}")
    part_a(SIGMA_SQ_BLOCK_DETAILED)
    part_a(Fr(100))
    part_b(SIGMA_SQ_BLOCK_DETAILED, STEPS)
    part_b(Fr(100), STEPS)


if __name__ == "__main__":
    main()
