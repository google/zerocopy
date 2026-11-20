#!/usr/bin/env python3
"""Find the smallest witness (fewest total ops) for which the direct-effect
round-robin bound C_i <= T_i + a_i*(n-1)*D_S fails on the toy 'ooo' core.
Uses the simulator in probe_composition.py (same directory). TOY MODEL ONLY."""
import random
import sys
import probe_composition as pc


def main():
    prng = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    rng = random.Random(prng)
    best = None
    for _ in range(trials):
        th = [pc.gen_thread(rng, 'ooo') for _ in range(pc.N)]
        size = sum(len(x) for x in th)
        if best is not None and size >= best[0]:
            continue
        T = [pc.simulate([x], 'ooo', 'iso')[0] for x in th]
        a = [sum(1 for k, _ in x if k == 'S') for x in th]
        C = pc.simulate(th, 'ooo', 'rr')
        for i in range(pc.N):
            bound = T[i] + a[i] * (pc.N - 1) * pc.D_S
            if C[i] > bound:
                best = (size, th, T, a, C, i, bound)
    if best is None:
        print('no witness found')
        return
    size, th, T, a, C, i, bound = best
    print(f'prng={prng} trials={trials}')
    for k, x in enumerate(th):
        print(f'thread {k}: ops={[(kind, deps) for kind, deps in x]} T_iso={T[k]} a={a[k]} C_corun={C[k]}')
    print(f'violating thread {i}: C={C[i]} > T+a*(n-1)*D_S = {bound}')


if __name__ == '__main__':
    main()
