#!/usr/bin/env python3
"""Monte Carlo extension of pct_changepoint_probe.py Part A for larger L.

Same transliteration of Coyote's Shuffle loop (draw point uniform on [0, L) for every
idx from L-1 down to 1) versus textbook Fisher-Yates (point uniform on [0, idx]).
Reports P(change point 0 is selected) and the mean selected index when the first c
shuffled elements are kept, for c in {1, 2, 3, 10}.

Usage: python3 pct_changepoint_mc.py <seed>
"""
import random, sys

def run(L, trials, c_list, rng, textbook):
    hit0 = {c: 0 for c in c_list}
    sums = {c: 0 for c in c_list}
    for _ in range(trials):
        r = list(range(L))
        for idx in range(L - 1, 0, -1):
            p = rng.randrange(idx + 1) if textbook else rng.randrange(L)
            r[idx], r[p] = r[p], r[idx]
        for c in c_list:
            head = r[:c]
            if 0 in head:
                hit0[c] += 1
            sums[c] += sum(head) / c
    return {c: (hit0[c] / trials, sums[c] / trials) for c in c_list}

def main():
    rng = random.Random(int(sys.argv[1]))
    c_list = [1, 2, 3, 10]
    print('L\ttrials\tvariant\tc\tP(0 selected)\tuniform c/L\tmean selected index\tuniform mean (L-1)/2')
    for L, trials in ((10, 100000), (100, 20000), (1000, 2000)):
        for textbook in (False, True):
            res = run(L, trials, c_list, rng, textbook)
            for c in c_list:
                if c > L:
                    continue
                p0, mean = res[c]
                print(f'{L}\t{trials}\t{"fisher_yates" if textbook else "coyote"}\t{c}\t{p0:.4f}\t{c/L:.4f}\t{mean:.2f}\t{(L-1)/2:.2f}')

if __name__ == '__main__':
    main()
