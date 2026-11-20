#!/usr/bin/env python3
"""Finite-model falsification test for the pair form of F3 (ghost complement).
NOT a proof.  Checks, for all pairs of PutGet lenses on |S| <= 4 with view
sizes 1..3:  (VWB l1 and VWB l2 and PutComm l1 l2)  <=>  HasGhostComplement.
(The right-hand side implies PutGet for both lenses, so restricting the
enumeration to PutGet lenses loses no instance of either side.)
Also re-checks the claim that VWB + PutComm implies two-way PutIndep.
"""
import itertools, sys
from collections import Counter
from bruteforce import putget_lenses, GetPut, PutGet, PutPut, PutIndep, PutComm

def has_ghost_complement(l1, l2, n, k1, k2):
    g1, p1 = l1; g2, p2 = l2
    if n == 0:
        return True
    if n % (k1 * k2) != 0:
        return False
    m = n // (k1 * k2)
    if not all(g1[p1[s][a]] == a and g2[p1[s][a]] == g2[s] for s in range(n) for a in range(k1)):
        return False
    if not all(g2[p2[s][b]] == b and g1[p2[s][b]] == g1[s] for s in range(n) for b in range(k2)):
        return False
    for c in itertools.product(range(m), repeat=n):
        if len({(g1[s], g2[s], c[s]) for s in range(n)}) != n:
            continue
        if all(c[p1[s][a]] == c[s] for s in range(n) for a in range(k1)) and \
           all(c[p2[s][b]] == c[s] for s in range(n) for b in range(k2)):
            return True
    return False

def main(max_n=4, max_k=3):
    stats = Counter()
    for n in range(0, max_n + 1):
        Ls = {k: putget_lenses(n, k) for k in range(1, max_k + 1)}
        vwb = {k: [GetPut(l, n, k) and PutPut(l, n, k) for l in Ls[k]] for k in Ls}
        for k1 in Ls:
            for k2 in Ls:
                if k2 < k1:
                    continue
                for i1, l1 in enumerate(Ls[k1]):
                    for i2, l2 in enumerate(Ls[k2]):
                        lhs = vwb[k1][i1] and vwb[k2][i2] and PutComm(l1, l2, n, k1, k2)
                        # cheap necessary condition for rhs: two-way independence
                        ind = PutIndep(l1, l2, n, k1) and PutIndep(l2, l1, n, k2)
                        if lhs and not ind:
                            print('VWB+PutComm => PutIndep REFUTED', n, k1, k2, l1, l2); return False
                        rhs = ind and has_ghost_complement(l1, l2, n, k1, k2)
                        stats['pairs'] += 1
                        stats['lhs'] += lhs
                        if lhs != rhs:
                            print('F3-pair REFUTED', n, k1, k2, l1, l2, lhs, rhs); return False
    print('F3 pair form not refuted on', dict(stats))
    return True

if __name__ == '__main__':
    ok = main()
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    sys.exit(0 if ok else 1)
