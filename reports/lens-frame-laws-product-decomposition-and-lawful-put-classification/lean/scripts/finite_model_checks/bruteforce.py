#!/usr/bin/env python3
"""Finite-model falsification tests for the statements F1, F2, F3.

This is NOT a proof.  It exhaustively enumerates lenses on tiny finite types
and checks that the statements are not refuted there, and it reports
for every hypothesis of F1 the smallest instance that violates exactly that
hypothesis (to cross-check the F4 witnesses).

State type S = range(n), view types = range(k).
A lens is (get, put): get[s] in range(k), put[s][a] in range(n).
"""
import itertools
import sys
from collections import Counter


def all_gets(n, k):
    return list(itertools.product(range(k), repeat=n))


def putget_lenses(n, k):
    """All lenses on range(n) -> range(k) satisfying PutGet."""
    out = []
    for get in all_gets(n, k):
        fibers = [[s for s in range(n) if get[s] == a] for a in range(k)]
        if n > 0 and any(len(f) == 0 for f in fibers):
            continue  # PutGet impossible: put s a must land in fiber a
        # put[s][a] ranges over fiber a
        per_s = list(itertools.product(*fibers))  # tuple indexed by a
        for put in itertools.product(per_s, repeat=n):
            out.append((get, put))
    return out


def all_lenses(n, k):
    out = []
    per_s = list(itertools.product(range(n), repeat=k))
    for get in all_gets(n, k):
        for put in itertools.product(per_s, repeat=n):
            out.append((get, put))
    return out


def GetPut(l, n, k):
    g, p = l
    return all(p[s][g[s]] == s for s in range(n))


def PutGet(l, n, k):
    g, p = l
    return all(g[p[s][a]] == a for s in range(n) for a in range(k))


def PutPut(l, n, k):
    g, p = l
    return all(p[p[s][a]][b] == p[s][b] for s in range(n) for a in range(k) for b in range(k))


def PutIndep(l1, l2, n, k1):
    g1, p1 = l1
    g2, p2 = l2
    return all(g2[p1[s][a]] == g2[s] for s in range(n) for a in range(k1))


def PutComm(l1, l2, n, k1, k2):
    g1, p1 = l1
    g2, p2 = l2
    return all(p2[p1[s][a]][b] == p1[p2[s][b]][a]
               for s in range(n) for a in range(k1) for b in range(k2))


def JointExt(l1, l2, n):
    g1, _ = l1
    g2, _ = l2
    seen = set()
    for s in range(n):
        key = (g1[s], g2[s])
        if key in seen:
            return False
        seen.add(key)
    return True


def IsProductDecomposition(l1, l2, n, k1, k2):
    g1, p1 = l1
    g2, p2 = l2
    pg = [(g1[s], g2[s]) for s in range(n)]
    inj = len(set(pg)) == n
    surj = set(pg) == set(itertools.product(range(k1), range(k2)))
    f1 = all(pg[p1[s][a]] == (a, g2[s]) for s in range(n) for a in range(k1))
    f2 = all(pg[p2[s][b]] == (g1[s], b) for s in range(n) for b in range(k2))
    return inj and surj and f1 and f2


def pairPut_inverse(l1, l2, n, k1, k2, s0):
    g1, p1 = l1
    g2, p2 = l2
    pp = lambda a, b: p2[p1[s0][a]][b]
    left = all(pp(g1[s], g2[s]) == s for s in range(n))
    right = all((g1[pp(a, b)], g2[pp(a, b)]) == (a, b) for a in range(k1) for b in range(k2))
    return left and right


def check_F1(max_n=4, max_k=3):
    stats = Counter()
    witnesses = {}
    for n in range(0, max_n + 1):
        for k1 in range(0, max_k + 1):
            L1 = putget_lenses(n, k1)
            for k2 in range(k1, max_k + 1):
                L2 = putget_lenses(n, k2)
                for l1 in L1:
                    for l2 in L2:
                        i12 = PutIndep(l1, l2, n, k1)
                        i21 = PutIndep(l2, l1, n, k2)
                        ext = JointExt(l1, l2, n)
                        ne = n > 0
                        concl = IsProductDecomposition(l1, l2, n, k1, k2)
                        hyps = i12 and i21 and ext and ne
                        stats['pairs'] += 1
                        # F1: hyps -> conclusion
                        if hyps and not concl:
                            print('F1 REFUTED', n, k1, k2, l1, l2)
                            return False
                        # F1 exact form (restricted to PutGet pairs)
                        rhs = i12 and i21 and ext and (ne or k1 * k2 == 0)
                        if concl != rhs:
                            print('F1-iff REFUTED', n, k1, k2, l1, l2)
                            return False
                        # derived laws need no nonemptiness
                        if i12 and ext:
                            if not (GetPut(l1, n, k1) and PutPut(l1, n, k1)):
                                print('derived law 1/2 REFUTED', n, k1, k2, l1, l2)
                                return False
                        if i12 and i21 and ext:
                            if not PutComm(l1, l2, n, k1, k2):
                                print('derived law 3 REFUTED', n, k1, k2, l1, l2)
                                return False
                        # explicit inverse needs only PutIndep l2 l1
                        if i21 and ext:
                            for s0 in range(n):
                                if not pairPut_inverse(l1, l2, n, k1, k2, s0):
                                    print('F1-inverse REFUTED', n, k1, k2, l1, l2, s0)
                                    return False
                        if hyps:
                            stats['hyps_hold'] += 1
                        # single-hypothesis violations (PutGet holds here by construction)
                        if ne and ext and i21 and not i12:
                            witnesses.setdefault('only PutIndep l1 l2 fails', (n, k1, k2, l1, l2))
                            # is the bijection still there?
                            stats['i12 fails: pairPut still inverse'] += all(
                                pairPut_inverse(l1, l2, n, k1, k2, s0) for s0 in range(n))
                            stats['i12 fails: total'] += 1
                        if ne and ext and i12 and not i21:
                            witnesses.setdefault('only PutIndep l2 l1 fails', (n, k1, k2, l1, l2))
                        if ne and i12 and i21 and not ext:
                            witnesses.setdefault('only JointExt fails', (n, k1, k2, l1, l2))
                        if (not ne) and i12 and i21 and ext and not concl:
                            witnesses.setdefault('only Nonempty S fails', (n, k1, k2, l1, l2))
    print('F1 family not refuted on', dict(stats))
    for k, v in witnesses.items():
        print('  smallest witness:', k, '->', v)
    return True


def check_F1_putget_necessity(max_n=3, max_k=2):
    """Pairs where l1 fails PutGet but everything else holds: conclusion must fail."""
    found = None
    for n in range(1, max_n + 1):
        for k1 in range(1, max_k + 1):
            for k2 in range(1, max_k + 1):
                L2 = putget_lenses(n, k2)
                for l1 in all_lenses(n, k1):
                    if PutGet(l1, n, k1):
                        continue
                    for l2 in L2:
                        if (PutIndep(l1, l2, n, k1) and PutIndep(l2, l1, n, k2)
                                and JointExt(l1, l2, n)):
                            if IsProductDecomposition(l1, l2, n, k1, k2):
                                print('PutGet necessity REFUTED', n, k1, k2, l1, l2)
                                return False
                            if found is None:
                                found = (n, k1, k2, l1, l2)
    print('PutGet necessity not refuted; smallest witness with only PutGet l1 failing:', found)
    return True


def has_constant_complement(l, n, k):
    g, p = l
    if k == 0:
        return n == 0
    if n % k != 0:
        return False
    m = n // k
    for c in itertools.product(range(m), repeat=n):
        pairs = {(g[s], c[s]) for s in range(n)}
        if len(pairs) != n:  # (get, c) bijective onto range(k) x range(m) since n == k*m
            continue
        if all(c[p[s][a]] == c[s] for s in range(n) for a in range(k)):
            # also need get(put s a) == a : the first component of e (put s a)
            if all(g[p[s][a]] == a for s in range(n) for a in range(k)):
                return True
    return False


def check_F3(max_n=4, max_k=3):
    stats = Counter()
    for n in range(0, max_n + 1):
        for k in range(1, max_k + 1):
            lenses = all_lenses(n, k) if n <= 3 else putget_lenses(n, k)
            for l in lenses:
                vwb = GetPut(l, n, k) and PutGet(l, n, k) and PutPut(l, n, k)
                cc = has_constant_complement(l, n, k)
                stats['lenses'] += 1
                stats['vwb'] += vwb
                if vwb != cc:
                    print('F3 REFUTED', n, k, l, vwb, cc)
                    return False
    print('F3 not refuted on', dict(stats),
          '(all lenses for |S|<=3; all PutGet lenses for |S|=4)')
    return True


def check_F2(max_n=4):
    """Families of 3 lenses with Boolean / ternary views, |S| <= max_n."""
    stats = Counter()
    for n in range(1, max_n + 1):
        for ks in [(2, 2, 2), (1, 2, 2), (2, 2, 1), (2, 1, 3)]:
            Ls = [putget_lenses(n, k) for k in ks]
            for l0 in Ls[0]:
                for l1 in Ls[1]:
                    if not (PutIndep(l0, l1, n, ks[0]) and PutIndep(l1, l0, n, ks[1])):
                        continue
                    for l2 in Ls[2]:
                        if not (PutIndep(l0, l2, n, ks[0]) and PutIndep(l2, l0, n, ks[2])
                                and PutIndep(l1, l2, n, ks[1]) and PutIndep(l2, l1, n, ks[2])):
                            continue
                        fam = [l0, l1, l2]
                        tup = [tuple(l[0][s] for l in fam) for s in range(n)]
                        ext = len(set(tup)) == n
                        if not ext:
                            continue
                        stats['families satisfying hyps'] += 1
                        surj = set(tup) == set(itertools.product(*[range(k) for k in ks]))
                        upd = all(
                            tup[fam[i][1][s][a]] == tuple(a if j == i else tup[s][j] for j in range(3))
                            for i in range(3) for s in range(n) for a in range(ks[i]))
                        laws = all(GetPut(fam[i], n, ks[i]) and PutPut(fam[i], n, ks[i])
                                   for i in range(3))
                        comm = all(PutComm(fam[i], fam[j], n, ks[i], ks[j])
                                   for i in range(3) for j in range(3) if i != j)
                        if not (surj and upd and laws and comm):
                            print('F2 REFUTED', n, ks, fam)
                            return False
    print('F2 (3-lens families) not refuted on', dict(stats))
    return True


if __name__ == '__main__':
    ok = True
    ok &= check_F1()
    ok &= check_F1_putget_necessity()
    ok &= check_F3()
    ok &= check_F2()
    print('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED')
    sys.exit(0 if ok else 1)
