import itertools, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *

ADDRS = [0, 1]
SUBSETS = [(0,), (1,), (0, 1), ()]

def successors(s, authority=True):
    """authority: True = return authority, 'local' = local return check, False = naive rule"""
    out = []
    if len(s) < 4:
        for m in (EXCL, SHARED):
            for A in SUBSETS:
                t = alloc(s, m, A)
                if t is not None: out.append(('alloc', m, A, t))
        for p in range(len(s)):
            for A in SUBSETS:
                t = borrow(s, p, A)
                if t is not None: out.append(('borrow', p, A, t))
                t = share(s, p, A)
                if t is not None: out.append(('share', p, A, t))
    for c in range(len(s)):
        if authority == 'local':
            if not local_return_check(s, c): continue
        elif authority and not return_authority(s, c):
            continue
        t = end_raw(s, c)
        if t is not None: out.append(('end', c, None, t))
    return out

def explore(authority, maxdepth=6):
    seen = {(): 0}
    frontier = [()]
    bad = []
    for depth in range(maxdepth):
        nf = []
        for s in frontier:
            for (op, x, y, t) in successors(s, authority):
                if t not in seen:
                    seen[t] = depth + 1
                    nf.append(t)
                    fails = [n for n, f in LAWS.items() if not f(t)]
                    if not write_exclusive(t): fails.append('WriteExclusive')
                    if op == 'end' and not no_resurrection(s, t): fails.append('NoResurrection')
                    if fails:
                        bad.append((s, op, x, t, fails))
        frontier = nf
    return seen, bad

if __name__ == '__main__':
    seen, bad = explore(True)
    print('authority: reachable', len(seen), 'bad', len(bad))
    for b in bad[:5]: print(b)
    seen, bad = explore('local')
    print('local check: reachable', len(seen), 'bad', len(bad))
    for b in bad[:5]: print(b)
    seen, bad = explore(False, 4)
    print('naive: reachable', len(seen), 'bad', len(bad))
    bad.sort(key=lambda b: len(b[3]))
    for b in bad[:5]: print(b)
