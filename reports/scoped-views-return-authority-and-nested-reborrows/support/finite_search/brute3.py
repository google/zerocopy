import itertools, sys, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *
from brute2 import gen_states

SEVEN = ['ParentLt', 'RootsDisjoint', 'DepthCounts', 'ExclChildLoaned', 'ParentCoversActive',
         'SharedChildrenShared', 'SharedChildBelowOwn']
EXTRA = ['ParentsExist', 'LoanTargetsChild']

def run(N, A, maxd, plt):
    per = gen_states(N, A, maxd, plt)
    safe_viol = collections.Counter(); safe_ex = {}
    inv_viol = collections.Counter(); inv_ex = {}
    nr_only = 0
    for s in itertools.product(*per):
        lawfail = frozenset(n for n in SEVEN if not LAWS[n](s))
        if len(lawfail) > 1: continue
        for c in range(N):
            if not return_authority(s, c): continue
            t = end_raw(s, c)
            if t is None: continue
            we = write_exclusive(t); nr = no_resurrection(s, t)
            if we and not nr: nr_only += 1
            if not (we and nr):
                safe_viol[lawfail] += 1
                key = lawfail
                # prefer examples where WE s holds (step-caused failure)
                score = (0 if write_exclusive(s) else 1, len(repr(s)))
                if key not in safe_ex or score < safe_ex[key][0]:
                    safe_ex[key] = (score, s, c, t)
            post = frozenset(n for n in SEVEN if not LAWS[n](t))
            if post:
                # nontrivial if some law other than the violated one fails afterwards
                nontriv = post - lawfail
                inv_viol[(lawfail, bool(nontriv))] += 1
                k = (lawfail, bool(nontriv))
                if k not in inv_ex or len(repr(s)) < len(repr(inv_ex[k][0])):
                    inv_ex[k] = (s, c, t, sorted(post))
    print('NR fails while WE holds:', nr_only)
    print('--- safety step: violated-law-set -> count')
    for k in sorted(safe_viol, key=lambda k: sorted(k)):
        print(sorted(k), safe_viol[k], safe_ex[k][0], safe_ex[k][1:])
    print('--- invariant step:')
    for k in sorted(inv_viol, key=lambda k: (sorted(k[0]), k[1])):
        print(sorted(k[0]), 'nontrivial' if k[1] else 'persist-only', inv_viol[k], inv_ex[k])

if __name__ == '__main__':
    N, A, maxd, plt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == '1'
    run(N, A, maxd, plt)
