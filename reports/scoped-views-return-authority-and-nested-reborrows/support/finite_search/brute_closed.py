import itertools, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *

A = 2
OWN = ('own', 0, 0)
def mkview(p, act, d):
    return (p, EXCL, act, tuple(OWN if a in d else None for a in range(A)))
DOMS = [(), (0,), (1,), (0, 1)]
MAXID = 4
PARS = [None] + list(range(MAXID))

def opts():
    return [mkview(p, act, d) for p in PARS for act in (True, False) for d in DOMS]

def variants(v0, comp):
    p, m, act, cs = v0
    d = tuple(a for a in range(A) if cs[a] is not None)
    if comp is None: return [v0]
    if comp == 'parent': return [mkview(q, act, d) for q in PARS]
    if comp == 'active': return [mkview(p, b, d) for b in (True, False)]
    if comp == 'domain': return [mkview(p, act, e) for e in DOMS]

def run():
    O = opts()
    bad = {}; ex = {}
    for n0 in range(0, 3):
        for s0 in itertools.product(O, repeat=n0):
            pe = parents_exist(s0)
            auth0 = [v for v in range(MAXID) if return_authority(s0, v)]
            if not auth0: continue
            for comp in (None, 'parent', 'active', 'domain', 'fresh'):
                vcomp = None if comp == 'fresh' else comp
                for k in range(n0 + 1):  # which old view varies (k == n0: none)
                    if comp in (None, 'fresh') and k != n0: continue
                    if comp not in (None, 'fresh') and k == n0: continue
                    olds_list = [list(s0)]
                    if k < n0:
                        olds_list = []
                        for vv in variants(s0[k], vcomp):
                            o = list(s0); o[k] = vv; olds_list.append(o)
                    for olds in olds_list:
                        for nn in range(0, 3 - n0 + 1):
                            newopts = [x for x in O if (comp == 'fresh' or not x[2])]
                            for news in itertools.product(newopts, repeat=nn):
                                s1 = tuple(olds) + tuple(news)
                                for v in auth0:
                                    if return_authority(s1, v): continue
                                    key = (comp, pe)
                                    bad[key] = bad.get(key, 0) + 1
                                    if key not in ex or len(repr((s0, s1))) < len(repr(ex[key])):
                                        ex[key] = (s0, s1, v)
    print(bad)
    for k in sorted(ex, key=str): print(k, ex[k])

run()
