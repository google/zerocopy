import itertools, sys, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *
from brute2 import gen_states

def run(N, A, maxd, plt, lawnames):
    per = gen_states(N, A, maxd, plt)
    cnt = 0
    viol = collections.Counter(); ex = {}
    for s in itertools.product(*per):
        if write_exclusive(s): continue
        v = frozenset(n for n in lawnames if not LAWS[n](s))
        viol[v] += 1
        if v not in ex or len(repr(s)) < len(repr(ex[v])): ex[v] = s
    mins = [v for v in viol if not any(w < v for w in viol)]
    for v in sorted(mins, key=len):
        print(sorted(v), viol[v], ex[v])

if __name__ == '__main__':
    N, A, maxd, plt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == '1'
    run(N, A, maxd, plt, list(LAWS))
