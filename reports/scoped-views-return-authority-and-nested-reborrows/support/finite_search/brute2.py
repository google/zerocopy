import itertools, sys, collections
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from model import *

def cells_opts(N, A, maxd, loan_targets):
    single = [None] + [('own', d, 0) for d in range(maxd + 1)] + [('loan', t) for t in loan_targets]
    return list(itertools.product(single, repeat=A))

def gen_states(N, A, maxd, parent_lt_struct=False, dangling=True):
    # per-view options
    per = []
    for i in range(N):
        if parent_lt_struct:
            pars = [None] + list(range(i))
            lts = list(range(i + 1, N))
        else:
            pars = [None] + list(range(N + (1 if dangling else 0)))
            lts = list(range(N + (1 if dangling else 0)))
        opts = []
        for p in pars:
            for m in (EXCL, SHARED):
                for act in (True, False):
                    for cs in cells_opts(N, A, maxd, lts):
                        opts.append((p, m, act, cs))
        per.append(opts)
    return per

def run(N, A, maxd, parent_lt_struct, authority_fn, label):
    per = gen_states(N, A, maxd, parent_lt_struct)
    total = 1
    for o in per: total *= len(o)
    print(label, 'states', total, flush=True)
    viol_sets = collections.Counter()
    examples = {}
    nbad = 0
    for s in itertools.product(*per):
        if not write_exclusive(s): continue
        for c in range(N):
            if not authority_fn(s, c): continue
            t = end_raw(s, c)
            if t is None: continue
            if write_exclusive(t) and no_resurrection(s, t): continue
            nbad += 1
            v = frozenset(n for n, f in LAWS.items() if not f(s))
            viol_sets[v] += 1
            if v not in examples or len(repr(s)) < len(repr(examples[v][0])):
                examples[v] = (s, c, t)
    print('bad', nbad)
    # minimal violated sets
    mins = [v for v in viol_sets if not any(w < v for w in viol_sets)]
    for v in sorted(mins, key=len):
        print(sorted(v), viol_sets[v])
        print('   ', examples[v])
    return viol_sets, examples

if __name__ == '__main__':
    N, A, maxd, plt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] == '1'
    run(N, A, maxd, plt, return_authority, f'N={N} A={A} d={maxd} plt={plt}')
