#!/usr/bin/env python3
"""Compare four formalisations of ACMG/AMP evidence combination over a bounded box.

Systems compared (all evaluated on criterion COUNTS, not on evidence content):
  R   : Richards et al. 2015 Table 5, encoded here directly from the published text
        (a re-encoding written for this probe).
  IV  : InterVar's classfy() function, extracted verbatim from Intervar.py at a
        pinned revision and executed with stubbed globals (no evidence file).
  B18 : Tavtigian et al. 2018 naive-Bayes model: OP = OPVSt^(Nsu/8+Nm/4+Nst/2+Nvst)
        for pathogenic evidence, inverse for benign; Post = OP*p/((OP-1)*p+1).
        Thresholds P > 0.99, LP >= 0.90, LB < 0.10, B < 0.001 (VUS otherwise).
  P20 : Tavtigian et al. 2020 points: Su=1, M=2, St=4, VSt=8 (benign negative);
        P >= 10, LP 6..9, VUS 0..5, LB -1..-6, B <= -7.
BA1 is treated as a stand-alone Benign override in B18 and P20 (both papers model
only the four graded strengths).

Usage: python3 acmg_probe.py /path/to/Intervar.py
"""
import itertools, json, math, os, re, sys
from collections import Counter

src = open(sys.argv[1]).read().splitlines()
# lines are 1-based in the report: sum_of_list at 727-731, classfy at 733-856
start = next(i for i, l in enumerate(src) if l.startswith('def sum_of_list('))
end = next(i for i, l in enumerate(src) if l.startswith('def check_PVS1('))
code = '\n'.join(src[start:end])
ns = {'os': os, 're': re, 'paras': {'evidence_file': '/nonexistent/evidence'}, 'user_evidence_dict': {}}
exec(code, ns)
classfy = ns['classfy']

def iv(pvs, ps, pm, pp, ba1, bs, bp):
    r = classfy(pvs, [1] * ps + [0] * (5 - ps), [1] * pm + [0] * (7 - pm), [1] * pp + [0] * (6 - pp),
                ba1, [1] * bs + [0] * (5 - bs), [1] * bp + [0] * (8 - bp), {}, [])
    return {'Pathogenic': 'P', 'Likely pathogenic': 'LP', 'Benign': 'B', 'Likely benign': 'LB',
            'Uncertain significance': 'VUS'}[r]

def richards(pvs, ps, pm, pp, ba1, bs, bp):
    path = (pvs >= 1 and (ps >= 1 or pm >= 2 or (pm == 1 and pp == 1) or pp >= 2)) or ps >= 2 or \
           (ps == 1 and (pm >= 3 or (pm == 2 and pp >= 2) or (pm == 1 and pp >= 4)))
    lpath = (pvs >= 1 and pm == 1) or (ps == 1 and 1 <= pm <= 2) or (ps == 1 and pp >= 2) or pm >= 3 or \
            (pm == 2 and pp >= 2) or (pm == 1 and pp >= 4)
    ben = ba1 >= 1 or bs >= 2
    lben = (bs == 1 and bp == 1) or bp >= 2
    pside = 'P' if path else ('LP' if lpath else None)
    bside = 'B' if ben else ('LB' if lben else None)
    if pside and bside:
        return 'VUS'          # "criteria for benign and pathogenic are contradictory"
    return pside or bside or 'VUS'

def bayes(pvs, ps, pm, pp, ba1, bs, bp, opvst=350.0, prior=0.10):
    if ba1:
        return 'B', None
    e = pp / 8 + pm / 4 + ps / 2 + pvs - (bp / 8 + bs / 2)
    op = opvst ** e
    post = op * prior / ((op - 1) * prior + 1)
    if post > 0.99:
        c = 'P'
    elif post >= 0.90:
        c = 'LP'
    elif post < 0.001:
        c = 'B'
    elif post < 0.10:
        c = 'LB'
    else:
        c = 'VUS'
    return c, post

def points(pvs, ps, pm, pp, ba1, bs, bp):
    if ba1:
        return 'B', None
    s = 8 * pvs + 4 * ps + 2 * pm + pp - 4 * bs - bp
    c = 'P' if s >= 10 else 'LP' if s >= 6 else 'VUS' if s >= 0 else 'LB' if s >= -6 else 'B'
    return c, s

box = list(itertools.product(range(2), range(5), range(7), range(6), range(2), range(5), range(8)))
out = {'box': 'PVS1 0-1, PS 0-4, PM 0-6, PP 0-5, BA1 0-1, BS 0-4, BP 0-7', 'n_combinations': len(box)}

agree = Counter(); dis_examples = {}
path_only = [c for c in box if c[4] == 0 and c[5] == 0 and c[6] == 0]
mixed = [c for c in box if (c[0] or c[1] or c[2] or c[3]) and (c[4] or c[5] or c[6])]
out['n_pathogenic_only'] = len(path_only)
out['n_mixed'] = len(mixed)

def cmp(name, f, g, subset):
    d = [c for c in subset if f(*c) != g(*c)]
    return len(d), d[:6]

R = richards; IV = iv
B18 = lambda *c: bayes(*c)[0]
B18b = lambda *c: bayes(*c, prior=0.102)[0]
P20 = lambda *c: points(*c)[0]
pairs = {'R_vs_IV': (R, IV), 'R_vs_B18(p=0.10)': (R, B18), 'R_vs_B18(p=0.102)': (R, B18b), 'R_vs_P20': (R, P20),
         'B18(p=0.102)_vs_P20': (B18b, P20)}
for nm, (f, g) in pairs.items():
    for subset_name, subset in (('all', box), ('pathogenic_only', path_only), ('mixed', mixed)):
        n, ex = cmp(nm, f, g, subset)
        out[f'{nm}:{subset_name}'] = {'disagreements': n, 'examples(pvs,ps,pm,pp,ba1,bs,bp)->(f,g)': [(e, f(*e), g(*e)) for e in ex]}

# the 18 Table-5 rules at their minimal counts, posterior under B18
rules = {
 'P(ia) PVS+>=1PS': (1,1,0,0), 'P(ib) PVS+>=2PM': (1,0,2,0), 'P(ic) PVS+1PM+1PP': (1,0,1,1), 'P(id) PVS+>=2PP': (1,0,0,2),
 'P(ii) >=2PS': (0,2,0,0), 'P(iiia) PS+>=3PM': (0,1,3,0), 'P(iiib) PS+2PM+>=2PP': (0,1,2,2), 'P(iiic) PS+1PM+>=4PP': (0,1,1,4),
 'LP(i) PVS+1PM': (1,0,1,0), 'LP(ii) PS+1-2PM': (0,1,1,0), 'LP(iii) PS+>=2PP': (0,1,0,2), 'LP(iv) >=3PM': (0,0,3,0),
 'LP(v) 2PM+>=2PP': (0,0,2,2), 'LP(vi) 1PM+>=4PP': (0,0,1,4),
}
tab = {}
for k, (a_, b_, c_, d_) in rules.items():
    cat10, post10 = bayes(a_, b_, c_, d_, 0, 0, 0)
    cat102, post102 = bayes(a_, b_, c_, d_, 0, 0, 0, prior=0.102)
    catp, pts = points(a_, b_, c_, d_, 0, 0, 0)
    tab[k] = {'OP': round(350 ** (d_/8 + c_/4 + b_/2 + a_), 1), 'post(p=0.10)': round(post10, 5), 'B18(p=0.10)': cat10,
              'post(p=0.102)': round(post102, 5), 'B18(p=0.102)': cat102, 'points': pts, 'P20': catp,
              'Richards': richards(a_, b_, c_, d_, 0, 0, 0), 'InterVar': iv(a_, b_, c_, d_, 0, 0, 0)}
out['table5_minimal_combinations'] = tab
out['benign_rules'] = {
    'LB(i) 1BS+1BP': dict(zip(('B18', 'post'), bayes(0,0,0,0,0,1,1))) | {'P20': points(0,0,0,0,0,1,1)},
    'LB(ii) 2BP': dict(zip(('B18', 'post'), bayes(0,0,0,0,0,0,2))) | {'P20': points(0,0,0,0,0,0,2)},
    'B(ii) 2BS': dict(zip(('B18', 'post'), bayes(0,0,0,0,0,2,0))) | {'P20': points(0,0,0,0,0,2,0)},
}
print(json.dumps(out, indent=1))
