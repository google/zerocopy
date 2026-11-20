#!/usr/bin/env python3
"""Compare round-trip probe outputs across pretty-printer option variants.

Usage: python3 compare_variants.py <dir containing rt_<variant>.jsonl>
Prints (1) a per-variant table and (2) the classification of the default
variant's MISMATCH rows by the smallest option set that resolves them.
Writes default_mismatches.tsv (name, module, class, printed, re-elaborated).
"""
import collections, json, os, sys

D = sys.argv[1] if len(sys.argv) > 1 else '.'
VARIANTS = ['default', 'docgenopts', 'numerals', 'coe', 'coetypes', 'numcoetypes',
            'proofs', 'explicit', 'ppexplicit', 'all']
OK = ('exact', 'defeq_red', 'defeq_def')

R = {}
for v in VARIANTS:
    p = os.path.join(D, f'rt_{v}.jsonl')
    if os.path.exists(p):
        R[v] = {json.loads(l)['name']: json.loads(l) for l in open(p)}

d = R['default']
mm = sorted(n for n, r in d.items() if r['status'] == 'MISMATCH')
base_len = sum(r['pp_len'] for r in d.values()) / len(d)
print(f"{'variant':12s} {'exact%':>7s} {'ok%':>6s} {'MISMATCH':>8s} {'mvars':>6s} {'elabF':>6s} "
      f"{'parseF':>6s} {'mean_len':>8s} {'len_x':>6s} {'ms/decl':>7s} {'fixes_default_MISMATCH':>22s}")
for v, rs in R.items():
    n = len(rs)
    c = collections.Counter(r['status'] for r in rs.values())
    ml = sum(r['pp_len'] for r in rs.values()) / n
    ms = sum(r['pp_ns'] + r['parse_ns'] + r['elab_ns'] + r['cmp_ns'] for r in rs.values()) / n / 1e6
    res = sum(1 for nm in mm if rs[nm]['status'] in OK)
    print(f"{v:12s} {100 * c['exact'] / n:7.2f} {100 * sum(c[k] for k in OK) / n:6.2f} {c['MISMATCH']:8d} "
          f"{c['elab_mvars']:6d} {c['elab_fail']:6d} {c['parse_fail']:6d} {ml:8.1f} {ml / base_len:6.2f} "
          f"{ms:7.3f} {res:12d}/{len(mm)}")

def fixed(v, n):
    return v in R and R[v][n]['status'] in OK

cls = collections.Counter()
rows = []
for n in mm:
    rn, rc = fixed('numerals', n), fixed('coetypes', n)
    if rn and not rc:
        k = 'A:numeral-literal-type'
    elif rc and not rn:
        k = 'B:coercion-target'
    elif rn and rc:
        k = 'C:either-option'
    elif fixed('numcoetypes', n):
        k = 'D:needs-both'
    elif fixed('ppexplicit', n):
        k = 'E:needs-pp.explicit'
    else:
        k = 'F:needs-pp.all'
    cls[k] += 1
    r = d[n]
    reelab = r['msg'][len('reelab: '):] if r['msg'].startswith('reelab: ') else ''
    rows.append((n, r['module'], k, r['printed'], reelab))
print()
for k in sorted(cls):
    print(f'{cls[k]:5d} {k}')
with open('default_mismatches.tsv', 'w') as f:
    f.write('name\tmodule\tclass\tprinted_default\treelaborated_then_printed\n')
    for row in rows:
        f.write('\t'.join(x.replace('\t', ' ') for x in row) + '\n')
