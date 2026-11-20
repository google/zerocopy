#!/usr/bin/env python3
"""Summarize ReelabProbe TSV outputs: status x text-roundtrip, timing quantiles,
and coarse classification of the first differing subterm pair."""
import collections, re, statistics, sys

def load(path):
    rows = []
    meta = {}
    with open(path, encoding='utf-8') as f:
        for line in f:
            line = line.rstrip('\n')
            if line.startswith('#'):
                parts = line[2:].split('\t')
                meta.setdefault(parts[0], []).append(parts[1:])
                continue
            if line.startswith('name\t'):
                continue
            p = line.split('\t')
            if len(p) < 10:
                continue
            rows.append(dict(name=p[0], module=p[1], status=p[2], text=p[3],
                             pp=int(p[4]), parse=int(p[5]), elab=int(p[6]), cmp=int(p[7]),
                             length=int(p[8]), detail=p[9]))
    return rows, meta

def classify_diff(detail):
    m = re.search(r'DIFF\[(.*?) ~~ (.*?)\]', detail)
    if not m:
        return 'no-diff-recorded'
    a, b = m.group(1), m.group(2)
    both = a + ' ' + b
    if re.search(r'\boptParam\b', both): return 'optParam/outParam/autoParam annotation'
    if re.search(r'\b(outParam|autoParam|semiOutParam)\b', both): return 'optParam/outParam/autoParam annotation'
    if re.match(r'^(Sort|Type|max|imax|succ|u_?\w*|[0-9]+)\b', a) and re.match(r'^(Sort|Type|max|imax|succ|u_?\w*|[0-9]+)\b', b):
        return 'universe level'
    if re.search(r'\.\{[^}]*\}', a) and re.search(r'\.\{[^}]*\}', b) and a.split('.{')[0] == b.split('.{')[0]:
        return 'universe level'
    if re.search(r'_proof_|byContradiction|of_decide|Decidable\.|\bproof\b|Nat\.lt_|_lemma', both):
        return 'proof subterm'
    if re.search(r'\binst[A-Z]\w*|\.inst\w*|\bto[A-Z]\w*|instHAdd|instHMul|instOfNat', both):
        return 'instance path'
    if re.search(r'OfNat\.ofNat|instOfNatNat|Nat\.cast|Int\.ofNat|NatCast|IntCast|↑', both):
        return 'numeral/coercion'
    if re.match(r'^#\d+$', a) or re.match(r'^#\d+$', b):
        return 'bound variable'
    return 'other'

def q(vals, p):
    if not vals: return float('nan')
    vals = sorted(vals)
    k = min(len(vals) - 1, int(round(p * (len(vals) - 1))))
    return vals[k]

def main():
    for path in sys.argv[1:]:
        rows, meta = load(path)
        print('=' * 70)
        print(path, 'rows', len(rows), 'meta', {k: v for k, v in meta.items() if k in ('mode', 'import_ms', 'candidates', 'total_ms')})
        st = collections.Counter(r['status'] for r in rows)
        n = len(rows)
        for k, v in st.most_common():
            print(f'  status {k:10s} {v:6d} {100.0*v/n:6.2f}%')
        cross = collections.Counter((r['status'], r['text']) for r in rows)
        print('  status x text-roundtrip:')
        for (s, t), v in sorted(cross.items()):
            print(f'    {s:10s} {t:8s} {v:6d}')
        tot = [ (r['pp'] + r['parse'] + r['elab'] + r['cmp']) / 1e6 for r in rows]
        print('  per-theorem total ms: median %.3f p90 %.3f p99 %.3f max %.1f mean %.3f' % (
            q(tot, .5), q(tot, .9), q(tot, .99), max(tot), statistics.mean(tot)))
        for fld in ('pp', 'parse', 'elab', 'cmp'):
            v = [r[fld] / 1e6 for r in rows]
            print(f'    {fld:6s} median {q(v,.5):.3f} p99 {q(v,.99):.3f} max {max(v):.1f} sum {sum(v)/1000:.1f}s')
        lens = [r['length'] for r in rows if r['length'] > 0]
        print('  printed length chars: median %d p90 %d max %d mean %.1f' % (q(lens, .5), q(lens, .9), max(lens), statistics.mean(lens)))
        for s in ('defeq', 'differ'):
            c = collections.Counter(classify_diff(r['detail']) for r in rows if r['status'] == s)
            print(f'  first-difference classes for {s}:', dict(c.most_common()))
            for tt in ('same', 'changed'):
                c2 = collections.Counter(classify_diff(r['detail']) for r in rows if r['status'] == s and r['text'] == tt)
                print(f'     with text {tt}:', dict(c2.most_common()))
        ef = collections.Counter(re.sub(r'\?m\.\d+|_uniq\.\d+|\d+', 'N', r['detail'].split(' || ')[0])[:70] for r in rows if r['status'] == 'elabfail')
        print('  top elabfail messages:')
        for k, v in ef.most_common(8):
            print(f'    {v:5d} {k}')
        mv = sum(1 for r in rows if r['status'] == 'mvar' and '⋯' in r['detail'])
        print(f'  mvar rows whose printed text contains the proof-elision glyph: {mv}')

if __name__ == '__main__':
    main()
