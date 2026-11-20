#!/usr/bin/env python3
"""Summarize round-trip probe JSONL outputs."""
import json, sys, collections, statistics

def pct(xs, p):
    if not xs:
        return float('nan')
    xs = sorted(xs)
    k = min(len(xs) - 1, max(0, int(round(p / 100.0 * (len(xs) - 1)))))
    return xs[k]

for path in sys.argv[1:]:
    rows = [json.loads(l) for l in open(path)]
    c = collections.Counter(r['status'] for r in rows)
    n = len(rows)
    print(f'=== {path}: n={n}')
    for k, v in c.most_common():
        print(f'  {k:12s} {v:7d}  {100.0*v/n:6.2f}%')
    tot = [ (r['pp_ns']+r['parse_ns']+r['elab_ns']+r['cmp_ns'])/1e6 for r in rows]
    for fld in ['pp_ns', 'parse_ns', 'elab_ns', 'cmp_ns']:
        xs = [r[fld]/1e6 for r in rows]
        print(f'  {fld:9s} sum={sum(xs)/1000:8.2f}s mean={statistics.mean(xs):7.3f}ms p50={pct(xs,50):7.3f} p90={pct(xs,90):7.3f} p99={pct(xs,99):8.3f} max={max(xs):9.1f}')
    print(f'  total     sum={sum(tot)/1000:8.2f}s mean={statistics.mean(tot):7.3f}ms p50={pct(tot,50):7.3f} p90={pct(tot,90):7.3f} p99={pct(tot,99):8.3f} max={max(tot):9.1f}')
    lens = [r['pp_len'] for r in rows if r['pp_len']]
    print(f'  pp_len mean={statistics.mean(lens):.1f} p50={pct(lens,50)} p90={pct(lens,90)} p99={pct(lens,99)} max={max(lens)}')
