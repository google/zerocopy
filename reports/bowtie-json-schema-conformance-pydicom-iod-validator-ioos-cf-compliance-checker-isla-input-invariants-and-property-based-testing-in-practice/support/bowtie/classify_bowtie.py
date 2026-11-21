#!/usr/bin/env python3
"""Classify a Bowtie `suite` JSONL report by disagreement kind.

Per implementation and per test: agree / FALSE_ACCEPT (expected invalid, reported valid) /
FALSE_REJECT (expected valid, reported invalid) / ERRORED (case- or test-level error) / SKIPPED.
Usage: classify_bowtie.py report.jsonl
"""
import json, sys, collections

def main(path):
    lines = [json.loads(l) for l in open(path)]
    header = lines[0]
    cases = {l['seq']: l['case'] for l in lines if 'case' in l}
    per = collections.defaultdict(collections.Counter)
    fa_by_desc = collections.defaultdict(collections.Counter)
    for l in lines:
        if 'implementation' not in l:
            continue
        impl = l['implementation']; seq = l['seq']; exp = l['expected']
        case = cases[seq]
        desc = case['description']
        if l.get('errored'):
            per[impl]['ERRORED'] += len(exp); per[impl]['errored_cases'] += 1
            continue
        if l.get('skipped'):
            per[impl]['SKIPPED'] += len(exp); continue
        for e, r in zip(exp, l['results']):
            if 'valid' in r:
                if r['valid'] == e:
                    per[impl]['agree'] += 1
                elif e is False:
                    per[impl]['FALSE_ACCEPT'] += 1; fa_by_desc[impl][desc] += 1
                else:
                    per[impl]['FALSE_REJECT'] += 1
            elif r.get('skipped'):
                per[impl]['SKIPPED'] += 1
            else:
                per[impl]['ERRORED'] += 1
    print('bowtie', header.get('bowtie_version'), 'dialect', header.get('dialect'), 'cases', len(cases),
          'tests', sum(len(c['tests']) for c in cases.values()))
    print(f"{'implementation':40s} {'version':28s} agree FALSE_ACCEPT FALSE_REJECT ERRORED SKIPPED errored_cases")
    for impl, c in sorted(per.items()):
        v = header['implementations'].get(impl, {}).get('version', '?')
        print(f"{impl:40s} {str(v):28s} {c['agree']:5d} {c['FALSE_ACCEPT']:12d} {c['FALSE_REJECT']:12d} {c['ERRORED']:7d} {c['SKIPPED']:7d} {c['errored_cases']:5d}")
    missing = set(header['implementations']) - set(per)
    if missing:
        print('implementations with no results:', sorted(missing))
    print('\nFALSE_ACCEPT by case description (top 6 per implementation):')
    for impl, d in sorted(fa_by_desc.items()):
        print(' ', impl, d.most_common(6))

if __name__ == '__main__':
    main(sys.argv[1])
