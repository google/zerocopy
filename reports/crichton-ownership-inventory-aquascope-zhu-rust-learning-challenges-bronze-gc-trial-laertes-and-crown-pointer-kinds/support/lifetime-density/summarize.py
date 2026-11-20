#!/usr/bin/env python3
"""Summarize lifetime-density raw output into a TSV table and a human-readable table."""
import re, sys
src = sys.argv[1]; tsv = sys.argv[2]
rows = []
for line in open(src):
    label, rest = line.rstrip('\n').split('\t')
    d = {k: int(v) for k, v in re.findall(r'(\w+): (\d+)', rest)}
    d['label'] = label; rows.append(d)
keys = ['files','parse_failures','nonblank_lines','sigs','sigs_lifetime_relevant','sigs_write_named','sigs_fn_lifetime_params','sigs_write_anon','sigs_write_static','sigs_output_lifetime','sigs_output_elided_only','sigs_output_named','sigs_elision_rule3','sigs_elision_rule2','sigs_must_annotate','sigs_must_annotate_written_named','sigs_elidable_but_named_output','ref_positions','refs_elided','refs_named','refs_static','refs_anon','adts','adts_with_lifetime_params','impls','impls_with_lifetime_params','traits','traits_with_lifetime_params']
tot = {k: sum(r[k] for r in rows) for k in keys}; tot['label'] = 'TOTAL'
with open(tsv, 'w') as out:
    out.write('crate\t' + '\t'.join(keys) + '\n')
    for r in rows + [tot]:
        out.write(r['label'] + '\t' + '\t'.join(str(r[k]) for k in keys) + '\n')
print('| crate | non-blank lines | fn signatures | write a named lifetime | declare fn lifetime params | output carries a lifetime | must annotate (E0106 if stripped) | of which write a named output lifetime | elided share of ref positions | ADTs with lifetime params | impls with lifetime params |')
print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
for r in rows + [tot]:
    s = r['sigs']
    pct = lambda a, b: f"{100*a/b:.1f}%" if b else "n/a"
    print(f"| {r['label']} | {r['nonblank_lines']} | {s} | {r['sigs_write_named']} ({pct(r['sigs_write_named'], s)}) | {r['sigs_fn_lifetime_params']} ({pct(r['sigs_fn_lifetime_params'], s)}) | {r['sigs_output_lifetime']} ({pct(r['sigs_output_lifetime'], s)}) | {r['sigs_must_annotate']} ({pct(r['sigs_must_annotate'], s)}) | {r['sigs_must_annotate_written_named']} | {pct(r['refs_elided'], r['ref_positions'])} | {r['adts_with_lifetime_params']}/{r['adts']} | {r['impls_with_lifetime_params']}/{r['impls']} |")
