#!/usr/bin/env python3
import csv,hashlib,json,pathlib,collections
p=pathlib.Path(__file__).resolve().parent.parent
root=p.parent.parent
s=p/'support'
m=json.loads((s/'validation-v81.json').read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert m['frozen_reference_parent']=='d16440e5a6e12e004a3849938cc75202da82bb6f'
assert sha(s/'version-inventory-ebcdcad-581.csv')==m['inventory_sha256']
inv=list(csv.DictReader((s/'version-inventory-ebcdcad-581.csv').open(newline='')))
rows=list(csv.DictReader((s/'newer-version-crosswalk-v81.csv').open(newline='')))
assert len(inv)==m['inventory_rows']==581
assert len(rows)==m['newer_version_rows']==361
assert {r['inventory_id'] for r in rows}=={r['inventory_id'] for r in inv if r['classification']=='newer_version_recheck'}
assert len({r['inventory_id'] for r in rows})==361
assert dict(collections.Counter(r['coverage_status'] for r in rows))==m['coverage_status_counts']
assert sha(s/'newer-version-crosswalk-v81.csv')==m['crosswalk_sha256']
assert [r['inventory_id'] for r in rows if r['coverage_status']=='unmapped']==['R348','R349','R352']
assert next(r for r in rows if r['inventory_id']=='R350')['coverage_status']=='contextual_or_paired_component_only'
assert next(r for r in inv if r['inventory_id']=='R578')['classification']=='no_newer_release'
for fn,digest in m['inherited_v80_sha256'].items():
 assert sha(s/fn)==digest
 assert sha(root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v80/support'/fn)==digest
for r in rows:
 original=next(x for x in inv if x['inventory_id']==r['inventory_id'])
 assert r['original_report_md']==original['report_md_at_commit']
 assert r['original_report_json']==original['report_json_at_commit']
 paths=r['source_matrices'].split(';') if r['source_matrices'] else []
 if r['inventory_id']=='R443':
  assert paths==['reports/lean-430rc2-to-4341-linux-aarch64-leantar-static-recheck/support/frozen-inventory-row.json']
 else:
  for path in paths:
   assert path in m['matrix_paths'].values()
   assert r['inventory_id'] in {x['inventory_id'] for x in csv.DictReader((root/path).open(newline=''))}
print('v81 package check: 581 inventory rows, 361 classified rows, inherited v80 bytes and source paths verified')
