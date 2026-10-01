#!/usr/bin/env python3
import csv,hashlib,json,pathlib,collections
p=pathlib.Path(__file__).resolve().parent.parent
root=p.parent.parent
s=p/'support';prev=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v81'
m=json.loads((s/'validation-v82.json').read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert m['frozen_reference_parent']=='1e87e9bf7b672c354b4c2903a372329ee61faf63'
assert sha(s/'version-inventory-ebcdcad-581.csv')==m['inventory_sha256']
inv=list(csv.DictReader((s/'version-inventory-ebcdcad-581.csv').open(newline='')))
rows=list(csv.DictReader((s/'newer-version-crosswalk-v82.csv').open(newline='')))
old=list(csv.DictReader((prev/'support/newer-version-crosswalk-v81.csv').open(newline='')))
assert len(inv)==m['inventory_rows']==581 and len(rows)==len(old)==m['newer_version_rows']==361
assert len({r['cohort'] for r in rows})==m['cohort_count']==11
assert {r['inventory_id'] for r in rows}=={r['inventory_id'] for r in inv if r['classification']=='newer_version_recheck'}
assert len({r['inventory_id'] for r in rows})==361
assert dict(collections.Counter(r['coverage_status'] for r in rows))=={'exact_claim_source_review':322,'contextual_or_paired_component_only':39}
assert m['coverage_status_counts']=={'exact_claim_source_review':322,'contextual_or_paired_component_only':39,'unmapped':0}
assert sha(s/'newer-version-crosswalk-v82.csv')==m['crosswalk_sha256']
old_by={r['inventory_id']:r for r in old};new_by={r['inventory_id']:r for r in rows}
assert set(m['new_cargo_ids'])=={'R348','R349','R352'}
selected={r['inventory_id']:r for r in csv.DictReader((root/m['cargo_matrix']).open(newline=''))}
assert set(selected)==set(m['new_cargo_ids'])
for rid,row in new_by.items():
 orig=old_by[rid]
 if rid in selected:
  assert orig['coverage_status']=='unmapped' and row['coverage_status']=='exact_claim_source_review'
  assert row['source_matrices']==row['exact_source_review']==m['cargo_matrix']
  assert row['original_report_md']==selected[rid]['report_md']
  assert row['original_report_json']==selected[rid]['report_json']
  assert all(row[k]==orig[k] for k in row if k not in {'coverage_status','source_matrices','source_relations','exact_source_review','execution_status'})
 else:assert row==orig
assert new_by['R350']['coverage_status']=='contextual_or_paired_component_only'
assert new_by['R443']['execution_status']=='static_architecture_only_no_execution'
assert next(r for r in inv if r['inventory_id']=='R578')['classification']=='no_newer_release'
for fn,digest in m['inherited_v81_sha256'].items():
 assert sha(s/fn)==sha(prev/'support'/fn)==digest
with (s/'source-package-inventory-v82.csv').open(newline='') as f:src=list(csv.DictReader(f))
assert len(src)==sum(1 for base in (prev,root/'reports/cargo-r348-r349-r352-to-rust-1981-source-review-2026-09-30') for x in base.rglob('*') if x.is_file())
for row in src:
 file=root/row['path'];assert file.is_file() and sha(file)==row['sha256'] and file.stat().st_size==int(row['bytes'])
assert sha(s/'source-package-inventory-v82.csv')==m['source_package_inventory_sha256']
print('v82 package check: 361 rows, 322 exact / 39 contextual / 0 unmapped, inherited bytes and source packages verified')
