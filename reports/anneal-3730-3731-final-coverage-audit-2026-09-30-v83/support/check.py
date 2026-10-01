#!/usr/bin/env python3
import csv,hashlib,json,pathlib,collections
p=pathlib.Path(__file__).resolve().parent.parent
root=p.parent.parent
s=p/'support';prev=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v82';v81=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v81';r350=root/'reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30'
m=json.loads((s/'validation-v83.json').read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert m['frozen_reference_parent']=='1e87e9bf7b672c354b4c2903a372329ee61faf63'
assert sha(s/'version-inventory-ebcdcad-581.csv')==sha(v81/'support/version-inventory-ebcdcad-581.csv')==m['inventory_sha256']
inv=list(csv.DictReader((s/'version-inventory-ebcdcad-581.csv').open(newline='')))
rows=list(csv.DictReader((s/'newer-version-crosswalk-v83.csv').open(newline='')))
old=list(csv.DictReader((prev/'support/newer-version-crosswalk-v82.csv').open(newline='')))
assert len(inv)==m['inventory_rows']==581 and len(rows)==len(old)==m['newer_version_rows']==361
assert len({r['cohort'] for r in rows})==m['cohort_count']==11
assert {r['inventory_id'] for r in rows}=={r['inventory_id'] for r in inv if r['classification']=='newer_version_recheck'}
assert len({r['inventory_id'] for r in rows})==361
assert dict(collections.Counter(r['coverage_status'] for r in rows))=={'exact_claim_source_review':323,'contextual_or_paired_component_only':38}
assert m['coverage_status_counts']=={'exact_claim_source_review':323,'contextual_or_paired_component_only':38,'unmapped':0}
assert sha(s/'newer-version-crosswalk-v83.csv')==m['crosswalk_sha256']
old_by={r['inventory_id']:r for r in old};new_by={r['inventory_id']:r for r in rows}
claim=json.loads((root/m['r350_claim_matrix']).read_text())
assert sha(root/m['r350_claim_matrix'])==m['r350_claim_matrix_sha256']
assert claim['inventory_id']=='R350' and claim['predecessor_report_md']==new_by['R350']['original_report_md'] and claim['predecessor_report_json']==new_by['R350']['original_report_json']
assert claim['runtime_status']=='unexecuted_in_this_review' and claim['charon_aeneas_anneal_status']=='unassessed_in_this_review'
for rid,row in new_by.items():
 orig=old_by[rid]
 if rid=='R350':
  assert orig['coverage_status']=='contextual_or_paired_component_only' and row['coverage_status']=='exact_claim_source_review'
  assert row['exact_source_review']==m['r350_claim_matrix'] and row['source_matrices']==orig['source_matrices']+';'+m['r350_claim_matrix']
  assert row['execution_status']=='source_only_no_new_runtime_or_package_execution'
  assert all(row[k]==orig[k] for k in row if k not in {'coverage_status','source_matrices','source_relations','exact_source_review','execution_status'})
 else:assert row==orig
assert new_by['R443']['execution_status']=='static_architecture_only_no_execution'
assert next(r for r in inv if r['inventory_id']=='R578')['classification']=='no_newer_release'
for fn,digest in m['inherited_v81_sha256'].items():assert sha(s/fn)==sha(v81/'support'/fn)==digest
with (s/'source-package-inventory-v83.csv').open(newline='') as f:src=list(csv.DictReader(f))
assert len(src)==sum(1 for base in (prev,r350) for x in base.rglob('*') if x.is_file())
for row in src:
 file=root/row['path'];assert file.is_file() and sha(file)==row['sha256'] and file.stat().st_size==int(row['bytes'])
assert sha(s/'source-package-inventory-v83.csv')==m['source_package_inventory_sha256']
print('v83 package check: 361 rows, 323 exact / 38 contextual / 0 unmapped, inherited bytes and local source packages verified')
