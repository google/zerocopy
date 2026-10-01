#!/usr/bin/env python3
import csv,hashlib,json,pathlib,collections,subprocess
p=pathlib.Path(__file__).resolve().parent.parent
root=p.parent.parent
s=p/'support';v83=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v83';v81=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v81';r350=root/'reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30'
m=json.loads((s/'validation-v84.json').read_text())
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
assert m['frozen_reference_parent']=='e9350ecdba2279577957dc7892bd0bded34dd039'
assert subprocess.run(['git','merge-base','--is-ancestor',m['frozen_reference_parent'],'HEAD'],cwd=root,capture_output=True).returncode==0
assert sha(s/'version-inventory-ebcdcad-581.csv')==sha(v83/'support/version-inventory-ebcdcad-581.csv')==sha(v81/'support/version-inventory-ebcdcad-581.csv')==m['inventory_sha256']
assert sha(s/'newer-version-crosswalk-v84.csv')==sha(v83/'support/newer-version-crosswalk-v83.csv')==m['crosswalk_sha256']==m['prior_v83_crosswalk_sha256']
inv=list(csv.DictReader((s/'version-inventory-ebcdcad-581.csv').open(newline='')))
rows=list(csv.DictReader((s/'newer-version-crosswalk-v84.csv').open(newline='')))
assert len(inv)==m['inventory_rows']==581 and len(rows)==m['newer_version_rows']==361 and len({r['cohort'] for r in rows})==m['cohort_count']==11
assert {r['inventory_id'] for r in rows}=={r['inventory_id'] for r in inv if r['classification']=='newer_version_recheck'}
assert dict(collections.Counter(r['coverage_status'] for r in rows))=={'exact_claim_source_review':323,'contextual_or_paired_component_only':38}
assert m['coverage_status_counts']=={'exact_claim_source_review':323,'contextual_or_paired_component_only':38,'unmapped':0}
by={r['inventory_id']:r for r in rows}
assert by['R350']['coverage_status']=='exact_claim_source_review' and by['R350']['execution_status']=='source_only_no_new_runtime_or_package_execution'
assert by['R443']['execution_status']=='static_architecture_only_no_execution'
assert next(r for r in inv if r['inventory_id']=='R578')['classification']=='no_newer_release'
for fn,digest in m['inherited_v81_sha256'].items():assert sha(s/fn)==sha(v83/'support'/fn)==sha(v81/'support'/fn)==digest
with (s/'source-package-inventory-v84.csv').open(newline='') as f:src=list(csv.DictReader(f))
assert len(src)==sum(1 for base in (v83,r350) for x in base.rglob('*') if x.is_file())
for row in src:
 file=root/row['path'];assert file.is_file() and sha(file)==row['sha256'] and file.stat().st_size==int(row['bytes'])
assert sha(s/'source-package-inventory-v84.csv')==m['source_package_inventory_sha256']
old={r['path']:r for r in csv.DictReader((v83/'support/source-package-inventory-v83.csv').open(newline='')) if r['path'].startswith('reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30/')}
new={r['path']:r for r in src if r['path'].startswith('reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30/')}
assert old.keys()==new.keys()
changed=sorted(path for path in old if old[path]['sha256']!=new[path]['sha256'])
assert changed==m['r350_current_source_changes_from_v83']==['reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30/support/check_source.py','reports/cargo-r350-coverage-to-rust-1981-source-review-2026-09-30/support/reproduce.md']
for path in changed:
 assert old[path]['sha256']==m['r350_historical_source_hashes'][path]
 assert new[path]['sha256']==m['r350_current_source_hashes'][path]
print('v84 package check: historical v83 crosswalk/inheritance intact; two current R350 support-file changes and 323/38/0 coverage verified')
