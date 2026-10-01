#!/usr/bin/env python3
"""Verify the inherited reference packages and this dated coverage delta."""
import collections
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess

PACKAGE = Path(__file__).resolve().parent.parent
SUPPORT = PACKAGE / 'support'

def find_reference_root():
    for parent in Path(__file__).resolve().parents:
        if (parent / 'tools' / 'reference.py').is_file():
            return parent
    configured = os.environ.get('ZEROCOPY_REFERENCE_ROOT')
    if configured and (Path(configured) / 'tools' / 'reference.py').is_file():
        return Path(configured).resolve()
    raise RuntimeError('run from a reference checkout or set ZEROCOPY_REFERENCE_ROOT')

ROOT = find_reference_root()
REPORTS = ROOT / 'reports'
M = json.loads((SUPPORT / 'validation-v85.json').read_text())

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

for commit in M['required_ancestors']:
    assert subprocess.run(['git','merge-base','--is-ancestor',commit,'HEAD'],cwd=ROOT,capture_output=True).returncode==0
assert M['reference_head']==M['required_ancestors'][-1]=='f6287f7169c5185623c32c3f6922aa40f59644a0'
v84 = REPORTS / M['inherited_from'] / 'support'
v85 = REPORTS / M['newer_crosswalk_from'] / 'support'
source_for = {
    '3730-crosswalk-final-v80.csv': v84/'3730-crosswalk-final-v80.csv',
    'investigation-final-v80.csv': v84/'investigation-final-v80.csv',
    'live-issue-snapshot-v80.json': v84/'live-issue-snapshot-v80.json',
    'row-challenge-v80.json': v84/'row-challenge-v80.json',
    'version-inventory-ebcdcad-581.csv': v84/'version-inventory-ebcdcad-581.csv',
    'newer-version-crosswalk-v85.csv': v85/'newer-version-crosswalk-v85.csv',
    'claim-applicability-matrix-v85.csv': v85/'claim-applicability-matrix-v85.csv',
}
for name, source in source_for.items():
    assert sha(source)==M['preserved_file_sha256'][name]
assert sha(SUPPORT/'live-issue-observation-2026-10-01.json')==M['live_issue_observation_sha256']
assert M['preserved_file_sha256']['live-issue-observation-2026-10-01.json']==M['live_issue_observation_sha256']
live=json.loads((SUPPORT/'live-issue-observation-2026-10-01.json').read_text())
assert live['observed_at']=='2026-10-01'
assert [(x['number'],x['status']) for x in live['issues']]==[(3731,'Open'),(3730,'Closed as not planned')]
assert '159 investigations' in live['issues'][0]['visible_body_excerpt']
assert 'I145–I159' in live['issues'][0]['visible_body_excerpt'] and '174-entry crosswalk' in live['issues'][0]['visible_body_excerpt']

issues=list(csv.DictReader(source_for['investigation-final-v80.csv'].open()))
suggestions=list(csv.DictReader(source_for['3730-crosswalk-final-v80.csv'].open()))
challenge=json.loads(source_for['row-challenge-v80.json'].read_text())
inventory=list(csv.DictReader(source_for['version-inventory-ebcdcad-581.csv'].open()))
cross=list(csv.DictReader(source_for['newer-version-crosswalk-v85.csv'].open()))
claims=list(csv.DictReader(source_for['claim-applicability-matrix-v85.csv'].open()))
assert (len(issues),len(suggestions),len(challenge),len(inventory),len(cross),len(claims))==(159,174,333,581,361,38)
assert len({r['id'] for r in issues})==159
assert len({r['inventory_id'] for r in inventory})==581
assert len({r['inventory_id'] for r in cross})==361
assert {r['inventory_id'] for r in cross}=={r['inventory_id'] for r in inventory if r['classification']=='newer_version_recheck'}
assert dict(collections.Counter(r['coverage_status'] for r in cross))=={'exact_claim_source_review':356,'contextual_or_paired_component_only':5}
assert {r['inventory_id'] for r in cross if r['coverage_status']=='contextual_or_paired_component_only'}=={'R120','R121','R139','R150','R236'}
assert M['counts']=={'investigations':159,'suggestions':174,'suggestion_links':345,'challenge_rows':333,
                     'version_inventory':581,'newer_version_rows':361,
                     'newer_version_source_status':{'exact_claim_source_review':356,'contextual_or_paired_component_only':5},
                     'source_revision_rows':72,'prior_comparison_rows':11,
                     'source_83_relations':{'changed':21,'unchanged':55,'unavailable':7}}
assert sum(r['classification']=='source_revision_recheck' for r in inventory)==72
assert sum(r['classification']=='prior_comparison' for r in inventory)==11

packages=set(M['package_names'])
rows=list(csv.DictReader((SUPPORT/'source-package-inventory-v85.csv').open()))
assert len(rows)==M['package_inventory_rows']==150
assert len({r['path'] for r in rows})==len(rows)
for row in rows:
    path=Path(row['path'])
    assert len(path.parts)>=3 and path.parts[0]=='reports' and path.parts[1] in packages
    file=ROOT/path
    assert file.is_file() and sha(file)==row['sha256'] and file.stat().st_size==int(row['bytes'])
assert sha(SUPPORT/'source-package-inventory-v85.csv')==M['package_inventory_sha256']

r121=REPORTS/'anneal-3731-r121-rust-version-runtime-2026-09-30'
s83=REPORTS/'anneal-3731-version-source-audit-83-2026-10-01'
assert sha(r121/'REPORT.md')==M['r121_report_sha256']
assert sha(s83/'REPORT.md')==M['source_83_report_sha256']
assert sha(s83/'status-83.csv')==M['source_83_status_sha256']
srows=list(csv.DictReader((s83/'status-83.csv').open()))
assert len(srows)==83 and {r['inventory_id'] for r in srows}=={r['inventory_id'] for r in inventory if r['classification'] in ('source_revision_recheck','prior_comparison')}
assert dict(collections.Counter(r['source_relation_at_mapped_scope'] for r in srows))=={'changed':21,'unchanged':55,'unavailable':7}
assert all(r['target_runtime']=='unexecuted_in_this_audit' and r['anneal_product']=='unassessed_in_this_audit' for r in srows)
evidence=json.loads((r121/'evidence.json').read_text())
assert set(evidence['compilers'])=={'nightly_2026_05_31','stable_1_98_1','nightly_2026_09_17'}
assert all(c['runs']['baseline']['exit']==0 and c['runs']['rust_incomplete']['exit']==1 for c in evidence['compilers'].values())
assert len({c['runs']['rust_incomplete']['stderr'] for c in evidence['compilers'].values()})==1
assert evidence['fixtures']['baseline']['projection_sha256']==evidence['fixtures']['rust_incomplete']['projection_sha256']
print('PASS: 159/174/345/333 inherited counts and hashes; 581 inventory; 356/5/0 newer source crosswalk; 72+11 source audit; R121 fixture; live issue excerpt')
