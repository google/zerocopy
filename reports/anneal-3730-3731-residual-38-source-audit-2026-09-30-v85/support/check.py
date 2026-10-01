#!/usr/bin/env python3
"""Offline integrity and exact-claim checker for the v85 source-only audit."""
import collections,csv,hashlib,json,pathlib,re,subprocess,tomllib
pkg=pathlib.Path(__file__).resolve().parent.parent
root=pkg.parent.parent
s=pkg/'support'
prev=root/'reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v84'
m=json.loads((s/'validation-v85.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
blob=lambda d:hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
def opening_paragraph(markdown, locator):
 lines=markdown.splitlines()
 if locator=='## Summary first paragraph':
  start=next(i+1 for i,line in enumerate(lines) if line.strip()=='## Summary')
 elif locator=='opening paragraph after H1':
  start=next(i+1 for i,line in enumerate(lines) if line.startswith('# '))
 else:
  raise AssertionError(f'unknown claim locator: {locator}')
 while start<len(lines) and (not lines[start].strip() or lines[start].startswith('#')):
  start+=1
 assert start<len(lines) and not lines[start].startswith(('-', '*', '|', '>'))
 end=start
 while end<len(lines) and lines[end].strip():
  end+=1
 return '\n'.join(lines[start:end])
def normalized_claim(paragraph):
 paragraph=re.sub(r'\[([^\]]+)\]\([^)]*\)',r'\1',paragraph)
 return ' '.join(paragraph.split())
assert m['frozen_reference_parent']=='6fe9f8ed36f1bfb474afe091a9799ee29016f667'
assert subprocess.run(['git','merge-base','--is-ancestor',m['frozen_reference_parent'],'HEAD'],cwd=root,capture_output=True).returncode==0
for fn,digest in m['inherited_sha256'].items():assert sha(s/fn)==sha(prev/'support'/fn)==digest
assert sha(s/'version-inventory-ebcdcad-581.csv')==m['frozen_inventory_sha256']
for fn,key in [('newer-version-crosswalk-v85.csv','crosswalk_sha256'),('claim-applicability-matrix-v85.csv','claim_matrix_sha256'),('source-pairs-v85.csv','source_pairs_sha256'),('version-pairs-v85.json','version_pairs_sha256')]:assert sha(s/fn)==m[key]
for fn,digest in m['pin_evidence_sha256'].items():assert sha(s/'pin-evidence'/fn)==digest
ids=json.loads((s/'version-pairs-v85.json').read_text())
assert ids['frozen_reference_parent']==m['frozen_reference_parent']
assert ids['paired_charon_old_new']==['a535e914f74db4fd9e6be7048f4233270d8945c0','e435e5f341863a49a7e85d2fee9988bc0c687c82']
assert ids['aeneas_old_new']==['ac9f1bc5262a5e4ff1e24ca78617121382202727','0855ce1b8ed3958512b6c19de6bf3035b7acb552']
assert ids['lean_old_new']==['3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc','68218e876d2a38b1985b8590fff244a83c321783']
channel=s/'pin-evidence/channel-rust-nightly-2026-09-17.toml'
assert sha(channel)==ids['rust_new_channel_manifest_sha256']
assert tomllib.loads(channel.read_text())['pkg']['rust']['git_commit_hash']==ids['paired_rust_new_source_revision']
link=s/'pin-evidence/rust-2026-09-17-cargo-gitlink.json'
assert sha(link)==ids['rust_new_cargo_gitlink_response_sha256']
assert json.loads(link.read_text())['sha']==ids['rust_new_cargo_gitlink']
pairs={r['pair_id']:r for r in csv.DictReader((s/'source-pairs-v85.csv').open(newline=''))}
assert len(pairs)==m['source_pair_count']==50
for key,row in pairs.items():
 assert row['old_url']==f"https://raw.githubusercontent.com/{row['repository']}/{row['old_revision']}/{row['old_path']}"
 old=pkg/row['old_snapshot'];assert old.is_file();olddata=old.read_bytes()
 assert (sha(old),blob(olddata),len(olddata))==(row['old_sha256'],row['old_git_blob_sha1'],int(row['old_bytes']))
 if row['new_path']:
  assert row['new_url']==f"https://raw.githubusercontent.com/{row['repository']}/{row['new_revision']}/{row['new_path']}"
  new=pkg/row['new_snapshot'];assert new.is_file();newdata=new.read_bytes()
  assert (sha(new),blob(newdata),len(newdata))==(row['new_sha256'],row['new_git_blob_sha1'],int(row['new_bytes']))
  expected='direct_sources_unchanged' if olddata==newdata else 'direct_source_diff_found' if row['old_path']==row['new_path'] else 'relocated_source_diff_found'
  assert row['path_status']==expected
 else:
  assert row['path_status']=='removed_or_reorganized_without_one_to_one_path' and not row['new_snapshot']
claim=list(csv.DictReader((s/'claim-applicability-matrix-v85.csv').open(newline='')))
assert len(claim)==m['residual_row_count']==38
assert len({r['inventory_id'] for r in claim})==38
assert dict(collections.Counter(r['source_classification'] for r in claim))==m['source_classification_counts']=={'direct source-diff found':33,'direct sources unchanged':1,'component not claim-relevant':4}
oldcross=list(csv.DictReader((prev/'support/newer-version-crosswalk-v84.csv').open(newline='')))
newcross=list(csv.DictReader((s/'newer-version-crosswalk-v85.csv').open(newline='')))
assert len(oldcross)==len(newcross)==361
oldby={r['inventory_id']:r for r in oldcross};newby={r['inventory_id']:r for r in newcross};claimby={r['inventory_id']:r for r in claim}
assert {r['inventory_id'] for r in oldcross if r['coverage_status']=='contextual_or_paired_component_only'}==set(claimby)
assert {r['inventory_id'] for r in newcross if r['coverage_status']=='contextual_or_paired_component_only'}=={'R120','R121','R139','R150','R236'}
assert dict(collections.Counter(r['coverage_status'] for r in newcross))==m['coverage_status_counts']=={'exact_claim_source_review':356,'contextual_or_paired_component_only':5}
assert {r['inventory_id'] for r in claim if r['source_classification']=='direct source-diff found'}.issubset({r['inventory_id'] for r in newcross if r['coverage_status']=='exact_claim_source_review'})
assert {'R142','R356','R358','R362','R365','R370','R371','R375','R376','R378','R379','R380','R382','R387','R388'}.issubset({r['inventory_id'] for r in claim if r['source_classification']=='direct source-diff found'})
for rid,row in newby.items():
 prior=oldby[rid]
 if rid not in claimby or claimby[rid]['v85_crosswalk_status']=='contextual_or_paired_component_only':assert row==prior
 else:
  assert prior['coverage_status']=='contextual_or_paired_component_only' and row['coverage_status']=='exact_claim_source_review'
  assert row['exact_source_review']=='reports/'+pkg.name+'/support/claim-applicability-matrix-v85.csv'
  assert all(row[k]==prior[k] for k in row if k not in {'coverage_status','source_matrices','source_relations','exact_source_review','execution_status'})
for row in claim:
 rid=row['inventory_id'];assert row['runtime_status']=='target_version_runtime_unexecuted'
 assert row['v85_crosswalk_status']==newby[rid]['coverage_status']
 assert row['original_report_md']==oldby[rid]['original_report_md']
 assert row['original_report_json']==oldby[rid]['original_report_json']
 data=subprocess.check_output(['git','show',ids['inventory_reference_commit']+':'+row['original_report_md']],cwd=root)
 metadata=subprocess.check_output(['git','show',ids['inventory_reference_commit']+':'+row['original_report_json']],cwd=root)
 assert hashlib.sha256(data).hexdigest()==row['frozen_report_md_sha256']
 assert hashlib.sha256(metadata).hexdigest()==row['frozen_report_json_sha256']
 actual=opening_paragraph(data.decode(),row['frozen_excerpt_locator'])
 assert normalized_claim(row['frozen_claim_verbatim'])==normalized_claim(actual),rid
 for key in row['source_pair_ids'].split(';') if row['source_pair_ids'] else []:assert key in pairs
assert next(r for r in csv.DictReader((s/'version-inventory-ebcdcad-581.csv').open(newline='')) if r['inventory_id']=='R578')['classification']=='no_newer_release'
assert newby['R443']['execution_status']=='static_architecture_only_no_execution'
print('v85 package check: 38 frozen claims, 50 source pairs, 33 direct diffs, 1 unchanged, 4 irrelevant; crosswalk 356/5/0 and inherited bytes verified')
