#!/usr/bin/env python3
"""Offline R516 frozen-corpus and recorded official source-range checker."""
import csv,hashlib,json,re,subprocess,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='aff25887303a095aeb6f4344af8f601fb42c9cca'
OLD='7ec1fa8b6d8a43c88bca0dbb376090d219ebc43b'
MAIN='36d26c5466e4d25940657ccb8d5b9557ccaf7be1'
STABLE='35d9211b841e7613c1d2f8f5af6d628ace696c4c'
def need(ok,why):
 if not ok:raise AssertionError(why)
def git(*a):return subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL)
def gb(p):return git('show',f'{FROZEN}:{p}')
def paths(c):
 need(git('rev-parse',f'{c}^{{commit}}').decode().strip()==c,'exact commit')
 return {p for p in git('ls-tree','-r','--name-only',c,'reports').decode().splitlines() if p.endswith('/REPORT.json')}
def main():
 d=json.loads((BASE/'matrix.json').read_text())
 need(d['schema']==1 and d['baseline_reference_commit']==BASELINE and d['frozen_reference_commit']==FROZEN,'corpus identity')
 need(d['baseline_count']==581 and d['current_count']==591,'corpus counts')
 ib=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes();need(hashlib.sha256(ib).hexdigest()==d['baseline_inventory_sha256'],'inventory hash')
 inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
 bp=set((BASE/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASELINE)=={x['report_json_at_commit'] for x in inv},'baseline paths')
 need(len(fp)==591 and bp<=fp and len(d['added_after_baseline'])==10 and {x['report_json'] for x in d['added_after_baseline']}==fp-bp,'ten additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md'),'addition pair')
  need(hashlib.sha256(gb(a['report_json'])).hexdigest()==a['json_sha256'] and hashlib.sha256(gb(a['report_md'])).hexdigest()==a['md_sha256'],'addition hash')
 x=next(z for z in inv if z['inventory_id']=='R516');need(sum(z['inventory_id']=='R516' for z in inv)==1,'one selector')
 s=list(csv.DictReader((BASE/'frozen-cohort.csv').open()));need(len(s)==1 and s[0]=={'inventory_id':'R516','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']},'selector paths')
 need(d['inventory_id']=='R516' and d['cohort']==x['cohort'] and d['title']==x['title'] and d['report_md']==x['report_md_at_commit'] and d['report_json']==x['report_json_at_commit'],'row identity')
 mb=gb(d['report_md']);jb=gb(d['report_json']);md=mb.decode();meta=json.loads(jb)
 need(hashlib.sha256(mb).hexdigest()==d['frozen_md_sha256'] and hashlib.sha256(jb).hexdigest()==d['frozen_json_sha256'],'report hashes')
 need(meta['subjects']==d['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'original subjects')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 start=i;j=lines.index('## Applicability');summary='\n'.join(lines[start:j]).rstrip();first=summary.split('\n\n')[0]
 need(d['claim_locator']=={'heading':'## Summary','line':start+1} and d['full_summary_exact']==summary and d['first_claim_paragraph_exact']==first and md.count(summary)==1,'exact claims')
 need(d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory excerpt')
 need(d['old_source_blob_sha1_mentions']==sorted(set(re.findall(r'\bblob `([0-9a-f]{40})`',md))),'blob mentions')
 need(d['old_source_commit']==OLD and d['current_main_commit']==MAIN,'main pins')
 need(d['stable_workspaces_package']=={'package':'Microsoft.CodeAnalysis.Workspaces.Common','version':'5.9.0','source_commit':STABLE,'source_relation_to_old':'diverged_from_old_main_line'},'stable pin')
 cb=(BASE/'official-main-compare.json').read_bytes();need(hashlib.sha256(cb).hexdigest()==d['current_main_compare_sha256'],'main compare hash')
 c=json.loads(cb);need(c['base_commit']==OLD and c['head_commit']==MAIN and c['status']=='ahead' and c['ahead_by']==c['total_commits']==len(c['commit_ids'])==7 and c['behind_by']==0,'main ancestry')
 need(len(c['changed_files'])<300 and len(c['changed_files'])>0,'complete-bounded changed-file list')
 sb=(BASE/'official-stable-compare.json').read_bytes();need(hashlib.sha256(sb).hexdigest()==d['stable_compare_sha256'],'stable compare hash')
 sc=json.loads(sb);need(sc['base_commit']==STABLE and sc['head_commit']==OLD and sc['status']=='diverged' and sc['ahead_by']>0 and sc['behind_by']>0,'stable divergence')
 changed={z['path'] for z in c['changed_files']}|{z['previous_filename'] for z in c['changed_files'] if z['previous_filename']}
 need({z['id'] for z in d['clauses']}=={'semantic_snapshot','sharing_lazy_caches','mutable_workspace','remote_identity_lifetime','build_workspace_mismatch','host_services_persistence'},'claim clauses')
 for z in d['clauses']:
  need(z['mapped_paths'] and not changed.intersection(z['mapped_paths']),'mapped paths unchanged')
  need(z['old_urls']==[f'https://github.com/dotnet/roslyn/blob/{OLD}/{p}' for p in z['mapped_paths']] and z['current_main_urls']==[f'https://github.com/dotnet/roslyn/blob/{MAIN}/{p}' for p in z['mapped_paths']],'commit-pinned links')
  need(z['source_result']=='unchanged_git_tree_paths_in_verified_ancestor_range' and z['runtime_result']=='unexecuted_in_this_review','clause scopes')
 need(d['source_result']=='no_observable_drift_in_mapped_paths_on_main' and d['current_runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed','separate conclusions')
 need(d['old_source_snapshot_sha256'] is None and d['new_source_snapshot_sha256'] is None,'no raw source snapshots')
 print('OK: exact frozen R516 summary/subjects; 581/591 corpus; 10 additions; 7-commit main range; 6 clauses/13 unchanged mapped paths; runtime unexecuted')
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL:',e,file=sys.stderr);raise
