#!/usr/bin/env python3
"""Offline exact five-row corpus and recorded official source checker."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837';FROZEN='e0cfc848df5d3bac60afe93fae903ba51d3d72ac'
PINS={'llvm/llvm-project':('ded546ad82656ce6605ee2f2aa60c78dec70d95f','229b9b2f4e20840a8280174fa08385fd9e36844b','main',181,5),'golang/tools':('98444708d405557b5ddd6179be1a6abc14150d5f','134264d72fba423ca1ad358683cd3c32699b010e','master',5,7),'rust-lang/rust-analyzer':('03fcb77246f2568adb0e9b2fa60d19c6cc1686f4','03fcb77246f2568adb0e9b2fa60d19c6cc1686f4','master',0,1)}
IDS=['R383','R404','R513','R514','R515'];REPOS={'R383':'llvm/llvm-project','R404':'golang/tools','R513':'rust-lang/rust-analyzer','R514':'rust-lang/rust-analyzer','R515':'rust-lang/rust-analyzer'}
ROLES={'R383':['current_mapped','historical','derived','current_mapped_and_derived'],'R404':['current_mapped','historical','historical','derived','derived'],'R513':['historical','current_mapped','historical','derived'],'R514':['historical','current_mapped','historical','derived'],'R515':['historical','current_mapped','derived','historical_and_derived']}
SIDECARS={'R383':['evidence-map.json'],'R404':['evidence-map.json'],'R513':['source-map.json','judgment-matrix.json','timeline.json'],'R514':['evidence-map.json'],'R515':['evidence-ledger.json']}
def need(ok,why):
 if not ok:raise AssertionError(why)
def git(*a):return subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL)
def gb(p):return git('show',f'{FROZEN}:{p}')
def sha(b):return hashlib.sha256(b).hexdigest()
def paths(c):
 need(git('rev-parse',f'{c}^{{commit}}').decode().strip()==c,'exact corpus commit')
 return {p for p in git('ls-tree','-r','--name-only',c,'reports').decode().splitlines() if p.endswith('/REPORT.json')}
def run():
 d=json.loads((P/'matrix.json').read_text());need(d['schema']==1 and d['baseline_reference_commit']==BASE and d['frozen_reference_commit']==FROZEN,'corpus IDs')
 need((d['baseline_count'],d['current_count'])==(581,599),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash');inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory rows')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==599 and bp<=fp and len(d['added_after_baseline'])==18 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'18 additions')
 for z in d['added_after_baseline']:
  need(z['report_md']==z['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(z['report_json']))==z['json_sha256'] and sha(gb(z['report_md']))==z['md_sha256'],'addition hashes')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'official observation hash');e=json.loads(eb);by={z['repository']:z for z in e['repositories']};need(set(by)==set(PINS),'three repos')
 for repo,(old,new,branch,n,count) in PINS.items():
  z=by[repo];need((z['old_commit'],z['selected_current_commit'],z['branch'])==(old,new,branch),'exact source pair')
  raw={ref:sha for sha,ref in (line.split('\t') for line in z['raw_ls_remote'].splitlines())};need(raw==z['refs'] and raw['HEAD']==raw['refs/heads/'+branch],'official raw refs')
  if repo=='llvm/llvm-project':
   later=z['later_ref_commit_observation'];need(z['selected_main_ref_observation']==new and z['ref_advanced_during_collection'] is True and raw['HEAD']==later['commit']=='642daaf27dd0cda7127d35bad1a3fe705a267918' and later['parent']==new and later['changed_path_count']==96 and later['clangd_changed_paths']==[],'moving LLVM ref bounded')
  else:need(raw['HEAD']==new,'observed current ref')
  c=z['compare_observation'];need((c['status'],c['ahead_by'],c['behind_by'],c['total_commits'],c['returned_changed_file_count'])==('identical' if n==0 else 'ahead',n,0,n,0 if n==0 else 300 if repo=='llvm/llvm-project' else 17),'recorded compare range')
  need(c['changed_file_list_complete']==(repo!='llvm/llvm-project'),'compare cap boundary')
  need(len(z['mapped_files'])==count and len({a['path'] for a in z['mapped_files']})==count,'mapped path census')
  for a in z['mapped_files']:
   need(a['old']['sha1_git_blob']==a['new']['sha1_git_blob'] and a['old']['size']==a['new']['size'],'unchanged mapped blob')
   need(len(a['old']['sha256_content'])==64 and len(a['new']['sha256_content'])==64 and a['old']['sha256_content']==a['new']['sha256_content'],'commit-pinned raw source hashes')
   need(a['old']['url']==f'https://raw.githubusercontent.com/{repo}/{old}/{a["path"]}' and a['new']['url']==f'https://raw.githubusercontent.com/{repo}/{new}/{a["path"]}','commit-pinned URLs')
  if n:
   log=z['official_gitiles_range'];need(log['count']==n and len(log['commits'])==n and log['first_commit']==new and log['last_parent']==old and log['next'] is None,'Gitiles forward ancestry')
 llvm=by['llvm/llvm-project'];sub=llvm['official_gitiles_clangd_subtree'];need(len(sub['visited_trees'])==5,'bounded clangd tree traversal')
 changed={a['path'] for a in sub['changed_leaves']};need(changed=={'clang-tools-extra/clangd/refactor/tweaks/ExtractFunction.cpp','clang-tools-extra/clangd/unittests/FindTargetTests.cpp','clang-tools-extra/clangd/unittests/tweaks/ExtractFunctionTests.cpp'},'exact clangd subtree delta')
 need(not changed&{a['path'] for a in llvm['mapped_files']},'clangd mapped non-overlap')
 go=by['golang/tools'];diffs=go['official_gitiles_commit_diffs'];need(len(diffs)==5 and {a['commit'] for a in diffs}==set(go['official_gitiles_range']['commits']),'Go per-commit diffs')
 need(sum(len(a['tree_diff']) for a in diffs)==18,'Go per-commit diff count')
 gpaths={v.get('new_path') for a in diffs for v in a['tree_diff']}|{v.get('old_path') for a in diffs for v in a['tree_diff']};need(not gpaths&{a['path'] for a in go['mapped_files']},'Go mapped non-overlap')
 need([r['inventory_id'] for r in d['rows']]==IDS,'five separate rows');sel=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(len(sel)==5,'selector count')
 for row,s in zip(d['rows'],sel):
  id=row['inventory_id'];xs=[x for x in inv if x['inventory_id']==id];need(len(xs)==1,'one inventory row');x=xs[0]
  need(s=={'inventory_id':id,'cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']},'exact selector')
  need((row['cohort'],row['title'],row['report_json'],row['report_md'])==(x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row metadata')
  mb=gb(row['report_md']);jb=gb(row['report_json']);md=mb.decode();meta=json.loads(jb)
  need(sha(mb)==row['frozen_md_sha256'] and sha(jb)==row['frozen_json_sha256'] and row['frozen_subjects_exact']==meta['subjects']==json.loads(x['exact_pinned_subject_identities_json']),'frozen bytes/subjects')
  sp=[{'path':row['report_md'].replace('REPORT.md',p),'sha256':sha(gb(row['report_md'].replace('REPORT.md',p)))} for p in SIDECARS[id]];need(row['frozen_sidecars']==sp,'frozen evidence sidecars')
  lines=md.splitlines();i=lines.index('## Summary')+1
  while not lines[i].strip():i+=1
  j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();parts=summary.split('\n\n')
  need(row['claim_locator']=={'heading':'## Summary','line':i+1} and row['full_summary_exact']==summary and row['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'exact claim text')
  repo=REPOS[id];orig=by[repo];mapped=[{'path':z['path'],'old_blob_sha':z['old']['sha1_git_blob'],'new_blob_sha':z['new']['sha1_git_blob']} for z in orig['mapped_files']]
  need(row['source_repository']==repo and row['old_commit']==orig['old_commit'] and row['selected_current_commit']==orig['selected_current_commit'] and row['mapped_files']==mapped,'row source mapping')
  clauses=[{'number':n,'exact_excerpt':p,'scope_role':ROLES[id][n-1],'source_paths':[z['path'] for z in mapped] if 'current_mapped' in ROLES[id][n-1] else [],'source_result':'mapped_blobs_unchanged_no_behavior_conclusion' if 'current_mapped' in ROLES[id][n-1] else 'not_a_new_current_source_claim','runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(parts,1)]
  need(row['clauses']==clauses,'claim clauses/roles')
  need(row['source_result']=='claim_mapped_source_blobs_unchanged_broader_behavior_unresolved' and row['runtime_result']=='unexecuted_in_this_review' and row['anneal_product_result']=='unassessed','result bounds')
  if id=='R383':
   em=json.loads(gb(sp[0]['path']));claims={v['id']:v for v in em['claims']};need(all(i in claims for i in ['C01','C02','C03','C04','C05']),'clangd exact claim IDs')
   for cid,locpaths in {'C01':['TUScheduler.h'],'C02':['ClangdServer.cpp','TUScheduler.h'],'C03':['GlobalCompilationDatabase.h'],'C04':['TUScheduler.h'],'C05':['FileIndex.cpp','Background.cpp']}.items():need(all(p in claims[cid]['locator'] for p in locpaths),'clangd claim locator')
  if id=='R404':
   em=json.loads(gb(sp[0]['path']));source=next(v for v in em['entries'] if v['id']=='G-CURRENT');need(source['identity']['revision']==orig['old_commit'] and source['paths']=={v['path']:v['old_blob_sha'] for v in mapped},'gopls exact source map')
  if id=='R515':
   em=json.loads(gb(sp[0]['path']));need(any(v.get('repository')==repo and v.get('blob')==mapped[0]['old_blob_sha'] for v in em['sources']),'RA ledger blob')
 need(d['full_source_archive_sha256'] is None,'no full source archive')
 print('OK: five exact frozen editor rows, 581/599 corpus and 18 additions; LLVM 181/3 clangd leaves, Go 5/18 diffs, RA same pin; mapped blobs unchanged; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
