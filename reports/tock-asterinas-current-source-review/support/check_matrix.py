#!/usr/bin/env python3
"""Offline three-row frozen-corpus and recorded official-source checker."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='327cce209828e92daba9e2be8a3f93232e35810c'
T0='78862168a64a4f9ce61c9c17370272770c4a7cbb';T1='eaae5cbf62df2bc24ee809ff9d2c7ca124e42e73';TN='842498efca186bba0071ed3d072fddd2dec3312e';A='a5238eb6a965a4616ce07a48f5dfbc8042c4cd44'
PINS={'R571':T0,'R572':T1,'R573':T0}
def need(ok,why):
 if not ok:raise AssertionError(why)
def git(*a):return subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL)
def gb(p):return git('show',f'{FROZEN}:{p}')
def sha(b):return hashlib.sha256(b).hexdigest()
def paths(c):
 need(git('rev-parse',f'{c}^{{commit}}').decode().strip()==c,'exact corpus commit')
 return {p for p in git('ls-tree','-r','--name-only',c,'reports').decode().splitlines() if p.endswith('/REPORT.json')}
def mapped_sources(id,sm):
 out=[]
 if id=='R571':
  for k,repo in [('tock_source','tock/tock'),('asterinas_source','asterinas/asterinas')]:
   for p,b in sm['subjects'][k]['files'].items():out.append((repo,sm['subjects'][k]['revision'],p,b))
 elif id=='R572':
  for z in sm['sources']:
   if z.get('repository') in ('tock/tock','asterinas/asterinas'):
    for p in z['paths']:out.append((z['repository'],z['revision'],p['path'],p['blob']))
 else:
  for z in sm['sources']:
   if z.get('repository') in ('tock/tock','asterinas/asterinas') and 'path' in z:out.append((z['repository'],z['revision'],z['path'],z['blob']))
 return out
def run():
 d=json.loads((P/'matrix.json').read_text());need(d['schema']==1 and d['baseline_reference_commit']==BASE and d['frozen_reference_commit']==FROZEN,'corpus IDs')
 need((d['baseline_count'],d['current_count'])==(581,597),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash');inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==597 and bp<=fp and len(d['added_after_baseline'])==16 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'16 additions')
 for z in d['added_after_baseline']:
  need(z['report_md']==z['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(z['report_json']))==z['json_sha256'] and sha(gb(z['report_md']))==z['md_sha256'],'addition hashes')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'observation hash');e=json.loads(eb)
 need({r['repository'] for r in e['repositories']}=={'tock/tock','asterinas/asterinas'},'separate repos')
 byrepo={r['repository']:r for r in e['repositories']};t=byrepo['tock/tock'];a=byrepo['asterinas/asterinas']
 for r,branch,current in [(t,'master',TN),(a,'main',A)]:
  need(r['official_default_branch']==branch and r['current_default_commit']==current and r['refs']['HEAD']==r['refs']['refs/heads/'+branch]==current,'current branch')
  raw={ref:sha for sha,ref in (line.split('\t') for line in r['raw_ls_remote'].splitlines())};need(raw==r['refs'],'raw refs')
 tp={v['old_commit']:v for v in t['pins']};ap={v['old_commit']:v for v in a['pins']};need(set(tp)=={T0,T1} and set(ap)=={A},'pin graph')
 for old,n,files in [(T0,23,28),(T1,21,25)]:
  v=tp[old];need((v['compare_status'],v['ahead_by'],v['behind_by'],v['total_commits'],len(v['changed_files']))==('ahead',n,0,n,files),'Tock compare range')
  need(len({z['path'] for z in v['changed_files']})==files,'complete changed-path list')
  for z in v['changed_files']:
   if z['status']=='removed':need('new_blob_sha' not in z and len(z.get('old_blob_sha',''))==40,'removed-file old blob semantics')
   else:need('old_blob_sha' not in z and len(z.get('new_blob_sha',''))==40,'present-file new blob semantics')
 need((ap[A]['compare_status'],ap[A]['ahead_by'],ap[A]['behind_by'],ap[A]['total_commits'],ap[A]['changed_files'])==('identical',0,0,0,[]),'Asterinas same pin')
 need(e['pin_relationship']=={'repository':'tock/tock','old':T0,'new':T1,'status':'ahead','ahead_by':2,'behind_by':0,'changed_paths':['doc/wg/cryptography/notes/cryptography-notes-2026-9-1.md','doc/wg/cryptography/notes/cryptography-notes-2026-9-22.md','doc/wg/cryptography/notes/cryptography-notes-2026-9-8.md']},'Tock pin relation')
 tr=t['latest_release'];ar=a['latest_release']
 need(tr['tag']=='release-2.2' and tr['tag_object_type']=='tag' and tr['peeled_type']=='commit' and tr['peeled_commit']=='9554639b17501a9f5940cef7a1770a0823e790c3' and tr['relation_to_first_pin']=={'status':'diverged','ahead_by':2639,'behind_by':12},'Tock release separate')
 need(ar['tag']=='v0.18.1' and ar['peeled_type']=='commit' and ar['peeled_commit']=='d924a9635a66c7c3bb43e563eaafa2c61d6ee9d5' and ar['relation_to_first_pin']=={'status':'ahead','ahead_by':268,'behind_by':0},'Asterinas release separate')
 rows=d['rows'];need([r['inventory_id'] for r in rows]==['R571','R572','R573'],'three rows')
 selectors=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(len(selectors)==3,'selector count')
 for r,sel in zip(rows,selectors):
  id=r['inventory_id'];xs=[v for v in inv if v['inventory_id']==id];need(len(xs)==1,'one selector');x=xs[0]
  need(sel=={'inventory_id':id,'cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']},'selector exact')
  need((r['cohort'],r['title'],r['report_json'],r['report_md'])==(x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row identity')
  mp=x['report_md_at_commit'];ep=mp.replace('REPORT.md','support/evidence-map.json' if id=='R571' else 'source-map.json')
  mb=gb(mp);jb=gb(r['report_json']);mapb=gb(ep);md=mb.decode();meta=json.loads(jb);sm=json.loads(mapb)
  need(r['evidence_map_path']==ep and sha(mb)==r['frozen_md_sha256'] and sha(jb)==r['frozen_json_sha256'] and sha(mapb)==r['frozen_evidence_map_sha256'],'frozen hashes')
  need(meta['subjects']==r['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subjects')
  heading='# Summary' if id=='R573' else '## Summary';end='# Applicability' if id=='R573' else '## Applicability';lines=md.splitlines();i=lines.index(heading)+1
  while not lines[i].strip():i+=1
  j=lines.index(end);summary='\n'.join(lines[i:j]).rstrip();parts=summary.split('\n\n')
  need(r['claim_locator']=={'heading':heading,'line':i+1} and r['full_summary_exact']==summary and r['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'exact claims')
  status='mapped_tock_kernel_lib_lint_delta_no_safety_semantics' if id=='R572' else 'mapped_paths_unchanged_broader_claim_unresolved'
  need(r['clauses']==[{'number':n,'exact_excerpt':p,'source_result':status,'runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(parts,1)],'clause texts/statuses')
  need(r['tock_old_commit']==PINS[id] and r['asterinas_old_commit']==A,'row pins')
  oldmap=mapped_sources(id,sm);need({(z['repository'],z['old_commit'],z['path'],z['old_blob']) for z in r['mapped_files']}==set(oldmap) and len(r['mapped_files'])==len(oldmap),'mapped source census')
  changed=[]
  for z in r['mapped_files']:
   need(z['old_commit']==(PINS[id] if z['repository']=='tock/tock' else A),'map pin')
   diff={v['path']:v for v in (tp[PINS[id]] if z['repository']=='tock/tock' else ap[A])['changed_files']}
   expected=diff[z['path']]['new_blob_sha'] if z['path'] in diff else z['old_blob'];state='changed_mapped_blob' if z['path'] in diff else 'unchanged_mapped_blob'
   need(z['new_blob']==expected and z['source_status']==state,'mapped blob relation')
   if z['path'] in diff:changed.append(z['path'])
  need(changed==(['kernel/src/lib.rs'] if id=='R572' else []),'row changed overlap')
  result='tock_mapped_kernel_lib_lint_delta_no_safety_conclusion' if id=='R572' else 'mapped_source_paths_unchanged_broader_claim_unresolved'
  need(r['source_result']==result and r['runtime_result']=='unexecuted_in_this_review' and r['anneal_product_result']=='unassessed','row result bounds')
 lib=next(v for v in tp[T1]['changed_files'] if v['path']=='kernel/src/lib.rs')
 need(lib['new_blob_sha']=='84a9f806ac8028253799ed85c45b65a867ee1faa' and '#![deny(clippy::undocumented_unsafe_blocks)]' in lib['patch'],'narrow lint delta')
 need(d['raw_source_snapshot_sha256'] is None,'no raw archive')
 print('OK: exact R571/R572/R573 claims/maps; 581/597 corpus, 16 additions; separate Tock/Asterinas source/release pins; one mapped lint delta; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
