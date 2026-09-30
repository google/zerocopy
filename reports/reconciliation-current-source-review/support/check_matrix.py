#!/usr/bin/env python3
"""Offline R510 frozen-corpus and two-repository source checker."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837';FROZEN='7aba064d95afec974b2478feca6f8c1a1c0b3088'
PINS={'kubernetes-sigs/controller-runtime':('8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b','8564dc352deed83f3dfcd5c5e47d1fed6c6dd28b','main',0,0),'kubernetes/kubernetes':('6d1d025050cb63ae5b8e53037aced205e6a28410','08147af84478f859c2e2234d71ceace8bdb412c7','master',20,38)}
BLOBS={'pkg/reconcile/reconcile.go':'88303ae781a1e6baf0d5ca5e935bcc4f1416aaf4','pkg/doc.go':'64693b4829d2212fc4f0504a9f22b758ccbdd5e5','staging/src/k8s.io/client-go/tools/cache/reflector.go':'82de01f9ae5f73ca1cd58491156afd7fd9ccb457'}
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
 need((d['baseline_count'],d['current_count'])==(581,603),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash');inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory rows')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={x['report_json_at_commit'] for x in inv},'baseline paths')
 need(len(fp)==603 and bp<=fp and len(d['added_after_baseline'])==22 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'22 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(a['report_json']))==a['json_sha256'] and sha(gb(a['report_md']))==a['md_sha256'],'addition hashes')
 xs=[x for x in inv if x['inventory_id']=='R510'];need(len(xs)==1,'one R510');x=xs[0]
 sel=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(sel==[{'inventory_id':'R510','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']}],'selector')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_json'],d['report_md'])==('R510',x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row identity')
 mp=x['report_md_at_commit'];ep=mp.replace('REPORT.md','support/evidence-map.json');mb=gb(mp);jb=gb(d['report_json']);emb=gb(ep);md=mb.decode();meta=json.loads(jb);em=json.loads(emb)
 need(d['evidence_map_path']==ep and sha(mb)==d['frozen_md_sha256'] and sha(jb)==d['frozen_json_sha256'] and sha(emb)==d['frozen_evidence_map_sha256'],'frozen hashes')
 need(d['frozen_subjects_exact']==meta['subjects']==json.loads(x['exact_pinned_subject_identities_json']),'subject pins')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();parts=summary.split('\n\n');need(len(parts)==3,'three Summary paragraphs')
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'exact claims')
 ids=[['controller-runtime-level-based','kubernetes-reflector','linux-inotify'],['controller-runtime-level-based','kubernetes-reflector','anneal-design'],['anneal-design','anneal-watch-loop-probe']]
 need(d['summary_paragraphs']==[{'number':n,'exact_excerpt':p,'evidence_ids':ids[n-1],'source_result':'mapped_source_blobs_unchanged_no_behavior_conclusion' if n==1 else 'derived_anneal_claim_unassessed','runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(parts,1)],'claim/evidence links')
 emap={z['id']:z for z in em['sources']};need(all(v in emap for group in ids for v in group),'source IDs')
 need(emap['controller-runtime-level-based']['paths']==['pkg/reconcile/reconcile.go','pkg/doc.go'] and emap['kubernetes-reflector']['path']=='staging/src/k8s.io/client-go/tools/cache/reflector.go','original source paths')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'source observation hash');obs=json.loads(eb);by={r['repository']:r for r in obs['repositories']};need(set(by)==set(PINS),'separate repos')
 mapped=[]
 for repo,(old,new,branch,n,count) in PINS.items():
  r=by[repo];need((r['old_commit'],r['selected_current_commit'],r['branch'])==(old,new,branch),'source pair')
  raw={ref:sha for sha,ref in (line.split('\t') for line in r['raw_ls_remote'].splitlines())};need(raw==r['refs'] and raw['HEAD']==raw['refs/heads/'+branch]==new,'official ref')
  cmp=r['compare'];need((cmp['status'],cmp['ahead_by'],cmp['behind_by'],cmp['total_commits'],cmp['returned_file_count'],cmp['file_list_complete'])==('identical' if n==0 else 'ahead',n,0,n,count,True),'forward range')
  need(len(cmp['changed_files'])==count and len({v['path'] for v in cmp['changed_files']})==count,'complete changed paths')
  need(not {v['path'] for v in cmp['changed_files']}&{v['path'] for v in r['mapped_files']},'mapped/changed non-overlap')
  for v in r['mapped_files']:
   need(v['path'] in BLOBS and v['old']['git_blob_sha1']==v['new']['git_blob_sha1']==BLOBS[v['path']],'mapped blob')
   need(v['old']['content_sha256']==v['new']['content_sha256'] and v['old']['size']==v['new']['size'],'raw content hash')
   need(v['old']['url']==f'https://raw.githubusercontent.com/{repo}/{old}/{v["path"]}' and v['new']['url']==f'https://raw.githubusercontent.com/{repo}/{new}/{v["path"]}','commit-pinned URLs')
   mapped.append({'repository':repo,'old_commit':old,'selected_current_commit':new,'path':v['path'],'old_blob_sha1':v['old']['git_blob_sha1'],'new_blob_sha1':v['new']['git_blob_sha1']})
 need(d['mapped_files']==mapped and len(mapped)==3,'matrix mapped files')
 cr=by['kubernetes-sigs/controller-runtime']['latest_release'];ku=by['kubernetes/kubernetes']['latest_release']
 need(cr['tag']=='v0.25.1' and cr['tag_ref_type']=='commit' and cr['peeled_commit']=='67b72c2517be1d2b0dec612477eb20c3c959a8aa' and cr['relation_to_old_pin']=={'status':'diverged','ahead_by':20,'behind_by':2},'controller release separate')
 need(ku['tag']=='v1.37.1' and ku['tag_ref_type']=='tag' and ku['tag_ref_sha']=='d2b770f4c94636a992534a8d3156b6b2d8e82ac3' and ku['peeled_commit']=='f78e722310e50bcaca9276be22276d9e91d91308' and ku['relation_to_old_pin']=={'status':'diverged','ahead_by':1255,'behind_by':40},'Kubernetes release separate')
 need(d['source_result']=='controller_runtime_same_pin_reflector_mapped_blob_unchanged_broader_behavior_unresolved' and d['runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed' and d['full_source_archive_sha256'] is None,'result bounds')
 print('OK: exact R510 frozen claims/source map; 581/603 corpus, 22 additions; controller same pin, Reflector +20/38 non-overlap; release branches separate; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
