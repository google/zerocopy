#!/usr/bin/env python3
"""Offline R410 frozen-claim and three-repository source checker."""
import csv,hashlib,json,subprocess,sys,urllib.parse
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837';FROZEN='0acbffd307e1d4288d784055f9883dd9fa5fd3b9'
PINS={'JetBrains/kotlin':('bce49f3701fb8dc461fb98240fdc7c3c81c592f2','79b33f2836ef88425c100924bb8d29bcdf52bf48','master',106,300,6),'swiftlang/sourcekit-lsp':('045c18e9e9ea35b896857b6cb982aa2373fb5816','045c18e9e9ea35b896857b6cb982aa2373fb5816','main',0,0,3),'swiftlang/swift':('f63674ca12ca2b79b5dd87cd6b04e57ef9b0485d','0fcad6fb60755587d39a758761b219bf433cf9dc','main',36,246,2)}
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
 need((d['baseline_count'],d['current_count'])==(581,601),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash');inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory rows')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==601 and bp<=fp and len(d['added_after_baseline'])==20 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'20 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(a['report_json']))==a['json_sha256'] and sha(gb(a['report_md']))==a['md_sha256'],'addition hashes')
 xs=[v for v in inv if v['inventory_id']=='R410'];need(len(xs)==1,'one R410');x=xs[0]
 row=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(row==[{'inventory_id':'R410','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']}],'selector')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_json'],d['report_md'])==('R410',x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row identity')
 mp=d['report_md'];ep=mp.replace('REPORT.md','evidence-map.json');mb=gb(mp);jb=gb(d['report_json']);emb=gb(ep);md=mb.decode();meta=json.loads(jb);em=json.loads(emb)
 need(d['evidence_map_path']==ep and sha(mb)==d['frozen_md_sha256'] and sha(jb)==d['frozen_json_sha256'] and sha(emb)==d['frozen_evidence_map_sha256'],'frozen hashes')
 need(d['frozen_subjects_exact']==meta['subjects']==json.loads(x['exact_pinned_subject_identities_json']),'subject graph')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();parts=summary.split('\n\n')
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and len(parts)==4 and d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'exact Summary')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'official observation hash');obs=json.loads(eb);by={r['repository']:r for r in obs['repositories']};need(set(by)==set(PINS),'three separate repositories')
 flat=[]
 for repo,(old,new,branch,n,fc,mc) in PINS.items():
  r=by[repo];need((r['old_commit'],r['selected_current_commit'],r['branch'])==(old,new,branch),'source pair')
  raw={ref:sha for sha,ref in (line.split('\t') for line in r['raw_ls_remote'].splitlines())};need(raw==r['refs'] and raw['HEAD']==raw['refs/heads/'+branch]==new,'official ref')
  cmp=r['compare'];need((cmp['status'],cmp['ahead_by'],cmp['behind_by'],cmp['total_commits'],cmp['returned_file_count'])==('identical' if n==0 else 'ahead',n,0,n,fc),'forward relation')
  need(cmp['file_list_complete']==(repo!='JetBrains/kotlin') and (cmp['changed_files'] is None if repo=='JetBrains/kotlin' else len(cmp['changed_files'])==fc),'compare list boundary')
  need(len(r['mapped_files'])==mc and len({v['path'] for v in r['mapped_files']})==mc,'mapped file census')
  if cmp['changed_files'] is not None:need(not {v['path'] for v in r['mapped_files']}&{v['path'] for v in cmp['changed_files']},'mapped/change non-overlap')
  for v in r['mapped_files']:
   need(v['old']['git_blob_sha1']==v['new']['git_blob_sha1'] and v['old']['content_sha256']==v['new']['content_sha256'] and v['old']['size']==v['new']['size'],'same mapped bytes')
   for key,rev in [('old',old),('new',new)]:
    z=v[key];need(len(z['git_blob_sha1'])==40 and len(z['content_sha256'])==64 and z['url']==f'https://raw.githubusercontent.com/{repo}/{rev}/{urllib.parse.quote(v["path"])}','commit-pinned source hash')
   flat.append({'repository':repo,'old_commit':old,'selected_current_commit':new,'path':v['path'],'old_blob_sha1':v['old']['git_blob_sha1'],'new_blob_sha1':v['new']['git_blob_sha1'],'claim_indices':v['claim_indices']})
 need(d['mapped_files']==flat and len(flat)==11,'exact mapped files')
 need(len(em['claims'])==6 and len(d['evidence_claims'])==6,'six evidence claims')
 for n,(c,v) in enumerate(zip(em['claims'],d['evidence_claims']),1):
  files=[{'repository':m['repository'],'path':m['path']} for m in flat if n in m['claim_indices']]
  need(v=={'number':n,'exact_claim':c['claim'],'role':c['role'],'mapped_files':files,'source_result':'mapped_source_blobs_unchanged_no_behavior_conclusion' if files else 'derived_anneal_claim_unassessed','runtime_result':'unexecuted_in_this_review'},'claim evidence mapping')
  for m in flat:
   if n in m['claim_indices']:need(m['repository']+'@'+m['old_commit']+':'+m['path'] in c['evidence'],'claim/source locator')
 refs=[[1,2,5],[1,4],[3,5],[6]]
 need(d['summary_paragraphs']==[{'number':n,'exact_excerpt':p,'evidence_claim_numbers':refs[n-1],'source_result':'mapped_source_blobs_unchanged_no_behavior_conclusion' if n<4 else 'derived_anneal_claim_unassessed','runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(parts,1)],'summary claim links')
 need(d['source_result']=='claim_mapped_blobs_unchanged_broader_behavior_unresolved' and d['runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed' and d['full_source_archive_sha256'] is None,'result bounds')
 print('OK: exact R410 Summary/6 claims/11 files; 581/601 corpus and 20 additions; Kotlin +106 capped, LSP same, Swift +36 complete; mapped blobs unchanged; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
