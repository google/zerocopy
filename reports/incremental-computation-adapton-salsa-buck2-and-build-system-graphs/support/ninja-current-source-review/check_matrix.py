#!/usr/bin/env python3
"""Offline R494 frozen-corpus and recorded official-source checker."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='48b8693b47bb3e33ada4fe6fbb437adad40bbb7e'
PIN='4e4df1e567eb3c1475a51af261cba2bfff60b4be'
TAG='3441b633c2fe2c494e958780ba0f4227b1327634'
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
 need((d['baseline_count'],d['current_count'])==(581,596),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash');inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==596 and bp<=fp and len(d['added_after_baseline'])==15 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'15 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(a['report_json']))==a['json_sha256'] and sha(gb(a['report_md']))==a['md_sha256'],'addition hashes')
 xs=[v for v in inv if v['inventory_id']=='R494'];need(len(xs)==1,'one R494 selector');x=xs[0]
 row=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(row==[{'inventory_id':'R494','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']}],'selector')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_json'],d['report_md'])==('R494',x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row identity')
 mb=gb(d['report_md']);jb=gb(d['report_json']);emb=gb(d['evidence_map_path']);md=mb.decode();meta=json.loads(jb);em=json.loads(emb)
 need(sha(mb)==d['frozen_md_sha256'] and sha(jb)==d['frozen_json_sha256'] and sha(emb)==d['frozen_evidence_map_sha256'],'frozen hashes')
 need(meta['subjects']==d['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subjects')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();paras=summary.split('\n\n')
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and len(paras)==5,'exact summary')
 need(d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory excerpt')
 ids=[['ninja-current-manual','gnu-make-4.4.1-manual'],['feldman-1979','gnu-make-4.4.1-manual'],['ninja-current-manual','martin-ninja-2011'],['ninja-current-manual','anneal-principles-design'],['ninja-current-manual','anneal-principles-design']]
 need(d['clauses']==[{'number':n,'exact_excerpt':p,'evidence_map_ids':ids[n-1],'ninja_source_result':'pinned_master_commit_unchanged_no_forward_range','runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(paras,1)],'claim clauses')
 emids={v['id'] for v in em['sources']};need(all(i in emids for group in ids for i in group),'evidence-map links')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'observation hash');e=json.loads(eb)
 need(e['repository']=='ninja-build/ninja' and e['old_pinned_commit']==e['default_branch_commit']==PIN and e['official_default_branch']=='master','pin/current ref')
 need(e['refs'].get('HEAD')==e['refs'].get('refs/heads/master')==PIN and e['refs'].get('refs/tags/v1.13.2')==TAG,'raw ref identities')
 raw={ref:sha for sha,ref in (line.split('\t') for line in e['raw_ls_remote'].splitlines())};need(raw==e['refs'],'exact raw refs')
 need(e['commit_parent_ids']==['c8b233e8053c03d2fd57389035b47d36e98e69a8','8a1b0c95d887243a1018a5a845c68d4cce1901bf'] and len(e['commit_tree_id'])==40 and e['forward_commit_count']==0 and e['changed_paths']==[],'zero forward range')
 src=e['claim_source'];need(src['path']=='doc/manual.asciidoc' and src['current_blob_sha']=='81ecf7d388f899a1481df9f25ec1065710de679d' and src['current_type']=='file','pinned manual blob')
 mapped=next(v for v in em['sources'] if v['id']=='ninja-current-manual');need('81ecf7d388f899a1481df9f25ec1065710de679d' in mapped['identity'] and src['old_evidence_map_identity']==mapped['identity'],'manual map identity')
 rel=e['latest_official_release'];need(rel['tag']=='v1.13.2' and rel['tag_commit']==rel['tag_ref_object_sha']==TAG and rel['tag_object_type']=='commit','release tag peeled identity')
 need(rel['source_relation_to_pin']=={'status':'diverged','ahead_by':196,'behind_by':60,'total_commits':196} and rel['manual_blob_sha']=='a9b97ee92b67d5d3a246d2e06e94bf44ff70b0c5','release divergence')
 need(d['ninja_old_and_current_master_commit']==PIN and d['source_result']=='master_same_pinned_commit_no_forward_source_comparison_latest_release_diverged' and d['current_runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed' and d['raw_source_snapshot_sha256'] is None,'result bounds')
 print('OK: exact R494 five-paragraph claim/evidence map; 581/596 corpus, 15 additions; master same pin, manual blob same; release diverged; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
