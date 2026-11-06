#!/usr/bin/env python3
"""Offline R405 exact-corpus and recorded official-source observation checker."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='3d730ab522554cd534b2ddf582b96e1e233f1fff'
PINS={'haskell/haskell-language-server':'187fcd4a685c220caabb72999565604b3287aff2','haskell/hie-bios':'32dd07707423ffabb34e44af68fcbd027b60ded2'}
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
 need((d['baseline_count'],d['current_count'])==(581,594),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash')
 inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==594 and bp<=fp and len(d['added_after_baseline'])==13 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'13 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(a['report_json']))==a['json_sha256'] and sha(gb(a['report_md']))==a['md_sha256'],'addition hashes')
 xs=[v for v in inv if v['inventory_id']=='R405'];need(len(xs)==1,'one R405 selector');x=xs[0]
 row=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(row==[{'inventory_id':'R405','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']}],'selector')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_json'],d['report_md'])==('R405',x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row identity')
 mb=gb(d['report_md']);jb=gb(d['report_json']);smb=gb(d['source_map_path']);md=mb.decode();meta=json.loads(jb);sm=json.loads(smb)
 need(sha(mb)==d['frozen_md_sha256'] and sha(jb)==d['frozen_json_sha256'] and sha(smb)==d['frozen_source_map_sha256'],'frozen hashes')
 need(meta['subjects']==d['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subjects')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();paras=summary.split('\n\n')
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and len(paras)==4,'exact summary')
 need(d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory excerpt')
 ids=[['hie-architecture','ghcide-readme','hls-readme','hie-bios-readme'],['hie-bios-readme','ghcide-readme'],['hls-graph-readme','hls-current-rules'],['hie-bios-readme','hls-graph-readme']]
 need(d['clauses']==[{'number':n,'exact_excerpt':p,'source_map_ids':ids[n-1],'source_result':'same_pinned_commit_no_forward_source_comparison_for_HLS_and_hie_bios','runtime_result':'unexecuted_in_this_review'} for n,p in enumerate(paras,1)],'claim clauses')
 source_map={v['id']:v for v in sm['sources']};need(all(i in source_map for z in ids for i in z),'source-map links')
 eb=(P/'official-source-observation.json').read_bytes();need(sha(eb)==d['official_observation_sha256'],'observation hash');e=json.loads(eb)
 need({r['repository'] for r in e['repositories']}==set(PINS),'separate repositories')
 for r in e['repositories']:
  repo=r['repository'];pin=PINS[repo];need(r['old_pinned_commit']==pin and r['official_default_branch']=='master' and r['default_branch_commit']==pin,'pin/current ref')
  need(r['refs'].get('HEAD')==r['refs'].get('refs/heads/master')==pin and set(r['refs'])=={'HEAD','refs/heads/master'},'raw ref mapping')
  raw={ref:sha for sha,ref in (line.split('\t') for line in r['raw_ls_remote'].splitlines())};need(raw==r['refs'],'exact raw refs')
  need(len(r['old_commit_parent_ids'])==1 and len(r['old_commit_tree_id'])==40 and r['forward_commit_count']==0 and r['changed_paths']==[],'zero forward range')
  mapped=[v for v in sm['sources'] if v.get('repository')==repo];need({v['source_map_id'] for v in r['mapped_sources']}=={v['id'] for v in mapped},'mapped source census')
  for v in r['mapped_sources']:
   z=source_map[v['source_map_id']];need(v['path']==z['path'] and v['old_source_map_blob_sha']==v['current_blob_sha']==z['blob_sha'] and v['supports']==z['supports'] and v['commit_pinned_url']==z['url'] and v['current_type']=='file','mapped blobs')
 need(d['hls_old_and_current_commit']==PINS['haskell/haskell-language-server'] and d['hie_bios_old_and_current_commit']==PINS['haskell/hie-bios'],'separate pin graph')
 need(d['source_result']=='both_default_branches_equal_their_original_pins_no_forward_comparison' and d['current_runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed' and d['raw_source_snapshot_sha256'] is None,'result bounds')
 print('OK: exact R405 frozen four-paragraph claim and source map; 581/594 corpus, 13 additions; HLS and hie-bios same pinned commits; 5 mapped blobs; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
