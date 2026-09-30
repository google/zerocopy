#!/usr/bin/env python3
"""Offline check of exact frozen R501 corpus and recorded source observations."""
import csv,hashlib,json,re,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent
BASE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='4774f2e455d1b70a6321b760deeb6caae0e6f920'
OLD='c480400b0e6cb9a9b36384935639fb3e6566bd68'
NEW='955de750a2aae45faa99e02e29715b794dd3b544'
CHANGE='76ab45a89c9f0ccc6e0bef3867a9ffcc775f8e10'
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
 need((d['baseline_count'],d['current_count'])==(581,593),'corpus counts')
 ib=(P/'version-inventory-ebcdcad-581.csv').read_bytes();need(sha(ib)==d['baseline_inventory_sha256'],'inventory hash')
 inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory rows')
 bp=set((P/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASE)=={v['report_json_at_commit'] for v in inv},'baseline paths')
 need(len(fp)==593 and bp<=fp and len(d['added_after_baseline'])==12 and {a['report_json'] for a in d['added_after_baseline']}==fp-bp,'12 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md') and sha(gb(a['report_json']))==a['json_sha256'] and sha(gb(a['report_md']))==a['md_sha256'],'added hashes')
 xs=[v for v in inv if v['inventory_id']=='R501'];need(len(xs)==1,'one R501');x=xs[0]
 row=list(csv.DictReader((P/'frozen-cohort.csv').open()));need(row==[{'inventory_id':'R501','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']}],'selector')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_json'],d['report_md'])==('R501',x['cohort'],x['title'],x['report_json_at_commit'],x['report_md_at_commit']),'row metadata')
 mb=gb(d['report_md']);jb=gb(d['report_json']);md=mb.decode();meta=json.loads(jb)
 need(sha(mb)==d['frozen_md_sha256'] and sha(jb)==d['frozen_json_sha256'],'frozen hashes')
 need(meta['subjects']==d['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subject graph')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();first=summary.split('\n\n')[0]
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and d['first_claim_paragraph_exact']==first,'exact summary')
 need(d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory excerpt')
 items=[{'number':int(m.group(1)),'exact_excerpt':m.group(0),'source_result':'no_architectural_drift_established','runtime_result':'unexecuted_in_this_review'} for m in re.finditer(r'(?m)^([1-4])\. (.*?)(?=\n[1-4]\. |\n\n)',summary,re.S)]
 need(len(items)==4 and d['four_summary_clauses']==items,'four claim clauses')
 need(d['old_source_commit']==OLD and d['selected_observed_main_commit']==NEW and meta['subjects'][0]['identity']['revision']==OLD,'old/new pins')
 eb=(P/'official-source-comparison.json').read_bytes();need(sha(eb)==d['source_evidence_sha256'],'evidence hash');e=json.loads(eb)
 need(e['old_commit']==OLD and e['selected_main_commit']==e['new_commit']==e['selected_main_ref_observation']==NEW,'observed source pair')
 need(e['range_log_count']==91 and e['range_first_commit']==NEW and e['range_last_parent']==OLD,'bounded forward ancestry')
 need(e['notable_commit']['commit']==CHANGE,'source change')
 changed={p['path']:(p['old_id'],p['new_id']) for p in e['netstack_changed_paths']}
 prefix='src/connectivity/network/netstack3/core/'
 need(changed=={prefix+'filter/src/logic.rs':('9424d1c255a43ffd80fffc8ff9f1bdb95efb447a','97ccaae10c4c6daf1076ccf96f9fa5eb6fcdd995'),prefix+'ip/src/base.rs':('83622aa653caec80c4cf23cedc53f49aed406894','d485be4e0bc166de5b31145d620a49f284cb3524'),prefix+'ip/src/base/tests.rs':('6ab184de0ae48aca0600890a0d1d488e548b9631','bc213737eb092e2a730fbf1c528131630a3ba60e')},'three changed blobs')
 need({v['old_path']:(v['old_id'],v['new_id']) for v in e['notable_commit']['tree_diff']}==changed,'change tree diff')
 need(set(e['unchanged_tree_ids'])=={'src/connectivity/network/netstack3/'+p for p in ('docs','src','core/tcp','core/udp','core/device','core/lock-order','core/sync')},'unchanged tree scope')
 need(d['source_result']=='three_changed_netstack3_blobs_narrow_claim_adjacent_no_architectural_conclusion' and d['current_runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed','result bounds')
 need(d['old_source_snapshot_sha256'] is None and d['new_source_snapshot_sha256'] is None,'no raw source snapshots')
 print('OK: exact R501 frozen claim/subjects; 581/593 corpus and 12 additions; bounded 91-commit source range; 3 changed blobs; runtime unexecuted')
if __name__=='__main__':
 try:run()
 except Exception as err:print('FAIL:',err,file=sys.stderr);raise
