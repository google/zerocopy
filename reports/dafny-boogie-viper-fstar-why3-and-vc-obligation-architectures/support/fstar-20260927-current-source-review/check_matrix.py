#!/usr/bin/env python3
"""Offline R400 frozen-corpus and recorded upstream-identity checker."""
import csv,hashlib,json,re,subprocess,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='6b1af799ae4ed60744e98137033ab66e1d3b68a5'
OLD='78bb239b54cc113be68fb1dc0cbdfeb19378766a'
TAG='48268f3522ec8da089bbeb5f4e1674d50280a9c7'
RELEASE='7deb38a27c86990664c6b41e4b6093597acdebd4'
def need(ok,why):
 if not ok:raise AssertionError(why)
def git(*a):return subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL)
def gb(p):return git('show',f'{FROZEN}:{p}')
def paths(c):
 need(git('rev-parse',f'{c}^{{commit}}').decode().strip()==c,'exact corpus commit')
 return {p for p in git('ls-tree','-r','--name-only',c,'reports').decode().splitlines() if p.endswith('/REPORT.json')}
def main():
 d=json.loads((BASE/'matrix.json').read_text());need(d['schema']==1 and d['baseline_reference_commit']==BASELINE and d['frozen_reference_commit']==FROZEN,'corpus IDs')
 need(d['baseline_count']==581 and d['current_count']==592,'corpus counts')
 ib=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes();need(hashlib.sha256(ib).hexdigest()==d['baseline_inventory_sha256'],'inventory hash')
 inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
 bp=set((BASE/'baseline-report-paths.txt').read_text().splitlines());fp=paths(FROZEN)
 need(len(bp)==581 and bp==paths(BASELINE)=={x['report_json_at_commit'] for x in inv},'baseline paths')
 need(len(fp)==592 and bp<=fp and len(d['added_after_baseline'])==11 and {x['report_json'] for x in d['added_after_baseline']}==fp-bp,'11 additions')
 for a in d['added_after_baseline']:
  need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md'),'addition pair')
  need(hashlib.sha256(gb(a['report_json'])).hexdigest()==a['json_sha256'] and hashlib.sha256(gb(a['report_md'])).hexdigest()==a['md_sha256'],'addition hashes')
 x=next(z for z in inv if z['inventory_id']=='R400');need(sum(z['inventory_id']=='R400' for z in inv)==1,'one selector')
 s=list(csv.DictReader((BASE/'frozen-cohort.csv').open()));need(len(s)==1 and s[0]=={'inventory_id':'R400','cohort':x['cohort'],'report_json':x['report_json_at_commit'],'report_md':x['report_md_at_commit']},'selector paths')
 need((d['inventory_id'],d['cohort'],d['title'],d['report_md'],d['report_json'])==('R400',x['cohort'],x['title'],x['report_md_at_commit'],x['report_json_at_commit']),'row ID')
 mb=gb(d['report_md']);jb=gb(d['report_json']);md=mb.decode();meta=json.loads(jb)
 need(hashlib.sha256(mb).hexdigest()==d['frozen_md_sha256'] and hashlib.sha256(jb).hexdigest()==d['frozen_json_sha256'],'frozen hashes')
 need(meta['subjects']==d['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subjects')
 lines=md.splitlines();i=lines.index('## Summary')+1
 while not lines[i].strip():i+=1
 j=lines.index('## Applicability');summary='\n'.join(lines[i:j]).rstrip();first=summary.split('\n\n')[0]
 need(d['claim_locator']=={'heading':'## Summary','line':i+1} and d['full_summary_exact']==summary and d['first_claim_paragraph_exact']==first and md.count(summary)==1,'exact summary')
 need(d['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory claim')
 need(d['old_source_blob_sha1_mentions']==sorted(set(re.findall(r'\bblob `([0-9a-f]{40})`',md))),'old blobs')
 need(d['old_source_commit']==d['current_master_commit']==OLD and d['latest_release_tag']=='v2026.09.27' and d['latest_release_annotated_tag_object']==TAG and d['latest_release_peeled_commit']==RELEASE,'source pin graph')
 raw=(BASE/'official-source-identity.json').read_bytes();need(hashlib.sha256(raw).hexdigest()==d['official_identity_sha256'],'official identity snapshot hash')
 o=json.loads(raw);need(o['pinned_commit']==OLD and o['refs']=={'HEAD':OLD,'refs/heads/master':OLD,'refs/tags/v2026.09.27':TAG,'refs/tags/v2026.09.27^{}':RELEASE},'recorded official refs')
 need(o['pinned_commit_author_date']==o['pinned_commit_committer_date']=='2026-09-29T23:36:07Z' and o['newer_source_commit_observed'] is False,'date/no-newer result')
 need({c['id'] for c in d['clauses']}=={'abstract_proof_state_primitives_divergence','smt_oracle_trust','native_tactic_execution','tactic_hook_stage_authority','historical_and_cross_prover_context'},'clauses')
 for c in d['clauses']:
  need(c['pinned_source_urls']==[f'https://github.com/FStarLang/FStar/blob/{OLD}/{p}' for p in c['paths']],'source URLs')
  need(c['new_source_result']=='no_newer_official_source_revision_observed' and c['runtime_result']=='unexecuted_in_this_review','clause bounds')
 need(d['source_result']=='no_newer_official_source_or_release_to_recheck' and d['current_runtime_result']=='unexecuted_in_this_review' and d['anneal_product_result']=='unassessed','results')
 need(d['old_source_snapshot_sha256'] is None and d['new_source_snapshot_sha256'] is None,'no acquired raw-source hashes')
 print('OK: exact frozen R400 summary/subjects; 581/592 corpus; 11 additions; master same commit; latest release older; runtime unexecuted')
if __name__=='__main__':
 try:main()
 except Exception as e:print('FAIL:',e,file=sys.stderr);raise
