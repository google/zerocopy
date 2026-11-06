#!/usr/bin/env python3
"""Offline check of R576's exact frozen claim and corpus reconciliation."""
import csv,hashlib,json,re,subprocess,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='a69cfaf1cbee462fb9bbae9a75d57e16e6c34a64'
OLD='607a22a90d1a5a1b507ce01bb8cd7ec020f954e7'
MIRROR='1e4744d68260a7cb91b62b12edc3f6a2187faaf1'
NATIVE='2bd066d87f5bafd315be9f40889d0a60b9e58e0b'
COHORT='TypeScript 6.0.2 source 607a22a90d1a5a1b507ce01bb8cd7ec020f954e7'
def need(ok,why):
    if not ok:raise AssertionError(why)
def gb(p):return subprocess.check_output(['git','show',f'{FROZEN}:{p}'],stderr=subprocess.DEVNULL)
def paths(c):
    need(subprocess.check_output(['git','rev-parse',f'{c}^{{commit}}'],text=True).strip()==c,'exact corpus commit')
    return {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',c,'reports'],text=True).splitlines() if p.endswith('/REPORT.json')}
def main():
    d=json.loads((BASE/'matrix.json').read_text())
    need(d['schema']==1 and d['baseline_reference_commit']==BASELINE and d['frozen_reference_commit']==FROZEN,'corpus identity')
    need(d['cohort']==COHORT and d['baseline_count']==581 and d['current_count']==589,'cohort census')
    ib=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes();need(hashlib.sha256(ib).hexdigest()==d['baseline_inventory_sha256'],'inventory hash')
    inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory size')
    baseline=set((BASE/'baseline-report-paths.txt').read_text().splitlines());need(len(baseline)==581 and baseline=={x['report_json_at_commit'] for x in inv}==paths(BASELINE),'baseline Git source')
    current=paths(FROZEN);adds={x['report_json'] for x in d['added_after_baseline']}
    need(len(current)==589 and len(adds)==8 and current-baseline==adds and not baseline-current,'eight additions')
    for x in d['added_after_baseline']:
        need(x['report_md']==x['report_json'].replace('REPORT.json','REPORT.md'),'addition pair')
        need(hashlib.sha256(gb(x['report_json'])).hexdigest()==x['json_sha256'] and hashlib.sha256(gb(x['report_md'])).hexdigest()==x['md_sha256'],'addition hashes')
    sel=[x for x in inv if x['cohort']==COHORT];selector=list(csv.DictReader((BASE/'frozen-cohort.csv').open()));rows=d['rows']
    need(len(sel)==len(selector)==len(rows)==1 and sel[0]['inventory_id']==selector[0]['inventory_id']==rows[0]['inventory_id']=='R576','single R576 selector')
    x=sel[0];s=selector[0];r=rows[0]
    need((x['report_md_at_commit'],x['report_json_at_commit'])==(s['report_md'],s['report_json'])==(r['report_md'],r['report_json']),'exact paths')
    mb=gb(r['report_md']);jb=gb(r['report_json']);md=mb.decode();meta=json.loads(jb)
    need(hashlib.sha256(mb).hexdigest()==r['frozen_md_sha256'] and hashlib.sha256(jb).hexdigest()==r['frozen_json_sha256'],'frozen hashes')
    need(meta['subjects']==r['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'original subjects')
    old=[z for z in meta['subjects'] if z['identity'].get('repository')=='microsoft/TypeScript'];need(len(old)==1 and old[0]==r['old_typescript_subject_exact'] and old[0]['identity']['revision']==OLD,'old source pin')
    lines=md.splitlines();i=lines.index('## Summary')+1
    while not lines[i].strip():i+=1
    start=i
    while i<len(lines) and lines[i].strip() and not lines[i].startswith('#'):i+=1
    excerpt='\n'.join(lines[start:i]);need(bool(excerpt) and md.count(excerpt)==1 and r['claim_excerpt_exact']==excerpt and r['claim_locator']=={'heading':'## Summary','line':start+1},'exact claim/locator')
    need(r['title']==x['title'] and r['inventory_cohort']==COHORT,'inventory identity')
    need(r['old_source_blob_sha1_mentions']==sorted(set(re.findall(r'\bblob `([0-9a-f]{40})`',md))),'old blob mentions')
    need(r['target']=={'release':'7.0.2','mirrored_repository':'microsoft/TypeScript','mirrored_tag':'v7.0.2','mirrored_commit':MIRROR,'original_native_repository':'microsoft/typescript-go','original_native_tag':'typescript/v7.0.2','original_native_commit':NATIVE,'mirrored_tag_ref_type':'lightweight','original_native_tag_ref_type':'lightweight'},'target pin graph')
    need(r['source_claim_result']=='unresolved_at_target' and r['current_runtime_result']=='unexecuted_in_this_review' and r['anneal_product_result']=='unassessed','separate conclusions')
    need(r['old_source_snapshot_sha256'] is None and r['new_source_snapshot_sha256'] is None,'no acquired raw-source hashes')
    print('OK: exact frozen R576 claim/metadata; eight additions; 7.0.2 mirror/native pins; source unresolved and runtime unexecuted')
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL:',e,file=sys.stderr);raise
