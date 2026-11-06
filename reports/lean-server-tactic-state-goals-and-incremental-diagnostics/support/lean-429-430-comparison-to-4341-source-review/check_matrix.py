#!/usr/bin/env python3
"""Offline verification of six frozen Lean prior-comparison report rows."""
import csv,hashlib,json,subprocess,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='6c0988948cb2098a7c2d11ff89bd20322d562eaa'
COHORT='Lean/Lake v4.29.0 versus v4.30.0-rc2 (prior comparison)'
OLD={'v4.29.0':'98dc76e3c0a9b856c9b98726b713fb04fab16740','v4.30.0-rc2':'3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc'}
NEW='5045d0056413266e57c625dcd7c365b10e377c52'
SELECTED='`waitForDiagnostics` explicitly allows a document version greater than or equal to the requested number, and its handler accepts `p.version ≤ doc.meta.version`.'
def need(ok,why):
    if not ok:raise AssertionError(why)
def gb(p):return subprocess.check_output(['git','show',f'{FROZEN}:{p}'],stderr=subprocess.DEVNULL)
def paths(c):
    need(subprocess.check_output(['git','rev-parse',f'{c}^{{commit}}'],text=True).strip()==c,'exact corpus commit')
    return {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',c,'reports'],text=True).splitlines() if p.endswith('/REPORT.json')}
def first_claim(md,iid):
    lines=md.splitlines()
    if iid=='R462':
        ex=SELECTED;need(md.count(ex)==1,'R462 selected source clause')
        line=md[:md.index(ex)].count('\n')+1
    else:
        h=next((i for i,l in enumerate(lines) if l.startswith('## ')),None);need(h is not None,'missing section')
        i=h+1
        while i<len(lines) and (not lines[i].strip() or lines[i].startswith('#')):i+=1
        start=i
        while i<len(lines) and lines[i].strip() and not lines[i].startswith('#'):i+=1
        ex='\n'.join(lines[start:i]);line=start+1
        need(bool(ex) and md.count(ex)==1,'first claim unique')
    heading=next(l.strip() for l in reversed(lines[:line-1]) if l.startswith('#'))
    return ex,{'heading':heading,'line':line}
def main():
    d=json.loads((BASE/'matrix.json').read_text())
    need(d['schema']==1 and d['baseline_reference_commit']==BASELINE and d['frozen_reference_commit']==FROZEN,'corpus identities')
    need(d['prior_source_commits']==OLD and d['target_source_commit']==NEW,'source identities')
    need(d['cohort']==COHORT and d['baseline_count']==581 and d['current_count']==588,'census')
    ib=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes();need(hashlib.sha256(ib).hexdigest()==d['baseline_inventory_sha256'],'inventory hash')
    inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory size')
    baseline=set((BASE/'baseline-report-paths.txt').read_text().splitlines());need(len(baseline)==581 and baseline=={x['report_json_at_commit'] for x in inv}==paths(BASELINE),'baseline frozen Git corpus')
    current=paths(FROZEN);add={x['report_json'] for x in d['added_after_baseline']}
    need(len(current)==588 and len(add)==7 and current-baseline==add and not baseline-current,'post-inventory reconciliation')
    for a in d['added_after_baseline']:
        need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md'),'added pair')
        need(hashlib.sha256(gb(a['report_json'])).hexdigest()==a['json_sha256'] and hashlib.sha256(gb(a['report_md'])).hexdigest()==a['md_sha256'],'added hashes')
    selected=[x for x in inv if x['cohort']==COHORT];selector=list(csv.DictReader((BASE/'frozen-cohort.csv').open()));rows=d['rows']
    need(len(selected)==len(selector)==len(rows)==6,'six rows')
    need({(x['inventory_id'],x['cohort'],x['report_md_at_commit'],x['report_json_at_commit']) for x in selected}==
         {(x['inventory_id'],x['cohort'],x['report_md'],x['report_json']) for x in selector}==
         {(x['inventory_id'],x['inventory_cohort'],x['report_md'],x['report_json']) for x in rows},'exact selector')
    idx={x['inventory_id']:x for x in selected};need(len(idx)==6,'unique IDs')
    for r in rows:
        iid=r['inventory_id'];x=idx[iid];mb=gb(r['report_md']);jb=gb(r['report_json']);md=mb.decode();meta=json.loads(jb)
        need(r['title']==x['title'] and r['inventory_cohort']==COHORT,'row inventory')
        need(hashlib.sha256(mb).hexdigest()==r['frozen_md_sha256'] and hashlib.sha256(jb).hexdigest()==r['frozen_json_sha256'],f'{iid}: frozen hashes')
        need(meta['subjects']==r['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),f'{iid}: original subject metadata')
        old=[s for s in meta['subjects'] if s['identity'].get('repository')=='leanprover/lean4' or s['identity'].get('upstream_commit') in OLD.values() or 'leanprover/lean4' in s['identity'].get('toolchain','')]
        need(r['direct_old_lean_subjects_exact']==old,f'{iid}: direct old identities')
        commits=sorted({s['identity'].get('revision') or s['identity'].get('upstream_commit') for s in old if (s['identity'].get('revision') or s['identity'].get('upstream_commit')) in OLD.values()})
        need(r['direct_old_source_commits']==commits and r['old_commit_mentions_in_report']=={c:md.count(c) for c in OLD.values()},f'{iid}: old source commits')
        ex,loc=first_claim(md,iid);need(r['claim_excerpt_exact']==ex and r['claim_locator']==loc,f'{iid}: exact excerpt/locator')
        need(r['prior_comparison_role']==('rechecked_source_claim' if iid=='R462' else 'historical_evidence'),f'{iid}: source role')
        need(r['target']=={'repository':'leanprover/lean4','tag':'v4.34.1','tag_ref_type':'lightweight','revision':NEW,'lake_source_same_repository':True},f'{iid}: target')
        need((r['rechecked_source_clause'] is not None)==(iid=='R462'),f'{iid}: selected source recheck')
        need(r['full_claim_at_target']=='unresolved' and r['current_runtime_result']=='unexecuted_in_this_review' and r['anneal_product_result']=='unassessed',f'{iid}: separate outcomes')
        need(r['old_source_snapshot_sha256'] is None and r['new_source_snapshot_sha256'] is None,f'{iid}: snapshot hashes')
    need(idx['R462']['inventory_id']=='R462','R462 present')
    print('OK: six frozen prior-comparison rows; seven additions; one narrow source clause rechecked; six full claims unresolved, runtime unexecuted')
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL:',e,file=sys.stderr);raise
