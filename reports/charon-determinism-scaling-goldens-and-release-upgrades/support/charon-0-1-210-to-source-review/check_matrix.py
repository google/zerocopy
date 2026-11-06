#!/usr/bin/env python3
"""Offline verification of the complete 45-row frozen Charon cohort.

This verifies local frozen Git objects and matrix transcription. It deliberately
does not claim to authenticate the linked official remote source pages.
"""
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

BASE=Path(__file__).resolve().parent
FROZEN='2e9db344b6c0e6391ff78655a18b81ecb7e293e1'
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
NEW_CHARON='2804f2dbc349a4c80201f7c528adf70f8d1ee5fa'
OLD_CHARON={'a535e914f74db4fd9e6be7048f4233270d8945c0','0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1'}
COHORTS={'Charon 0.1.210 + Rust nightly-2026-05-31':17,
         'Charon 0.1.210 + Rust/Cargo nightly-2026-05-31':28}

def need(condition,why):
    if not condition:raise AssertionError(why)

def git_bytes(path):
    return subprocess.check_output(['git','show',f'{FROZEN}:{path}'],stderr=subprocess.DEVNULL)

def git_paths(commit):
    need(subprocess.check_output(['git','rev-parse',f'{commit}^{{commit}}'],text=True).strip()==commit,'commit identity')
    return {p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',commit,'reports'],text=True).splitlines() if p.endswith('/REPORT.json')}

def first_claim(md):
    lines=md.splitlines()
    h=next((i for i,s in enumerate(lines) if s.startswith('## ')),None)
    need(h is not None,'missing level-two section')
    i=h+1
    while i<len(lines) and (not lines[i].strip() or lines[i].startswith('#')):i+=1
    start=i
    while i<len(lines) and lines[i].strip() and not lines[i].startswith('#'):i+=1
    need(i>start,'empty first section')
    return '\n'.join(lines[start:i]),start+1,lines[h].strip()

def repo_subjects(subjects,repo):
    return [s for s in subjects if s['identity'].get('repository')==repo]

def main():
    doc=json.loads((BASE/'matrix.json').read_text())
    need(doc['schema']==1 and doc['frozen_reference_commit']==FROZEN and doc['baseline_reference_commit']==BASELINE,'matrix Git identity')
    need(doc['cohorts']==COHORTS and doc['baseline_count']==581 and doc['current_count']==587,'matrix census')
    need(set(doc['old_charon_source_commits'])==OLD_CHARON,'old Charon revision set')
    inventory_bytes=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes()
    need(hashlib.sha256(inventory_bytes).hexdigest()==doc['baseline_inventory_sha256'],'inventory SHA-256')
    inventory=list(csv.DictReader(inventory_bytes.decode().splitlines()))
    need(len(inventory)==581,'baseline inventory rows')
    baseline=set((BASE/'baseline-report-paths.txt').read_text().splitlines())
    need(len(baseline)==581 and baseline=={s['report_json_at_commit'] for s in inventory},'baseline path inventory')
    need(baseline==git_paths(BASELINE),'baseline Git path set')
    current=git_paths(FROZEN)
    additions={a['report_json'] for a in doc['added_after_baseline']}
    need(len(current)==587 and len(additions)==6 and current-baseline==additions and not baseline-current,'current Git reconciliation')
    for a in doc['added_after_baseline']:
        need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md'),'added path pair')
        need(hashlib.sha256(git_bytes(a['report_json'])).hexdigest()==a['json_sha256'],'added metadata hash')
        need(hashlib.sha256(git_bytes(a['report_md'])).hexdigest()==a['md_sha256'],'added report hash')
    selected=[s for s in inventory if s['cohort'] in COHORTS]
    selector=list(csv.DictReader((BASE/'frozen-cohort.csv').open()))
    rows=doc['rows']
    need(len(selected)==len(selector)==len(rows)==45,'45-row count')
    need({c:sum(s['cohort']==c for s in selected) for c in COHORTS}==COHORTS,'17+28 partition')
    need(len({r['inventory_id'] for r in rows})==45 and len({r['report_json'] for r in rows})==45,'unique rows')
    need({(s['inventory_id'],s['cohort'],s['report_md_at_commit'],s['report_json_at_commit']) for s in selected}==
         {(s['inventory_id'],s['cohort'],s['report_md'],s['report_json']) for s in selector},'selector/inventory relation')
    need({(s['inventory_id'],s['cohort'],s['report_md'],s['report_json']) for s in selector}==
         {(r['inventory_id'],r['inventory_cohort'],r['report_md'],r['report_json']) for r in rows},'row/selector relation')
    index={s['inventory_id']:s for s in selected}
    direct={'charon':0,'rust':0,'cargo':0}
    for r in rows:
        iid=r['inventory_id'];inv=index[iid]
        need(r['inventory_cohort']==inv['cohort'] and r['title']==inv['title'],f'{iid}: inventory record')
        mb=git_bytes(r['report_md']);jb=git_bytes(r['report_json'])
        need(hashlib.sha256(mb).hexdigest()==r['frozen_md_sha256'],f'{iid}: Markdown hash')
        need(hashlib.sha256(jb).hexdigest()==r['frozen_json_sha256'],f'{iid}: metadata hash')
        md=mb.decode();subjects=json.loads(jb)['subjects']
        need(subjects==json.loads(inv['exact_pinned_subject_identities_json'])==r['frozen_subjects_exact'],f'{iid}: exact original subjects')
        excerpt,line,heading=first_claim(md)
        need(r['claim_excerpt_exact']==excerpt and r['claim_locator']=={'heading':heading,'line':line},f'{iid}: exact excerpt and locator')
        need(md.count(excerpt)==1,f'{iid}: excerpt unique')
        pg=r['pin_graph']
        charon=repo_subjects(subjects,'AeneasVerif/charon')
        rust=repo_subjects(subjects,'rust-lang/rust')
        cargo=repo_subjects(subjects,'rust-lang/cargo')
        other=[s for s in subjects if s not in charon+rust+cargo]
        need(pg['direct_charon_subjects']==charon and pg['direct_rust_source_subjects']==rust and pg['direct_cargo_source_subjects']==cargo and pg['other_or_composite_subjects']==other,f'{iid}: paired subject graph')
        links=[]
        for s in charon+rust+cargo:
            rev=s['identity'].get('revision')
            if isinstance(rev,str) and re.fullmatch('[0-9a-f]{40}',rev):links.append('https://github.com/'+s['identity']['repository']+'/commit/'+rev)
        need(pg['direct_commit_links']==links,f'{iid}: direct commit links')
        for s in charon:
            need(s['identity'].get('revision') in OLD_CHARON,f'{iid}: unexpected Charon revision')
        direct['charon']+=bool(charon);direct['rust']+=bool(rust);direct['cargo']+=bool(cargo)
        need(r['old_source_git_blob_sha1_mentions']==sorted(set(re.findall(r'\bblob\s+`([0-9a-f]{40})`',md))),f'{iid}: old blob mentions')
        need(r['old_source_snapshot_sha256'] is None and r['new_source_snapshot_sha256'] is None,f'{iid}: unsupported source snapshot hash')
        t=r['target']
        need(t=={'charon_tag':'nightly-2026.09.30','charon_tag_ref_type':'lightweight','charon_source_commit':NEW_CHARON,'charon_package_version':'0.1.274','rust_channel':'nightly-2026-09-17','rust_components':['rustc-dev','llvm-tools','rust-src','miri'],'rustc_source_commit':None,'cargo_source_commit':None,'component_commit_status':'not_resolved_from_inspected_official_sources'},f'{iid}: target identity')
        need(r['source_claim_result']=='unresolved_at_target' and r['current_runtime_result']=='unexecuted_in_this_review' and r['compatibility_result']=='unresolved' and r['anneal_product_result']=='unassessed',f'{iid}: separate outcome bounds')
    print(f'OK: 45 exact frozen rows (17+28); 6 additions; direct Charon/Rust/Cargo subject rows {direct}; all claim results unresolved and current runtime unexecuted')

if __name__=='__main__':
    try:main()
    except Exception as exc:
        print(f'FAIL: {exc}',file=sys.stderr)
        raise
