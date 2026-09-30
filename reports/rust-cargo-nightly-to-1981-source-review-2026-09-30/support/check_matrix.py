#!/usr/bin/env python3
"""Offline check of all 51 frozen report claims and current cohort reconciliation.

Run in a reference checkout that contains the frozen d36bc9c commit. The
checker validates local Git objects, not the official remote source pages.
"""
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

BASE=Path(__file__).resolve().parent
FROZEN='d36bc9c6d21837e9881cde82a67ce72af50d415f'
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
STABLE_RUST='48a229ceaefd4985c50990b14116b6d856af0985'
COHORT='Rust/Cargo/rustc nightly-2026-05-31'

def git_bytes(path):
    return subprocess.check_output(['git','show',f'{FROZEN}:{path}'],stderr=subprocess.DEVNULL)

def need(ok,why):
    if not ok:raise AssertionError(why)

def main():
    doc=json.loads((BASE/'matrix.json').read_text())
    need(doc['frozen_reference_commit']==FROZEN,'frozen commit mismatch')
    need(doc['baseline_reference_commit']==BASELINE,'baseline commit mismatch')
    need(doc['cohort']==COHORT,'cohort mismatch')
    need(doc['baseline_count']==581 and doc['current_count']==586,'census count')
    inventory_bytes=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes()
    need(hashlib.sha256(inventory_bytes).hexdigest()==doc['baseline_inventory_sha256'],'baseline inventory SHA-256')
    inventory=list(csv.DictReader(inventory_bytes.decode().splitlines()))
    need(len(inventory)==581,'baseline inventory rows')
    selector=list(csv.DictReader((BASE/'frozen-cohort.csv').open()))
    rows=doc['rows'];need(len(selector)==len(rows)==51,'51-row count')
    need(len({r['inventory_id'] for r in rows})==51,'duplicate row ID')
    need(len({r['report_json'] for r in rows})==51,'duplicate report')
    need(all(x['cohort']==COHORT for x in selector),'mixed selector')
    inventory_selected=[x for x in inventory if x['cohort']==COHORT]
    need(len(inventory_selected)==51,'baseline cohort size')
    need({(x['inventory_id'],x['report_md_at_commit'],x['report_json_at_commit']) for x in inventory_selected}==
         {(x['inventory_id'],x['report_md'],x['report_json']) for x in selector},'selector/inventory mismatch')
    need({(x['inventory_id'],x['report_md'],x['report_json']) for x in selector}==
         {(x['inventory_id'],x['report_md'],x['report_json']) for x in rows},'row/selector mismatch')
    baseline=set((BASE/'baseline-report-paths.txt').read_text().splitlines())
    need(len(baseline)==581 and all(x.endswith('/REPORT.json') for x in baseline),'baseline paths')
    need(baseline=={x['report_json_at_commit'] for x in inventory},'baseline inventory path set')
    baseline_git={p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',BASELINE,'reports'],text=True).splitlines() if p.endswith('/REPORT.json')}
    need(baseline==baseline_git,'baseline path set not frozen Git tree')
    current={p for p in subprocess.check_output(['git','ls-tree','-r','--name-only',FROZEN,'reports'],text=True).splitlines() if p.endswith('/REPORT.json')}
    added={x['report_json'] for x in doc['added_after_baseline']}
    need(len(current)==586 and len(added)==5,'current/added counts')
    need(current-baseline==added and not baseline-current,'unaccounted report additions/removals')
    for x in doc['added_after_baseline']:
        need(hashlib.sha256(git_bytes(x['report_json'])).hexdigest()==x['json_sha256'],'added metadata hash')
        need(hashlib.sha256(git_bytes(x['report_md'])).hexdigest()==x['md_sha256'],'added report hash')
    categories={'selected_source_continuity':0,'already_current':0,'unresolved':0}
    blobs=0
    for r in rows:
        iid=r['inventory_id'];mb=git_bytes(r['report_md']);jb=git_bytes(r['report_json'])
        need(hashlib.sha256(mb).hexdigest()==r['frozen_md_sha256'],f'{iid}: report hash')
        need(hashlib.sha256(jb).hexdigest()==r['frozen_json_sha256'],f'{iid}: metadata hash')
        md=mb.decode();meta=json.loads(jb);lines=md.splitlines()
        need(meta['subjects']==r['frozen_subjects_exact'],f'{iid}: subject identities')
        old_rust=[s for s in meta['subjects'] if s['identity'].get('repository')=='rust-lang/rust']
        old_cargo=[s for s in meta['subjects'] if s['identity'].get('repository')=='rust-lang/cargo']
        need(r['old_rust_subjects_exact']==old_rust and r['old_cargo_subjects_exact']==old_cargo,f'{iid}: component identities')
        expected_links=[]
        for s in old_rust+old_cargo:
            ident=s['identity'];rev=ident.get('revision')
            if isinstance(rev,str) and re.fullmatch(r'[0-9a-f]{40}',rev):
                expected_links.append(f"https://github.com/{ident['repository']}/commit/{rev}")
        need(r['old_commit_links']==expected_links,f'{iid}: commit links')
        mentions=sorted(set(re.findall(r'\bblob\s+`([0-9a-f]{40})`',md)))
        need(r['frozen_source_blob_sha1_mentions']==mentions,f'{iid}: blob mentions')
        blobs+=bool(mentions)
        loc=r['claim_locator'];line=loc['line'];excerpt=r['claim_excerpt_exact']
        need(1<=line<=len(lines) and md.count(excerpt)==1,f'{iid}: excerpt present/unique')
        need('\n'.join(lines[line-1:]).startswith(excerpt) or excerpt in lines[line-1],f'{iid}: line locator')
        heading=next((s.strip() for s in reversed(lines[:line-1]) if s.startswith('#')),lines[0])
        need(heading==loc['heading'],f'{iid}: heading locator')
        need(r['stable_rustc']=={'version':'1.98.1','repository':'rust-lang/rust','revision':STABLE_RUST},f'{iid}: stable rustc')
        need(r['new_rustc_commit_link']==f'https://github.com/rust-lang/rust/commit/{STABLE_RUST}',f'{iid}: new commit link')
        need(r['stable_cargo']=={'version':'1.98.1','repository':'rust-lang/cargo','source_revision':None,'source_revision_status':'unresolved_from_official_release_pages'},f'{iid}: stable Cargo resolution')
        need(r['runtime_current_review']=='unexecuted_in_this_review',f'{iid}: runtime label')
        need(r['old_source_snapshot_sha256'] is None and r['new_source_snapshot_sha256'] is None,f'{iid}: snapshot status')
        need(r['comparison'] in categories,f'{iid}: comparison label')
        expected='selected_source_continuity' if iid=='R559' else 'already_current' if iid=='R240' else 'unresolved'
        need(r['comparison']==expected,f'{iid}: result selection')
        if iid=='R240':
            need(any(s['identity'].get('revision')==STABLE_RUST and s['identity'].get('version')=='1.98.1' for s in old_rust),f'{iid}: already current Rust pin')
            need(any(s['identity'].get('version')=='1.98.1' and 'Cargo' in s['name'] for s in meta['subjects']),f'{iid}: already current Cargo version')
        if iid=='R559':
            need('ff2c18d685b65832c296731f23f1664779b874f2' in mentions,f'{iid}: old source blob')
            need(r['old_source_git_blob_sha1']=='ff2c18d685b65832c296731f23f1664779b874f2',f'{iid}: selected old blob')
        else:need(r['old_source_git_blob_sha1'] is None,f'{iid}: old source blob label')
        categories[r['comparison']]+=1
    need(categories=={'selected_source_continuity':1,'already_current':1,'unresolved':49},'category totals')
    print(f'OK: 51 frozen claims and metadata; {blobs} rows with frozen blob SHA-1 mentions; 5 added reports accounted for; 1 selected source continuity, 1 already current, 49 unresolved; no newer run')

if __name__=='__main__':
    try:main()
    except Exception as exc:
        print(f'FAIL: {exc}',file=sys.stderr)
        raise
