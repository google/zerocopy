#!/usr/bin/env python3
"""Offline check of R502/R503 against exact frozen reference Git content."""
import csv, hashlib, json, re, subprocess, sys
from pathlib import Path
BASE=Path(__file__).resolve().parent
BASELINE='ebcdcadb63fefd1e6c0f46cb2030270ae3232837'
FROZEN='85c0dbe51660afbd6a6362eade507f00c49b4ec5'
IDS={'R502','R503'}
def need(ok,why):
    if not ok: raise AssertionError(why)
def git(*args):return subprocess.check_output(['git',*args],stderr=subprocess.DEVNULL)
def gb(p):return git('show',f'{FROZEN}:{p}')
def paths(c):
    need(git('rev-parse',f'{c}^{{commit}}').decode().strip()==c,'exact corpus commit')
    return {p for p in git('ls-tree','-r','--name-only',c,'reports').decode().splitlines() if p.endswith('/REPORT.json')}
def summary(md):
    lines=md.splitlines();i=lines.index('## Summary')+1
    while not lines[i].strip():i+=1
    start=i
    while i<len(lines) and lines[i].strip() and not lines[i].startswith('#'):i+=1
    return {'heading':'## Summary','line':start+1},'\n'.join(lines[start:i])
def main():
    d=json.loads((BASE/'matrix.json').read_text());need(d['schema']==1 and d['baseline_reference_commit']==BASELINE and d['frozen_reference_commit']==FROZEN,'corpus ID')
    need(d['baseline_count']==581 and d['current_count']==590,'corpus counts')
    ib=(BASE/'version-inventory-ebcdcad-581.csv').read_bytes()
    need(hashlib.sha256(ib).hexdigest()==d['baseline_inventory_sha256'],'inventory hash')
    inv=list(csv.DictReader(ib.decode().splitlines()));need(len(inv)==581,'inventory count')
    bp=set((BASE/'baseline-report-paths.txt').read_text().splitlines())
    need(len(bp)==581 and bp==paths(BASELINE)=={x['report_json_at_commit'] for x in inv},'baseline paths')
    fp=paths(FROZEN);adds=d['added_after_baseline'];need(len(fp)==590 and len(adds)==9 and {x['report_json'] for x in adds}==fp-bp and bp<=fp,'nine additions')
    for a in adds:
        need(a['report_md']==a['report_json'].replace('REPORT.json','REPORT.md'),'addition paths')
        need(hashlib.sha256(gb(a['report_json'])).hexdigest()==a['json_sha256'] and hashlib.sha256(gb(a['report_md'])).hexdigest()==a['md_sha256'],'addition hashes')
    sel={x['inventory_id']:x for x in inv if x['inventory_id'] in IDS}
    csvsel=list(csv.DictReader((BASE/'frozen-cohort.csv').open()))
    need(len(sel)==len(csvsel)==len(d['rows'])==2 and {x['inventory_id'] for x in csvsel}==IDS and {x['inventory_id'] for x in d['rows']}==IDS,'exact selector')
    for r in d['rows']:
        x=sel[r['inventory_id']]
        need((r['report_json'],r['report_md'])==(x['report_json_at_commit'],x['report_md_at_commit']),'frozen paths')
        mb=gb(r['report_md']);jb=gb(r['report_json']);md=mb.decode();meta=json.loads(jb)
        need(hashlib.sha256(mb).hexdigest()==r['frozen_md_sha256'] and hashlib.sha256(jb).hexdigest()==r['frozen_json_sha256'],'frozen hashes')
        need(meta['subjects']==r['frozen_subjects_exact']==json.loads(x['exact_pinned_subject_identities_json']),'subject identities')
        need(r['title']==x['title'] and r['cohort']==x['cohort'] and r['inventory_claim_excerpt_exact_or_normalized']==x['claim_or_cell_to_recheck'],'inventory row')
        loc,excerpt=summary(md);need(loc==r['claim_locator'] and excerpt==r['claim_excerpt_exact'] and md.count(excerpt)==1,'exact claim/locator')
        need(r['old_source_blob_sha1_mentions']==sorted(set(re.findall(r'\bblob `([0-9a-f]{40})`',md))),'old blob mentions')
        need(r['current_runtime_result']=='unexecuted_in_this_review' and r['anneal_product_result']=='unassessed','runtime/product separation')
    pins=d['source_pin_graph']
    need(pins['nix_old_R503_commit']=='9bc9ab32a57504f068847af4f8013417476cb1ec' and pins['nix_release']=='2.35.2' and pins['nix_annotated_tag_object']=='a400e1f45939a4e0521f66e76470eea9e8ea666b' and pins['nix_peeled_release_commit']=='2c73b59da29606068c0c98db015dd3a66955525d','Nix pin graph')
    need(pins['guix_release']=='1.5.0' and pins['guix_annotated_tag_object']=='749a73cacad30fd9e149d9086c7e4e4a0b86834b' and pins['guix_peeled_release_commit']=='230aa373f315f247852ee07dff34146e9b480aec','Guix pin graph')
    need(pins['nix_cross_commit_ancestry']=='unverified' and pins['guix_devel_manual_commit']=='unresolved','pin limits')
    statuses={r['inventory_id']:r['source_claim_result'] for r in d['rows']}
    need(statuses=={'R502':'already_current_at_pinned_manual_no_newer_version_delta','R503':'selected_nix_documentation_continuity_full_claim_unresolved'},'source results')
    need(d['old_source_snapshot_sha256'] is None and d['new_source_snapshot_sha256'] is None,'no raw source snapshots')
    print('OK: 2 exact frozen claims; 581/590 corpus; 9 additions; pin graph; separate source/runtime/product limits')
if __name__=='__main__':
    try: main()
    except Exception as e: print('FAIL:',e,file=sys.stderr);raise
