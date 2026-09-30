#!/usr/bin/env python3
"""Offline v79 preservation, source-scope, and frozen-corpus checker."""
import csv, hashlib, json, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPORTS=ROOT/'reports'
OLD=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v78'/'support'
V49=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v49'/'support'
PARENT='037531430436ec7d21966544e72ac7d7c60b1c24'
V78_COMMIT='2ab4fa557cc4d42351aaec1d89d3e8e7801911b5'
V49_COMMIT='4db5d007205b9b1a3967f0f05b4b08d49c6563e1'
FIELDS=('v79_status','v79_gate_categories','v79_specific_remaining_delta','v79_scope_assessment','v79_review_package','v79_new_evidence_packages','v79_evidence_files','v79_next_prerequisite','v79_evidence_relation','v79_linked_source_ids')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def main():
    v=json.loads((HERE/'validation-v79.json').read_text())
    sources=json.loads((HERE/'source-map-v79.json').read_text())
    assert (v['reference_tip_at_start'],v['v78_published_commit'],v['v49_published_commit'])==(PARENT,V78_COMMIT,V49_COMMIT)
    assert git('cat-file','-t',PARENT)==git('cat-file','-t',V78_COMMIT)==git('cat-file','-t',V49_COMMIT)=='commit'
    assert git('merge-base','--is-ancestor',V49_COMMIT,V78_COMMIT) == ''
    assert git('merge-base','--is-ancestor',V78_COMMIT,PARENT) == ''
    # The original corpus hash is checked from the parent Git object, independent of the regenerated candidate catalog.
    parent_catalog=subprocess.check_output(['git','show',f'{PARENT}:CATALOG.json'],cwd=ROOT)
    assert hashlib.sha256(parent_catalog).hexdigest()==v['catalog_at_parent_sha256']
    assert (v['row_count'],v['investigation_count'],v['suggestion_count'],v['suggestion_destination_links'])==(333,159,174,345)
    assert v['changed_status_ids']==v['changed_gate_ids']==v['changed_prerequisite_ids']==v['changed_residual_ids']==[]
    assert len(sources)==1 and sorted(sources)==v['new_report_packages']
    review=sources['mathlib-430rc2-to-4341-cache-source-review']
    assert review['classification']=='version_source_review_unmapped' and review['predecessors']==[]
    cohort=rows(REPORTS/'mathlib-430rc2-to-4341-cache-source-review'/'support/frozen-cohort.csv')
    matrix=json.loads((REPORTS/'mathlib-430rc2-to-4341-cache-source-review'/'support/matrix.json').read_text())
    assert [r['inventory_id'] for r in cohort]==review['frozen_report_ids']==['R495','R496','R497','R498']
    assert [r['report_md'] for r in cohort]==review['frozen_report_paths']==[r['report_md'] for r in matrix['rows']]
    published_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    assert all(path.split('/')[1] not in predecessors for path in review['frozen_report_paths'] for predecessors in published_map.values())
    actual=git('diff','--name-only',V78_COMMIT,PARENT,'--','reports').splitlines()
    assert sorted({Path(x).parent.name for x in actual if x.endswith('/REPORT.json')})==v['new_report_packages']
    assert v['source_review_context_packages']==sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog')
    assert v['inventory_only_packages']==sorted(p for p,s in sources.items() if s['classification']!='source_review_v67_analog')
    for key,digest in v['input_sha256'].items():assert sha(OLD/key[4:])==digest,key
    assert sha(HERE/'source-map-v79.json')==v['source_map_sha256']
    for name,digest in v['generated_sha256'].items():assert sha(HERE/name)==digest,name
    assert (HERE/'live-issue-snapshot-v79.json').read_bytes()==(OLD/'live-issue-snapshot-v78.json').read_bytes()
    prior_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    mapping={i:sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog' and set(s['predecessors'])&set(old)) for i,old in prior_map.items()}
    mapping={i:p for i,p in mapping.items() if p}
    assert sorted(mapping)==v['context_investigation_ids']
    for p,s in sources.items():
        assert (REPORTS/p/'REPORT.md').is_file() and (REPORTS/p/'REPORT.json').is_file()
        if s['classification']=='source_review_v67_analog':
            assert s['predecessors'] and all(any(x in old for old in prior_map.values()) for x in s['predecessors'])
        else:assert not s['predecessors']
    old=json.loads((OLD/'row-challenge-v78.json').read_text())
    old49=json.loads((V49/'row-challenge-v49.json').read_text())
    new=json.loads((HERE/'row-challenge-v79.json').read_text())
    assert len(old49)==len(old)==len(new)==333
    assert [r['id'] for r in old49]==[r['id'] for r in old]==[r['id'] for r in new]
    assert {r['id'] for r in new if r['kind']=='investigation'}=={f'I{i:03}' for i in range(1,160)}
    cross=rows(OLD/'3730-crosswalk-final-v78.csv')
    dest={r['3730_id']:r['3731_destinations'].split(';') for r in cross}
    assert len(dest)==174 and sum(map(len,dest.values()))==345
    context_s=[]
    for a,b,c in zip(old49,old,new):
        item=c['id']
        assert all(c[k]==val for k,val in b.items()),item
        assert all(c[k]==val for k,val in a.items()),item
        assert (c['v79_status'],c['v79_gate_categories'],c['v79_specific_remaining_delta'],c['v79_next_prerequisite'])==(b['v78_status'],b['v78_gate_categories'],b['v78_specific_remaining_delta'],b['v78_next_prerequisite']),item
        links=[item] if item in mapping else [x for x in dest.get(item,[]) if x in mapping]
        packs=sorted({p for i in links for p in mapping[i]})
        assert c['v79_linked_source_ids']==links and c['v79_new_evidence_packages']==packs,item
        assert c['v79_evidence_files']==[f'reports/{p}/REPORT.md' for p in packs],item
        assert c['v79_review_package']==(HERE.parent.name if packs else b['v78_review_package']),item
        assert all((ROOT/p).is_file() for p in c['v79_evidence_files'])
        if c['kind']=='suggestion' and packs:context_s.append(item)
    assert context_s==v['context_suggestion_ids'] and len(context_s)==0
    byid={r['id']:r for r in new}
    for name,oldname,key,n in [('investigation-final-v79.csv','investigation-final-v78.csv','id',159),('3730-crosswalk-final-v79.csv','3730-crosswalk-final-v78.csv','3730_id',174)]:
        a,b=rows(HERE/name),rows(OLD/oldname)
        assert len(a)==len(b)==n and [r[key] for r in a]==[r[key] for r in b]
        for x,y in zip(a,b):
            assert all(x[k]==val for k,val in y.items()),x[key]
            src=byid[x[key]]
            for f in FIELDS:
                value=src[f]
                assert x[f]==(';'.join(value) if isinstance(value,list) else value),(x[key],f)
            assert x['status']==x['v79_status']
    inventory=rows(HERE/'source-package-inventory-v79.csv')
    expected=[]
    for package in [OLD.parent.name,*v['new_report_packages']]:
        for p in sorted((REPORTS/package).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':expected.append(p.relative_to(ROOT).as_posix())
    assert len(inventory)==v['inventory_files'] and [r['path'] for r in inventory]==expected
    assert all(sha(ROOT/r['path'])==r['sha256'] and (ROOT/r['path']).stat().st_size==int(r['size']) for r in inventory)
    meta=json.loads((HERE.parent/'REPORT.json').read_text())
    assert meta['subjects'][0]['identity']['reference_parent']==PARENT
    assert meta['subjects'][1]['identity']['source_inventory_sha256']==sha(HERE/'source-package-inventory-v79.csv')
    print('PASS: v79 frozen parent, v49→v78→v79 lineage, 333 inherited rows, 345 links, 1 package, 43 inventory files')
if __name__=='__main__':main()
