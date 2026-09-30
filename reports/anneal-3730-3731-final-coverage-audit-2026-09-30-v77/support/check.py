#!/usr/bin/env python3
"""Offline v77 preservation, source-scope, and frozen-corpus checker."""
import csv, hashlib, json, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPORTS=ROOT/'reports'
OLD=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v76'/'support'
V49=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v49'/'support'
PARENT='1a73769318280689985be655c67693ac59b56cae'
V76_COMMIT='47d8250bff3ea17f1fbb4340370032e03692617b'
V49_COMMIT='4db5d007205b9b1a3967f0f05b4b08d49c6563e1'
FIELDS=('v77_status','v77_gate_categories','v77_specific_remaining_delta','v77_scope_assessment','v77_review_package','v77_new_evidence_packages','v77_evidence_files','v77_next_prerequisite','v77_evidence_relation','v77_linked_source_ids')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def main():
    v=json.loads((HERE/'validation-v77.json').read_text())
    sources=json.loads((HERE/'source-map-v77.json').read_text())
    assert (v['reference_tip_at_start'],v['v76_published_commit'],v['v49_published_commit'])==(PARENT,V76_COMMIT,V49_COMMIT)
    assert git('cat-file','-t',PARENT)==git('cat-file','-t',V76_COMMIT)==git('cat-file','-t',V49_COMMIT)=='commit'
    assert git('merge-base','--is-ancestor',V49_COMMIT,V76_COMMIT) == ''
    assert git('merge-base','--is-ancestor',V76_COMMIT,PARENT) == ''
    # The original corpus hash is checked from the parent Git object, independent of the regenerated candidate catalog.
    parent_catalog=subprocess.check_output(['git','show',f'{PARENT}:CATALOG.json'],cwd=ROOT)
    assert hashlib.sha256(parent_catalog).hexdigest()==v['catalog_at_parent_sha256']
    assert (v['row_count'],v['investigation_count'],v['suggestion_count'],v['suggestion_destination_links'])==(333,159,174,345)
    assert v['changed_status_ids']==v['changed_gate_ids']==v['changed_prerequisite_ids']==v['changed_residual_ids']==[]
    assert len(sources)==1 and sorted(sources)==v['new_report_packages']
    grouped=sources['sel4-compcert-everest-current-source-review']
    assert grouped['mapped_report_ids']==['R507']
    assert grouped['inventory_only_report_ids']==['R578']
    assert grouped['inventory_only_report_paths']==['reports/verified-compiler-pass-composition-compcert-3-18-popl-2008/REPORT.md']
    assert not any(grouped['inventory_only_report_paths'][0].split('/')[1] in xs for xs in json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text()).values())
    actual=git('diff','--name-only',V76_COMMIT,PARENT,'--','reports').splitlines()
    assert sorted({Path(x).parent.name for x in actual if x.endswith('/REPORT.json')})==v['new_report_packages']
    assert v['source_review_context_packages']==sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog')
    assert v['inventory_only_packages']==sorted(p for p,s in sources.items() if s['classification']!='source_review_v67_analog')
    for key,digest in v['input_sha256'].items():assert sha(OLD/key[4:])==digest,key
    assert sha(HERE/'source-map-v77.json')==v['source_map_sha256']
    for name,digest in v['generated_sha256'].items():assert sha(HERE/name)==digest,name
    assert (HERE/'live-issue-snapshot-v77.json').read_bytes()==(OLD/'live-issue-snapshot-v76.json').read_bytes()
    prior_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    mapping={i:sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog' and set(s['predecessors'])&set(old)) for i,old in prior_map.items()}
    mapping={i:p for i,p in mapping.items() if p}
    assert sorted(mapping)==v['context_investigation_ids']
    for p,s in sources.items():
        assert (REPORTS/p/'REPORT.md').is_file() and (REPORTS/p/'REPORT.json').is_file()
        if s['classification']=='source_review_v67_analog':
            assert s['predecessors'] and all(any(x in old for old in prior_map.values()) for x in s['predecessors'])
        else:assert not s['predecessors']
    old=json.loads((OLD/'row-challenge-v76.json').read_text())
    old49=json.loads((V49/'row-challenge-v49.json').read_text())
    new=json.loads((HERE/'row-challenge-v77.json').read_text())
    assert len(old49)==len(old)==len(new)==333
    assert [r['id'] for r in old49]==[r['id'] for r in old]==[r['id'] for r in new]
    assert {r['id'] for r in new if r['kind']=='investigation'}=={f'I{i:03}' for i in range(1,160)}
    cross=rows(OLD/'3730-crosswalk-final-v76.csv')
    dest={r['3730_id']:r['3731_destinations'].split(';') for r in cross}
    assert len(dest)==174 and sum(map(len,dest.values()))==345
    context_s=[]
    for a,b,c in zip(old49,old,new):
        item=c['id']
        assert all(c[k]==val for k,val in b.items()),item
        assert all(c[k]==val for k,val in a.items()),item
        assert (c['v77_status'],c['v77_gate_categories'],c['v77_specific_remaining_delta'],c['v77_next_prerequisite'])==(b['v76_status'],b['v76_gate_categories'],b['v76_specific_remaining_delta'],b['v76_next_prerequisite']),item
        links=[item] if item in mapping else [x for x in dest.get(item,[]) if x in mapping]
        packs=sorted({p for i in links for p in mapping[i]})
        assert c['v77_linked_source_ids']==links and c['v77_new_evidence_packages']==packs,item
        assert c['v77_evidence_files']==[f'reports/{p}/REPORT.md' for p in packs],item
        assert c['v77_review_package']==(HERE.parent.name if packs else b['v76_review_package']),item
        assert all((ROOT/p).is_file() for p in c['v77_evidence_files'])
        if c['kind']=='suggestion' and packs:context_s.append(item)
    assert context_s==v['context_suggestion_ids'] and len(context_s)==1
    byid={r['id']:r for r in new}
    for name,oldname,key,n in [('investigation-final-v77.csv','investigation-final-v76.csv','id',159),('3730-crosswalk-final-v77.csv','3730-crosswalk-final-v76.csv','3730_id',174)]:
        a,b=rows(HERE/name),rows(OLD/oldname)
        assert len(a)==len(b)==n and [r[key] for r in a]==[r[key] for r in b]
        for x,y in zip(a,b):
            assert all(x[k]==val for k,val in y.items()),x[key]
            src=byid[x[key]]
            for f in FIELDS:
                value=src[f]
                assert x[f]==(';'.join(value) if isinstance(value,list) else value),(x[key],f)
            assert x['status']==x['v77_status']
    inventory=rows(HERE/'source-package-inventory-v77.csv')
    expected=[]
    for package in [OLD.parent.name,*v['new_report_packages']]:
        for p in sorted((REPORTS/package).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':expected.append(p.relative_to(ROOT).as_posix())
    assert len(inventory)==v['inventory_files'] and [r['path'] for r in inventory]==expected
    assert all(sha(ROOT/r['path'])==r['sha256'] and (ROOT/r['path']).stat().st_size==int(r['size']) for r in inventory)
    meta=json.loads((HERE.parent/'REPORT.json').read_text())
    assert meta['subjects'][0]['identity']['reference_parent']==PARENT
    assert meta['subjects'][1]['identity']['source_inventory_sha256']==sha(HERE/'source-package-inventory-v77.csv')
    print('PASS: v77 frozen parent, v49→v76→v77 lineage, 333 inherited rows, 345 links, 1 package, 39 inventory files')
if __name__=='__main__':main()
