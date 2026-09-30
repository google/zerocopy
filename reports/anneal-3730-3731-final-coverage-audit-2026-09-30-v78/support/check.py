#!/usr/bin/env python3
"""Offline v78 preservation, source-scope, and frozen-corpus checker."""
import csv, hashlib, json, subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPORTS=ROOT/'reports'
OLD=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v77'/'support'
V49=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v49'/'support'
PARENT='bdc6c4706d89a710b2ff8925de2eb26b7f97c55d'
V77_COMMIT='d8ebe60bc920363d4e43d95713e7e6a2de5363d7'
V49_COMMIT='4db5d007205b9b1a3967f0f05b4b08d49c6563e1'
FIELDS=('v78_status','v78_gate_categories','v78_specific_remaining_delta','v78_scope_assessment','v78_review_package','v78_new_evidence_packages','v78_evidence_files','v78_next_prerequisite','v78_evidence_relation','v78_linked_source_ids')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def main():
    v=json.loads((HERE/'validation-v78.json').read_text())
    sources=json.loads((HERE/'source-map-v78.json').read_text())
    assert (v['reference_tip_at_start'],v['v77_published_commit'],v['v49_published_commit'])==(PARENT,V77_COMMIT,V49_COMMIT)
    assert git('cat-file','-t',PARENT)==git('cat-file','-t',V77_COMMIT)==git('cat-file','-t',V49_COMMIT)=='commit'
    assert git('merge-base','--is-ancestor',V49_COMMIT,V77_COMMIT) == ''
    assert git('merge-base','--is-ancestor',V77_COMMIT,PARENT) == ''
    # The original corpus hash is checked from the parent Git object, independent of the regenerated candidate catalog.
    parent_catalog=subprocess.check_output(['git','show',f'{PARENT}:CATALOG.json'],cwd=ROOT)
    assert hashlib.sha256(parent_catalog).hexdigest()==v['catalog_at_parent_sha256']
    assert (v['row_count'],v['investigation_count'],v['suggestion_count'],v['suggestion_destination_links'])==(333,159,174,345)
    assert v['changed_status_ids']==v['changed_gate_ids']==v['changed_prerequisite_ids']==v['changed_residual_ids']==[]
    assert len(sources)==1 and sorted(sources)==v['new_report_packages']
    review=sources['redleaf-linux-current-source-review']
    assert review['mapped_report_ids']==['R511']
    assert review['mapped_investigation_ids']==['I007','I159']
    assert review['explicitly_unmapped_investigation_ids']==['I092']
    matrix=json.loads((REPORTS/'redleaf-linux-current-source-review'/'support/matrix.json').read_text())
    assert matrix['inventory_id']=='R511'
    assert matrix['report_md']=='reports/redleaf-mixed-language-isolation-boundaries-2020-2026/REPORT.md'
    published_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    assert sorted(i for i,paths in published_map.items() if review['predecessors'][0] in paths)==review['mapped_investigation_ids']
    assert 'I092' not in published_map
    actual=git('diff','--name-only',V77_COMMIT,PARENT,'--','reports').splitlines()
    assert sorted({Path(x).parent.name for x in actual if x.endswith('/REPORT.json')})==v['new_report_packages']
    assert v['source_review_context_packages']==sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog')
    assert v['inventory_only_packages']==sorted(p for p,s in sources.items() if s['classification']!='source_review_v67_analog')
    for key,digest in v['input_sha256'].items():assert sha(OLD/key[4:])==digest,key
    assert sha(HERE/'source-map-v78.json')==v['source_map_sha256']
    for name,digest in v['generated_sha256'].items():assert sha(HERE/name)==digest,name
    assert (HERE/'live-issue-snapshot-v78.json').read_bytes()==(OLD/'live-issue-snapshot-v77.json').read_bytes()
    prior_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    mapping={i:sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog' and set(s['predecessors'])&set(old)) for i,old in prior_map.items()}
    mapping={i:p for i,p in mapping.items() if p}
    assert sorted(mapping)==v['context_investigation_ids']
    for p,s in sources.items():
        assert (REPORTS/p/'REPORT.md').is_file() and (REPORTS/p/'REPORT.json').is_file()
        if s['classification']=='source_review_v67_analog':
            assert s['predecessors'] and all(any(x in old for old in prior_map.values()) for x in s['predecessors'])
        else:assert not s['predecessors']
    old=json.loads((OLD/'row-challenge-v77.json').read_text())
    old49=json.loads((V49/'row-challenge-v49.json').read_text())
    new=json.loads((HERE/'row-challenge-v78.json').read_text())
    assert len(old49)==len(old)==len(new)==333
    assert [r['id'] for r in old49]==[r['id'] for r in old]==[r['id'] for r in new]
    assert {r['id'] for r in new if r['kind']=='investigation'}=={f'I{i:03}' for i in range(1,160)}
    cross=rows(OLD/'3730-crosswalk-final-v77.csv')
    dest={r['3730_id']:r['3731_destinations'].split(';') for r in cross}
    assert len(dest)==174 and sum(map(len,dest.values()))==345
    context_s=[]
    for a,b,c in zip(old49,old,new):
        item=c['id']
        assert all(c[k]==val for k,val in b.items()),item
        assert all(c[k]==val for k,val in a.items()),item
        assert (c['v78_status'],c['v78_gate_categories'],c['v78_specific_remaining_delta'],c['v78_next_prerequisite'])==(b['v77_status'],b['v77_gate_categories'],b['v77_specific_remaining_delta'],b['v77_next_prerequisite']),item
        links=[item] if item in mapping else [x for x in dest.get(item,[]) if x in mapping]
        packs=sorted({p for i in links for p in mapping[i]})
        assert c['v78_linked_source_ids']==links and c['v78_new_evidence_packages']==packs,item
        assert c['v78_evidence_files']==[f'reports/{p}/REPORT.md' for p in packs],item
        assert c['v78_review_package']==(HERE.parent.name if packs else b['v77_review_package']),item
        assert all((ROOT/p).is_file() for p in c['v78_evidence_files'])
        if c['kind']=='suggestion' and packs:context_s.append(item)
    assert context_s==v['context_suggestion_ids'] and len(context_s)==14
    byid={r['id']:r for r in new}
    for name,oldname,key,n in [('investigation-final-v78.csv','investigation-final-v77.csv','id',159),('3730-crosswalk-final-v78.csv','3730-crosswalk-final-v77.csv','3730_id',174)]:
        a,b=rows(HERE/name),rows(OLD/oldname)
        assert len(a)==len(b)==n and [r[key] for r in a]==[r[key] for r in b]
        for x,y in zip(a,b):
            assert all(x[k]==val for k,val in y.items()),x[key]
            src=byid[x[key]]
            for f in FIELDS:
                value=src[f]
                assert x[f]==(';'.join(value) if isinstance(value,list) else value),(x[key],f)
            assert x['status']==x['v78_status']
    inventory=rows(HERE/'source-package-inventory-v78.csv')
    expected=[]
    for package in [OLD.parent.name,*v['new_report_packages']]:
        for p in sorted((REPORTS/package).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':expected.append(p.relative_to(ROOT).as_posix())
    assert len(inventory)==v['inventory_files'] and [r['path'] for r in inventory]==expected
    assert all(sha(ROOT/r['path'])==r['sha256'] and (ROOT/r['path']).stat().st_size==int(r['size']) for r in inventory)
    meta=json.loads((HERE.parent/'REPORT.json').read_text())
    assert meta['subjects'][0]['identity']['reference_parent']==PARENT
    assert meta['subjects'][1]['identity']['source_inventory_sha256']==sha(HERE/'source-package-inventory-v78.csv')
    print('PASS: v78 frozen parent, v49→v77→v78 lineage, 333 inherited rows, 345 links, 1 package, 38 inventory files')
if __name__=='__main__':main()
