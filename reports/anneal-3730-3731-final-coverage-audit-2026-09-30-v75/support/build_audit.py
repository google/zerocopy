#!/usr/bin/env python3
"""Build v75 from published v74 and the exact post-v74 corpus delta."""
import csv, hashlib, json, subprocess
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPORTS=ROOT/'reports'
OLD=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v74'/'support'
PARENT='b78cc3c330fb54d8bce1b769e33fe785c2df3b10'
V74_COMMIT='ca4e34659fadfb1ad24084db833adae9ffd8eb05'
FIELDS=('v75_status','v75_gate_categories','v75_specific_remaining_delta','v75_scope_assessment','v75_review_package','v75_new_evidence_packages','v75_evidence_files','v75_next_prerequisite','v75_evidence_relation','v75_linked_source_ids')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def readcsv(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def writecsv(p,rows):
    with p.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def main():
    assert git('rev-parse','HEAD')==PARENT
    assert git('cat-file','-t',PARENT)=='commit'
    assert git('cat-file','-t',V74_COMMIT)=='commit'
    sources=json.loads((HERE/'source-map-v75.json').read_text())
    changed=git('diff','--name-only',V74_COMMIT,PARENT,'--','reports').splitlines()
    packages=sorted({Path(x).parent.name for x in changed if x.endswith('/REPORT.json')})
    assert sorted(sources)==packages and len(packages)==1
    prior_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    mapping={i:[p for p,s in sources.items() if s['classification']=='source_review_v67_analog' and set(s['predecessors'])&set(old)] for i,old in prior_map.items()}
    mapping={i:p for i,p in mapping.items() if p}
    cross=readcsv(OLD/'3730-crosswalk-final-v74.csv')
    dest={r['3730_id']:r['3731_destinations'].split(';') for r in cross}
    assert len(cross)==len(dest)==174 and sum(map(len,dest.values()))==345
    old=json.loads((OLD/'row-challenge-v74.json').read_text())
    assert len(old)==333 and len({r['id'] for r in old})==333
    new=[]
    for prior in old:
        r=dict(prior);item=r['id']
        links=([item] if item in mapping else [x for x in dest.get(item,[]) if x in mapping])
        packs=sorted({p for i in links for p in mapping[i]})
        if prior['kind']=='investigation' and packs:
            relation='newer source review context only'
            assessment='Post-v74 version/source review of inherited source/spec analogs; no Anneal product execution, full claim revalidation, gate or residual change.'
        elif prior['kind']=='suggestion' and packs:
            relation='newer source review context via exact destination links'
            assessment='Post-v74 source review context through inherited #3731 destinations '+', '.join(links)+'; no direct suggestion execution or coverage claim.'
        else:
            relation='no mapped v75 source-review evidence'
            assessment='The post-v74 package provides no exact mapped new evidence for this row; inherited disposition and residual remain.'
        r.update({'v75_status':prior['v74_status'],'v75_gate_categories':prior['v74_gate_categories'],
          'v75_specific_remaining_delta':prior['v74_specific_remaining_delta'],
          'v75_scope_assessment':assessment,'v75_review_package':HERE.parent.name if packs else prior['v74_review_package'],
          'v75_new_evidence_packages':packs,
          'v75_evidence_files':[f'reports/{p}/REPORT.md' for p in packs],
          'v75_next_prerequisite':prior['v74_next_prerequisite'],'v75_evidence_relation':relation,
          'v75_linked_source_ids':links})
        new.append(r)
    (HERE/'row-challenge-v75.json').write_text(json.dumps(new,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
    byid={r['id']:r for r in new}
    def extend(a,b,key):
        rows=readcsv(OLD/a)
        for r in rows:
            src=byid[r[key]]
            for f in FIELDS:r[f]=';'.join(src[f]) if isinstance(src[f],list) else src[f]
        writecsv(HERE/b,rows)
        return rows
    inv=extend('investigation-final-v74.csv','investigation-final-v75.csv','id')
    sug=extend('3730-crosswalk-final-v74.csv','3730-crosswalk-final-v75.csv','3730_id')
    assert (len(inv),len(sug))==(159,174)
    (HERE/'live-issue-snapshot-v75.json').write_bytes((OLD/'live-issue-snapshot-v74.json').read_bytes())
    inventory=[]
    for package in [OLD.parent.name,*packages]:
        for p in sorted((REPORTS/package).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':
                inventory.append({'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p),'size':p.stat().st_size})
    writecsv(HERE/'source-package-inventory-v75.csv',inventory)
    context_i=sorted(i for i in mapping)
    context_s=[r['id'] for r in new if r['kind']=='suggestion' and r['v75_linked_source_ids']]
    v={'reference_tip_at_start':PARENT,'v74_published_commit':V74_COMMIT,
      'v49_published_commit':git('log','--format=%H','--diff-filter=A','--','reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v49/REPORT.md').splitlines()[0],
      'source_reference_package':OLD.parent.name,'new_report_packages':packages,
      'source_review_context_packages':sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog'),
      'inventory_only_packages':sorted(p for p,s in sources.items() if s['classification']!='source_review_v67_analog'),
      'row_count':len(new),'investigation_count':len(inv),'suggestion_count':len(sug),'suggestion_destination_links':sum(map(len,dest.values())),
      'context_investigation_ids':context_i,'context_suggestion_ids':context_s,
      'changed_status_ids':[],'changed_gate_ids':[],'changed_prerequisite_ids':[],'changed_residual_ids':[],
      'status_counts':{'investigations':dict(Counter(r['status'] for r in inv)),'suggestions':dict(Counter(r['status'] for r in sug))},
      'inventory_files':len(inventory),'catalog_at_parent_sha256':sha(ROOT/'CATALOG.json'),
      'input_sha256':{f'v74/{name}':sha(OLD/name) for name in ['row-challenge-v74.json','investigation-final-v74.csv','3730-crosswalk-final-v74.csv','live-issue-snapshot-v74.json','validation-v74.json']},
      'source_map_sha256':sha(HERE/'source-map-v75.json'),
      'generated_sha256':{name:sha(HERE/name) for name in ['row-challenge-v75.json','investigation-final-v75.csv','3730-crosswalk-final-v75.csv','live-issue-snapshot-v75.json','source-package-inventory-v75.csv']}}
    (HERE/'validation-v75.json').write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'rows':len(new),'context_investigations':len(context_i),'context_suggestions':len(context_s),'inventory_files':len(inventory),'packages':len(packages)},sort_keys=True))
if __name__=='__main__':main()
