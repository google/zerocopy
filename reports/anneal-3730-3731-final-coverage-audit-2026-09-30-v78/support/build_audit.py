#!/usr/bin/env python3
"""Build v78 from published v77 and the exact post-v77 corpus delta."""
import csv, hashlib, json, subprocess
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
REPORTS=ROOT/'reports'
OLD=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-30-v77'/'support'
PARENT='bdc6c4706d89a710b2ff8925de2eb26b7f97c55d'
V77_COMMIT='d8ebe60bc920363d4e43d95713e7e6a2de5363d7'
FIELDS=('v78_status','v78_gate_categories','v78_specific_remaining_delta','v78_scope_assessment','v78_review_package','v78_new_evidence_packages','v78_evidence_files','v78_next_prerequisite','v78_evidence_relation','v78_linked_source_ids')
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
    assert git('cat-file','-t',V77_COMMIT)=='commit'
    sources=json.loads((HERE/'source-map-v78.json').read_text())
    changed=git('diff','--name-only',V77_COMMIT,PARENT,'--','reports').splitlines()
    packages=sorted({Path(x).parent.name for x in changed if x.endswith('/REPORT.json')})
    assert sorted(sources)==packages and len(packages)==1
    prior_map=json.loads((REPORTS/'anneal-3731-source-spec-synthesis-2026-09-30'/'support/id-map.json').read_text())
    mapping={i:[p for p,s in sources.items() if s['classification']=='source_review_v67_analog' and set(s['predecessors'])&set(old)] for i,old in prior_map.items()}
    mapping={i:p for i,p in mapping.items() if p}
    cross=readcsv(OLD/'3730-crosswalk-final-v77.csv')
    dest={r['3730_id']:r['3731_destinations'].split(';') for r in cross}
    assert len(cross)==len(dest)==174 and sum(map(len,dest.values()))==345
    old=json.loads((OLD/'row-challenge-v77.json').read_text())
    assert len(old)==333 and len({r['id'] for r in old})==333
    new=[]
    for prior in old:
        r=dict(prior);item=r['id']
        links=([item] if item in mapping else [x for x in dest.get(item,[]) if x in mapping])
        packs=sorted({p for i in links for p in mapping[i]})
        if prior['kind']=='investigation' and packs:
            relation='newer source review context only'
            assessment='Post-v77 version/source review of inherited source/spec analogs; no Anneal product execution, full claim revalidation, gate or residual change.'
        elif prior['kind']=='suggestion' and packs:
            relation='newer source review context via exact destination links'
            assessment='Post-v77 source review context through inherited #3731 destinations '+', '.join(links)+'; no direct suggestion execution or coverage claim.'
        else:
            relation='no mapped v78 source-review evidence'
            assessment='The post-v77 package provides no exact mapped new evidence for this row; inherited disposition and residual remain.'
        r.update({'v78_status':prior['v77_status'],'v78_gate_categories':prior['v77_gate_categories'],
          'v78_specific_remaining_delta':prior['v77_specific_remaining_delta'],
          'v78_scope_assessment':assessment,'v78_review_package':HERE.parent.name if packs else prior['v77_review_package'],
          'v78_new_evidence_packages':packs,
          'v78_evidence_files':[f'reports/{p}/REPORT.md' for p in packs],
          'v78_next_prerequisite':prior['v77_next_prerequisite'],'v78_evidence_relation':relation,
          'v78_linked_source_ids':links})
        new.append(r)
    (HERE/'row-challenge-v78.json').write_text(json.dumps(new,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
    byid={r['id']:r for r in new}
    def extend(a,b,key):
        rows=readcsv(OLD/a)
        for r in rows:
            src=byid[r[key]]
            for f in FIELDS:r[f]=';'.join(src[f]) if isinstance(src[f],list) else src[f]
        writecsv(HERE/b,rows)
        return rows
    inv=extend('investigation-final-v77.csv','investigation-final-v78.csv','id')
    sug=extend('3730-crosswalk-final-v77.csv','3730-crosswalk-final-v78.csv','3730_id')
    assert (len(inv),len(sug))==(159,174)
    (HERE/'live-issue-snapshot-v78.json').write_bytes((OLD/'live-issue-snapshot-v77.json').read_bytes())
    inventory=[]
    for package in [OLD.parent.name,*packages]:
        for p in sorted((REPORTS/package).rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':
                inventory.append({'path':p.relative_to(ROOT).as_posix(),'sha256':sha(p),'size':p.stat().st_size})
    writecsv(HERE/'source-package-inventory-v78.csv',inventory)
    context_i=sorted(i for i in mapping)
    context_s=[r['id'] for r in new if r['kind']=='suggestion' and r['v78_linked_source_ids']]
    v={'reference_tip_at_start':PARENT,'v77_published_commit':V77_COMMIT,
      'v49_published_commit':git('log','--format=%H','--diff-filter=A','--','reports/anneal-3730-3731-final-coverage-audit-2026-09-30-v49/REPORT.md').splitlines()[0],
      'source_reference_package':OLD.parent.name,'new_report_packages':packages,
      'source_review_context_packages':sorted(p for p,s in sources.items() if s['classification']=='source_review_v67_analog'),
      'inventory_only_packages':sorted(p for p,s in sources.items() if s['classification']!='source_review_v67_analog'),
      'row_count':len(new),'investigation_count':len(inv),'suggestion_count':len(sug),'suggestion_destination_links':sum(map(len,dest.values())),
      'context_investigation_ids':context_i,'context_suggestion_ids':context_s,
      'changed_status_ids':[],'changed_gate_ids':[],'changed_prerequisite_ids':[],'changed_residual_ids':[],
      'status_counts':{'investigations':dict(Counter(r['status'] for r in inv)),'suggestions':dict(Counter(r['status'] for r in sug))},
      'inventory_files':len(inventory),'catalog_at_parent_sha256':sha(ROOT/'CATALOG.json'),
      'input_sha256':{f'v77/{name}':sha(OLD/name) for name in ['row-challenge-v77.json','investigation-final-v77.csv','3730-crosswalk-final-v77.csv','live-issue-snapshot-v77.json','validation-v77.json']},
      'source_map_sha256':sha(HERE/'source-map-v78.json'),
      'generated_sha256':{name:sha(HERE/name) for name in ['row-challenge-v78.json','investigation-final-v78.csv','3730-crosswalk-final-v78.csv','live-issue-snapshot-v78.json','source-package-inventory-v78.csv']}}
    (HERE/'validation-v78.json').write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'rows':len(new),'context_investigations':len(context_i),'context_suggestions':len(context_s),'inventory_files':len(inventory),'packages':len(packages)},sort_keys=True))
if __name__=='__main__':main()
