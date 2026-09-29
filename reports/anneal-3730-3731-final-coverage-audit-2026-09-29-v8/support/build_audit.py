#!/usr/bin/env python3
"""Offline deterministic v8 issue/report coverage audit; no network or source edits."""
from __future__ import annotations
import csv,hashlib,json,re,sys
from collections import Counter,defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
V7=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-29-v7'/'support'
sys.path.insert(0,str(REPORTS.parent/'tools'))
import reference

def sha(b): return hashlib.sha256(b).hexdigest()
def read_csv(p):
    with p.open(newline='') as f: return list(csv.DictReader(f))
def write_csv(p,rows):
    assert rows
    with p.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0])); w.writeheader(); w.writerows(rows)
def inspect(p):
    result=[]
    for f in sorted(x for x in p.rglob('*') if x.is_file()):
        b=f.read_bytes();typ='binary';detail='opaque'
        if f.suffix.lower()=='.json':
            try:json.loads(b);typ='json';detail='parsed'
            except (ValueError,UnicodeDecodeError):typ='json-invalid-specimen';detail='retained raw bytes'
        elif f.suffix.lower()=='.csv':typ='csv';detail=f'{len(read_csv(f))} data rows'
        else:
            try:txt=b.decode();typ='utf8';detail=f'{txt.count(chr(10))} lines'
            except UnicodeDecodeError:pass
        result.append({'package':p.name,'relative_file':f.relative_to(p).as_posix(),
                       'bytes':len(b),'sha256':sha(b),'inspection':typ,'detail':detail})
    return result

def main():
    issue=json.loads((HERE/'issue-scope-snapshot.json').read_text())
    b30=issue['3730']['body'];b31=issue['3731']['body']
    assert len(issue['3730']['comments'])==len(issue['3731']['comments'])==1
    c30=issue['3730']['comments'][0]['body'];c31=issue['3731']['comments'][0]['body']
    heads30=re.findall(r'^### ([A-Z]\d{2})\.',b30,re.M)
    heads31=re.findall(r'^\*\*(I\d{3})\s+[—-]',b31,re.M)+re.findall(r'^\*\*(I\d{3})\s+[—-]',c31,re.M)
    cross_text=c31.split('## Complete #3730 → #3731 crosswalk',1)[1]
    cross_issue=re.findall(r'^\| ([A-Z]\d{2}) \| [^\n]* \| (I\d{3}[^|]*) \|$',cross_text,re.M)
    assert len(heads30)==len(set(heads30))==174
    assert heads31==[f'I{i:03}' for i in range(1,160)]
    assert len(cross_issue)==len({k for k,_ in cross_issue})==174
    assert set(heads30)=={k for k,_ in cross_issue}
    issue_sha={'3730_body':sha(b30.encode()),'3730_comment':sha(c30.encode()),
               '3731_body':sha(b31.encode()),'3731_comment':sha(c31.encode())}
    v7=json.loads((V7/'validation-v7.json').read_text())
    assert issue_sha==v7['issue_sha256'], 'Upstream issue changed; re-audit source required'
    assert issue['3730']['state']=='closed' and issue['3731']['state']=='open'
    prior=read_csv(V7/'investigation-final-v7.csv')
    old_cross=read_csv(V7/'3730-crosswalk-final-v7.csv')
    assert len(prior)==159 and [r['id'] for r in prior]==heads31
    assert len(old_cross)==174 and [r['3730_id'] for r in old_cross]==heads30
    old_map={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue:assert set(re.findall(r'I\d{3}',dest))==old_map[key],key
    scope=json.loads((HERE/'new-package-scope.json').read_text())
    residuals=json.loads((HERE/'residual-overrides.json').read_text())
    assert set(residuals)<=set(heads31)
    prior_cited=set()
    for row in prior:
        for value in row.values():prior_cited.update(re.findall(r'anneal-3730-[a-z0-9-]+',value or ''))
    # Freeze only packages completed at the public issue/report snapshot.
    # Later report packages do not retroactively alter this audit's rebuild.
    all_packages=prior_cited | set(scope)
    out_of_snapshot={'R25 I023 signature/recovery','R26 I070 competing writers/crash injection'}
    assert len(all_packages)==72 and len(prior_cited)==70 and len(scope)==2
    coverage=[]
    for name in sorted(all_packages):
        p=REPORTS/name;report,problems=reference._load_report(p)
        assert report is not None and not problems,(name,problems)
        coverage.append({'package':name,'in_v7_ledger':name in prior_cited,'new_in_v8':name in scope,
                         'report_md_sha256':sha((p/'REPORT.md').read_bytes()),
                         'validator':'reference._load_report: valid'})
    write_csv(HERE/'all-package-accounting-v8.csv',coverage)
    mapped=defaultdict(list);review=[];inventory=[]
    for name,data in sorted(scope.items()):
        p=REPORTS/name;files=inspect(p);inventory.extend(files)
        assert all((p/f).is_file() for f in data['evidence_files'])
        for n in data['ids']:
            key=f'I{n:03}';assert key in heads31; mapped[key].append(name)
        review.append({'suite':data['suite'],'package':name,'reviewed_ids':';'.join(f'I{x:03}' for x in data['ids']),
                       'actual_procedure_and_observation':data['method'],'evidence_boundary':data['boundary'],
                       'primary_evidence_files':';'.join(data['evidence_files']),
                       'file_count':len(files),'bytes':sum(int(x['bytes']) for x in files),
                       'validator':'reference._load_report: valid'})
    assert {r['suite'] for r in review}=={f'R{i:02}' for i in range(23,25)}
    write_csv(HERE/'new-package-review-v8.csv',review)
    write_csv(HERE/'new-file-inventory-v8.csv',inventory)
    rows=[]
    for row in prior:
        key=row['id'];new=mapped[key]
        status='partial' if key in {'I023','I070'} else row['status']
        rows.append({**row,'status':status,
                     'specific_remaining_delta':residuals.get(key,row['specific_remaining_delta']),
                     'v8_experiment_packages':';'.join(new),
                     'v8_evidence_scope_and_limit':' | '.join(scope[n]['method']+' Boundary: '+scope[n]['boundary'] for n in new),
                     'v8_evidence_files':';'.join(n+'/'+f for n in new for f in scope[n]['evidence_files'])})
    write_csv(HERE/'investigation-final-v8.csv',rows)
    gate_by_id={
      'I028':'Anneal batch/live generator implementation',
      'I061':'Rust-hosted Lean InfoView/RPC integration',
      'I063':'selected external editor and Anneal transaction loop',
      'I072':'selected Lean MCP adapter and Anneal workspace integration',
      'I086':'compatible same-process OCaml Aeneas API or dependency scope',
    }
    not_run=[{'id':r['id'],'title':r['title'],'remaining_delta':r['specific_remaining_delta'],
              'primary_gate':gate_by_id[r['id']]}
             for r in rows if r['status']=='not-run']
    assert {r['id'] for r in not_run}==set(gate_by_id)
    write_csv(HERE/'not-run-investigations-v8.csv',not_run)
    byid={r['id']:r for r in rows};cross=[]
    for row in old_cross:
        key=row['3730_id'];dest=row['3731_destinations'].split(';')
        packages=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v8_experiment_packages'].split(';') if p))
        files=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v8_evidence_files'].split(';') if p))
        status='partial' if key=='G07' else row['status']
        basis=('R24 executed an isolated batch-checked tactic-candidate prototype with private copies and CAS; projected virtual documents, warm-prefix reuse and cleanup remain untested.'
               if key=='G07' else row['suggestion_scope_basis'])
        exact='; '.join(d+': '+byid[d]['specific_remaining_delta'] for d in dest)
        if key in {'N11','C04'}:exact=row['specific_remaining_delta']
        cross.append({**row,'status':status,
                      'destination_statuses':';'.join(byid[d]['status'] for d in dest),
                      'suggestion_scope_basis':basis,'specific_remaining_delta':exact,
                      'v8_experiment_packages':packages,'v8_evidence_files':files})
    write_csv(HERE/'3730-crosswalk-final-v8.csv',cross)
    not_run_suggestions=[{'3730_id':r['3730_id'],'suggestion':r['suggestion'],
                          '3731_destinations':r['3731_destinations'],
                          'remaining_delta':r['specific_remaining_delta']}
                         for r in cross if r['status']=='not-run']
    assert len(not_run_suggestions)==22
    write_csv(HERE/'not-run-suggestions-v8.csv',not_run_suggestions)
    old_suites=read_csv(V7/'remaining-local-experiments-v7.csv')
    suite_map={data['suite']:name for name,data in scope.items()}
    assert {r['gap'] for r in old_suites}==set(suite_map)
    disposition=[]
    for r in old_suites:
        name=suite_map[r['gap']];data=scope[name]
        disposition.append({'suite':r['gap'],'requested_ids':r['investigation_ids'],
                            'completed_package':name,'procedure':data['method'],'exact_boundary':data['boundary']})
    write_csv(HERE/'r23-r24-disposition-v8.csv',disposition)
    # R25/R26 are further feasible component controls, not current evidence.
    remaining=[
      ('R25','I023','Last-good model after a changed function signature and after Rust/Aeneas recovery, with old/new proof queries and explicit provisional/current status.','In progress outside snapshot; pinned tiny local fixture, real Anneal UI/live RPC and comprehension remain gated.'),
      ('R26','I070','Two competing scratch publishers plus crash injection around candidate verification, journal, immutable-generation creation and CURRENT-pointer switch.','In progress outside snapshot; fixture-specific guard, no Anneal subject mapping or durable transaction claim.'),
    ]
    write_csv(HERE/'remaining-local-experiments-v8.csv',[
      {'gap':x,'investigation_ids':ids,'bounded_next_experiment':work,'resource_and_evidence_limit':limit}
      for x,ids,work,limit in remaining])
    gates=read_csv(V7/'gated-work-v7.csv')
    for g in gates:
        if g['gate']=='G01':g['exact_unavailable_or_conditional_dimension']='R09 added one-shot trait/external/reorder/shrink/error evidence; same-process Aeneas reset and in-memory handoff still require an OCaml library build or compatible prebuilt API.'
        if g['gate']=='G05':g['exact_unavailable_or_conditional_dimension']='R18 added direct Lean two-file rename, nonempty import action, signature and inlay edits; actual Volar/Razor/editor client and Lean MCP adapter comparisons remain unavailable.'
        if g['gate']=='G06':g['exact_unavailable_or_conditional_dimension']='R18-R24 direct component and model probes do not supply the missing Anneal V2 editor/MCP bridge, Rust-hosted Lean projection, shared workspace authority or integrated batch/live engine.'
    write_csv(HERE/'gated-work-v8.csv',gates)
    validation={'snapshot_utc':issue['snapshot_utc'],'issue_3730_state':issue['3730']['state'],
                'issue_3731_state':issue['3731']['state'],'issue_sha256':issue_sha,
                'investigation_rows':len(rows),'investigation_statuses':dict(Counter(r['status'] for r in rows)),
                'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(r['status'] for r in cross)),
                'complete_investigations':[r['id'] for r in rows if r['status']=='complete'],
                'complete_suggestions':[r['3730_id'] for r in cross if r['status']=='complete'],
                'all_report_packages':len(all_packages),'prior_accounted_packages':len(prior_cited),
                'new_package_count':len(scope),'new_packages':sorted(scope),
                'in_progress_out_of_snapshot':sorted(out_of_snapshot),
                'new_inspected_file_count':len(inventory),
                'new_inspected_bytes':sum(int(x['bytes']) for x in inventory),
                'source_v7_investigation_sha256':sha((V7/'investigation-final-v7.csv').read_bytes()),
                'source_v7_crosswalk_sha256':sha((V7/'3730-crosswalk-final-v7.csv').read_bytes()),
                'r23_r24_completed':len(disposition),'remaining_locally_executable_suites':len(remaining),
                'gate_groups':len(gates)}
    (HERE/'validation-v8.json').write_text(json.dumps(validation,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(validation,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
