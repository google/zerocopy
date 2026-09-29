#!/usr/bin/env python3
"""Offline deterministic v6 issue/report coverage audit; no network or source edits."""
from __future__ import annotations
import csv,hashlib,json,re,sys
from collections import Counter,defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
V5=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-29-v5'/'support'
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
    v5=json.loads((V5/'validation-v5.json').read_text())
    assert issue_sha==v5['issue_sha256'], 'Upstream issue changed; re-audit source required'
    assert issue['3730']['state']=='closed' and issue['3731']['state']=='open'
    prior=read_csv(V5/'investigation-final-v5.csv')
    old_cross=read_csv(V5/'3730-crosswalk-final-v5.csv')
    assert len(prior)==159 and [r['id'] for r in prior]==heads31
    assert len(old_cross)==174 and [r['3730_id'] for r in old_cross]==heads30
    old_map={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue:assert set(re.findall(r'I\d{3}',dest))==old_map[key],key
    scope=json.loads((HERE/'new-package-scope.json').read_text())
    residuals=json.loads((HERE/'residual-overrides.json').read_text())
    assert set(residuals)<=set(heads31)
    all_packages={p.name for p in REPORTS.iterdir() if p.is_dir() and p.name.startswith('anneal-3730-')
                  and 'coverage-audit' not in p.name and 'gap-audit' not in p.name}
    prior_cited=set()
    for row in prior:
        for value in row.values():prior_cited.update(re.findall(r'anneal-3730-[a-z0-9-]+',value or ''))
    assert all_packages-prior_cited==set(scope),(sorted(all_packages-prior_cited),sorted(scope))
    assert len(all_packages)==68 and len(prior_cited)==65 and len(scope)==3
    coverage=[]
    for name in sorted(all_packages):
        p=REPORTS/name;report,problems=reference._load_report(p)
        assert report is not None and not problems,(name,problems)
        coverage.append({'package':name,'in_v5_ledger':name in prior_cited,'new_in_v6':name in scope,
                         'report_md_sha256':sha((p/'REPORT.md').read_bytes()),
                         'validator':'reference._load_report: valid'})
    write_csv(HERE/'all-package-accounting-v6.csv',coverage)
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
    assert {r['suite'] for r in review}=={f'R{i:02}' for i in range(18,21)}
    write_csv(HERE/'new-package-review-v6.csv',review)
    write_csv(HERE/'new-file-inventory-v6.csv',inventory)
    rows=[]
    for row in prior:
        key=row['id'];new=mapped[key]
        status=row['status']
        rows.append({**row,'status':status,
                     'specific_remaining_delta':residuals.get(key,row['specific_remaining_delta']),
                     'v6_experiment_packages':';'.join(new),
                     'v6_evidence_scope_and_limit':' | '.join(scope[n]['method']+' Boundary: '+scope[n]['boundary'] for n in new),
                     'v6_evidence_files':';'.join(n+'/'+f for n in new for f in scope[n]['evidence_files'])})
    write_csv(HERE/'investigation-final-v6.csv',rows)
    byid={r['id']:r for r in rows};cross=[]
    for row in old_cross:
        key=row['3730_id'];dest=row['3731_destinations'].split(';')
        packages=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v6_experiment_packages'].split(';') if p))
        files=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v6_evidence_files'].split(';') if p))
        status=row['status']
        basis=row['suggestion_scope_basis']
        exact='; '.join(d+': '+byid[d]['specific_remaining_delta'] for d in dest)
        if key in {'N11','C04'}:exact=row['specific_remaining_delta']
        cross.append({**row,'status':status,
                      'destination_statuses':';'.join(byid[d]['status'] for d in dest),
                      'suggestion_scope_basis':basis,'specific_remaining_delta':exact,
                      'v6_experiment_packages':packages,'v6_evidence_files':files})
    write_csv(HERE/'3730-crosswalk-final-v6.csv',cross)
    old_suites=read_csv(V5/'remaining-local-experiments-v5.csv')
    suite_map={data['suite']:name for name,data in scope.items()}
    assert {r['gap'] for r in old_suites}==set(suite_map)
    disposition=[]
    for r in old_suites:
        name=suite_map[r['gap']];data=scope[name]
        disposition.append({'suite':r['gap'],'requested_ids':r['investigation_ids'],
                            'completed_package':name,'procedure':data['method'],'exact_boundary':data['boundary']})
    write_csv(HERE/'r18-r20-disposition-v6.csv',disposition)
    # Distinguish the closed, planned suite list from further executable component controls.
    remaining=[
      ('R21','I089-I104;I120;I125;I150','One combined valid native/plugin/setup/OLean family-mix matrix with Lake-discovered fresh server and explicit loaded-byte/initializer oracle, using existing cached pins.','Tiny component graph; no Anneal archive, broad ABI proof or cross-version guarantee.'),
      ('R22','I073-I080;I105;I134','Selected active CLI gate graceful SIGINT/SIGTERM escalation, pipe/lock inventory and same-directory retry compared with SIGKILL.','No Anneal scheduler, remote workers or all-stage phase coverage.'),
    ]
    write_csv(HERE/'remaining-local-experiments-v6.csv',[
      {'gap':x,'investigation_ids':ids,'bounded_next_experiment':work,'resource_and_evidence_limit':limit}
      for x,ids,work,limit in remaining])
    gates=read_csv(V5/'gated-work-v5.csv')
    for g in gates:
        if g['gate']=='G01':g['exact_unavailable_or_conditional_dimension']='R09 added one-shot trait/external/reorder/shrink/error evidence; same-process Aeneas reset and in-memory handoff still require an OCaml library build or compatible prebuilt API.'
        if g['gate']=='G05':g['exact_unavailable_or_conditional_dimension']='R18 added direct Lean two-file rename, nonempty import action, signature and inlay edits; actual Volar/Razor/editor client and Lean MCP adapter comparisons remain unavailable.'
        if g['gate']=='G06':g['exact_unavailable_or_conditional_dimension']='R18-R20 direct component and model probes do not supply the missing Anneal V2 editor/MCP bridge, Rust-hosted Lean projection, shared workspace authority or integrated batch/live engine.'
    write_csv(HERE/'gated-work-v6.csv',gates)
    validation={'snapshot_utc':issue['snapshot_utc'],'issue_3730_state':issue['3730']['state'],
                'issue_3731_state':issue['3731']['state'],'issue_sha256':issue_sha,
                'investigation_rows':len(rows),'investigation_statuses':dict(Counter(r['status'] for r in rows)),
                'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(r['status'] for r in cross)),
                'complete_investigations':[r['id'] for r in rows if r['status']=='complete'],
                'complete_suggestions':[r['3730_id'] for r in cross if r['status']=='complete'],
                'all_report_packages':len(all_packages),'prior_accounted_packages':len(prior_cited),
                'new_package_count':len(scope),'new_packages':sorted(scope),
                'new_inspected_file_count':len(inventory),
                'new_inspected_bytes':sum(int(x['bytes']) for x in inventory),
                'source_v5_investigation_sha256':sha((V5/'investigation-final-v5.csv').read_bytes()),
                'source_v5_crosswalk_sha256':sha((V5/'3730-crosswalk-final-v5.csv').read_bytes()),
                'r18_r20_completed':len(disposition),'remaining_locally_executable_suites':len(remaining),
                'gate_groups':len(gates)}
    (HERE/'validation-v6.json').write_text(json.dumps(validation,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(validation,indent=2,ensure_ascii=False))
if __name__=='__main__':main()
