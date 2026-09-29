#!/usr/bin/env python3
"""Deterministically rebuild the v3 #3730/#3731 evidence ledger.

Issue text is a preserved 2026-09-29 public GitHub API acquisition. This builder
is offline: it validates issue shape/hashes and inspects all completed report
packages, but never changes source reports or fetches unstable state itself.
"""
from __future__ import annotations
import csv,hashlib,json,re,sys
from collections import Counter,defaultdict
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
V2=REPORTS/'anneal-3730-3731-final-coverage-audit-2026-09-29-v2'/'support'
sys.path.insert(0,str(REPORTS.parent/'tools'))
import reference

def sha(data):return hashlib.sha256(data).hexdigest()
def read_csv(p):
    with p.open(newline='') as f:return list(csv.DictReader(f))
def write_csv(p,rows):
    assert rows
    with p.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
def valid_package(p):
    r,problems=reference._load_report(p)
    assert r is not None and not problems,(p,problems)
def inspect(p):
    files=sorted(x for x in p.rglob('*') if x.is_file())
    rows=[]
    for f in files:
        b=f.read_bytes();kind='binary';detail='opaque'
        if f.suffix.lower()=='.json':
            try:json.loads(b);kind='json';detail='parsed'
            except (ValueError,UnicodeDecodeError) as e:kind='json-invalid-specimen';detail=type(e).__name__
        elif f.suffix.lower()=='.csv':kind='csv';detail=f'{len(read_csv(f))} data rows'
        else:
            try:s=b.decode('utf-8');kind='utf8';detail=f'{s.count(chr(10))} lines'
            except UnicodeDecodeError:pass
        rows.append({'package':p.name,'relative_file':f.relative_to(p).as_posix(),
                     'bytes':len(b),'sha256':sha(b),'inspection':kind,'detail':detail})
    return rows

def main():
    issue=json.loads((HERE/'issue-scope-snapshot.json').read_text())
    b30=issue['3730']['body'];b31=issue['3731']['body'];c30=issue['3730']['comments'][0]['body'];c31=issue['3731']['comments'][0]['body']
    heads30=re.findall(r'^### ([A-Z]\d{2})\.',b30,re.M)
    heads31=re.findall(r'^\*\*(I\d{3})\s+[—-]',b31,re.M)+re.findall(r'^\*\*(I\d{3})\s+[—-]',c31,re.M)
    cross_text=c31.split('## Complete #3730 → #3731 crosswalk',1)[1]
    cross_issue=re.findall(r'^\| ([A-Z]\d{2}) \| [^\n]* \| (I\d{3}[^|]*) \|$',cross_text,re.M)
    assert len(heads30)==len(set(heads30))==174
    assert heads31==[f'I{i:03}' for i in range(1,160)]
    assert len(cross_issue)==len({x[0] for x in cross_issue})==174
    assert set(heads30)=={x[0] for x in cross_issue}
    issue_sha={
      '3730_body':sha(b30.encode()),'3730_comment':sha(c30.encode()),
      '3731_body':sha(b31.encode()),'3731_comment':sha(c31.encode())}
    prior_validation=json.loads((V2/'validation-v2.json').read_text())
    assert issue_sha=={
      '3730_body':prior_validation['issue_3730_body_sha256'],
      '3730_comment':prior_validation['issue_3730_comment_sha256'],
      '3731_body':prior_validation['issue_3731_body_sha256'],
      '3731_comment':prior_validation['issue_3731_comment_sha256']}

    scope=json.loads((HERE/'new-package-scope.json').read_text())
    residuals=json.loads((HERE/'residual-overrides.json').read_text())
    suggestion_basis=json.loads((HERE/'suggestion-overrides.json').read_text())
    prior=read_csv(V2/'investigation-final-v2.csv')
    old_cross=read_csv(V2/'3730-crosswalk-final-v2.csv')
    assert len(prior)==159 and [r['id'] for r in prior]==heads31
    assert len(old_cross)==174
    old_map={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue:assert set(re.findall(r'I\d{3}',dest))==old_map[key],key
    assert set(residuals)<=set(heads31)
    assert set(suggestion_basis)<=set(heads30)

    # Every #3730 report-created package (other than the audit lineage itself)
    # must occur in the prior ledger or in this exact eight-package delta.
    all_packages={p.name for p in REPORTS.iterdir() if p.is_dir() and p.name.startswith('anneal-3730-')
      and 'coverage-audit' not in p.name and 'gap-audit' not in p.name}
    prior_cited=set()
    for row in prior:
        for v in row.values():prior_cited.update(re.findall(r'anneal-3730-[a-z0-9-]+',v or ''))
    assert all_packages-prior_cited==set(scope),(sorted(all_packages-prior_cited),sorted(scope))
    assert len(all_packages)==55 and len(prior_cited)==47 and len(scope)==8
    for name in sorted(all_packages):valid_package(REPORTS/name)
    coverage=[{'package':n,'in_v2_investigation_ledger':n in prior_cited,
               'new_in_v3':n in scope,'report_md_sha256':sha((REPORTS/n/'REPORT.md').read_bytes()),
               'validator':'reference._load_report: valid'} for n in sorted(all_packages)]
    write_csv(HERE/'all-package-accounting-v3.csv',coverage)

    new_inv=[];review=[];mapped=defaultdict(list)
    for name,data in sorted(scope.items()):
        p=REPORTS/name;files=inspect(p);new_inv.extend(files)
        assert all((p/f).is_file() for f in data['evidence_files'])
        review.append({'package':name,'reviewed_ids':';'.join(f'I{x:03}' for x in data['ids']),
                       'actual_procedure_and_observation':data['method'],'evidence_boundary':data['boundary'],
                       'primary_evidence_files':';'.join(data['evidence_files']),
                       'file_count':len(files),'bytes':sum(int(x['bytes']) for x in files),
                       'validator':'reference._load_report: valid'})
        for n in data['ids']:mapped[f'I{n:03}'].append(name)
    write_csv(HERE/'new-package-review-v3.csv',review)
    write_csv(HERE/'new-file-inventory-v3.csv',new_inv)
    rows=[]
    for r in prior:
        key=r['id'];new=mapped[key]
        extra=' | '.join(scope[n]['method']+' Boundary: '+scope[n]['boundary'] for n in new)
        evidence=';'.join(n+'/'+f for n in new for f in scope[n]['evidence_files'])
        # No v3 package completes a full issue row. In particular, I028/I059/
        # I060/I063/I086 have component context but no requested comparison;
        # I141 is a protocol without participants and stays conditional.
        rows.append({**r,'v3_experiment_packages':';'.join(new),
                     'v3_evidence_scope_and_limit':extra,'v3_evidence_files':evidence,
                     'specific_remaining_delta':residuals.get(key,r['specific_remaining_delta'])})
    assert len(rows)==159
    write_csv(HERE/'investigation-final-v3.csv',rows)
    byid={r['id']:r for r in rows}
    cross=[]
    for r in old_cross:
        key=r['3730_id'];dest=r['3731_destinations'].split(';')
        pkgs=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v3_experiment_packages'].split(';') if p))
        evidence=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['v3_evidence_files'].split(';') if p))
        exact='; '.join(d+': '+byid[d]['specific_remaining_delta'] for d in dest)
        basis=suggestion_basis.get(key,r['suggestion_scope_basis'])
        if key in ('N11','C04'):
            # These have a fully answered bounded direct-Lean suggestion; do
            # not turn broader destination residuals into a false suggestion gap.
            exact=r['specific_remaining_delta']
        cross.append({**r,'v3_experiment_packages':pkgs,'v3_evidence_files':evidence,'suggestion_scope_basis':basis,
                      'specific_remaining_delta':exact})
    assert len(cross)==174
    write_csv(HERE/'3730-crosswalk-final-v3.csv',cross)

    follow=[]
    suite_map={'R01':'anneal-3730-lean-transitive-import-rpc-matrix-2026-09-29',
      'R02':'anneal-3730-charon-subject-output-phase-matrix-2026-09-29',
      'R03':'anneal-3730-aeneas-manifest-batch-oracle-2026-09-29',
      'R04':'anneal-3730-lake-cache-publication-atomicity-2026-09-29',
      'R05':'anneal-3730-resource-soak-contamination-2026-09-29',
      'R06':'anneal-3730-rust-charon-aeneas-lean-golden-vertical-2026-09-29',
      'R07':'anneal-3730-source-owned-projection-diagnostic-matrix-2026-09-29'}
    old_suites=read_csv(V2/'remaining-local-experiments-v2.csv')
    assert {r['gap'] for r in old_suites}==set(suite_map)
    for r in old_suites:
        n=suite_map[r['gap']]
        follow.append({'suite':r['gap'],'requested_ids':r['investigation_ids'],
          'completed_package':n,'procedure':scope[n]['method'],'exact_boundary':scope[n]['boundary']})
    write_csv(HERE/'r01-r07-disposition-v3.csv',follow)

    local=[
      ('R08','I073-I080;I105','Small pinned Charon Cargo build-script/proc-macro/include/env path-dependency closure and controlled private target; add a deliberate wrong-unit selection reject.','Installed nightly/Charon, one tiny crate, no cross-target std; component-only.'),
      ('R09','I082-I088;I148-I149','One-shot Aeneas trait/external dependency and generated-file shrink/reorder/errors matrix with fresh Lean consumer and exact manifest.','Installed CLI only; no same-process OCaml library or compiled registry mutation.'),
      ('R10','I089-I104;I108-I109;I151','Bounded Lake same-key concurrent writer conflict and artifact-write interruption for OLean/ILean/C with integrity/fresh import oracle.','Scratch cache, two tiny consumers, strict disk/RSS caps; no power-loss claim.'),
      ('R11','I041-I050;I113-I119;I139;I153-I154','Longer bounded Lean server edit/open/close/restart soak, conflicting same-name import sentinels, and selected rich RPC reference lifetime checks.','Cached pins, guarded sequential ramp; no Mathlib-scale or Anneal broker.'),
      ('R12','I126-I132;I135;I147-I149;I158-I159','Broaden hand-assembled Rust→Lean comparator mutants: weaker claim, changed imports, source reorder, exact model/axiom/obligation manifest and fresh batch.','Pinned tuple, small fixture; not an Anneal generator or upgrade proof.'),
      ('R13','I025-I032;I059-I063','Direct Lean LSP completion/code-action/encoding controls over a Unicode proof plus a larger illustrative source-map edit stream.','No real Rust-hosted projection or supported editor adapter; bounded component/model evidence only.'),
    ]
    write_csv(HERE/'remaining-local-experiments-v3.csv',[
      {'gap':x,'investigation_ids':ids,'bounded_next_experiment':work,'resource_and_evidence_limit':limit}
      for x,ids,work,limit in local])
    gates=read_csv(V2/'gated-work-v2.csv')
    for g in gates:
        if g['gate']=='G02':
            g['exact_unavailable_or_conditional_dimension']='I141 now has a validated study protocol and zero participants/outcome rows; actual human understanding remains unmeasured.'
            g['unblock_condition']='Render/freeze a truthful Anneal UI and study materials, recruit consenting human participants, then collect/analyze outcomes.'
        if g['gate']=='G01':
            g['exact_unavailable_or_conditional_dimension']='Same-process Aeneas reset and in-memory handoff remain unavailable with installed one-shot CLI; additional CLI/batch oracle probes do not test the OCaml API.'
    write_csv(HERE/'gated-work-v3.csv',gates)
    validation={'snapshot_utc':issue['snapshot_utc'],'issue_3730_state':issue['3730']['state'],
      'issue_3731_state':issue['3731']['state'],'issue_sha256':issue_sha,
      'investigation_rows':len(rows),'investigation_statuses':dict(Counter(r['status'] for r in rows)),
      'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(r['status'] for r in cross)),
      'complete_investigations':[r['id'] for r in rows if r['status']=='complete'],
      'complete_suggestions':[r['3730_id'] for r in cross if r['status']=='complete'],
      'all_report_packages':len(all_packages),'prior_accounted_packages':len(prior_cited),
      'new_package_count':len(scope),'new_packages':sorted(scope),
      'new_inspected_file_count':len(new_inv),'new_inspected_bytes':sum(int(x['bytes']) for x in new_inv),
      'source_v2_investigation_sha256':sha((V2/'investigation-final-v2.csv').read_bytes()),
      'source_v2_crosswalk_sha256':sha((V2/'3730-crosswalk-final-v2.csv').read_bytes()),
      'r01_r07_completed':len(follow),'remaining_locally_executable_suites':len(local),'gate_groups':len(gates)}
    (HERE/'validation-v3.json').write_text(json.dumps(validation,indent=2)+'\n')
    print(json.dumps({k:v for k,v in validation.items() if k!='new_packages'},indent=2))

if __name__=='__main__':main()
