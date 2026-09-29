#!/usr/bin/env python3
"""Deterministic offline v12 ledger from frozen live-issue snapshot and package evidence."""
from __future__ import annotations
import csv, hashlib, json, re, sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
V11 = REPORTS / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v11' / 'support'
sys.path.insert(0, str(REPORTS.parent / 'tools'))
import reference

def sha(data): return hashlib.sha256(data).hexdigest()
def read_csv(path):
    with path.open(newline='') as f: return list(csv.DictReader(f))
def write_csv(path, rows):
    assert rows
    with path.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator='\n'); w.writeheader(); w.writerows(rows)
def dump(path, obj): path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def inspect(package):
    out = []
    for p in sorted(p for p in package.rglob('*') if p.is_file()):
        data=p.read_bytes(); note='binary'
        if p.suffix == '.json':
            try: json.loads(data); note='parsed JSON'
            except (ValueError, UnicodeDecodeError): note='retained invalid-JSON specimen'
        elif p.suffix == '.csv': note=f'{len(read_csv(p))} CSV rows'
        else:
            try: note=f'{data.decode().count(chr(10))} UTF-8 lines'
            except UnicodeDecodeError: pass
        out.append({'package':package.name,'relative_file':p.relative_to(package).as_posix(),
                    'bytes':len(data),'sha256':sha(data),'inspection':note})
    return out

def main():
    issue=json.loads((HERE/'issue-scope-snapshot.json').read_text())
    b30,b31=(issue[str(n)]['body'] for n in (3730,3731))
    assert len(issue['3730']['comments'])==len(issue['3731']['comments'])==1
    c30,c31=(issue[str(n)]['comments'][0]['body'] for n in (3730,3731))
    heads30=re.findall(r'^### ([A-Z]\d{2})\.', b30, re.M)
    heads31=re.findall(r'^\*\*(I\d{3})\s+[—-]',b31,re.M)+re.findall(r'^\*\*(I\d{3})\s+[—-]',c31,re.M)
    assert len(heads30)==len(set(heads30))==174
    assert heads31==[f'I{i:03}' for i in range(1,160)]
    cross_text=c31.split('## Complete #3730 → #3731 crosswalk',1)[1]
    cross_issue=re.findall(r'^\| ([A-Z]\d{2}) \| [^\n]* \| (I\d{3}[^|]*) \|$',cross_text,re.M)
    assert len(cross_issue)==len({a for a,_ in cross_issue})==174
    assert set(heads30)=={a for a,_ in cross_issue}
    hashes={'3730_body':sha(b30.encode()),'3730_comment':sha(c30.encode()),
            '3731_body':sha(b31.encode()),'3731_comment':sha(c31.encode())}
    v11=json.loads((V11/'validation-v11.json').read_text())
    assert hashes==v11['issue_sha256'], 'Issue changed: manually re-review before extending v11 rows'
    assert issue['3730']['state']=='closed' and issue['3731']['state']=='open'
    prior=read_csv(V11/'investigation-final-v11.csv')
    old_cross=read_csv(V11/'3730-crosswalk-final-v11.csv')
    assert [x['id'] for x in prior]==heads31 and [x['3730_id'] for x in old_cross]==heads30
    oldmap={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue: assert set(re.findall(r'I\d{3}',dest))==oldmap[key],key

    scope=json.loads((HERE/'new-package-scope.json').read_text())
    residuals=json.loads((HERE/'residual-overrides.json').read_text())
    assert set(residuals)<=set(heads31)
    prior_packages={x['package'] for x in read_csv(V11/'all-package-accounting-v11.csv')}
    assert len(prior_packages)==91 and not prior_packages.intersection(scope)
    current={p.name for p in REPORTS.iterdir() if p.is_dir() and p.name.startswith('anneal-3730-')
             and 'coverage-audit' not in p.name and 'gap-audit' not in p.name
             }
    assert current==prior_packages|set(scope), ('new',sorted(current-(prior_packages|set(scope))),
                                                 'missing',sorted((prior_packages|set(scope))-current))
    accounting=[]
    for name in sorted(current):
        p=REPORTS/name; report,problems=reference._load_report(p)
        assert report is not None and not problems,(name,problems)
        accounting.append({'package':name,'v11':name in prior_packages,'v12':name in scope,
                           'report_md_sha256':sha((p/'REPORT.md').read_bytes()),
                           'reference_loader':'valid'})
    write_csv(HERE/'all-package-accounting-v12.csv',accounting)
    mapped=defaultdict(list); review=[]; inventory=[]
    for name,s in sorted(scope.items()):
        p=REPORTS/name; files=inspect(p); inventory.extend(files)
        for ef in s['evidence_files']: assert (p/ef).is_file(),(name,ef)
        for key in s['ids']: assert key in heads31; mapped[key].append(name)
        for key in s['suggestions']: assert key in heads30
        review.append({'package':name,'investigations':';'.join(s['ids']),
                       'suggestions':';'.join(s['suggestions']),
                       'actual_method':s['method'],'boundary':s['boundary'],
                       'evidence_files':';'.join(s['evidence_files']),
                       'inspected_files':len(files),'inspected_bytes':sum(f['bytes'] for f in files),
                       'offline_checker':'passed independently in v12'})
    write_csv(HERE/'new-package-review-v12.csv',review)
    write_csv(HERE/'new-file-inventory-v12.csv',inventory)
    rows=[]
    for old in prior:
        key=old['id']; names=mapped[key]
        rows.append({**old,'specific_remaining_delta':residuals.get(key,old['specific_remaining_delta']),
                     'v12_experiment_packages':';'.join(names),
                     'v12_evidence_scope_and_limit':' | '.join(scope[n]['method']+' Boundary: '+scope[n]['boundary'] for n in names),
                     'v12_evidence_files':';'.join(n+'/'+ef for n in names for ef in scope[n]['evidence_files'])})
    write_csv(HERE/'investigation-final-v12.csv',rows)
    byid={x['id']:x for x in rows}
    notrun=[{'id':x['id'],'title':x['title'],'remaining_delta':x['specific_remaining_delta']} for x in rows if x['status']=='not-run']
    assert [x['id'] for x in notrun]==['I072']
    write_csv(HERE/'not-run-investigations-v12.csv',notrun)
    suggestion_overrides={
      'E11':('partial','Restricted oracle-guided one-shot trait body/signature output graph and guarded OLean reuse executed; producer still whole-crate, with no same-process item invalidation or broader economics.'),
      'F03':('not-run','Later-than-4.30 compatible Lean/Lake pin not cached; R44 changes Charon/Aeneas pairs under the same 4.30.0-rc2 Lean, so it cannot answer later Lake ownership.'),
      'F04':('not-run','Scoped inventory found no built Anneal omnibus archive. One-module read-only Lake missing-manifest control ran, but actual archive, server first goal and producer removal at target scope remain.'),
      'G03':('not-run','Toy stdio bridge now shows async handle/reconnect/expiry/cancel/failure over actual Lean goals; no existing MCP SDK/adapter or client interoperability/revision negotiation was run.'),
      'G15':('not-run','Hash-gated manually joined navigation covers reorder, ambiguous names, and actual generated-helper fanout; no producer-authenticated mapping, actual Anneal workspace or agent usability trial.'),
      'H08':('partial','A tiny A→B→A direct Lean router preserved unsaved A state; R48 added one full chain ending in a Lake-launched server. Actual editor workspace-folder switch, two-worker Lake/server capacity, Anneal pool and broker remain.'),
      'H09':('partial','Direct Lean returned processed -32800; R47 shared one real Cargo build between two toy owners with individual/last-owner cancellation and failure retry. Editor→Anneal shared scheduler cancellation remains.'),
      'J06':('partial','Two tiny Rust→Charon→Aeneas→batch Lean workflows ran under sampled guards; R48 extended one chain through Lake and live server, then skipped a two-worker cell by memory admission. No Anneal scheduler or hard peak.'),
      'M03':('partial','Two cached compatible Charon/Aeneas pairs passed four tiny full Rust→LLBC→Lean fresh checks and rejected cross-pairs; larger upgrade corpus and workaround deletion remain.'),
      'M04':('partial','Two cached compatible Charon/Aeneas pairs passed four tiny full Rust→LLBC→Lean fresh checks and rejected cross-pairs; larger upgrade corpus and workaround deletion remain.'),
      'M06':('partial','Nine Lake runs of real Aeneas-generated source showed no-op/mtime replay and byte-change rebuild/restore; no realistic workload economics or selected workaround deletion.'),
      'L09':('not-run','No existing Lean MCP adapter was found in scoped local inventory; toy bridges cannot substitute for two-client real adapter plus Anneal workspace integration.')
    }
    cross=[]
    for old in old_cross:
        key=old['3730_id']; names=[n for n,s in scope.items() if key in s['suggestions']]
        status,basis=suggestion_overrides.get(key,(old['status'],old['suggestion_scope_basis']))
        destinations=old['3731_destinations'].split(';')
        exact=basis if key in suggestion_overrides else old['specific_remaining_delta']
        cross.append({**old,'status':status,'destination_statuses':';'.join(byid[d]['status'] for d in destinations),
                      'suggestion_scope_basis':basis,'specific_remaining_delta':exact,
                      'v12_experiment_packages':';'.join(names),
                      'v12_evidence_files':';'.join(n+'/'+ef for n in names for ef in scope[n]['evidence_files'])})
    write_csv(HERE/'3730-crosswalk-final-v12.csv',cross)
    notrun_s=[{'3730_id':x['3730_id'],'suggestion':x['suggestion'],'destinations':x['3731_destinations'],
               'remaining_delta':x['specific_remaining_delta']} for x in cross if x['status']=='not-run']
    assert {x['3730_id'] for x in notrun_s}=={'F03','F04','G03','G15','L09'}
    write_csv(HERE/'not-run-suggestions-v12.csv',notrun_s)
    gates=read_csv(V11/'gated-work-v11.csv')
    write_csv(HERE/'gated-work-v12.csv',gates)
    validation={'snapshot_utc':issue['snapshot_utc'],'reference_commit':'d3e0e39ab26ddd79d03bea58cfe87813a33ef633',
                'issue_3730_state':issue['3730']['state'],'issue_3731_state':issue['3731']['state'],
                'issue_sha256':hashes,'investigation_rows':len(rows),
                'investigation_statuses':dict(Counter(x['status'] for x in rows)),
                'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(x['status'] for x in cross)),
                'all_substantive_packages':len(current),'prior_accounted_packages':len(prior_packages),
                'new_package_count':len(scope),'new_packages':sorted(scope),
                'new_inspected_file_count':len(inventory),'new_inspected_bytes':sum(x['bytes'] for x in inventory),
                'source_v11_investigation_sha256':sha((V11/'investigation-final-v11.csv').read_bytes()),
                'source_v11_crosswalk_sha256':sha((V11/'3730-crosswalk-final-v11.csv').read_bytes()),
                'not_run_investigations':[x['id'] for x in notrun],
                'not_run_suggestions':[x['3730_id'] for x in notrun_s],
                'status_changes_from_v11':[{'3730_id':x['3730_id'],'before':old_cross[i]['status'],'after':x['status']}
                                           for i,x in enumerate(cross) if x['status']!=old_cross[i]['status']]}
    dump(HERE/'validation-v12.json',validation)
    print(json.dumps(validation,indent=2))
if __name__=='__main__': main()
