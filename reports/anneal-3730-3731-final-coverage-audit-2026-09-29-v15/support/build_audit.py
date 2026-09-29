#!/usr/bin/env python3
"""Deterministic offline v15 ledger from frozen live-issue snapshot and package evidence."""
from __future__ import annotations
import csv, hashlib, json, re, sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
V14 = REPORTS / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v14' / 'support'
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
    v14=json.loads((V14/'validation-v14.json').read_text())
    assert hashes==v14['issue_sha256'], 'Issue changed: manually re-review before extending v14 rows'
    assert issue['3730']['state']=='closed' and issue['3731']['state']=='open'
    prior=read_csv(V14/'investigation-final-v14.csv')
    old_cross=read_csv(V14/'3730-crosswalk-final-v14.csv')
    assert [x['id'] for x in prior]==heads31 and [x['3730_id'] for x in old_cross]==heads30
    oldmap={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue: assert set(re.findall(r'I\d{3}',dest))==oldmap[key],key

    scope=json.loads((HERE/'new-package-scope.json').read_text())
    residuals=json.loads((HERE/'residual-overrides.json').read_text())
    assert set(residuals)<=set(heads31)
    prior_packages={x['package'] for x in read_csv(V14/'all-package-accounting-v14.csv')}
    assert len(prior_packages)==108 and not prior_packages.intersection(scope)
    current={p.name for p in REPORTS.iterdir() if p.is_dir() and p.name.startswith('anneal-3730-')
             and 'coverage-audit' not in p.name and 'gap-audit' not in p.name
             }
    assert current==prior_packages|set(scope), ('new',sorted(current-(prior_packages|set(scope))),
                                                 'missing',sorted((prior_packages|set(scope))-current))
    accounting=[]
    for name in sorted(current):
        p=REPORTS/name; report,problems=reference._load_report(p)
        assert report is not None and not problems,(name,problems)
        accounting.append({'package':name,'v14':name in prior_packages,'v15':name in scope,
                           'report_md_sha256':sha((p/'REPORT.md').read_bytes()),
                           'reference_loader':'valid'})
    write_csv(HERE/'all-package-accounting-v15.csv',accounting)
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
                       'offline_checker':'passed independently in v15'})
    write_csv(HERE/'new-package-review-v15.csv',review)
    write_csv(HERE/'new-file-inventory-v15.csv',inventory)
    rows=[]
    for old in prior:
        key=old['id']; names=mapped[key]
        rows.append({**old,'specific_remaining_delta':residuals.get(key,old['specific_remaining_delta']),
                     'v15_experiment_packages':';'.join(names),
                     'v15_evidence_scope_and_limit':' | '.join(scope[n]['method']+' Boundary: '+scope[n]['boundary'] for n in names),
                     'v15_evidence_files':';'.join(n+'/'+ef for n in names for ef in scope[n]['evidence_files'])})
    write_csv(HERE/'investigation-final-v15.csv',rows)
    byid={x['id']:x for x in rows}
    notrun=[{'id':x['id'],'title':x['title'],'remaining_delta':x['specific_remaining_delta']} for x in rows if x['status']=='not-run']
    assert [x['id'] for x in notrun]==['I072']
    write_csv(HERE/'not-run-investigations-v15.csv',notrun)
    suggestion_overrides={
      'E11':('partial','Restricted oracle-guided one-shot trait body/signature output graph and guarded OLean reuse executed; producer still whole-crate, with no same-process item invalidation or broader economics.'),
      'F03':('not-run','Later-than-4.30 compatible Lean/Lake pin not cached; R44 changes Charon/Aeneas pairs under the same 4.30.0-rc2 Lean, so it cannot answer later Lake ownership.'),
      'F04':('not-run','Scoped inventory found no built Anneal omnibus archive. One-module read-only Lake missing-manifest control ran, but actual archive, server first goal and producer removal at target scope remain.'),
      'G03':('not-run','The stdlib 2026-07-28 wire model now has a real pinned Lean goal composition, including stale source, pre-start cancellation and forwarded in-flight Lean -32800; both bridges remain toy raw-client code with no existing MCP SDK/adapter, independent client interoperability or Anneal task service.'),
      'G15':('not-run','Hash-gated manually joined navigation covers reorder, ambiguous names, and actual generated-helper fanout; no producer-authenticated mapping, actual Anneal workspace or agent usability trial.'),
      'H08':('partial','A tiny A→B→A direct Lean router preserved unsaved A state; R48 added one full chain ending in a Lake-launched server. Actual editor workspace-folder switch, two-worker Lake/server capacity, Anneal pool and broker remain.'),
      'H09':('partial','Direct Lean returned processed -32800; R47 shared one real Cargo build between two toy owners with individual/last-owner cancellation and failure retry. Editor→Anneal shared scheduler cancellation remains.'),
      'J06':('partial','Two tiny Rust→Charon→Aeneas→batch Lean workflows ran under sampled guards; R48 extended one chain through Lake and live server, then skipped a two-worker cell by memory admission. No Anneal scheduler or hard peak.'),
      'M03':('partial','Two cached compatible Charon/Aeneas pairs passed four tiny full Rust→LLBC→Lean fresh checks and rejected cross-pairs; larger upgrade corpus and workaround deletion remain.'),
      'M04':('partial','Two cached compatible Charon/Aeneas pairs passed four tiny full Rust→LLBC→Lean fresh checks and rejected cross-pairs; larger upgrade corpus and workaround deletion remain.'),
      'M06':('partial','Nine Lake runs of real Aeneas-generated source showed no-op/mtime replay and byte-change rebuild/restore; no realistic workload economics or selected workaround deletion.'),
      'L09':('not-run','No existing Lean MCP adapter was found in scoped local inventory; current-wire toy bridge over real Lean LSP still cannot substitute for two-client existing adapter plus Anneal workspace integration.')
    }
    suggestion_overrides.update({
      'B08':('partial','Direct Lean local-instance/macro/autoImplicit controls changed elaborated proof meaning under identical theorem source. Anneal wrapper generation, Rust subject manifest and proposition/dependency attestation remain.'),
      'C02':('partial','Twenty nested plainGoal and three plainTermGoal cursor controls now ran on one accepted direct Lean file. Rich RPC, failure/unsaved-edit position grid, generated proof and Anneal projection remain.'),
      'H01':('partial','Direct and lake serve accepted the tested physical, absent-file, anneal and untitled URI forms for a tiny imported unsaved buffer. Product URI routing, regeneration and Rust editor lifecycle remain.'),
      'H02':('partial','LSP goals worked for custom and absent-file URIs under cached Lake launch; lake setup-file still failed for an absent physical file. Product shadow-file/virtual-header strategy and mapped import setup remain.'),
      'H04':('partial','Tiny direct/Lake unsaved imported URIs and close/reopen goal behavior ran. Actual hidden Lean document ownership, Rust editor open/change/save/rename/close and cleanup remain.'),
      'A05':('partial','Separate old URI retained a revision-1 goal while live URI advanced; close rejected it, same-server reopen and fresh server recomputed the old goal. No exact-revision broker, comparable workload economics or attributable retention storage.'),
      'A06':('partial','Same-URI rapid edits returned latest goal and a separate old URI returned its old goal until close. Explicit latest-at-start/completion/exact-revision envelope with expiry/restart remains.'),
      'C10':('partial','Eight fresh Lean proof files imported one tiny Model→Helper graph: all passed at model 8, all failed after model reverted to 7, all passed after propositions updated. No realistic Anneal generated many-proof scale, live worker invalidation or scheduling policy.'),
      'F01':('partial','Synthetic same-physical-producer Lake consumers exposed assigned name/index configuration slots and setup-file importArts lower bound. Complete prepared archive schema, real consumer and operation-specific server/plugin contracts remain.'),
      'F05':('partial','Assigned dependency name/index changed producer-owned compiled configuration state while Dep replayed. Direct duplicate-name requires failed, and a root manifest selected one of two physical producer versions through wrappers in either tested order. Broader version, platform/tool hash, used option, read-only simultaneous consumer and cross-layer Anneal identity collisions remain.'),
      'F10':('partial','Selected clean/replay/no-build/rehash controls retained Lake labels, net file deltas, .trace.nobuild and positively sampled Lean children; verbose replay can print historical Lean command. No syscall read/transient-write trace or prepared-scale parallelism proof.')
    })
    suggestion_overrides.update({
      'A05':('partial','Eight distinct proof files in four bounded direct/Lake two-worker waves now show old imported contexts returning solved goals after OLean rebuild while fresh batch/workers reject. Exact historical-query broker, equivalent-workload retention/recompute costs and expiry remain.'),
      'C02':('partial','Valid nested tactic/term grid plus same-URI unsaved syntax-error/unknown-tactic/recovery grid now recorded 28 additional exact plainGoal positions and fresh batch controls. Rich RPC, macro-expanded/generated proofs, source map and Anneal projection remain.'),
      'C10':('partial','Eight unchanged proof files shared a Model→Helper graph; fresh batch rejected all after model change and four bounded two-worker direct/Lake waves split stale old goals from fresh failure. No eight simultaneous workers, representative Anneal scale, generated graph or sound product scheduling/invalidation policy.'),
      'F01':('partial','One pinned Lake producer frozen at dependency index 1 served a matching consumer without producer mutation; changed-index consumer failed on producer configuration lock until thawed, then rewrote config bytes. Complete multi-identity prepared archive schema and server/plugin consumers remain.'),
      'F05':('partial','Assigned name/index and wrapper-manifest choices affected compiled configuration state; a new frozen index-1 producer rejected a shifted-index consumer, while thawed shifted control rewrote config OLean/trace. Broader version/platform/tool/used-option collisions and product identity remain.')
    })
    cross=[]
    for old in old_cross:
        key=old['3730_id']; names=[n for n,s in scope.items() if key in s['suggestions']]
        status,basis=suggestion_overrides.get(key,(old['status'],old['suggestion_scope_basis']))
        destinations=old['3731_destinations'].split(';')
        exact=basis if key in suggestion_overrides else old['specific_remaining_delta']
        cross.append({**old,'status':status,'destination_statuses':';'.join(byid[d]['status'] for d in destinations),
                      'suggestion_scope_basis':basis,'specific_remaining_delta':exact,
                      'v15_experiment_packages':';'.join(names),
                      'v15_evidence_files':';'.join(n+'/'+ef for n in names for ef in scope[n]['evidence_files'])})
    write_csv(HERE/'3730-crosswalk-final-v15.csv',cross)
    notrun_s=[{'3730_id':x['3730_id'],'suggestion':x['suggestion'],'destinations':x['3731_destinations'],
               'remaining_delta':x['specific_remaining_delta']} for x in cross if x['status']=='not-run']
    assert {x['3730_id'] for x in notrun_s}=={'F03','F04','G03','G15','L09'}
    write_csv(HERE/'not-run-suggestions-v15.csv',notrun_s)
    candidate=json.loads((HERE/'candidate-review-v15.json').read_text())
    assert [r['id'] for r in candidate]==['I033','H01','H02','H03','H04','I047','A05','A06',
                                         'I056','C10','I090','F01','F02','F03','F04','F05','I095','F10',
                                         'I036','I037','I043']
    assert all((r['id'] in heads31 or r['id'] in heads30) and r['remaining_delta'] for r in candidate)
    write_csv(HERE/'candidate-review-v15.csv',candidate)
    gates=read_csv(V14/'gated-work-v14.csv')
    write_csv(HERE/'gated-work-v15.csv',gates)
    validation={'snapshot_utc':issue['snapshot_utc'],'reference_commit':'c7abd976962801c3a3a1796c072a3530b3a78921',
                'issue_3730_state':issue['3730']['state'],'issue_3731_state':issue['3731']['state'],
                'issue_sha256':hashes,'investigation_rows':len(rows),
                'investigation_statuses':dict(Counter(x['status'] for x in rows)),
                'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(x['status'] for x in cross)),
                'all_substantive_packages':len(current),'prior_accounted_packages':len(prior_packages),
                'new_package_count':len(scope),'new_packages':sorted(scope),
                'new_inspected_file_count':len(inventory),'new_inspected_bytes':sum(x['bytes'] for x in inventory),
                'candidate_review_rows':len(candidate),
                'source_v14_investigation_sha256':sha((V14/'investigation-final-v14.csv').read_bytes()),
                'source_v14_crosswalk_sha256':sha((V14/'3730-crosswalk-final-v14.csv').read_bytes()),
                'not_run_investigations':[x['id'] for x in notrun],
                'not_run_suggestions':[x['3730_id'] for x in notrun_s],
                'status_changes_from_v14':[{'3730_id':x['3730_id'],'before':old_cross[i]['status'],'after':x['status']}
                                           for i,x in enumerate(cross) if x['status']!=old_cross[i]['status']]}
    dump(HERE/'validation-v15.json',validation)
    print(json.dumps(validation,indent=2))
if __name__=='__main__': main()
