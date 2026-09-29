#!/usr/bin/env python3
"""Offline deterministic v10 issue/report coverage audit; no network or source edits."""
from __future__ import annotations
import csv
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
V9 = REPORTS / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v9' / 'support'
sys.path.insert(0, str(REPORTS.parent / 'tools'))
import reference


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_csv(path):
    with path.open(newline='') as f:
        return list(csv.DictReader(f))


def write_csv(path, rows):
    assert rows
    with path.open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def inspect(package):
    result = []
    for file in sorted(p for p in package.rglob('*') if p.is_file()):
        data = file.read_bytes()
        kind, detail = 'binary', 'opaque'
        if file.suffix.lower() == '.json':
            try:
                json.loads(data)
                kind, detail = 'json', 'parsed'
            except (ValueError, UnicodeDecodeError):
                kind, detail = 'json-invalid-specimen', 'retained raw bytes'
        elif file.suffix.lower() == '.csv':
            kind, detail = 'csv', f'{len(read_csv(file))} data rows'
        else:
            try:
                text = data.decode()
                kind, detail = 'utf8', f'{text.count(chr(10))} lines'
            except UnicodeDecodeError:
                pass
        result.append({'package': package.name, 'relative_file': file.relative_to(package).as_posix(),
                       'bytes': len(data), 'sha256': sha(data), 'inspection': kind, 'detail': detail})
    return result


def main():
    issue = json.loads((HERE / 'issue-scope-snapshot.json').read_text())
    b30, b31 = issue['3730']['body'], issue['3731']['body']
    assert len(issue['3730']['comments']) == len(issue['3731']['comments']) == 1
    c30, c31 = issue['3730']['comments'][0]['body'], issue['3731']['comments'][0]['body']
    heads30 = re.findall(r'^### ([A-Z]\d{2})\.', b30, re.M)
    heads31 = re.findall(r'^\*\*(I\d{3})\s+[—-]', b31, re.M) + re.findall(r'^\*\*(I\d{3})\s+[—-]', c31, re.M)
    cross_text = c31.split('## Complete #3730 → #3731 crosswalk', 1)[1]
    cross_issue = re.findall(r'^\| ([A-Z]\d{2}) \| [^\n]* \| (I\d{3}[^|]*) \|$', cross_text, re.M)
    assert len(heads30) == len(set(heads30)) == 174
    assert heads31 == [f'I{i:03}' for i in range(1, 160)]
    assert len(cross_issue) == len({key for key, _ in cross_issue}) == 174
    assert set(heads30) == {key for key, _ in cross_issue}
    hashes = {'3730_body': sha(b30.encode()), '3730_comment': sha(c30.encode()),
              '3731_body': sha(b31.encode()), '3731_comment': sha(c31.encode())}
    v9 = json.loads((V9 / 'validation-v9.json').read_text())
    assert hashes == v9['issue_sha256'], 'issue changed after v9; inspect before extending ledger'
    assert issue['3730']['state'] == 'closed' and issue['3731']['state'] == 'open'
    prior = read_csv(V9 / 'investigation-final-v9.csv')
    old_cross = read_csv(V9 / '3730-crosswalk-final-v9.csv')
    assert len(prior) == 159 and [r['id'] for r in prior] == heads31
    assert len(old_cross) == 174 and [r['3730_id'] for r in old_cross] == heads30
    old_map = {r['3730_id']: set(r['3731_destinations'].split(';')) for r in old_cross}
    for key, destinations in cross_issue:
        assert set(re.findall(r'I\d{3}', destinations)) == old_map[key], key

    scope = json.loads((HERE / 'new-package-scope.json').read_text())
    residuals = json.loads((HERE / 'residual-overrides.json').read_text())
    assert set(residuals) <= set(heads31)
    assert {v['suite'] for v in scope.values()} == {'R32 / C11', 'R33 / E10', 'R34 / J02',
                                                     'R35 / J05', 'R36 / D01'}
    old_packages = {r['package'] for r in read_csv(V9 / 'all-package-accounting-v9.csv')}
    assert len(old_packages) == 79 and not old_packages.intersection(scope)
    packages = old_packages | set(scope)
    current_substantive = {p.name for p in REPORTS.iterdir() if p.is_dir()
                           and p.name.startswith('anneal-3730-') and 'coverage-audit' not in p.name
                           and 'gap-audit' not in p.name}
    assert packages == current_substantive, ('unaccounted', sorted(current_substantive - packages),
                                             'missing', sorted(packages - current_substantive))
    package_accounting = []
    for name in sorted(packages):
        path = REPORTS / name
        report, problems = reference._load_report(path)
        assert report is not None and not problems, (name, problems)
        package_accounting.append({'package': name, 'in_v9': name in old_packages,
                                   'new_in_v10': name in scope,
                                   'report_md_sha256': sha((path / 'REPORT.md').read_bytes()),
                                   'validator': 'reference._load_report: valid'})
    write_csv(HERE / 'all-package-accounting-v10.csv', package_accounting)

    mapped = defaultdict(list)
    review, inventory = [], []
    for name, data in sorted(scope.items()):
        path = REPORTS / name
        files = inspect(path)
        inventory.extend(files)
        assert all((path / file).is_file() for file in data['evidence_files'])
        for number in data['ids']:
            key = f'I{number:03}'
            assert key in heads31
            mapped[key].append(name)
        review.append({'suite': data['suite'], 'package': name,
                       'reviewed_ids': ';'.join(f'I{x:03}' for x in data['ids']),
                       'actual_procedure_and_observation': data['method'],
                       'evidence_boundary': data['boundary'],
                       'primary_evidence_files': ';'.join(data['evidence_files']),
                       'file_count': len(files), 'bytes': sum(x['bytes'] for x in files),
                       'validator': 'reference._load_report plus offline checker: valid'})
    write_csv(HERE / 'new-package-review-v10.csv', review)
    write_csv(HERE / 'new-file-inventory-v10.csv', inventory)

    rows = []
    for old in prior:
        key = old['id']
        new = mapped[key]
        rows.append({**old, 'specific_remaining_delta': residuals.get(key, old['specific_remaining_delta']),
                     'v10_experiment_packages': ';'.join(new),
                     'v10_evidence_scope_and_limit': ' | '.join(
                         scope[name]['method'] + ' Boundary: ' + scope[name]['boundary'] for name in new),
                     'v10_evidence_files': ';'.join(name + '/' + f for name in new
                                                    for f in scope[name]['evidence_files'])})
    write_csv(HERE / 'investigation-final-v10.csv', rows)
    not_run = [{'id': r['id'], 'title': r['title'], 'remaining_delta': r['specific_remaining_delta'],
                'primary_gate': 'selected existing Lean MCP adapter and Anneal workspace integration'}
               for r in rows if r['status'] == 'not-run']
    assert [r['id'] for r in not_run] == ['I072']
    write_csv(HERE / 'not-run-investigations-v10.csv', not_run)

    new_suggestions = {
      'C11': 'R32 executed direct Lean upstream/downstream imports and showed dirty source, old OLean and reused worker boundaries; supported Anneal live-proof import and cycle policy remain absent.',
      'D01': 'R36 executed saved versus private materialized Cargo/Charon subjects with build-script, proc-macro, include/env/path and wrong-unit controls; real unsaved rustc/editor overlay and complete shadow fidelity remain absent.',
      'E10': 'R33 held Aeneas generated Lean byte-identical while an external Lean source model changed proof, axiom and worker outcomes; compiled Aeneas registry and Anneal invalidation remain absent.',
      'J02': 'R34 classified all files/bytes/inodes for one/two tiny direct Lean workers and link/clone controls; full cross-stage Anneal/Mathlib copied-byte and peak-write bill remains absent.',
      'J05': 'R35 ran guarded 1/2/4/8 tiny direct Lean scratch pools with local-build/shared imports, goal/edit fanout, footprint and cleanup; realistic long-lived Anneal/MCP topology and peak/CPU limits remain absent.'}
    by_id = {r['id']: r for r in rows}
    cross = []
    for old in old_cross:
        key = old['3730_id']
        destinations = old['3731_destinations'].split(';')
        new_packages = ';'.join(dict.fromkeys(p for dest in destinations
                                              for p in by_id[dest]['v10_experiment_packages'].split(';') if p))
        files = ';'.join(dict.fromkeys(p for dest in destinations
                                      for p in by_id[dest]['v10_evidence_files'].split(';') if p))
        status = 'partial' if key in new_suggestions else old['status']
        exact = '; '.join(dest + ': ' + by_id[dest]['specific_remaining_delta'] for dest in destinations)
        if key in {'N11', 'C04'}:
            exact = old['specific_remaining_delta']
        cross.append({**old, 'status': status,
                      'destination_statuses': ';'.join(by_id[dest]['status'] for dest in destinations),
                      'suggestion_scope_basis': new_suggestions.get(key, old['suggestion_scope_basis']),
                      'specific_remaining_delta': exact,
                      'v10_experiment_packages': new_packages, 'v10_evidence_files': files})
    write_csv(HERE / '3730-crosswalk-final-v10.csv', cross)
    not_run_suggestions = [{'3730_id': r['3730_id'], 'suggestion': r['suggestion'],
                            '3731_destinations': r['3731_destinations'],
                            'remaining_delta': r['specific_remaining_delta']}
                           for r in cross if r['status'] == 'not-run']
    assert len(not_run_suggestions) == 16
    write_csv(HERE / 'not-run-suggestions-v10.csv', not_run_suggestions)

    prior_plans = json.loads((V9 / 'remaining-local-experiments-v9.json').read_text())['identified_unexecuted_suites']
    assert {p['suite'] for p in prior_plans} == {'R32', 'R33', 'R34', 'R35', 'R36'}
    by_suite = {d['suite'].split(' / ')[0]: name for name, d in scope.items()}
    disposition = [{'suite': p['suite'], 'suggestions': p['suggestions'],
                    'investigations': p['investigations'],
                    'completed_package': by_suite[p['suite']],
                    'actual_method': scope[by_suite[p['suite']]]['method'],
                    'exact_boundary': scope[by_suite[p['suite']]]['boundary']}
                   for p in prior_plans]
    write_csv(HERE / 'r32-r36-disposition-v10.csv', disposition)
    remaining = [
      {'suite': 'R37', 'suggestions': 'J06', 'investigations': 'I115',
       'bounded_experiment': 'Measure nested Cargo/Charon and direct Lean server worker/thread budgets at 1/2/4 tiny local units with OS process-tree, CPU, footprint and admission controls.',
       'limit': 'Small components only; no Anneal scheduler or Mathlib capacity claim.'},
      {'suite': 'R38', 'suggestions': 'J09', 'investigations': 'I105;I110;I139',
       'bounded_experiment': 'Inject one malformed proof and one server cancellation/crash into an admitted 4/8-worker direct Lean pool; verify unaffected peers, stale-result fencing model, clean restart and resource cleanup.',
       'limit': 'Direct Lean plus policy model; no actual Anneal high-concurrency failure path.'},
      {'suite': 'R39', 'suggestions': 'J10', 'investigations': 'I116;I122',
       'bounded_experiment': 'Extend the existing tiny direct Lean server edit/query/restart soak with periodic physical-footprint, process-child and disk ledgers under a fixed time/resource cap.',
       'limit': 'Still not a long-lived Anneal daemon or realistic large import; no hours-long guarantee.'},
      {'suite': 'R40', 'suggestions': 'J14', 'investigations': 'I119;I124',
       'bounded_experiment': 'Repeat a small process/file/inode resource fixture on host APFS and the already cached Ubuntu Docker overlayfs image with no pull or host backup mount, recording filesystem-specific cleanup/rename charges.',
       'limit': 'Emulated linux/amd64 container and synthetic workload; no native ext4/XFS/Windows or Linux Lean toolchain.'},
      {'suite': 'R41', 'suggestions': 'N08', 'investigations': 'I159',
       'bounded_experiment': 'Construct a tiny generated-Lean-as-canonical-source prototype and a source-span/obligation/axiom comparator against a Rust-hosted view, then exercise edit, regeneration, fresh batch and server refresh.',
       'limit': 'Synthetic design experiment; cannot decide Anneal product topology or its actual generator semantics.'}
    ]
    (HERE / 'remaining-local-experiments-v10.json').write_text(json.dumps({
        'identified_bounded_local_suites': remaining,
        'assessment': 'Five additional bounded component/design suites remain executable with currently available local tools. Each leaves its product-level suggestion partial unless the relevant Anneal implementation or platform/dependency gate is supplied.'
    }, indent=2, ensure_ascii=False) + '\n')
    gates = read_csv(V9 / 'gated-work-v9.csv')
    for gate in gates:
        if gate['gate'] == 'G05':
            gate['exact_unavailable_or_conditional_dimension'] = 'R32 added direct Lean cross-proof import behavior, but an actual editor client and an existing Lean MCP adapter are still absent from this checkout/PATH inventory.'
        if gate['gate'] == 'G06':
            gate['exact_unavailable_or_conditional_dimension'] = 'R32–R36 add direct Lean, Aeneas/Charon and synthetic workspace evidence, but no implemented Anneal V2 editor/MCP bridge, Rust-hosted projection, shared authority, scheduler or generated scratch service.'
        if gate['gate'] == 'G07':
            gate['exact_unavailable_or_conditional_dimension'] = 'C11/D01/E10/J02/J05 component results sharpen design gates but do not adopt an Anneal V2 topology or decide canonical generated-source policy.'
    write_csv(HERE / 'gated-work-v10.csv', gates)

    validation = {'snapshot_utc': issue['snapshot_utc'], 'issue_3730_state': issue['3730']['state'],
                  'issue_3731_state': issue['3731']['state'], 'issue_sha256': hashes,
                  'investigation_rows': len(rows),
                  'investigation_statuses': dict(Counter(r['status'] for r in rows)),
                  'crosswalk_rows': len(cross),
                  'crosswalk_statuses': dict(Counter(r['status'] for r in cross)),
                  'complete_investigations': [r['id'] for r in rows if r['status'] == 'complete'],
                  'complete_suggestions': [r['3730_id'] for r in cross if r['status'] == 'complete'],
                  'all_report_packages': len(packages), 'prior_accounted_packages': len(old_packages),
                  'new_package_count': len(scope), 'new_packages': sorted(scope),
                  'new_inspected_file_count': len(inventory),
                  'new_inspected_bytes': sum(r['bytes'] for r in inventory),
                  'source_v9_investigation_sha256': sha((V9 / 'investigation-final-v9.csv').read_bytes()),
                  'source_v9_crosswalk_sha256': sha((V9 / '3730-crosswalk-final-v9.csv').read_bytes()),
                  'r32_r36_completed': len(disposition),
                  'remaining_bounded_local_suites': len(remaining), 'gate_groups': len(gates)}
    (HERE / 'validation-v10.json').write_text(json.dumps(validation, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(validation, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
