#!/usr/bin/env python3
"""Offline deterministic v11 issue/report coverage audit; no network or source edits."""
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
V10 = REPORTS / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v10' / 'support'
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
    v10 = json.loads((V10 / 'validation-v10.json').read_text())
    assert hashes == v10['issue_sha256'], 'issue changed after v10; inspect before extending ledger'
    assert issue['3730']['state'] == 'closed' and issue['3731']['state'] == 'open'
    prior = read_csv(V10 / 'investigation-final-v10.csv')
    old_cross = read_csv(V10 / '3730-crosswalk-final-v10.csv')
    assert len(prior) == 159 and [r['id'] for r in prior] == heads31
    assert len(old_cross) == 174 and [r['3730_id'] for r in old_cross] == heads30
    old_map = {r['3730_id']: set(r['3731_destinations'].split(';')) for r in old_cross}
    for key, destinations in cross_issue:
        assert set(re.findall(r'I\d{3}', destinations)) == old_map[key], key

    scope = json.loads((HERE / 'new-package-scope.json').read_text())
    residuals = json.loads((HERE / 'residual-overrides.json').read_text())
    assert set(residuals) <= set(heads31)
    assert {v['suite'] for v in scope.values()} == {'R37 / J06', 'R38 / J09', 'R39 / J10',
                                                     'R40 / J14', 'R41 / N08', 'R42 / I079-I148',
                                                     'R43 / I079-I148'}
    old_packages = {r['package'] for r in read_csv(V10 / 'all-package-accounting-v10.csv')}
    assert len(old_packages) == 84 and not old_packages.intersection(scope)
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
        package_accounting.append({'package': name, 'in_v10': name in old_packages,
                                   'new_in_v11': name in scope,
                                   'report_md_sha256': sha((path / 'REPORT.md').read_bytes()),
                                   'validator': 'reference._load_report: valid'})
    write_csv(HERE / 'all-package-accounting-v11.csv', package_accounting)

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
    write_csv(HERE / 'new-package-review-v11.csv', review)
    write_csv(HERE / 'new-file-inventory-v11.csv', inventory)

    rows = []
    for old in prior:
        key = old['id']
        new = mapped[key]
        rows.append({**old, 'specific_remaining_delta': residuals.get(key, old['specific_remaining_delta']),
                     'v11_experiment_packages': ';'.join(new),
                     'v11_evidence_scope_and_limit': ' | '.join(
                         scope[name]['method'] + ' Boundary: ' + scope[name]['boundary'] for name in new),
                     'v11_evidence_files': ';'.join(name + '/' + f for name in new
                                                    for f in scope[name]['evidence_files'])})
    write_csv(HERE / 'investigation-final-v11.csv', rows)
    not_run = [{'id': r['id'], 'title': r['title'], 'remaining_delta': r['specific_remaining_delta'],
                'primary_gate': 'selected existing Lean MCP adapter and Anneal workspace integration'}
               for r in rows if r['status'] == 'not-run']
    assert [r['id'] for r in not_run] == ['I072']
    write_csv(HERE / 'not-run-investigations-v11.csv', not_run)

    new_suggestions = {
      'J06': 'R37 ran separate tiny 1/2/4 outer by 1/2 inner Cargo/Charon and direct Lean matrices with resource ledgers; no combined representative Anneal scheduler or hard peak/capacity bound.',
      'J09': 'R38 admitted four tiny direct Lean servers, isolated one malformed buffer, sent cancellation and killed/restarted one peer; no processed cancellation in this run, actual Anneal fence or shared generated workspace.',
      'J10': 'R39 ran a 5.6-minute direct Lean edit/query soak with two orderly restarts and sampled footprint/disk/tree ledgers; no hours-long realistic-import or Anneal daemon drift proof.',
      'J14': 'R40 compared tiny APFS and emulated Ubuntu Docker overlayfs copy/clone/hardlink/mutation counters; no exclusive overlayfs extent-byte bill, native ext4/XFS/Windows or large Anneal jobs.',
      'N08': 'R41 executed a synthetic generated-Lean canonical proof with Rust-hosted projection, range/provenance mapping and acceptance controls; no real Anneal V2 generator, editor/MCP bridge or product architecture decision.'}
    by_id = {r['id']: r for r in rows}
    cross = []
    for old in old_cross:
        key = old['3730_id']
        destinations = old['3731_destinations'].split(';')
        new_packages = ';'.join(dict.fromkeys(p for dest in destinations
                                              for p in by_id[dest]['v11_experiment_packages'].split(';') if p))
        files = ';'.join(dict.fromkeys(p for dest in destinations
                                      for p in by_id[dest]['v11_evidence_files'].split(';') if p))
        status = 'partial' if key in new_suggestions else old['status']
        exact = '; '.join(dest + ': ' + by_id[dest]['specific_remaining_delta'] for dest in destinations)
        if key in {'N11', 'C04'}:
            exact = old['specific_remaining_delta']
        cross.append({**old, 'status': status,
                      'destination_statuses': ';'.join(by_id[dest]['status'] for dest in destinations),
                      'suggestion_scope_basis': new_suggestions.get(key, old['suggestion_scope_basis']),
                      'specific_remaining_delta': exact,
                      'v11_experiment_packages': new_packages, 'v11_evidence_files': files})
    write_csv(HERE / '3730-crosswalk-final-v11.csv', cross)
    not_run_suggestions = [{'3730_id': r['3730_id'], 'suggestion': r['suggestion'],
                            '3731_destinations': r['3731_destinations'],
                            'remaining_delta': r['specific_remaining_delta']}
                           for r in cross if r['status'] == 'not-run']
    assert len(not_run_suggestions) == 11
    write_csv(HERE / 'not-run-suggestions-v11.csv', not_run_suggestions)

    prior_plans = json.loads((V10 / 'remaining-local-experiments-v10.json').read_text())['identified_bounded_local_suites']
    assert {p['suite'] for p in prior_plans} == {'R37', 'R38', 'R39', 'R40', 'R41'}
    by_suite = {d['suite'].split(' / ')[0]: name for name, d in scope.items()}
    disposition = [{'suite': p['suite'], 'suggestions': p['suggestions'],
                    'investigations': p['investigations'],
                    'completed_package': by_suite[p['suite']],
                    'actual_method': scope[by_suite[p['suite']]]['method'],
                    'exact_boundary': scope[by_suite[p['suite']]]['boundary']}
                   for p in prior_plans]
    write_csv(HERE / 'r37-r41-disposition-v11.csv', disposition)
    remaining = []
    (HERE / 'remaining-local-experiments-v11.json').write_text(json.dumps({
        'identified_bounded_local_suites': remaining,
        'assessment': 'R37 exposed warm Charon byte instability; R42 isolated its varying LLBC field; R43 tested the exact five variants through one-shot Aeneas, fresh Lean and same-path Lake replay. No further bounded local suite is clearly exposed by these seven packages. The partial product-level residuals and listed external/platform/human/implementation gates remain.'
    }, indent=2, ensure_ascii=False) + '\n')
    gates = read_csv(V10 / 'gated-work-v10.csv')
    for gate in gates:
        if gate['gate'] == 'G05':
            gate['exact_unavailable_or_conditional_dimension'] = 'Direct Lean protocols and the R41 synthetic Rust-hosted projection add evidence, but an actual editor client and an existing Lean MCP adapter remain absent from this checkout/PATH inventory.'
        if gate['gate'] == 'G06':
            gate['exact_unavailable_or_conditional_dimension'] = 'R37–R41 add component resource/failure probes and a synthetic Rust-hosted view, but no implemented Anneal V2 editor/MCP bridge, shared authority, combined scheduler or generated scratch service.'
        if gate['gate'] == 'G07':
            gate['exact_unavailable_or_conditional_dimension'] = 'R41 compares one generated-Lean canonical-source synthetic contract, but it cannot adopt an Anneal V2 topology or decide real generated-source authority.'
    write_csv(HERE / 'gated-work-v11.csv', gates)

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
                  'source_v10_investigation_sha256': sha((V10 / 'investigation-final-v10.csv').read_bytes()),
                  'source_v10_crosswalk_sha256': sha((V10 / '3730-crosswalk-final-v10.csv').read_bytes()),
                  'r37_r41_completed': len(disposition),
                  'remaining_bounded_local_suites': len(remaining), 'gate_groups': len(gates)}
    (HERE / 'validation-v11.json').write_text(json.dumps(validation, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(validation, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    main()
