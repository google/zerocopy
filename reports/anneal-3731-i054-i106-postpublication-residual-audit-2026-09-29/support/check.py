#!/usr/bin/env python3
"""Check the retained 53-row audit and the I076 Charon specimens offline."""
import csv
import hashlib
import json
from pathlib import Path
import re

support = Path(__file__).resolve().parent
package = support.parent
reports = package.parent
v23 = reports / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v23'
prior = reports / 'anneal-3731-i054-i106-independent-rereview-2026-09-29'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline='') as stream:
        return list(csv.DictReader(stream))

metadata = json.loads((package / 'REPORT.json').read_text())
assert sha(support / 'probe.py') == metadata['subjects'][2]['identity']['probe_sha256']
assert sha(support / 'live-issue-scope.txt') == metadata['subjects'][1]['identity']['scope_sha256']
assert sha(v23 / 'support/investigation-final-v23.csv') == metadata['subjects'][0]['identity']['ledger_sha256']

ledger = {row['id']: row for row in rows(v23 / 'support/investigation-final-v23.csv')}
earlier = {row['id']: row for row in rows(prior / 'support/row-review.csv')}
decisions = rows(support / 'row-decisions.csv')
assert [row['id'] for row in decisions] == [f'I{i:03d}' for i in range(54, 107)]
issue_lines = (support / 'live-issue-scope.txt').read_text().splitlines()
assert len(issue_lines) == 53
for row, line in zip(decisions, issue_lines):
    match = re.fullmatch(r'\*\*(I\d{3}) — (.*?) \[([^]]+)\]\.\*\* (.*)', line)
    assert match is not None
    item, title, methods, scope = match.groups()
    assert (row['id'], row['title'], row['requested_scope']) == (item, title, scope)
    source = ledger[item]
    assert (title, methods, scope) == (source['title'], source['requested_methods'], source['requested_scope'])
    assert row['v23_status'] == row['post_status'] == source['v23_status']
    assert row['cited_packages'] == earlier[item]['cited_packages']
    assert row['remaining_gate'] == source['v23_specific_remaining_delta']
    assert row['evidence_assessment']
    assert row['cached_only_decision'] == (
        'new bounded component executed; full scope gated' if item == 'I076'
        else 'no distinct remaining cached-only cell identified')

inventory = rows(support / 'cited-package-inventory.csv')
cited = {name for row in decisions for name in row['cited_packages'].split(';') if name}
assert {row['package'] for row in inventory} == cited
assert len(inventory) == len(cited) == 86
for entry in inventory:
    name = entry['package']
    assert (reports / name / 'REPORT.md').is_file()
    assert (reports / name / 'REPORT.json').is_file()
    assert re.fullmatch(r'[0-9a-f]{64}', entry['report_md_sha256'])
    assert re.fullmatch(r'[0-9a-f]{64}', entry['report_json_sha256'])

result = json.loads((support / 'results.json').read_text())
assert set(result['outputs']) == {'left', 'right'}
for name, value in (('left', '11'), ('right', '29')):
    artifact = support / 'artifacts' / f'{name}.llbc'
    recorded = result['outputs'][name]
    assert sha(artifact) == recorded['sha256']
    assert artifact.stat().st_size == recorded['bytes']
    data = json.loads(artifact.read_text())
    trans = data['translated']
    assert data['charon_version'] == '0.1.210' and data['has_errors'] is False
    assert trans['crate_name'] == 'shared_unit'
    assert trans['files'][0]['name']['Local'] == f'{name}/src/lib.rs'
    source_text = (support / 'inputs' / name / 'src/lib.rs').read_text()
    assert trans['files'][0]['contents'] == source_text == f'pub fn marker() -> u32 {{ {value} }}\n'
    local = [f for f in trans['fun_decls'] if f and f['item_meta']['is_local']]
    assert len(local) == 1
    assert [part['Ident'][0] for part in local[0]['item_meta']['name']] == ['shared_unit', 'marker']
    literal = local[0]['body']['Structured']['body']['statements'][0]['kind']['Assign'][1]['Use'][0]['Const']['kind']['Literal']['Scalar']['Unsigned']
    assert literal == ['U32', value]
    assert recorded['projection'] == {
        'charon_version': '0.1.210', 'crate_name': 'shared_unit', 'has_errors': False,
        'source_name': f'{name}/src/lib.rs', 'source_text': source_text,
        'function_name': ['shared_unit', 'marker'], 'literal': ['U32', value],
    }
    assert result['input_sha256'][f'{name}/src/lib.rs'] == sha(support / 'inputs' / name / 'src/lib.rs')
assert result['outputs']['left']['sha256'] != result['outputs']['right']['sha256']
assert [command['case'] for command in result['commands']] == ['left', 'right']
assert all(command['returncode'] == 0 for command in result['commands'])
assert result['tool_sha256']['charon'] == metadata['subjects'][2]['identity']['charon_sha256']
print('PASS: live issue scope, 53 v23 decisions, 86 cited packages, and distinct I076 Charon outputs')
