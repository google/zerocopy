#!/usr/bin/env python3
"""Validate the retained I107-I159 row audit and Lake control without tool execution."""
import csv
import hashlib
import json
from pathlib import Path
import re

support = Path(__file__).resolve().parent
package = support.parent
reports = package.parent
ledger_path = reports / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v23/support/investigation-final-v23.csv'
prior_path = reports / 'anneal-3731-i107-i159-independent-rereview-2026-09-29/support/row-review.csv'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline='') as stream:
        return list(csv.DictReader(stream))

metadata = json.loads((package / 'REPORT.json').read_text())
subjects = metadata['subjects']
assert sha(ledger_path) == subjects[0]['identity']['ledger_sha256']
assert sha(support / 'live-issue-scope.txt') == subjects[1]['identity']['scope_sha256']
assert sha(support / 'probe.py') == subjects[2]['identity']['probe_sha256']
issue = json.loads((support / 'issue-source.json').read_text())
assert issue['retained_slice_sha256'] == subjects[1]['identity']['scope_sha256']
assert issue['body_sha256'] == subjects[1]['identity']['full_body_sha256']
assert issue['comment_sha256'] == subjects[1]['identity']['scope_extension_comment_sha256']
assert issue['body_url'] == 'https://github.com/google/zerocopy/issues/3731'
assert issue['scope_extension_url'].startswith(issue['body_url'] + '#issuecomment-')

ledger = {row['id']: row for row in rows(ledger_path)}
prior = {row['id']: row for row in rows(prior_path)}
decisions = rows(support / 'row-decisions.csv')
assert [row['id'] for row in decisions] == [f'I{i:03d}' for i in range(107, 160)]
lines = (support / 'live-issue-scope.txt').read_text().splitlines()
assert len(lines) == len(decisions) == 53
assert {row['id'] for row in decisions if row['post_status'] == 'complete'} == {'I137', 'I138'}
assert {row['id'] for row in decisions if row['post_status'] == 'conditional'} == {'I141', 'I143'}
package_fields = [name for name in next(iter(ledger.values()))
                  if name.endswith(('_experiment_packages', '_evidence_packages'))
                  or name == 'prior_evidence_packages']
for row, line in zip(decisions, lines):
    match = re.fullmatch(r'\*\*(I\d{3}) — (.*?) \[([^]]+)\]\.\*\* (.*)', line)
    assert match is not None
    item, title, methods, scope = match.groups()
    source = ledger[item]
    assert row['id'] == item
    assert (title, methods, scope) == (source['title'], source['requested_methods'], source['requested_scope'])
    assert (row['title'], row['requested_scope']) == (title, scope)
    assert row['v23_status'] == row['post_status'] == source['v23_status']
    assert row['evidence_assessment'] and row['remaining_gate']
    cited = {name for name in row['cited_packages'].split(';') if name}
    expected = {name for field in package_fields for name in source[field].split(';') if name}
    if item == 'I145':
        expected.add('anneal-3731-i054-i106-postpublication-residual-audit-2026-09-29')
    assert cited == expected
    assert row['cited_packages'] == ';'.join(sorted(cited))
    if item in ('I126', 'I127'):
        assert row['cached_only_decision'] == 'new bounded component executed; full scope gated'
        assert row['remaining_gate'] != source['v23_specific_remaining_delta']
    elif item == 'I145':
        assert row['cached_only_decision'] == 'new cross-slice I076 witness; full scope gated'
        assert row['remaining_gate'] == source['v23_specific_remaining_delta']
    else:
        assert row['cached_only_decision'] == 'no distinct remaining cached-only cell identified'
        assert row['remaining_gate'] == source['v23_specific_remaining_delta']
    assert prior[item]['exact_requested_scope'] == scope

inventory = rows(support / 'cited-package-inventory.csv')
all_cited = {name for row in decisions for name in row['cited_packages'].split(';') if name}
assert len(inventory) == len(all_cited) == 125
assert [row['package'] for row in inventory] == sorted(all_cited)
for entry in inventory:
    root = reports / entry['package']
    assert (root / 'REPORT.md').is_file() and (root / 'REPORT.json').is_file()
    for field in ('report_md_sha256', 'report_json_sha256'):
        assert re.fullmatch(r'[0-9a-f]{64}', entry[field])

result = json.loads((support / 'results.json').read_text())
inputs = support / 'inputs'
assert set(result['input_sha256']) == {'Dep.lean', 'dynamic-lakefile.lean', 'static-lakefile.lean'}
for name, digest in result['input_sha256'].items():
    assert sha(inputs / name) == digest
dynamic = (inputs / 'dynamic-lakefile.lean').read_text()
static = (inputs / 'static-lakefile.lean').read_text()
assert 'run_cmd do' in dynamic and 'I126_MARKER_PATH' in dynamic
assert 'IO.FS.writeFile path "lake config executed\\n"' in dynamic
assert 'run_cmd' not in static and 'lean_lib Dep' in static
marker_digest = hashlib.sha256(b'lake config executed\n').hexdigest()
assert result['tool_sha256'] == {
    'lean': subjects[2]['identity']['lean_sha256'],
    'lake': subjects[2]['identity']['lake_sha256'],
    'sandbox_exec': subjects[2]['identity']['sandbox_exec_sha256'],
}
cases = result['cases']
assert [case['label'] for case in cases] == ['dynamic-allow', 'dynamic-deny', 'static-deny']
for case in cases:
    assert case['source_sha256'] == result['input_sha256']['Dep.lean']
    assert case['config_sha256'] == result['input_sha256'][case['config']]
    assert case['config'] == ('static-lakefile.lean' if case['label'] == 'static-deny'
                              else 'dynamic-lakefile.lean')
    assert case['argv'][-5:] == ['$BIN/lake', '--keep-toolchain', '--no-cache', 'build', 'Dep']
    assert case['seconds'] < 30
    assert re.fullmatch(r'[0-9a-f]{64}', case['stdout_sha256'])
    assert re.fullmatch(r'[0-9a-f]{64}', case['stderr_sha256'])
allow, denied, control = cases
assert allow['argv'] == ['$BIN/lake', '--keep-toolchain', '--no-cache', 'build', 'Dep']
assert allow['profile'] is None and allow['sandbox_denies_outside_write'] is False
assert allow['returncode'] == 0 and allow['marker_exists'] is True
assert allow['marker_sha256'] == marker_digest
for case in (denied, control):
    assert case['argv'][:3] == ['/usr/bin/sandbox-exec', '-f', f"$WORK/{case['label']}/profile.sb"]
    assert case['sandbox_denies_outside_write'] is True
    assert '(allow default)' in case['profile'] and '(deny network*)' in case['profile']
    assert f'(deny file-write* (subpath "$WORK/{case["label"]}/outside"))' in case['profile']
    assert case['marker_exists'] is False and case['marker_sha256'] is None
assert denied['returncode'] != 0
assert 'operation not permitted' in denied['stderr']
assert '$WORK/dynamic-deny/outside/marker.txt' in denied['stderr']
assert control['returncode'] == 0
assert 'Build completed successfully' in allow['stdout']
assert 'Build completed successfully' in control['stdout']
print('PASS: live scope, 53 v23 decisions, 125 cited packages, and three Lake controls')
