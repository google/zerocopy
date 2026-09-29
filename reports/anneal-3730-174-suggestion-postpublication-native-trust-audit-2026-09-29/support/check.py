#!/usr/bin/env python3
"""Read-only check of all 174 suggestion decisions and native plugin streams."""
import csv
import hashlib
import json
from pathlib import Path
import re

support = Path(__file__).resolve().parent
package = support.parent
reports = package.parent
v24_path = reports / 'anneal-3730-3731-final-coverage-audit-2026-09-29-v24/support/3730-crosswalk-final-v24.csv'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    with path.open(newline='') as stream:
        return list(csv.DictReader(stream))

metadata = json.loads((package / 'REPORT.json').read_text())
subjects = metadata['subjects']
assert sha(v24_path) == subjects[0]['identity']['v24_crosswalk_sha256']
assert sha(support / 'live-issue-body.md') == subjects[1]['identity']['issue_3730_body_sha256']
assert sha(support / 'live-issue-comment.md') == subjects[1]['identity']['issue_3730_comment_sha256']
assert sha(support / 'live-3731-crosswalk-comment.md') == subjects[1]['identity']['issue_3731_crosswalk_comment_sha256']
assert sha(support / 'probe.py') == subjects[2]['identity']['probe_sha256']
assert sha(support / 'results.json') == subjects[2]['identity']['result_sha256']
assert '174 numbered suggestions' in (support / 'live-issue-comment.md').read_text()

body = (support / 'live-issue-body.md').read_text()
comment = (support / 'live-3731-crosswalk-comment.md').read_text()
headings = list(re.finditer(r'(?m)^### ([A-O]\d{2})\. ([^\n]+)$', body))
cross = {item: (title.strip(), set(re.findall(r'I\d{3}', destinations)))
         for item, title, destinations in re.findall(
             r'(?m)^\| ([A-O]\d{2}) \| ([^|]+) \| ([^|]+) \|', comment)}
current = rows(support / 'row-decisions.csv')
v24 = {row['3730_id']: row for row in rows(v24_path)}
assert len(headings) == len(cross) == len(current) == len(v24) == 174
assert [row['id'] for row in current] == [match.group(1) for match in headings]
assert sum(len(dest) for _, dest in cross.values()) == 345
complete = {'C04', 'C13', 'N11'}
i145_links = {'A01', 'A02', 'A08', 'C01', 'F05', 'G01', 'G02', 'G12', 'L01', 'O03'}
package_fields = [key for key in next(iter(v24.values()))
                  if key.endswith(('_experiment_packages', '_evidence_packages', '_review_package'))]
for n, (row, heading) in enumerate(zip(current, headings)):
    item, original = heading.groups()
    end = headings[n + 1].start() if n + 1 < len(headings) else body.index('\n---\n\n## Suggested sequencing', heading.end())
    requested = body[heading.start():end].strip()
    old = v24[item]
    title, destinations = cross[item]
    assert row['id'] == item and row['original_heading'] == original
    assert row['requested_text'] == requested
    assert row['requested_text_sha256'] == hashlib.sha256(requested.encode()).hexdigest()
    assert row['consolidation_title'] == title == old['suggestion']
    assert set(row['destinations'].split(';')) == destinations == set(old['3731_destinations'].split(';'))
    assert row['audit_status'] == row['v24_status'] == old['v24_status']
    assert (row['entire_requested_scope_supported'] == 'true') == (item in complete)
    assert row['scope_assessment'] and row['cached_only_decision'] and row['remaining_gate']
    cited = {name for name in row['cited_packages'].split(';') if name}
    expected = {name for field in package_fields for name in old[field].split(';') if name}
    assert cited == expected
    assert row['cited_packages'] == ';'.join(sorted(cited))
    assert row['next_prerequisite'] == old['v24_next_prerequisite']
    if item == 'G09':
        assert row['destinations'] == 'I069;I126'
        assert row['cached_only_decision'].startswith('new bounded native-plugin control executed')
        assert 'native-plugin initializer' in row['remaining_gate']
        assert row['remaining_gate'] != old['v24_specific_remaining_delta']
    else:
        assert row['remaining_gate'] == old['v24_specific_remaining_delta']
    if item == 'D07':
        assert 'v24 I076 control directly linked' == row['new_evidence_relation']
    elif item in i145_links:
        assert 'v24 I076→I145 cross-slice witness only' == row['new_evidence_relation']
    elif item == 'G09':
        assert row['new_evidence_relation'] == 'new native-plugin I126 control, directly linked'
    else:
        assert row['new_evidence_relation'].startswith('I005/I127 have no direct')

assert {row['id'] for row in current if row['audit_status'] == 'complete'} == complete
assert {row['id'] for row in current if row['audit_status'] == 'not-run'} == {'F03', 'F04', 'G03', 'G15', 'L09'}
assert {row['id'] for row in current if row['audit_status'] == 'conditional'} == {'E01', 'E02', 'E03', 'L10'}
assert {row['id'] for row in current if row['cached_only_decision'].startswith('new bounded')} == {'G09'}
inverse = {item: {row['id'] for row in current if item in row['destinations'].split(';')}
           for item in ('I005', 'I076', 'I126', 'I127', 'I145')}
assert inverse == {'I005': set(), 'I076': {'D07'}, 'I126': {'G09'},
                   'I127': set(), 'I145': i145_links}

inventory = rows(support / 'cited-package-inventory.csv')
all_cited = {name for row in current for name in row['cited_packages'].split(';') if name}
assert len(inventory) == len(all_cited) == 111
assert [entry['package'] for entry in inventory] == sorted(all_cited)
for entry in inventory:
    root = reports / entry['package']
    assert (root / 'REPORT.md').is_file() and (root / 'REPORT.json').is_file()
    assert all(re.fullmatch(r'[0-9a-f]{64}', entry[key])
               for key in ('report_md_sha256', 'report_json_sha256'))

inputs = support / 'inputs'
result = json.loads((support / 'results.json').read_text())
assert result['tool_sha256']['lean'] == subjects[2]['identity']['lean_sha256']
assert result['input_sha256']['plugin__probe_Plugin.dylib'] == subjects[2]['identity']['plugin_sha256']
assert result['input_sha256'] == {name: sha(inputs / name) for name in
                                  ('Plugin.lean', 'Proof.lean', 'plugin__probe_Plugin.dylib')}
assert (inputs / 'Plugin.lean').read_text() == (
    'import Lean\ninitialize do\n'
    '  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n'
    '  if !p.isEmpty then IO.FS.writeFile p "plugin-v1"\n')
assert result['case_timeout_seconds'] == 15
assert result['resource_limits'] == {'cpu_seconds': 10, 'nofile': 256, 'file_bytes': 16777216}
cases = result['cases']
assert [case['label'] for case in cases] == ['plugin-allow', 'plugin-deny', 'plain-deny']
for case in cases:
    name = case['label']
    assert case['process_exited'] and not case['timed_out'] and case['seconds'] < 15
    assert case['plugin_sha256'] == subjects[2]['identity']['plugin_sha256']
    assert case['proof_sha256'] == result['input_sha256']['Proof.lean']
    assert case['argv'][:4] == ['/usr/bin/sandbox-exec', '-f', f'$WORK/{name}/profile.sb', '$BIN/lean']
    assert case['argv'][-1] == 'Proof.lean'
    assert '(deny network*)' in case['profile']
    for channel in ('stdout', 'stderr'):
        raw = (support / 'raw-streams' / f'{name}.{channel}').read_bytes()
        assert hashlib.sha256(raw).hexdigest() == case[f'{channel}_raw_sha256']
        if name != 'plugin-deny':
            assert raw == b'' == case[channel].encode()
    assert case['plugin_used'] == (name != 'plain-deny')
    assert case['marker_write_denied'] == (name != 'plugin-allow')
allow, denied, plain = cases
assert allow['returncode'] == 0 and allow['marker_exists']
assert allow['marker_sha256'] == hashlib.sha256(b'plugin-v1').hexdigest()
assert '(deny file-write*' not in allow['profile']
for case in (denied, plain):
    assert case['returncode'] == (1 if case is denied else 0)
    assert not case['marker_exists'] and case['marker_sha256'] is None
    assert f'(deny file-write* (subpath "$WORK/{case["label"]}/outside"))' in case['profile']
raw_denial = (support / 'raw-streams/plugin-deny.stderr').read_text()
assert 'operation not permitted' in raw_denial
path = raw_denial.split('  file: ', 1)[1].strip()
assert path.endswith('/plugin-deny/outside/marker.txt')
assert path.startswith('/Users/josh/Codex/Meta/Data/20260929-lean-report-review/')
work = path.removesuffix('/plugin-deny/outside/marker.txt')
assert denied['stderr'] == raw_denial.replace(work, '$WORK')
assert '--plugin=$WORK/plugin-allow/workspace/plugin__probe_Plugin.dylib' in allow['argv']
assert '--plugin=$WORK/plugin-deny/workspace/plugin__probe_Plugin.dylib' in denied['argv']
assert not any(arg.startswith('--plugin=') for arg in plain['argv'])

excluded = json.loads((support / 'excluded-basename-attempt.json').read_text())
assert excluded['classification'].startswith('excluded setup attempt')
assert [case['returncode'] for case in excluded['cases']] == [1, 1, 0]
assert all(not case['marker_exists'] for case in excluded['cases'])
assert all("initializer not found 'initialize_plugin-v1'" in case['stderr']
           for case in excluded['cases'][:2])
print('PASS: 174 live requests, 345 links, 111 citations, native-plugin controls and excluded setup attempt')
