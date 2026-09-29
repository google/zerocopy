#!/usr/bin/env python3
"""Check retained evidence and the final fixture without launching Lean."""
import hashlib
import json
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
transcript = root / (sys.argv[1] if len(sys.argv) > 1 else 'transcript.json')
data = json.loads(transcript.read_text())
events = data['events']
sha = lambda blob: hashlib.sha256(blob).hexdigest()
by_kind = lambda kind: [e for e in events if e['kind'] == kind]
index = lambda kind: next(i for i, e in enumerate(events) if e['kind'] == kind)

assert '4.30.0-rc2' in data['lean_version']
assert '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in data['lean_version']
builds = by_kind('build_dependency')
assert [e['value'] for e in builds] == [3, 4]
assert all(e['returncode'] == 0 for e in builds)
for build in builds:
    assert build['source_sha256'] == sha(f"def sharedValue : Nat := {build['value']}\n".encode())
assert data['old_olean_sha256'] == builds[0]['olean_sha256']
assert data['new_olean_sha256'] == builds[1]['olean_sha256']
assert data['old_olean_sha256'] != data['new_olean_sha256']
assert sha((root / 'fixture' / 'Dep.olean').read_bytes()) == data['new_olean_sha256']
assert sha((root / 'fixture' / 'Dep.lean').read_bytes()) == builds[1]['source_sha256']

proof = b'import Dep\ntheorem current : sharedValue = 3 := by\n  rfl\n'
proof_hash = sha(proof)
for name in ('OldOpen.lean', 'NewOpen.lean'):
    assert (root / 'fixture' / name).read_bytes() == proof
for kind in ('old_worker_before_change', 'new_worker_same_server_after_dependency_rebuild',
             'closed_reopened_worker_after_dependency_rebuild', 'fresh_batch_after_dependency_rebuild'):
    assert by_kind(kind)[0]['source_sha256'] == proof_hash

assert data['old_worker_goal_before']['result'] == {'goals': [], 'rendered': 'no goals'}
assert data['old_worker_goal_after']['result'] == {'goals': [], 'rendered': 'no goals'}
late_old = by_kind('old_worker_after_new_worker')
if transcript.name == 'simultaneous-transcript.json':
    assert len(late_old) == 1
if late_old:
    assert len(late_old) == 1
    assert data['old_worker_goal_after_new_worker']['result'] == {'goals': [], 'rendered': 'no goals'}
    assert late_old[0]['goal'] == data['old_worker_goal_after_new_worker']
    assert late_old[0]['source_sha256'] == proof_hash
for key in ('new_worker_goal_same_server', 'reopened_worker_goal_same_server'):
    assert data[key]['result']['goals'] == ['⊢ sharedValue = 3']
assert data['fresh_batch_returncode'] == 1
batch = by_kind('fresh_batch_after_dependency_rebuild')[0]
assert batch['returncode'] == 1 and 'Tactic `rfl` failed' in batch['stdout']

assert len(by_kind('server_start')) == len(by_kind('server_exit')) == 1
assert by_kind('server_exit')[0]['returncode'] == 0
assert index('old_worker_before_change') < index('artifact_changed') < index('old_worker_after_dependency_rebuild')
assert index('old_worker_after_dependency_rebuild') < index('new_worker_same_server_after_dependency_rebuild')
assert index('new_worker_same_server_after_dependency_rebuild') < index('closed_reopened_worker_after_dependency_rebuild')
if late_old:
    assert index('new_worker_same_server_after_dependency_rebuild') < index('old_worker_after_new_worker')
    assert index('old_worker_after_new_worker') < index('closed_reopened_worker_after_dependency_rebuild')
assert index('closed_reopened_worker_after_dependency_rebuild') < index('fresh_batch_after_dependency_rebuild')
assert any(e.get('message', {}).get('method') == 'workspace/didChangeWatchedFiles'
           for e in events[index('artifact_changed'):index('old_worker_after_dependency_rebuild')])
assert any(e.get('message', {}).get('method') == 'textDocument/didClose'
           for e in events[index('new_worker_same_server_after_dependency_rebuild'):
                           index('closed_reopened_worker_after_dependency_rebuild')])

def failure_diagnostic(name, version):
    return any(d['uri'].endswith('/' + name) and d.get('version') == version
               and any('Tactic `rfl` failed' in item.get('message', '') for item in d['diagnostics'])
               for d in data['diagnostics'])

assert failure_diagnostic('NewOpen.lean', 1)
assert failure_diagnostic('OldOpen.lean', 2)
print('PASS: pinned tool, artifact/source hashes, one-server chronology, goals, diagnostics, and batch result')
