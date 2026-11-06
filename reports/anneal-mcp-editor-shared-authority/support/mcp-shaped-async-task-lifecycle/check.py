#!/usr/bin/env python3
"""Offline checks of retained toy-task transcript and real Lean observations."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE / 'work'
R = json.loads((HERE / 'results.json').read_text())


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


assert R['schema'] == 1
assert R['boundary'].startswith('Toy JSON-RPC')
assert R['availability']['npm_global_exit'] == 0
assert all(v is None for v in R['availability']['python_modules'].values())
assert all(v is None for v in R['availability']['named_executables'].values())
assert all('mcp' not in v.lower() for v in R['availability']['npm_global_packages'])
assert sha(ROOT / 'Proof.lean') == R['fixture']['sha256']
assert hashlib.sha256(R['fixture']['text'].encode()).hexdigest() == R['fixture']['sha256']
assert R['lean_sha256'] == 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'

neg = R['negotiation']
assert neg['async']['result']['protocolVersion'] == 'toy-async-v2'
assert neg['async']['result']['capabilities']['toyTasks'] is True
assert neg['async_reconnect']['result']['protocolVersion'] == 'toy-async-v2'
assert {x['name'] for x in neg['async_tools']['result']['tools']} == {
    'start_goal', 'get_task', 'result_task', 'cancel_task', 'release_task'}
assert neg['legacy']['result']['protocolVersion'] == 'toy-sync-v1'
assert neg['legacy']['result']['capabilities']['toyTasks'] is False
assert {x['name'] for x in neg['legacy_tools']['result']['tools']} == {'goal_sync'}
assert neg['legacy_rejected_async']['error']['code'] == -32602
assert neg['legacy_sync']['status'] == 'complete'


def lean_goal(result: dict) -> None:
    assert result['wait']['result'] == {}
    assert result['goal']['result']['goals'] == ['n : Nat\n⊢ n + 0 = n']
    diagnostics = result['diagnostics']
    assert diagnostics['version'] == 1
    assert len(diagnostics['diagnostics']) == 1
    assert 'unsolved goals' in diagnostics['diagnostics'][0]['message']
    assert isinstance(result['lsp_pid'], int) and result['lsp_pid'] > 0


lean_goal(neg['legacy_sync']['result'])
task = R['async_task']
handle = task['accepted']['handle']
assert task['accepted'] == {'status': 'accepted', 'handle': handle, 'progressToken': handle}
assert task['awaiting'][-1]['phase'] == 'waiting'
assert task['pending']['status'] == 'waiting'
assert task['released']['status'] == 'released'
assert task['disconnected_bridge']['bridge_exit'] == 0
assert task['reconnect_poll'][-1]['phase'] == 'complete'
assert task['retrieved']['status'] == 'complete'
assert task['retrieved']['source_sha256'] == R['fixture']['sha256']
lean_goal(task['retrieved']['result'])
assert task['expired'] == {'status': 'expired', 'handle': handle}
assert R['processes']['C']['bridge_exit'] == R['processes']['legacy']['bridge_exit'] == 0
assert len({task['disconnected_bridge']['bridge_pid'], R['processes']['C']['bridge_pid'],
            R['processes']['legacy']['bridge_pid']}) == 3

cancel = R['cancellation']
assert cancel['awaiting'][-1]['phase'] == 'waiting'
assert cancel['request']['status'] == 'cancel_requested'
assert cancel['poll'][-1]['phase'] == 'cancelled'
assert cancel['result'] == {'status': 'cancelled', 'handle': cancel['accepted']['handle']}

failure = R['partial_failure']
assert failure['awaiting'][-1]['phase'] == 'waiting'
assert failure['poll'][-1]['phase'] == 'failed'
assert failure['result']['status'] == 'failed'
assert 'injected failure after Lean goal before result publication' in failure['result']['error']
assert failure['result']['partial']['goal_observed'] is True
assert 'result' not in failure['result']

recovery = R['recovery']
assert recovery['awaiting'][-1]['phase'] == 'waiting'
assert recovery['poll'][-1]['phase'] == 'complete'
assert recovery['result']['status'] == 'complete'
lean_goal(recovery['result']['result'])
assert recovery['result']['result']['goal']['result'] == task['retrieved']['result']['goal']['result']

handles = {task['accepted']['handle'], cancel['accepted']['handle'],
           failure['accepted']['handle'], recovery['accepted']['handle']}
assert len(handles) == len(R['task_states']) == 4
assert handles == set(R['task_states'])
for name, item in R['task_states'].items():
    directory = ROOT / 'tasks' / name
    assert json.loads((directory / 'state.json').read_text()) == item
    assert sha(directory / 'source.lean') == R['fixture']['sha256']
    assert item['source_sha256'] == R['fixture']['sha256']
    assert (directory / 'worker.pid').is_file()
    assert (directory / 'worker.stderr').is_file()
    assert item['phase'] in ('complete', 'cancelled', 'failed')
assert R['task_states'][handle]['phase'] == 'complete'
assert R['task_states'][cancel['accepted']['handle']]['phase'] == 'cancelled'
assert R['task_states'][failure['accepted']['handle']]['phase'] == 'failed'
assert R['task_states'][recovery['accepted']['handle']]['phase'] == 'complete'
assert R['task_states'][handle]['lsp_exit'] == R['task_states'][failure['accepted']['handle']]['lsp_exit'] == 0

notifications = [entry['message'] for log in R['client_transcripts'].values() for entry in log
                 if entry['direction'] == 'server' and entry['message'].get('method') == 'notifications/progress']
assert notifications
assert any(x['params']['handle'] == handle for x in notifications)
assert any(x['params']['phase'] == 'checking' for x in notifications)
assert any(x['params']['phase'] == 'failed' for x in notifications)
assert any(x['params']['phase'] == 'complete' for x in notifications)
assert not any(x['params']['handle'] == handle for x in [entry['message']
               for entry in R['client_transcripts']['C'] if entry['direction'] == 'server'
               and entry['message'].get('method') == 'notifications/progress'])

summary = {'tasks': 4, 'real_lean_goal_queries': 4, 'bridge_reconnect_retrieved': True,
           'result_expired': True, 'cancel_before_check': True,
           'partial_failure_after_lsp': True, 'recovery_after_failure': True,
           'toy_revision_fallback': True, 'progress_notifications': len(notifications),
           'installed_mcp_sdk_or_adapter_in_scope': False}
(HERE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('PASS: four toy tasks, real Lean goal, reconnect retrieval, expiry, cancel, partial failure, recovery, fallback')
