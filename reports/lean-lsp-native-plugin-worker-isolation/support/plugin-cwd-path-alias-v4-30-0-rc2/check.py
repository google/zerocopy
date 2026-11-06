#!/usr/bin/env python3
"""Offline checks for the bounded I125 cwd/path-alias transcript."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent.parent / 'anneal-3730-plugin-reversal-worker-order-2026-09-29' / 'support'
PINNED_LEAN_SHA256 = 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

rows = json.loads((HERE / 'transcript.json').read_text())
assert [x['seq'] for x in rows] == list(range(len(rows)))
subject = next(x for x in rows if x['kind'] == 'subject')
assert subject['lean_sha256'] == PINNED_LEAN_SHA256
assert subject['v1_sha256'] == sha(PRIOR / 'artifacts/plugin-v1.dylib')
assert subject['v2_sha256'] == sha(PRIOR / 'artifacts/plugin-v2.dylib')
assert subject['free_memory_percent'] >= 25 and subject['free_disk_bytes'] >= 10 * 1024**3

cli = {x['label']: x for x in rows if x['kind'] == 'cli'}
assert list(cli) == ['lean-path-a-cwd-empty', 'cwd-a', 'cwd-b']
assert cli['lean-path-a-cwd-empty']['exit'] != 0
assert cli['lean-path-a-cwd-empty']['resolved'] is None
assert cli['lean-path-a-cwd-empty']['marker'] is None
assert 'no such file or directory' in cli['lean-path-a-cwd-empty']['stderr']
assert cli['cwd-a']['exit'] == 0 and cli['cwd-a']['marker'] == 'plugin-v1'
assert cli['cwd-b']['exit'] == 0 and cli['cwd-b']['marker'] == 'plugin-v2'
assert cli['cwd-b']['lean_path'] == cli['cwd-a']['lean_path']

phases = [x for x in rows if x['kind'] == 'phase']
assert [(x['label'], x['marker'], x['resolved_sha256']) for x in phases] == [
    ('alias-a-first-worker', 'plugin-v1', subject['v1_sha256']),
    ('alias-b-new-worker', 'plugin-v2', subject['v2_sha256']),
    ('alias-b-fresh-server', 'plugin-v2', subject['v2_sha256'])]
assert all('error' not in x['wait'] and 'error' not in x['goal'] for x in phases)
assert all(x['goal'].get('result') is not None for x in phases)
switch = next(x for x in rows if x['kind'] == 'alias_switch')
assert phases[0]['seq'] < switch['seq'] < phases[1]['seq']
assert switch['resolved_sha256'] == subject['v2_sha256']
old = next(x for x in rows if x['kind'] == 'old_worker_goal')
assert phases[1]['seq'] < old['seq'] and 'error' not in old['goal']
starts = [x for x in rows if x['kind'] == 'server_start']
stops = [x for x in rows if x['kind'] == 'server_stop']
assert [x['label'] for x in starts] == [x['label'] for x in stops] == ['retained', 'fresh']
assert starts[0]['seq'] < stops[0]['seq'] < starts[1]['seq'] < stops[1]['seq']
assert all(x['exit'] == 0 for x in stops)
print('I125 plugin cwd/path-alias transcript: OK')
