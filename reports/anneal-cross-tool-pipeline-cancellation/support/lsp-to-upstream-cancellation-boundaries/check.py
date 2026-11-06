#!/usr/bin/env python3
"""Validate retained direct Lean/Cargo cancellation evidence without executing tools."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
data = json.loads((ROOT/'results.json').read_text())
events = data['events']
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert '4.30.0-rc2' in data['lean_version']
assert '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in data['lean_version']
assert 'cargo 1.98.1' in data['cargo_version']
assert data['preflight']['free_memory_percent'] >= 25
assert data['preflight']['disk_free_bytes'] >= 5*1024**3

lean = data['lean']
assert sha(ROOT/'fixture'/'Slow.lean') == lean['source_sha256']
assert lean['cancel_response']['id'] == lean['request_id']
assert lean['cancel_response']['error']['code'] == -32800
assert lean['later_wait_response']['result'] == {}
assert lean['batch_returncode'] == 0 and lean['batch_stderr'] == ''
client_cancel = next(e for e in events if e['kind']=='client_message'
                     and e['message'].get('method')=='$/cancelRequest')
assert client_cancel['message']['params']['id'] == lean['request_id']
server_cancel = next(e for e in events if e['kind']=='server_message'
                     and e['message'].get('id')==lean['request_id']
                     and e['message'].get('error',{}).get('code')==-32800)
assert server_cancel['seconds'] > client_cancel['seconds']
assert any(e['kind']=='server_message' and e['message'].get('id')==lean['later_wait_response']['id']
           and e['seconds'] > server_cancel['seconds'] for e in events)
starts=[e for e in events if e['kind']=='lean_start']
exits=[e for e in events if e['kind']=='lean_exit']
assert len(starts)==len(exits)==1 and starts[0]['pid']==exits[0]['pid']
assert exits[0]['returncode']==0 and exits[0]['group_after']==[]
assert any(e['kind']=='server_message' and e['message'].get('method')=='textDocument/publishDiagnostics'
           and e['message']['params']['diagnostics']==[] for e in events)

cargo = data['cargo']
assert sha(ROOT/'fixture'/'Cargo.toml')==cargo['cargo_toml_sha256']
assert sha(ROOT/'fixture'/'build.rs')==cargo['build_script_sha256']
assert cargo['victim_exit']==-15 and cargo['peer_exit']==cargo['retry_exit']==0
assert cargo['victim_artifact_after_cancel'] is False
assert cargo['peer_artifact_after_completion'] is True
assert cargo['victim_artifact_after_retry'] is True
assert cargo['peer_after_victim_cancel']['poll'] is None
assert cargo['peer_after_victim_cancel']['group']
assert cargo['after']=={'victim':[], 'peer':[]}
for label, pid, marker in [('victim',cargo['victim_pid'],cargo['victim_marker']),
                           ('peer',cargo['peer_pid'],cargo['peer_marker'])]:
    build_pid, sleep_pid=map(int,marker.split())
    group={row['pid']:row for row in cargo['before'][label]}
    assert {pid,build_pid,sleep_pid} <= set(group)
    assert all(row['pgid']==pid for row in group.values())
print('PASS: processed Lean cancellation and continued service; Cargo descendant cleanup, peer survival, and retry')
