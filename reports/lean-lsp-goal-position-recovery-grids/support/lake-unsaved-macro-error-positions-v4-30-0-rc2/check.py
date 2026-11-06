#!/usr/bin/env python3
"""Offline checks for retained Lake unsaved macro/error position evidence."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
r = json.loads((ROOT / 'results.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert r['tools'] == {
    'lake_sha256': '9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb',
    'lean_sha256': 'b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'}
assert r['preflight']['memory_free_percent'] >= 20
assert r['preflight']['disk_free_bytes'] >= 10 * 1024**3
assert 0 < r['resources']['peak_process_group_rss_kib'] <= 1536 * 1024
assert 0 < r['resources']['elapsed_seconds'] <= 300
assert r['resources']['samples'] >= 10
for name in ('Dep.lean', 'Proof.lean'):
    data = (ROOT / 'fixture' / name).read_text()
    assert data == r['source'][name]
    assert sha(ROOT / 'fixture' / name) == r['source']['sha256'][name]
assert r['source']['variants']['solved'] == r['source']['variants']['restored'] == r['source']['Proof.lean']
assert r['source']['variants']['hole'].endswith('  solve_macro ?_\n')
assert r['source']['variants']['syntax'].endswith('  solve_macro )\n')
assert r['build']['exit'] == r['setup']['exit'] == 0
assert 'Built Dep' in r['build']['stdout'] and 'Built Proof' in r['build']['stdout']
assert '$WORK/dep/.lake/build/lib/lean/Dep.olean' in r['setup']['stdout']
assert all(r['artifacts'].values()) and r['artifacts']['Dep.olean'] != r['artifacts']['Proof.olean']
assert {k:v['exit'] for k,v in r['batches'].items()} == {'solved':0,'hole':1,'syntax':1}
assert 'unsolved goals' in r['batches']['hole']['stdout']
assert "unexpected token ')'" in r['batches']['syntax']['stdout']
assert all(v['result'] == {} for v in r['waits'].values())
assert r['stop'] == {'exit':0,'stderr':''}
assert len(r['connect']['result']['sessionId']) > 0
assert r['positions'] == {'incoming':[4,2], 'macro_body':[4,8], 'tactic_end':[4,16], 'next_line':[5,0], 'eof':[5,2]}
expected = {
    'solved':   ['goal','empty','empty','empty','null'],
    'hole':     ['goal','goal','goal','goal','null'],
    'syntax':   ['goal','empty','null','null','null'],
    'restored': ['goal','empty','empty','empty','null']}

def render(x):
    if isinstance(x, str): return x
    if isinstance(x, list): return ''.join(map(render, x))
    if isinstance(x, dict):
        if 'info' in x and 'subexprPos' in x: return ''
        for key in ('text','append','tag'):
            if key in x: return render(x[key])
    raise AssertionError(f'unknown rich text node: {x!r}')

for version,(name,classes) in enumerate(expected.items(),1):
    assert len(r['live'][name]) == 5
    for (point,coords),kind in zip(r['positions'].items(),classes):
        pair=r['live'][name][point]
        assert pair['position'] == {'line':coords[0], 'character':coords[1]}
        plain=pair['plain'];rich=pair['rich']
        assert 'error' not in plain and 'error' not in rich
        p=plain['result'];q=rich['result']
        if kind == 'null': assert p is None and q is None
        elif kind == 'empty': assert p['goals'] == [] and q['goals'] == []
        else:
            assert len(p['goals']) == len(q['goals']) == 1
            assert p['goals'][0] == 'h : depValue = 7\n⊢ depValue = 7'
            g=q['goals'][0]
            assert g['hyps'][0]['names'] == ['h']
            assert render(g['hyps'][0]['type']) == 'depValue = 7'
            assert render(g['type']) == 'depValue = 7'
    assert r['waits'][name]['result'] == {}
assert [len(r['diagnostics'][n][-1]) for n in expected] == [0,2,1,0]
assert all(d['severity']==1 for n in ('hole','syntax') for d in r['diagnostics'][n][-1])
assert len(r['events']) >= 100
requests=[e['message'] for e in r['events'] if e['direction']=='client' and e['message'].get('method') in ('$/lean/plainGoal','$/lean/rpc/call')]
assert len(requests)==40
assert len([m for m in requests if m['method']=='$/lean/plainGoal'])==20
assert len([m for m in requests if m['method']=='$/lean/rpc/call'])==20
ids={m['id'] for m in requests}
replies=[e['message'] for e in r['events'] if e['direction']=='server' and e['message'].get('id') in ids]
assert {m['id'] for m in replies}==ids and len(replies)==40
assert [e['message']['params']['textDocument']['version'] for e in r['events'] if e['direction']=='client' and e['message'].get('method')=='textDocument/didChange'] == [2,3,4]
print('PASS: Lake import, batch controls, 20 plain/rich unsaved macro/error pairs, diagnostics, resource bounds, shutdown')
