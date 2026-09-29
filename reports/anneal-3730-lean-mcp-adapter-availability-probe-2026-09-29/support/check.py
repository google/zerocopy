#!/usr/bin/env python3
"""Offline assertions for adapter inventory and synthetic two-client MCP shapes."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
R=json.loads((HERE/'results.json').read_text())
assert R['schema']==1 and len(R['events'])==11
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def event(client,step):
    hits=[e for e in R['events'] if e['client']==client and e['step']==step]
    assert len(hits)==1,(client,step)
    return hits[0]['reply']
def data(m):
    result=m['result'];return result.get('isError'),json.loads(result['content'][0]['text'])
a=R['availability']
assert all(v is None for v in a['named_resolutions'].values())
assert all(not row['matching_executables'] for row in a['path_scan'])
assert a['checkout_matching_paths'] and all(p.startswith('./reports/') for p in a['checkout_matching_paths'])
assert any('lean-mcp-implementations' in p for p in a['checkout_matching_paths'])
assert any('adapter-availability-probe' in p for p in a['checkout_matching_paths'])
w=R['workspace'];v1=HERE/'artifacts/Proof-v1.lean';v2=HERE/'artifacts/Proof-v2.lean'
assert w['initial_sha256']==w['retained_v1_sha256']==sha(v1)
assert w['final_sha256']==w['expected_final_sha256']==w['retained_v2_sha256']==sha(v2)
assert w['initial_text']==v1.read_text() and w['final_text']==v2.read_text()
for client in ('A','B'):
    init=event(client,'initialize');assert init['result']['serverInfo']['name']=='synthetic-lean-lsp-bridge'
    names=[x['name'] for x in event(client,'tools/list')['result']['tools']]
    assert names==['get_goal','slow_goal','apply_edit']
    assert R['processes'][client]['bridge_rc']==0
    assert json.loads(R['processes'][client]['stderr'])['lsp_rc']==0
cancel=event('A','cancelled-42');assert cancel['id']==42 and cancel['error']['code']==-32800
a0=data(event('A','parallel-43'));b0=data(event('B','uncancelled-42'))
assert a0[0] is False and b0[0] is False
assert a0[1]['status']==b0[1]['status']=='current'
assert a0[1]['source_sha256']==b0[1]['source_sha256']==w['initial_sha256']
assert a0[1]['goal']['result']['goals']==b0[1]['goal']['result']['goals']
assert 'n + 0 = n' in a0[1]['goal']['result']['rendered']
assert any('unsolved goals' in d['message'] for d in a0[1]['diagnostics']['diagnostics'])
assert a0[1]['lsp_pid']!=b0[1]['lsp_pid']
applied=data(event('A','apply-v2'));assert applied==(False,{'status':'applied','old_sha256':w['initial_sha256'],'new_sha256':w['final_sha256']})
stale=data(event('B','stale-v1'));assert stale==(True,{'status':'stale','expected':w['initial_sha256'],'current':w['final_sha256']})
for client in ('A','B'):
    err,fresh=data(event(client,'fresh-v2'))
    assert err is False and fresh['status']=='current' and fresh['source_sha256']==w['final_sha256']
    assert fresh['goal']['result']['rendered']=='no goals'
    assert fresh['diagnostics']['diagnostics']==[]
    assert fresh['lsp_document_version']==2
assert data(event('A','fresh-v2'))[1]['lsp_pid']==a0[1]['lsp_pid']
assert data(event('B','fresh-v2'))[1]['lsp_pid']==b0[1]['lsp_pid']
for client in ('A','B'):
    client_messages=[x['message'] for x in R['client_transcripts'][client] if x['direction']=='client']
    assert any(m.get('id')==42 and m.get('method')=='tools/call' for m in client_messages)
    assert any(m.get('id')==45 and m.get('method')=='tools/call' for m in client_messages)
assert any(x['message'].get('method')=='notifications/cancelled' and x['message']['params']['requestId']==42
           for x in R['client_transcripts']['A'] if x['direction']=='client')
assert not any(x['message'].get('method')=='notifications/cancelled'
               for x in R['client_transcripts']['B'] if x['direction']=='client')
print('OK: no adapter in scoped inventory; two toy stdio clients, isolated ID cancellation, stale hash rejection, shared-proof refresh, distinct Lean processes')
