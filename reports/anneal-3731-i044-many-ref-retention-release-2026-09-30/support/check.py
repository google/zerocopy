#!/usr/bin/env python3
"""Offline validation of retained 32-reference RPC release/keep-alive evidence."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
oracle=json.loads((HERE/'oracle.json').read_text())
result=json.loads((HERE/'results.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert result['status']=='completed' and result['stop_reason'] is None
assert result['outcome']=={'released_expected_error':True,'retained_success':True}
assert result['oracle_prelaunch_sha256']==sha(HERE/'oracle.json')
assert result['lean_sha256']==oracle['lean_sha256']
assert result['harness_sha256']==oracle['harness_sha256']
assert hashlib.sha256(oracle['source'].encode()).hexdigest()==oracle['source_sha256']
assert (HERE/'Proof.lean').read_bytes()==oracle['source'].encode()
assert len(oracle['hypothesis_names'])==32 and len(set(oracle['hypothesis_names']))==32
assert oracle['source'].splitlines()[oracle['proof_position']['line']]=='  exact ?_'
assert set(oracle['retain_indices'])|set(oracle['release_indices'])==set(range(32))
assert not set(oracle['retain_indices'])&set(oracle['release_indices'])

events=result['events'];assert all(e['seq']==i for i,e in enumerate(events))
client=[(i,e['message']) for i,e in enumerate(events) if e['kind']=='client']
server=[(i,e['message']) for i,e in enumerate(events) if e['kind']=='server']
def client_id(rid):
    matches=[(i,m) for i,m in client if m.get('id')==rid]
    assert len(matches)==1,(rid,matches)
    return matches[0]
def server_id(rid):
    matches=[(i,m) for i,m in server if m.get('id')==rid and ('result' in m or 'error' in m)]
    assert len(matches)==1,(rid,matches)
    return matches[0]

uri=result['uri'];sid=result['session_id'];pos=oracle['proof_position']
opens=[m for _,m in client if m.get('method')=='textDocument/didOpen']
assert len(opens)==1
assert opens[0]['params']['textDocument']=={
    'uri':uri,'languageId':'lean','version':1,'text':oracle['source']}
assert not any(m.get('method') in ('textDocument/didChange','textDocument/didClose') for _,m in client)
for rid,method,field in ((1000,'textDocument/waitForDiagnostics','wait'),
                         (1001,'$/lean/rpc/connect','connect'),
                         (1002,'$/lean/rpc/call','rich')):
    ci,cm=client_id(rid);si,sm=server_id(rid)
    assert ci<si and cm['method']==method and sm==result[field]
assert result['connect']['result']['sessionId']==sid
assert client_id(1002)[1]['params']=={
    'textDocument':{'uri':uri},'position':pos,'sessionId':sid,
    'method':'Lean.Widget.getInteractiveGoals',
    'params':{'textDocument':{'uri':uri},'position':pos}}

goals=result['rich']['result']['goals'];assert len(goals)==1
bundles=goals[0]['hyps'];assert len(bundles)==32
def first_info(node):
    if isinstance(node,dict):
        if isinstance(node.get('info'),dict) and isinstance(node['info'].get('p'),str):
            return node['info']
        for value in node.values():
            found=first_info(value)
            if found is not None:return found
    if isinstance(node,list):
        for value in node:
            found=first_info(value)
            if found is not None:return found
    return None
refs=[]
for i,(bundle,name) in enumerate(zip(bundles,oracle['hypothesis_names'])):
    assert bundle['names']==[name]
    ref=first_info(bundle['type']);assert ref is not None
    refs.append(ref)
assert refs==result['references'] and len({ref['p'] for ref in refs})==32

def text_leaves(node):
    if isinstance(node,dict):
        return (node.get('text','') if isinstance(node.get('text'),str) else '')+''.join(
            text_leaves(v) for k,v in node.items() if k!='text')
    if isinstance(node,list):return ''.join(text_leaves(v) for v in node)
    return ''
assert len(result['pre_dereferences'])==len(result['post_dereferences'])==32
for phase,rows,start in (('pre',result['pre_dereferences'],1003),
                          ('post',result['post_dereferences'],1035)):
    for i,row in enumerate(rows):
        assert row['index']==i and row['name']==oracle['hypothesis_names'][i] and row['reference']==refs[i]
        rid=start+i;ci,cm=client_id(rid);si,sm=server_id(rid)
        assert ci<si and sm==row['response']
        assert cm['method']=='$/lean/rpc/call'
        assert cm['params']=={'textDocument':{'uri':uri},'position':pos,'sessionId':sid,
                              'method':'Lean.Widget.InteractiveDiagnostics.infoToInteractive',
                              'params':refs[i]}
        if phase=='pre' or i in oracle['retain_indices']:
            assert 'result' in sm and 'error' not in sm
            assert sm['result']['exprExplicit']
        else:
            assert sm.get('error',{}).get('code')==oracle['expected_release_error_code']
            assert f"RPC reference '{refs[i]['p']}' is not valid" in sm['error']['message']
for i in oracle['retain_indices']:
    before=result['pre_dereferences'][i]['response']['result']
    after=result['post_dereferences'][i]['response']['result']
    assert before['doc']==after['doc']
    assert text_leaves(before['exprExplicit'])==text_leaves(after['exprExplicit'])

release_index=result['release_event_index'];lo=result['interval_start_event_index'];hi=result['interval_end_event_index']
assert release_index+1==lo and lo<hi and hi-lo==5
for rid in range(1003,1035):
    assert client_id(rid)[0]<server_id(rid)[0]<release_index
for rid in range(1035,1067):
    assert hi<=client_id(rid)[0]<server_id(rid)[0]
assert (events[hi]['ms']-events[release_index]['ms'])/1000>=oracle['minimum_observation_seconds']
release=events[release_index]
assert release['kind']=='client'
assert release['message']=={'jsonrpc':'2.0','method':'$/lean/rpc/release',
                            'params':{'uri':uri,'sessionId':sid,
                                      'refs':[refs[i] for i in oracle['release_indices']]}}
assert events[hi]['kind']=='client' and events[hi]['message'].get('id')==1035
for event,kept,scheduled in zip(events[lo:hi],result['keepalives'],oracle['keepalive_schedule_seconds']):
    assert event['kind']=='client'
    assert event['message']=={'jsonrpc':'2.0','method':'$/lean/rpc/keepAlive',
                              'params':{'uri':uri,'sessionId':sid}}
    assert kept['scheduled_seconds']==scheduled
    assert scheduled<=kept['elapsed_seconds']<scheduled+1
assert result['interval_elapsed_seconds']>=oracle['minimum_observation_seconds']
assert all(b['elapsed_seconds']-a['elapsed_seconds']<10
           for a,b in zip(result['keepalives'],result['keepalives'][1:]))
assert result['interval_elapsed_seconds']-result['keepalives'][-1]['elapsed_seconds']<10

before=result['tree_before_release'];after=result['tree_after_interval']
assert before['count']==after['count']==2
assert {p['pid'] for p in before['processes']}=={p['pid'] for p in after['processes']}
assert result['server_pid'] in {p['pid'] for p in after['processes']}
assert result['server_exit_before_cleanup'] is None and result['server_exit_after_cleanup']==0
assert result['poststop_tree']['count']==0 and result['cleanup']['work_exists_after'] is False
limit=result['limits'];samples=result['samples'];assert samples
assert result['initial_preflight']['estimated_reclaimable_percent']>limit['minimum_start_reclaimable_percent']
assert result['initial_preflight']['free_disk_bytes']>limit['minimum_disk_bytes']
assert all(s['host']['estimated_reclaimable_percent']>=limit['minimum_live_reclaimable_percent'] and
           s['host']['free_disk_bytes']>=limit['minimum_disk_bytes'] and
           s['tree']['rss_bytes']<=limit['maximum_tree_rss_bytes'] and
           s['scratch_bytes']<=limit['maximum_scratch_bytes'] and
           s['elapsed_seconds']<=limit['maximum_total_seconds'] for s in samples)
print(json.dumps({'status':'pass','refs':32,'released':16,'retained':16,
                  'interval_seconds':result['interval_elapsed_seconds'],
                  'min_reclaimable_percent':min(s['host']['estimated_reclaimable_percent'] for s in samples),
                  'peak_tree_rss_bytes':max(s['tree']['rss_bytes'] for s in samples)}))
