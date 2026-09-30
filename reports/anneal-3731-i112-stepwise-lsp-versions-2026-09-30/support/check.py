#!/usr/bin/env python3
"""Offline event/source/resource check for the stepwise Lean version probe."""
import hashlib, json
from pathlib import Path

HERE=Path(__file__).resolve().parent
oracle=json.loads((HERE/'oracle.json').read_text())
result=json.loads((HERE/'results.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
assert result['status']=='completed' and result['stop_reason'] is None
assert result['oracle_prelaunch_sha256']==sha((HERE/'oracle.json').read_bytes())
assert result['lean_sha256']==oracle['lean_sha256']
assert result['harness_sha256']==oracle['harness_sha256']
variants={v['label']:v for v in oracle['variants']}
assert len(variants)==6 and len({v['marker'] for v in variants.values()})==6
assert all(sha(v['source'].encode())==v['source_sha256'] for v in variants.values())
assert (HERE/'Proof-v1.lean').read_bytes()==variants['open-v1']['source'].encode()
assert [variants[k]['version'] for k in oracle['malformed_sequence']]==[1,2,4,4,3,5]
assert [variants[k]['version'] for k in oracle['monotonic_sequence']]==[1,2,3,4,5]

events=result['events'];assert all(e['seq']==i for i,e in enumerate(events))
def messages(a,b,kind=None,method=None,rid=None):
    return [(i,e['message']) for i,e in enumerate(events[a:b],a)
            if (kind is None or e['kind']==kind) and 'message' in e and
               (method is None or e['message'].get('method')==method) and
               (rid is None or e['message'].get('id')==rid)]
def one(a,b,kind,method=None,rid=None):
    out=messages(a,b,kind,method,rid)
    assert len(out)==1,(a,b,kind,method,rid,len(out))
    return out[0]
def marker_publications(a,b,uri,marker):
    return [{'event_index':i,'params':m['params']} for i,m in
            messages(a,b,'server','textDocument/publishDiagnostics')
            if m['params'].get('uri')==uri and
            any(marker in d.get('message','') for d in m['params'].get('diagnostics',[]))]
def goal_text(response):
    assert 'result' in response and 'error' not in response
    goals=response['result']['goals'];assert len(goals)==1
    return goals[0]

assert len(result['runs'])==2
for run,expected_label,sequence in zip(result['runs'],('malformed','monotonic'),
                                       (oracle['malformed_sequence'],oracle['monotonic_sequence'])):
    assert run['label']==expected_label and run['status']=='completed'
    assert run['admission']['estimated_reclaimable_percent']>result['limits']['minimum_start_reclaimable_percent']
    assert run['admission']['free_disk_bytes']>result['limits']['minimum_disk_bytes']
    assert run['duration_seconds']<oracle['server_max_seconds']
    assert run['server_exit_before_cleanup'] is None and run['server_exit_after_cleanup']==0
    assert run['poststop_tree']['count']==0
    assert run['disk_source_sha256_before']==run['disk_source_sha256_after']==variants['open-v1']['source_sha256']
    assert len(run['steps'])==len(sequence)
    uri=run['uri'];last_end=None;pid_sets=[]
    for idx,(step,key) in enumerate(zip(run['steps'],sequence)):
        variant=variants[key];a=step['event_start_index'];b=step['event_end_index']
        assert 0<=a<b<=len(events) and (last_end is None or a==last_end)
        last_end=b
        assert step['label']==key and step['version']==variant['version']
        assert step['source_sha256']==variant['source_sha256']
        assert step['marker']==variant['marker']
        assert step['disk_source_sha256']==variants['open-v1']['source_sha256']
        if idx==0:
            ci,change=one(a,b,'client','textDocument/didOpen')
            assert change['params']['textDocument']=={'uri':uri,'languageId':'lean',
                'version':variant['version'],'text':variant['source']}
        else:
            ci,change=one(a,b,'client','textDocument/didChange')
            assert change['params']=={'textDocument':{'uri':uri,'version':variant['version']},
                                      'contentChanges':[{'text':variant['source']}]}
        wi,wait_req=one(a,b,'client','textDocument/waitForDiagnostics')
        wri,wait_resp=one(a,b,'server',rid=wait_req['id'])
        assert ci<wi<wri and wait_req['params']=={'uri':uri,'version':variant['version']}
        assert wait_resp==step['wait'] and wait_resp.get('result')=={}
        gi,goal_req=one(a,b,'client','$/lean/plainGoal')
        gri,goal_resp=one(a,b,'server',rid=goal_req['id'])
        assert wri<gi<gri
        assert goal_req['params']=={'textDocument':{'uri':uri},
                                   'position':oracle['goal_position']}
        assert goal_resp==step['goal']
        assert goal_text(goal_resp)==f"⊢ {variant['numeral']} = {variant['numeral']}"
        observed=marker_publications(a,gi,uri,variant['marker'])
        assert observed==step['marker_observations'] and observed
        assert all(x['params']['version']==variant['version'] for x in observed)
        assert all(x['event_index']>ci for x in observed)
        tree=step['tree'];assert tree['count']==2
        pids={p['pid'] for p in tree['processes']};assert run['server_pid'] in pids
        pid_sets.append(pids)
        assert not messages(a,b,'client','textDocument/didClose')
    assert all(pids==pid_sets[0] for pids in pid_sets)
    quiet=run['quiet'];a=quiet['event_start_index'];b=quiet['event_end_index']
    assert a==last_end and a<b and quiet['seconds']==oracle['post_final_quiet_seconds']
    gi,goal_req=one(a,b,'client','$/lean/plainGoal')
    gri,goal_resp=one(a,b,'server',rid=goal_req['id'])
    assert gi<gri and goal_resp==quiet['goal']
    final_step=run['steps'][-1]
    final_response_index,_=one(final_step['event_start_index'],final_step['event_end_index'],
                               'server',rid=final_step['goal']['id'])
    assert (events[gi]['ms']-events[final_response_index]['ms'])/1000>=oracle['post_final_quiet_seconds']
    assert not any(m.get('method') in ('textDocument/didOpen','textDocument/didChange','textDocument/didClose')
                   for _,m in messages(final_response_index+1,gi,'client'))
    assert goal_text(goal_resp)=='⊢ 5 = 5'
    assert quiet['tree']['count']==2
    assert {p['pid'] for p in quiet['tree']['processes']}==pid_sets[0]
    assert quiet['diagnostics']['version']==5
    assert any('missing_v5' in d['message'] for d in quiet['diagnostics']['diagnostics'])

assert len(result['batch'])==6
for row,v in zip(result['batch'],oracle['variants']):
    assert row['label']==v['label'] and row['source_sha256']==row['input_sha256']==v['source_sha256']
    assert row['admission']['estimated_reclaimable_percent']>result['limits']['minimum_start_reclaimable_percent']
    assert row['admission']['free_disk_bytes']>result['limits']['minimum_disk_bytes']
    assert row['exit_code']==1 and row['duration_seconds']<oracle['batch_timeout_seconds']
    assert row['poststop_tree']['count']==0 and not row['stderr']
    diagnostic=[json.loads(line) for line in row['stdout'].splitlines() if line.strip()]
    assert any(v['marker'] in str(x.get('data','')) for x in diagnostic)
    assert any(f"⊢ {v['numeral']} = {v['numeral']}" in str(x.get('data','')) for x in diagnostic)

limits=result['limits'];samples=result['samples'];assert samples
assert result['initial_preflight']['estimated_reclaimable_percent']>limits['minimum_start_reclaimable_percent']
assert result['initial_preflight']['free_disk_bytes']>limits['minimum_disk_bytes']
assert all(s['host']['estimated_reclaimable_percent']>=limits['minimum_live_reclaimable_percent'] and
           s['host']['free_disk_bytes']>=limits['minimum_disk_bytes'] and
           s['tree']['rss_bytes']<=limits['maximum_tree_rss_bytes'] and
           s['scratch_bytes']<=limits['maximum_scratch_bytes'] and
           s['elapsed_seconds']<=(limits['maximum_batch_seconds'] if s['phase'].startswith('batch-')
                                  else limits['maximum_server_seconds']) for s in samples)
assert result['cleanup']['work_exists_after'] is False
print(json.dumps({'status':'pass','malformed_goals':[goal_text(s['goal']) for s in result['runs'][0]['steps']],
                  'monotonic_goals':[goal_text(s['goal']) for s in result['runs'][1]['steps']],
                  'batch_count':len(result['batch']),
                  'minimum_reclaimable_percent':min(s['host']['estimated_reclaimable_percent'] for s in samples),
                  'peak_tree_rss_bytes':max(s['tree']['rss_bytes'] for s in samples)}))
