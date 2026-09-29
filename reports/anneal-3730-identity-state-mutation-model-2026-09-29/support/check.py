#!/usr/bin/env python3
"""Validate the retained finite graph, traces, mutation controls, and race results."""
import hashlib,json
from pathlib import Path
from model import State, INITIAL, POLICIES, DEPTH, oracle, run_schedule, successors
H=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((H/'results.json').read_text());space=json.loads((H/'state-space.json').read_text())
assert r['code_sha256']==sha(H/'model.py')
assert r['state_space_sha256']==sha(H/'state-space.json')
assert space['bound']==DEPTH==7
nodes=space['nodes'];edges=space['edges'];graph=r['graph']
assert len(nodes)==graph['reachable_states']==2710
assert len(edges)==graph['checked_edges']==11060
assert [n['id'] for n in nodes]==list(range(len(nodes)))
states=[State(**n['state']) for n in nodes]
assert states[0]==INITIAL
assert len(set(states))==len(states)
assert all(0<=n['depth']<=DEPTH for n in nodes)
assert {str(d):sum(n['depth']==d for n in nodes) for d in range(DEPTH+1)}==graph['depth_histogram']
edge_set={(e['source'],e['action'],e['target']) for e in edges}
assert len(edge_set)==len(edges)
id_by_state={s:i for i,s in enumerate(states)}
for n in nodes:
    s=states[n['id']]
    if n['depth']==DEPTH:continue
    for action,t in successors(s):
        assert (n['id'],action,id_by_state[t]) in edge_set
        assert nodes[id_by_state[t]]['depth']<=n['depth']+1
for label,policy in POLICIES.items():
    actual=sum(policy(s) and not oracle(s) for s in states)
    assert graph['policy_counts'][label]['unsafe_states']==actual
    if label=='full_capture':assert actual==0
    else:
        ce=graph['shortest_counterexamples'][label]
        actions=[x['action'] for x in ce['schedule']]
        played=run_schedule(actions)
        assert played['final']==ce['final']
        assert len(actions)==ce['depth']==1
        assert policy(State(**ce['final'])) and not oracle(State(**ce['final']))
        assert not any(policy(s) and not oracle(s) for s,n in zip(states,nodes) if n['depth']<ce['depth'])
for name,record in r['controls'].items():
    assert run_schedule(record['schedule'])==record,name
assert r['controls']['source_ABA']['final']['source_digest']=='A'
assert r['controls']['source_ABA']['final']['source_revision']==2
assert r['controls']['artifact_XYX']['final']['artifact_digest']=='X'
assert r['controls']['artifact_XYX']['final']['artifact_revision']==2
assert r['controls']['source_ABA_reopen_reset']['final']['version']==1
assert len(r['patch_orders'])==6
assert sum(x['full']['invalid_accept_count'] for x in r['patch_orders'])==0
assert sum(x['uri_version']['invalid_accept_count'] for x in r['patch_orders'])==4
assert len(r['forced_thread_races'])==4
assert sum(x['invalid_accept_count'] for x in r['forced_thread_races'] if x['policy']=='full')==0
assert sum(x['invalid_accept_count'] for x in r['forced_thread_races'] if x['policy']=='uri_version')==2
for x in r['forced_thread_races']:
    captures=[e for e in x['events'] if e['event']=='capture']
    applies=[e for e in x['events'] if e['event']=='apply']
    assert [e['client'] for e in captures]==[0,1]
    assert [e['client'] for e in applies]==[x['first'],1-x['first']]
    assert captures[0]['stamp']==captures[1]['stamp']
print(json.dumps({'status':'bounded graph and race assertions passed',
                  'states':len(nodes),'edges':len(edges),
                  'model_sha256':sha(H/'model.py'),'results_sha256':sha(H/'results.json'),
                  'state_space_sha256':sha(H/'state-space.json')},indent=2))
