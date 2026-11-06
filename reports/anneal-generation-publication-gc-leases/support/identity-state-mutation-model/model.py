#!/usr/bin/env python3
"""Finite symbolic response identity and two-client patch-CAS mutation suite."""
from collections import deque
from dataclasses import asdict, dataclass, replace
from itertools import permutations
from pathlib import Path
import hashlib, json, platform, threading, time

HERE=Path(__file__).resolve().parent
DEPTH=7

@dataclass(frozen=True)
class State:
    source_revision:int=0
    source_digest:str='A'
    artifact_revision:int=0
    artifact_digest:str='X'
    subject:str='lib'
    path:str='/physical/src/lib.rs'
    uri:str='file:///project/src/lib.rs'
    open_epoch:int=0
    version:int=1
    generation:int=0
    worker:int=0
    rpc:int=0
    cancelled:bool=False

INITIAL=State()
def stamp(s):return (s.source_revision,s.source_digest,s.artifact_revision,s.artifact_digest,
                     s.subject,s.path,s.uri,s.open_epoch,s.version,s.generation,s.worker,s.rpc)
CAPTURE=stamp(INITIAL)

def successors(s):
    """Finite deterministic action order; each dimension changes at most twice."""
    if s.source_digest=='A' and s.source_revision==0:
        yield 'editor-write-B',replace(s,source_revision=1,source_digest='B',version=s.version+1)
        yield 'external-replace-B-unnoticed',replace(s,source_digest='B')
    if s.source_digest=='B' and s.source_revision<2:
        yield 'agent-write-A',replace(s,source_revision=s.source_revision+1,source_digest='A',version=min(3,s.version+1))
    if s.artifact_digest=='X' and s.artifact_revision==0:
        yield 'artifact-replace-Y',replace(s,artifact_revision=1,artifact_digest='Y')
        yield 'artifact-replace-Y-same-revision',replace(s,artifact_digest='Y')
    if s.artifact_digest=='Y' and s.artifact_revision<2:
        yield 'artifact-restore-X',replace(s,artifact_revision=s.artifact_revision+1,artifact_digest='X')
    if s.subject=='lib':yield 'same-path-subject-alias-test',replace(s,subject='test')
    if s.uri==INITIAL.uri:yield 'same-physical-file-uri-alias',replace(s,uri='file:///alias/src/lib.rs')
    if s.open_epoch==0 and (s.source_revision>0 or s.source_digest!=INITIAL.source_digest):
        yield 'close-reopen-version-1',replace(s,open_epoch=1,version=1,worker=s.worker+1)
    if s.generation==0:yield 'new-stage-generation',replace(s,generation=1)
    if s.worker==0:yield 'restart-worker',replace(s,worker=1)
    if s.rpc==0:yield 'reconnect-rpc',replace(s,rpc=1)
    if not s.cancelled:yield 'cancel-captured-request',replace(s,cancelled=True)

def oracle(s):return stamp(s)==CAPTURE and not s.cancelled
POLICIES={
    'full_capture':oracle,
    'uri_version_only':lambda s:(s.uri,s.version)==(INITIAL.uri,INITIAL.version) and not s.cancelled,
    'path_only':lambda s:s.path==INITIAL.path and not s.cancelled,
    'generation_only':lambda s:s.generation==INITIAL.generation and not s.cancelled,
    'cancellation_only':lambda s:not s.cancelled,
}
def explore():
    queue=deque([INITIAL]);depth={INITIAL:0};parent={INITIAL:None};edges=0;attempts=0
    while queue:
        s=queue.popleft();d=depth[s]
        if d==DEPTH:continue
        for name,t in successors(s):
            attempts+=1
            assert t!=s
            edges+=1
            if t not in depth:
                depth[t]=d+1;parent[t]=(s,name);queue.append(t)
    def trace(s):
        a=[]
        while parent[s] is not None:
            before,name=parent[s];a.append(dict(action=name,after=asdict(s)));s=before
        return list(reversed(a))
    bad={};counts={}
    order=sorted(depth,key=lambda s:(depth[s],trace(s)[-1]['action'] if depth[s] else ''))
    preferred={'uri_version_only':'external-replace-B-unnoticed',
               'path_only':'same-path-subject-alias-test',
               'generation_only':'editor-write-B',
               'cancellation_only':'artifact-replace-Y'}
    for label,policy in POLICIES.items():
        violations=[s for s in order if policy(s) and not oracle(s)]
        counts[label]=dict(unsafe_states=len(violations),accepted_states=sum(policy(s) for s in depth),
                           correct_states=sum(policy(s)==oracle(s) for s in depth))
        if violations:
            best_depth=depth[violations[0]]
            tied=[s for s in violations if depth[s]==best_depth]
            s=next((s for s in tied if trace(s)[-1]['action']==preferred.get(label)),tied[0])
            bad[label]=dict(depth=depth[s],schedule=trace(s),final=asdict(s),
                                         captured=CAPTURE,current=stamp(s),policy_accept=True,oracle_accept=False)
    return depth,dict(bound=DEPTH,reachable_states=len(depth),checked_edges=edges,attempted_transitions=attempts,
                      depth_histogram={str(i):sum(x==i for x in depth.values()) for i in range(DEPTH+1)},
                      policy_counts=counts,shortest_counterexamples=bad)

def run_schedule(names):
    s=INITIAL;trace=[]
    for name in names:
        choices=dict(successors(s))
        assert name in choices,(name,s)
        s=choices[name]
        trace.append(dict(action=name,state=asdict(s),oracle_accept=oracle(s),
                          policy_accept={k:p(s) for k,p in POLICIES.items()}))
    return dict(schedule=list(names),steps=trace,final=asdict(s))

@dataclass
class PatchState:
    source:str='A'
    revision:int=0
    uri:str='file:///project/src/lib.rs'
    version:int=1
    open_epoch:int=0
    generation:int=0

def patch_cas(policy,order):
    st=PatchState();captured={};rows=[];proposals={0:'B',1:'C'}
    for action in order:
        op=int(action[-1])
        if action.startswith('begin'):
            captured[op]=asdict(st);rows.append(dict(action=action,captured=captured[op].copy()))
        else:
            cap=captured[op];same_full=(cap==asdict(st))
            if policy=='full':allowed=same_full
            elif policy=='uri_version':allowed=(cap['uri'],cap['version'])==(st.uri,st.version)
            else:raise ValueError(policy)
            before=asdict(st)
            if allowed:
                st.source=proposals[op];st.revision+=1
                # The adapter patch is external to this editor session; its version remains 1.
            rows.append(dict(action=action,before=before,captured=cap.copy(),accepted=allowed,
                             valid_at_apply=same_full,after=asdict(st)))
    return dict(policy=policy,order=list(order),trace=rows,final=asdict(st),
                invalid_accept_count=sum(x.get('accepted',False) and not x.get('valid_at_apply',False) for x in rows))

def all_patch_orders():
    rows=[]
    for order in permutations(('begin0','begin1','apply0','apply1')):
        if any(order.index('begin'+str(i))>order.index('apply'+str(i)) for i in (0,1)):continue
        rows.append({p:patch_cas(p,order) for p in ('full','uri_version')})
    return rows

def forced_thread_race(policy,first):
    """Actual two threads overlap capture, then apply under forced linearization."""
    st=PatchState();lock=threading.Lock();both_captured=threading.Barrier(3)
    capture_release=[threading.Event(),threading.Event()];captured_done=[threading.Event(),threading.Event()]
    release=[threading.Event(),threading.Event()];done=[threading.Event(),threading.Event()]
    log=[];errors=[]
    def worker(i):
        try:
            capture_release[i].wait(timeout=5)
            with lock:
                cap=asdict(st);log.append(dict(event='capture',client=i,stamp=cap.copy()))
            captured_done[i].set()
            both_captured.wait(timeout=5);release[i].wait(timeout=5)
            with lock:
                same_full=cap==asdict(st)
                allowed=same_full if policy=='full' else (cap['uri'],cap['version'])==(st.uri,st.version)
                if allowed:st.source='B' if i==0 else 'C';st.revision+=1
                log.append(dict(event='apply',client=i,accepted=allowed,valid_at_apply=same_full,state=asdict(st)))
            done[i].set()
        except Exception as e:errors.append(repr(e));done[i].set()
    threads=[threading.Thread(target=worker,args=(i,),daemon=True) for i in (0,1)]
    for t in threads:t.start()
    capture_release[0].set();assert captured_done[0].wait(5)
    capture_release[1].set();assert captured_done[1].wait(5)
    both_captured.wait(timeout=5)
    release[first].set();assert done[first].wait(5)
    release[1-first].set();assert done[1-first].wait(5)
    for t in threads:t.join(timeout=5)
    assert not errors,errors
    return dict(policy=policy,first=first,events=log,final=asdict(st),
                invalid_accept_count=sum(x.get('accepted',False) and not x.get('valid_at_apply',False) for x in log))

def main():
    states,graph=explore()
    node_order=sorted(states,key=lambda s:(states[s],stamp(s),s.cancelled))
    ids={s:i for i,s in enumerate(node_order)}
    nodes=[dict(id=i,depth=states[s],state=asdict(s)) for i,s in enumerate(node_order)]
    edges=[dict(source=ids[s],action=name,target=ids[t]) for s in node_order if states[s]<DEPTH for name,t in successors(s)]
    assert len(nodes)==graph['reachable_states'] and len(edges)==graph['checked_edges']
    space=dict(bound=DEPTH,nodes=nodes,edges=edges)
    (HERE/'state-space.json').write_text(json.dumps(space,indent=2)+'\n')
    assert graph['policy_counts']['full_capture']['unsafe_states']==0
    assert set(graph['shortest_counterexamples'])==set(POLICIES)-{'full_capture'}
    assert all(x['depth']==1 for x in graph['shortest_counterexamples'].values())
    schedules={
        'source_ABA':['editor-write-B','agent-write-A'],
        'source_ABA_reopen_reset':['editor-write-B','agent-write-A','close-reopen-version-1'],
        'unnoticed_source_change':['external-replace-B-unnoticed'],
        'artifact_XYX':['artifact-replace-Y','artifact-restore-X'],
        'artifact_same_revision':['artifact-replace-Y-same-revision'],
        'subject_alias_same_path':['same-path-subject-alias-test'],
        'uri_alias_same_physical_path':['same-physical-file-uri-alias'],
        'worker_and_rpc':['restart-worker','reconnect-rpc'],
        'cancellation':['cancel-captured-request'],
        'cross_layer_source_artifact':['editor-write-B','artifact-replace-Y'],
    }
    controls={k:run_schedule(v) for k,v in schedules.items()}
    assert controls['source_ABA']['final']['source_digest']=='A' and controls['source_ABA']['final']['source_revision']==2
    assert controls['artifact_XYX']['final']['artifact_digest']=='X' and controls['artifact_XYX']['final']['artifact_revision']==2
    assert controls['source_ABA_reopen_reset']['final']['version']==1
    assert controls['source_ABA_reopen_reset']['steps'][-1]['policy_accept']['uri_version_only']
    assert not controls['source_ABA_reopen_reset']['steps'][-1]['oracle_accept']
    assert controls['subject_alias_same_path']['steps'][-1]['policy_accept']['path_only']
    assert not controls['subject_alias_same_path']['steps'][-1]['oracle_accept']
    patch=all_patch_orders()
    assert len(patch)==6
    assert sum(x['full']['invalid_accept_count'] for x in patch)==0
    assert sum(x['uri_version']['invalid_accept_count'] for x in patch)==4
    threads=[forced_thread_race(policy,first) for policy in ('full','uri_version') for first in (0,1)]
    assert sum(x['invalid_accept_count'] for x in threads if x['policy']=='full')==0
    assert sum(x['invalid_accept_count'] for x in threads if x['policy']=='uri_version')==2
    result=dict(model='symbolic response freshness and patch authority, not Anneal',platform=platform.platform(),
                python_version=__import__('sys').version,graph=graph,controls=controls,
                patch_orders=patch,forced_thread_races=threads,
                state_space_sha256=hashlib.sha256((HERE/'state-space.json').read_bytes()).hexdigest(),
                code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(reachable_states=graph['reachable_states'],checked_edges=graph['checked_edges'],
                          shortest={k:v['schedule'][0]['action'] for k,v in graph['shortest_counterexamples'].items()},
                          patch_orders=len(patch),thread_races=len(threads)),indent=2))
if __name__=='__main__':main()
