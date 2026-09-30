#!/usr/bin/env python3
"""One-shot direct Lean many-reference keep-alive/release experiment."""
import hashlib, importlib.util, json, os, re, shutil, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports')
HARNESS = REPORTS/'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
WORK = HERE/'work'; RESULT = HERE/'results.json'
MIN_START=30.; MIN_LIVE=20.; MIN_DISK=10*1024**3
MAX_RSS=1200*1024**2; MAX_SCRATCH=100*1024**2; MAX_TOTAL=70.
sha=lambda b:hashlib.sha256(b).hexdigest()
now=lambda:datetime.now(timezone.utc).isoformat()

def headroom():
    t=subprocess.check_output(['/usr/bin/vm_stat'],text=True,timeout=5)
    page=int(re.search(r'page size of (\d+) bytes',t).group(1))
    pages={x:int(re.search(rf'Pages {x}:\s+(\d+)\.',t).group(1)) for x in ('free','inactive','speculative')}
    physical=int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True,timeout=5))
    return {'estimated_reclaimable_percent':round(100*page*sum(pages.values())/physical,4),
            'free_disk_bytes':shutil.disk_usage(HERE).free,'physical_bytes':physical,
            'page_size':page,'pages':pages}

def scratch():
    return sum(p.stat().st_size for p in WORK.rglob('*') if p.is_file()) if WORK.exists() else 0

def refs_from_goal(goal, names):
    refs=[]
    def find(node):
        if isinstance(node,dict):
            info=node.get('info')
            if isinstance(info,dict) and isinstance(info.get('p'),str):return info
            for value in node.values():
                found=find(value)
                if found is not None:return found
        elif isinstance(node,list):
            for value in node:
                found=find(value)
                if found is not None:return found
        return None
    bundles=goal['hyps']
    assert len(bundles)==len(names)
    for bundle,name in zip(bundles,names):
        assert bundle['names']==[name],(name,bundle['names'])
        ref=find(bundle['type'])
        assert ref is not None,(name,bundle['type'])
        refs.append(ref)
    assert len({x['p'] for x in refs})==len(names)
    return refs

def main():
    assert not WORK.exists() and not RESULT.exists(),'one-shot result or work path already exists'
    oracle_raw=(HERE/'oracle.json').read_bytes();o=json.loads(oracle_raw)
    assert sha(LEAN.read_bytes())==o['lean_sha256']
    assert sha(HARNESS.read_bytes())==o['harness_sha256']
    source=o['source'];assert sha(source.encode())==o['source_sha256']
    assert len(o['hypothesis_names'])==32
    assert set(o['retain_indices'])|set(o['release_indices'])==set(range(32))
    assert not set(o['retain_indices'])&set(o['release_indices'])
    result={'schema':1,'observed_utc':now(),'status':'prepared','stop_reason':None,
            'oracle_prelaunch_sha256':sha(oracle_raw),'lean_sha256':o['lean_sha256'],
            'harness_sha256':o['harness_sha256'],
            'limits':{'minimum_start_reclaimable_percent':MIN_START,
                      'minimum_live_reclaimable_percent':MIN_LIVE,
                      'minimum_disk_bytes':MIN_DISK,'maximum_tree_rss_bytes':MAX_RSS,
                      'maximum_scratch_bytes':MAX_SCRATCH,'maximum_total_seconds':MAX_TOTAL},
            'samples':[],'keepalives':[],'pre_dereferences':[],'post_dereferences':[]}
    h=headroom();result['initial_preflight']=h
    reason='admission_memory' if h['estimated_reclaimable_percent']<=MIN_START else (
           'admission_disk' if h['free_disk_bytes']<=MIN_DISK else None)
    if reason:
        result.update(status='admission_denied',stop_reason=reason)
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'reason':reason}));return
    spec=importlib.util.spec_from_file_location('pinned_rpc_harness',HARNESS)
    harness=importlib.util.module_from_spec(spec);spec.loader.exec_module(harness)
    WORK.mkdir();path=WORK/'Proof.lean';path.write_bytes(source.encode());uri=path.as_uri()
    server=None;start=time.monotonic()
    def sample():
        host=headroom();tree=harness.prior.tree(server.p.pid) if server else {'count':0,'rss_bytes':0,'processes':[]}
        row={'elapsed_seconds':round(time.monotonic()-start,4),'host':host,'tree':tree,'scratch_bytes':scratch()}
        result['samples'].append(row)
        reason=('memory_guard' if host['estimated_reclaimable_percent']<MIN_LIVE else
                'disk_guard' if host['free_disk_bytes']<MIN_DISK else
                'rss_guard' if tree['rss_bytes']>MAX_RSS else
                'scratch_guard' if row['scratch_bytes']>MAX_SCRATCH else
                'timeout_guard' if row['elapsed_seconds']>MAX_TOTAL else
                'server_exit' if server and server.p.poll() is not None else None)
        if reason:raise RuntimeError(reason)
        return row
    try:
        server=harness.Server('rpc-many-ref-retention',WORK,'direct');server.n=1000
        result['server_pid']=server.p.pid;result['uri']=uri;result['argv']=[str(LEAN),'--server']
        result['environment']={'LEAN_NUM_THREADS':'1','LEAN_PATH':str(WORK/'.lake/build/lib/lean')}
        sample();result['wait']=harness.open_uri(server,uri,source);sample()
        result['connect']=server.request('$/lean/rpc/connect',{'uri':uri},8)
        sid=result['connect']['result']['sessionId'];result['session_id']=sid
        position=o['proof_position'];doc={'uri':uri}
        result['rich']=server.request('$/lean/rpc/call',{'textDocument':doc,'position':position,
            'sessionId':sid,'method':'Lean.Widget.getInteractiveGoals',
            'params':{'textDocument':doc,'position':position}},8)
        goals=result['rich']['result']['goals'];assert len(goals)==1,len(goals)
        refs=refs_from_goal(goals[0],o['hypothesis_names']);result['references']=refs
        def call(i):
            ref=refs[i]
            response=server.request('$/lean/rpc/call',{'textDocument':doc,'position':position,
                'sessionId':sid,'method':'Lean.Widget.InteractiveDiagnostics.infoToInteractive',
                'params':ref},8)
            sample()
            return {'index':i,'name':o['hypothesis_names'][i],'reference':ref,'response':response}
        for i in range(len(refs)):
            sample();result['pre_dereferences'].append(call(i))
        assert all('result' in x['response'] for x in result['pre_dereferences'])
        result['tree_before_release']=harness.prior.tree(server.p.pid)
        release_refs=[refs[i] for i in o['release_indices']]
        result['release_event_index']=len(harness.prior.EVENTS)
        server.send({'jsonrpc':'2.0','method':'$/lean/rpc/release',
                     'params':{'uri':uri,'sessionId':sid,'refs':release_refs}})
        sample()
        result['interval_start_event_index']=len(harness.prior.EVENTS)
        interval_start=time.monotonic();result['interval_started_utc']=now()
        for scheduled in o['keepalive_schedule_seconds']:
            while time.monotonic()-interval_start<scheduled:
                sample();time.sleep(.1)
            sample()
            server.send({'jsonrpc':'2.0','method':'$/lean/rpc/keepAlive',
                         'params':{'uri':uri,'sessionId':sid}})
            result['keepalives'].append({'scheduled_seconds':scheduled,
                'elapsed_seconds':round(time.monotonic()-interval_start,4),'utc':now()})
        while time.monotonic()-interval_start<o['minimum_observation_seconds']:
            sample();time.sleep(.1)
        sample();result['interval_elapsed_seconds']=round(time.monotonic()-interval_start,4)
        result['interval_end_event_index']=len(harness.prior.EVENTS)
        result['tree_after_interval']=harness.prior.tree(server.p.pid)
        for i in range(len(refs)):
            sample();result['post_dereferences'].append(call(i))
        observed_released=all(x['response'].get('error',{}).get('code')==o['expected_release_error_code']
                              for x in result['post_dereferences'] if x['index'] in o['release_indices'])
        observed_retained=all('result' in x['response']
                              for x in result['post_dereferences'] if x['index'] in o['retain_indices'])
        result['status']='completed' if observed_released and observed_retained else 'observed_mismatch'
        result['outcome']={'released_expected_error':observed_released,'retained_success':observed_retained}
    except Exception as error:
        result['status']='stopped';result['stop_reason']=repr(error)
    finally:
        if server:
            result['server_exit_before_cleanup']=server.p.poll()
            server.stop();result['server_exit_after_cleanup']=server.p.returncode
            result['poststop_tree']=harness.prior.tree(server.p.pid)
        result['events']=harness.prior.EVENTS if 'harness' in locals() else []
        result['postrun_host']=headroom()
        shutil.rmtree(WORK)
        result['cleanup']={'work_exists_after':WORK.exists()}
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'stop_reason':result['stop_reason'],
                          'references':len(result.get('references',[])),
                          'interval_seconds':result.get('interval_elapsed_seconds'),
                          'outcome':result.get('outcome')}))
if __name__=='__main__':main()
