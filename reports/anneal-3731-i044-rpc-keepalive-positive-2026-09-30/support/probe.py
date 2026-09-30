#!/usr/bin/env python3
"""One-shot, guarded positive Lean RPC keep-alive/reference control."""
import hashlib, importlib.util, json, os, re, shutil, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports')
HARNESS=REPORTS/'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
HARNESS_SHA='9d5d5c7e3d85e8679e1ee04f9f8df485d163be3bd0eebaa0ffadaf27f7dc50a7'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LEAN_SHA='b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997'
WORK=HERE/'work';RESULT=HERE/'results.json'
MIN_START=30.;MIN_LIVE=20.;MIN_DISK=10*1024**3;MAX_RSS=1200*1024**2;MAX_SCRATCH=100*1024**2;MAX_TOTAL=65.
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def headroom():
    t=subprocess.check_output(['/usr/bin/vm_stat'],text=True,timeout=5)
    page=int(re.search(r'page size of (\d+) bytes',t).group(1))
    counts={x:int(re.search(rf'Pages {x}:\s+(\d+)\.',t).group(1)) for x in ('free','inactive','speculative')}
    physical=int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True,timeout=5))
    return {'estimated_reclaimable_percent':round(100*page*sum(counts.values())/physical,4),
      'free_disk_bytes':shutil.disk_usage(HERE).free,'physical_bytes':physical,'page_size':page,'pages':counts}
def scratch():return sum(p.stat().st_size for p in WORK.rglob('*') if p.is_file()) if WORK.exists() else 0
def admit():
    h=headroom();return h,('admission_memory' if h['estimated_reclaimable_percent']<=MIN_START else
                         'admission_disk' if h['free_disk_bytes']<=MIN_DISK else None)
def main():
    assert not WORK.exists() and not RESULT.exists(),'one-shot output already exists'
    raw=(HERE/'oracle.json').read_bytes();o=json.loads(raw)
    assert sha(LEAN.read_bytes())==LEAN_SHA==o['lean_sha256']
    assert sha(HARNESS.read_bytes())==HARNESS_SHA
    assert sha((HERE/'baseline-expiry-results.json').read_bytes())==o['baseline_results_sha256']
    source=o['source'];assert sha(source.encode())==o['source_sha256']
    result={'schema':1,'observed_utc':now(),'status':'prepared','stop_reason':None,
      'oracle_prelaunch_sha256':sha(raw),'baseline_results_sha256':o['baseline_results_sha256'],
      'lean_sha256':LEAN_SHA,'harness_sha256':HARNESS_SHA,
      'limits':{'minimum_start_reclaimable_percent':MIN_START,'minimum_live_reclaimable_percent':MIN_LIVE,
       'minimum_disk_bytes':MIN_DISK,'maximum_tree_rss_bytes':MAX_RSS,
       'maximum_scratch_bytes':MAX_SCRATCH,'maximum_total_seconds':MAX_TOTAL},'samples':[],'keepalives':[]}
    h,reason=admit();result['initial_preflight']=h
    if reason:
        result.update(status='admission_denied',stop_reason=reason)
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(result['status']);return
    spec=importlib.util.spec_from_file_location('cached_uri_harness',HARNESS)
    harness=importlib.util.module_from_spec(spec);spec.loader.exec_module(harness)
    WORK.mkdir();path=WORK/'Proof.lean';path.write_bytes(source.encode());uri=path.as_uri()
    server=None;start=time.monotonic()
    def sample():
        host=headroom();tree=harness.prior.tree(server.p.pid) if server else {'rss_bytes':0,'processes':[],'count':0}
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
        server=harness.Server('rpc-keepalive-positive',WORK,'direct')
        server.n=1000
        result['server_pid']=server.p.pid;result['uri']=uri;result['argv']=[str(LEAN),'--server']
        result['environment']={'LEAN_NUM_THREADS':'1','LEAN_PATH':str(WORK/'.lake/build/lib/lean')}
        sample();result['wait']=harness.open_uri(server,uri,source);sample()
        result['connect']=server.request('$/lean/rpc/connect',{'uri':uri},10)
        sid=result['connect']['result']['sessionId'];result['session_id']=sid
        pos={'line':1,'character':8}
        def call():
            return server.request('$/lean/rpc/call',{'textDocument':{'uri':uri},'position':pos,
              'sessionId':sid,'method':o['rpc_method'],'params':result['reference']},10)
        result['rich']=server.request('$/lean/rpc/call',{'textDocument':{'uri':uri},'position':pos,
          'sessionId':sid,'method':'Lean.Widget.getInteractiveGoals',
          'params':{'textDocument':{'uri':uri},'position':pos}},10)
        result['reference']=result['rich']['result']['goals'][0]['hyps'][0]['type']['tag'][0]['info']
        result['before']=call();assert 'result' in result['before']
        result['tree_before_idle']=harness.prior.tree(server.p.pid)
        result['interval_start_event_index']=len(harness.prior.EVENTS)
        interval_start=time.monotonic();result['interval_started_utc']=now()
        for scheduled in o['keepalive_schedule_seconds']:
            while time.monotonic()-interval_start<scheduled:
                sample();time.sleep(.1)
            sample()
            server.send({'jsonrpc':'2.0','method':o['keepalive_notification'],
                         'params':{'uri':uri,'sessionId':sid}})
            result['keepalives'].append({'scheduled_seconds':scheduled,
              'elapsed_seconds':round(time.monotonic()-interval_start,4),'utc':now()})
        while time.monotonic()-interval_start<o['minimum_observation_seconds']:
            sample();time.sleep(.1)
        sample();result['interval_elapsed_seconds']=round(time.monotonic()-interval_start,4)
        result['interval_end_event_index']=len(harness.prior.EVENTS)
        result['tree_after_idle']=harness.prior.tree(server.p.pid)
        result['after']=call();result['status']='completed' if 'result' in result['after'] else 'rpc_error'
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
          'interval_elapsed_seconds':result.get('interval_elapsed_seconds'),
          'keepalives':len(result['keepalives']),'after_error':result.get('after',{}).get('error')}))
if __name__=='__main__':main()
