#!/usr/bin/env python3
"""One-shot, guarded direct Lean stepwise document-version experiment."""
import hashlib, importlib.util, json, os, re, shutil, signal, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports')
HARNESS=REPORTS/'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
WORK=HERE/'work';RESULT=HERE/'results.json'
MIN_START=30.;MIN_LIVE=20.;MIN_DISK=10*1024**3;MAX_RSS=1200*1024**2;MAX_SCRATCH=100*1024**2
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
def scratch():return sum(p.stat().st_size for p in WORK.rglob('*') if p.is_file()) if WORK.exists() else 0
def admit():
    h=headroom()
    reason='admission_memory' if h['estimated_reclaimable_percent']<=MIN_START else (
           'admission_disk' if h['free_disk_bytes']<=MIN_DISK else None)
    return h,reason
def diagnostics_with_marker(events,uri,marker,start=0):
    found=[]
    for i,event in enumerate(events[start:],start):
        m=event.get('message',{})
        if event.get('kind')=='server' and m.get('method')=='textDocument/publishDiagnostics':
            p=m['params']
            if p.get('uri')==uri and any(marker in d.get('message','') for d in p.get('diagnostics',[])):
                found.append({'event_index':i,'params':p})
    return found

def main():
    assert not WORK.exists() and not RESULT.exists(),'one-shot output already exists'
    raw=(HERE/'oracle.json').read_bytes();o=json.loads(raw)
    assert sha(LEAN.read_bytes())==o['lean_sha256']
    assert sha(HARNESS.read_bytes())==o['harness_sha256']
    variants={x['label']:x for x in o['variants']}
    assert len(variants)==6 and all(sha(x['source'].encode())==x['source_sha256'] for x in variants.values())
    assert (HERE/'Proof-v1.lean').read_bytes()==variants['open-v1']['source'].encode()
    result={'schema':1,'observed_utc':now(),'status':'prepared','stop_reason':None,
            'oracle_prelaunch_sha256':sha(raw),'lean_sha256':o['lean_sha256'],
            'harness_sha256':o['harness_sha256'],'samples':[],'runs':[],'batch':[],
            'limits':{'minimum_start_reclaimable_percent':MIN_START,
                      'minimum_live_reclaimable_percent':MIN_LIVE,'minimum_disk_bytes':MIN_DISK,
                      'maximum_tree_rss_bytes':MAX_RSS,'maximum_scratch_bytes':MAX_SCRATCH,
                      'maximum_server_seconds':o['server_max_seconds'],
                      'maximum_batch_seconds':o['batch_timeout_seconds']}}
    h,reason=admit();result['initial_preflight']=h
    if reason:
        result.update(status='admission_denied',stop_reason=reason)
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'reason':reason}));return
    spec=importlib.util.spec_from_file_location('pinned_lsp_harness',HARNESS)
    harness=importlib.util.module_from_spec(spec);spec.loader.exec_module(harness)
    WORK.mkdir()
    def sample(pid,phase,elapsed,max_seconds):
        host=headroom();tree=harness.prior.tree(pid)
        row={'phase':phase,'elapsed_seconds':round(elapsed,4),'host':host,
             'tree':tree,'scratch_bytes':scratch()}
        result['samples'].append(row)
        reason=('memory_guard' if host['estimated_reclaimable_percent']<MIN_LIVE else
                'disk_guard' if host['free_disk_bytes']<MIN_DISK else
                'rss_guard' if tree['rss_bytes']>MAX_RSS else
                'scratch_guard' if row['scratch_bytes']>MAX_SCRATCH else
                'timeout_guard' if elapsed>max_seconds else None)
        if reason:raise RuntimeError(reason)
        return row
    def run_server(label,sequence):
        admission,reason=admit()
        row={'label':label,'admission':admission,'status':'prepared','steps':[]}
        result['runs'].append(row)
        if reason:raise RuntimeError(label+'_'+reason)
        root=WORK/label;root.mkdir()
        source0=variants['open-v1']['source'];path=root/'Proof.lean';path.write_bytes(source0.encode())
        uri=path.as_uri();row['uri']=uri;row['disk_source_sha256_before']=sha(path.read_bytes())
        start=time.monotonic();server=None
        try:
            server=harness.Server(label,root,'direct');server.n=1000
            row['server_pid']=server.p.pid;row['argv']=[str(LEAN),'--server']
            row['environment']={'LEAN_NUM_THREADS':'1','LEAN_PATH':str(root/'.lake/build/lib/lean')}
            sample(server.p.pid,label,time.monotonic()-start,o['server_max_seconds'])
            for j,key in enumerate(sequence):
                v=variants[key];index_start=len(harness.prior.EVENTS)
                if j==0:
                    server.send({'jsonrpc':'2.0','method':'textDocument/didOpen',
                                 'params':{'textDocument':{'uri':uri,'languageId':'lean',
                                                            'version':v['version'],'text':v['source']}}})
                else:
                    server.send({'jsonrpc':'2.0','method':'textDocument/didChange',
                                 'params':{'textDocument':{'uri':uri,'version':v['version']},
                                           'contentChanges':[{'text':v['source']}]}})
                wait=server.request('textDocument/waitForDiagnostics',
                                    {'uri':uri,'version':v['version']},6)
                marker_seen=diagnostics_with_marker(harness.prior.EVENTS,uri,v['marker'],index_start)
                marker_deadline=time.monotonic()+o['diagnostic_marker_wait_seconds']
                while not marker_seen and time.monotonic()<marker_deadline:
                    sample(server.p.pid,label,time.monotonic()-start,o['server_max_seconds'])
                    try:server.read(min(.2,max(.05,marker_deadline-time.monotonic())))
                    except TimeoutError:pass
                    marker_seen=diagnostics_with_marker(harness.prior.EVENTS,uri,v['marker'],index_start)
                sample(server.p.pid,label,time.monotonic()-start,o['server_max_seconds'])
                goal=server.request('$/lean/plainGoal',
                                    {'textDocument':{'uri':uri},'position':o['goal_position']},6)
                sample(server.p.pid,label,time.monotonic()-start,o['server_max_seconds'])
                row['steps'].append({'label':key,'version':v['version'],'source_sha256':v['source_sha256'],
                    'marker':v['marker'],'event_start_index':index_start,
                    'event_end_index':len(harness.prior.EVENTS),
                    'marker_observations':marker_seen,'wait':wait,'goal':goal,
                    'disk_source_sha256':sha(path.read_bytes()),
                    'tree':harness.prior.tree(server.p.pid)})
            quiet_start=len(harness.prior.EVENTS)
            until=time.monotonic()+o['post_final_quiet_seconds']
            while time.monotonic()<until:
                sample(server.p.pid,label,time.monotonic()-start,o['server_max_seconds'])
                try:server.read(min(.2,max(.05,until-time.monotonic())))
                except TimeoutError:pass
            quiet_goal=server.request('$/lean/plainGoal',
                                    {'textDocument':{'uri':uri},'position':o['goal_position']},6)
            row['quiet']={'seconds':o['post_final_quiet_seconds'],
                          'event_start_index':quiet_start,'event_end_index':len(harness.prior.EVENTS),
                          'goal':quiet_goal,'diagnostics':server.diags.get(uri),
                          'tree':harness.prior.tree(server.p.pid)}
            row['disk_source_sha256_after']=sha(path.read_bytes())
            row['status']='completed'
        finally:
            if server:
                row['server_exit_before_cleanup']=server.p.poll()
                server.stop();row['server_exit_after_cleanup']=server.p.returncode
                row['poststop_tree']=harness.prior.tree(server.p.pid)
            row['duration_seconds']=round(time.monotonic()-start,4)
    def run_batch(v):
        admission,reason=admit()
        entry={'label':v['label'],'source_sha256':v['source_sha256'],'admission':admission}
        result['batch'].append(entry)
        if reason:raise RuntimeError('batch_'+reason)
        root=WORK/'batch';root.mkdir(exist_ok=True)
        path=root/(v['label']+'.lean');path.write_bytes(v['source'].encode())
        env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(root/'.lake/build/lib/lean'))
        argv=[str(LEAN),'--json',str(path)]
        entry['argv']=argv;entry['environment']={'LEAN_NUM_THREADS':'1','LEAN_PATH':env['LEAN_PATH']}
        p=subprocess.Popen(argv,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                           start_new_session=True)
        start=time.monotonic()
        try:
            while True:
                sample(p.pid,'batch-'+v['label'],time.monotonic()-start,o['batch_timeout_seconds'])
                try:out,err=p.communicate(timeout=.1);break
                except subprocess.TimeoutExpired:continue
        except Exception:
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=5)
            raise
        entry.update(exit_code=p.returncode,stdout=out.decode(errors='replace'),
                     stderr=err.decode(errors='replace'),
                     duration_seconds=round(time.monotonic()-start,4),
                     input_sha256=sha(path.read_bytes()),
                     poststop_tree=harness.prior.tree(p.pid))
    try:
        run_server('malformed',o['malformed_sequence'])
        run_server('monotonic',o['monotonic_sequence'])
        for v in o['variants']:run_batch(v)
        result['status']='completed'
    except Exception as error:
        result['status']='stopped';result['stop_reason']=repr(error)
    finally:
        result['events']=harness.prior.EVENTS
        result['postrun_host']=headroom()
        shutil.rmtree(WORK)
        result['cleanup']={'work_exists_after':WORK.exists()}
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'stop_reason':result['stop_reason'],
                          'server_runs':[(r['label'],r['status']) for r in result['runs']],
                          'batch_count':len(result['batch'])}))
if __name__=='__main__':main()
