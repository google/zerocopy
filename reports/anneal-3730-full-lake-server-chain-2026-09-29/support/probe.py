#!/usr/bin/env python3
"""Bounded one/two tiny real Charon→Aeneas→Lean→Lake→server chains."""
import concurrent.futures as cf, gzip, hashlib, importlib.util, json, os, re, select, shutil, signal, subprocess, threading, time
from pathlib import Path
HERE=Path(__file__).resolve().parent; WORK=HERE/'work'; RESULTS=HERE/'results.json'; LOGS=HERE/'logs'
REF=HERE.parents[1]/'anneal-3730-combined-pipeline-concurrency-2026-09-29/support/probe.py'
spec=importlib.util.spec_from_file_location('r46',REF); r46=importlib.util.module_from_spec(spec);spec.loader.exec_module(r46)
r46.WORK=WORK;r46.RSS_CAP_KIB=4_500_000;r46.CELL_CAP_S=120;r46.FOOTPRINT_MODE='off'
LAKE=r46.LEANROOT/'bin/lake';LEAN=r46.LEAN;BACKEND=r46.BACKEND
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def save_log(label,stdout,stderr):
    LOGS.mkdir(exist_ok=True)
    for stream,data in [('stdout',stdout),('stderr',stderr)]:
        (LOGS/f'{label}.{stream}.gz').write_bytes(gzip.compress(data.encode(),mtime=0))
    return {'stdout_sha256':hashlib.sha256(stdout.encode()).hexdigest(),
            'stderr_sha256':hashlib.sha256(stderr.encode()).hexdigest()}

def setup_lake(unitroot):
    root=unitroot/'lake';root.mkdir(); gen=unitroot/'generated'
    for name in ('Types.lean','Funs.lean'):
        target=root/'Current'/name;target.parent.mkdir(exist_ok=True);shutil.copyfile(gen/name,target)
    shutil.copyfile(gen/'Current.lean',root/'Current.lean')
    proof=('import Current\n'
      'theorem goal_inc : pipeline_workload.inc 0#u32 = .ok 1#u32 := by\n'
      '  trace_state\n  rfl\n#print axioms goal_inc\n')
    (root/'Proof.lean').write_text(proof)
    (root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire aeneas from "'+str(BACKEND)+'"\n'
       'package r48_probe\nlean_lib Current\n@[default_target]\nlean_lib Proof\n')
    manifest=json.loads((BACKEND/'lake-manifest.json').read_text())
    manifest['packages'].append({'type':'path','scope':'','name':'aeneas','manifestFile':'lake-manifest.json',
         'inherited':False,'dir':str(BACKEND),'configFile':'lakefile.lean'})
    manifest['name']='r48_probe';(root/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    packages=root/'.lake/packages';packages.parent.mkdir(exist_ok=True);packages.symlink_to(BACKEND/'.lake/packages',target_is_directory=True)
    return root

class Client:
    def __init__(self,root,group):
        self.root=root;self.group=group;self.buf=b'';self.id=0;self.messages=[]
        self.p=subprocess.Popen([str(LAKE),'--keep-toolchain','--no-cache','serve'],cwd=root,
          env=dict(os.environ,LEAN_NUM_THREADS='1',LAKE_NO_NET='1'),stdin=subprocess.PIPE,
          stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        group.add(self.p);self.uri=(root/'Proof.lean').as_uri()
        self.request('initialize',{'processId':os.getpid(),'rootUri':root.as_uri(),
          'capabilities':{},'initializationOptions':{'hasWidgets':False}},timeout=20)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush();self.messages.append({'direction':'client','message':msg})
    def receive(self,predicate,timeout=35):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if self.group.abort:raise RuntimeError(self.group.abort)
            while b'\r\n\r\n' in self.buf:
                head,body=self.buf.split(b'\r\n\r\n',1)
                lengths=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if not lengths or len(body)<lengths[0]:break
                raw,self.buf=body[:lengths[0]],body[lengths[0]:];msg=json.loads(raw)
                self.messages.append({'direction':'server','message':msg})
                if 'method' in msg and 'id' in msg:self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if predicate(msg):return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                part=os.read(self.p.stdout.fileno(),65536)
                if not part:raise RuntimeError('lake serve stdout closed')
                self.buf+=part
        raise TimeoutError('lake serve LSP response')
    def request(self,method,params,timeout=35):
        self.id+=1;rid=self.id;self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.receive(lambda m:'method' not in m and m.get('id')==rid,timeout)
    def stop(self):
        if self.p.poll() is None:
            try:
                self.request('shutdown',None,timeout=7);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=7)
            except Exception:
                os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        self.group.remove(self.p)
        return {'pid':self.p.pid,'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace'),
                'group_after':r46.tree([self.p.pid])}

def server_case(root,group,label):
    client=Client(root,group)
    try:
        source=(root/'Proof.lean').read_text()
        client.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{
          'uri':client.uri,'languageId':'lean','version':1,'text':source}}})
        wait=client.request('textDocument/waitForDiagnostics',{'uri':client.uri,'version':1},timeout=40)
        goal=client.request('$/lean/plainGoal',{'textDocument':{'uri':client.uri,'version':1},
          'position':{'line':2,'character':3}},timeout=40)
        return {'wait':wait,'goal':goal,'messages':client.messages,'source_sha256':sha(root/'Proof.lean')}
    finally:
        stop=client.stop();save_log(label+'-server','',stop['stderr']);
        if stop['group_after']['processes']:raise RuntimeError('server child leak')

def workflow(group,unit):
    root,crate,_,i=unit
    base=r46.worker(group,unit)
    lake=setup_lake(root)
    env=dict(os.environ,LEAN_NUM_THREADS='1',LAKE_NO_NET='1')
    build=group.run(f'u{i}:lake-build',[LAKE,'build','-v'],lake,env,timeout=95)
    logs=save_log(f'u{i}-lake',build['stdout'],build['stderr'])
    if build['exit']!=0:raise RuntimeError('Lake build failed: '+build['stderr'][-800:])
    local=[x for x in build['stdout'].splitlines() if re.search(r'\b(?:Built|Replayed) (?:Current|Proof)(?:\.|\b)',x)]
    assert (lake/'.lake/build/lib/lean/Proof.olean').exists()
    live=server_case(lake,group,f'u{i}')
    fresh=group.run(f'u{i}:fresh-batch',[LAKE,'env',str(LEAN),'--json','Proof.lean'],lake,env,timeout=30)
    freshlog=save_log(f'u{i}-batch',fresh['stdout'],fresh['stderr'])
    if fresh['exit']!=0:raise RuntimeError('fresh batch failed: '+fresh['stdout'][-800:])
    return {'unit':i,'direct':base,'lake':{'exit':build['exit'],'seconds':build['seconds'],
           'local_jobs':local,'logs':logs,'proof_olean_sha256':sha(lake/'.lake/build/lib/lean/Proof.olean')},
           'server':live,'fresh':{'exit':fresh['exit'],'seconds':fresh['seconds'],'logs':freshlog,
            'stdout_excerpt':fresh['stdout'][:1500]},
           'source_hashes':{n:sha(lake/n) for n in ('Current.lean','Current/Types.lean','Current/Funs.lean','Proof.lean')}}

def pressure():return r46.pressure()
def run_cell(label,n,parallel):
    cellroot=WORK/label;cellroot.mkdir();units=r46.setup(cellroot,n)
    group=r46.Group(label);stop=threading.Event();monitor=threading.Thread(target=group.monitor,args=(stop,),daemon=True);monitor.start()
    outputs=[];errors=[]
    try:
        if parallel:
            with cf.ThreadPoolExecutor(max_workers=n) as pool:
                for fut in [pool.submit(workflow,group,u) for u in units]:
                    try:outputs.append(fut.result())
                    except Exception as e:errors.append(repr(e))
        else:
            for u in units:
                try:outputs.append(workflow(group,u))
                except Exception as e:errors.append(repr(e));break
    finally:
        stop.set();monitor.join(timeout=8)
        for root,_,_,_ in units:shutil.rmtree(root/'target',ignore_errors=True)
    return {'label':label,'workers':n,'parallel':parallel,'wall_seconds':round(time.monotonic()-group.start,3),
       'sampled_peak_rss_kib':group.peak['rss_kib'],'sampled_peak_processes':group.max_count,
       'sample_count':group.samples,'min_free_percent':group.min_free,'abort':group.abort,'errors':errors,
       'units':sorted(outputs,key=lambda x:x['unit']),'cleanup_tree':r46.tree(group.all_roots)}

def main():
    if WORK.exists() or LOGS.exists():raise RuntimeError('work/logs exist; replay only in fresh copy')
    disk=shutil.disk_usage(HERE).free;mem=pressure();ram=int(subprocess.check_output(['sysctl','-n','hw.memsize']))
    if disk<10*1024**3 or mem is None or mem<40:raise RuntimeError(f'preflight disk={disk} mem={mem}')
    tools={n:{'path':str(p),'sha256':sha(p)} for n,p in {
      'cargo':r46.CARGO,'charon':r46.CHARON,'aeneas':r46.AENEAS,'lean':LEAN,'lake':LAKE,
      'aeneas_olean':BACKEND/'.lake/build/lib/lean/Aeneas.olean'}.items()}
    result={'preflight':{'disk_free_bytes':disk,'memory_free_percent':mem,'ram_bytes':ram},
      'caps':{'sampled_rss_kib':r46.RSS_CAP_KIB,'duration_s':r46.CELL_CAP_S,'workers_max':2},
      'tools':tools,'cells':[]};WORK.mkdir()
    one=run_cell('one',1,False);result['cells'].append(one);RESULTS.write_text(json.dumps(result,indent=2)+'\n')
    # Projection is deliberately conservative: a two-worker cell is denied if the
    # first complete chain already consumes >1.5 GiB sampled RSS or headroom falls.
    cur=pressure();projected=2*one['sampled_peak_rss_kib']
    allowed=(not one['abort'] and not one['errors'] and len(one['units'])==1 and cur is not None and cur>=45
      and one['sampled_peak_rss_kib']<1_500_000 and projected<3_000_000 and shutil.disk_usage(HERE).free>15*1024**3)
    if allowed:result['cells'].append(run_cell('two-parallel',2,True))
    else:result['cells'].append({'label':'two-parallel','admission':{'allowed':False,
      'reason':'requires complete one-worker run, >=45% free, one-worker sampled peak <1.5 GiB, projected two-worker peak <3.0 GiB, >15 GiB disk',
      'current_free_percent':cur,'one_peak_rss_kib':one['sampled_peak_rss_kib'],'projected_two_rss_kib':projected}})
    RESULTS.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'cells':[(c['label'],len(c.get('units',[])),c.get('sampled_peak_rss_kib'),c.get('errors'),c.get('abort')) for c in result['cells']],
      'two_admission':result['cells'][1].get('admission')},indent=2))
if __name__=='__main__':main()
