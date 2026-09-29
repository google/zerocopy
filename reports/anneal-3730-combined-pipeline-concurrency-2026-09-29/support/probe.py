#!/usr/bin/env python3
"""Tiny pinned four-stage workflow concurrency, standard library only."""
import argparse
import concurrent.futures as cf
from contextlib import nullcontext
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import threading
import time

HERE = Path(__file__).resolve().parent
WORK = HERE / 'work'
T = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST = T / 'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON, AENEAS, CARGO = T/'bin/charon', T/'bin/aeneas', RUST/'cargo'
LEANROOT = T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN = LEANROOT/'bin/lean'
BACKEND = T/'aeneas-release/backends/lean'
PACKAGES = ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
RSS_CAP_KIB = 4_000_000
PROCESS_CAP = 40
CELL_CAP_S = 90
SOURCE = '''#![allow(dead_code)]
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
'''
RESULT = {'tools':{}, 'preflight':{}, 'cells':[], 'guards':{'rss_cap_kib':RSS_CAP_KIB,'process_cap':PROCESS_CAP,'cell_cap_s':CELL_CAP_S}}
FOOTPRINT_MODE = 'on'
OUTPUT = HERE/'results.json'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,s): p.parent.mkdir(parents=True,exist_ok=True); p.write_text(s)
def pressure():
    p=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',p.stdout)
    return int(m.group(1)) if m else None
def ps_rows():
    p=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],capture_output=True,text=True,timeout=5)
    out={}
    for line in p.stdout.splitlines():
        a=line.strip().split(None,4)
        if len(a)==5:
            try: out[int(a[0])]={'pid':int(a[0]),'ppid':int(a[1]),'pgid':int(a[2]),'rss_kib':int(a[3]),'comm':a[4]}
            except ValueError: pass
    return out
def tree(roots):
    rows=ps_rows(); ids=set(roots)
    while True:
        more={pid for pid,x in rows.items() if x['ppid'] in ids or x['pgid'] in roots}
        if more<=ids: break
        ids|=more
    selected=[rows[p] for p in sorted(ids) if p in rows]
    return {'count':len(selected),'rss_kib':sum(x['rss_kib'] for x in selected),'processes':selected}
def footprint(pid):
    try:
        p=subprocess.run(['footprint','--pid',str(pid),'--noCategories','--format','bytes'],capture_output=True,text=True,timeout=4)
        m=re.search(r'phys_footprint:\s*(\d+) B',p.stdout)
        return {'pid':pid,'exit':p.returncode,'bytes':int(m.group(1)) if m else None,'stderr':p.stderr[:200]}
    except Exception as e: return {'pid':pid,'error':str(e)}

class Group:
    def __init__(self,label,lean_limit=None):
        self.label=label;self.lock=threading.Lock();self.active={};self.all_roots=[];self.abort=None;self.samples=0
        self.lean_gate=threading.Semaphore(lean_limit) if lean_limit else nullcontext()
        self.peak={'count':0,'rss_kib':0,'processes':[]};self.max_count=0;self.footprints=[]
        self.group_footprints=[]
        self.start=time.monotonic();self.min_free=100
    def add(self,p):
        with self.lock:self.active[p.pid]=p;self.all_roots.append(p.pid)
    def remove(self,p):
        with self.lock:self.active.pop(p.pid,None)
    def monitor(self,stop):
        last_fp=0
        while not stop.is_set():
            with self.lock: roots=list(self.active)
            t=tree(roots);self.samples+=1
            if t['rss_kib']>self.peak['rss_kib']:self.peak=t
            self.max_count=max(self.max_count,t['count'])
            if t['rss_kib']>RSS_CAP_KIB:self.abort='sampled group RSS cap'
            if t['count']>PROCESS_CAP:self.abort='process cap'
            if time.monotonic()-self.start>CELL_CAP_S:self.abort='duration cap'
            if self.samples%10==0:
                q=pressure()
                if q is not None:
                    self.min_free=min(self.min_free,q)
                    if q<25:self.abort='memory pressure floor'
            if FOOTPRINT_MODE == 'on' and roots and time.monotonic()-last_fp>1.5:
                # Intrusive sequential per-PID readings: a sampled group sum,
                # never an instantaneous or true peak physical footprint.
                fs=[footprint(x['pid']) for x in t['processes']]
                self.footprints.extend(fs)
                good=[x['bytes'] for x in fs if x.get('bytes') is not None]
                self.group_footprints.append({'rss_kib_at_snapshot':t['rss_kib'],
                    'pids':[x['pid'] for x in t['processes']],
                    'measurements':fs,'complete':len(good)==len(fs),
                    'sum_phys_footprint_bytes':sum(good) if good else None})
                last_fp=time.monotonic()
            if self.abort:
                with self.lock:procs=list(self.active.values())
                for p in procs:
                    if p.poll() is None:
                        try:os.killpg(p.pid,signal.SIGKILL)
                        except ProcessLookupError:pass
                break
            stop.wait(.04)
    def run(self,label,argv,cwd,env,timeout=40):
        if self.abort: raise RuntimeError(self.abort)
        start=time.monotonic();p=subprocess.Popen(list(map(str,argv)),cwd=cwd,env=env,
              stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        self.add(p)
        try:
            stdout,stderr=p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            self.abort='phase timeout'
            os.killpg(p.pid,signal.SIGKILL);stdout,stderr=p.communicate()
        finally:self.remove(p)
        return {'label':label,'argv':list(map(str,argv)),'cwd':str(cwd),'exit':p.returncode,
            'seconds':round(time.monotonic()-start,3),'stdout':stdout.decode(errors='replace'),
            'stderr':stderr.decode(errors='replace')}

def rust_env(target):
    e=dict(os.environ);e.update(RUSTUP_HOME=str(T/'rustup'),CARGO_HOME=str(T/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',
      RAYON_NUM_THREADS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(target),
      PATH=os.pathsep.join([str(RUST),str(T/'bin'),e.get('PATH','')]))
    return e
def lean_env(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ,LEAN_NUM_THREADS='1');e['LEAN_PATH']=os.pathsep.join(map(str,[comp,*(p for p in libs if p.is_dir())]));return e
def setup(cell,n):
    units=[]
    for i in range(n):
        root=cell/f'u{i}';crate=root/'crate';crate.mkdir(parents=True)
        put(crate/'Cargo.toml','[package]\nname = "pipeline_workload"\nversion = "0.1.0"\nedition = "2021"\n')
        put(crate/'src/lib.rs',SOURCE)
        e=rust_env(root/'target')
        p=subprocess.run([str(CARGO),'generate-lockfile','--offline'],cwd=crate,env=e,capture_output=True,text=True,timeout=15)
        assert p.returncode==0,(p.stdout,p.stderr)
        units.append((root,crate,e,i))
    return units
def worker(group,unit):
    root,crate,rustenv,i=unit;llbc=root/'current.llbc';gen=root/'generated';gen.mkdir()
    commands=[]
    def call(label,argv,cwd,env):
        r=group.run(f'u{i}:{label}',argv,cwd,env);commands.append(r)
        if r['exit']!=0:raise RuntimeError(f'{label} failed: {r["stderr"][-500:]}')
    start=time.monotonic()
    call('charon',[CHARON,'cargo','--preset','aeneas','--dest-file',llbc,'--',
      '--manifest-path',crate/'Cargo.toml','--lib','--offline','--locked','-j','1'],root,rustenv)
    call('aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential','-split-files',
      '-gen-lib-entry','-dest',gen,llbc],root,dict(os.environ))
    comp=root/'consumer';(comp/'Current').mkdir(parents=True)
    for name in ['Types.lean','Funs.lean']:shutil.copyfile(gen/name,comp/'Current'/name)
    shutil.copyfile(gen/'Current.lean',comp/'Current.lean')
    le=lean_env(comp)
    with group.lean_gate:
        for module in ['Current/Types','Current/Funs','Current']:
            call('lean:'+module,[LEAN,'-o',module+'.olean',module+'.lean'],comp,le)
        proof='import Current\n' + ''.join(
          f'theorem obl_{fn} : pipeline_workload.{fn} 0#u32 = .ok {v}#u32 := by rfl\n#print axioms obl_{fn}\n'
          for fn,v in [('inc',1),('twice',2),('choose',3)])
        put(comp/'Proof.lean',proof)
        call('lean:proof',[LEAN,'Proof.lean'],comp,le)
    out=commands[-1]['stdout']
    assert out.count('does not depend on any axioms')==0  # Aeneas carries known imported axioms.
    assert out.count("'obl_")==3 and 'sorryAx' not in out
    return {'unit':i,'seconds':round(time.monotonic()-start,3),'commands':commands,
      'hashes':{'rust':sha(crate/'src/lib.rs'),'llbc':sha(llbc),
        'types':sha(gen/'Types.lean'),'funs':sha(gen/'Funs.lean'),'entry':sha(gen/'Current.lean'),
        'proof':sha(comp/'Proof.lean'),'funs_olean':sha(comp/'Current/Funs.olean')},
      'axiom_stdout':out}
def cell(label,n,parallel,lean_limit=None):
    c=WORK/label;c.mkdir();units=setup(c,n);g=Group(label,lean_limit);stop=threading.Event()
    monitor=threading.Thread(target=g.monitor,args=(stop,),daemon=True);monitor.start()
    outputs=[];errors=[]
    try:
        if parallel:
            with cf.ThreadPoolExecutor(max_workers=n) as pool:
                futs=[pool.submit(worker,g,u) for u in units]
                for f in futs:
                    try:outputs.append(f.result())
                    except Exception as e:errors.append(str(e))
        else:
            for u in units:
                try:outputs.append(worker(g,u))
                except Exception as e:errors.append(str(e));break
    finally:stop.set();monitor.join(timeout=8)
    cleanup=tree(g.all_roots)
    row={'label':label,'workers':n,'parallel':parallel,'seconds':round(time.monotonic()-g.start,3),
      'sampled_peak_rss_kib':g.peak['rss_kib'],'sampled_peak_processes':g.max_count,
      'peak_tree':g.peak,'footprint_samples':g.footprints,'group_footprint_samples':g.group_footprints,
      'samples':g.samples,
      'min_free_percent':g.min_free,'abort':g.abort,'errors':errors,'lean_limit':lean_limit,
      'units':sorted(outputs,key=lambda x:x['unit']),
      'cleanup_tree':cleanup}
    for root,_,_,_ in units:
        shutil.rmtree(root/'target',ignore_errors=True)
    return row
def main():
    global FOOTPRINT_MODE, OUTPUT
    ap=argparse.ArgumentParser();ap.add_argument('--footprint',choices=['on','off'],default='on')
    ap.add_argument('--output',default='results.json');args=ap.parse_args()
    FOOTPRINT_MODE=args.footprint;OUTPUT=HERE/args.output
    RESULT['footprint_mode']=FOOTPRINT_MODE
    if WORK.exists():raise SystemExit('support/work must be absent; remove it only after preserving prior results')
    free=shutil.disk_usage(HERE).free;mem=pressure()
    RESULT['preflight']={'disk_free_bytes':free,'memory_free_percent':mem,'ram_bytes':int(subprocess.check_output(['sysctl','-n','hw.memsize']))}
    assert free>10*1024**3 and mem is not None and mem>=35
    for name,p in {'charon':CHARON,'aeneas':AENEAS,'cargo':CARGO,'lean':LEAN,
                   'aeneas_olean':BACKEND/'.lake/build/lib/lean/Aeneas.olean'}.items():
        assert p.is_file(),p;RESULT['tools'][name]={'path':str(p),'sha256':sha(p)}
    WORK.mkdir()
    for label,n,parallel,lean_limit in [('serial-2',2,False,None),('parallel-2',2,True,None),('parallel-2-lean1',2,True,1)]:
        q=pressure();allowed=q is not None and q>=35 and shutil.disk_usage(HERE).free>10*1024**3
        RESULT['cells'].append({'label':label,'admission':{'free_percent':q,'allowed':allowed}})
        if not allowed:break
        RESULT['cells'][-1].update(cell(label,n,parallel,lean_limit))
        OUTPUT.write_text(json.dumps(RESULT,indent=2)+'\n')
        if label!='parallel-2' and (RESULT['cells'][-1]['abort'] or RESULT['cells'][-1]['errors']):break
    two=next((x for x in RESULT['cells'] if x['label']=='parallel-2-lean1' and 'units' in x),None)
    q=pressure();four_ok=two is not None and not two['abort'] and len(two['units'])==2 and q is not None and q>=45 and two['sampled_peak_rss_kib']<1_000_000 and shutil.disk_usage(HERE).free>15*1024**3
    if four_ok:RESULT['cells'].append({'label':'parallel-4','admission':{'free_percent':q,'allowed':True},**cell('parallel-4',4,True)})
    else:RESULT['cells'].append({'label':'parallel-4','admission':{'free_percent':q,'allowed':False,'reason':'requires >=45% free, 2-worker sampled peak <1,000,000 KiB, and >15 GiB disk'}})
    # Selected generated output bytes must match across the same source workers.
    done=[x for x in RESULT['cells'] if 'units' in x and not x['abort'] and not x['errors']]
    for x in done:
        assert len(x['units'])==x['workers'],x
        assert x['sampled_peak_rss_kib']<=RSS_CAP_KIB and not x['cleanup_tree']['processes']
    base=done[0]['units'][0]['hashes']
    RESULT['output_comparison']={key:len({u['hashes'][key] for x in done for u in x['units']})==1 for key in ['rust','types','funs','entry','funs_olean']}
    assert all(RESULT['output_comparison'].values())
    OUTPUT.write_text(json.dumps(RESULT,indent=2)+'\n')
    print(json.dumps({'cells':[(x['label'],len(x.get('units',[])),x.get('sampled_peak_rss_kib')) for x in RESULT['cells']], 'output_comparison':RESULT['output_comparison']}))
if __name__=='__main__':main()
