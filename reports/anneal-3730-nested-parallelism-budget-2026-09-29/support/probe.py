#!/usr/bin/env python3
"""R37 tiny nested Cargo/Charon and direct Lean server budget ramp."""
import hashlib,json,os,re,select,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CARGO=RUSTBIN/'cargo';LEAN=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
OUTERS=(1,2,4);INNERS=(1,2)
RSS_CAP_KIB=4_000_000;PROCESS_CAP=32;CELL_SECONDS=40;FREE_FLOOR_PERCENT=25
RECORDS=[];T0=time.monotonic()
def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def event(event_type,**kw):RECORDS.append({'seq':len(RECORDS),'ms':round((time.monotonic()-T0)*1000,2),'event_type':event_type,**kw})
def command(argv,**kwargs):return subprocess.run(list(map(str,argv)),capture_output=True,text=True,timeout=kwargs.pop('timeout',10),**kwargs)
def pressure():
    p=command(['memory_pressure','-Q']);m=re.search(r'System-wide memory free percentage: (\d+)%',p.stdout)
    return {'free_percent':int(m.group(1)) if m else None,'raw':p.stdout,'rc':p.returncode}
def rustenv(inner):
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS=str(inner),CARGO_INCREMENTAL='0',
      RAYON_NUM_THREADS=str(inner),
      PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def rows_ps():
    p=command(['ps','-axo','pid=,ppid=,pgid=,%cpu=,rss=,comm='],timeout=4)
    rows={}
    for line in p.stdout.splitlines():
        x=line.strip().split(None,5)
        if len(x)!=6:continue
        try:pid,ppid,pgid=int(x[0]),int(x[1]),int(x[2]);cpu=float(x[3]);rss=int(x[4])
        except ValueError:continue
        rows[pid]={'pid':pid,'ppid':ppid,'pgid':pgid,'cpu_percent':cpu,'rss_kib':rss,'comm':x[5]}
    return rows
def tree(roots):
    allrows=rows_ps();seen=set(roots)
    while True:
        more={pid for pid,row in allrows.items() if row['ppid'] in seen}
        if more<=seen:break
        seen|=more
    found=[allrows[pid] for pid in sorted(seen) if pid in allrows]
    return {'count':len(found),'rss_kib':sum(x['rss_kib'] for x in found),
      'cpu_percent_sum':round(sum(x['cpu_percent'] for x in found),2),'processes':found}
def threads(pid):
    try:
        p=command(['ps','-p',str(pid),'-M'],timeout=3)
        return max(0,len(p.stdout.splitlines())-1) if p.returncode==0 else None
    except Exception:return None
def footprint(pid):
    try:
        p=command(['footprint','--pid',str(pid),'--noCategories','--format','bytes'],timeout=5)
        m=re.search(r'phys_footprint:\s*(\d+) B',p.stdout)
        return {'pid':pid,'rc':p.returncode,'phys_footprint_bytes':int(m.group(1)) if m else None,
          'stdout':p.stdout[:2500],'stderr':p.stderr[:300]}
    except Exception as ex:return {'pid':pid,'error':repr(ex)}
def resource_sample(snapshot):
    return {'thread_counts':{str(x['pid']):threads(x['pid']) for x in snapshot['processes']},
      'footprints':[footprint(x['pid']) for x in snapshot['processes']]}
def admission(outer,kind):
    p=pressure();free=shutil.disk_usage(HERE).free
    allowed=p['free_percent'] is not None and p['free_percent']>=FREE_FLOOR_PERCENT and free>5*1024**3
    row={'outer':outer,'kind':kind,'pressure':p,'disk_free_bytes':free,'allowed':allowed,
      'reason':None if allowed else 'free memory below 25%, unknown, or disk below 5 GiB'}
    event('admission',**row);return row
def cargo_unit(cell,i):
    base=cell/f'u{i}';root=base/'root'
    for dep in ('dep_a','dep_b'):
        write(base/dep/'Cargo.toml',f'[package]\nname="{dep}"\nversion="0.1.0"\nedition="2021"\n')
        write(base/dep/'src/lib.rs',f'pub fn {dep}(x:u32)->u32{{x.wrapping_add(1)}}\n')
    write(root/'Cargo.toml',f'[package]\nname="r37u{i}"\nversion="0.1.0"\nedition="2021"\n'
      '[dependencies]\ndep_a={path="../dep_a"}\ndep_b={path="../dep_b"}\n')
    write(root/'src/lib.rs','pub fn combined(x:u32)->u32{dep_a::dep_a(x).wrapping_add(dep_b::dep_b(x))}\n')
    write(root/'build.rs','fn main(){println!("cargo:rerun-if-changed=src/lib.rs");'
      'std::thread::sleep(std::time::Duration::from_millis(150));}\n')
    p=command([CARGO,'generate-lockfile','--manifest-path',root/'Cargo.toml','--offline'],
      cwd=root,env=rustenv(1),timeout=15)
    assert p.returncode==0,(p.stdout,p.stderr)
    return root
def cargo_argv(root,dest,inner):
    return [CHARON,'cargo','--preset','aeneas','--dest-file',dest,'--',
      '--manifest-path',root/'Cargo.toml','--lib','--offline','--locked','-j',str(inner)]
def cargo_group(label,roots,inner,dests):
    procs=[];start=time.monotonic();logs=[]
    for i,(root,dest) in enumerate(zip(roots,dests)):
        out=root/f'{label}.stdout';err=root/f'{label}.stderr';fo=open(out,'wb');fe=open(err,'wb')
        p=subprocess.Popen(list(map(str,cargo_argv(root,dest,inner))),cwd=root,env=rustenv(inner),
          stdout=fo,stderr=fe,start_new_session=True)
        procs.append(p);logs.append((fo,fe,out,err))
    peak={'count':0,'rss_kib':0,'cpu_percent_sum':0,'processes':[]};max_count=0;max_cpu=0.0
    samples=0;resource=None;aborted=None;floor=None
    while any(p.poll() is None for p in procs):
        t=tree([p.pid for p in procs]);samples+=1
        if t['rss_kib']>peak['rss_kib']:peak=t
        max_count=max(max_count,t['count']);max_cpu=max(max_cpu,t['cpu_percent_sum'])
        if resource is None and t['count']>=len(procs)+1 and time.monotonic()-start>.08:
            resource=resource_sample(t)
        if samples%5==0:
            q=pressure()['free_percent'];floor=q if floor is None else min(floor,q) if q is not None else floor
            if q is not None and q<FREE_FLOOR_PERCENT:aborted='memory pressure guard'
        if t['rss_kib']>RSS_CAP_KIB:aborted='RSS cap'
        if t['count']>PROCESS_CAP:aborted='process cap'
        if time.monotonic()-start>CELL_SECONDS:aborted='duration cap'
        if aborted:
            for p in procs:
                if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
            break
        time.sleep(.025)
    results=[]
    for p,(fo,fe,out,err),dest in zip(procs,logs,dests):
        p.wait(timeout=5);fo.close();fe.close()
        results.append({'pid':p.pid,'rc':p.returncode,'stdout':out.read_text(errors='replace'),
          'stderr':err.read_text(errors='replace'),'dest':str(dest),'llbc_exists':dest.is_file(),
          'llbc_sha256':sha(dest) if dest.is_file() else None,
          'llbc_mtime_ns':dest.stat().st_mtime_ns if dest.is_file() else None})
    result={'label':label,'outer':len(roots),'inner':inner,'elapsed_ms':round((time.monotonic()-start)*1000,2),
      'peak_rss_tree':peak,'max_process_count':max_count,'max_cpu_percent_sum':max_cpu,
      'resource_sample':resource,'samples':samples,'min_free_percent':floor,'aborted':aborted,
      'results':results,'cleanup_tree':tree([p.pid for p in procs])}
    event('cargo_group',**result);return result
def cargo_cell(outer,inner):
    cell=WORK/f'cargo-o{outer}-i{inner}';roots=[cargo_unit(cell,i) for i in range(outer)]
    dests=[(root/'probe.llbc') for root in roots]
    cold=cargo_group('cold',roots,inner,dests)
    assert not cold['aborted'] and all(x['rc']==0 and x['llbc_exists'] for x in cold['results']),cold
    warm=cargo_group('warm-noop',roots,inner,dests)
    assert not warm['aborted'] and all(x['rc']==0 for x in warm['results']),warm
    for root in roots:
        with open(root/'src/lib.rs','a') as f:f.write('// warm incremental source comment\n')
    incremental=cargo_group('warm-incremental',roots,inner,dests)
    assert not incremental['aborted'] and all(x['rc']==0 and x['llbc_exists'] for x in incremental['results']),incremental
    return {'outer':outer,'inner':inner,'root_paths':list(map(str,roots)),
      'cold':cold,'warm_noop':warm,'warm_incremental':incremental,
      'noop_unchanged_output':[a['llbc_mtime_ns']==b['llbc_mtime_ns'] for a,b in zip(cold['results'],warm['results'])],
      'incremental_changed_output':[a['llbc_mtime_ns']!=b['llbc_mtime_ns'] for a,b in zip(warm['results'],incremental['results'])]}
class LeanServer:
    def __init__(self,label,root,inner):
        self.label=label;self.root=root;self.buf=b'';self.n=10;self.sent={}
        e=dict(os.environ,LEAN_NUM_THREADS=str(inner))
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=e,
          stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),
          rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
        if 'id' in msg and 'method' in msg:self.sent[msg['id']]=time.monotonic()
    def read(self,timeout=20):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                head,body=self.buf.split(b'\r\n\r\n',1)
                sizes=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if sizes and len(body)>=sizes[0]:
                    raw,self.buf=body[:sizes[0]],body[sizes[0]:]
                    msg=json.loads(raw)
                    if 'method' in msg and 'id' in msg:self.send(dict(jsonrpc='2.0',id=msg['id'],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                data=os.read(self.p.stdout.fileno(),65536)
                if not data:break
                self.buf+=data
        raise TimeoutError(f'{self.label} read')
    def until(self,rid,timeout=20):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            msg=self.read(max(.1,end-time.monotonic()))
            if msg.get('id')==rid and 'method' not in msg:
                return {'response':msg,'latency_ms':round((time.monotonic()-self.sent[rid])*1000,2)}
        raise TimeoutError(f'{self.label} id {rid}')
    def request(self,method,params):
        rid=self.n;self.n+=1;self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return rid
    def stop(self):
        try:
            rid=self.request('shutdown',None);self.until(rid,5)
            self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
        except Exception:
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        return {'pid':self.p.pid,'rc':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}
LEAN_TEXT='theorem demo (n : Nat) : n = n := by\n  exact ?_\n'
def lean_cell(outer,inner):
    cell=WORK/f'lean-o{outer}-i{inner}';cell.mkdir();servers=[]
    for i in range(outer):
        root=cell/f'u{i}';root.mkdir();write(root/'Proof.lean',LEAN_TEXT)
        servers.append(LeanServer(f'u{i}',root,inner))
    roots=[s.p.pid for s in servers];starts=[];cold=[];warm=[];stops=[]
    try:
        for s in servers:
            init=s.until(1);s.send(dict(jsonrpc='2.0',method='initialized',params={}));starts.append(init)
        for s in servers:
            file=s.root/'Proof.lean';uri=file.as_uri()
            s.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={
              'textDocument':dict(uri=uri,languageId='lean',version=1,text=LEAN_TEXT)}))
            s.request('textDocument/waitForDiagnostics',dict(uri=uri,version=1))
        waits=[s.until(10) for s in servers]
        for s in servers:s.request('$/lean/plainGoal',dict(textDocument=dict(uri=(s.root/'Proof.lean').as_uri()),
          position=dict(line=1,character=8)))
        goals=[s.until(11) for s in servers]
        for w,g in zip(waits,goals):
            assert 'n = n' in json.dumps(g['response']),g
            cold.append({'wait_ms':w['latency_ms'],'goal_ms':g['latency_ms'],'goal':g['response']})
        stable=tree(roots);resource=resource_sample(stable);p=pressure()
        assert stable['rss_kib']<=RSS_CAP_KIB and stable['count']<=PROCESS_CAP
        for s in servers:
            uri=(s.root/'Proof.lean').as_uri();updated=LEAN_TEXT+'-- warm edit\n';write(s.root/'Proof.lean',updated)
            s.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={
              'textDocument':dict(uri=uri,version=2),'contentChanges':[dict(text=updated)]}))
            s.request('textDocument/waitForDiagnostics',dict(uri=uri,version=2))
        waits2=[s.until(12) for s in servers]
        for s in servers:s.request('$/lean/plainGoal',dict(textDocument=dict(uri=(s.root/'Proof.lean').as_uri()),
          position=dict(line=1,character=8)))
        goals2=[s.until(13) for s in servers]
        for w,g in zip(waits2,goals2):
            assert 'n = n' in json.dumps(g['response']),g
            warm.append({'wait_ms':w['latency_ms'],'goal_ms':g['latency_ms'],'goal':g['response']})
        return {'outer':outer,'inner':inner,'server_pids':roots,'startup':starts,'cold':cold,'warm':warm,
          'stable_tree':stable,'resource_sample':resource,'memory_pressure':p,
          'configured_LEAN_NUM_THREADS':inner}
    finally:
        for s in servers:stops.append(s.stop())
        event('lean_cleanup',outer=outer,inner=inner,stops=stops,tree=tree(roots))
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,CARGO,LEAN):assert p.is_file(),p
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();host={'mem_bytes':int(command(['sysctl','-n','hw.memsize']).stdout.strip()),
      'pressure_initial':pressure(),'disk_free_initial':shutil.disk_usage(WORK).free}
    results={'cargo':{},'lean':{}};skipped=[]
    for kind in ('cargo','lean'):
        for outer in OUTERS:
            for inner in INNERS:
                a=admission(outer,kind)
                key=f'o{outer}-i{inner}'
                if not a['allowed']:
                    skipped.append({'kind':kind,'cell':key,'admission':a});continue
                try:results[kind][key]=cargo_cell(outer,inner) if kind=='cargo' else lean_cell(outer,inner)
                except Exception as ex:
                    skipped.append({'kind':kind,'cell':key,'error':repr(ex)})
                    event('cell_error',kind=kind,cell=key,error=repr(ex))
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'host':host,'limits':{'rss_cap_kib':RSS_CAP_KIB,'process_cap':PROCESS_CAP,
        'cell_seconds':CELL_SECONDS,'free_floor_percent':FREE_FLOOR_PERCENT},
      'tools':{str(p):sha(p) for p in (CHARON,CARGO,LEAN)},
      'results':results,'skipped':skipped,'events':RECORDS,
      'scope':'tiny direct Charon/Cargo and Lean server components; no Anneal or Mathlib capacity claim'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'cargo':list(results['cargo']),'lean':list(results['lean']),
      'skipped':skipped},default=str))
if __name__=='__main__':main()
