#!/usr/bin/env python3
"""Guarded multi-minute direct Lean file-worker resource/RPC soak."""
import hashlib,json,os,re,select,shutil,signal,subprocess,threading,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work';OUT=HERE/'transcript.json'
LEAN=Path(os.environ['LEAN_BIN']).resolve();START=time.monotonic();EVENTS=[];LOG_LOCK=threading.Lock()
RSS_MAX=3200*1024*1024;DISK_MAX=30*1024*1024;FREE_MIN=30;PROCESS_MAX=6;TIME_MAX=210
def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):
    with LOG_LOCK:EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def cmd(argv,**kw):return subprocess.run(argv,capture_output=True,text=True,timeout=kw.pop('timeout',8),**kw)
def free():
    p=cmd(['memory_pressure','-Q']);m=re.search(r'System-wide memory free percentage: (\d+)%',p.stdout)
    return int(m.group(1)) if m else None
def inv():
    files=[p for p in WORK.rglob('*') if p.is_file()]
    return dict(files=len(files),blocks_bytes=sum(p.stat().st_blocks*512 for p in files),
                logical_bytes=sum(p.stat().st_size for p in files),temp=[str(p.relative_to(WORK)) for p in files if '.tmp' in p.name or '.temp' in p.name])
def tree(pid):
    p=cmd(['ps','-axo','pid=,ppid=,rss=,comm='],timeout=5);rows={}
    for line in p.stdout.splitlines():
        xs=line.strip().split(maxsplit=3)
        if len(xs)!=4:continue
        try:a,b,c=map(int,xs[:3])
        except ValueError:continue
        rows[a]=dict(pid=a,ppid=b,rss_bytes=c*1024,comm=xs[3])
    seen={pid}
    while True:
        new=seen|{k for k,v in rows.items() if v['ppid'] in seen}
        if new==seen:break
        seen=new
    got=[rows[i] for i in sorted(seen) if i in rows]
    return dict(count=len(got),rss_bytes=sum(x['rss_bytes'] for x in got),processes=got)
def guard(pid,phase):
    t=tree(pid);i=inv();f=free();bad=[]
    if t['rss_bytes']>RSS_MAX:bad.append('RSS')
    if t['count']>PROCESS_MAX:bad.append('processes')
    if i['blocks_bytes']>DISK_MAX:bad.append('disk')
    if f is None or f<FREE_MIN:bad.append('free-memory')
    if time.monotonic()-START>TIME_MAX:bad.append('duration')
    log('guard',phase=phase,tree=t,inventory=i,free_percent=f,violations=bad)
    if bad:
        try:os.killpg(pid,signal.SIGKILL)
        except ProcessLookupError:pass
        raise RuntimeError('guard: '+','.join(bad))
    return t
def footprint(pid):
    try:
        p=cmd(['footprint','--pid',str(pid),'--noCategories','--format','bytes'],timeout=8)
        m=re.search(r'phys_footprint:\s*(\d+) B',p.stdout)
        return dict(pid=pid,rc=p.returncode,value_bytes=int(m.group(1)) if m else None,stdout=p.stdout,stderr=p.stderr)
    except Exception as e:return dict(pid=pid,error=repr(e))
def source(value,roundno=0):
    return f'import Dep\n#eval selected\ntheorem check : selected = {value} := by rfl\ntheorem hole (n : Nat) : n = {value} := by\n  exact ?_\n-- round {roundno}\n'
def goal_ok(r,value):return 'error' not in r and f'n = {value}' in json.dumps(r,sort_keys=True)
def info_ref(r):
    try:return r['result']['goals'][0]['hyps'][0]['type']['tag'][0]['info']
    except (KeyError,IndexError,TypeError):return None

class Server:
    def __init__(self,label,root):
        self.label=label;self.root=root;self.n=10;self.buf=b'';self.diags={}
        env=dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        log('start',label=label,pid=self.p.pid,lean_path=str(root))
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
        self.until(1);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
        self.abort_reason=None;self.monitor_stop=threading.Event()
        self.monitor=threading.Thread(target=self._watch,daemon=True);self.monitor.start()
    def _watch(self):
        polls=0
        while not self.monitor_stop.wait(.5) and self.p.poll() is None:
            polls+=1;t=tree(self.p.pid);i=inv();f=free();bad=[]
            if t['rss_bytes']>RSS_MAX:bad.append('RSS')
            if t['count']>PROCESS_MAX:bad.append('processes')
            if i['blocks_bytes']>DISK_MAX:bad.append('disk')
            if f is None or f<FREE_MIN:bad.append('free-memory')
            if time.monotonic()-START>TIME_MAX:bad.append('duration')
            if polls%10==0:log('monitor',label=self.label,tree=t,inventory=i,free_percent=f)
            if bad:
                self.abort_reason=','.join(bad)
                log('watchdog_abort',label=self.label,reason=self.abort_reason,tree=t,inventory=i,free_percent=f)
                try:os.killpg(self.p.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                return
    def send(self,msg):
        b=json.dumps(msg,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush();log('client',label=self.label,message=msg)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                h,body=self.buf.split(b'\r\n\r\n',1)
                ls=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if ls and len(body)>=ls[0]:
                    raw,self.buf=body[:ls[0]],body[ls[0]:];m=json.loads(raw);log('server',label=self.label,message=m)
                    if m.get('method')=='textDocument/publishDiagnostics':self.diags[m['params']['uri']]=m['params']
                    if m.get('method') in ('client/registerCapability','workspace/inlayHint/refresh') and 'id' in m:
                        self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
                    return m
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError(f'{self.label} read')
    def until(self,rid,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            m=self.read(max(.1,end-time.monotonic()))
            if m.get('id')==rid and 'method' not in m:return m
        raise TimeoutError(f'{self.label} id {rid}')
    def req(self,method,params,rid=None,timeout=15):
        if rid is None:rid=self.n;self.n+=1
        start=time.monotonic();self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));r=self.until(rid,timeout)
        log('latency',label=self.label,method=method,id=rid,elapsed_ms=round((time.monotonic()-start)*1000,1));return r
    def open(self,file,text,v=1):
        uri=file.as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=uri,languageId='lean',version=v,text=text)}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=v))
    def edit(self,uri,text,v):
        self.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={'textDocument':dict(uri=uri,version=v),'contentChanges':[dict(text=text)]}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=v))
    def goal(self,uri):return self.req('$/lean/plainGoal',dict(textDocument=dict(uri=uri),position=dict(line=4,character=8)))
    def connect(self,uri):return self.req('$/lean/rpc/connect',dict(uri=uri))
    def rpc(self,uri,sid,method='Lean.Widget.getInteractiveGoals',params=None):
        pos=dict(line=4,character=8)
        if params is None:params=dict(textDocument=dict(uri=uri),position=pos)
        return self.req('$/lean/rpc/call',dict(textDocument=dict(uri=uri),position=pos,sessionId=sid,method=method,params=params))
    def close(self,uri):self.send(dict(jsonrpc='2.0',method='textDocument/didClose',params={'textDocument':dict(uri=uri)}))
    def stop(self):
        self.monitor_stop.set();self.monitor.join(timeout=2)
        if self.p.poll() is not None:return
        try:
            self.req('shutdown',None,rid=999,timeout=6);self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=6)
        except Exception as e:log('stop_exception',label=self.label,error=repr(e))
        finally:
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
            log('stop',label=self.label,pid=self.p.pid,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'),after=tree(self.p.pid))

def compile_dep(root,value):
    root.mkdir();txt=f'def selected : Nat := {value}\n';(root/'Dep.lean').write_text(txt)
    e=dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
    p=cmd([str(LEAN),'-o',str(root/'Dep.olean'),str(root/'Dep.lean')],cwd=root,env=e,timeout=30)
    log('compile',root=root.name,value=value,source_sha256=sha(txt),olean_sha256=sha(root/'Dep.olean') if (root/'Dep.olean').exists() else None,rc=p.returncode,stdout=p.stdout,stderr=p.stderr)
    assert p.returncode==0

def worker_source(base,index,roundno=0):
    return f'import Dep\n#eval selected\ntheorem check : selected = {base} := by rfl\ntheorem hole (n : Nat) : n = {base+index} := by\n  exact ?_\n-- round {roundno}\n'

def pause(seconds,server):
    end=time.monotonic()+seconds
    while time.monotonic()<end:
        if server.abort_reason:raise RuntimeError('watchdog '+server.abort_reason)
        if time.monotonic()-START>TIME_MAX:raise RuntimeError('duration cap')
        time.sleep(min(.25,max(0,end-time.monotonic())))

def ramp_cell(label,root,base,workers,rounds,prior_session=None,cross_value=None):
    s=Server(label,root);files=[root/f'Proof{i}.lean' for i in range(workers)]
    uris=[p.as_uri() for p in files];versions=[1]*workers;checks=[];sid=None;ref=None
    try:
        for i,p in enumerate(files):
            txt=worker_source(base,i);p.write_text(txt);s.open(p,txt)
            g=s.goal(uris[i]);assert goal_ok(g,base+i),g
            d=s.diags.get(uris[i],{});messages=[z.get('message') for z in d.get('diagnostics',[])]
            assert str(base) in messages and not any('Tactic `rfl` failed' in z for z in messages),messages
            log('open_sentinel',label=label,file=i,base=base,goal=g,diagnostics=d,sha256=sha(txt))
            guard(s.p.pid,label+f'-open-{i}')
        if prior_session:
            old=s.rpc(uris[0],prior_session)
            log('prior_server_session',label=label,old_session=prior_session,response=old)
            assert old.get('error',{}).get('code')==-32900
        sid=s.connect(uris[0])['result']['sessionId'];rich=s.rpc(uris[0],sid);ref=info_ref(rich)
        assert ref is not None
        popup=s.rpc(uris[0],sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
        assert 'result' in popup
        log('rpc_start',label=label,session=sid,reference=ref,popup=popup)
        stable=tree(s.p.pid)
        log('resource',label=label,phase='stable',tree=stable,footprints=[footprint(z['pid']) for z in stable['processes']],free_percent=free(),inventory=inv())
        begun=time.monotonic()
        for r in range(1,rounds+1):
            for i,p in enumerate(files):
                versions[i]+=1;txt=worker_source(base,i,r)
                wait=s.edit(uris[i],txt,versions[i]);g=s.goal(uris[i]);assert goal_ok(g,base+i),g
                d=s.diags.get(uris[i],{});messages=[z.get('message') for z in d.get('diagnostics',[])]
                assert str(base) in messages and not any('Tactic `rfl` failed' in z for z in messages),messages
                checks.append(dict(round=r,file=i,version=versions[i],sha256=sha(txt),goal=g,diagnostics=d,wait=wait,ok=True))
            if r==3:
                before=s.rpc(uris[0],sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
                s.send(dict(jsonrpc='2.0',method='$/lean/rpc/release',params=dict(uri=uris[0],sessionId=sid,refs=[ref])))
                after=s.rpc(uris[0],sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
                log('rpc_release',label=label,session=sid,reference=ref,before=before,after=after)
                assert 'result' in before and after.get('error',{}).get('code')==-32602
            if r==5:
                old_sid=sid
                for i,p in enumerate(files):
                    s.close(uris[i]);s.open(p,worker_source(base,i,r),1);versions[i]=1
                stale=s.rpc(uris[0],old_sid);sid=s.connect(uris[0])['result']['sessionId']
                rich=s.rpc(uris[0],sid);ref=info_ref(rich)
                log('reopen',label=label,round=r,old_session=old_sid,new_session=sid,stale=stale,rich=rich,reference=ref)
                assert stale.get('error',{}).get('code')==-32900 and ref is not None
            if r==7:
                popup=s.rpc(uris[0],sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
                log('rpc_after_reopen',label=label,session=sid,reference=ref,popup=popup)
                assert 'result' in popup
            guard(s.p.pid,label+f'-round-{r}')
            log('round_resource',label=label,round=r,tree=tree(s.p.pid),free_percent=free())
            pause(5,s)
        if cross_value is not None:
            other=root.parent/('A' if root.name=='B' else 'B')/'Cross.lean';other.write_text(worker_source(cross_value,0))
            s.open(other,other.read_text());d=s.diags.get(other.as_uri(),{})
            log('cross_import',label=label,expected_local=cross_value,server_import=base,diagnostics=d)
            msgs=[z.get('message','') for z in d.get('diagnostics',[])]
            assert str(base) in msgs and any('not definitionally equal' in z for z in msgs)
            s.close(other.as_uri());guard(s.p.pid,label+'-cross')
        ending=tree(s.p.pid)
        log('resource',label=label,phase='end',tree=ending,footprints=[footprint(z['pid']) for z in ending['processes']],free_percent=free(),inventory=inv())
        log('cell',label=label,workers=workers,status='completed',rounds=rounds,elapsed_ms=round((time.monotonic()-begun)*1000,1),checks=checks,stable_rss_bytes=stable['rss_bytes'],end_rss_bytes=ending['rss_bytes'],session=sid)
        return dict(stable_rss=stable['rss_bytes'],end_rss=ending['rss_bytes'],session=sid)
    finally:s.stop()

def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    host=dict(memory_bytes=int(cmd(['sysctl','-n','hw.memsize']).stdout.strip()),free_start=free(),swap_start=cmd(['sysctl','vm.swapusage']).stdout.strip(),df=cmd(['df','-Pk',str(WORK)]).stdout)
    log('subject',lean_version=cmd([str(LEAN),'--version']).stdout.strip(),lean_sha256=sha(LEAN),host=host,limits=dict(rss=RSS_MAX,disk=DISK_MAX,free=FREE_MIN,processes=PROCESS_MAX,seconds=TIME_MAX))
    df_free_kib=int(host['df'].splitlines()[-1].split()[3])
    if host['memory_bytes']<8*1024**3 or host['free_start'] is None or host['free_start']<40 or df_free_kib<1024*1024:
        for n in (1,2,4):log('cell',label=f'A-{n}',workers=n,status='skipped',reason='host start guard')
        log('finish',status='all-skipped',inventory=inv());return
    a,b=WORK/'A',WORK/'B';compile_dep(a,11);compile_dep(b,22)
    one=ramp_cell('A-1',a,11,1,9)
    two=ramp_cell('A-2',a,11,2,9,prior_session=one['session'])
    predicted=two['stable_rss']+2*max(0,two['stable_rss']-one['stable_rss'])
    headroom=free();remaining=TIME_MAX-(time.monotonic()-START)
    allow=predicted<RSS_MAX*.8 and headroom is not None and headroom>=40 and remaining>=85
    log('four_admission',predicted_rss_bytes=predicted,free_percent=headroom,remaining_seconds=round(remaining,1),allowed=allow)
    if allow:four=ramp_cell('A-4',a,11,4,9,prior_session=two['session']);prior=four['session']
    else:
        log('cell',label='A-4',workers=4,status='skipped',reason='two-worker extrapolation/free-memory/time guard')
        prior=two['session']
    ramp_cell('B-1',b,22,1,6,cross_value=11)
    log('finish',status='completed',inventory=inv(),swap_end=cmd(['sysctl','vm.swapusage']).stdout.strip(),free_end=free(),prior_A_session=prior)

try:main()
except Exception as e:log('fatal',error=repr(e));raise
finally:
    raw=json.dumps(EVENTS,indent=2)+'\n'
    raw=raw.replace(WORK.as_uri(),'$WORK_URI').replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN')
    OUT.write_text(raw)
