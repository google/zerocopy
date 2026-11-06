#!/usr/bin/env python3
"""Sequential bounded direct Lean LSP soak, conflicting imports, RPC refs."""
import hashlib,json,os,re,select,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work';OUT=HERE/'transcript.json'
LEAN=Path(os.environ['LEAN_BIN']).resolve();START=time.monotonic();EVENTS=[]
RSS_MAX=2100*1024*1024;DISK_MAX=16*1024*1024;FREE_MIN=30;PROCESS_MAX=4;TIME_MAX=160
def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
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
    if bad:raise RuntimeError('guard: '+','.join(bad))
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
                    if m.get('method')=='client/registerCapability' and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
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
            if m.get('id')==rid:return m
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

def cycle(label,root,value,rounds=12,wrong=None):
    s=Server(label,root);uri=(root/'Proof.lean').as_uri();text=source(value);(root/'Proof.lean').write_text(text)
    try:
        s.open(root/'Proof.lean',text);g=s.goal(uri);assert goal_ok(g,value),g
        sid=s.connect(uri)['result']['sessionId'];rich=s.rpc(uri,sid);ref=info_ref(rich)
        popup=s.rpc(uri,sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref) if ref else None
        log('rpc_reference',label=label,phase='initial',session=sid,info_ref=ref,popup=popup,rich=rich)
        guard(s.p.pid,label+'-initial')
        initial=tree(s.p.pid);log('resource',label=label,phase='initial',tree=initial,footprints=[footprint(p['pid']) for p in initial['processes']])
        version=1;checks=[];pids=[]
        for r in range(1,rounds+1):
            text=source(value,r);version+=1
            wait=s.edit(uri,text,version);g=s.goal(uri);ok=goal_ok(g,value);assert ok,g
            checks.append(dict(round=r,version=version,source_sha256=sha(text),goal_ok=ok,wait=wait,goal=g,diag=s.diags.get(uri)))
            if r in (3,6,9,12):
                rich=s.rpc(uri,sid);ref_after=info_ref(rich)
                old_popup=s.rpc(uri,sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref) if ref else None
                log('rpc_reference',label=label,phase=f'edit-{r}',session=sid,old_info_ref=ref,old_popup=old_popup,new_info_ref=ref_after,rich=rich)
                if r==3 and ref:
                    s.send(dict(jsonrpc='2.0',method='$/lean/rpc/release',params=dict(uri=uri,sessionId=sid,refs=[ref])))
                    after_release=s.rpc(uri,sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref)
                    log('release_control',label=label,session=sid,reference=ref,response=after_release)
            if r in (4,8):
                oldsid=sid;s.close(uri);s.open(root/'Proof.lean',text,1);version=1
                stale=s.rpc(uri,oldsid);sid=s.connect(uri)['result']['sessionId']
                renewed=s.rpc(uri,sid);log('reopen',label=label,round=r,old_session=oldsid,new_session=sid,stale=stale,renewed=renewed)
                assert stale.get('error',{}).get('code')==-32900
                assert goal_ok(s.goal(uri),value)
            pids.append([p['pid'] for p in tree(s.p.pid)['processes']])
            guard(s.p.pid,f'{label}-edit-{r}')
        if wrong is not None:
            other=root.parent/('B' if root.name=='A' else 'A')/'WrongUnderA.lean';other.write_text(source(wrong))
            s.open(other,source(wrong));cross=s.diags.get(other.as_uri());g=s.goal(other.as_uri())
            log('wrong_import',label=label,other_uri=other.as_uri(),expected_local=wrong,server_import=value,diagnostics=cross,goal=g)
            s.close(other.as_uri());guard(s.p.pid,label+'-wrong-import')
        log('cycle',label=label,rounds=rounds,checks=checks,pid_sequences=pids,final_session=sid)
        return sid,ref
    finally:s.stop()

def timeout_control(root,value):
    s=Server('timeout',root);uri=(root/'Timeout.lean').as_uri();txt=source(value);(root/'Timeout.lean').write_text(txt)
    try:
        s.open(root/'Timeout.lean',txt);guard(s.p.pid,'timeout-open')
        rid=900;start=time.monotonic();s.send(dict(jsonrpc='2.0',id=rid,method='textDocument/waitForDiagnostics',params=dict(uri=uri,version=999)))
        time.sleep(.12);log('client_deadline',request_id=rid,elapsed_ms=round((time.monotonic()-start)*1000,1))
        s.send(dict(jsonrpc='2.0',method='$/cancelRequest',params=dict(id=rid)))
        try:reply=s.until(rid,5)
        except TimeoutError as e:reply={'client_wait_error':repr(e)}
        recovered=s.goal(uri);log('timeout_control',reply=reply,recovered=recovered,elapsed_ms=round((time.monotonic()-start)*1000,1))
        assert goal_ok(recovered,value)
        guard(s.p.pid,'timeout-recovered')
    finally:s.stop()

def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    host=dict(memory_bytes=int(cmd(['sysctl','-n','hw.memsize']).stdout.strip()),free_start=free(),swap_start=cmd(['sysctl','vm.swapusage']).stdout.strip())
    log('subject',lean_version=cmd([str(LEAN),'--version']).stdout.strip(),lean_sha256=sha(LEAN),host=host,limits=dict(rss=RSS_MAX,disk=DISK_MAX,free=FREE_MIN,processes=PROCESS_MAX,seconds=TIME_MAX))
    assert host['memory_bytes']>=8*1024**3 and host['free_start'] is not None and host['free_start']>=40
    a,b=WORK/'A',WORK/'B';compile_dep(a,11);compile_dep(b,22)
    sid,ref=cycle('A-first',a,11,wrong=22)
    # A new watchdog revisits the same URI and document version after a full stop.
    s=Server('A-restart',a);uri=(a/'Proof.lean').as_uri()
    try:
        s.open(a/'Proof.lean',source(11,12),1);old=s.rpc(uri,sid);newid=s.connect(uri)['result']['sessionId'];new=s.rpc(uri,newid)
        log('restart',old_session=sid,old_reference=ref,old=old,new_session=newid,new=new,goal=s.goal(uri))
        assert old.get('error',{}).get('code')==-32900 and goal_ok(s.goal(uri),11)
        guard(s.p.pid,'A-restart')
    finally:s.stop()
    cycle('B',b,22)
    timeout_control(b,22)
    post=Server('post-timeout-restart',b);post_uri=(b/'Timeout.lean').as_uri()
    try:
        post.open(b/'Timeout.lean',source(22),1)
        post_goal=post.goal(post_uri);post_sid=post.connect(post_uri)['result']['sessionId']
        post_rich=post.rpc(post_uri,post_sid)
        log('post_timeout_restart',goal=post_goal,session=post_sid,rich=post_rich)
        assert goal_ok(post_goal,22) and 'result' in post_rich
        guard(post.p.pid,'post-timeout-restart')
    finally:post.stop()
    log('finish',inventory=inv(),swap_end=cmd(['sysctl','vm.swapusage']).stdout.strip(),free_end=free())

try:main()
except Exception as e:log('fatal',error=repr(e));raise
finally:
    raw=json.dumps(EVENTS,indent=2)+'\n'
    raw=raw.replace(WORK.as_uri(),'$WORK_URI').replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN')
    OUT.write_text(raw)
