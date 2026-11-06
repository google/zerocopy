#!/usr/bin/env python3
"""Sequential Lean 4.29/4.30-rc2 transitive import, plugin, option, and RPC probe."""
import hashlib,json,os,re,select,shutil,subprocess,time
from pathlib import Path
H=Path(__file__).resolve().parent;WORK=H/'work'
TOOLROOT=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains')
VERSIONS={'4.29.0':'leanprover--lean4---v4.29.0','4.30.0-rc2':'leanprover--lean4---v4.30.0-rc2'}
EVENTS=[];T0=time.monotonic();RSS_CAP=3*1024**3
PROOF='''import Mid
open Lean Elab Command
run_cmd do logInfo s!"OPTION={(← getOptions).getBool `pp.universes false}"
#eval transitive
theorem data : transitive = 7 := by rfl
theorem macro_check : True := by probe_tac
theorem rpc_check (n : Nat) (h : n = transitive) : n = transitive := by
  exact ?_
'''
SLOW='''import Lean
theorem demo : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  exact ?_
'''
FAST='theorem demo : False := by\n  exact ?_\n'
def sha(x):return hashlib.sha256(x.read_bytes() if isinstance(x,Path) else x.encode()).hexdigest()
def event(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-T0)*1000,1),kind=kind,**kw))
def cmd(label,args,cwd,env,timeout=30):
    start=time.monotonic()
    try:
        p=subprocess.run(list(map(str,args)),cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
        rc,out,err=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as e:
        rc='timeout';out=(e.stdout or b'').decode(errors='replace');err=(e.stderr or b'').decode(errors='replace')
    row=dict(label=label,argv=list(map(str,args)),cwd=str(cwd),rc=rc,elapsed_ms=round((time.monotonic()-start)*1000,1),stdout=out,stderr=err)
    event('command',**row);return row
def env_for(bin,version,root):
    env=dict(os.environ,ELAN_TOOLCHAIN='leanprover/lean4:v'+version,LEAN_NUM_THREADS='1',LAKE_CACHE_DIR='',LAKE_ARTIFACT_CACHE='false',MATHLIB_NO_CACHE_ON_UPDATE='1',PLUGIN_MARKER=str(root/'marker.txt'))
    env['PATH']=str(bin)+os.pathsep+env.get('PATH','')
    return env
def tree(pid):
    p=subprocess.run(['ps','-axo','pid=,ppid=,rss=,comm='],capture_output=True,text=True,timeout=5)
    rows={}
    for line in p.stdout.splitlines():
        xs=line.split(maxsplit=3)
        if len(xs)!=4:continue
        try:i,parent,rss=map(int,xs[:3])
        except ValueError:continue
        rows[i]=dict(pid=i,parent=parent,rss_bytes=rss*1024,comm=xs[3])
    seen={pid}
    while True:
        new={i for i,v in rows.items() if v['parent'] in seen}
        if new<=seen:break
        seen|=new
    found=[rows[i] for i in sorted(seen) if i in rows]
    return dict(count=len(found),rss_bytes=sum(x['rss_bytes'] for x in found),processes=found)
def lakefile(option):return 'import Lake\nopen Lake DSL\npackage rpc_matrix where\n  moreServerOptions := #[⟨`pp.universes, '+('true' if option else 'false')+'⟩]\nlean_lib Base\nlean_lib Mid\nlean_lib Plugin\n'
def base(value,macro):return 'import Lean\nsyntax "probe_tac" : tactic\nmacro_rules | `(tactic| probe_tac) => `(tactic| '+macro+')\ndef selected : Nat := '+str(value)+'\n'
def plugin(tag):return 'import Lean\ninitialize do\n  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n  if !p.isEmpty then IO.FS.writeFile p "plugin-'+tag+'"\n'
def make(root,version,value,macro,option,tag):
    root.mkdir(parents=True)
    (root/'lean-toolchain').write_text('leanprover/lean4:v'+version+'\n')
    (root/'lakefile.lean').write_text(lakefile(option))
    (root/'Base.lean').write_text(base(value,macro))
    (root/'Mid.lean').write_text('import Base\ndef transitive : Nat := selected\n')
    (root/'Plugin.lean').write_text(plugin(tag))
    (root/'Proof.lean').write_text(PROOF);(root/'New.lean').write_text(PROOF)
def dylib(root):return root/'.lake/build/lib/lean/rpc__matrix_Plugin.dylib'
def arts(root):
    ps=[root/'.lake/build/lib/lean/Base.olean',root/'.lake/build/lib/lean/Mid.olean',dylib(root)]
    return {p.name:(sha(p) if p.exists() else None) for p in ps}
class Server:
    def __init__(self,label,root,lean,env,plugin_path=None):
        self.label=label;self.root=root;self.buf=b'';self.n=10;self.diags={}
        if plugin_path:
            args=[str(lean.with_name('lake')),'--keep-toolchain','--no-cache','env',str(lean),'--plugin='+str(plugin_path),'--server']
        else:args=[str(lean),'--server']
        self.p=subprocess.Popen(args,cwd=root,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        event('launch',label=label,argv=args,pid=self.p.pid)
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
        self.until(1,18);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush();event('client',label=self.label,message=msg)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                h,b=self.buf.split(b'\r\n\r\n',1)
                n=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if n and len(b)>=n[0]:
                    raw,self.buf=b[:n[0]],b[n[0]:];m=json.loads(raw);event('server',label=self.label,message=m)
                    if m.get('method')=='textDocument/publishDiagnostics':self.diags[m['params']['uri']]=m['params']
                    if 'method' in m and 'id' in m:self.send(dict(jsonrpc='2.0',id=m['id'],result=None))
                    return m
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                x=os.read(self.p.stdout.fileno(),65536)
                if not x:break
                self.buf+=x
        raise TimeoutError(self.label+' read')
    def until(self,rid,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            m=self.read(max(.1,end-time.monotonic()))
            if m.get('id')==rid and 'method' not in m:return m
        raise TimeoutError(self.label+' request '+str(rid))
    def req(self,method,params,rid=None,timeout=15):
        if rid is None:rid=self.n;self.n+=1
        self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return self.until(rid,timeout)
    def open(self,name,text=None,ver=1,wait=True):
        u=(self.root/name).as_uri();text=text if text is not None else (self.root/name).read_text()
        self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=u,languageId='lean',version=ver,text=text)}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=u,version=ver)) if wait else None
    def close(self,name):self.send(dict(jsonrpc='2.0',method='textDocument/didClose',params={'textDocument':dict(uri=(self.root/name).as_uri())}))
    def watched(self,name):self.send(dict(jsonrpc='2.0',method='workspace/didChangeWatchedFiles',params={'changes':[dict(uri=(self.root/name).as_uri(),type=2)]}))
    def goal(self,name,line,col,rid=None):return self.req('$/lean/plainGoal',dict(textDocument=dict(uri=(self.root/name).as_uri()),position=dict(line=line,character=col)),rid)
    def connect(self,name):return self.req('$/lean/rpc/connect',dict(uri=(self.root/name).as_uri()))
    def rpc(self,name,sid,method,params,line=7,col=8):
        return self.req('$/lean/rpc/call',dict(textDocument=dict(uri=(self.root/name).as_uri()),position=dict(line=line,character=col),sessionId=sid,method=method,params=params))
    def release(self,name,sid,refs):self.send(dict(jsonrpc='2.0',method='$/lean/rpc/release',params=dict(uri=(self.root/name).as_uri(),sessionId=sid,refs=refs)))
    def stop(self):
        if self.p.poll() is None:
            try:self.req('shutdown',None,rid=99,timeout=5);self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
            except Exception:self.p.kill();self.p.wait()
        event('stop',label=self.label,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))
def info_ref(obj):
    if isinstance(obj,dict):
        if 'info' in obj and isinstance(obj['info'],dict) and 'p' in obj['info']:return obj['info']
        for x in obj.values():
            r=info_ref(x)
            if r:return r
    if isinstance(obj,list):
        for x in obj:
            r=info_ref(x)
            if r:return r
    return None
def sample(s,phase,name):
    t=tree(s.p.pid)
    if t['rss_bytes']>RSS_CAP:raise MemoryError('3 GiB sampled server tree cap')
    row=dict(phase=phase,name=name,goal_data=s.goal(name,4,39),goal_macro=s.goal(name,5,42),goal_rpc=s.goal(name,7,8),diagnostics=s.diags.get((s.root/name).as_uri()),marker=(s.root/'marker.txt').read_text() if (s.root/'marker.txt').exists() else None,artifacts=arts(s.root),tree=t)
    event('sample',label=s.label,**row);return row
def setup(label,lake,root,env):
    r=cmd(label,[lake,'--keep-toolchain','--no-cache','setup-file','Proof.lean'],root,env)
    try:value=json.loads(r['stdout'])
    except Exception:value=None
    event('setup',label=label,json=value,artifacts=arts(root));return value
def one(version):
    bin=TOOLROOT/VERSIONS[version]/'bin';lean=bin/'lean';lake=bin/'lake';root=WORK/('v'+version.replace('.','_').replace('-','_'))
    env=env_for(bin,version,root)
    event('subject',version=version,lean_version=cmd('lean-version-'+version,[lean,'--version'],WORK,env)['stdout'].strip(),lean_sha256=sha(lean),lake_sha256=sha(lake))
    make(root,version,7,'trivial',False,'v1');v2=WORK/('plugin-v2-'+version.replace('.','_').replace('-','_'));make(v2,version,9,'skip',True,'v2')
    for label,r in [('v1',root),('v2',v2)]:
        c=cmd('build-'+version+'-'+label,[lake,'--keep-toolchain','--no-cache','build','Mid','+Plugin:dynlib'],r,env)
        if c['rc']!=0:raise RuntimeError(c)
    before=setup('setup-before-'+version,lake,root,env)
    s=Server('main-'+version,root,lean,env,dylib(root))
    try:
        s.open('Proof.lean');old=sample(s,'old','Proof.lean')
        sid=s.connect('Proof.lean')['result']['sessionId']
        params=dict(textDocument=dict(uri=(root/'Proof.lean').as_uri()),position=dict(line=7,character=8))
        rich=s.rpc('Proof.lean',sid,'Lean.Widget.getInteractiveGoals',params)
        ref=info_ref(rich.get('result'))
        deref=s.rpc('Proof.lean',sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref) if ref else None
        event('rpc_initial',version=version,session=sid,rich=rich,info_ref=ref,deref=deref)
        (root/'Base.lean').write_text(base(9,'skip'))
        (root/'lakefile.lean').write_text(lakefile(True))
        p=dylib(root);tmp=p.with_suffix('.replacement');shutil.copy2(dylib(v2),tmp);os.replace(tmp,p)
        event('transition',version=version,base_sha256=sha(root/'Base.lean'),lakefile_sha256=sha(root/'lakefile.lean'),plugin_sha256=sha(p),artifacts=arts(root))
        for name in ['Base.lean','Plugin.lean','lakefile.lean']:s.watched(name)
        old_after_change=sample(s,'old-after-change-before-new','Proof.lean')
        s.open('New.lean');new=sample(s,'new','New.lean')
        old_after_new=sample(s,'old-after-new','Proof.lean')
        retained=s.rpc('Proof.lean',sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref) if ref else None
        s.release('Proof.lean',sid,[ref] if ref else [])
        released=s.rpc('Proof.lean',sid,'Lean.Widget.InteractiveDiagnostics.infoToInteractive',ref) if ref else None
        event('rpc_retained_release',version=version,session=sid,ref=ref,retained=retained,after_release=released)
    finally:s.stop()
    fresh=Server('fresh-'+version,root,lean,env,dylib(root))
    try:
        fresh.open('Proof.lean');reopened=sample(fresh,'fresh-server','Proof.lean')
        stale_session=fresh.rpc('Proof.lean',sid,'Lean.Widget.getInteractiveGoals',params)
        fresh_sid=fresh.connect('Proof.lean')['result']['sessionId']
        fresh_rich=fresh.rpc('Proof.lean',fresh_sid,'Lean.Widget.getInteractiveGoals',params)
        event('rpc_after_restart',version=version,old_session=stale_session,new_session=fresh_sid,new_rich=fresh_rich)
    finally:fresh.stop()
    after=setup('setup-after-'+version,lake,root,env)
    batch=cmd('batch-after-'+version,[lake,'--keep-toolchain','--no-cache','env',lean,'--plugin='+str(dylib(root)),'Proof.lean'],root,env)
    event('matrix',version=version,setup_before=before,setup_after=after,old=old,old_after_change=old_after_change,new=new,old_after_new=old_after_new,reopened=reopened,batch_rc=batch['rc'])
    # One watchdog, two file workers: delayed old reply and a reused request number.
    gate=WORK/('gate-'+version.replace('.','_').replace('-','_'));gate.mkdir()
    (gate/'Slow.lean').write_text(SLOW);(gate/'Fast.lean').write_text(FAST)
    (gate/'gate.release').unlink(missing_ok=True);(gate/'gate.entered').unlink(missing_ok=True)
    gated=Server('gated-'+version,gate,lean,env)
    try:
        gated.open('Slow.lean',wait=False)
        deadline=time.monotonic()+12
        while not (gate/'gate.entered').exists() and time.monotonic()<deadline:time.sleep(.01)
        if not (gate/'gate.entered').exists():raise TimeoutError('tactic gate not entered')
        gated.send(dict(jsonrpc='2.0',id=50,method='$/lean/plainGoal',params=dict(textDocument=dict(uri=(gate/'Slow.lean').as_uri()),position=dict(line=5,character=8))))
        gated.open('Fast.lean')
        fast=gated.goal('Fast.lean',1,9,rid=50)
        (gate/'gate.release').write_text('release')
        delayed=gated.until(50,15)
        event('causal_delay',version=version,same_transport_pid=gated.p.pid,reused_request_id=50,fast=fast,delayed=delayed,tree=tree(gated.p.pid))
    finally:
        (gate/'gate.release').write_text('release');gated.stop()
def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    pressure=cmd('memory-pressure',['memory_pressure','-Q'],WORK,os.environ,5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',pressure['stdout'])
    if m and int(m.group(1))<20:raise RuntimeError('low free memory')
    for v in VERSIONS:one(v)
    (H/'transcript.json').write_text(json.dumps(EVENTS,indent=2)+'\n')
    print(json.dumps(dict(events=len(EVENTS),probe_sha256=sha(Path(__file__)),transcript_sha256=sha(H/'transcript.json')),indent=2))
if __name__=='__main__':main()
