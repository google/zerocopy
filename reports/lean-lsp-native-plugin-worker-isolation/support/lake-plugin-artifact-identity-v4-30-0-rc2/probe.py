#!/usr/bin/env python3
"""Sequential, scratch-only native/plugin and prepared-artifact probe."""
import hashlib, json, os, re, select, shutil, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE/'work'
BIN=Path(os.environ.get('LEAN_BIN','/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'))
LAKE=BIN.with_name('lake')
TOOLCHAIN='leanprover/lean4:v4.30.0-rc2'
ENV=dict(os.environ,ELAN_TOOLCHAIN=TOOLCHAIN,LEAN_NUM_THREADS='1',LAKE_CACHE_DIR='',LAKE_ARTIFACT_CACHE='false',MATHLIB_NO_CACHE_ON_UPDATE='1')
ENV['PATH']=str(BIN.parent)+os.pathsep+ENV.get('PATH','')
LOG=[]; T0=time.monotonic()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def event(kind,**kw): LOG.append(dict(seq=len(LOG),time_ms=round((time.monotonic()-T0)*1000,1),kind=kind,**kw))
def cmd(label,argv,cwd,env=None,timeout=30):
    start=time.monotonic()
    try:
        p=subprocess.run(list(map(str,argv)),cwd=cwd,env=env or ENV,capture_output=True,text=True,timeout=timeout)
        rc,out,err=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as e:
        rc,out,err='timeout',(e.stdout or b'').decode(errors='replace'),(e.stderr or b'').decode(errors='replace')
    row=dict(label=label,argv=list(map(str,argv)),cwd=str(cwd),rc=rc,elapsed_ms=round((time.monotonic()-start)*1000,1),stdout=out,stderr=err)
    event('command',**row); return row
def write_fixture(root,plugin_tag='v1',alien=False):
    root.mkdir(parents=True)
    (root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage plugin_probe\nlean_lib Dep\nlean_lib Plugin\n'+('lean_lib Alien\n' if alien else ''))
    (root/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    (root/'Dep.lean').write_text('import Lean\nsyntax "probe_tac" : tactic\nmacro_rules | `(tactic| probe_tac) => `(tactic| decide)\ndef selected : Nat := 7\n')
    (root/'Plugin.lean').write_text('import Lean\ninitialize do\n  let p := (← IO.getEnv "PLUGIN_MARKER").getD ""\n  if !p.isEmpty then IO.FS.writeFile p "plugin-'+plugin_tag+'"\n')
    if alien:(root/'Alien.lean').write_text('import Lean\ninitialize pure ()\n')
    proof='import Dep\ntheorem checked : selected = 7 := by\n  probe_tac\n#eval selected\n'
    (root/'Proof.lean').write_text(proof);(root/'New.lean').write_text(proof)
def dynlib(root): return root/'.lake/build/lib/lean/plugin__probe_Plugin.dylib'
def built(root):
    r=cmd('build-'+root.name,[LAKE,'--keep-toolchain','--no-cache','build','Dep','+Plugin:dynlib'],root)
    if r['rc']!=0: raise RuntimeError(r)
    event('built',root=str(root),artifacts={p.name:dict(sha256=sha(p),bytes=p.stat().st_size) for p in [root/'.lake/build/lib/lean/Dep.olean',root/'.lake/build/lib/lean/Dep.ilean',root/'.lake/build/ir/Dep.c',dynlib(root)]})
def copytree(src,dst): shutil.copytree(src,dst)
def batch(label,root,plugin=True):
    env=dict(ENV,PLUGIN_MARKER=str(root/'marker.txt'))
    args=[LAKE,'--keep-toolchain','--no-cache','env',BIN]
    if plugin: args+=['--plugin='+str(dynlib(root))]
    args+=['Proof.lean']
    r=cmd(label,args,root,env)
    event('batch_outcome',label=label,marker=(root/'marker.txt').read_text() if (root/'marker.txt').exists() else None)
    return r
class Server:
    def __init__(self,label,root):
        self.label=label;self.root=root;self.buf=b'';self.next=10;self.diags={}
        env=dict(ENV,LEAN_PATH=str(root/'.lake/build/lib/lean'),PLUGIN_MARKER=str(root/'marker.txt'))
        args=[str(BIN),'--plugin='+str(dynlib(root)),'--server']
        self.p=subprocess.Popen(args,cwd=root,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        event('server_start',label=label,argv=args,pid=self.p.pid)
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
                    raw,self.buf=b[:n[0]],b[n[0]:];msg=json.loads(raw);event('server',label=self.label,message=msg)
                    if msg.get('method')=='textDocument/publishDiagnostics':self.diags[msg['params']['uri']]=msg['params']
                    if 'method' in msg and 'id' in msg:self.send(dict(jsonrpc='2.0',id=msg['id'],result=None))
                    return msg
            rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if rd:
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
    def req(self,method,params):
        rid=self.next;self.next+=1;self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return self.until(rid)
    def open(self,name):
        u=(self.root/name).as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={'textDocument':dict(uri=u,languageId='lean',version=1,text=(self.root/name).read_text())}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=u,version=1))
    def goal(self,name):return self.req('$/lean/plainGoal',dict(textDocument=dict(uri=(self.root/name).as_uri()),position=dict(line=2,character=4)))
    def stop(self):
        if self.p.poll() is None:
            try:
                self.send(dict(jsonrpc='2.0',id=99,method='shutdown',params=None));self.until(99,5);self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
            except Exception:self.p.kill();self.p.wait()
        event('server_stop',label=self.label,rc=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace'))
def phase(s,label,name):
    wait=s.open(name);goal=s.goal(name) if 'error' not in wait else None;u=(s.root/name).as_uri()
    marker=(s.root/'marker.txt').read_text() if (s.root/'marker.txt').exists() else None
    event('phase',label=label,wait=wait,goal=goal,diagnostics=s.diags.get(u),marker=marker)
def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    q=cmd('memory-pressure',['memory_pressure','-Q'],WORK,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',q['stdout'])
    if m and int(m.group(1))<20:raise RuntimeError('low free memory')
    event('subject',lean_sha256=sha(BIN),lake_sha256=sha(LAKE),lean_version=cmd('lean-version',[BIN,'--version'],WORK)['stdout'].strip(),os=cmd('uname',['uname','-a'],WORK)['stdout'].strip())
    v1=WORK/'seed-v1';v2=WORK/'seed-v2';write_fixture(v1);write_fixture(v2,'v2');built(v1);built(v2)
    alien=WORK/'seed-alien';write_fixture(alien,alien=True);built(alien)
    r=cmd('build-alien',[LAKE,'--keep-toolchain','--no-cache','build','+Alien:dynlib'],alien)
    if r['rc']!=0:raise RuntimeError(r)
    alienlib=next((alien/'.lake/build/lib/lean').glob('*Alien*.dylib'))
    event('alien-binary',path=str(alienlib),sha256=sha(alienlib))
    # A fresh prepared copy for each omitted family; no cache restoration.
    for family,relative in [('olean','.lake/build/lib/lean/Dep.olean'),('ilean','.lake/build/lib/lean/Dep.ilean'),('c','.lake/build/ir/Dep.c'),('dynlib',str(dynlib(v1).relative_to(v1)))]:
        root=WORK/('prune-'+family);copytree(v1,root);target=root/relative;before=sha(target);target.unlink()
        event('prune',family=family,path=str(target),prior_sha256=before)
        cmd('no-build-'+family,[LAKE,'--keep-toolchain','--no-cache','--no-build','build','Dep','+Plugin:dynlib'],root)
        batch('batch-before-setup-'+family,root)
        if family=='dynlib':batch('batch-without-plugin-after-prune-dynlib',root,plugin=False)
        cmd('setup-'+family,[LAKE,'--keep-toolchain','--no-cache','setup-file','Proof.lean'],root)
        batch('batch-after-setup-'+family,root)
        event('after-prune',family=family,restored=target.exists(),sha256=sha(target) if target.exists() else None)
    live=WORK/'live';copytree(v1,live)
    s=Server('old-loaded',live)
    try:
        phase(s,'old-before','Proof.lean')
        path=dynlib(live);old=sha(path);tmp=path.with_suffix('.replacement');shutil.copy2(dynlib(v2),tmp);os.replace(tmp,path)
        event('replace-plugin',old_sha256=old,new_sha256=sha(path),old_marker=(live/'marker.txt').read_text() if (live/'marker.txt').exists() else None)
        event('old-goal-after',goal=s.goal('Proof.lean'),marker=(live/'marker.txt').read_text() if (live/'marker.txt').exists() else None)
        phase(s,'old-process-new-worker','New.lean')
    finally:s.stop()
    batch('batch-fresh-after-replace',live)
    fresh=Server('fresh-after-replace',live)
    try:phase(fresh,'fresh','Proof.lean')
    finally:fresh.stop()
    abi=WORK/'bad-abi-live';copytree(v1,abi)
    old=Server('bad-abi-old-loaded',abi)
    try:
        phase(old,'bad-abi-before','Proof.lean')
        path=dynlib(abi);prior=sha(path);tmp=path.with_suffix('.replacement');shutil.copy2(alienlib,tmp);os.replace(tmp,path)
        event('replace-bad-abi',old_sha256=prior,new_sha256=sha(path),old_marker=(abi/'marker.txt').read_text() if (abi/'marker.txt').exists() else None)
        event('bad-abi-old-goal-after',goal=old.goal('Proof.lean'))
        try:phase(old,'bad-abi-new-worker','New.lean')
        except Exception as e:event('bad-abi-new-worker-error',error=repr(e))
    finally:old.stop()
    batch('batch-fresh-bad-abi',abi)
    # Explicit corrupt/missing ABI controls are fresh processes only.
    corrupt=WORK/'corrupt';copytree(v1,corrupt);p=dynlib(corrupt);p.write_bytes(b'not a Mach-O dylib\n');batch('batch-invalid-dylib',corrupt)
    missing=WORK/'missing';copytree(v1,missing);dynlib(missing).unlink();batch('batch-missing-dylib',missing)
    out=HERE/'transcript.json';out.write_text(json.dumps(LOG,indent=2)+'\n')
    print(json.dumps({'events':len(LOG),'transcript_sha256':sha(out),'probe_sha256':sha(Path(__file__)),'work':str(WORK)},indent=2))
if __name__=='__main__':main()
