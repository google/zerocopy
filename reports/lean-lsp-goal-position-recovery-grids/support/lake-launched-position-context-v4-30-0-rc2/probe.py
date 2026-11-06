#!/usr/bin/env python3
"""Bounded offline Lake-launched plain/rich tactic-position probe."""
import argparse, hashlib, json, os, re, select, shutil, signal, subprocess, time
from pathlib import Path

BIN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE, LEAN = BIN/'lake', BIN/'lean'
PROFILE = '(version 1) (allow default) (deny network*)'
SOURCE = '''import Dep

theorem positioned (n : Nat) (h : n = depValue) : n + 0 = depValue := by
  have hz : n + 0 = depValue := by
    simpa using h
  exact hz
#print axioms positioned
#eval depValue
'''
DEP = 'def depValue : Nat := 7\n'
POSITIONS = {'outer_have': (3,2), 'inner_start': (4,4), 'inner_inside': (4,8),
             'inner_end': (4,17), 'outer_exact': (5,2), 'outer_exact_end': (5,10),
             'eof': (8,0)}

def digest(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def memory_free():
    s=subprocess.check_output(['vm_stat'],text=True)
    page=int(re.search(r'page size of (\d+) bytes',s).group(1))
    count=sum(int(re.search(rf'^{k}:\s+(\d+)',s,re.M).group(1)) for k in ('Pages free','Pages inactive','Pages speculative','Pages purgeable'))
    return round(100*count*page/int(subprocess.check_output(['sysctl','-n','hw.memsize'],text=True)),2)
def env(work):
    e=dict(os.environ)
    e.update(HOME=str(work/'home'),XDG_CACHE_HOME=str(work/'xdg'),ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',
             LAKE_CACHE_DIR=str(work/'cache'),LAKE_ARTIFACT_CACHE='false',LAKE_NO_NET='1',
             LEAN_NUM_THREADS='1',PATH=str(BIN)+os.pathsep+e.get('PATH',''))
    return e
def make(work):
    dep,root=work/'dep',work/'project';dep.mkdir();root.mkdir()
    (dep/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
    (dep/'Dep.lean').write_text(DEP)
    (dep/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    (root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../dep"\npackage position_probe\n@[default_target]\nlean_lib Proof\n')
    (root/'Proof.lean').write_text(SOURCE)
    (root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    manifest={'version':'1.2.0','packagesDir':'.lake/packages','packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json','inherited':False,'dir':'../dep','configFile':'lakefile.lean'}],'name':'position_probe','lakeDir':'.lake','fixedToolchain':False}
    (root/'lake-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    return dep,root
def norm(obj,work):
    return json.loads(json.dumps(obj,ensure_ascii=False).replace(work.as_uri(),'$WORK_URI').replace(str(work),'$WORK').replace(str(BIN.parent),'$TOOLCHAIN'))
class Server:
    def __init__(self,root,e,events):
        self.root=root;self.events=events;self.buf=b'';self.id=10
        self.p=subprocess.Popen(['/usr/bin/sandbox-exec','-p',PROFILE,str(LAKE),'--keep-toolchain','--no-cache','serve'],cwd=root,env=e,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}})
        self.until(1,25);self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,m):
        raw=json.dumps(m,ensure_ascii=False,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
        self.events.append({'direction':'client','message':m})
    def read(self,timeout):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                h,b=self.buf.split(b'\r\n\r\n',1);n=int(re.search(rb'Content-Length:\s*(\d+)',h,re.I).group(1))
                if len(b)>=n:
                    raw,self.buf=b[:n],b[n:];m=json.loads(raw)
                    self.events.append({'direction':'server','message':m})
                    if 'method' in m and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
                    return m
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                part=os.read(self.p.stdout.fileno(),65536)
                if not part:raise RuntimeError('server closed stdout')
                self.buf+=part
        raise TimeoutError('server response')
    def until(self,rid,timeout=35):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            m=self.read(end-time.monotonic())
            if m.get('id')==rid:return m
        raise TimeoutError(f'request {rid}')
    def req(self,method,params,timeout=35):
        self.id+=1;rid=self.id
        self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.until(rid,timeout)
    def stop(self):
        try:
            if self.p.poll() is None:
                self.send({'jsonrpc':'2.0','id':99,'method':'shutdown','params':None});self.until(99,7)
                self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=7)
        except Exception:
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        return {'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();work=a.work.resolve()
    if work.exists():raise SystemExit('work must be absent')
    disk=shutil.disk_usage(work.parent).free;mem=memory_free()
    if disk<10*1024**3 or mem<20:raise SystemExit(f'preflight denied disk={disk} free_memory={mem}')
    if not (LAKE.is_file() and LEAN.is_file()):raise SystemExit('pinned local tools missing')
    work.mkdir();(work/'home').mkdir();(work/'xdg').mkdir();dep,root=make(work);e=env(work)
    def command(label,args,timeout=35):
        p=subprocess.run(['/usr/bin/sandbox-exec','-p',PROFILE,str(LAKE),'--keep-toolchain',*args],cwd=root,env=e,capture_output=True,text=True,timeout=timeout)
        return {'label':label,'args':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    build=command('build',['-v','build','Proof'])
    batch=command('batch',['--no-cache','env','lean','--json','Proof.lean'])
    setup=command('setup',['--no-cache','setup-file','Proof.lean'])
    events=[];s=None;live={}
    try:
        s=Server(root,e,events);uri=(root/'Proof.lean').as_uri();doc={'uri':uri,'version':1}
        s.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':SOURCE}}})
        wait=s.req('textDocument/waitForDiagnostics',doc)
        conn=s.req('$/lean/rpc/connect',{'uri':uri});session=conn['result']['sessionId']
        for name,(line,col) in POSITIONS.items():
            pos={'line':line,'character':col}
            plain=s.req('$/lean/plainGoal',{'textDocument':doc,'position':pos})
            rich=s.req('$/lean/rpc/call',{'textDocument':doc,'position':pos,'sessionId':session,'method':'Lean.Widget.getInteractiveGoals','params':{'textDocument':doc,'position':pos}})
            live[name]={'position':pos,'plain':plain,'rich':rich}
    finally:
        stop=s.stop() if s else {'exit':None,'stderr':'start failed'}
    result={'preflight':{'disk_free_bytes':disk,'memory_free_percent':mem},
            'tools':{'lake_sha256':digest(LAKE),'lean_sha256':digest(LEAN)},
            'source':{'Dep.lean':DEP,'Proof.lean':SOURCE,'sha256':{'Dep.lean':digest(dep/'Dep.lean'),'Proof.lean':digest(root/'Proof.lean')}},
            'artifacts':{'Dep.olean':digest(dep/'.lake/build/lib/lean/Dep.olean') if (dep/'.lake/build/lib/lean/Dep.olean').exists() else None,
                         'Proof.olean':digest(root/'.lake/build/lib/lean/Proof.olean') if (root/'.lake/build/lib/lean/Proof.olean').exists() else None},
            'build':build,'batch':batch,'setup':setup,'wait':wait,'connect':conn,'positions':POSITIONS,'live':live,'stop':stop,'events':events}
    a.output.write_text(json.dumps(norm(result,work),indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'build':build['exit'],'batch':batch['exit'],'setup':setup['exit'],'server':stop['exit'],
                      'goals':{k:v['plain']['result'] for k,v in live.items()}},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
