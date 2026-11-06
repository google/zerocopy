#!/usr/bin/env python3
"""Small offline Lake artifact-cache consumer ablation, Lean 4.30.0-rc2."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import signal
import subprocess
import time

BIN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE = BIN / 'lake'
LEAN = BIN / 'lean'
PROFILE = '(version 1) (allow default) (deny network*)'
TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def files(root):
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*')) if p.is_file()}

def memory_free_percent():
    s = subprocess.check_output(['vm_stat'], text=True)
    page = int(re.search(r'page size of (\d+) bytes', s).group(1))
    count = 0
    for label in ('Pages free', 'Pages inactive', 'Pages speculative', 'Pages purgeable'):
        count += int(re.search(rf'^{label}:\s+(\d+)', s, re.M).group(1))
    total = int(subprocess.check_output(['sysctl', '-n', 'hw.memsize'], text=True))
    return round(100 * count * page / total, 2)

def fixture(root):
    dep, consumer = root/'producer', root/'consumer'
    dep.mkdir(parents=True); consumer.mkdir()
    (dep/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
    (dep/'Dep.lean').write_text('def depValue : Nat := 7\n')
    (dep/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    (consumer/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
    (consumer/'Generated.lean').write_text('import Dep\ntheorem generatedEq : depValue + 1 = 8 := by\n  trace_state\n  decide\n#print axioms generatedEq\n#eval depValue + 1\n')
    (consumer/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    manifest = {'version':'1.2.0','packagesDir':'.lake/packages','packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json','inherited':False,'dir':'../producer','configFile':'lakefile.lean'}],'name':'probe_consumer','lakeDir':'.lake','fixedToolchain':False}
    (consumer/'lake-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return dep, consumer

def env_for(work, cache, artifact):
    e = dict(os.environ)
    e.update(HOME=str(work/'home'), XDG_CACHE_HOME=str(work/'xdg'), ELAN_TOOLCHAIN=TOOLCHAIN,
             LEAN_NUM_THREADS='1', LAKE_NO_NET='1', LAKE_CACHE_DIR=str(cache),
             PATH=str(BIN)+os.pathsep+e.get('PATH',''))
    e.pop('LAKE_ARTIFACT_CACHE',None)
    if artifact is not None: e['LAKE_ARTIFACT_CACHE'] = 'true' if artifact else 'false'
    return e

def call(records, label, cwd, args, env, work, timeout=35):
    start=time.monotonic()
    cmd=['/usr/bin/sandbox-exec','-p',PROFILE,str(LAKE),'--keep-toolchain',*args]
    try:
        p=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
        code,out,err=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as x:
        code='timeout';out=x.stdout or '';err=x.stderr or ''
        if isinstance(out,bytes):out=out.decode(errors='replace')
        if isinstance(err,bytes):err=err.decode(errors='replace')
    norm=lambda s:s.replace(str(work),'$WORK').replace(str(BIN.parent),'$TOOLCHAIN')
    rec={'label':label,'command':[norm(x) for x in cmd],'cwd':norm(str(cwd)),
         'exit':code,'seconds':round(time.monotonic()-start,3),
         'stdout':norm(out),'stderr':norm(err)}
    records.append(rec)
    return rec

class Server:
    def __init__(self, root, env):
        self.p=subprocess.Popen(['/usr/bin/sandbox-exec','-p',PROFILE,str(LAKE),'--keep-toolchain','--no-cache','serve'],cwd=root,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,bufsize=0)
        self.buf=b'';self.id=0;self.messages=[]
        self.request('initialize',{'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}},20)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,msg):
        b=json.dumps(msg,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush()
        self.messages.append({'direction':'client','message':msg})
    def receive(self,rid,timeout):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            while b'\r\n\r\n' in self.buf:
                h,b=self.buf.split(b'\r\n\r\n',1)
                n=int(re.search(rb'Content-Length:\s*(\d+)',h,re.I).group(1))
                if len(b)<n:break
                msg=json.loads(b[:n]);self.buf=b[n:]
                self.messages.append({'direction':'server','message':msg})
                if 'method' in msg and 'id' in msg:self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if 'method' not in msg and msg.get('id')==rid:return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                part=os.read(self.p.stdout.fileno(),65536)
                if not part:raise RuntimeError('server closed')
                self.buf+=part
        raise TimeoutError('server response')
    def request(self,method,params,timeout=35):
        self.id+=1;rid=self.id
        self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.receive(rid,timeout)
    def stop(self):
        try:
            if self.p.poll() is None:
                self.request('shutdown',None,6)
                self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=6)
        except Exception:
            os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        return {'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}

def goal(records,label,consumer,env,work):
    start=time.monotonic();s=None
    try:
        s=Server(consumer,env)
        uri=(consumer/'Generated.lean').as_uri()
        source=(consumer/'Generated.lean').read_text()
        s.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':source}}})
        wait=s.request('textDocument/waitForDiagnostics',{'uri':uri,'version':1},35)
        answer=s.request('$/lean/plainGoal',{'textDocument':{'uri':uri,'version':1},'position':{'line':2,'character':3}},35)
        code=0;err=''
    except Exception as x:
        wait=None;answer=None;code=1;err=repr(x)
    finally:
        stop=s.stop() if s else None
    notices=[]
    if s:
        for item in s.messages:
            m=item['message']
            if item['direction']=='server' and m.get('method') in ('textDocument/publishDiagnostics','$/lean/fileProgress'):
                notices.append(m)
    rec={'label':label,'exit':code,'seconds':round(time.monotonic()-start,3),'wait':wait,'goal':answer,'error':err,'stop':stop,
         'notifications':json.loads(json.dumps(notices).replace(str(work),'$WORK').replace(str(BIN.parent),'$TOOLCHAIN'))}
    records.append(rec)
    return rec

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();work=a.work.resolve()
    if work.exists():raise SystemExit('work path must be absent')
    disk=shutil.disk_usage(work.parent).free;mem=memory_free_percent()
    if disk<10*1024**3 or mem<20:raise SystemExit(f'preflight denied: disk={disk} memory_free_percent={mem}')
    if not (LAKE.is_file() and LEAN.is_file()):raise SystemExit('pinned local toolchain absent')
    work.mkdir();(work/'home').mkdir();(work/'xdg').mkdir()
    result={'preflight':{'disk_free_bytes':disk,'memory_free_percent':mem},
            'tools':{'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN)},'runs':[],'cells':{}}
    records=result['runs']; clean=work/'clean';dep,consumer=fixture(clean)
    clean_env=env_for(work,work/'clean-cache',False)
    call(records,'clean-build',consumer,['-v','build','Generated'],clean_env,work)
    call(records,'clean-batch',consumer,['--no-cache','env','lean','--json','Generated.lean'],clean_env,work)
    goal(records,'clean-first-goal',consumer,clean_env,work)
    result['clean']={'producer':files(dep),'consumer':files(consumer)}
    seed=work/'seed'; seed_dep,seed_consumer=fixture(seed)
    seed_cache=work/'seed-cache'; seed_env=env_for(work,seed_cache,True)
    call(records,'seed-build',seed_consumer,['-v','build','Generated'],seed_env,work)
    result['seed']={'cache':files(seed_cache),'producer':files(seed_dep)}
    # Every cell is a new consumer and private producer copy, with the same read-only seed cache.
    for name in ('fresh_full','no_source','no_trace','no_hash','no_setup','no_config'):
        cell=work/name;shutil.copytree(seed,cell)
        d,c=cell/'producer',cell/'consumer'
        shutil.rmtree(c/'.lake',ignore_errors=True)
        removed=[]
        if name=='fresh_full':
            shutil.rmtree(d/'.lake/build',ignore_errors=True);removed=['.lake/build/']
        elif name=='no_source':
            (d/'Dep.lean').unlink();removed=['Dep.lean']
        elif name=='no_trace':
            for p in d.rglob('*.trace'):p.unlink();removed.append(str(p.relative_to(d)))
        elif name=='no_hash':
            for p in d.rglob('*.hash'):p.unlink();removed.append(str(p.relative_to(d)))
        elif name=='no_setup':
            for p in d.rglob('*.setup.json'):p.unlink();removed.append(str(p.relative_to(d)))
        elif name=='no_config':
            shutil.rmtree(d/'.lake/config',ignore_errors=True);removed=['.lake/config/']
        before=files(d);cache_before=files(seed_cache)
        e=env_for(work,seed_cache,None)
        build=call(records,name+'-no-build',c,['-v','--no-build','build','Generated'],e,work)
        batch=call(records,name+'-batch',c,['--no-cache','env','lean','--json','Generated.lean'],e,work)
        first=goal(records,name+'-first-goal',c,e,work)
        result['cells'][name]={'removed':removed,'before':before,'after':files(d),'cache_unchanged':cache_before==files(seed_cache),
                                'build_exit':build['exit'],'batch_exit':batch['exit'],'goal_exit':first['exit'] if first else None}
        a.output.write_text(json.dumps(result,indent=2)+'\n')
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:{q:v[q] for q in ('build_exit','batch_exit','goal_exit','cache_unchanged')} for k,v in result['cells'].items()},indent=2))

if __name__=='__main__':main()
