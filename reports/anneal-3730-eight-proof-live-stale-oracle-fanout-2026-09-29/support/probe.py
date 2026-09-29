#!/usr/bin/env python3
"""Eight-proof Model→Helper batch oracle versus two-worker live stale-import waves."""
import hashlib
import json
import os
import re
import select
import shutil
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
WORK=ROOT/'work'
ARTIFACTS=ROOT/'artifacts'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LAKE=LEAN.with_name('lake')
PIN='leanprover/lean4:v4.30.0-rc2'
ENV=dict(os.environ,ELAN_TOOLCHAIN=PIN,LEAN_NUM_THREADS='1',LAKE_ARTIFACT_CACHE='false',LAKE_NO_NET='1')
ENV['PATH']=str(LEAN.parent)+os.pathsep+ENV.get('PATH','')
START=time.monotonic();EVENTS=[];RESULT={'schema':1,'waves':[],'batch':[]}
CAP=3_758_096_384 # 3.5 GiB summed process-tree RSS, conservative accounting

def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def put(path,text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
def run(label,argv,env=None,timeout=35):
    t=time.monotonic()
    p=subprocess.run([str(x) for x in argv],cwd=WORK,env=env or ENV,
        capture_output=True,text=True,timeout=timeout)
    rec=dict(label=label,argv=[str(x) for x in argv],rc=p.returncode,stdout=p.stdout,
        stderr=p.stderr,elapsed_ms=round((time.monotonic()-t)*1000,1))
    log('command',**rec);return rec
def tree(root):
    p=subprocess.run(['ps','-axo','pid=,ppid=,rss=,comm='],capture_output=True,text=True,timeout=4)
    rows={}
    for line in p.stdout.splitlines():
        xs=line.split(maxsplit=3)
        if len(xs)!=4:continue
        try:pid,ppid,rss=map(int,xs[:3])
        except ValueError:continue
        rows[pid]=dict(pid=pid,ppid=ppid,rss_bytes=rss*1024,comm=xs[3])
    seen={root}
    while True:
        add={pid for pid,row in rows.items() if row['ppid'] in seen}
        if add<=seen:break
        seen|=add
    found=[rows[pid] for pid in sorted(seen) if pid in rows]
    result={'count':len(found),'rss_bytes':sum(x['rss_bytes'] for x in found),'processes':found}
    assert result['rss_bytes']<CAP,result
    return result
def artifacts():
    return {name:sha(WORK/'.lake/build/lib/lean'/(name+'.olean')) for name in ('Model','Helper')}
def build(value,label):
    put(WORK/'Model.lean',f'def model : Nat := {value}\n')
    rec=run(label,[LAKE,'--keep-toolchain','--no-cache','build','Helper'],timeout=45)
    assert rec['rc']==0,(label,rec)
    found=artifacts()
    dest=ARTIFACTS/str(value);dest.mkdir(parents=True,exist_ok=True)
    for name in found:
        shutil.copyfile(WORK/'.lake/build/lib/lean'/(name+'.olean'),dest/(name+'.olean'))
    log('artifacts',label=label,value=value,sha256=found)
    return found
def proof(i):
    return f'import Helper\n#eval helper\ntheorem proof_{i} : helper = 8 := by\n  rfl\n'
def goal_pos():return {'line':3,'character':5}
def env_direct():return dict(ENV,LEAN_PATH=str(WORK/'.lake/build/lib/lean'))
def batch(label):
    for i in range(8):
        rec=run(f'{label}-{i}',[LEAN,'--json',f'Proof{i}.lean'],env_direct(),timeout=20)
        RESULT['batch'].append(dict(stage=label,proof=i,**rec))

class Server:
    def __init__(self,label,mode):
        self.label=label;self.mode=mode;self.buf=b'';self.n=10
        if mode=='direct':argv=[LEAN,'--server'];env=env_direct()
        else:argv=[LAKE,'--keep-toolchain','--no-cache','serve'];env=ENV
        self.p=subprocess.Popen([str(x) for x in argv],cwd=WORK,env=env,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        log('launch',label=label,mode=mode,argv=[str(x) for x in argv],pid=self.p.pid)
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{
            'processId':os.getpid(),'rootUri':WORK.as_uri(),'capabilities':{},
            'initializationOptions':{'hasWidgets':False}}})
        self.until(1,20)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw)
        self.p.stdin.flush();log('client',label=self.label,message=msg)
    def read(self,timeout=20):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            if b'\r\n\r\n' in self.buf:
                head,body=self.buf.split(b'\r\n\r\n',1)
                lens=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if lens and len(body)>=lens[0]:
                    raw,self.buf=body[:lens[0]],body[lens[0]:]
                    msg=json.loads(raw);log('server',label=self.label,message=msg)
                    if msg.get('method')=='client/registerCapability' and 'id' in msg:
                        self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buf+=chunk
        raise TimeoutError((self.label,'server read'))
    def until(self,rid,timeout=20):
        deadline=time.monotonic()+timeout
        while time.monotonic()<deadline:
            msg=self.read(max(.1,deadline-time.monotonic()))
            if msg.get('id')==rid:return msg
        raise TimeoutError((self.label,rid))
    def request(self,method,params,timeout=20):
        rid=self.n;self.n+=1
        self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.until(rid,timeout)
    def open(self,i):
        uri=(WORK/f'Proof{i}.lean').as_uri()
        self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{
            'textDocument':{'uri':uri,'languageId':'lean','version':1,'text':proof(i)}}})
        return self.wait(i,1)
    def wait(self,i,v):
        return self.request('textDocument/waitForDiagnostics',{'uri':(WORK/f'Proof{i}.lean').as_uri(),'version':v},25)
    def goal(self,i):
        return self.request('$/lean/plainGoal',{'textDocument':{'uri':(WORK/f'Proof{i}.lean').as_uri()},'position':goal_pos()})
    def change(self,i):
        uri=(WORK/f'Proof{i}.lean').as_uri()
        self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{
            'textDocument':{'uri':uri,'version':2},'contentChanges':[{'text':proof(i)}]}})
        return self.wait(i,2)
    def watched(self):
        self.send({'jsonrpc':'2.0','method':'workspace/didChangeWatchedFiles','params':{'changes':[
            {'uri':(WORK/f'{name}.lean').as_uri(),'type':2} for name in ('Model','Helper')]}})
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.send({'jsonrpc':'2.0','id':99,'method':'shutdown','params':None})
            self.until(99,6)
            self.send({'jsonrpc':'2.0','method':'exit'})
            self.p.wait(timeout=6)
        finally:
            if self.p.poll() is None:self.p.kill();self.p.wait()
            log('stop',label=self.label,rc=self.p.returncode,
                stderr=self.p.stderr.read().decode(errors='replace'))

def wave(index,mode,proofs):
    base=build(8,f'wave-{index}-base-build')
    old=Server(f'wave-{index}-old',mode)
    row={'index':index,'mode':mode,'proofs':proofs,'base_artifacts':base}
    try:
        row['base_waits']={str(i):old.open(i) for i in proofs}
        row['base_goals']={str(i):old.goal(i) for i in proofs}
        row['base_tree']=tree(old.p.pid)
        edited=build(7,f'wave-{index}-edited-build')
        row['edited_artifacts']=edited
        old.watched()
        row['old_waits']={str(i):old.change(i) for i in proofs}
        row['old_goals']={str(i):old.goal(i) for i in proofs}
        row['old_tree']=tree(old.p.pid)
    finally:old.stop()
    fresh=Server(f'wave-{index}-fresh',mode)
    try:
        row['fresh_waits']={str(i):fresh.open(i) for i in proofs}
        row['fresh_goals']={str(i):fresh.goal(i) for i in proofs}
        row['fresh_tree']=tree(fresh.p.pid)
    finally:fresh.stop()
    RESULT['waves'].append(row)
    log('wave',index=index,mode=mode,proofs=proofs)

def main():
    assert not WORK.exists() and not ARTIFACTS.exists(),'copy the package before rerunning'
    assert shutil.disk_usage(ROOT).free>3*1024**3
    version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
    assert '4.30.0-rc2' in version
    RESULT['tools']={'lean_version':version,'lean_sha256':sha(LEAN),
        'lake_version':subprocess.check_output([str(LAKE),'--version'],text=True).strip(),
        'lake_sha256':sha(LAKE),'rss_cap_bytes':CAP}
    WORK.mkdir()
    put(WORK/'lakefile.lean','import Lake\nopen Lake DSL\npackage fanout_probe\nlean_lib Model\nlean_lib Helper\n')
    put(WORK/'lean-toolchain',PIN+'\n')
    put(WORK/'Helper.lean','import Model\ndef helper : Nat := model\n')
    for i in range(8):put(WORK/f'Proof{i}.lean',proof(i))
    RESULT['sources']={p.name:sha(p) for p in sorted(WORK.glob('*.lean'))}
    RESULT['initial_artifacts']=build(8,'initial-base-build')
    batch('base')
    for i,mode in enumerate(('direct','direct','lake','lake')):
        wave(i,mode,[2*i,2*i+1])
        if i==0:batch('edited')
    RESULT['final_artifacts']=artifacts()
    RESULT['events']=EVENTS
    raw=json.dumps(RESULT,indent=2,ensure_ascii=False)+'\n'
    raw=raw.replace(WORK.as_uri(),'$WORK_URI').replace(str(WORK),'$WORK')
    raw=raw.replace(str(LEAN),'$LEAN').replace(str(LAKE),'$LAKE')
    (ROOT/'results.json').write_text(raw)
    print('completed four two-proof waves, eight base/edited batch oracles')

if __name__=='__main__':main()
