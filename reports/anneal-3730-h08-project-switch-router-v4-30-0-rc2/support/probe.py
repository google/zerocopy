#!/usr/bin/env python3
"""A→B→A synthetic project router over two real, private Lean servers."""
import hashlib
import json
import os
import re
import select
import shutil
import signal
import subprocess
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
WORK=ROOT/'work'
LEAN=Path(os.environ['LEAN_BIN']).resolve()
EVENTS=[]
START=time.monotonic()

def log(kind, **values): EVENTS.append({'kind':kind,'seconds':round(time.monotonic()-START,4),**values})
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def process_rows():
    text=subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],text=True)
    rows=[]
    for line in text.splitlines():
        parts=line.split(maxsplit=4)
        if len(parts)==5 and all(part.isdigit() for part in parts[:4]):
            rows.append({'pid':int(parts[0]),'ppid':int(parts[1]),'pgid':int(parts[2]),
                         'rss_bytes':int(parts[3])*1024,'command':parts[4]})
    return rows
def processes(root_pid):
    rows=process_rows();selected={root_pid}
    changed=True
    while changed:
        old=len(selected)
        selected.update(row['pid'] for row in rows if row['ppid'] in selected)
        changed=len(selected)!=old
    return [row for row in rows if row['pid'] in selected]
def free_memory():
    text=subprocess.check_output(['memory_pressure','-Q'],text=True,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',text)
    return int(m[1]) if m else None

class Server:
    def __init__(self, label, directory):
        self.label=label;self.directory=directory;self.buffer=b'';self.seq=0;self.diag={}
        self.uri=(directory/'Proof.lean').as_uri()
        self.process=subprocess.Popen([str(LEAN),'--server'],cwd=directory,
            env=dict(os.environ,LEAN_PATH=str(directory),LEAN_NUM_THREADS='1'),
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            bufsize=0,start_new_session=True)
        log('server_start',project=label,pid=self.process.pid)
        t=time.monotonic()
        self.request('initialize',{'processId':os.getpid(),'rootUri':directory.as_uri(),
            'capabilities':{},'initializationOptions':{'hasWidgets':False}})
        self.initialize_ms=round((time.monotonic()-t)*1000,2)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        self.process.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw)
        self.process.stdin.flush();log('client_message',project=self.label,message=msg)
    def receive(self,predicate,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            while b'\r\n\r\n' in self.buffer:
                head,body=self.buffer.split(b'\r\n\r\n',1)
                lengths=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if not lengths or len(body)<lengths[0]:break
                raw,self.buffer=body[:lengths[0]],body[lengths[0]:]
                msg=json.loads(raw);log('server_message',project=self.label,message=msg)
                if msg.get('method')=='textDocument/publishDiagnostics':
                    p=msg['params'];self.diag[p.get('version')]=p['diagnostics']
                if 'method' in msg and 'id' in msg:self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                if predicate(msg):return msg
            ready,_,_=select.select([self.process.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                chunk=os.read(self.process.stdout.fileno(),65536)
                if not chunk:raise RuntimeError('server stdout closed')
                self.buffer+=chunk
        raise TimeoutError((self.label,'LSP response'))
    def request(self,method,params):
        self.seq+=1;rid=self.seq
        self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.receive(lambda m:'method' not in m and m.get('id')==rid)
    def await_diagnostics(self,version):
        t=time.monotonic();barrier=self.request('textDocument/waitForDiagnostics',{'uri':self.uri,'version':version})
        if version not in self.diag:
            self.receive(lambda m:m.get('method')=='textDocument/publishDiagnostics'
                         and m['params'].get('version')==version)
        return {'barrier':barrier,'diagnostics':self.diag[version],
                'wait_ms':round((time.monotonic()-t)*1000,2)}
    def open(self,source):
        self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{
            'uri':self.uri,'languageId':'lean','version':1,'text':source}}})
        return self.await_diagnostics(1)
    def change(self,source):
        self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{
            'textDocument':{'uri':self.uri,'version':2},'contentChanges':[{'text':source}]}})
        return self.await_diagnostics(2)
    def goal(self,version):
        return self.request('$/lean/plainGoal',{'textDocument':{'uri':self.uri,'version':version},
            'position':{'line':3,'character':5}})
    def stop(self):
        before=processes(self.process.pid)
        tracked={row['pid'] for row in before}
        if self.process.poll() is None:
            try:
                self.request('shutdown',None)
                self.send({'jsonrpc':'2.0','method':'exit'})
                self.process.wait(timeout=5)
            except Exception as exc:
                log('forced_stop',project=self.label,error=repr(exc))
                os.killpg(self.process.pid,signal.SIGKILL);self.process.wait(timeout=5)
        time.sleep(.1)
        result={'pid':self.process.pid,'returncode':self.process.returncode,
                'processes_before':before,
                'tracked_pids_after':[row for row in process_rows() if row['pid'] in tracked],
                'stderr':self.process.stderr.read().decode(errors='replace')}
        log('server_stop',project=self.label,**result)
        return result

def source(value):
    return (f'import Dep\n#eval selected\ntheorem expected : selected = {value} := by\n'
            '  rfl\ntheorem pending : True := by\n  trivial\n')

def build_project(label,value):
    folder=WORK/label;folder.mkdir()
    (folder/'Dep.lean').write_text(f'def selected : Nat := {value}\n')
    (folder/'Proof.lean').write_text(source(value))
    result=subprocess.run([str(LEAN),'-o','Dep.olean','Dep.lean'],cwd=folder,
        env=dict(os.environ,LEAN_NUM_THREADS='1'),capture_output=True,text=True,timeout=20)
    assert result.returncode==0,(label,result.stderr)
    row={'value':value,'dependency_source_sha256':sha(folder/'Dep.lean'),
         'dependency_artifact_sha256':sha(folder/'Dep.olean'),
         'proof_source_sha256':sha(folder/'Proof.lean'),
         'build_returncode':result.returncode,'build_stdout':result.stdout,'build_stderr':result.stderr}
    log('build_project',project=label,**row)
    return folder,row

def main():
    assert not WORK.exists(),'copy package or remove only support/work before replay'
    pre={'free_memory_percent':free_memory(),'disk_free_bytes':shutil.disk_usage(ROOT).free}
    assert pre['free_memory_percent'] is not None and pre['free_memory_percent']>=25
    assert pre['disk_free_bytes']>=5*1024**3
    WORK.mkdir()
    a,ab=build_project('A',11);b,bb=build_project('B',22)
    servers=[];route=[]
    def switch(label,server,reused):
        item={'project':label,'pid':server.process.pid,'reused':reused}
        route.append(item);log('switch',**item)
    try:
        first=Server('A',a);servers.append(first);switch('A',first,False)
        opened_a=first.open(source(11));initial_goal=first.goal(1)
        edited=source(11).replace('selected = 11','selected = 99')
        edited_a=first.change(edited);edited_goal=first.goal(2)
        second=Server('B',b);servers.append(second);switch('B',second,False)
        opened_b=second.open(source(22));goal_b=second.goal(1)
        two_server_rows={'A':processes(first.process.pid),'B':processes(second.process.pid)}
        assert sum(r['rss_bytes'] for rows in two_server_rows.values() for r in rows)<1800*1024**2
        switch('A',first,True)
        resumed_a=first.await_diagnostics(2);resumed_goal=first.goal(2)
        first_stop=first.stop()
        cold=Server('A-restarted',a);servers.append(cold);switch('A',cold,False)
        reopened_a=cold.open((a/'Proof.lean').read_text());cold_goal=cold.goal(1)
        switch('B',second,True)
        resumed_b=second.await_diagnostics(1);resumed_b_goal=second.goal(1)
        result={'preflight':pre,'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
            'lean_sha256':sha(LEAN),'projects':{'A':ab,'B':bb},'route':route,
            'A_initial':{'pid':first.process.pid,'initialize_ms':first.initialize_ms,
                'open':opened_a,'goal':initial_goal},
            'A_unsaved':{'buffer_sha256':hashlib.sha256(edited.encode()).hexdigest(),
                'disk_sha256':sha(a/'Proof.lean'),'edit':edited_a,'goal':edited_goal},
            'B_initial':{'pid':second.process.pid,'initialize_ms':second.initialize_ms,
                'open':opened_b,'goal':goal_b},
            'two_server_processes':two_server_rows,
            'A_resumed':{'pid':first.process.pid,'wait':resumed_a,'goal':resumed_goal},
            'A_first_stop':first_stop,
            'A_cold':{'pid':cold.process.pid,'initialize_ms':cold.initialize_ms,
                'open':reopened_a,'goal':cold_goal},
            'B_resumed':{'pid':second.process.pid,'wait':resumed_b,'goal':resumed_b_goal}}
    finally:
        stops=[]
        for server in servers:
            if server.process.poll() is None:stops.append(server.stop())
        if 'result' in locals():result['final_stops']=stops
    assert result['A_unsaved']['buffer_sha256']!=result['A_unsaved']['disk_sha256']
    assert result['A_first_stop']['tracked_pids_after']==[]
    assert all(stop['tracked_pids_after']==[] and stop['returncode']==0 for stop in result['final_stops'])
    result['events']=EVENTS
    raw=json.dumps(result,indent=2,ensure_ascii=False)
    raw=raw.replace(str(WORK),'$WORK').replace(str(LEAN),'$LEAN_BIN')
    (ROOT/'results.json').write_text(raw+'\n')
    print(json.dumps({'route':route,'A_unsaved_diagnostics':len(edited_a['diagnostics']),
        'A_resumed_diagnostics':len(resumed_a['diagnostics']),
        'A_cold_diagnostics':len(reopened_a['diagnostics']),
        'B_diagnostics':len(opened_b['diagnostics'])},indent=2))

if __name__=='__main__':main()
