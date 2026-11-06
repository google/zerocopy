#!/usr/bin/env python3
"""Direct Lean LSP plus an explicitly local, MCP-shaped two-client broker model."""
from __future__ import annotations

import hashlib
import json
import os
import platform
import select
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUT=HERE/'results.json'
LEAN=Path(os.environ['LEAN_BIN']).resolve()
SCRATCH=Path(os.environ.get('ANNEAL_PROBE_SCRATCH',tempfile.gettempdir()))
GOOD_HOST='//% theorem demo : True := by\n//%   trivial\n'
BAD_HOST='//% theorem demo : False := by\n//%   exact ?_\n'
SLOW='''import Lean

theorem slow : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  trivial
'''

def digest(v):return hashlib.sha256(v if isinstance(v,bytes) else v.encode()).hexdigest()
def project(host):
    lines=host.splitlines(keepends=True)
    assert lines and all(x.startswith('//% ') for x in lines)
    return ''.join(x[4:] for x in lines)

class Wire:
    def __init__(self,root,label,events,encodings=None):
        self.root=root;self.label=label;self.events=events;self.buf=b'';self.nextid=10
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,
            env=dict(os.environ,LEAN_NUM_THREADS='1'),stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        self.log('start',pid=self.p.pid)
        caps={'general':{'positionEncodings':encodings or ['utf-16']},
              'textDocument':{'synchronization':{'didSave':True,'dynamicRegistration':False}}}
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{
            'processId':os.getpid(),'rootUri':root.as_uri(),'capabilities':caps,
            'initializationOptions':{'hasWidgets':False}}})
        self.initialize=self.until(lambda m:m.get('id')==1)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def log(self,kind,**x):self.events.append({'seq':len(self.events),'server':self.label,'kind':kind,**x})
    def send(self,message):
        data=json.dumps(message,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(data)).encode()+b'\r\n\r\n'+data)
        self.p.stdin.flush();self.log('send',message=message)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                head,body=self.buf.split(b'\r\n\r\n',1)
                lengths=[int(x.split(b':',1)[1]) for x in head.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if lengths and len(body)>=lengths[0]:
                    raw,self.buf=body[:lengths[0]],body[lengths[0]:]
                    value=json.loads(raw);self.log('recv',message=value)
                    if value.get('method')=='client/registerCapability' and 'id' in value:
                        self.send({'jsonrpc':'2.0','id':value['id'],'result':None})
                    return value
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                new=os.read(self.p.stdout.fileno(),65536)
                if not new:break
                self.buf+=new
        raise TimeoutError('read '+self.label)
    def until(self,predicate,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            value=self.read(max(.1,end-time.monotonic()))
            if predicate(value):return value
        raise TimeoutError('until '+self.label)
    def request(self,method,params):
        rid=self.nextid;self.nextid+=1
        self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':params})
        return self.until(lambda m:m.get('id')==rid)
    def open(self,path,text,version):
        self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{
            'textDocument':{'uri':path.as_uri(),'languageId':'lean','version':version,'text':text}}})
    def change(self,path,text,version):
        self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{
            'textDocument':{'uri':path.as_uri(),'version':version},'contentChanges':[{'text':text}]}})
    def close(self,path):
        self.send({'jsonrpc':'2.0','method':'textDocument/didClose','params':{'textDocument':{'uri':path.as_uri()}}})
    def wait(self,path,version):
        return self.request('textDocument/waitForDiagnostics',{'uri':path.as_uri(),'version':version})
    def goal(self,path):
        return self.request('$/lean/plainGoal',{'textDocument':{'uri':path.as_uri()},
                                             'position':{'line':1,'character':9}})
    def stop(self):
        if self.p.poll() is not None:return
        try:
            self.request('shutdown',None)
            self.send({'jsonrpc':'2.0','method':'exit'})
            self.p.wait(timeout=5)
        except Exception as exc:
            self.log('shutdown_error',error=repr(exc));self.p.kill();self.p.wait(timeout=5)
        self.log('exit',returncode=self.p.returncode,stderr=self.p.stderr.read().decode(errors='replace')[-1000:])

class Broker:
    """Local model: one authority and two logical clients, not an MCP transport."""
    def __init__(self,root,wire,events):
        self.root=root;self.wire=wire;self.events=events
        self.host=root/'Host.rs';self.hidden=root/'Hidden.lean'
        self.host_text='';self.version=0;self.lsp_version=0;self.incarnation=1
        self.document_epoch=0
        self.opened=False;self.dedup={};self.subscribers={}
    def event(self,kind,**x):self.events.append({'seq':len(self.events),'server':'broker','kind':kind,**x})
    def negotiate(self,client,wants_subscription):
        caps={'protocolVersion':'2026-07-28','subscription':bool(wants_subscription),
              'poll':True,'edit':client=='agent' or client=='editor'}
        self.subscribers[client]={'supports':bool(wants_subscription),'received':[],
                                  'drop_next':False}
        self.event('capabilities',client=client,result=caps)
        return caps
    def subscribe(self,client):
        state=self.subscribers[client]
        result={'status':'subscribed' if state['supports'] else 'unsupported-use-poll'}
        self.event('subscribe',client=client,result=result)
        return result
    def notify(self,kind):
        event={'kind':kind,'version':self.version,'source_sha256':digest(self.host_text),
               'incarnation':self.incarnation,'document_epoch':self.document_epoch}
        for client,state in self.subscribers.items():
            if not state['supports']:continue
            if state['drop_next']:
                state['drop_next']=False;self.event('drop_notification',client=client,event=event)
            else:state['received'].append(event);self.event('notification',client=client,event=event)
    def poll(self,client):
        result={'status':'current' if self.opened else 'closed',
                'host_uri':self.host.as_uri(),'hidden_uri':self.hidden.as_uri(),
                'version':self.version,'source_sha256':digest(self.host_text),
                'projection_sha256':digest(project(self.host_text)) if self.opened else None,
                'lsp_version':self.lsp_version,'incarnation':self.incarnation,
                'document_epoch':self.document_epoch}
        self.event('poll',client=client,result=result)
        return result
    def open_host(self,host_text):
        self.host_text=host_text;self.version=1;self.lsp_version=1;self.opened=True
        self.document_epoch+=1
        self.wire.open(self.hidden,project(host_text),self.lsp_version)
        self.wire.wait(self.hidden,self.lsp_version)
        self.notify('generation-changed')
    def cas_edit(self,client,request_id,expected_epoch,expected_version,expected_sha,new_text):
        key=(client,request_id)
        payload={'expected_epoch':expected_epoch,'expected_version':expected_version,
                 'expected_sha':expected_sha,'new_sha':digest(new_text)}
        if key in self.dedup:
            old_payload,old_result=self.dedup[key]
            result=old_result if old_payload==payload else {'status':'id-reuse-conflict'}
            self.event('retry',client=client,request_id=request_id,result=result)
            return result
        if not self.opened:result={'status':'closed'}
        elif expected_epoch!=self.document_epoch or expected_version!=self.version or expected_sha!=digest(self.host_text):
            result={'status':'conflict','current_version':self.version,
                    'current_sha256':digest(self.host_text),'current_document_epoch':self.document_epoch}
        else:
            self.version+=1;self.lsp_version+=1;self.host_text=new_text
            self.wire.change(self.hidden,project(new_text),self.lsp_version)
            self.wire.wait(self.hidden,self.lsp_version)
            result={'status':'applied','version':self.version,'source_sha256':digest(new_text)}
            self.notify('generation-changed')
        self.dedup[key]=(payload,result)
        self.event('edit',client=client,request_id=request_id,result=result)
        return result
    def goal(self,client):
        if not self.opened:return {'status':'closed'}
        raw=self.wire.goal(self.hidden)
        result={'client':client,'version':self.version,'incarnation':self.incarnation,
                'document_epoch':self.document_epoch,
                'source_sha256':digest(self.host_text),'lean_response':raw}
        self.event('goal',client=client,result=result)
        return result
    def dual_goals(self):
        ids={'editor':80,'agent':81}
        for client,rid in ids.items():
            self.wire.send({'jsonrpc':'2.0','id':rid,'method':'$/lean/plainGoal',
                            'params':{'textDocument':{'uri':self.hidden.as_uri()},
                                      'position':{'line':1,'character':9}}})
        got={}
        while len(got)<2:
            message=self.wire.read()
            if message.get('id') in ids.values():
                client=next(c for c,n in ids.items() if n==message['id'])
                got[client]=message
        self.event('dual_goals',logical_request_ids={'editor':1,'agent':1},
                   wire_request_ids=ids,responses=got)
        return got
    def restart_lean(self):
        self.wire.p.kill();self.wire.p.wait(timeout=5)
        self.event('lean_killed',old_incarnation=self.incarnation)
        self.incarnation+=1
        self.wire=Wire(self.root,'restarted',self.events)
        self.lsp_version=1
        self.wire.open(self.hidden,project(self.host_text),1)
        self.wire.wait(self.hidden,1)
        self.notify('worker-restarted')
    def save(self):
        self.host.write_text(self.host_text)
        self.event('host_saved',path=self.host.as_uri(),source_sha256=digest(self.host_text))
    def rename(self):
        self.wire.close(self.hidden)
        old_host=self.host;self.host=self.root/'Renamed.rs';self.hidden=self.root/'RenamedHidden.lean'
        self.document_epoch+=1
        if old_host.exists():old_host.rename(self.host)
        self.lsp_version=1
        self.wire.open(self.hidden,project(self.host_text),1)
        self.wire.wait(self.hidden,1)
        self.event('host_renamed',old=old_host.as_uri(),new=self.host.as_uri())
    def close(self):
        self.wire.close(self.hidden);self.opened=False
        self.event('host_closed',version=self.version)
    def reopen_from_disk(self):
        self.open_host(self.host.read_text())
        self.event('reopen_from_disk',disk_sha256=digest(self.host_text))

def cancellation_probe(root,events):
    slow=root/'Slow.lean';slow.write_text(SLOW)
    (root/'gate.release').unlink(missing_ok=True)
    (root/'gate.entered').unlink(missing_ok=True)
    w=Wire(root,'cancel',events)
    try:
        w.open(slow,SLOW,1)
        w.send({'jsonrpc':'2.0','id':200,'method':'textDocument/waitForDiagnostics',
                'params':{'uri':slow.as_uri(),'version':1}})
        deadline=time.monotonic()+15
        while not (root/'gate.entered').exists() and time.monotonic()<deadline:time.sleep(.01)
        if not (root/'gate.entered').exists():raise TimeoutError('gate not entered')
        w.send({'jsonrpc':'2.0','id':201,'method':'$/lean/plainGoal',
                'params':{'textDocument':{'uri':slow.as_uri()},'position':{'line':7,'character':9}}})
        w.send({'jsonrpc':'2.0','method':'$/cancelRequest','params':{'id':201}})
        (root/'gate.release').write_text('go\n')
        seen={}
        deadline=time.monotonic()+20
        while len(seen)<2 and time.monotonic()<deadline:
            m=w.read(max(.1,deadline-time.monotonic()))
            if m.get('id') in (200,201):seen[m['id']]=m
        assert len(seen)==2
        return seen
    finally:w.stop()

def encoding_probe(root,events):
    file=root/'Encoding.lean'
    text='theorem enc : True := by\n  trivial\n'
    w=Wire(root,'utf8-offered',events,encodings=['utf-8'])
    try:
        w.open(file,text,1)
        wait=w.wait(file,1)
        goal=w.goal(file)
        return {'offered':['utf-8'],'server_capabilities':w.initialize.get('result',{}).get('capabilities',{}),
                'wait':wait,'goal':goal}
    finally:w.stop()

def main():
    assert SCRATCH.is_dir()
    events=[]
    with tempfile.TemporaryDirectory(prefix='lean-two-client-',dir=SCRATCH) as t:
        root=Path(t)
        host=root/'Host.rs';hidden=root/'Hidden.lean'
        host.write_text(BAD_HOST);hidden.write_text(project(BAD_HOST))
        batch=subprocess.run([str(LEAN),'--json',str(hidden)],cwd=root,capture_output=True,text=True,timeout=20)
        w=Wire(root,'initial',events)
        broker=Broker(root,w,events)
        try:
            cap_editor=broker.negotiate('editor',True)
            cap_agent=broker.negotiate('agent',False)
            assert broker.subscribe('editor')['status']=='subscribed'
            assert broker.subscribe('agent')['status']=='unsupported-use-poll'
            broker.open_host(GOOD_HOST)
            initial=broker.poll('agent')
            goal_good=broker.goal('agent')
            dual=broker.dual_goals()
            assert dual['editor'].get('result')==dual['agent'].get('result')
            # A live editor edit occurs after the agent captured the source hash.
            broker.subscribers['editor']['drop_next']=True
            edit=broker.cas_edit('editor','edit-1',initial['document_epoch'],initial['version'],initial['source_sha256'],BAD_HOST)
            assert edit['status']=='applied'
            stale=broker.cas_edit('agent','agent-old',initial['document_epoch'],initial['version'],initial['source_sha256'],GOOD_HOST)
            assert stale['status']=='conflict'
            missed=broker.subscribers['editor']['received'][-1]
            reconciled=broker.poll('editor')
            assert missed['version']==1 and reconciled['version']==2
            # Model a lost mutation response and retry the same logical ID.
            retry=broker.cas_edit('editor','edit-1',initial['document_epoch'],initial['version'],initial['source_sha256'],BAD_HOST)
            conflict_id=broker.cas_edit('editor','edit-1',initial['document_epoch'],initial['version'],initial['source_sha256'],GOOD_HOST)
            assert retry==edit and conflict_id['status']=='id-reuse-conflict'
            assert broker.version==2
            goal_bad=broker.goal('agent')
            agent_current=broker.poll('agent')
            agent_applied=broker.cas_edit('agent','agent-fresh',agent_current['document_epoch'],agent_current['version'],
                                          agent_current['source_sha256'],GOOD_HOST)
            assert agent_applied['status']=='applied'
            goal_good_from_editor=broker.goal('editor')
            editor_current=broker.poll('editor')
            editor_restored=broker.cas_edit('editor','edit-restore',editor_current['document_epoch'],editor_current['version'],
                                            editor_current['source_sha256'],BAD_HOST)
            assert editor_restored['status']=='applied'
            assert digest(host.read_bytes())==digest(BAD_HOST)
            broker.restart_lean()
            after_restart=broker.goal('agent')
            assert after_restart['source_sha256']==goal_bad['source_sha256']
            assert after_restart['incarnation']==2
            broker.save();broker.rename()
            after_rename=broker.goal('agent')
            broker.close();closed=broker.goal('agent')
            assert closed['status']=='closed'
            broker.reopen_from_disk();reopened=broker.goal('agent')
            assert reopened['source_sha256']==digest(BAD_HOST)
            old_session=broker.poll('agent')
            broker.close();broker.reopen_from_disk()
            aba_reopen=broker.cas_edit('agent','old-epoch',old_session['document_epoch'],
                                        old_session['version'],old_session['source_sha256'],GOOD_HOST)
            assert aba_reopen['status']=='conflict' and broker.version==1
            summary={'lean_binary_sha256':digest(LEAN.read_bytes()),
                     'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
                     'good_host_sha256':digest(GOOD_HOST),'bad_host_sha256':digest(BAD_HOST),
                     'disk_batch_exit':batch.returncode,
                     'capabilities':{'editor':cap_editor,'agent':cap_agent},
                     'initial':initial,'goal_good':goal_good,'dual_equal':True,
                     'edit':edit,'stale_edit':stale,'missed_event':missed,
                     'reconciled':reconciled,'retry':retry,'id_reuse_conflict':conflict_id,
                     'goal_bad':goal_bad,'after_restart':after_restart,
                     'agent_applied':agent_applied,'goal_good_from_editor':goal_good_from_editor,
                     'editor_restored':editor_restored,
                     'after_rename':after_rename,'closed':closed,'reopened':reopened,
                     'same_text_reopen_old_epoch':aba_reopen,
                     'disk_hidden_sha256':digest(hidden.read_bytes())}
        finally:
            broker.wire.stop()
        cancelled=cancellation_probe(root,events)
        summary['cancellation']={'wait':cancelled[200],'goal':cancelled[201]}
        summary['utf8_offer']=encoding_probe(root,events)
    result={'host':{'system':platform.platform(),'machine':platform.machine(),
                    'python':platform.python_version()},
            'summary':summary,'events':events}
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    raw=raw.replace(str(root),'$WORK').replace(str(LEAN),'$LEAN_BIN')
    OUT.write_text(raw)
    print(json.dumps({'disk_batch_exit':summary['disk_batch_exit'],
                      'cas':edit['status'],'stale':stale['status'],
                      'retry':retry['status'],'reconciled_version':reconciled['version'],
                      'cancel_response':cancelled[201].get('error',{}).get('code')}))

if __name__=='__main__':main()
