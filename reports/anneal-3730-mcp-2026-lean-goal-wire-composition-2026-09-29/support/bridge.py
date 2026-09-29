#!/usr/bin/env python3
"""Local 2026-07-28 MCP-shaped Tasks model backed by a real pinned Lean LSP goal."""
import hashlib,json,os,select,signal,subprocess,sys,threading,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
SOURCE=ROOT/'Proof.lean';SLOW=ROOT/'Slow.lean';VERSION='2026-07-28';EXT='io.modelcontextprotocol/tasks'
lock=threading.Lock();tasks={};counter=0;queries=[];active_queries=0
def sha(raw):return hashlib.sha256(raw).hexdigest()
def stamp():return datetime.now(timezone.utc).isoformat().replace('+00:00','Z')
def emit(obj):sys.stdout.write(json.dumps(obj,separators=(',',':'),ensure_ascii=False)+'\n');sys.stdout.flush()
def answer(req,result=None,error=None):emit({'jsonrpc':'2.0','id':req.get('id'),**({'result':result} if error is None else {'error':error})})
def err(code,message,data=None):return {'code':code,'message':message,**({'data':data} if data is not None else {})}
def meta(req):return (req.get('params') or {}).get('_meta') or {}
def process_rows():
    rows={}
    for line in subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],text=True).splitlines():
        f=line.split(maxsplit=4)
        if len(f)==5 and f[0].isdigit():rows[int(f[0])]={'pid':int(f[0]),'ppid':int(f[1]),'pgid':int(f[2]),'rss_kib':int(f[3]),'comm':f[4]}
    return rows
def descendants(root):
    rows=process_rows();ids={root}
    while True:
        more={pid for pid,r in rows.items() if r['ppid'] in ids}
        if more<=ids:break
        ids|=more
    return [rows[i] for i in sorted(ids) if i in rows]
class LeanLSP:
    def __init__(self):
        env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(ROOT))
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=ROOT,env=env,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        self.buf=b'';self.diag=[];self.write_lock=threading.Lock()
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),
          'rootUri':ROOT.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}})
        self.until(1,15);self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        with self.write_lock:
            self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
    def read(self,deadline):
        while time.monotonic()<deadline:
            if b'\r\n\r\n' in self.buf:
                header,body=self.buf.split(b'\r\n\r\n',1)
                lengths=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if lengths and len(body)>=lengths[0]:
                    raw,self.buf=body[:lengths[0]],body[lengths[0]:];msg=json.loads(raw)
                    if msg.get('method')=='textDocument/publishDiagnostics':self.diag.append(msg['params'])
                    if 'method' in msg and 'id' in msg:self.send({'jsonrpc':'2.0','id':msg['id'],'result':None})
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,deadline-time.monotonic())))
            if ready:
                data=os.read(self.p.stdout.fileno(),65536)
                if not data:raise RuntimeError('Lean LSP closed stdout')
                self.buf+=data
        raise TimeoutError('Lean LSP response')
    def until(self,rid,timeout):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            msg=self.read(end)
            if msg.get('id')==rid and 'method' not in msg:return msg
        raise TimeoutError('Lean LSP request')
    def goal(self,path,task=None):
        source=path.read_text();uri=path.as_uri()
        self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{
          'uri':uri,'languageId':'lean','version':1,'text':source}}})
        self.send({'jsonrpc':'2.0','id':2,'method':'textDocument/waitForDiagnostics','params':{'uri':uri,'version':1}})
        if task is not None:
            with lock:task['statusMessage']='Lean waitForDiagnostics in flight';task['lastUpdatedAt']=stamp()
        waited=self.until(2,20)
        self.send({'jsonrpc':'2.0','id':3,'method':'$/lean/plainGoal','params':{
          'textDocument':{'uri':uri,'version':1},'position':{'line':6 if path==SLOW else 1,'character':3}}})
        goal=self.until(3,20)
        return {'wait':waited,'goal':goal,'diagnostics':self.diag,'source_sha256':sha(source.encode())}
    def close(self):
        before=descendants(self.p.pid);tracked={r['pid'] for r in before}
        if self.p.poll() is None:
            try:
                self.send({'jsonrpc':'2.0','id':4,'method':'shutdown','params':None});self.until(4,5)
                self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=5)
            except Exception:
                os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        time.sleep(.1);after=[r for r in process_rows().values() if r['pid'] in tracked]
        return {'pid':self.p.pid,'exit':self.p.returncode,'before':before,'tracked_after':after,
                'stderr':self.p.stderr.read().decode(errors='replace')}
def real_goal(path,task=None):
    global active_queries
    with lock:active_queries+=1
    srv=None
    try:
        srv=LeanLSP()
        if task is not None:
            with lock:task['lsp']=srv
        observed=srv.goal(path,task)
    finally:
        cleanup=srv.close() if srv is not None else None
        with lock:
            active_queries-=1
            if task is not None:task.pop('lsp',None)
    observed['cleanup']=cleanup
    with lock:queries.append({'source_sha256':observed['source_sha256'],'wait':observed['wait'],
                               'goal':observed['goal'],'upstream_cancel_sent':bool(task and task.get('upstream_cancel_sent')),
                               'cleanup':cleanup})
    return observed
def tool_result(observed):
    goals=(observed['goal'].get('result') or {}).get('goals') or []
    if not goals:raise RuntimeError('no goal returned')
    return {'resultType':'complete','content':[{'type':'text','text':goals[0]}],
            'isError':False,'_meta':{'sourceSha256':observed['source_sha256'],
                                    'lspExit':observed['cleanup']['exit'],
                                    'trackedAfter':observed['cleanup']['tracked_after']}}
def public(task):
    keys=['taskId','status','statusMessage','createdAt','lastUpdatedAt','ttlMs','pollIntervalMs','result','error']
    return {'resultType':'complete',**{k:task[k] for k in keys if k in task}}
def finish(task):
    task['gate'].wait(15)
    with lock:
        if task['cancel_requested']:
            task['status']='cancelled';task['statusMessage']='cancelled before Lean start';task['lastUpdatedAt']=stamp();return
    try:result=tool_result(real_goal(Path(task['source_path']),task))
    except Exception as ex:
        with lock:
            if task['cancel_requested']:
                task['status']='cancelled';task['statusMessage']='upstream cancellation or query failure after cancel'
            else:
                task['status']='failed';task['statusMessage']='Lean query failed'
            task['error']=err(-32603,str(ex));task['lastUpdatedAt']=stamp()
    else:
        with lock:
            if task['cancel_requested']:
                task['status']='cancelled';task['statusMessage']='result suppressed after in-flight cancellation'
            else:
                task['status']='completed';task['statusMessage']='Lean goal returned';task['result']=result
            task['lastUpdatedAt']=stamp()
def lookup(req):
    tid=(req.get('params') or {}).get('taskId')
    with lock:
        task=tasks.get(tid)
        if task and time.monotonic()>=task['expires_mono']:return None,err(-32602,'task expired')
        if not task:return None,err(-32602,'task not found')
    return task,None
def handle(req):
    global counter
    method=req.get('method');m=meta(req);version=m.get('io.modelcontextprotocol/protocolVersion')
    if version!=VERSION:
        answer(req,error=err(-32602,'missing protocol version') if version is None else
               err(-32022,'unsupported protocol version',{'supported':[VERSION]}));return
    if method=='server/discover':
        answer(req,{'resultType':'complete','supportedVersions':[VERSION],
          'capabilities':{'tools':{},'extensions':{EXT:{}}},
          '_meta':{'io.modelcontextprotocol/serverInfo':{'name':'lean-goal-test-bridge','version':'1'}}});return
    if method=='initialize':answer(req,error=err(-32601,'method not found'));return
    if method=='tools/call':
        params=req.get('params') or {};args=params.get('arguments') or {}
        if params.get('name')!='lean_goal':answer(req,error=err(-32602,'unknown tool'));return
        chosen=SLOW if args.get('slow') else SOURCE
        expected=args.get('expected_sha256');current=sha(chosen.read_bytes())
        if expected!=current:answer(req,error=err(-32602,'stale source',{'current_sha256':current}));return
        caps=m.get('io.modelcontextprotocol/clientCapabilities') or {}
        if EXT not in caps.get('extensions',{}):
            try:answer(req,tool_result(real_goal(chosen)))
            except Exception as ex:answer(req,error=err(-32603,str(ex)))
            return
        with lock:
            counter+=1;tid=f'task-{counter}';now=stamp();task={'taskId':tid,'status':'working',
              'statusMessage':'waiting at test gate','createdAt':now,'lastUpdatedAt':now,
              'ttlMs':10000,'pollIntervalMs':50,'expires_mono':time.monotonic()+10,
              'cancel_requested':False,'source_path':str(chosen),'gate':threading.Event()};tasks[tid]=task
        threading.Thread(target=finish,args=(task,),daemon=True).start()
        answer(req,{'resultType':'task',**{k:task[k] for k in ['taskId','status','statusMessage','createdAt','lastUpdatedAt','ttlMs','pollIntervalMs']}});return
    if method in ('tasks/get','tasks/cancel','test/release'):
        task,e=lookup(req)
        if e:answer(req,error=e);return
        if method=='tasks/get':
            with lock:result=public(task)
            answer(req,result);return
        if method=='tasks/cancel':
            with lock:
                task['cancel_requested']=True
                lsp=task.get('lsp') if task.get('statusMessage')=='Lean waitForDiagnostics in flight' else None
            if lsp is not None:
                try:
                    lsp.send({'jsonrpc':'2.0','method':'$/cancelRequest','params':{'id':2}})
                    with lock:task['upstream_cancel_sent']=True
                except Exception as ex:
                    with lock:task['upstream_cancel_error']=repr(ex)
            answer(req,{'resultType':'complete'});return
        task['gate'].set();answer(req,{'resultType':'complete'});return
    if method=='test/stats':
        with lock:count=len(queries);items=list(queries);active=active_queries
        answer(req,{'resultType':'complete','queryCount':count,'activeQueries':active,'queries':items});return
    answer(req,error=err(-32601,'method not found'))
for line in sys.stdin:
    if not line.strip():continue
    try:req=json.loads(line)
    except json.JSONDecodeError:emit({'jsonrpc':'2.0','id':None,'error':err(-32700,'parse error')});continue
    if 'id' not in req:continue
    handle(req)
