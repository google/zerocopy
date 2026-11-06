#!/usr/bin/env python3
"""Synthetic MCP-shaped stdio bridge over pinned Lean LSP; not an MCP adapter."""
import fcntl,hashlib,json,os,select,subprocess,sys,tempfile,threading,time
from pathlib import Path

LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
ROOT=Path(sys.argv[1]).resolve();SOURCE=ROOT/'Proof.lean';LOCK=ROOT/'.proof.lock'
ENV=dict(os.environ,ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',LEAN_NUM_THREADS='1',LEAN_PATH=str(ROOT))
def digest(b):return hashlib.sha256(b).hexdigest()
def reply(id,result=None,error=None):
    m={'jsonrpc':'2.0','id':id}
    if error is None:m['result']=result
    else:m['error']=error
    with OUT_LOCK:
        sys.stdout.write(json.dumps(m,separators=(',',':'),ensure_ascii=False)+'\n');sys.stdout.flush()
OUT_LOCK=threading.Lock();CANCEL_LOCK=threading.Lock();CANCELLED=set();LSP_LOCK=threading.Lock();THREADS=[]
class LSP:
    def __init__(self):
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=ROOT,env=ENV,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        self.buf=b'';self.version=0;self.current=None;self.diags=[]
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{'processId':os.getpid(),'rootUri':ROOT.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}}})
        self.until(1);self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def send(self,m):
        raw=json.dumps(m,separators=(',',':'),ensure_ascii=False).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
    def read(self,timeout=12):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                h,b=self.buf.split(b'\r\n\r\n',1)
                sizes=[int(x.split(b':',1)[1]) for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if sizes and len(b)>=sizes[0]:
                    raw,self.buf=b[:sizes[0]],b[sizes[0]:]
                    m=json.loads(raw)
                    if m.get('method')=='textDocument/publishDiagnostics':self.diags.append(m['params'])
                    if 'method' in m and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
                    return m
            rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if rd:
                data=os.read(self.p.stdout.fileno(),65536)
                if not data:break
                self.buf+=data
        raise TimeoutError('Lean LSP')
    def until(self,id):
        for _ in range(100):
            m=self.read()
            if m.get('id')==id and 'method' not in m:return m
        raise TimeoutError('Lean LSP id '+str(id))
    def query(self,text,sha):
        uri=SOURCE.as_uri()
        if self.current!=sha:
            self.version+=1;self.current=sha
            if self.version==1:self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':uri,'languageId':'lean','version':self.version,'text':text}}})
            else:self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':uri,'version':self.version},'contentChanges':[{'text':text}]}})
        self.send({'jsonrpc':'2.0','id':100+self.version,'method':'textDocument/waitForDiagnostics','params':{'uri':uri,'version':self.version}})
        wait=self.until(100+self.version)
        self.send({'jsonrpc':'2.0','id':200+self.version,'method':'$/lean/plainGoal','params':{'textDocument':{'uri':uri},'position':{'line':2,'character':4}}})
        goal=self.until(200+self.version)
        ds=[d for d in self.diags if d.get('version')==self.version]
        return {'source_sha256':sha,'lsp_document_version':self.version,'wait':wait,'goal':goal,'diagnostics':ds[-1] if ds else None,'lsp_pid':self.p.pid}
    def close(self):
        if self.p.poll() is None:
            try:self.send({'jsonrpc':'2.0','id':999,'method':'shutdown','params':None});self.until(999);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
            except Exception:self.p.kill();self.p.wait()
        return {'lsp_rc':self.p.returncode,'lsp_stderr':self.p.stderr.read().decode(errors='replace')}
LSP_SERVER=None
def is_cancelled(id):
    with CANCEL_LOCK:return id in CANCELLED
def tool_result(obj,is_error=False):return {'content':[{'type':'text','text':json.dumps(obj,sort_keys=True)}],'isError':is_error}
def handle(m):
    global LSP_SERVER
    id=m['id'];name=m.get('params',{}).get('name');args=m.get('params',{}).get('arguments',{})
    if name not in ('get_goal','slow_goal','apply_edit'):
        reply(id,error={'code':-32602,'message':'unknown toy tool'});return
    if name=='slow_goal':
        end=time.monotonic()+.65
        while time.monotonic()<end:
            if is_cancelled(id):reply(id,error={'code':-32800,'message':'cancelled'});return
            time.sleep(.01)
    if is_cancelled(id):reply(id,error={'code':-32800,'message':'cancelled'});return
    expected=args.get('expected_sha256')
    if not isinstance(expected,str):reply(id,error={'code':-32602,'message':'expected_sha256 required'});return
    if name=='apply_edit':
        new=args.get('new_text')
        if not isinstance(new,str):reply(id,error={'code':-32602,'message':'new_text required'});return
        with LOCK.open('a+b') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            actual=SOURCE.read_bytes();current=digest(actual)
            if current!=expected:result=tool_result({'status':'stale','expected':expected,'current':current},True)
            else:
                fd,tmp=tempfile.mkstemp(dir=ROOT,prefix='.proof-')
                try:
                    with os.fdopen(fd,'wb') as f:f.write(new.encode());f.flush();os.fsync(f.fileno())
                    os.replace(tmp,SOURCE)
                finally:
                    if os.path.exists(tmp):os.unlink(tmp)
                result=tool_result({'status':'applied','old_sha256':current,'new_sha256':digest(new.encode())})
            fcntl.flock(lock,fcntl.LOCK_UN)
        reply(id,result=result);return
    actual=SOURCE.read_bytes();current=digest(actual)
    if current!=expected:
        reply(id,result=tool_result({'status':'stale','expected':expected,'current':current},True));return
    with LSP_LOCK:
        if is_cancelled(id):reply(id,error={'code':-32800,'message':'cancelled'});return
        if LSP_SERVER is None:LSP_SERVER=LSP()
        observed=LSP_SERVER.query(actual.decode(),current)
    if is_cancelled(id):reply(id,error={'code':-32800,'message':'cancelled'});return
    reply(id,result=tool_result({'status':'current',**observed}))
def main():
    assert SOURCE.is_file() and LEAN.is_file()
    for line in sys.stdin:
        if not line.strip():continue
        try:m=json.loads(line)
        except ValueError:continue
        method=m.get('method');id=m.get('id')
        if method=='notifications/cancelled':
            with CANCEL_LOCK:CANCELLED.add(m.get('params',{}).get('requestId'))
        elif method=='initialize' and id is not None:
            reply(id,{'protocolVersion':'2024-11-05','capabilities':{'tools':{}},'serverInfo':{'name':'synthetic-lean-lsp-bridge','version':'0'}})
        elif method=='tools/list' and id is not None:
            reply(id,{'tools':[{'name':n,'description':'synthetic fixture tool','inputSchema':{'type':'object','properties':{'expected_sha256':{'type':'string'}}}} for n in ('get_goal','slow_goal','apply_edit')]})
        elif method=='tools/call' and id is not None:
            t=threading.Thread(target=handle,args=(m,),daemon=False);THREADS.append(t);t.start()
        elif id is not None:reply(id,error={'code':-32601,'message':'unknown toy method'})
    for t in THREADS:t.join(timeout=20)
    if LSP_SERVER is not None:
        with LSP_LOCK:state=LSP_SERVER.close()
        print(json.dumps(state),file=sys.stderr)
if __name__=='__main__':main()
