#!/usr/bin/env python3
"""Two synthetic MCP-shaped stdio clients sharing one pinned Lean workspace."""
import hashlib,json,os,re,select,shutil,subprocess,sys,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
WORK=Path('/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/i072-work')
SOURCE1='import Lean\ntheorem checked (n : Nat) : n + 0 = n := by\n  skip\n'
SOURCE2='import Lean\ntheorem checked (n : Nat) : n + 0 = n := by\n  exact Nat.add_zero n\n'
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory():
    path=[]
    for d in dict.fromkeys(os.environ['PATH'].split(os.pathsep)):
        n=[]
        try:
            for e in os.scandir(d):
                low=e.name.lower()
                if 'mcp' not in low and not re.search(r'(^|[-_])lean(4|$|[-_])',low):continue
                try:
                    if e.is_file() and os.access(e.path,os.X_OK):n.append(e.name)
                except OSError:continue
            n.sort()
        except OSError as e:n=['unreadable:'+str(e)]
        path.append({'directory':d,'matching_executables':n})
    rg=shutil.which('rg');files=[]
    if rg:
        p=subprocess.run([rg,'--files','.'],cwd=REPO,capture_output=True,text=True,timeout=10)
        files=sorted(f for f in p.stdout.splitlines() if ('mcp' in f.lower() or 'adapter' in f.lower()) and not f.startswith('./.git/'))
    return {'path_scan':path,'checkout_matching_paths':files,'searched_names':['lean-mcp','lean_mcp','leanmcp','mcp-lean','lean-server-mcp','lean-lsp-mcp'],
            'named_resolutions':{n:shutil.which(n) for n in ['lean-mcp','lean_mcp','leanmcp','mcp-lean','lean-server-mcp','lean-lsp-mcp']},
            'boundary':'Only checkout file names and current PATH executable names were inventoried; report/source text is not an installed adapter.'}
class Client:
    def __init__(self,name):
        self.name=name;self.p=subprocess.Popen([sys.executable,str(HERE/'bridge.py'),str(WORK)],cwd=REPO,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=False,bufsize=0)
        self.buf=b'';self.log=[];self.pending={}
    def send(self,m):
        b=(json.dumps(m,separators=(',',':'),ensure_ascii=False)+'\n').encode()
        self.p.stdin.write(b);self.p.stdin.flush();self.log.append({'direction':'client','message':m})
    def read(self,timeout=20):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\n' in self.buf:
                line,self.buf=self.buf.split(b'\n',1)
                m=json.loads(line);self.log.append({'direction':'server','message':m});return m
            rd,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if rd:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError(self.name+' stdio')
    def until(self,id):
        if id in self.pending:return self.pending.pop(id)
        for _ in range(50):
            m=self.read()
            if m.get('id')==id:return m
            if 'id' in m:self.pending[m['id']]=m
        raise TimeoutError(self.name+' id '+str(id))
    def close(self):
        self.p.stdin.close();self.p.wait(timeout=15)
        return {'bridge_rc':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace'),'pid':self.p.pid}
def request(id,method,params=None):return {'jsonrpc':'2.0','id':id,'method':method,'params':params or {}}
def call(id,name,**args):return request(id,'tools/call',{'name':name,'arguments':args})
def payload(response):
    if 'error' in response:return {'protocol_error':response['error']}
    result=response['result'];return {'isError':result.get('isError'),'data':json.loads(result['content'][0]['text'])}
def main():
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();(WORK/'Proof.lean').write_text(SOURCE1)
    first=sha(SOURCE1.encode());second=sha(SOURCE2.encode())
    availability=inventory()
    # Source-only repo reports are present; no executable adapter in PATH.
    assert not any(availability['named_resolutions'].values())
    a=Client('A');b=Client('B');events=[]
    try:
        for c in (a,b):
            c.send(request(1,'initialize',{'protocolVersion':'2024-11-05','capabilities':{},'clientInfo':{'name':c.name,'version':'0'}}))
            events.append({'client':c.name,'step':'initialize','reply':c.until(1)})
            c.send(request(2,'tools/list'));events.append({'client':c.name,'step':'tools/list','reply':c.until(2)})
        # Same request ID is legal in separate stdio sessions. Cancel A only.
        a.send(call(42,'slow_goal',expected_sha256=first));b.send(call(42,'slow_goal',expected_sha256=first))
        time.sleep(.08)
        a.send({'jsonrpc':'2.0','method':'notifications/cancelled','params':{'requestId':42,'reason':'user cancelled A only'}})
        a.send(call(43,'get_goal',expected_sha256=first))
        events.append({'client':'A','step':'cancelled-42','reply':a.until(42)})
        events.append({'client':'A','step':'parallel-43','reply':a.until(43)})
        events.append({'client':'B','step':'uncancelled-42','reply':b.until(42)})
        a.send(call(44,'apply_edit',expected_sha256=first,new_text=SOURCE2))
        events.append({'client':'A','step':'apply-v2','reply':a.until(44)})
        b.send(call(44,'get_goal',expected_sha256=first))
        events.append({'client':'B','step':'stale-v1','reply':b.until(44)})
        b.send(call(45,'get_goal',expected_sha256=second));a.send(call(45,'get_goal',expected_sha256=second))
        events.append({'client':'B','step':'fresh-v2','reply':b.until(45)})
        events.append({'client':'A','step':'fresh-v2','reply':a.until(45)})
    finally:
        states={'A':a.close(),'B':b.close()}
    artifacts=HERE/'artifacts';artifacts.mkdir(exist_ok=True)
    (artifacts/'Proof-v1.lean').write_text(SOURCE1)
    (artifacts/'Proof-v2.lean').write_bytes((WORK/'Proof.lean').read_bytes())
    result={'schema':1,'availability':availability,'workspace':{'initial_sha256':first,'final_sha256':sha((WORK/'Proof.lean').read_bytes()),'expected_final_sha256':second,
             'initial_text':SOURCE1,'final_text':(WORK/'Proof.lean').read_text(),
             'retained_v1_sha256':sha((artifacts/'Proof-v1.lean').read_bytes()),'retained_v2_sha256':sha((artifacts/'Proof-v2.lean').read_bytes())},
             'events':events,'client_transcripts':{'A':a.log,'B':b.log},'processes':states,
             'boundary':'Synthetic MCP-shaped stdio bridge over two real Lean LSP processes, not an existing Lean MCP adapter or Anneal workspace.'}
    (HERE/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'events':len(events),'results_sha256':sha((HERE/'results.json').read_bytes())},indent=2))
if __name__=='__main__':main()
