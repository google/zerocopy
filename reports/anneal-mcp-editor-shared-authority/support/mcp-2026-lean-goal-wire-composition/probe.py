#!/usr/bin/env python3
"""Raw stdio client for current-wire toy Tasks bridge with actual Lean LSP backend."""
import hashlib,json,os,re,select,shutil,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
VERSION='2026-07-28';EXT='io.modelcontextprotocol/tasks'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
class Client:
    def __init__(self):
        self.log=[];self.next_id=1;self.buffer=b''
        self.p=subprocess.Popen([sys.executable,str(HERE/'bridge.py')],cwd=HERE,
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
    def send(self,msg):
        self.log.append({'direction':'client','message':msg})
        self.p.stdin.write((json.dumps(msg,separators=(',',':'))+'\n').encode());self.p.stdin.flush()
    def read(self,timeout=25):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\n' in self.buffer:
                line,self.buffer=self.buffer.split(b'\n',1)
                msg=json.loads(line);self.log.append({'direction':'server','message':msg});return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buffer+=chunk
        raise TimeoutError('bridge response')
    def request(self,method,params=None,version=VERSION,capability=False):
        p=dict(params or {})
        if version is not False:
            p['_meta']={'io.modelcontextprotocol/protocolVersion':version,
              'io.modelcontextprotocol/clientInfo':{'name':'raw-local-test','version':'1'},
              'io.modelcontextprotocol/clientCapabilities':{'extensions':{EXT:{}}} if capability else {}}
        rid=self.next_id;self.next_id+=1;self.send({'jsonrpc':'2.0','id':rid,'method':method,'params':p})
        msg=self.read();assert msg['id']==rid,(rid,msg);return msg
    def close(self):
        self.p.stdin.close();self.p.wait(timeout=5)
        return {'pid':self.p.pid,'exit':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')}
def poll(client,tid,status):
    seen=[];end=time.monotonic()+15
    while time.monotonic()<end:
        q=client.request('tasks/get',{'taskId':tid},capability=True)
        assert 'result' in q,q
        seen.append(q['result']['status'])
        if seen[-1]==status:return q,seen
        time.sleep(.05)
    raise TimeoutError((tid,seen))
def main():
    mem=subprocess.check_output(['memory_pressure','-Q'],text=True,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',mem)
    free=int(m[1]) if m else None;disk=shutil.disk_usage(HERE).free
    if free is None or free<30 or disk<2*1024**3:raise RuntimeError(f'preflight free={free} disk={disk}')
    source=HERE/'Proof.lean';digest=sha(source)
    client=Client();cases={}
    try:
        cases['wrong_version']=client.request('server/discover',version='1900-01-01')
        assert cases['wrong_version']['error']['code']==-32022
        cases['discover']=client.request('server/discover')
        assert EXT in cases['discover']['result']['capabilities']['extensions']
        cases['stale']=client.request('tools/call',{'name':'lean_goal','arguments':{'expected_sha256':'0'*64}},capability=True)
        assert cases['stale']['error']['code']==-32602
        cases['sync']=client.request('tools/call',{'name':'lean_goal','arguments':{'expected_sha256':digest}})
        assert cases['sync']['result']['resultType']=='complete'
        assert '⊢ True' in cases['sync']['result']['content'][0]['text']
        cases['start']=client.request('tools/call',{'name':'lean_goal','arguments':{'expected_sha256':digest}},capability=True)
        assert cases['start']['result']['resultType']=='task'
        tid=cases['start']['result']['taskId']
        cases['initial']=client.request('tasks/get',{'taskId':tid},capability=True)
        assert cases['initial']['result']['status']=='working'
        cases['old_result_method']=client.request('tasks/result',{'taskId':tid},capability=True)
        assert cases['old_result_method']['error']['code']==-32601
        client.request('test/release',{'taskId':tid},capability=True)
        cases['completed'],cases['states']=poll(client,tid,'completed')
        final=cases['completed']['result']['result']
        assert final['resultType']=='complete' and '⊢ True' in final['content'][0]['text']
        assert final['_meta']['sourceSha256']==digest and final['_meta']['trackedAfter']==[]
        cases['cancel_start']=client.request('tools/call',{'name':'lean_goal','arguments':{'expected_sha256':digest}},capability=True)
        cid=cases['cancel_start']['result']['taskId']
        cases['cancel_ack']=client.request('tasks/cancel',{'taskId':cid},capability=True)
        assert cases['cancel_ack']['result']=={'resultType':'complete'}
        client.request('test/release',{'taskId':cid},capability=True)
        cases['cancelled'],cases['cancel_states']=poll(client,cid,'cancelled')
        cases['before_slow_stats']=client.request('test/stats')
        assert cases['before_slow_stats']['result']['queryCount']==2 # sync + completed task; cancelled-before-start did not query Lean
        slow_digest=sha(HERE/'Slow.lean')
        cases['slow_start']=client.request('tools/call',{'name':'lean_goal','arguments':{
            'slow':True,'expected_sha256':slow_digest}},capability=True)
        sid=cases['slow_start']['result']['taskId']
        client.request('test/release',{'taskId':sid},capability=True)
        deadline=time.monotonic()+10;inflight=[]
        while time.monotonic()<deadline:
            item=client.request('tasks/get',{'taskId':sid},capability=True)
            inflight.append(item['result']['statusMessage'])
            if item['result']['statusMessage']=='Lean waitForDiagnostics in flight':break
            time.sleep(.03)
        else:raise TimeoutError(('slow Lean did not enter wait',inflight))
        cases['slow_inflight']=item
        time.sleep(.15)
        cases['slow_cancel_ack']=client.request('tasks/cancel',{'taskId':sid},capability=True)
        assert cases['slow_cancel_ack']['result']=={'resultType':'complete'}
        cases['slow_cancelled'],cases['slow_states']=poll(client,sid,'cancelled')
        assert 'result' not in cases['slow_cancelled']['result']
        cases['stats']=client.request('test/stats')
        assert cases['stats']['result']['queryCount']==3
        assert cases['stats']['result']['activeQueries']==0
        assert all(q['cleanup']['tracked_after']==[] for q in cases['stats']['result']['queries'])
    finally:closed=client.close()
    assert closed['exit']==0 and not closed['stderr'],closed
    batch=subprocess.run([str(LEAN),'--json',str(source)],cwd=HERE,
        env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(HERE)),capture_output=True,text=True,timeout=20)
    assert batch.returncode==0 and '⊢ True' in batch.stdout and 'target' in batch.stdout,(batch.returncode,batch.stdout,batch.stderr)
    slow_batch=subprocess.run([str(LEAN),'--json',str(HERE/'Slow.lean')],cwd=HERE,
        env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(HERE)),capture_output=True,text=True,timeout=20)
    assert slow_batch.returncode==0 and '⊢ True' in slow_batch.stdout and "'target' does not depend on any axioms" in slow_batch.stdout
    result={'scope':'stdlib modern wire shape with real pinned Lean LSP goal; no SDK/Anneal adapter',
      'preflight':{'free_memory_percent':free,'free_disk_bytes':disk},
      'pins':{'lean':str(LEAN),'lean_sha256':sha(LEAN),'source_sha256':digest,
              'bridge_sha256':sha(HERE/'bridge.py'),'probe_sha256':sha(HERE/'probe.py'),
              'slow_source_sha256':sha(HERE/'Slow.lean')},
      'cases':cases,'transcript':client.log,'bridge_process':closed,
      'batch':{'argv':[str(LEAN),'--json',str(source)],'exit':batch.returncode,
               'stdout':batch.stdout,'stderr':batch.stderr},
      'slow_batch':{'argv':[str(LEAN),'--json',str(HERE/'Slow.lean')],'exit':slow_batch.returncode,
                    'stdout':slow_batch.stdout,'stderr':slow_batch.stderr}}
    (HERE/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'bridge_events':len(client.log),'query_count':cases['stats']['result']['queryCount'],
      'task_statuses':[cases['completed']['result']['status'],cases['cancelled']['result']['status'],cases['slow_cancelled']['result']['status']],
      'batch_exit':batch.returncode,'free_memory_percent':free}))
if __name__=='__main__':main()
