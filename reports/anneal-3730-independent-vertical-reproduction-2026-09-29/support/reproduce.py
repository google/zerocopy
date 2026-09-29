#!/usr/bin/env python3
"""Independent small implementation of the vertical-report procedure, not Anneal."""
import hashlib,json,os,re,select,subprocess,tempfile,time
from pathlib import Path

LEAN=Path(os.environ['LEAN_BIN']).resolve()
SCRATCH=Path(os.environ['ANNEAL_PROBE_SCRATCH']).resolve()
OUT=Path(__file__).with_name('results.json')
LOG=[]

def digest(x):return hashlib.sha256(x if isinstance(x,bytes) else x.encode()).hexdigest()
def emit(kind,**data):LOG.append(dict(seq=len(LOG),kind=kind,**data))
def run(name,argv,cwd,env=None):
    p=subprocess.run(argv,cwd=cwd,env=dict(os.environ,LEAN_NUM_THREADS='1',**(env or {})),
                     text=True,capture_output=True,timeout=20)
    emit('command',name=name,cwd='$WORK/'+cwd.name,
         argv=[str(x).replace(str(LEAN),'$LEAN_BIN') for x in argv],rc=p.returncode,
         stdout=p.stdout.replace(str(cwd),'$WORK/'+cwd.name),
         stderr=p.stderr.replace(str(cwd),'$WORK/'+cwd.name))
    return p

class Lsp:
    def __init__(self,cwd):
        self.cwd=cwd;self.buf=b'';self.n=2
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=cwd,
            env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(cwd)),
            stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0)
        emit('server_start',cwd='$WORK/'+cwd.name,pid=self.p.pid)
        self.send({'jsonrpc':'2.0','id':1,'method':'initialize','params':{
          'processId':os.getpid(),'rootUri':cwd.as_uri(),'capabilities':{},
          'initializationOptions':{'hasWidgets':False}}})
        self.until(lambda x:x.get('id')==1)
        self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
    def norm(self,x):return json.loads(json.dumps(x).replace(str(self.cwd),'$WORK/'+self.cwd.name))
    def send(self,x):
        b=json.dumps(x,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b)
        self.p.stdin.flush();emit('send',message=self.norm(x))
    def read(self):
        end=time.monotonic()+15
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                h,body=self.buf.split(b'\r\n\r\n',1)
                n=[int(v.split(b':',1)[1]) for v in h.split(b'\r\n') if v.lower().startswith(b'content-length:')]
                if n and len(body)>=n[0]:
                    raw,self.buf=body[:n[0]],body[n[0]:]
                    x=json.loads(raw);emit('receive',message=self.norm(x))
                    if x.get('method')=='client/registerCapability' and 'id' in x:
                        self.send({'jsonrpc':'2.0','id':x['id'],'result':None})
                    return x
            ready,_,_=select.select([self.p.stdout],[],[],max(.01,min(.1,end-time.monotonic())))
            if ready:
                b=os.read(self.p.stdout.fileno(),65536)
                if not b:break
                self.buf+=b
        raise TimeoutError('LSP read')
    def until(self,pred):
        for _ in range(100):
            x=self.read()
            if pred(x):return x
        raise TimeoutError('LSP response')
    def request(self,method,params):
        n=self.n;self.n+=1
        self.send({'jsonrpc':'2.0','id':n,'method':method,'params':params})
        return self.until(lambda x:x.get('id')==n)
    def stop(self):
        try:
            self.request('shutdown',None)
            self.send({'jsonrpc':'2.0','method':'exit'})
            self.p.wait(timeout=3)
        except Exception:
            self.p.kill();self.p.wait()
        emit('server_stop',rc=self.p.returncode)

def host(n,body):return 'pub const MODEL_VALUE: u8 = '+str(n)+';\n'+''.join('// anneal: '+line+'\n' for line in body.splitlines())
def translate(text):
    m=re.search(r'^pub const MODEL_VALUE: u8 = ([0-9]+);$',text,re.M)
    assert m
    payload=''.join(line[len('// anneal: '):]+'\n' for line in text.splitlines() if line.startswith('// anneal: '))
    return 'import Lean\ndef modelValue : Nat := '+m.group(1)+'\n','import Generated\n'+payload

def snapshot(base,name,text,generated_override=None,proof_override=None):
    d=base/name;d.mkdir()
    model,proof=translate(text)
    if generated_override is not None:model=generated_override
    if proof_override is not None:proof=proof_override
    (d/'RustHost.rs').write_text(text)
    (d/'Generated.lean').write_text(model)
    (d/'Proof.lean').write_text(proof)
    entry={'host_sha256':digest(text),'model_sha256':digest(model),'proof_sha256':digest(proof)}
    emit('snapshot',name=name,**entry)
    return d,entry

def build_model(name,d):
    p=run(name+'-model',[str(LEAN),'--json','-o','Generated.olean','Generated.lean'],d)
    path=d/'Generated.olean'
    return {'rc':p.returncode,'artifact_sha256':digest(path.read_bytes()) if path.exists() else None}

def check(name,d,expected):
    env={'LEAN_PATH':str(d)}
    p=run(name+'-proof',[str(LEAN),'--json','Proof.lean'],d,env)
    if p.returncode:
        return {'proof_rc':p.returncode,'artifact_rc':None,'oracle_rc':None,'axiom_data':None}
    c=run(name+'-artifact',[str(LEAN),'--json','-o','Proof.olean','Proof.lean'],d,env)
    assert c.returncode==0
    oracle='import Proof\nexample : modelValue = '+str(expected)+' := claim\n#print axioms claim\n'
    (d/'Oracle.lean').write_text(oracle)
    o=run(name+'-oracle',[str(LEAN),'--json','Oracle.lean'],d,env)
    ax=[json.loads(line).get('data') for line in o.stdout.splitlines() if line.startswith('{') and 'axiom' in line]
    result={'proof_rc':p.returncode,'artifact_rc':c.returncode,'oracle_rc':o.returncode,
            'axiom_data':ax,'oracle_sha256':digest(oracle),
            'proof_artifact_sha256':digest((d/'Proof.olean').read_bytes())}
    emit('check',name=name,**result)
    return result

def live(name,d,first,second=None):
    s=Lsp(d)
    try:
        uri=(d/'Proof.lean').as_uri()
        s.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{
           'uri':uri,'languageId':'lean','version':1,'text':first}}})
        w1=s.request('textDocument/waitForDiagnostics',{'uri':uri,'version':1})
        g1=s.request('$/lean/plainGoal',{'textDocument':{'uri':uri},
           'position':{'line':2,'character':len(first.splitlines()[2])}})
        result={'initial_wait':w1,'initial_goal':g1,'disk_proof_sha256':digest((d/'Proof.lean').read_bytes())}
        if second is not None:
            s.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{
              'textDocument':{'uri':uri,'version':2},'contentChanges':[{'text':second}]}})
            w2=s.request('textDocument/waitForDiagnostics',{'uri':uri,'version':2})
            g2=s.request('$/lean/plainGoal',{'textDocument':{'uri':uri},
              'position':{'line':2,'character':len(second.splitlines()[2])}})
            result.update(edited_wait=w2,edited_goal=g2,
                          disk_proof_sha256_after_edit=digest((d/'Proof.lean').read_bytes()))
        emit('live',name=name,**result)
        return result
    finally:s.stop()

def main():
    SCRATCH.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='vertical-repro-',dir=SCRATCH) as temp:
        base=Path(temp)
        initial=host(3,'theorem claim : modelValue = 3 := by\n  exact ?_')
        a=host(3,'theorem claim : modelValue = 3 := by\n  rfl')
        f=host(5,'theorem claim : modelValue = 5 := by\n  rfl')
        b=host(4,'theorem claim : modelValue = 4 := by\n  rfl')
        state={'host':initial,'revision':0,'selected':None}
        def cas(old,new):
            okay=digest(state['host'])==digest(old)
            if okay:state['host']=new;state['revision']+=1
            emit('cas',expected_sha256=digest(old),new_sha256=digest(new),
                 accepted=okay,revision=state['revision'])
            return okay
        assert cas(initial,a)
        ad,asnap=snapshot(base,'A',a)
        ai,aisnap=snapshot(base,'A-initial',initial)
        am=build_model('A',ad);assert am['rc']==0
        (ai/'Generated.olean').write_bytes((ad/'Generated.olean').read_bytes())
        alive=live('A',ai,(ai/'Proof.lean').read_text(),(ad/'Proof.lean').read_text())
        assert 'modelValue = 3' in str(alive['initial_goal']) and 'no goals' in str(alive['edited_goal'])
        ac=check('A',ad,3);assert ac['proof_rc']==ac['oracle_rc']==0
        state['selected']={'name':'A','revision':1,'host_sha256':asnap['host_sha256'],
                           'model_artifact_sha256':am['artifact_sha256']}
        emit('publish',selected=state['selected'])

        # Start an old A compilation and wait for a causal gate inside Lean.
        late_proof=('import Generated\ntheorem claim : modelValue = 3 := by\n'
          '  run_tac do\n    IO.FS.writeFile "gate.entered" "1"\n'
          '    while !(← (System.FilePath.mk "gate.release").pathExists) do\n'
          '      IO.sleep 10\n  rfl\n')
        ld,lsnap=snapshot(base,'A-late',a,proof_override=late_proof)
        (ld/'Generated.olean').write_bytes((ad/'Generated.olean').read_bytes())
        late=subprocess.Popen([str(LEAN),'--json','-o','Proof.olean','Proof.lean'],cwd=ld,
            env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(ld)),
            stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        emit('late_started',pid=late.pid,revision=1)
        end=time.monotonic()+10
        while not (ld/'gate.entered').exists() and time.monotonic()<end:
            if late.poll() is not None:break
            time.sleep(.01)
        assert (ld/'gate.entered').exists() and late.poll() is None
        emit('late_gate_entered',revision=1)

        assert cas(a,f)
        fd,fsnap=snapshot(base,'F-invalid',f,generated_override='import Lean\ndef modelValue : Nat :=\n')
        fm=build_model('F-invalid',fd);assert fm['rc']!=0
        emit('failed_generation',revision=state['revision'],last_good=state['selected'])
        assert cas(f,b)
        bd,bsnap=snapshot(base,'B',b)
        bm=build_model('B',bd);assert bm['rc']==0
        blive=live('B',bd,(bd/'Proof.lean').read_text())
        assert 'no goals' in str(blive['initial_goal'])
        bc=check('B',bd,4);assert bc['proof_rc']==bc['oracle_rc']==0
        state['selected']={'name':'B','revision':3,'host_sha256':bsnap['host_sha256'],
                           'model_artifact_sha256':bm['artifact_sha256']}
        emit('publish',selected=state['selected'])
        assert not cas(a,initial)
        (ld/'gate.release').write_text('1')
        late_out,late_err=late.communicate(timeout=15)
        emit('late_completed',rc=late.returncode,stdout=late_out.decode(errors='replace'),
             stderr=late_err.decode(errors='replace'),selected=state['selected'])
        assert late.returncode==0 and (ld/'Proof.olean').exists()
        late_oracle='import Proof\nexample : modelValue = 3 := claim\n#print axioms claim\n'
        (ld/'Oracle.lean').write_text(late_oracle)
        lo=run('A-late-oracle',[str(LEAN),'--json','Oracle.lean'],ld,{'LEAN_PATH':str(ld)})
        assert lo.returncode==0
        late_disposition='reject-stale' if 1<state['selected']['revision'] else 'publish'
        assert late_disposition=='reject-stale' and state['selected']['name']=='B'
        emit('late_disposition',decision=late_disposition,selected=state['selected'])

        controls={}
        stale_live=None
        for name,proof in {
          'stale-on-B':translate(a)[1],
          'weak-on-B':'import Generated\ntheorem claim : True := by trivial\n',
          'admitted-on-B':'import Generated\ntheorem claim : modelValue = 4 := by sorry\n',
        }.items():
            cd,cs=snapshot(base,name,b,proof_override=proof)
            (cd/'Generated.olean').write_bytes((bd/'Generated.olean').read_bytes())
            controls[name]=check(name,cd,4)
            if name=='stale-on-B':
                stale_live=live('stale-on-B',cd,proof)
        assert controls['stale-on-B']['proof_rc']!=0
        assert controls['weak-on-B']['proof_rc']==0 and controls['weak-on-B']['oracle_rc']!=0
        assert controls['admitted-on-B']['oracle_rc']==0 and 'sorryAx' in str(controls['admitted-on-B']['axiom_data'])
        result={'tool_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
                'tool_sha256':digest(LEAN.read_bytes()),'snapshots':{'initial':aisnap,'A':asnap,'F':fsnap,'B':bsnap,'A-late':lsnap},
                'models':{'A':am,'F':fm,'B':bm},'checks':{'A':ac,'B':bc,**controls},
                'live':{'A':alive,'B':blive,'stale-on-B':stale_live},'late':{'rc':late.returncode,'oracle_rc':lo.returncode,
                'decision':late_disposition},'final_selected':state['selected'],'events':LOG}
        OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'A_goal':alive['edited_goal'].get('result'),
                          'B_goal':blive['initial_goal'].get('result'),
                          'A_oracle':ac['oracle_rc'],'B_oracle':bc['oracle_rc'],
                          'F_model':fm['rc'],'controls':{k:(v['proof_rc'],v['oracle_rc']) for k,v in controls.items()},
                          'late':result['late'],'selected':state['selected']['name']},indent=2))

if __name__=='__main__':main()
