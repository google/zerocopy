#!/usr/bin/env python3
"""Small direct Lean/Lake document and module context probe, no dependencies."""
import hashlib,json,os,pathlib,select,shutil,subprocess,time
R=pathlib.Path(__file__).resolve().parent; W=R/'work'
BIN=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin'); LEAN=BIN/'lean'; LAKE=BIN/'lake'
E={**os.environ,'LEAN_NUM_THREADS':'1','ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2','LAKE_CACHE_DIR':'','LAKE_ARTIFACT_CACHE':'false'}
def sha(x):
 if isinstance(x,pathlib.Path):x=x.read_bytes()
 if isinstance(x,str):x=x.encode()
 return hashlib.sha256(x).hexdigest()
def run(cmd,cwd,env=E):
 p=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,capture_output=True,text=True,timeout=30)
 return {'cmd':[str(x) for x in cmd],'rc':p.returncode,'out':p.stdout,'err':p.stderr}
class S:
 def __init__(self,cwd,env):
  self.p=subprocess.Popen([str(LEAN),'--server'],cwd=cwd,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0);self.buf=b'';self.id=1;self.events=[]
  self.req('initialize',{'processId':os.getpid(),'rootUri':cwd.as_uri(),'capabilities':{},'initializationOptions':{'hasWidgets':False}})
  self.send({'jsonrpc':'2.0','method':'initialized','params':{}})
 def send(self,m):
  b=json.dumps(m,separators=(',',':')).encode();self.p.stdin.write(b'Content-Length: '+str(len(b)).encode()+b'\r\n\r\n'+b);self.p.stdin.flush();self.events.append({'dir':'client','msg':m})
 def recv(self,timeout=15):
  stop=time.monotonic()+timeout
  while time.monotonic()<stop:
   if b'\r\n\r\n' in self.buf:
    h,b=self.buf.split(b'\r\n\r\n',1);length=int([x.split(b':',1)[1] for x in h.split(b'\r\n') if x.lower().startswith(b'content-length:')][0]);
    if len(b)>=length:
     m=json.loads(b[:length]);self.buf=b[length:];self.events.append({'dir':'server','msg':m})
     if m.get('method')=='client/registerCapability' and 'id' in m:self.send({'jsonrpc':'2.0','id':m['id'],'result':None})
     return m
   ready,_,_=select.select([self.p.stdout],[],[],.1)
   if ready:
    b=os.read(self.p.stdout.fileno(),65536)
    if not b:break
    self.buf+=b
  raise TimeoutError('LSP receive')
 def req(self,method,params):
  self.id+=1;i=self.id;self.send({'jsonrpc':'2.0','id':i,'method':method,'params':params})
  while True:
   m=self.recv()
   if m.get('id')==i:return m
 def open(self,p,text,version):self.send({'jsonrpc':'2.0','method':'textDocument/didOpen','params':{'textDocument':{'uri':p.as_uri(),'languageId':'lean','version':version,'text':text}}})
 def edit(self,p,text,version):self.send({'jsonrpc':'2.0','method':'textDocument/didChange','params':{'textDocument':{'uri':p.as_uri(),'version':version},'contentChanges':[{'text':text}]}})
 def wait(self,p,version):return self.req('textDocument/waitForDiagnostics',{'uri':p.as_uri(),'version':version})
 def close(self):
  try:self.req('shutdown',None);self.send({'jsonrpc':'2.0','method':'exit'});self.p.wait(timeout=3)
  except Exception:self.p.kill();self.p.wait()
  self.events.append({'dir':'exit','rc':self.p.returncode,'stderr':self.p.stderr.read().decode(errors='replace')})
def main():
 if W.exists():shutil.rmtree(W)
 W.mkdir();o={'subject':{'lean_sha256':sha(LEAN),'lake_sha256':sha(LAKE),'version':run([LEAN,'--version'],W)},'files':{},'runs':{}}
 def put(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s);o['files'][str(p.relative_to(W))]={'sha256':sha(s),'text':s,'uri':p.as_uri()};return p
 proj=W/'project';proj.mkdir();put(proj/'lean-toolchain','leanprover/lean4:v4.30.0-rc2\n');put(proj/'lakefile.lean','import Lake\nopen Lake DSL\npackage Context where\nlean_lib A\nlean_lib B\n')
 A7='def marker : Nat := 7\n';A9='def marker : Nat := 9\n';B='import A\nexample : marker = 7 := by decide\n#eval marker\n'
 a=put(proj/'A.lean',A7);b=put(proj/'B.lean',B)
 o['runs']['build_A7']=run([LAKE,'build','A','--keep-toolchain','--no-cache'],proj);artifact=proj/'.lake/build/lib/lean/A.olean';o['runs']['A7_olean_sha256']=sha(artifact)
 env={**E,'LEAN_PATH':str(artifact.parent)};o['runs']['batch_B_A7']=run([LEAN,'--json',b],proj,env)
 s=S(proj,env);s.open(a,A7,1);s.open(b,B,1);s.wait(a,1);s.wait(b,1)
 s.edit(a,A9,2);s.wait(a,2)
 # Force B to re-elaborate without changing A.olean; only its open source changes.
 s.edit(b,B+'\n#check marker\n',2);s.wait(b,2)
 o['runs']['unsaved']={'events':s.events,'disk_A_sha256':sha(a),'olean_A_sha256':sha(artifact)};s.close();o['runs']['unsaved']['events']=s.events
 o['runs']['batch_B_after_unsaved']=run([LEAN,'--json',b],proj,env)
 put(a,A9);o['runs']['build_A9']=run([LAKE,'build','A','--keep-toolchain','--no-cache'],proj);o['runs']['A9_olean_sha256']=sha(artifact)
 o['runs']['batch_B_A9']=run([LEAN,'--json',b],proj,env)
 s=S(proj,env);s.open(b,B,1);s.wait(b,1);o['runs']['fresh_B_after_build']={'events':s.events};s.close();o['runs']['fresh_B_after_build']['events']=s.events
 # Same URI and source, different generation-specific search path in fresh workers.
 gen7=W/'gen7';gen9=W/'gen9';gen7.mkdir();gen9.mkdir()
 # Rebuild value 7 into isolated generation, then preserve both artifacts.
 put(a,A7);o['runs']['rebuild_A7']=run([LAKE,'build','A','--keep-toolchain','--no-cache'],proj);shutil.copy2(artifact,gen7/'A.olean')
 put(a,A9);o['runs']['rebuild_A9']=run([LAKE,'build','A','--keep-toolchain','--no-cache'],proj);shutil.copy2(artifact,gen9/'A.olean')
 for name,gen in [('gen7',gen7),('gen9',gen9)]:
  s=S(proj,{**E,'LEAN_PATH':str(gen)});s.open(b,B,1);s.wait(b,1);o['runs'][name]={'artifact_sha256':sha(gen/'A.olean'),'B_uri':b.as_uri(),'B_sha256':sha(B),'events':s.events};s.close();o['runs'][name]['events']=s.events
 # A neutral workspace prevents Lake project setup from selecting the project's .lake output.
 neutral=W/'neutral';neutral.mkdir();stable=put(neutral/'B.lean',B)
 for name,gen in [('neutral_gen7',gen7),('neutral_gen9',gen9)]:
  e={**E,'LEAN_PATH':str(gen)};o['runs'][name+'_batch']=run([LEAN,'--json',stable],neutral,e)
  s=S(neutral,e);s.open(stable,B,1);s.wait(stable,1);o['runs'][name]={'artifact_sha256':sha(gen/'A.olean'),'B_uri':stable.as_uri(),'B_sha256':sha(B),'events':s.events};s.close();o['runs'][name]['events']=s.events
 # Prepare valid outputs and then introduce a cycle at the same paths.
 stale=W/'cycle_stale';stale.mkdir();put(stale/'lean-toolchain','leanprover/lean4:v4.30.0-rc2\n');put(stale/'lakefile.lean','import Lake\nopen Lake DSL\npackage CycleStale where\nlean_lib A\nlean_lib B\n');put(stale/'A.lean','def a : Nat := 1\n');put(stale/'B.lean','import A\ndef b : Nat := a + 1\n');o['runs']['cycle_stale_seed']=run([LAKE,'build','B','--keep-toolchain','--no-cache'],stale)
 o['runs']['cycle_stale_A_before']=sha(stale/'.lake/build/lib/lean/A.olean');o['runs']['cycle_stale_B_before']=sha(stale/'.lake/build/lib/lean/B.olean')
 put(stale/'A.lean','import B\ndef a : Nat := 1\n');o['runs']['cycle_stale_rebuild']=run([LAKE,'build','B','--keep-toolchain','--no-cache'],stale)
 # Cyclic import in clean Lake graph, with stale A/B outputs present in a second run.
 cycle=W/'cycle';cycle.mkdir();put(cycle/'lean-toolchain','leanprover/lean4:v4.30.0-rc2\n');put(cycle/'lakefile.lean','import Lake\nopen Lake DSL\npackage Cycle where\nlean_lib A\nlean_lib B\n');put(cycle/'A.lean','import B\ndef a : Nat := 1\n');put(cycle/'B.lean','import A\ndef b : Nat := 2\n');o['runs']['cycle_clean']=run([LAKE,'build','A','--keep-toolchain','--no-cache'],cycle)
 # Deliberate declaration order and wrapper context controls.
 c=W/'context';c.mkdir()
 cases={
  'ordered':'def later : Nat := 1\ntheorem early : later = 1 := by rfl\n',
  'ordered_axiom':'def later : Nat := 1\naxiom early : later = 1\n#print early\n',
  'forward_axiom':'axiom early : later = 1\ndef later : Nat := 1\n#print early\n',
  'forward':'theorem early : later = 1 := by rfl\ndef later : Nat := 1\n',
  'context_full':'set_option autoImplicit false\nnamespace N\nsection\nvariable (n : Nat)\nlocal notation "myN" => n\ntheorem proof : myN = n := by rfl\n#print N.proof\nend\nend N\n',
  'scratch_missing_context':'set_option autoImplicit false\nnamespace N\ntheorem proof : myN = n := by rfl\n#print N.proof\nend N\n',
  'scratch_recreated_context':'set_option autoImplicit false\nnamespace N\nsection\nvariable (n : Nat)\nlocal notation "myN" => n\ntheorem proof : myN = n := by rfl\n#print N.proof\nend\nend N\n'
 }
 for name,src in cases.items():p=put(c/(name+'.lean'),src);o['runs'][name]=run([LEAN,'--json',p],c)
 raw=json.dumps(o,indent=2);raw=raw.replace(str(W),'$WORK').replace(str(BIN),'$LEAN_BIN').replace(str(BIN.parent),'$LEAN_HOME').replace(str(pathlib.Path.home()),'$HOME');(R/'raw.json').write_text(raw+'\n')
 print({k:(v.get('rc') if isinstance(v,dict) else None) for k,v in o['runs'].items() if k in ('build_A7','batch_B_A7','batch_B_after_unsaved','build_A9','batch_B_A9','cycle_clean','ordered','forward','context_full','scratch_missing_context','scratch_recreated_context')})
if __name__=='__main__':main()
