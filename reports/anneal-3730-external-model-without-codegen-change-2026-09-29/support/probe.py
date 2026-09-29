#!/usr/bin/env python3
"""E10: vary only a Lean external model while Aeneas output is fixed."""
import hashlib,json,os,select,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
SOURCE='''#![allow(dead_code)]
unsafe extern "C" { fn external_double(x: u32) -> u32; }
pub fn external_call(x: u32) -> u32 { unsafe { external_double(x) } }
'''
CHECK='import Source\n#print axioms external_probe.external_call\nexample : external_probe.external_call 1#u32 = .ok 2#u32 := by rfl\n'
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
COMMANDS=[];EVENTS=[];T0=time.monotonic()
def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inventory(root):return {p.relative_to(root).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
  for p in sorted(root.rglob('*')) if p.is_file()}
def log(kind,**kw):EVENTS.append({'seq':len(EVENTS),'ms':round((time.monotonic()-T0)*1000,2),'kind':kind,**kw})
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',
      PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def leanenv(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_NUM_THREADS']='1';e['LEAN_PATH']=os.pathsep.join(str(p) for p in [comp,*libs] if p.is_dir())
    return e
def run(label,args,cwd,env=None,timeout=90):
    argv=list(map(str,args));t=time.monotonic()
    p=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
    row={'label':label,'argv':argv,'cwd':str(cwd),'rc':p.returncode,
      'ms':round((time.monotonic()-t)*1000,2),'stdout':p.stdout,'stderr':p.stderr}
    COMMANDS.append(row);return row
def aeneas(llbc,dest,label):return run(label,[AENEAS,*FLAGS,'-dest',dest,llbc],WORK)
def model_text(template,kind):
    target='axiom external_double : Std.U32 → Result Std.U32'
    assert target in template
    if kind=='axiom':return template
    if kind=='concrete':repl='def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)'
    elif kind=='wrong':repl='def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x 2#u32)'
    elif kind=='missing':repl='-- external_double intentionally omitted'
    else:raise ValueError(kind)
    return template.replace(target,repl)
def setup_variant(name,generated,model):
    d=WORK/'variants'/name;(d/'Source').mkdir(parents=True)
    for part in ('Types','Funs'):shutil.copyfile(generated/f'{part}.lean',d/'Source'/f'{part}.lean')
    shutil.copyfile(generated/'Source.lean',d/'Source.lean')
    write(d/'Source/FunsExternal.lean',model);write(d/'Check.lean',CHECK)
    return d
def compile_variant(name,d):
    e=leanenv(d);rows=[]
    for m in ('Source/Types','Source/FunsExternal','Source/Funs','Source'):
        row=run(name+':compile:'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],d,e);rows.append(row)
        if row['rc']!=0:break
    check=None
    if len(rows)==4 and all(x['rc']==0 for x in rows):check=run(name+':check',[LEAN,'Check.lean'],d,e)
    return {'model_sha256':sha(d/'Source/FunsExternal.lean'),'generated_sha256':{
      x:sha(d/x) for x in ('Source/Types.lean','Source/Funs.lean','Source.lean')},
      'compile_rcs':[x['rc'] for x in rows],'compile_diagnostics':[
         {'stdout':x['stdout'],'stderr':x['stderr']} for x in rows],
      'check_rc':check['rc'] if check else None,'check_stdout':check['stdout'] if check else None,
      'check_stderr':check['stderr'] if check else None,'olean':{
      x:sha(d/x) for x in ('Source/Types.olean','Source/FunsExternal.olean','Source/Funs.olean','Source.olean') if (d/x).is_file()}}
def process_tree(root_pid):
    p=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,stat=,comm='],capture_output=True,text=True,check=True)
    rows=[]
    for line in p.stdout.splitlines():
        x=line.strip().split(None,4)
        if len(x)==5:rows.append({'pid':int(x[0]),'ppid':int(x[1]),
          'pgid':int(x[2]),'stat':x[3],'comm':x[4]})
    found={root_pid}
    while True:
        more={r['pid'] for r in rows if r['ppid'] in found}
        if more<=found:break
        found|=more
    return [r for r in rows if r['pid'] in found]
class Server:
    def __init__(self,label,root):
        self.label=label;self.root=root;self.n=10;self.buf=b'';self.diags={}
        self.p=subprocess.Popen([str(LEAN),'--server'],cwd=root,env=leanenv(root),
          stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,bufsize=0,start_new_session=True)
        log('start',server=label,pid=self.p.pid)
        self.send(dict(jsonrpc='2.0',id=1,method='initialize',params=dict(processId=os.getpid(),
          rootUri=root.as_uri(),capabilities={},initializationOptions={'hasWidgets':False})))
        self.until(1);self.send(dict(jsonrpc='2.0',method='initialized',params={}))
    def send(self,msg):
        raw=json.dumps(msg,separators=(',',':')).encode()
        self.p.stdin.write(b'Content-Length: '+str(len(raw)).encode()+b'\r\n\r\n'+raw);self.p.stdin.flush()
        log('client',server=self.label,message=msg)
    def read(self,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            if b'\r\n\r\n' in self.buf:
                header,body=self.buf.split(b'\r\n\r\n',1)
                sizes=[int(x.split(b':',1)[1]) for x in header.split(b'\r\n') if x.lower().startswith(b'content-length:')]
                if sizes and len(body)>=sizes[0]:
                    raw,self.buf=body[:sizes[0]],body[sizes[0]:]
                    msg=json.loads(raw);log('server',server=self.label,message=msg)
                    if msg.get('method')=='textDocument/publishDiagnostics':
                        self.diags[msg['params']['uri']]=msg['params']
                    if 'method' in msg and 'id' in msg:
                        self.send(dict(jsonrpc='2.0',id=msg['id'],result=None))
                    return msg
            ready,_,_=select.select([self.p.stdout],[],[],min(.1,max(0,end-time.monotonic())))
            if ready:
                chunk=os.read(self.p.stdout.fileno(),65536)
                if not chunk:break
                self.buf+=chunk
        raise TimeoutError(f'{self.label} read')
    def until(self,rid,timeout=15):
        end=time.monotonic()+timeout
        while time.monotonic()<end:
            msg=self.read(max(.1,end-time.monotonic()))
            if msg.get('id')==rid and 'method' not in msg:return msg
        raise TimeoutError(f'{self.label} id={rid}')
    def req(self,method,params,rid=None):
        if rid is None:rid=self.n;self.n+=1
        self.send(dict(jsonrpc='2.0',id=rid,method=method,params=params));return self.until(rid)
    def open(self,path,text,version=1):
        uri=path.as_uri();self.send(dict(jsonrpc='2.0',method='textDocument/didOpen',params={
          'textDocument':dict(uri=uri,languageId='lean',version=version,text=text)}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=version))
    def edit(self,uri,text,version):
        self.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={
          'textDocument':dict(uri=uri,version=version),'contentChanges':[dict(text=text)]}))
        return self.req('textDocument/waitForDiagnostics',dict(uri=uri,version=version))
    def stop(self):
        try:
            self.req('shutdown',None,rid=999);self.send(dict(jsonrpc='2.0',method='exit'));self.p.wait(timeout=5)
        except Exception as exc:
            log('stop_error',server=self.label,error=repr(exc))
            if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait(timeout=5)
        log('stop',server=self.label,pid=self.p.pid,rc=self.p.returncode,
          stderr=self.p.stderr.read().decode(errors='replace'))
def live_worker_control(concrete_dir,wrong_model):
    d=WORK/'live';shutil.copytree(concrete_dir,d)
    check=d/'Check.lean';old_text=check.read_text();uri=check.as_uri()
    s=Server('old-incarnation',d)
    try:
        initial=s.open(check,old_text,1);initial_diag=s.diags.get(uri)
        old_group_initial=process_tree(s.p.pid)
        before_olean={p:sha(d/p) for p in ('Source/FunsExternal.olean','Source/Funs.olean')}
        write(d/'Source/FunsExternal.lean',wrong_model)
        e=leanenv(d)
        recompiled=[]
        for m in ('Source/FunsExternal','Source/Funs','Source'):
            row=run('live:recompile:'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],d,e)
            recompiled.append(row);assert row['rc']==0,row
        after_olean={p:sha(d/p) for p in before_olean}
        edited=old_text+'-- proof document version 2 after external model replacement\n'
        write(check,edited);old_after=s.edit(uri,edited,2);old_after_diag=s.diags.get(uri)
        old_group_after=process_tree(s.p.pid)
        old_pid=s.p.pid
    finally:s.stop()
    fresh=Server('new-incarnation',d)
    try:
        new_after=fresh.open(check,check.read_text(),1);new_pid=fresh.p.pid
        new_diag=fresh.diags.get(uri);new_group=process_tree(fresh.p.pid)
    finally:fresh.stop()
    return {'old_pid':old_pid,'new_pid':new_pid,'old_initial':initial,'old_initial_diagnostics':initial_diag,
      'old_after_rebuild':old_after,'old_after_diagnostics':old_after_diag,
      'new_after_restart':new_after,'new_diagnostics':new_diag,
      'old_tree_initial':old_group_initial,'old_tree_after_rebuild':old_group_after,
      'new_tree':new_group,'before_olean':before_olean,'after_olean':after_olean,
      'external_model_sha256':sha(d/'Source/FunsExternal.lean'),'check_sha256':sha(check)}
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,AENEAS,LEAN):assert p.is_file(),p
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();src=WORK/'source.rs';write(src,SOURCE)
    llbc=WORK/'source.llbc';r=run('charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,
      '--',src,'--crate-type','lib','--crate-name','external_probe','--edition','2021'],WORK,rustenv());assert r['rc']==0,r
    assert json.loads(llbc.read_text())['has_errors'] is False
    generated=WORK/'generated';generated.mkdir();r=aeneas(llbc,generated,'aeneas:first');assert r['rc']==0,r
    generated_manifest=inventory(generated)
    template=(generated/'FunsExternal_Template.lean').read_text()
    variants={};dirs={}
    for kind in ('concrete','wrong','axiom','missing'):
        model=model_text(template,kind);d=setup_variant(kind,generated,model);dirs[kind]=d
        variants[kind]=compile_variant(kind,d)
    assert variants['concrete']['check_rc']==0
    assert variants['wrong']['check_rc']!=0 and variants['axiom']['check_rc']!=0
    assert variants['missing']['compile_rcs'][-1]!=0
    assert 'depends on axioms: [external_double]' in variants['axiom']['check_stdout']
    # Negative cache control: wrong source but stale concrete .olean files.
    stale=setup_variant('stale-cache',generated,model_text(template,'wrong'))
    for p in dirs['concrete'].rglob('*.olean'):
        dst=stale/p.relative_to(dirs['concrete']);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
    reused=run('stale-cache:check',[LEAN,'Check.lean'],stale,leanenv(stale));assert reused['rc']==0,reused
    cache={'generated_only_key':hashlib.sha256(''.join(x['sha256'] for x in generated_manifest.values()).encode()).hexdigest(),
      'candidate_external_model_sha256':sha(stale/'Source/FunsExternal.lean'),
      'loaded_external_olean_sha256':sha(stale/'Source/FunsExternal.olean'),
      'actual_concrete_external_model_sha256':variants['concrete']['model_sha256'],
      'wrong_fresh_check_rc':variants['wrong']['check_rc'],'stale_reuse_check_rc':reused['rc'],
      'stale_reuse_stdout':reused['stdout'],'stale_reuse_stderr':reused['stderr'],
      'generated_only_acceptance_invalid':True}
    # A second Aeneas run after model variants still emits exactly the same
    # generated source: Aeneas never read the separate Lean model file.
    again=WORK/'generated-again';again.mkdir();r=aeneas(llbc,again,'aeneas:again');assert r['rc']==0,r
    assert inventory(again)==generated_manifest
    live=live_worker_control(dirs['concrete'],model_text(template,'wrong'))
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'tools':{str(p):sha(p) for p in (CHARON,AENEAS,LEAN)},'source_sha256':sha(src),'llbc_sha256':sha(llbc),
      'generated':generated_manifest,'regenerated':inventory(again),'variants':variants,
      'cache_negative_control':cache,'live_workers':live,'commands':COMMANDS,'protocol':EVENTS,
      'external_kind':'separate Lean source file FunsExternal.lean, not an Aeneas compiled registry'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'commands':len(COMMANDS),'variants':{k:v['check_rc'] for k,v in variants.items()},
      'stale_cache':reused['rc'],'old_worker':live['old_pid'],'new_worker':live['new_pid']}))
if __name__=='__main__':main()
