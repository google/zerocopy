#!/usr/bin/env python3
"""R25: A -> broken-signature intent -> supported B recovery with actual CLIs."""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
A='#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(1) }\n'
FAILED='#![allow(dead_code)]\npub fn inc(x: u64) -> u64 { x.wrapping_add(2) }\npub fn broken(\n'
B='#![allow(dead_code)]\npub fn inc(x: u64) -> u64 { x.wrapping_add(2) }\n'
OLD_GOAL='recovery_probe.inc 0#u32 = .ok 1#u32'
NEW_GOAL='recovery_probe.inc 0#u64 = .ok 2#u64'
PROOFS={
 'A-initial':f'import Current\nexample : {OLD_GOAL} := by rfl\n',
 'A-provisional':f'import Current\nexample : {OLD_GOAL} := by\n  have h : {OLD_GOAL} := by rfl\n  exact h\n',
 'B-old-assumptions':f'import Recovery\nexample : {OLD_GOAL} := by rfl\n',
 'B-adapted':f'import Recovery\nexample : {NEW_GOAL} := by rfl\n'}
COMMANDS=[];EVENTS=[]
def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inventory(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
  for p in sorted(root.rglob('*')) if p.is_file()}
def event(name,**kw):EVENTS.append({'seq':len(EVENTS),'name':name,**kw})
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
         'ms':round((time.monotonic()-t)*1000,1),'stdout':p.stdout,'stderr':p.stderr}
    COMMANDS.append(row);return row
def charon(src,out,label):return run(label,[CHARON,'rustc','--preset','aeneas','--dest-file',out,
  '--',src,'--crate-type','lib','--crate-name','recovery_probe','--edition','2021'],WORK,rustenv())
def aeneas(llbc,dest,label):return run(label,[AENEAS,*FLAGS,'-dest',dest,llbc],WORK)
def compile_model(name,generated):
    c=WORK/f'model-{name}';(c/name).mkdir(parents=True)
    for m in ('Types','Funs'):shutil.copyfile(generated/f'{m}.lean',c/name/f'{m}.lean')
    shutil.copyfile(generated/f'{name}.lean',c/f'{name}.lean')
    e=leanenv(c)
    for m in (f'{name}/Types',f'{name}/Funs',name):
        r=run(f'{name}:compile:{m}',[LEAN,'-o',f'{m}.olean',f'{m}.lean'],c,e);assert r['rc']==0,r
    return c
def signature(generated):
    text=(generated/'Funs.lean').read_text()
    m=re.search(r'^def inc \(x : ([^)]+)\) : Result ([^ ]+) := do$',text,re.M)
    assert m,text
    return {'input':m.group(1),'output':m.group(2),'line':m.group(0)}
def proof(c,key,label):
    text=PROOFS[key];write(WORK/'proof-snapshots'/f'{key}.lean',text);write(c/'Proof.lean',text)
    r=run(label,[LEAN,'Proof.lean'],c,leanenv(c))
    return {'proof':key,'proof_sha256':sha(c/'Proof.lean'),'rc':r['rc'],
            'stdout':r['stdout'],'stderr':r['stderr']}
def model_id(rust,llbc,generated):
    return hashlib.sha256((rust+llbc+''.join(x['sha256'] for x in generated.values())).encode()).hexdigest()
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,AENEAS,LEAN):assert p.is_file(),p
    assert (BACKEND/'.lake/build/lib/lean/Aeneas.olean').is_file()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();src=WORK/'source.rs';snaps=WORK/'source-snapshots';snaps.mkdir()
    write(src,A);write(snaps/'A.rs',A);rust_A=sha(src)
    llbc_A=WORK/'current.llbc';r=charon(src,llbc_A,'A:charon');assert r['rc']==0,r
    assert json.loads(llbc_A.read_text())['has_errors'] is False
    out_A=WORK/'generated-A';out_A.mkdir();r=aeneas(llbc_A,out_A,'A:aeneas');assert r['rc']==0,r
    gen_A=inventory(out_A);sig_A=signature(out_A);assert sig_A['input']=='Std.U32'
    mod_A=compile_model('Current',out_A);pa=proof(mod_A,'A-initial','A:initial-proof');assert pa['rc']==0,pa
    llbc_A_sha=sha(llbc_A);id_A=model_id(rust_A,llbc_A_sha,gen_A)
    event('publish-A-current',rust_sha256=rust_A,model_id=id_A,proof_sha256=pa['proof_sha256'])
    # Intent has switched to u64/+2, but Rust cannot compile; old bytes remain.
    write(src,FAILED);write(snaps/'failed.rs',FAILED);rust_failed=sha(src)
    r=charon(src,llbc_A,'failure:charon');assert r['rc']!=0 and sha(llbc_A)==llbc_A_sha
    failed_charon_rc=r['rc']
    old_llbc_sha=llbc_A_sha
    event('current-rust-failed',rust_sha256=rust_failed,retained_model_id=id_A)
    provisional=proof(mod_A,'A-provisional','failure:last-good-proof');assert provisional['rc']==0,provisional
    fail_policies={
      'stop':{'query_performed':False,'feedback':'unavailable: current Rust failed',
              'current_verified':False,'requested_rust_sha256':rust_failed},
      'last_good':{'query_performed':True,'feedback':'provisional: model A',
                   'freshness':'stale','current_verified':False,'requested_rust_sha256':rust_failed,
                   'model_rust_sha256':rust_A,'model_id':id_A,'query':provisional}}
    event('old-model-query-provisional',requested_rust_sha256=rust_failed,model_id=id_A,
          proof_sha256=provisional['proof_sha256'],current_verified=False)
    # Recovery: fresh supported u64 model B, new root and output directory.
    write(src,B);write(snaps/'B.rs',B);rust_B=sha(src)
    llbc_B=WORK/'recovery.llbc';r=charon(src,llbc_B,'B:charon');assert r['rc']==0,r
    assert json.loads(llbc_B.read_text())['has_errors'] is False
    out_B=WORK/'generated-B';out_B.mkdir();r=aeneas(llbc_B,out_B,'B:aeneas');assert r['rc']==0,r
    gen_B=inventory(out_B);sig_B=signature(out_B);assert sig_B['input']=='Std.U64' and sig_B!=sig_A
    mod_B=compile_model('Recovery',out_B);id_B=model_id(rust_B,sha(llbc_B),gen_B);assert id_A!=id_B
    event('publish-B-current-stop-provisional',rust_sha256=rust_B,model_id=id_B,prior_model_id=id_A)
    old_against_B=proof(mod_B,'B-old-assumptions','B:old-assumptions');assert old_against_B['rc']!=0,old_against_B
    adapted=proof(mod_B,'B-adapted','B:adapted-proof');assert adapted['rc']==0,adapted
    event('B-current-proof-accepted',rust_sha256=rust_B,model_id=id_B,proof_sha256=adapted['proof_sha256'])
    # Negative control: old A still proves old statement after B exists.
    late_old=proof(mod_A,'A-provisional','B:late-A-control');assert late_old['rc']==0,late_old
    event('late-A-result-rejected-as-current',requested_rust_sha256=rust_B,
          actual_model_id=id_A,current_model_id=id_B,query_rc=late_old['rc'],current_verified=False)
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'tools':{str(p):sha(p) for p in (CHARON,AENEAS,LEAN)},'source_snapshots':inventory(snaps),
      'proof_snapshots':inventory(WORK/'proof-snapshots'),
      'A':{'rust_sha256':rust_A,'llbc_sha256':old_llbc_sha,'generated':gen_A,'signature':sig_A,
           'model_id':id_A,'initial_proof':pa},
      'failure':{'rust_sha256':rust_failed,'charon_rc':failed_charon_rc,'retained_llbc_sha256':old_llbc_sha,
                 'policies':fail_policies},
      'B':{'rust_sha256':rust_B,'llbc_sha256':sha(llbc_B),'generated':gen_B,'signature':sig_B,
           'model_id':id_B,'old_assumptions':old_against_B,'adapted':adapted,
           'freshness':'current','current_model_proof_accepted':True,
           'provisional_stopped_at':'publish-B-current-stop-provisional',
           'late_A':{'query':late_old,'actual_model_id':id_A,'current_model_id':id_B,
                     'current_verified':False}},
      'events':EVENTS,'commands':COMMANDS,
      'policy_origin':'experiment-side freshness/promotion; no Anneal implementation'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'commands':len(COMMANDS),'A':sig_A,'B':sig_B,
      'old_on_B_rc':old_against_B['rc'],'adapted_on_B_rc':adapted['rc']}))
if __name__=='__main__':main()
