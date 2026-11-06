#!/usr/bin/env python3
"""I023: actual pinned pipeline plus explicit experiment-side freshness policies."""
import hashlib,json,os,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
GOOD='#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(1) }\n'
SYNTAX='#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(2) }\npub fn broken(\n'
UNSUPPORTED='#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(2) }\n'+\
            'pub unsafe fn bad(ptr: *const u32) -> u32 { *ptr }\n'
GOAL='last_good_probe.inc 0#u32 = .ok 1#u32'
PROOFS={
 'v1':f'import Current\nexample : {GOAL} := by rfl\n',
 'v2':f'import Current\nexample : {GOAL} := by\n  have h : {GOAL} := by rfl\n  exact h\n',
 'v3':f'import Current\nexample : {GOAL} := by\n  have h : {GOAL} := rfl\n  simpa using h\n'}
COMMANDS=[]

def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inventory(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
    for p in sorted(root.rglob('*')) if p.is_file()}
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',
      PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def leanenv(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_PATH']=os.pathsep.join(str(p) for p in [comp,*libs] if p.is_dir());e['LEAN_NUM_THREADS']='1'
    return e
def run(label,argv,cwd,env=None,timeout=90):
    a=list(map(str,argv));t=time.monotonic()
    p=subprocess.run(a,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
    r={'label':label,'argv':a,'cwd':str(cwd),'rc':p.returncode,'ms':round((time.monotonic()-t)*1000,1),
       'stdout':p.stdout,'stderr':p.stderr}
    COMMANDS.append(r);return r
def charon(src,out,label):
    return run(label,[CHARON,'rustc','--preset','aeneas','--dest-file',out,
       '--',src,'--crate-type','lib','--crate-name','last_good_probe','--edition','2021'],WORK,rustenv())
def aeneas(llbc,dest,label):return run(label,[AENEAS,*FLAGS,'-dest',dest,llbc],WORK)
def compile_old_model(generated):
    comp=WORK/'old-model';(comp/'Current').mkdir(parents=True)
    for m in ('Types','Funs'):shutil.copyfile(generated/f'{m}.lean',comp/'Current'/f'{m}.lean')
    shutil.copyfile(generated/'Current.lean',comp/'Current.lean')
    e=leanenv(comp)
    for m in ('Current/Types','Current/Funs','Current'):
        r=run('compile-old:'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],comp,e);assert r['rc']==0,r
    return comp
def proof_query(comp,version,label):
    write(WORK/'proof-snapshots'/f'{version}.lean',PROOFS[version])
    write(comp/'Proof.lean',PROOFS[version])
    r=run(label,[LEAN,'Proof.lean'],comp,leanenv(comp))
    return {'proof_version':version,'proof_sha256':sha(comp/'Proof.lean'),'lean_rc':r['rc'],
            'lean_stdout':r['stdout'],'lean_stderr':r['stderr']}
def policies(failure_kind,current_rust_sha,old_rust_sha,old_model_id,old_model,proof_version):
    # These are intentionally simple experiment-side API policies, not Anneal.
    stop={'mode':'stop-interaction','rust_status':failure_kind,'query_performed':False,
          'feedback':'unavailable: current Rust model failed','current_verified':False,
          'requested_rust_sha256':current_rust_sha,'old_model_rust_sha256':old_rust_sha}
    query=proof_query(old_model,proof_version,f'last-good:{failure_kind}:proof-{proof_version}')
    assert query['lean_rc']==0,query
    last={'mode':'explicit-last-good','rust_status':failure_kind,'query_performed':True,
          'feedback':'provisional: evaluated against last-good Rust model',
          'freshness':'stale','current_verified':False,'model_id':old_model_id,
          'requested_rust_sha256':current_rust_sha,'model_rust_sha256':old_rust_sha,
          'query':query}
    assert current_rust_sha!=old_rust_sha and not stop['current_verified'] and not last['current_verified']
    return {'stop':stop,'last_good':last,'naive_exit_zero_would_mislabel_current':query['lean_rc']==0}
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,AENEAS,LEAN):assert p.is_file(),p
    assert (BACKEND/'.lake/build/lib/lean/Aeneas.olean').is_file()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();snap=WORK/'snapshots';snap.mkdir()
    source=WORK/'source.rs';write(source,GOOD);write(snap/'A-good.rs',GOOD)
    rust_A=sha(source);llbc=WORK/'current.llbc';r=charon(source,llbc,'A:charon');assert r['rc']==0,r
    llbc_A=sha(llbc);assert json.loads(llbc.read_text())['has_errors'] is False
    generated=WORK/'generated-A';generated.mkdir();r=aeneas(llbc,generated,'A:aeneas');assert r['rc']==0,r
    generated_A=inventory(generated);old=compile_old_model(generated)
    initial=proof_query(old,'v1','A:proof-v1');assert initial['lean_rc']==0,initial
    model_id=hashlib.sha256((rust_A+llbc_A+''.join(x['sha256'] for x in generated_A.values())).encode()).hexdigest()
    baseline={'rust_sha256':rust_A,'llbc_sha256':llbc_A,'generated':generated_A,
              'old_compiled':inventory(old),'model_id':model_id,'proof':initial,
              'current_verified':True,'freshness':'current'}
    # Same LLBC destination survives a failed Rust compile: old bytes are not a new model.
    write(source,SYNTAX);write(snap/'B-syntax.rs',SYNTAX);rust_B=sha(source)
    r=charon(source,llbc,'B:charon-syntax-error');assert r['rc']!=0,r
    assert sha(llbc)==llbc_A
    syntax={'rust_sha256':rust_B,'charon_rc':r['rc'],'llbc_path_still_exists':llbc.is_file(),
            'retained_llbc_sha256':sha(llbc),'policies':policies('rust-syntax-error',rust_B,rust_A,model_id,old,'v2')}
    # A compilable Rust revision can still fail at Aeneas with partial Lean output.
    write(source,UNSUPPORTED);write(snap/'C-unsupported.rs',UNSUPPORTED);rust_C=sha(source)
    candidate=WORK/'candidate.llbc';r=charon(source,candidate,'C:charon');assert r['rc']==0,r
    assert json.loads(candidate.read_text())['has_errors'] is False
    partial=WORK/'generated-C-partial';partial.mkdir();r=aeneas(candidate,partial,'C:aeneas-unsupported')
    assert r['rc']!=0 and (partial/'Funs.lean').is_file() and 'sorry' in (partial/'Funs.lean').read_text(),r
    unsupported={'rust_sha256':rust_C,'candidate_llbc_sha256':sha(candidate),'aeneas_rc':r['rc'],
       'partial_generated':inventory(partial),'partial_contains_sorry':True,
       'policies':policies('unsupported-extraction',rust_C,rust_A,model_id,old,'v3')}
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
       'tools':{str(p):sha(p) for p in (CHARON,AENEAS,LEAN)},'baseline':baseline,
       'syntax_failure':syntax,'unsupported_extraction':unsupported,
       'source_snapshots':inventory(snap),'proof_snapshots':inventory(WORK/'proof-snapshots'),
       'commands':COMMANDS,
       'policy_origin':'experiment-side; not Anneal or tool-generated freshness metadata'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'commands':len(COMMANDS),'baseline':initial['lean_rc'],
                      'syntax':syntax['charon_rc'],'unsupported':unsupported['aeneas_rc']}))
if __name__=='__main__':main()
