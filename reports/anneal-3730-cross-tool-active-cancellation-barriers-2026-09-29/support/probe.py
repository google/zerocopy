#!/usr/bin/env python3
"""R20: deterministic active CLI cancellation; no Anneal scheduler is exercised."""
import hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon'; AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN=LEANROOT/'bin/lean'; LAKE=LEANROOT/'bin/lake'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
LOG=[]

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(p,s): p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def inventory(d):
    return {p.relative_to(d).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(d.rglob('*')) if p.is_file() and not p.is_fifo()}
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
        CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',RAYON_NUM_THREADS='1',
        PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def leanenv(compiled):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_PATH']=os.pathsep.join(str(p) for p in [compiled,*libs] if p.is_dir())
    e['LEAN_NUM_THREADS']='1';return e
def argv(a):return [str(x) for x in a]
def run(label,a,cwd,env=None,timeout=90):
    t=time.monotonic();p=subprocess.Popen(argv(a),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    try: out,err=p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=5)
    row={'label':label,'argv':argv(a),'cwd':str(cwd),'pid':p.pid,'rc':p.returncode,
         'ms':round((time.monotonic()-t)*1000,1),'stdout':out.decode(errors='replace'),'stderr':err.decode(errors='replace')}
    LOG.append(row);return row
def wait_for(p,path,timeout=30):
    t=time.monotonic()
    while time.monotonic()-t<timeout:
        if path.exists():return {'marker':str(path),'ms':round((time.monotonic()-t)*1000,1),'alive':p.poll() is None}
        if p.poll() is not None:break
        time.sleep(.02)
    raise RuntimeError(f'barrier not reached: {path}; rc={p.poll()}')
def pgmembers(pgid):
    ps=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,comm='],capture_output=True,text=True,check=True)
    rows=[]
    for line in ps.stdout.splitlines():
        parts=line.strip().split(None,3)
        if len(parts)==4 and parts[2]==str(pgid):rows.append({'pid':int(parts[0]),'ppid':int(parts[1]),'pgid':int(parts[2]),'comm':parts[3]})
    return rows
def kill_at(label,p,a,cwd,marker):
    gate=wait_for(p,marker);before=pgmembers(p.pid)
    assert gate['alive'] and before,(label,gate,before)
    os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=10);time.sleep(.1)
    after=pgmembers(p.pid)
    row={'label':label,'argv':argv(a),'cwd':str(cwd),'pid':p.pid,'barrier':gate,'members_before':before,
         'signal':'SIGKILL','rc':p.returncode,'stdout':out.decode(errors='replace'),
         'stderr':err.decode(errors='replace'),'members_after':after}
    LOG.append(row);assert not after,row;return row
def charon_cmd(src,dest):
    return [CHARON,'rustc','--preset','aeneas','--format','all','--dest-file',dest,
            '--',src,'--crate-type','lib','--crate-name','cancel_probe','--edition','2021']
def aeneas_cmd(llbc,dest):return [AENEAS,*FLAGS,'-dest',dest,llbc]
def make_source(path,n):write(path,f'#![allow(dead_code)]\npub fn inc(x: u32) -> u32 {{ x.wrapping_add({n}) }}\n')
def compile_generated(label,generated,expected):
    # The source name is Base/Current and determines generated import/module names.
    stem=label.capitalize();comp=WORK/f'lean-{label}';(comp/stem).mkdir(parents=True)
    for name in ('Types','Funs'):
        shutil.copyfile(generated/f'{name}.lean',comp/stem/f'{name}.lean')
    shutil.copyfile(generated/f'{stem}.lean',comp/f'{stem}.lean')
    env=leanenv(comp)
    for module in (f'{stem}/Types',f'{stem}/Funs',stem):
        r=run(f'{label}:lean:{module}',[LEAN,'-o',f'{module}.olean',f'{module}.lean'],comp,env)
        assert r['rc']==0,r
    write(comp/'Check.lean',f'import {stem}\nexample : cancel_probe.inc 0#u32 = .ok {expected}#u32 := by rfl\n#print axioms cancel_probe.inc\n')
    r=run(f'{label}:lean:oracle',[LEAN,'Check.lean'],comp,env)
    assert r['rc']==0 and 'sorryAx' not in r['stdout'],r
    return {'compiled':inventory(comp),'oracle_stdout':r['stdout']}
def aeneas_ready(label,llbc,expected):
    dest=WORK/f'{label}-generated';dest.mkdir()
    r=run(f'{label}:aeneas',aeneas_cmd(llbc,dest),WORK)
    assert r['rc']==0,r
    return {'generated':inventory(dest),'lean':compile_generated(label,dest,expected)}

def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for binary in (CHARON,AENEAS,LEAN,LAKE):assert binary.is_file(),binary
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();results={}
    # Pre-exec wrapper gate: only establishes cancellation before a CLI launch.
    pre=WORK/'pre';pre.mkdir();write(pre/'gate.py','import time\nfrom pathlib import Path\nPath("entered").write_text("1")\nwhile not Path("release").exists(): time.sleep(.01)\n')
    a=[sys.executable,'gate.py'];p=subprocess.Popen(a,cwd=pre,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    results['pre_exec']=kill_at('pre-exec-wrapper',p,a,pre,pre/'entered')
    results['pre_exec']['cli_started']=False
    # Charon is actively blocked when emitting its second serialization format.
    c=WORK/'charon';c.mkdir();src=c/'base.rs';make_source(src,1)
    base=c/'base';fifo=c/'base.llbc.postcard';os.mkfifo(fifo)
    a=charon_cmd(src,base);p=subprocess.Popen(argv(a),cwd=c,env=rustenv(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    marker=c/'base.llbc';results['charon_cancel']=kill_at('charon-after-json-before-postcard',p,a,c,marker)
    assert json.loads(marker.read_text())['has_errors'] is False
    results['charon_cancel']['json_sha256']=sha(marker)
    fifo.unlink();marker.unlink() # clean incomplete generation before retry
    r=run('charon-retry',a,c,rustenv());assert r['rc']==0,r
    assert marker.is_file() and fifo.is_file()
    r=run('charon-postcard-parse',[CHARON,'pretty-print','--format','postcard',fifo],c,rustenv())
    assert r['rc']==0,r
    results['charon_retry']={'artifacts':inventory(c),'json_valid':True,'postcard_parse_rc':r['rc']}
    # Aeneas is actively blocked opening Funs after Types has been written.
    ad=WORK/'aeneas-cancel';ad.mkdir();af=ad/'Funs.lean';os.mkfifo(af)
    a=aeneas_cmd(marker,ad);p=subprocess.Popen(argv(a),cwd=WORK,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    results['aeneas_cancel']=kill_at('aeneas-after-types-before-funs',p,a,WORK,ad/'Types.lean')
    results['aeneas_cancel']['partial']=inventory(ad)
    assert (ad/'Types.lean').is_file() and af.is_fifo()
    # Fresh private output; never accept interrupted files as a complete generation.
    results['aeneas_retry']=aeneas_ready('base',marker,1)
    # Lake/Lean barrier is inside B's tactic, after A's olean exists.
    lake=WORK/'lake';(lake/'Cancel').mkdir(parents=True)
    write(lake/'lean-toolchain','leanprover/lean4:v4.30.0-rc2\n')
    write(lake/'lakefile.lean','import Lake\nopen Lake DSL\npackage cancel_probe\nlean_lib Cancel\n')
    write(lake/'Cancel/A.lean','def seed : Nat := 7\n')
    write(lake/'Cancel/B.lean','import Cancel.A\nimport Lean\ntheorem gate : True := by\n  run_tac do\n    IO.FS.writeFile "gate.entered" "1"\n    while !(← (System.FilePath.mk "gate.release").pathExists) do\n      IO.sleep 10\n  exact True.intro\ndef chosen : Nat := seed + 1\n')
    e=dict(os.environ);e.update(ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',LEAN_NUM_THREADS='1')
    a=[LAKE,'--keep-toolchain','--no-cache','build','Cancel.B'];p=subprocess.Popen(argv(a),cwd=lake,env=e,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    results['lake_cancel']=kill_at('lake-lean-in-tactic-after-A-olean',p,a,lake,lake/'gate.entered')
    results['lake_cancel']['A_olean_exists']=(lake/'.lake/build/lib/lean/Cancel/A.olean').is_file()
    results['lake_cancel']['B_olean_exists']=(lake/'.lake/build/lib/lean/Cancel/B.olean').is_file()
    assert results['lake_cancel']['A_olean_exists'] and not results['lake_cancel']['B_olean_exists']
    write(lake/'gate.release','1');r=run('lake-retry',a,lake,e);assert r['rc']==0,r
    write(lake/'Check.lean','import Cancel.B\nexample : chosen = 8 := by rfl\n')
    r=run('lake-fresh-consumer',[LAKE,'--keep-toolchain','env',LEAN,'Check.lean'],lake,e)
    assert r['rc']==0,r
    results['lake_retry']={'artifacts':inventory(lake/'Cancel'),'A_olean_sha256':sha(lake/'.lake/build/lib/lean/Cancel/A.olean'),
                           'B_olean_sha256':sha(lake/'.lake/build/lib/lean/Cancel/B.olean'),'consumer_rc':r['rc']}
    # Experiment-side stage-completion fence. Old Aeneas CLI succeeds, then its
    # private wrapper is held. B completes Charon->Aeneas->Lean before A resumes.
    old=WORK/'old-job';old.mkdir();old_out=old/'generated';old_out.mkdir()
    wrapper=HERE/'gated_stage.py';a=[sys.executable,wrapper,AENEAS,marker,old_out,old/'entered',old/'release',WORK/'authority.json',old/'decision.json','1']
    write(WORK/'authority.json',json.dumps({'generation':1}))
    p=subprocess.Popen(argv(a),cwd=old,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    results['old_wait']=wait_for(p,old/'entered');assert results['old_wait']['alive']
    results['old_wait']['members']=pgmembers(p.pid)
    results['old_wait']['aeneas_transcript']=json.loads((old/'entered').read_text())
    new=WORK/'new';new.mkdir();make_source(new/'current.rs',2)
    # Name `current` is carried through generated module names.
    llbc=new/'current.llbc';r=run('new:charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,
        '--',new/'current.rs','--crate-type','lib','--crate-name','cancel_probe','--edition','2021'],new,rustenv())
    assert r['rc']==0,r
    results['new_complete']=aeneas_ready('current',llbc,2)
    write(WORK/'authority.json',json.dumps({'generation':2,'accepted':'current'}))
    write(old/'release','1');out,err=p.communicate(timeout=10)
    results['late_fence']={'wrapper_argv':argv(a),'wrapper_rc':p.returncode,'stdout':out.decode(errors='replace'),
        'stderr':err.decode(errors='replace'),'decision':json.loads((old/'decision.json').read_text()),
        'old_generated':inventory(old_out),'authority':json.loads((WORK/'authority.json').read_text()),
        'old_job_is_cli_success_then_wrapper_wait':True}
    assert p.returncode==0 and results['late_fence']['decision']['publish'] is False
    binaries={str(p):sha(p) for p in (CHARON,AENEAS,LEAN,LAKE)}
    result={'schema':1,'tools':binaries,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        'results':results,'commands':LOG,'fixture_hashes':{'rust_base':sha(src),'rust_new':sha(new/'current.rs'),
            'lake_B':sha(lake/'Cancel/B.lean'),'gated_stage':sha(wrapper)}}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'cases':list(results),'commands':len(LOG)},indent=2))
if __name__=='__main__':main()
