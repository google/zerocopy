#!/usr/bin/env python3
"""R22 direct CLI signal escalation at deterministic active-stage barriers."""
import fcntl, gzip, hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN=LEANROOT/'bin/lean';LAKE=LEANROOT/'bin/lake'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
COMMANDS=[]

def write(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inv(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
    for p in sorted(root.rglob('*')) if p.is_file() and not p.is_fifo()}
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',RAYON_NUM_THREADS='1',
      PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def leanenv(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_NUM_THREADS']='1';e['LEAN_PATH']=os.pathsep.join(str(p) for p in [comp,*libs] if p.is_dir())
    return e
def av(a):return [str(x) for x in a]
def run(label,a,cwd,env=None,timeout=90):
    t=time.monotonic();p=subprocess.Popen(av(a),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    try:out,err=p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=5)
    r={'label':label,'argv':av(a),'cwd':str(cwd),'pid':p.pid,'rc':p.returncode,
       'ms':round((time.monotonic()-t)*1000,1),'stdout':out.decode(errors='replace'),'stderr':err.decode(errors='replace')}
    COMMANDS.append(r);return r
def members(pgid):
    p=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,stat=,comm='],capture_output=True,text=True,check=True)
    rows=[]
    for line in p.stdout.splitlines():
        parts=line.strip().split(None,4)
        if len(parts)==5 and parts[2]==str(pgid):rows.append({'pid':int(parts[0]),'ppid':int(parts[1]),'pgid':int(parts[2]),'stat':parts[3],'comm':parts[4]})
    return rows
def live(pgid):return [r for r in members(pgid) if not r['stat'].startswith('Z')]
def fds(rows):
    # Preserve raw lsof descriptor/type/name/lock fields; lack of a listed lock
    # cannot rule out every kernel or external lock mechanism.
    out=[]
    for row in rows:
        p=subprocess.run(['lsof','-nP','-p',str(row['pid'])],capture_output=True,text=True,timeout=5)
        out.append({'pid':row['pid'],'rc':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
    return out
def flock_probe(path):
    try:
        with open(path,'rb') as f:
            try:
                fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)
                fcntl.flock(f,fcntl.LOCK_UN)
                return {'path':str(path),'exclusive_flock_obtained':True}
            except BlockingIOError:return {'path':str(path),'exclusive_flock_obtained':False}
    except OSError as ex:return {'path':str(path),'error':str(ex)}
def await_marker(p,marker,timeout=30):
    t=time.monotonic()
    while time.monotonic()-t<timeout:
        if marker.exists() and p.poll() is None:return round((time.monotonic()-t)*1000,1)
        if p.poll() is not None:break
        time.sleep(.02)
    raise RuntimeError(f'active barrier missed {marker} rc={p.poll()}')
def stop(label,a,cwd,env,marker,lockpath,first_signal):
    p=subprocess.Popen(av(a),cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    entered_ms=await_marker(p,marker)
    before=members(p.pid);assert before
    sample={'members':before,'lsof':fds(before),'flock':flock_probe(lockpath),'output_at_gate':inv(cwd)}
    timeline=[]
    for sig in ([first_signal,signal.SIGTERM,signal.SIGKILL] if first_signal!=signal.SIGKILL else [signal.SIGKILL]):
        active=live(p.pid)
        if not active:break
        t=time.monotonic()
        try:os.killpg(p.pid,sig)
        except (ProcessLookupError,PermissionError):
            # A group containing only terminating/zombie members may disappear
            # between ps and killpg on macOS. Retain the race explicitly.
            if live(p.pid):raise
            timeline.append({'signal':signal.Signals(sig).name,'race':'group gone before send','members_after_grace':members(p.pid)})
            break
        for _ in range(50):
            if not live(p.pid):break
            time.sleep(.02)
        timeline.append({'signal':signal.Signals(sig).name,'ms_after_send':round((time.monotonic()-t)*1000,1),
                         'members_after_grace':members(p.pid)})
    if live(p.pid):
        os.killpg(p.pid,signal.SIGKILL);time.sleep(.1)
        timeline.append({'signal':'SIGKILL-final','members_after_grace':members(p.pid)})
    out,err=p.communicate(timeout=5)
    time.sleep(.1);after=members(p.pid)
    r={'label':label,'argv':av(a),'cwd':str(cwd),'pid':p.pid,'barrier':str(marker),'entered_ms':entered_ms,
       'first_signal':signal.Signals(first_signal).name,'before':sample,'timeline':timeline,'rc':p.returncode,
       'stdout':out.decode(errors='replace'),'stderr':err.decode(errors='replace'),
       'after':{'members':after,'lsof':fds(after),'flock':flock_probe(lockpath),'output':inv(cwd)}}
    COMMANDS.append(r)
    assert not [m for m in after if not m['stat'].startswith('Z')] and p.returncode!=0,r
    return r
def charon_cmd(src,base):return [CHARON,'rustc','--preset','aeneas','--format','all','--dest-file',base,
    '--',src,'--crate-type','lib','--crate-name','signal_probe','--edition','2021']
def aeneas_cmd(llbc,dest):return [AENEAS,*FLAGS,'-dest',dest,llbc]
def check_lean(case,generated):
    # Generated module stem `Input` comes from input.llbc.
    c=case/'consumer';(c/'Input').mkdir(parents=True)
    for m in ('Types','Funs'):shutil.copyfile(generated/f'{m}.lean',c/'Input'/f'{m}.lean')
    shutil.copyfile(generated/'Input.lean',c/'Input.lean')
    e=leanenv(c)
    for m in ('Input/Types','Input/Funs','Input'):
        r=run('lean:'+str(case.name)+':'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],c,e);assert r['rc']==0,r
    write(c/'Check.lean','import Input\nexample : signal_probe.inc 0#u32 = .ok 1#u32 := by rfl\n')
    r=run('lean:'+str(case.name)+':oracle',[LEAN,'Check.lean'],c,e)
    assert r['rc']==0,r
    return {'oracle_rc':r['rc'],'generated':inv(generated),'consumer':inv(c)}
def lake_case(label,sig):
    d=WORK/label;(d/'Cancel').mkdir(parents=True)
    write(d/'lean-toolchain','leanprover/lean4:v4.30.0-rc2\n')
    write(d/'lakefile.lean','import Lake\nopen Lake DSL\npackage signal_probe\nlean_lib Cancel\n')
    write(d/'Cancel/A.lean','def seed : Nat := 7\n')
    write(d/'Cancel/B.lean','import Cancel.A\nimport Lean\ntheorem gate : True := by\n  run_tac do\n    IO.FS.writeFile "gate.entered" "1"\n    while !(← (System.FilePath.mk "gate.release").pathExists) do\n      IO.sleep 10\n  exact True.intro\ndef chosen : Nat := seed + 1\n')
    e=dict(os.environ);e.update(ELAN_TOOLCHAIN='leanprover/lean4:v4.30.0-rc2',LEAN_NUM_THREADS='1')
    a=[LAKE,'--keep-toolchain','--no-cache','build','Cancel.B']
    row=stop(label+':active',a,d,e,d/'gate.entered',d/'.lake/build/lib/lean/Cancel/A.olean',sig)
    row['A_olean_exists']=(d/'.lake/build/lib/lean/Cancel/A.olean').is_file()
    row['B_olean_exists']=(d/'.lake/build/lib/lean/Cancel/B.olean').is_file()
    assert row['A_olean_exists'] and not row['B_olean_exists']
    write(d/'gate.release','1');r=run(label+':same-dir-retry',a,d,e);assert r['rc']==0,r
    write(d/'Check.lean','import Cancel.B\nexample : chosen = 8 := by rfl\n')
    r=run(label+':fresh-consumer',[LAKE,'--keep-toolchain','env',LEAN,'Check.lean'],d,e);assert r['rc']==0,r
    return {'cancel':row,'retry_rc':0,'consumer_rc':r['rc'],'B_olean_sha256':sha(d/'.lake/build/lib/lean/Cancel/B.olean')}
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,AENEAS,LEAN,LAKE):assert p.is_file()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();source=WORK/'input.rs';write(source,'#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(1) }\n')
    # First obtain one complete LLBC input for the Aeneas cases.
    baseline=WORK/'baseline';baseline.mkdir()
    base=baseline/'input';r=run('baseline:charon',charon_cmd(source,base),baseline,rustenv());assert r['rc']==0,r
    llbc=baseline/'input.llbc';assert json.loads(llbc.read_text())['has_errors'] is False
    result={'charon':{},'aeneas':{},'lake':{}}
    for label,sig in [('graceful',signal.SIGINT),('kill-control',signal.SIGKILL)]:
        d=WORK/('charon-'+label);d.mkdir();base=d/'input';fifo=d/'input.llbc.postcard';os.mkfifo(fifo)
        a=charon_cmd(source,base)
        row=stop('charon:'+label+':active',a,d,rustenv(),d/'input.llbc',d/'input.llbc',sig)
        partial=d/'input.llbc';assert json.loads(partial.read_text())['has_errors'] is False
        row['partial_json_sha256']=sha(partial)
        fifo.unlink() # remove blocked artifact, retain and overwrite parseable partial JSON
        r=run('charon:'+label+':same-dir-retry',a,d,rustenv());assert r['rc']==0,r
        assert json.loads(partial.read_text())['has_errors'] is False and fifo.is_file()
        r=run('charon:'+label+':postcard-parse',[CHARON,'pretty-print','--format','postcard',fifo],d,rustenv())
        assert r['rc']==0,r
        result['charon'][label]={'cancel':row,'retry_rc':0,'postcard_parse_rc':0,'complete':inv(d)}
    for label,sig in [('graceful',signal.SIGTERM),('kill-control',signal.SIGKILL),
                      ('escalation-control',signal.SIGINT)]:
        d=WORK/('aeneas-'+label);d.mkdir();fifo=d/'Funs.lean';os.mkfifo(fifo)
        actual=aeneas_cmd(llbc,d)
        a=([sys.executable,HERE/'ignore_int_supervisor.py',*actual]
           if label=='escalation-control' else actual)
        row=stop('aeneas:'+label+':active',a,d,None,d/'Types.lean',d/'Types.lean',sig)
        assert (d/'Types.lean').is_file() and fifo.is_fifo()
        row['partial_types_sha256']=sha(d/'Types.lean')
        fifo.unlink() # retain Types but retry in exact same output directory
        r=run('aeneas:'+label+':same-dir-retry',actual,d);assert r['rc']==0,r
        oracle=check_lean(d,d)
        result['aeneas'][label]={'cancel':row,'retry_rc':0,'oracle':oracle}
    for label,sig in [('graceful',signal.SIGINT),('kill-control',signal.SIGKILL)]:
        result['lake'][label]=lake_case('lake-'+label,sig)
    data={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
          'tool_hashes':{str(p):sha(p) for p in (CHARON,AENEAS,LEAN,LAKE)},
          'fixture_sha256':sha(source),'results':result,'commands':COMMANDS}
    with gzip.open(HERE/'results.json.gz','wt',compresslevel=9) as f:
        json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'ok':True,'cases':{k:list(v) for k,v in result.items()},'commands':len(COMMANDS)},indent=2))
if __name__=='__main__':main()
