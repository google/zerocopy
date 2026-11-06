#!/usr/bin/env python3
"""Private CLI invocation-boundary cancellation, descendant and retry controls."""
import argparse,hashlib,json,os,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
RLIB=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
LEANBIN=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin'
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RESULT=HERE/'results.json'

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inv(root):
    if not root.exists():return {}
    return {str(p.relative_to(root)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.rglob('*')) if p.is_file()}
def group_members(pgid):
    run=subprocess.run(['/bin/ps','-axo','pid=,ppid=,pgid=,stat=,rss=,comm='],capture_output=True,text=True,timeout=5)
    out=[]
    for line in run.stdout.splitlines():
        v=line.split(None,5)
        if len(v)==6 and v[2]==str(pgid):out.append({'pid':int(v[0]),'ppid':int(v[1]),'pgid':int(v[2]),'stat':v[3],'rss_kib':int(v[4]),'comm':v[5]})
    return out
def surviving_recorded_pids(members):
    if not members:return []
    pids={x['pid'] for x in members}
    run=subprocess.run(['/bin/ps','-axo','pid='],capture_output=True,text=True,timeout=5)
    present={int(x.strip()) for x in run.stdout.splitlines() if x.strip().isdigit()}
    return sorted(pids & present)
def runner(label,cwd,cmd,env,output_root,work,delay_ms=0):
    def norm(s):return str(s).replace(str(work),'$WORK').replace(str(TOOLS),'$TOOLS').replace(str(HERE),'$REPORT')
    prior=inv(output_root)
    start=time.monotonic()
    p=subprocess.Popen([str(x) for x in cmd],cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                       text=True,start_new_session=True)
    # Popen has confirmed exec; stop the actual CLI group at the invocation
    # boundary, inspect members, then kill the complete group.
    if delay_ms:time.sleep(delay_ms/1000)
    live=p.poll() is None
    if live:
        os.killpg(p.pid,signal.SIGSTOP)
    stopped=group_members(p.pid) if live else []
    if live:os.killpg(p.pid,signal.SIGKILL)
    stdout,stderr=p.communicate(timeout=10)
    time.sleep(.05)
    remaining=group_members(p.pid)
    surviving=surviving_recorded_pids(stopped)
    after_cancel=inv(output_root)
    retry_start=time.monotonic()
    retry=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,capture_output=True,text=True,timeout=60)
    after_retry=inv(output_root)
    return {'stage':label,'delay_before_stop_ms':delay_ms,'cwd':norm(cwd),'argv':[norm(x) for x in cmd],
            'cancel':{'signal':'SIGSTOP then SIGKILL' if live else 'process completed before stop',
                      'stopped_group':stopped,'exit':p.returncode,'seconds':round(time.monotonic()-start,4),
                      'stdout':norm(stdout),'stderr':norm(stderr),'remaining_group':remaining,
                      'surviving_recorded_pids':surviving,
                      'output_before':prior,'output_after':after_cancel},
            'retry':{'exit':retry.returncode,'seconds':round(time.monotonic()-retry_start,4),
                     'stdout':norm(retry.stdout),'stderr':norm(retry.stderr),'output_after':after_retry}}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose an absent owned work directory'
    assert shutil.disk_usage(work.parent).free>=15*(1<<30),'15 GiB free-disk guard'
    work.mkdir();(work/'home').mkdir()
    rust_env=dict(os.environ);rust_env.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
        'CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
        'CHARON_TOOLCHAIN_IS_IN_PATH':'1','BUILD_VALUE':'7','PROC_VALUE':'3','PROBE_ENV':'A',
        'PATH':os.pathsep.join([str(RUST),str(TOOLS/'bin'),os.environ.get('PATH','')]),
        'DYLD_LIBRARY_PATH':os.pathsep.join([str(RLIB),str(RLIB/'rustlib/aarch64-apple-darwin/lib')])})
    lean_env=dict(os.environ);lean_env.update({'ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2','LEAN_NUM_THREADS':'1',
        'HOME':str(work/'home'),'LAKE_ARTIFACT_CACHE':'false',
        'PATH':os.pathsep.join([str(LEANBIN),os.environ.get('PATH','')])})
    src=work/'cargo-source';shutil.copytree(HERE/'cargo-fixture',src)
    stages=[]
    cargo_target=work/'cargo-target';env=dict(rust_env,CARGO_TARGET_DIR=str(cargo_target))
    stages.append(runner('cargo',src,[RUST/'cargo','build','--offline','--locked','--manifest-path',src/'Cargo.toml','--package','app_closure','--lib'],env,cargo_target,work))
    charon_target=work/'charon-target';charon_out=work/'charon-output';charon_out.mkdir();env=dict(rust_env,CARGO_TARGET_DIR=str(charon_target))
    stages.append(runner('charon',src,[CHARON,'cargo','--preset','aeneas','--dest-file',charon_out/'app.llbc','--',
        '--manifest-path',src/'Cargo.toml','--package','app_closure','--lib','--offline','--locked','-v'],env,charon_out,work))
    aeneas_out=work/'aeneas-output';aeneas_out.mkdir()
    stages.append(runner('aeneas',work,[AENEAS,'-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry',
        '-dest',aeneas_out,HERE/'aeneas-input.llbc'],dict(os.environ),aeneas_out,work))
    lake_root=work/'lake-source';lake_root.mkdir();(lake_root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
    (lake_root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage cancellation_probe\n@[default_target]\nlean_lib Probe\n')
    (lake_root/'Probe.lean').write_text('def value : Nat := 7\ntheorem proof : value = 7 := by decide\n')
    stages.append(runner('lake',lake_root,[LEANBIN/'lake','--keep-toolchain','--no-cache','build','Probe'],lean_env,lake_root/'.lake',work))
    lean_root=work/'lean-output';lean_root.mkdir();(lean_root/'Check.lean').write_text('def value : Nat := 7\n#check value\n')
    stages.append(runner('lean',lean_root,[LEANBIN/'lean','--json',lean_root/'Check.lean'],lean_env,lean_root/'build-output',work))
    # These three cold, separate outputs allow bounded cancellation after
    # subprocess work begins; never share their writable targets with retries
    # of the earlier trials.
    cargo_active=work/'cargo-active-target';env=dict(rust_env,CARGO_TARGET_DIR=str(cargo_active))
    stages.append(runner('cargo-active',src,[RUST/'cargo','build','--offline','--locked','--manifest-path',src/'Cargo.toml',
        '--package','app_closure','--lib'],env,cargo_active,work,delay_ms=80))
    charon_active_target=work/'charon-active-target';charon_active_out=work/'charon-active-output';charon_active_out.mkdir()
    env=dict(rust_env,CARGO_TARGET_DIR=str(charon_active_target))
    stages.append(runner('charon-active',src,[CHARON,'cargo','--preset','aeneas','--dest-file',charon_active_out/'app.llbc','--',
        '--manifest-path',src/'Cargo.toml','--package','app_closure','--lib','--offline','--locked','-v'],env,charon_active_out,work,delay_ms=80))
    lake_active=work/'lake-active-source';shutil.copytree(lake_root,lake_active,ignore=shutil.ignore_patterns('.lake'))
    stages.append(runner('lake-active',lake_active,[LEANBIN/'lake','--keep-toolchain','--no-cache','build','Probe'],
        lean_env,lake_active/'.lake',work,delay_ms=80))
    for r in stages:
        assert r['cancel']['signal']=='SIGSTOP then SIGKILL',r['stage']
        assert r['cancel']['stopped_group'] and not r['cancel']['remaining_group'],r['stage']
        assert not r['cancel']['surviving_recorded_pids'],r['stage']
        assert r['retry']['exit']==0,r['stage']
    assert (charon_out/'app.llbc').is_file()
    assert json.loads((charon_out/'app.llbc').read_text())['translated']['crate_name']=='app_closure'
    assert (aeneas_out/'Funs.lean').is_file()
    assert (lake_root/'.lake/build/lib/lean/Probe.olean').is_file()
    art=HERE/'artifacts';art.mkdir(exist_ok=True)
    chosen={'cargo-app.rmeta':next((cargo_target/'debug/deps').glob('libapp_closure-*.rmeta')),
            'charon-app.llbc':charon_out/'app.llbc','aeneas-Funs.lean':aeneas_out/'Funs.lean',
            'lake-Probe.olean':lake_root/'.lake/build/lib/lean/Probe.olean'}
    for name,path in chosen.items():shutil.copyfile(path,art/name)
    result={'tool_sha256':{'cargo':sha(RUST/'cargo'),'charon':sha(CHARON),'aeneas':sha(AENEAS),
                           'lake':sha(LEANBIN/'lake'),'lean':sha(LEANBIN/'lean')},
            'fixture_sha256':{'cargo_lock':sha(HERE/'cargo-fixture/Cargo.lock'),'aeneas_input':sha(HERE/'aeneas-input.llbc')},
            'artifacts_sha256':{name:sha(art/name) for name in chosen},
            'stages':stages,'work_root':'$WORK'}
    RESULT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps([{'stage':x['stage'],'stopped':len(x['cancel']['stopped_group']),
                       'remaining':len(x['cancel']['remaining_group']),'cancel_output_files':len(x['cancel']['output_after']),
                       'retry_exit':x['retry']['exit'],'retry_output_files':len(x['retry']['output_after'])} for x in stages],indent=2))

if __name__=='__main__':main()
