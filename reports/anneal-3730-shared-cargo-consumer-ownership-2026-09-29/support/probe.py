#!/usr/bin/env python3
"""One actual Cargo build shared by two toy request owners; no network/install."""
import hashlib, json, os, re, shutil, signal, subprocess, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FIX=ROOT/'fixture'; WORK=ROOT/'work'; OUT=ROOT/'results.json'
CARGO=Path(os.environ.get('CARGO_BIN',shutil.which('cargo'))).resolve()

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ps_group(group):
    rows=[]
    for line in subprocess.check_output(['ps','-axo','pid=,ppid=,pgid=,rss=,comm='],text=True).splitlines():
        f=line.split(maxsplit=4)
        if len(f)==5 and f[2].isdigit() and int(f[2])==group:
            rows.append({'pid':int(f[0]),'ppid':int(f[1]),'pgid':int(f[2]),'rss_kib':int(f[3]),'comm':f[4]})
    return rows

def preflight():
    free=shutil.disk_usage(ROOT).free
    mem=subprocess.check_output(['memory_pressure','-Q'],text=True,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',mem)
    pct=int(m.group(1)) if m else None
    if free<2_000_000_000 or pct is None or pct<25: raise RuntimeError(f'resource preflight free={free} mem={pct}')
    return {'free_disk_bytes':free,'free_memory_percent':pct}

def wait_marker(path,p,seconds=20):
    end=time.monotonic()+seconds
    while time.monotonic()<end:
        if path.exists(): return path.read_text().strip()
        if p.poll() is not None: raise RuntimeError('Cargo exited before marker')
        time.sleep(.03)
    raise TimeoutError('build script marker')

def run_case(name,fail=False,cancel_one=False,cancel_both=False):
    root=WORK/name; shutil.copytree(FIX,root)
    env=dict(os.environ,CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',FAIL_BUILD='1' if fail else '0')
    cmd=[str(CARGO),'build','--offline','-j','1','--target-dir',str(root/'target')]
    event=[]; owners={'editor':'active','agent':'active'}
    p=subprocess.Popen(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
    t0=time.monotonic();event.append({'kind':'start','owners':owners.copy(),'pid':p.pid})
    try:
        marker=wait_marker(root/'entered',p)
        group_at_marker=ps_group(p.pid);rss_at_marker=sum(x['rss_kib'] for x in group_at_marker)
        assert rss_at_marker<2_000_000, rss_at_marker
        event.append({'kind':'marker','marker':marker,'group':group_at_marker,'sampled_rss_kib':rss_at_marker})
        if cancel_one or cancel_both:
            owners['editor']='cancelled';event.append({'kind':'cancel_editor','owners':owners.copy(),'backend_poll':p.poll()})
            assert p.poll() is None
            if cancel_both:
                owners['agent']='cancelled';event.append({'kind':'cancel_agent','owners':owners.copy(),'backend_poll':p.poll()})
                os.killpg(p.pid,signal.SIGTERM);event.append({'kind':'signal_last_owner','signal':'SIGTERM'})
        stdout,stderr=p.communicate(timeout=25)
        group_after=ps_group(p.pid);assert not group_after,group_after
        artifact=root/'target/debug/libshared_job_probe.rlib'
        first={'exit':p.returncode,'stdout':stdout,'stderr':stderr,'artifact_exists':artifact.exists(),
               'artifact_sha256':sha(artifact) if artifact.exists() else None,'owners':owners.copy(),
               'group_after':group_after,'elapsed_seconds':round(time.monotonic()-t0,4)}
        if cancel_both:
            assert p.returncode!=0 and not artifact.exists()
            per_consumer={'editor':'cancelled','agent':'cancelled'}
        elif fail:
            assert p.returncode!=0 and not artifact.exists()
            per_consumer={'editor':'failed','agent':'failed'}
        elif cancel_one:
            assert p.returncode==0 and artifact.exists()
            per_consumer={'editor':'cancelled','agent':'success'}
        else:
            assert p.returncode==0 and artifact.exists()
            per_consumer={'editor':'success','agent':'success'}
        event.append({'kind':'first_result','consumer_results':per_consumer,'backend_exit':p.returncode})
        retry=None
        if cancel_both or fail:
            (root/'entered').unlink(missing_ok=True)
            env['FAIL_BUILD']='0';q=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True,timeout=30)
            assert q.returncode==0 and artifact.exists()
            retry={'exit':q.returncode,'stdout':q.stdout,'stderr':q.stderr,
                   'artifact_sha256':sha(artifact),'group_after':ps_group(p.pid)}
            event.append({'kind':'retry_success','artifact_sha256':retry['artifact_sha256']})
        return {'name':name,'command':cmd,'marker':marker,'events':event,'first':first,
                'consumer_results':per_consumer,'retry':retry,
                'fixture_sha256':{x.relative_to(root).as_posix():sha(x) for x in (root/'Cargo.toml',root/'build.rs',root/'src/lib.rs')}}
    finally:
        if p.poll() is None:
            os.killpg(p.pid,signal.SIGKILL);p.communicate(timeout=5)

def main():
    if WORK.exists(): raise RuntimeError(f'refusing existing {WORK}')
    pf=preflight();WORK.mkdir()
    cases=[run_case('cancel-one',cancel_one=True),run_case('cancel-both',cancel_both=True),run_case('failure',fail=True)]
    result={'preflight':pf,'cargo':str(CARGO),'cargo_sha256':sha(CARGO),'fixture_sha256':
            {x.relative_to(FIX).as_posix():sha(x) for x in (FIX/'Cargo.toml',FIX/'build.rs',FIX/'src/lib.rs')},
            'cases':cases}
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'cases':[(c['name'],c['first']['exit'],c['consumer_results'],bool(c['retry'])) for c in cases],
                      'cargo_sha256':result['cargo_sha256']},indent=2))
if __name__=='__main__':main()
