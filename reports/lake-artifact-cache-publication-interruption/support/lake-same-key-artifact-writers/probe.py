#!/usr/bin/env python3
"""Bounded same-key Lake writers and cross-volume artifact-write interruption.

Creates/detaches a 128 MiB scratch APFS disk image under --work. No downloads or
installs. Acquired report files are replaced only inside this package.
"""
from __future__ import annotations
import argparse,hashlib,json,os,pathlib,platform,resource,shutil,signal,subprocess,time
HERE=pathlib.Path(__file__).resolve().parent
FIX=HERE/'fixture'; OUT=HERE/'results.json'; ART=HERE/'artifacts'
TOOLS=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
BIN=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin'
LAKE=BIN/'lake'; LEAN=BIN/'lean'; SOURCE=BIN.parent/'src/lean/Lake/Lake/Build/Common.lean'
TOOLCHAIN='leanprover/lean4:v4.30.0-rc2'
RSS_CAP_KIB=3_800_000; DISK_CAP=256*1024*1024
R={'environment':{},'records':[],'cases':{},'limits':[]}
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def inv(root):
    root=pathlib.Path(root)
    return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
            for p in sorted(root.rglob('*')) if p.is_file()}
def total(root):return sum(p.stat().st_size for p in pathlib.Path(root).rglob('*') if p.is_file())
def norm(s,work):return str(s).replace(str(work),'$WORK').replace(str(BIN.parent),'$TOOLCHAIN')
def fixture(dst):shutil.copytree(FIX,dst);return dst/'producer',dst/'consumer'
def env(work,cache,enabled=True,marker=None):
    e=dict(os.environ);e.update({'ELAN_TOOLCHAIN':TOOLCHAIN,'LEAN_NUM_THREADS':'1',
       'MATHLIB_NO_CACHE_ON_UPDATE':'1','LAKE_CACHE_DIR':str(cache),
       'LAKE_ARTIFACT_CACHE':'true' if enabled else 'false',
       'HOME':str(work/'empty-home'),'PATH':str(BIN)+os.pathsep+e.get('PATH','')})
    if marker:e['PROBE_MARKER']=str(marker)
    else:e.pop('PROBE_MARKER',None)
    return e
def ps_sample(pids):
    out=subprocess.run(['/bin/ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True,timeout=3).stdout
    rows={}
    for line in out.splitlines():
        x=line.split()
        if len(x)==3 and all(y.isdigit() for y in x):
            pid,ppid,rss=map(int,x);rows[pid]=(ppid,rss)
    seen=set(pids)
    while True:
        before=len(seen);seen.update(pid for pid,(ppid,_) in rows.items() if ppid in seen)
        if len(seen)==before:break
    return {'rss_kib_sum':sum(rows[x][1] for x in seen if x in rows),'processes':sum(x in rows for x in seen)}
def communicate(label,procs,work,timeout=30):
    t=time.monotonic();peak={'rss_kib_sum':0,'processes':0};reason=None
    while any(p.poll() is None for p in procs):
        s=ps_sample([p.pid for p in procs if p.poll() is None])
        for k in peak:peak[k]=max(peak[k],s[k])
        if peak['rss_kib_sum']>RSS_CAP_KIB:reason='rss guard';break
        if time.monotonic()-t>timeout:reason='timeout guard';break
        if total(work)>DISK_CAP:reason='disk guard';break
        time.sleep(.04)
    if reason:
        for p in procs:
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
    out=[]
    for i,p in enumerate(procs):
        stdout,stderr=p.communicate(timeout=5)
        rec={'label':label+(f'-{i}' if len(procs)>1 else ''),'pid':p.pid,'exit':p.returncode,
             'seconds':round(time.monotonic()-t,4),'stdout':norm(stdout,work),'stderr':norm(stderr,work)}
        R['records'].append(rec);out.append(rec)
    if reason:raise RuntimeError(f'{label}: {reason} at {peak}')
    return out,peak
def launch(cwd,work,cache,args,enabled=True,marker=None,limit=None):
    def pre():
        if limit is not None:resource.setrlimit(resource.RLIMIT_FSIZE,(limit,limit))
    cmd=[str(LAKE),'--keep-toolchain',*args]
    p=subprocess.Popen(cmd,cwd=cwd,env=env(work,cache,enabled,marker),stdout=subprocess.PIPE,
       stderr=subprocess.PIPE,text=True,start_new_session=True,preexec_fn=pre)
    R['records'].append({'label':'launch','argv':[norm(x,work) for x in cmd],
       'cwd':norm(cwd,work),'cache':norm(cache,work),'file_size_limit':limit,'pid':p.pid})
    return p
def run(label,cwd,work,cache,args,enabled=True,marker=None,limit=None):
    p=launch(cwd,work,cache,args,enabled,marker,limit)
    return communicate(label,[p],work)[0][0]
def direct(label,cache,work):
    maps=list((cache/'outputs/probe_dep').glob('*.json'));assert len(maps)==1,maps
    data=json.loads(maps[0].read_text())['data']['o'][0]
    obj=cache/'artifacts'/data
    root=work/('direct-'+label);root.mkdir();(root/'Dep.olean').symlink_to(obj)
    (root/'Check.lean').write_text('import Dep\ntheorem cacheEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
    e=env(work,cache);e['LEAN_PATH']=str(root)
    p=subprocess.run([str(LEAN),'--json','Check.lean'],cwd=root,env=e,capture_output=True,text=True,timeout=12)
    rec={'label':label,'argv':[str(LEAN),'--json','Check.lean'],'exit':p.returncode,
      'stdout':norm(p.stdout,work),'stderr':norm(p.stderr,work),
      'object_sha256':sha(obj),'object_bytes':obj.stat().st_size}
    R['records'].append(rec);return rec

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=pathlib.Path,required=True);a=ap.parse_args()
    work=a.work.resolve()
    if work.exists():raise SystemExit('--work must be absent and owned for this experiment')
    if shutil.disk_usage(work.parent).free<20*(1<<30):raise SystemExit('20 GiB free-disk guard')
    mem=subprocess.run(['/usr/bin/memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
    if mem.returncode or 'System-wide memory free percentage:' not in mem.stdout:
        raise SystemExit('memory-pressure preflight unavailable')
    freepct=int(mem.stdout.rsplit('System-wide memory free percentage:',1)[1].split('%',1)[0].strip())
    if freepct<35:raise SystemExit(f'free-memory guard: {freepct}% < 35%')
    assert all(p.is_file() for p in [LAKE,LEAN,SOURCE])
    work.mkdir();(work/'empty-home').mkdir();mount=work/'mount';mount.mkdir()
    image=work/'cache.sparseimage';attached=False
    create=subprocess.run(['/usr/bin/hdiutil','create','-size','128m','-fs','APFS',
       '-volname','R10Scratch','-type','SPARSE','-ov','-o',str(image)],capture_output=True,text=True,timeout=30)
    assert create.returncode==0,create.stderr
    attach=subprocess.run(['/usr/bin/hdiutil','attach','-nobrowse','-mountpoint',str(mount),str(image)],
       capture_output=True,text=True,timeout=30)
    assert attach.returncode==0,attach.stderr
    attached=True
    try:
        if ART.exists():shutil.rmtree(ART)
        ART.mkdir()
        R['environment']={'platform':platform.platform(),'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN),
          'cache_writer_source_sha256':sha(SOURCE),'scratch_cache_device':os.stat(mount).st_dev,
          'local_fixture_device':os.stat(work).st_dev,'image_logical_bytes':128*1024*1024,
          'disk_cap_bytes':DISK_CAP,'rss_cap_kib':RSS_CAP_KIB,'max_concurrent_consumers':2,
          'initial_memory_free_percent':freepct,
          'fixture':inv(FIX)}
        assert os.stat(mount).st_dev!=os.stat(work).st_dev
        # Build locally first; cache-only stage must cross volumes and take copy fallback.
        dep,con=fixture(work/'golden');gold=mount/'golden-cache'
        assert run('golden-prebuild',con,work,gold,['build','Dep'],False)['exit']==0
        assert run('golden-cache',con,work,gold,['build','Dep'])['exit']==0
        golden=inv(gold);exts={p.suffix[1:]:p for p in (gold/'artifacts').iterdir() if p.is_file()}
        assert {'olean','ilean','c'}<=set(exts),exts
        assert direct('golden-direct-import',gold,work)['exit']==0
        shutil.copytree(gold,ART/'golden-cache')
        R['cases']['golden']={'cache':golden,'artifact_paths':{x:p.name for x,p in exts.items()}}
        # Two independent package roots, one empty same-key cache. The run_cmd marker
        # brings both producers into overlapping elaboration before cache publication.
        for trial in range(3):
            p1,c1=fixture(work/f'pair-{trial}-a');p2,c2=fixture(work/f'pair-{trial}-b')
            cache=mount/f'pair-cache-{trial}'
            ma=work/f'pair-{trial}-a.entered';mb=work/f'pair-{trial}-b.entered'
            procs=[launch(c1,work,cache,['build','Dep'],marker=ma),
                   launch(c2,work,cache,['build','Dep'],marker=mb)]
            results,peak=communicate(f'same-key-pair-{trial}',procs,work)
            maps=list((cache/'outputs/probe_dep').glob('*.json'))
            map_valid=len(maps)==1
            if map_valid:
                try:json.loads(maps[0].read_text())
                except (ValueError,UnicodeDecodeError):map_valid=False
            current=inv(cache)
            integrity=(set(current)==set(golden) and all(current[k]['sha256']==golden[k]['sha256'] for k in golden))
            # A failed/corrupt race is retained, then retried after clearing only
            # the cache so a fresh consumer has an unambiguous recovery oracle.
            shutil.copytree(cache,ART/f'pair-cache-{trial}')
            repaired=False
            if not integrity or not map_valid or any(x['exit'] for x in results):
                shutil.rmtree(cache);rd,rc=fixture(work/f'pair-{trial}-repair')
                assert run(f'pair-{trial}-repair-build',rc,work,cache,['build','Dep'])['exit']==0
                repaired=True
            fd,fc=fixture(work/f'pair-{trial}-fresh')
            setup=run(f'pair-{trial}-fresh-setup',fc,work,cache,['--no-build','setup-file','Generated.lean'])
            imp=direct(f'pair-{trial}-fresh-import',cache,work)
            assert setup['exit']==imp['exit']==0
            R['cases'][f'pair-{trial}']={'markers':[ma.exists(),mb.exists()],
              'exits':[x['exit'] for x in results],'peak_sampled':peak,
              'map_valid_before_repair':map_valid,'cache_matches_golden_before_repair':integrity,
              'repair_needed':repaired,'cache_before_repair':current,'cache_after':inv(cache),
              'fresh_setup_exit':setup['exit'],'fresh_import_exit':imp['exit']}
        # For each type, preseed all other objects in a new cache, force cross-volume
        # fallback write, and cap this Lake process halfway through target bytes.
        for ext in ('olean','ilean','c'):
            d,c=fixture(work/f'interrupt-{ext}');cache=mount/f'interrupt-cache-{ext}'
            assert run(f'{ext}-prebuild',c,work,cache,['build','Dep'],False)['exit']==0
            (cache/'artifacts').mkdir(parents=True)
            for x,p in exts.items():
                if x!=ext:shutil.copyfile(p,cache/'artifacts'/p.name)
            expected=exts[ext];target=cache/'artifacts'/expected.name
            cap=max(64,expected.stat().st_size//2)
            failed=run(f'{ext}-limited-write',c,work,cache,['build','Dep'],limit=cap)
            partial=target.is_file() and 0<target.stat().st_size<expected.stat().st_size
            if target.is_file():shutil.copyfile(target,ART/f'partial-{ext}.bin')
            before=inv(cache);maps=list((cache/'outputs/probe_dep').glob('*.json')) if (cache/'outputs/probe_dep').exists() else []
            # A fresh setup must not be described as accepting the partial cache.
            freshd,freshc=fixture(work/f'interrupt-{ext}-fresh')
            setup=run(f'{ext}-fresh-no-build-after-failure',freshc,work,cache,
                      ['--no-build','setup-file','Generated.lean'])
            # Try an ordinary retry *without* deleting the partial object.
            # A successful exit must still be checked against content hashes.
            present_retry=run(f'{ext}-retry-with-partial-present',c,work,cache,['build','Dep'])
            present_integrity=target.is_file() and sha(target)==sha(expected)
            present_maps=list((cache/'outputs/probe_dep').glob('*.json')) if (cache/'outputs/probe_dep').exists() else []
            present_fresh_setup=None;present_fresh_import=None
            if len(present_maps)==1:
                pd,pc=fixture(work/f'interrupt-{ext}-present-fresh')
                present_fresh_setup=run(f'{ext}-fresh-no-build-with-partial-present',pc,work,cache,
                    ['--no-build','setup-file','Generated.lean'])['exit']
                if present_fresh_setup==0:
                    present_fresh_import=direct(f'{ext}-fresh-import-with-partial-present',cache,work)['exit']
            present_inventory=inv(cache)
            shutil.copytree(cache,ART/f'partial-present-cache-{ext}')
            # Explicitly remove the interrupted object/map and rebuild from local
            # outputs. This does not assume Lake validates present object bytes.
            if target.exists():target.unlink()
            for m in present_maps:m.unlink()
            repair=run(f'{ext}-repair-build',c,work,cache,['build','Dep'])
            final=inv(cache)
            fresh2d,fresh2c=fixture(work/f'interrupt-{ext}-repaired-fresh')
            setup2=run(f'{ext}-repaired-fresh-setup',fresh2c,work,cache,
                       ['--no-build','setup-file','Generated.lean'])
            imp=direct(f'{ext}-repaired-fresh-import',cache,work)
            assert repair['exit']==setup2['exit']==imp['exit']==0
            assert final==golden,(ext,final,golden)
            assert partial and failed['exit']!=0 and setup['exit']!=0,(ext,failed,setup,before)
            shutil.copytree(cache,ART/f'repaired-cache-{ext}')
            R['cases'][f'interrupt-{ext}']={'target_file':expected.name,'target_expected_sha256':sha(expected),
               'target_expected_bytes':expected.stat().st_size,'file_size_limit':cap,
               'failed_exit':failed['exit'],'partial_observed':partial,
               'partial_sha256':sha(ART/f'partial-{ext}.bin'),
               'partial_bytes':(ART/f'partial-{ext}.bin').stat().st_size,
               'cache_after_failure':before,'no_build_exit_after_failure':setup['exit'],
               'retry_with_partial_present_exit':present_retry['exit'],
               'partial_present_integrity_matches_golden':present_integrity,
               'cache_after_present_retry':present_inventory,
               'fresh_setup_with_partial_present_exit':present_fresh_setup,
               'fresh_import_with_partial_present_exit':present_fresh_import,
               'cache_after_repair':final,'fresh_setup_exit':setup2['exit'],
               'fresh_import_exit':imp['exit']}
        R['limits']=['No power-loss or filesystem-crash durability claim.',
          'Two tiny same-key writers in three gated schedules; one success is not general shared-writer safety.',
          'Artifact interrupts use macOS APFS cross-volume hard-link fallback and RLIMIT_FSIZE, not arbitrary kill phases.',
          'Fresh direct Lean import checks OLean semantics; all three object hashes are separately compared to golden.',
          'No Anneal generated workspace, Mathlib-sized dependency, or native Linux/Windows filesystem.']
        OUT.write_text(json.dumps(R,indent=2,sort_keys=True)+'\n')
        print(json.dumps({'pair_exits':[R['cases'][f'pair-{i}']['exits'] for i in range(3)],
          'partial_bytes':{x:R['cases'][f'interrupt-{x}']['partial_bytes'] for x in ('olean','ilean','c')},
          'records':len(R['records'])},sort_keys=True))
    finally:
        if attached:
            detach=subprocess.run(['/usr/bin/hdiutil','detach',str(mount)],capture_output=True,text=True,timeout=30)
            if detach.returncode:raise RuntimeError('scratch disk image detach failed: '+detach.stderr)
        if image.exists():image.unlink()
if __name__=='__main__':main()
