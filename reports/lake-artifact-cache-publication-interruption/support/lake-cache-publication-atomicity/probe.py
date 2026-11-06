#!/usr/bin/env python3
"""Pinned Lake cache-map write interruption, artifact failure, corruption and sharing."""
import argparse,hashlib,json,os,pathlib,platform,resource,shutil,signal,subprocess,sys,time

HERE=pathlib.Path(__file__).resolve().parent;FIX=HERE/'fixture';ART=HERE/'artifacts';OUT=HERE/'results.json'
BASE=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE=BASE/'lake';LEAN=BASE/'lean';TOOLCHAIN='leanprover/lean4:v4.30.0-rc2'
RSS_GUARD_KIB=5_500_000

def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def invent(p):
    if not p.exists():return {}
    return {str(x.relative_to(p)):{'bytes':x.stat().st_size,'sha256':sha(x)}
            for x in sorted(p.rglob('*')) if x.is_file()}
def norm(s,work):return s.replace(str(work),'$WORK').replace(str(BASE.parent),'$TOOLCHAIN')
def make(root):
    shutil.copytree(FIX,root)
    return root/'producer',root/'consumer'
def env(work,cache,enabled=True,marker=None):
    e=dict(os.environ);e.update({'ELAN_TOOLCHAIN':TOOLCHAIN,'LEAN_NUM_THREADS':'1',
      'MATHLIB_NO_CACHE_ON_UPDATE':'1','LAKE_CACHE_DIR':str(cache),
      'LAKE_ARTIFACT_CACHE':'true' if enabled else 'false',
      'HOME':str(work/'empty-home'),'PATH':str(BASE)+os.pathsep+e.get('PATH','')})
    if marker:e['PROBE_MARKER']=str(marker)
    else:e.pop('PROBE_MARKER',None)
    return e
def call(records,label,cwd,work,cache,args,enabled=True,limit=None,marker=None,timeout=25):
    argv=[LAKE,'--keep-toolchain',*args]
    def preexec():
        if limit is not None:resource.setrlimit(resource.RLIMIT_FSIZE,(limit,limit))
    t=time.monotonic();p=subprocess.Popen([str(x) for x in argv],cwd=cwd,env=env(work,cache,enabled,marker),
          stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True,preexec_fn=preexec)
    try:stdout,stderr=p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);stdout,stderr=p.communicate(timeout=5)
        raise TimeoutError(label)
    rec={'label':label,'argv':[norm(str(x),work) for x in argv],
         'cwd':norm(str(cwd),work),'cache':norm(str(cache),work),
         'enabled':enabled,'file_size_limit':limit,'exit':p.returncode,
         'seconds':round(time.monotonic()-t,4),'stdout':norm(stdout,work),'stderr':norm(stderr,work)}
    records.append(rec);return rec
def direct_lean(records,label,cache,work):
    mapping=next((cache/'outputs/probe_dep').glob('*.json'))
    obj=json.loads(mapping.read_text())['data']['o'][0]
    path=cache/'artifacts'/obj
    root=work/('direct-'+label);root.mkdir();(root/'Dep.olean').symlink_to(path)
    (root/'Check.lean').write_text('import Dep\ntheorem cacheEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
    e=env(work,cache);e['LEAN_PATH']=str(root)
    t=time.monotonic();p=subprocess.run([str(LEAN),'--json',str(root/'Check.lean')],cwd=root,env=e,
                         capture_output=True,text=True,timeout=12)
    rec={'label':label,'argv':[norm(str(LEAN),work),'--json',norm(str(root/'Check.lean'),work)],
         'cwd':norm(str(root),work),'exit':p.returncode,
         'seconds':round(time.monotonic()-t,4),'stdout':norm(p.stdout,work),'stderr':norm(p.stderr,work),
         'object_sha256':sha(path),'object_bytes':path.stat().st_size}
    records.append(rec);return rec
def snapshot(name,root):
    shutil.copytree(root,ART/name)
def ps_sample(pids):
    p=subprocess.run(['/bin/ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True,timeout=2)
    rows={}
    for line in p.stdout.splitlines():
        q=line.split()
        if len(q)==3 and all(x.isdigit() for x in q):
            pid,ppid,rss=map(int,q);rows[pid]=(ppid,rss)
    seen=set(pids)
    while True:
        before=len(seen);seen.update(pid for pid,(ppid,_) in rows.items() if ppid in seen)
        if len(seen)==before:break
    return {'rss_kib_sum':sum(rows[x][1] for x in seen if x in rows),
            'processes':sum(x in rows for x in seen)}
def pair(records,label,cwd,work,cache,enabled,markers=None):
    started=[];t=time.monotonic()
    for i in range(2):
        marker=(markers[i] if markers else None)
        p=subprocess.Popen([str(LAKE),'--keep-toolchain','build','Dep'],cwd=cwd[i],
             env=env(work,cache,enabled,marker),stdout=subprocess.PIPE,stderr=subprocess.PIPE,
             text=True,start_new_session=True)
        started.append(p)
    peak={'rss_kib_sum':0,'processes':0};timed_out=False
    while any(p.poll() is None for p in started):
        s=ps_sample([p.pid for p in started if p.poll() is None])
        peak={k:max(peak[k],s[k]) for k in peak}
        if peak['rss_kib_sum']>RSS_GUARD_KIB or time.monotonic()-t>18:
            timed_out=True
            for p in started:
                if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
            break
        time.sleep(.03)
    results=[]
    for i,p in enumerate(started):
        stdout,stderr=p.communicate(timeout=5)
        rec={'label':f'{label}-{i}','cwd':norm(str(cwd[i]),work),'cache':norm(str(cache),work),
             'enabled':enabled,'exit':p.returncode,'seconds':round(time.monotonic()-t,4),
             'stdout':norm(stdout,work),'stderr':norm(stderr,work)}
        records.append(rec);results.append(rec)
    if timed_out:raise RuntimeError(f'pair guard: {label}, {peak}')
    return results,peak
def immutable(root):
    for p in sorted(root.rglob('*'),reverse=True):
        p.chmod(0o444 if p.is_file() else 0o555)
    root.chmod(0o555)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=pathlib.Path,required=True);a=ap.parse_args()
    work=a.work.resolve()
    if work.exists():raise SystemExit('choose an absent owned --work path')
    if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('15 GiB free-disk guard')
    work.mkdir(parents=True);(work/'empty-home').mkdir()
    if ART.exists():shutil.rmtree(ART)
    ART.mkdir();records=[];obs={}
    # Prebuild without cache, then turn cache on: existing local artifacts isolate cache writes.
    dep,c=make(work/'map');cache=work/'cache-map'
    assert call(records,'map-prebuild',c,work,cache,['build','Dep'],False)['exit']==0
    assert not invent(cache)
    failed=call(records,'map-write-limited',c,work,cache,['build','Dep'],True,limit=64)
    map_files=list((cache/'outputs/probe_dep').glob('*.json'))
    assert failed['exit']<0 and len(map_files)==1 and map_files[0].stat().st_size==64
    assert len([x for x in (cache/'artifacts').iterdir() if x.is_file()])==3
    shutil.copyfile(map_files[0],ART/'partial-output-map.json')
    obs['map_failure']={'exit':failed['exit'],'cache':invent(cache),'producer':invent(dep),
                        'partial_map_sha256':sha(map_files[0])}
    fresh_dep,fresh_c=make(work/'map-fresh')
    rejected=call(records,'map-partial-no-build',fresh_c,work,cache,['--no-build','setup-file','Generated.lean'])
    assert rejected['exit']==3 and ('invalid' in rejected['stderr'].lower() or 'invalid' in rejected['stdout'].lower())
    repaired=call(records,'map-retry-build',fresh_c,work,cache,['build','Dep'])
    setup=call(records,'map-repaired-no-build',fresh_c,work,cache,['--no-build','setup-file','Generated.lean'])
    assert repaired['exit']==setup['exit']==0
    assert next((cache/'outputs/probe_dep').glob('*.json')).stat().st_size>64
    assert direct_lean(records,'map-repaired-direct-lean',cache,work)['exit']==0
    obs['map_repaired']={'cache':invent(cache),'fresh_producer':invent(fresh_dep)}
    snapshot('map-repaired-cache',cache)
    # Refuse creation of the first content-addressed cache object, then retry.
    adep,ac=make(work/'artifact');acache=work/'cache-artifact'
    assert call(records,'artifact-prebuild',ac,work,acache,['build','Dep'],False)['exit']==0
    (acache/'artifacts').mkdir(parents=True);(acache/'artifacts').chmod(0o500)
    afail=call(records,'artifact-write-denied',ac,work,acache,['build','Dep'])
    assert afail['exit']!=0 and not invent(acache)
    obs['artifact_failure']={'exit':afail['exit'],'stderr':afail['stderr'],'cache':invent(acache),
                             'producer':invent(adep)}
    (acache/'artifacts').chmod(0o700)
    aretry=call(records,'artifact-retry-build',ac,work,acache,['build','Dep'])
    assert aretry['exit']==0 and len(invent(acache))==4
    obs['artifact_repaired']={'cache':invent(acache),'producer':invent(adep)}
    snapshot('artifact-repaired-cache',acache)
    # A present but damaged object is a different failure: preserve the false cache hit.
    bad=work/'cache-bad-object';shutil.copytree(cache,bad)
    obj=next((bad/'artifacts').glob('*.olean'));old_sha=sha(obj);old_size=obj.stat().st_size
    obj.chmod(0o644);obj.write_bytes(obj.read_bytes()[:100])
    bad_map=next((bad/'outputs/probe_dep').glob('*.json'));map_sha_before=sha(bad_map)
    bdep,bc=make(work/'bad-object')
    bad_setup=call(records,'bad-object-no-build-setup',bc,work,bad,['--no-build','setup-file','Generated.lean'])
    bad_build=call(records,'bad-object-ordinary-build',bc,work,bad,['build','Dep'])
    bad_loader=direct_lean(records,'bad-object-direct-lean',bad,work)
    assert bad_setup['exit']==bad_build['exit']==0 and obj.stat().st_size==100
    assert bad_loader['exit']!=0 and sha(bad_map)==map_sha_before
    obs['bad_object']={'original_sha256':old_sha,'original_bytes':old_size,
                       'corrupt_sha256':sha(obj),'corrupt_bytes':obj.stat().st_size,
                       'map_sha256':map_sha_before,'lake_setup_exit':bad_setup['exit'],
                       'lake_build_exit':bad_build['exit'],'lean_exit':bad_loader['exit'],
                       'cache':invent(bad)}
    shutil.copyfile(obj,ART/'truncated-olean.bin')
    obj.unlink()
    missing_dep,missing_c=make(work/'missing-object')
    missing=call(records,'missing-object-no-build',missing_c,work,bad,['--no-build','setup-file','Generated.lean'])
    fixed=call(records,'missing-object-rebuild',missing_c,work,bad,['build','Dep'])
    fixed_setup=call(records,'fixed-object-no-build',missing_c,work,bad,['--no-build','setup-file','Generated.lean'])
    fixed_loader=direct_lean(records,'fixed-object-direct-lean',bad,work)
    assert missing['exit']==3 and fixed['exit']==fixed_setup['exit']==fixed_loader['exit']==0
    assert obj.stat().st_size==old_size and sha(obj)==old_sha
    obs['object_repaired_after_delete']={'cache':invent(bad),'producer':invent(missing_dep),
                                         'repaired_sha256':sha(obj)}
    snapshot('object-repaired-cache',bad)
    # Two private writable package trees consume a read-only cache concurrently.
    immutable_cache=work/'cache-immutable';shutil.copytree(cache,immutable_cache)
    before_immutable=invent(immutable_cache);immutable(immutable_cache)
    p1,c1=make(work/'private-a');p2,c2=make(work/'private-b')
    private_pair,private_peak=pair(records,'private-immutable-cache',[c1,c2],work,immutable_cache,True)
    assert [x['exit'] for x in private_pair]==[0,0] and invent(immutable_cache)==before_immutable
    assert call(records,'private-a-setup',c1,work,immutable_cache,['--no-build','setup-file','Generated.lean'])['exit']==0
    assert call(records,'private-b-setup',c2,work,immutable_cache,['--no-build','setup-file','Generated.lean'])['exit']==0
    obs['private_immutable']={'cache_unchanged':invent(immutable_cache)==before_immutable,
                              'cache':before_immutable,'producer_a':invent(p1),'producer_b':invent(p2),
                              'peak_sampled':private_peak,'exits':[x['exit'] for x in private_pair]}
    # Deliberately share the same writable package tree, separately from immutable-cache test.
    sdep,sc=make(work/'shared-package');scache=work/'cache-shared-package'
    ma,mb=work/'shared-A-marker',work/'shared-B-marker'
    shared_pair,shared_peak=pair(records,'shared-writable-package',[sc,sc],work,scache,False,[ma,mb])
    shared_setup=call(records,'shared-package-post-setup',sc,work,scache,
                      ['--no-build','setup-file','Generated.lean'],False)
    obs['shared_writable_package']={'markers':[ma.exists(),mb.exists()],
              'exits':[x['exit'] for x in shared_pair],'setup_exit':shared_setup['exit'],
              'producer':invent(sdep),'cache':invent(scache),'peak_sampled':shared_peak}
    assert len(shared_pair)==2
    # The shared writable schedule is observed, not asserted universally safe.
    src=BASE.parent/'src/lean/Lake/Lake';source_files=[src/'Config/Cache.lean',src/'Build/Common.lean']
    result={'environment':{'platform':platform.platform(),'python':sys.version,
              'toolchain':TOOLCHAIN,'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN),
              'cache_source_sha256':{p.name:sha(p) for p in source_files},
              'rss_guard_kib':RSS_GUARD_KIB,'max_concurrent_consumers':2},
            'fixture':invent(FIX),'records':records,'observations':obs}
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'map_exit':failed['exit'],'artifact_exit':afail['exit'],
                      'bad_object_lean_exit':bad_loader['exit'],
                      'private_exits':obs['private_immutable']['exits'],
                      'shared_exits':obs['shared_writable_package']['exits'],
                      'shared_markers':obs['shared_writable_package']['markers']},sort_keys=True))

if __name__=='__main__':main()
