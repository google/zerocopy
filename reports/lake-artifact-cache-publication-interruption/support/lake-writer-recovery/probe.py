#!/usr/bin/env python3
"""Bounded Lake artifact-cache writer kill, two-consumer race, and retry probe."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
BASE = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LAKE, LEAN = BASE/'lake', BASE/'lean'
TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2'
RESULTS = HERE/'results.json'
ARTIFACTS = HERE/'artifacts'
LIMIT_RSS_KIB = 5_500_000


def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def inventory(root):
    if not root.exists(): return {}
    return {str(p.relative_to(root)): {'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(root.rglob('*')) if p.is_file()}


def make(root):
    dep,c=(root/'producer',root/'consumer')
    dep.mkdir(parents=True);c.mkdir(parents=True)
    (dep/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n')
    (dep/'Dep.lean').write_text('''import Lean
run_cmd do
  let opt ← IO.getEnv "PROBE_MARKER"
  if let some marker := opt then
    IO.FS.writeFile marker "entered"
    IO.sleep 1500
def depValue : Nat := 7
''')
    (dep/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    (c/'lakefile.lean').write_text('import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage probe_consumer\n@[default_target]\nlean_lib Generated\n')
    (c/'Generated.lean').write_text('import Dep\ntheorem generatedEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
    (c/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    (c/'lake-manifest.json').write_text(json.dumps({'version':'1.2.0','packagesDir':'.lake/packages',
      'packages':[{'type':'path','scope':'','name':'probe_dep','manifestFile':'lake-manifest.json',
                   'inherited':False,'dir':'../producer','configFile':'lakefile.lean'}],
      'name':'probe_consumer','lakeDir':'.lake','fixedToolchain':False},indent=2)+'\n')
    return dep,c


def env(work,cache,marker=None):
    e=dict(os.environ)
    e.update({'ELAN_TOOLCHAIN':TOOLCHAIN,'LEAN_NUM_THREADS':'1','MATHLIB_NO_CACHE_ON_UPDATE':'1',
              'LAKE_CACHE_DIR':str(cache),'LAKE_ARTIFACT_CACHE':'true','HOME':str(work/'empty-home'),
              'PATH':str(BASE)+os.pathsep+e.get('PATH','')})
    if marker is None: e.pop('PROBE_MARKER',None)
    else: e['PROBE_MARKER']=str(marker)
    return e


def ps_sample(pids):
    p=subprocess.run(['/bin/ps','-axo','pid=,ppid=,rss='],capture_output=True,text=True,timeout=2)
    rows={}
    for line in p.stdout.splitlines():
        parts=line.split()
        if len(parts)==3 and all(x.isdigit() for x in parts):
            pid,ppid,rss=map(int,parts);rows[pid]=(ppid,rss)
    seen=set(pids)
    while True:
        before=len(seen)
        seen.update(pid for pid,(ppid,_) in rows.items() if ppid in seen)
        if len(seen)==before: break
    return {'rss_kib_sum':sum(rows[x][1] for x in seen if x in rows),
            'processes':sum(x in rows for x in seen)}


def normalize(s,work):
    return s.replace(str(work),'$WORK').replace(str(BASE.parent),'$TOOLCHAIN')


def call(records,label,cwd,args,work,cache,marker=None,timeout=25):
    argv=[LAKE,'--keep-toolchain',*args]
    t=time.monotonic()
    try:
        p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env(work,cache,marker),
                         capture_output=True,text=True,timeout=timeout)
        code,out,err=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as x:
        code='timeout';out=x.stdout or b'';err=x.stderr or b''
        if isinstance(out,bytes):out=out.decode(errors='replace')
        if isinstance(err,bytes):err=err.decode(errors='replace')
    rec={'label':label,'cwd':normalize(str(cwd),work),'argv':[normalize(str(x),work) for x in argv],
         'cache':normalize(str(cache),work),'exit':code,'seconds':round(time.monotonic()-t,4),
         'stdout':normalize(out,work),'stderr':normalize(err,work)}
    records.append(rec)
    return rec


def start(cwd,work,cache,marker):
    return subprocess.Popen([str(LAKE),'--keep-toolchain','build','Dep'],cwd=cwd,
          env=env(work,cache,marker),stdout=subprocess.PIPE,stderr=subprocess.PIPE,
          text=True,start_new_session=True)


def collect(p,label,cwd,work,cache,seconds):
    out,err=p.communicate(timeout=5)
    return {'label':label,'cwd':normalize(str(cwd),work),'cache':normalize(str(cache),work),
            'exit':p.returncode,'seconds':round(seconds,4),
            'stdout':normalize(out,work),'stderr':normalize(err,work)}


def wait_markers(procs,markers,timeout=12):
    t=time.monotonic();peak={'rss_kib_sum':0,'processes':0};reason=None
    while not all(m.exists() for m in markers):
        sample=ps_sample([p.pid for p in procs if p.poll() is None])
        peak={k:max(peak[k],sample[k]) for k in peak}
        if peak['rss_kib_sum']>LIMIT_RSS_KIB: reason='memory-guard';break
        if any(p.poll() is not None for p in procs): reason='early-exit';break
        if time.monotonic()-t>timeout: reason='marker-timeout';break
        time.sleep(.02)
    if reason:
        for p in procs:
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
        raise RuntimeError(f'{reason}; markers={[m.exists() for m in markers]}, peak={peak}')
    return peak


def wait_finish(procs,peak,timeout=15):
    t=time.monotonic()
    while any(p.poll() is None for p in procs):
        sample=ps_sample([p.pid for p in procs if p.poll() is None])
        peak={k:max(peak[k],sample[k]) for k in peak}
        if peak['rss_kib_sum']>LIMIT_RSS_KIB or time.monotonic()-t>timeout:
            for p in procs:
                if p.poll() is None:os.killpg(p.pid,signal.SIGKILL)
            raise RuntimeError(f'resource guard after marker: {peak}')
        time.sleep(.02)
    return peak


def cache_mapping(cache):
    maps=sorted((cache/'outputs/probe_dep').glob('*.json'))
    return maps


def direct_loader(records,label,cache,work):
    mapping=cache_mapping(cache)[0]
    item=json.loads(mapping.read_text())
    object_path=cache/'artifacts'/item['data']['o'][0]
    root=work/('loader-'+label)
    root.mkdir()
    (root/'Dep.olean').symlink_to(object_path)
    (root/'Check.lean').write_text('import Dep\ntheorem cacheEq : depValue + 1 = 8 := by decide\n#eval depValue + 1\n')
    e=env(work,cache);e['LEAN_PATH']=str(root)
    t=time.monotonic()
    p=subprocess.run([str(LEAN),'--json',str(root/'Check.lean')],cwd=root,env=e,
                     capture_output=True,text=True,timeout=15)
    rec={'label':label,'cwd':normalize(str(root),work),
         'argv':[normalize(str(LEAN),work),'--json',normalize(str(root/'Check.lean'),work)],
         'cache':normalize(str(cache),work),'exit':p.returncode,
         'seconds':round(time.monotonic()-t,4),'stdout':normalize(p.stdout,work),
         'stderr':normalize(p.stderr,work),'object_sha256':sha(object_path)}
    records.append(rec)
    return rec


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',required=True,type=Path);a=ap.parse_args()
    work=a.work.resolve()
    if work.exists():raise SystemExit('choose an absent --work path')
    if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('disk guard: need 15 GiB free')
    work.mkdir(parents=True);(work/'empty-home').mkdir()
    if ARTIFACTS.exists():shutil.rmtree(ARTIFACTS)
    ARTIFACTS.mkdir()
    records=[];obs={}
    # One real writer killed inside Dep elaboration; no cacheable Dep result yet.
    solo_dep,solo_c=make(work/'solo');solo_cache=work/'cache-solo'
    prime=call(records,'solo-prime-no-build',solo_c,['--no-build','build','Dep'],work,solo_cache)
    marker=work/'marker-solo';t=time.monotonic();p=start(solo_c,work,solo_cache,marker)
    peak_solo=wait_markers([p],[marker]);os.killpg(p.pid,signal.SIGKILL)
    killed=collect(p,'solo-killed-writer',solo_c,work,solo_cache,time.monotonic()-t);records.append(killed)
    obs['solo_after_kill']={'marker':marker.exists(),'peak_sampled':peak_solo,
                            'cache':inventory(solo_cache),'producer':inventory(solo_dep)}
    shutil.copytree(solo_dep,ARTIFACTS/'solo-killed-package')
    failed_setup=call(records,'solo-setup-after-kill',solo_c,['--no-build','setup-file','Generated.lean'],work,solo_cache)
    retried=call(records,'solo-retry-build',solo_c,['build','Dep'],work,solo_cache)
    setup=call(records,'solo-setup-after-retry',solo_c,['--no-build','setup-file','Generated.lean'],work,solo_cache)
    obs['solo_after_retry']={'cache':inventory(solo_cache),'producer':inventory(solo_dep)}
    shutil.copytree(solo_cache,ARTIFACTS/'solo-repaired-cache')
    # Two independent writable package trees share exactly one Lake artifact cache.
    dep_a,c_a=make(work/'pair-a');dep_b,c_b=make(work/'pair-b');shared=work/'cache-shared'
    call(records,'pair-prime-a',c_a,['--no-build','build','Dep'],work,shared)
    call(records,'pair-prime-b',c_b,['--no-build','build','Dep'],work,shared)
    ma,mb=work/'marker-A',work/'marker-B';t=time.monotonic()
    pa=start(c_a,work,shared,ma);pb=start(c_b,work,shared,mb)
    peak_pair=wait_markers([pa,pb],[ma,mb]);os.killpg(pa.pid,signal.SIGKILL)
    peak_pair=wait_finish([pa,pb],peak_pair)
    rec_a=collect(pa,'pair-killed-A',c_a,work,shared,time.monotonic()-t)
    rec_b=collect(pb,'pair-survived-B',c_b,work,shared,time.monotonic()-t)
    records.extend((rec_a,rec_b))
    obs['pair_after_survivor']={'markers':[ma.exists(),mb.exists()],'peak_sampled':peak_pair,
                                'cache':inventory(shared),'package_a':inventory(dep_a),'package_b':inventory(dep_b),
                                'maps':[str(x.relative_to(shared)) for x in cache_mapping(shared)]}
    shutil.copytree(shared,ARTIFACTS/'shared-cache')
    shutil.copytree(dep_a,ARTIFACTS/'pair-killed-package')
    fetch_a=call(records,'pair-A-no-build-fetch',c_a,['--no-build','build','Dep'],work,shared)
    setup_a=call(records,'pair-A-setup',c_a,['--no-build','setup-file','Generated.lean'],work,shared)
    pair_loader=direct_loader(records,'pair-cache-direct-lean-loader',shared,work)
    obs['pair_after_fetch']={'cache':inventory(shared),'package_a':inventory(dep_a),'package_b':inventory(dep_b)}
    # Controlled local mapping corruption in a copy, not a claim about kill timing.
    corrupt=work/'cache-corrupt';shutil.copytree(shared,corrupt)
    maps=cache_mapping(corrupt);assert maps
    mapping=maps[0];prior=sha(mapping);mapping.write_text('{"data":')
    shutil.copyfile(mapping,ARTIFACTS/'truncated-output-map.json')
    bad_dep,bad_c=make(work/'corrupt-consumer')
    before_bad={'cache':inventory(corrupt),'producer':inventory(bad_dep)}
    bad_setup=call(records,'corrupt-map-no-build-setup',bad_c,['--no-build','setup-file','Generated.lean'],work,corrupt)
    repair=call(records,'corrupt-map-retry-build',bad_c,['build','Dep'],work,corrupt)
    repaired_setup=call(records,'corrupt-map-setup-after-retry',bad_c,['--no-build','setup-file','Generated.lean'],work,corrupt)
    repaired_loader=direct_loader(records,'repaired-cache-direct-lean-loader',corrupt,work)
    obs['corruption']={'mapping':str(mapping.relative_to(corrupt)),'prior_sha256':prior,
                       'corrupt_sha256':byte_sha(b'{"data":'),'before':before_bad,
                       'after':{'cache':inventory(corrupt),'producer':inventory(bad_dep)}}
    # Preserve the repaired cache separately from the intentionally malformed map.
    shutil.copytree(corrupt,ARTIFACTS/'repaired-cache')
    assert prime['exit']==3 and killed['exit']==-9 and failed_setup['exit']==3
    assert retried['exit']==setup['exit']==0
    assert rec_a['exit']==-9 and rec_b['exit']==0 and fetch_a['exit']==setup_a['exit']==0
    assert pair_loader['exit']==0 and '8' in pair_loader['stdout']
    assert bad_setup['exit']==3 and repair['exit']==repaired_setup['exit']==repaired_loader['exit']==0
    assert '8' in repaired_loader['stdout']
    assert sha(mapping)!=obs['corruption']['corrupt_sha256']
    result={'environment':{'platform':platform.platform(),'python':sys.version,
            'lake_sha256':sha(LAKE),'lean_sha256':sha(LEAN),'toolchain':TOOLCHAIN,
            'rss_guard_kib':LIMIT_RSS_KIB,'max_concurrent_consumers':2},
            'records':records,'observations':obs}
    RESULTS.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'exits':{x['label']:x['exit'] for x in records},
                      'pair_peak_sampled':peak_pair,'solo_peak_sampled':peak_solo,
                      'shared_cache_files':len(obs['pair_after_survivor']['cache']),
                      'corrupt_map_repaired':repair['exit']==0},sort_keys=True))


def byte_sha(b):return hashlib.sha256(b).hexdigest()

if __name__=='__main__':main()
