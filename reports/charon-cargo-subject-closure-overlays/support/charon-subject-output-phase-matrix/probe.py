#!/usr/bin/env python3
"""Pinned Charon/Cargo subject and regular-file output-phase controls."""
import hashlib,json,os,pathlib,platform,re,resource,shutil,signal,subprocess,sys,time

HERE=pathlib.Path(__file__).resolve().parent
FIX=HERE/'fixture';ART=HERE/'artifacts';MAN=HERE/'manifests';RAW=HERE/'raw-results.json'
TOOLS=pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
RLIB=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
CHARON=TOOLS/'bin/charon';CARGO=RBIN/'cargo';RUSTC=RBIN/'rustc'

def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def files(root):return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file() and 'target' not in p.parts}
def norm(s,work):return s.replace(str(work),'$WORK').replace(str(HERE),'$REPORT')

def env_for(target,extra=None):
    e=dict(os.environ);e.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
        'CARGO_TARGET_DIR':str(target),'CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0',
        'RAYON_NUM_THREADS':'1','CHARON_TOOLCHAIN_IS_IN_PATH':'1',
        'PATH':os.pathsep.join([str(RBIN),str(TOOLS/'bin'),e.get('PATH','')]),
        'DYLD_LIBRARY_PATH':os.pathsep.join([str(RLIB),str(RLIB/'rustlib/aarch64-apple-darwin/lib'),e.get('DYLD_LIBRARY_PATH','')])})
    e.update(extra or {});return e

def projection(path):
    try:d=json.loads(path.read_text())
    except (OSError,UnicodeDecodeError,json.JSONDecodeError):return None
    t=d.get('translated') or {};fs=[]
    for x in t.get('fun_decls',[]):
        if not x or not x.get('item_meta',{}).get('is_local'):continue
        m=x['item_meta'];parts=[y['Ident'][0] for y in m['name'] if 'Ident' in y]
        fs.append({'name':'::'.join(parts),'span':m.get('span'),'source_text':m.get('source_text'),
                   'body_sha256':hashlib.sha256(json.dumps(x.get('body'),sort_keys=True).encode()).hexdigest(),
                   'markers':[a['DocComment'].strip() for a in m.get('attr_info',{}).get('attributes',[])
                              if isinstance(a,dict) and 'DocComment' in a]})
    return {'crate_name':t.get('crate_name'),'has_errors':d.get('has_errors'),
            'local_functions':fs,'file_names':[x.get('name') for x in t.get('files',[])],
            'raw_sha256':sha(path)}

def invoke(label,root,target,dest,flags,work,extra=None,quota=None):
    command=[CHARON,'cargo','--preset','aeneas','--dest-file',dest,'--',
             '--manifest-path',root/'Cargo.toml','--package','subject_matrix',*flags,
             '--offline','--locked','-v']
    env=env_for(target,extra)
    def limit():
        if quota is not None:resource.setrlimit(resource.RLIMIT_FSIZE,(quota,quota))
    start=time.monotonic()
    p=subprocess.Popen([str(x) for x in command],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                       text=True,start_new_session=True,preexec_fn=limit)
    try:out,err=p.communicate(timeout=60)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=5);raise TimeoutError(label)
    elapsed=round(time.monotonic()-start,4)
    ps=subprocess.run(['/bin/ps','-axo','pid=,pgid='],capture_output=True,text=True,timeout=5)
    group_pids=[]
    for line in ps.stdout.splitlines():
        fields=line.split()
        if len(fields)==2 and fields[1]==str(p.pid):group_pids.append(int(fields[0]))
    invoked_units=re.findall(r'^\s*Running `[^\n]*charon-driver rustc --crate-name ([^ ]+)',err,re.MULTILINE)
    manifest={'label':label,'cwd':norm(str(root),work),'source_tree':files(root),
              'target_dir':norm(str(target),work),'destination':norm(str(dest),work),
              'argv':[norm(str(x),work) for x in command],
              'environment':{'CARGO_TARGET_DIR':norm(str(target),work),'CARGO_BUILD_JOBS':'1',
                             'CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
                             'RUSTFLAGS':env.get('RUSTFLAGS'),'FILE_SIZE_LIMIT':quota},
              'charon_sha256':sha(CHARON),'cargo_sha256':sha(CARGO),'rustc_sha256':sha(RUSTC),
              'exit':p.returncode,'seconds':elapsed,'stdout':norm(out,work),'stderr':norm(err,work),
              'charon_driver_crate_invocations':invoked_units,
              'remaining_process_group_pids':group_pids,
              'destination_exists':dest.exists(),'destination_bytes':dest.stat().st_size if dest.exists() else None,
              'destination_sha256':sha(dest) if dest.exists() else None,
              'projection':projection(dest) if dest.exists() else None}
    (MAN/(label+'.json')).write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    return manifest

def make_workspace(src,dest):
    shutil.copytree(src,dest)
    return dest

def main():
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=pathlib.Path,required=True);args=ap.parse_args()
    work=args.work.resolve()
    if work.exists():raise SystemExit('choose an absent owned --work path')
    if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('15 GiB free-disk guard')
    work.mkdir(parents=True)
    for path in (ART,MAN):
        if path.exists():shutil.rmtree(path)
        path.mkdir()
    cases=[]
    def case(label,flags,variant='A',extra=None,quota=None):
        root=make_workspace(FIX,work/('source-'+label))
        if variant=='B':
            p=root/'src/lib.rs';s=p.read_text();s=s.replace('/// source marker: alpha\npub fn alpha(x: u32) -> u32 { x.wrapping_add(1) }\n/// source marker: beta\npub fn beta(x: u32) -> u32 { x.wrapping_mul(2) }',
                '/// source marker: beta\npub fn beta(x: u32) -> u32 { x.wrapping_mul(2) }\n/// source marker: alpha\npub fn alpha(x: u32) -> u32 { x.wrapping_add(1) }')
            assert s!=p.read_text();p.write_text(s)
        elif variant=='comment':
            p=root/'src/lib.rs';p.write_text('// unrelated prefix\n'+p.read_text())
        target=work/('target-'+label);dest=ART/(label+'.llbc')
        r=invoke(label,root,target,dest,flags,work,extra,quota);cases.append(r);return r
    base=case('lib-base',['--lib']);assert base['exit']==0 and base['projection']
    bin_=case('bin-base',['--bin','subject_matrix_cli']);assert bin_['exit']==0 and bin_['projection']
    tests=[case(label,['--test','check']) for label in ('test-base','test-repeat-1','test-repeat-2','test-repeat-3')]
    assert all(x['exit']==0 and x['projection'] for x in tests)
    feature=case('lib-feature',['--lib','--features','selected']);assert feature['exit']==0 and feature['projection']
    host=case('lib-explicit-host',['--lib','--target','aarch64-apple-darwin']);assert host['exit']==0 and host['projection']
    flag=case('lib-rustflags',['--lib'],extra={'RUSTFLAGS':'-C opt-level=1'});assert flag['exit']==0 and flag['projection']
    comment=case('lib-comment',['--lib'],variant='comment');assert comment['exit']==0
    reorder=case('lib-reorder',['--lib'],variant='B');assert reorder['exit']==0
    restored=case('lib-restored',['--lib']);assert restored['exit']==0
    # Private output and target roots permit two simultaneous Charon processes.
    pair=[]
    for label,flags in [('parallel-default',['--lib']),('parallel-feature',['--lib','--features','selected'])]:
        root=make_workspace(FIX,work/('source-'+label));target=work/('target-'+label);dest=ART/(label+'.llbc')
        pair.append((label,root,target,dest,flags))
    import concurrent.futures
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        futures=[pool.submit(invoke,label,root,target,dest,flags,work) for label,root,target,dest,flags in pair]
        concurrent=[f.result() for f in futures]
    cases.extend(concurrent)
    assert all(x['exit']==0 and x['projection'] for x in concurrent)
    assert concurrent[0]['projection']['crate_name']==concurrent[1]['projection']['crate_name']
    # Output-phase failure: a regular-file destination is preseeded with a successful output,
    # and the process is denied writes beyond 4 KiB during Charon's serialization.
    good=ART/'last-good.llbc';shutil.copyfile(ART/'lib-base.llbc',good)
    active=ART/'quota-active.llbc';shutil.copyfile(good,active)
    quota_root=make_workspace(FIX,work/'source-quota')
    failed=invoke('quota-output-failure',quota_root,work/'target-quota',active,['--lib'],work,quota=4096)
    cases.append(failed)
    assert failed['exit']!=0 and sha(good)==base['destination_sha256']
    failed_state={'exit':failed['exit'],'bytes':failed['destination_bytes'],
                  'sha256':failed['destination_sha256'],'parseable':failed['projection'] is not None,
                  'same_as_old':failed['destination_sha256']==sha(good),
                  'last_good_sha256':sha(good)}
    if active.exists():shutil.copyfile(active,ART/'quota-partial.llbc')
    qt=work/'target-quota'
    quota_files=[p for p in qt.rglob('*') if p.is_file()]
    failed_state['target_before_retry']={'files':len(quota_files),
                                         'bytes':sum(p.stat().st_size for p in quota_files)}
    retry=invoke('quota-retry',quota_root,work/'target-quota',active,['--lib'],work)
    cases.append(retry);assert retry['exit']==0 and retry['projection'] and sha(good)==base['destination_sha256']
    # Negative host-target control where installed std is unavailable; no output is a result.
    unsupported=case('target-x86-missing-std',['--lib','--target','x86_64-apple-darwin'])
    assert unsupported['exit']!=0 and not unsupported['projection']
    def names(r):return {x['name'].split('::')[-1] for x in r['projection']['local_functions']}
    assert 'default_only' in names(base) and 'feature_only' not in names(base)
    assert 'feature_only' in names(feature) and 'default_only' not in names(feature)
    assert 'main' in names(bin_)
    assert all(set(x['charon_driver_crate_invocations'])=={'subject_matrix','check','subject_matrix_cli'}
               and len(x['charon_driver_crate_invocations'])==3 for x in tests)
    assert all(x['projection']['crate_name'] in {'subject_matrix','check','subject_matrix_cli'} for x in tests)
    assert names(base)==names(host)==names(flag)==names(comment)==names(reorder)==names(restored)
    assert sha(ART/'lib-base.llbc')==base['destination_sha256']
    assert all(not x['remaining_process_group_pids'] for x in cases)
    target_inventory={}
    for x in cases:
        target=work/('target-'+x['label'])
        if target.exists():
            fs=[p for p in target.rglob('*') if p.is_file()]
            target_inventory[x['label']]={'files':len(fs),'bytes':sum(p.stat().st_size for p in fs)}
    qfiles=[p for p in qt.rglob('*') if p.is_file()]
    target_inventory['quota-shared-retry']={'files':len(qfiles),'bytes':sum(p.stat().st_size for p in qfiles)}
    semantic={x['label']:{'crate_name':x['projection']['crate_name'] if x['projection'] else None,
                         'local_names':sorted(names(x)) if x['projection'] else None,
                         'raw_sha256':x['destination_sha256']} for x in cases}
    result={'environment':{'platform':platform.platform(),'python':sys.version,
                           'charon_sha256':sha(CHARON),'cargo_sha256':sha(CARGO),'rustc_sha256':sha(RUSTC)},
            'fixture':files(FIX),'cases':cases,'semantic':semantic,'quota_output':failed_state,
            'target_inventory':target_inventory,'max_concurrent_charon_processes':2}
    RAW.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'cases':len(cases),'quota_output':failed_state,
                      'concurrent_outputs':[x['destination_sha256'] for x in concurrent]},sort_keys=True))

if __name__=='__main__':main()
