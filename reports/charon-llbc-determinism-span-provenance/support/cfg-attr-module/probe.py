#!/usr/bin/env python3
"""One-shot guarded Charon cfg_attr(path) module-file selection observation."""
import hashlib, json, os, re, shutil, signal, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

HERE=Path(__file__).resolve().parent
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
BIN={'charon':TOOLS/'bin/charon','cargo':RUST/'cargo','rustc':RUST/'rustc'}
PINS={'charon':'51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b',
      'cargo':'71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1',
      'rustc':'2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc'}
WORK=HERE/'work'; RAW=HERE/'raw'; ART=HERE/'artifacts'; RESULT=HERE/'results.json'
MIN_START=30;MIN_LIVE=20;MIN_DISK=10*1024**3;MAX_RSS=512*1024;MAX_SCRATCH=100*1024;TIMEOUT=15
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def headroom():
    t=subprocess.check_output(['/usr/bin/vm_stat'],text=True,timeout=5)
    page=int(re.search(r'page size of (\d+) bytes',t).group(1))
    counts={x:int(re.search(rf'Pages {x}:\s+(\d+)\.',t).group(1)) for x in ('free','inactive','speculative')}
    phys=int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True,timeout=5))
    return {'estimated_reclaimable_percent':round(100*page*sum(counts.values())/phys,4),
            'free_disk_bytes':shutil.disk_usage(HERE).free,'physical_bytes':phys,'page_size':page,'pages':counts}
def rss(pgid):
    if pgid is None:return 0
    out=subprocess.check_output(['/bin/ps','-axo','pgid=,rss=,state='],text=True,timeout=5)
    return sum(int(c[1]) for line in out.splitlines() if len(c:=line.split())==3 and c[0]==str(pgid) and not c[2].startswith('Z'))
def scratch():
    return int(subprocess.check_output(['/usr/bin/du','-sk',str(WORK)],text=True,timeout=5).split()[0]) if WORK.exists() else 0
def sample(pgid,start):
    h=headroom();s={'elapsed_seconds':round(time.monotonic()-start,4),'host':h,
                    'process_group_rss_kib':rss(pgid),'scratch_kib':scratch()}
    reason=('memory_guard' if h['estimated_reclaimable_percent']<MIN_LIVE else
            'disk_guard' if h['free_disk_bytes']<MIN_DISK else
            'rss_guard' if s['process_group_rss_kib']>MAX_RSS else
            'scratch_guard' if s['scratch_kib']>MAX_SCRATCH else
            'timeout_guard' if s['elapsed_seconds']>TIMEOUT else None)
    return s,reason
def admit():
    s,reason=sample(None,time.monotonic())
    if not reason and s['host']['estimated_reclaimable_percent']<=MIN_START:reason='admission_memory'
    return s,reason
def stop(p):
    if p.poll() is not None:return
    try:os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:return
    try:p.wait(timeout=2)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait(timeout=2)
def environment(target,flag=None):
    e=dict(os.environ)
    for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER'):e.pop(k,None)
    e.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
              'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1',
              'CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1','CARGO_TARGET_DIR':str(target),
              'PATH':os.pathsep.join((str(RUST),str(TOOLS/'bin'),e.get('PATH',''))),
              'DYLD_LIBRARY_PATH':os.pathsep.join((str(RUST.parent/'lib'),str(RUST.parent/'lib/rustlib/aarch64-apple-darwin/lib'),e.get('DYLD_LIBRARY_PATH','')))})
    if flag:e['RUSTFLAGS']=flag
    return e
def decode(path):
    raw=path.read_bytes();d=json.loads(raw);tr=d['translated']
    files=[{'id':f['id'],'name':f['name'],'crate_name':f['crate_name'],'contents':f['contents'],
            'contents_sha256':sha(f['contents'].encode()) if f['contents'] is not None else None} for f in tr['files']]
    items=[]
    for kind,decls in (('function',tr['fun_decls']),('global',tr['global_decls']),('type',tr['type_decls'])):
        for decl in decls:
            m=decl.get('item_meta',{})
            if not m.get('is_local'):continue
            name='::'.join(p['Ident'][0] for p in m['name'] if 'Ident' in p)
            items.append({'kind':kind,'def_id':decl.get('def_id'),'name':name,'file_id':m['span']['data']['file_id'],
                          'span':m['span'],'source_text':m.get('source_text')})
    return {'sha256':sha(raw),'bytes':len(raw),'has_errors':d['has_errors'],'crate_name':tr['crate_name'],
            'dest_file':tr['options']['dest_file'],'files':files,'local_items':items,'item_names':tr['item_names']}
def run(label,argv,cwd,env,dest=None):
    pre,reason=admit();out={'preflight':pre,'status':'admission_denied' if reason else 'running','stop_reason':reason}
    if reason:return out
    out.update({'argv':argv,'cwd':str(cwd),'environment':{k:env.get(k) for k in
        ('RUSTUP_HOME','CARGO_HOME','CHARON_TOOLCHAIN_IS_IN_PATH','CARGO_NET_OFFLINE','CARGO_BUILD_JOBS',
         'CARGO_INCREMENTAL','RAYON_NUM_THREADS','CARGO_TARGET_DIR','RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS',
         'RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','PATH','DYLD_LIBRARY_PATH')},'started_utc':now(),'samples':[]})
    stdout=(RAW/f'{label}.stdout').open('wb');stderr=(RAW/f'{label}.stderr').open('wb')
    start=time.monotonic();p=subprocess.Popen(argv,cwd=cwd,env=env,stdout=stdout,stderr=stderr,start_new_session=True);out['pid']=p.pid
    while True:
        s,reason=sample(p.pid,start);out['samples'].append(s)
        if reason or p.poll() is not None:break
        time.sleep(.05)
    if reason:stop(p)
    p.wait(timeout=3);stdout.close();stderr.close()
    out.update({'status':'guard_stopped' if reason else 'completed','stop_reason':reason,'exit':p.returncode,
                'ended_utc':now(),'stdout_sha256':sha((RAW/f'{label}.stdout').read_bytes()),
                'stderr_sha256':sha((RAW/f'{label}.stderr').read_bytes()),'postrun_group_rss_kib':rss(p.pid)})
    if dest is not None:
        out['dest_exists']=dest.exists()
        if dest.exists():out['decoded']=decode(dest)
    return out
def main():
    assert not any(p.exists() for p in (WORK,RAW,ART,RESULT)), 'one shot outputs already exist'
    oracle_raw=(HERE/'oracle.json').read_bytes();o=json.loads(oracle_raw)
    assert {k:sha(p.read_bytes()) for k,p in BIN.items()}==PINS
    assert {name:sha((HERE/'fixture'/name).read_bytes()) for name in o['fixture_sha256']}==o['fixture_sha256']
    result={'schema':1,'observed_utc':now(),'status':'prepared','stop_reason':None,'oracle_prelaunch_sha256':sha(oracle_raw),
      'binary_sha256':PINS,'limits':{'minimum_start_reclaimable_percent':MIN_START,'minimum_live_reclaimable_percent':MIN_LIVE,
      'minimum_disk_bytes':MIN_DISK,'maximum_process_group_rss_kib':MAX_RSS,
      'maximum_scratch_kib':MAX_SCRATCH,'timeout_seconds_per_process':TIMEOUT},'runs':{}}
    initial,reason=admit();result['initial_preflight']=initial
    if reason:
        result.update(status='admission_denied',stop_reason=reason)
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(result['status']);return
    WORK.mkdir();RAW.mkdir();ART.mkdir();crate=WORK/'crate';shutil.copytree(HERE/'fixture',crate)
    try:
        for label in ('default','alternate'):
            env=environment(WORK/f'target-{label}')
            dest=ART/f'{label}.llbc'
            argv=[str(BIN['charon']),'cargo','--preset','aeneas','--dest-file',str(dest),'--',
              '--manifest-path',str(crate/'Cargo.toml'),'--lib','--offline','--locked','-v','-j','1',
              *o['runs'][label]['cargo_flags']]
            result['runs'][label]=run(label,argv,crate,env,dest)
            rr=result['runs'][label]
            if rr['status']!='completed' or rr['exit']!=0:
                result['status']='stopped_after_'+label;result['stop_reason']=rr['stop_reason'] or 'unexpected_exit';return
        result['status']='completed'
    finally:
        result['postrun_host']=headroom();shutil.rmtree(WORK)
        result['cleanup']={'work_exists_after':WORK.exists()}
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'stop_reason':result['stop_reason'],
          'runs':{k:(v['status'],v.get('exit')) for k,v in result['runs'].items()}}))
if __name__=='__main__':main()
