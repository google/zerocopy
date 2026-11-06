#!/usr/bin/env python3
"""One-shot guarded Charon alias versus physical-copy source identity probe."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import time
from datetime import datetime, timezone

HERE=Path(__file__).resolve().parent
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON=TOOLS/'bin/charon'
CARGO=RUST/'cargo'
RUSTC=RUST/'rustc'
PINS={'charon':'51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b',
      'cargo':'71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1',
      'rustc':'2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc'}
WORK=HERE/'work';RAW=HERE/'raw';ART=HERE/'artifacts';RESULT=HERE/'results.json'
MIN_START=30.0;MIN_LIVE=20.0;MIN_DISK=10*1024**3
MAX_RSS_KIB=512*1024;MAX_SCRATCH_KIB=100*1024;TIMEOUT=15.0

def sha(raw):return hashlib.sha256(raw).hexdigest()
def now():return datetime.now(timezone.utc).isoformat()
def headroom():
    text=subprocess.check_output(['/usr/bin/vm_stat'],text=True,timeout=5)
    page=int(re.search(r'page size of (\d+) bytes',text).group(1))
    counts={x:int(re.search(rf'Pages {x}:\s+(\d+)\.',text).group(1)) for x in ('free','inactive','speculative')}
    phys=int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True,timeout=5))
    return {'estimated_reclaimable_percent':round(100*page*sum(counts.values())/phys,4),
            'free_disk_bytes':shutil.disk_usage(HERE).free,'page_size':page,'pages':counts,'physical_bytes':phys}
def rss_kib(pgid):
    if pgid is None:return 0
    output=subprocess.check_output(['/bin/ps','-axo','pgid=,rss=,state='],text=True,timeout=5)
    return sum(int(cols[1]) for line in output.splitlines() if len(cols:=line.split())==3
               and cols[0]==str(pgid) and not cols[2].startswith('Z'))
def scratch_kib():
    return int(subprocess.check_output(['/usr/bin/du','-sk',str(WORK)],text=True,timeout=5).split()[0]) if WORK.exists() else 0
def sample(pgid,start):
    host=headroom()
    row={'elapsed_seconds':round(time.monotonic()-start,4),'host':host,
         'process_group_rss_kib':rss_kib(pgid),'scratch_kib':scratch_kib()}
    reason=(('memory_guard' if host['estimated_reclaimable_percent']<MIN_LIVE else None)
            or ('disk_guard' if host['free_disk_bytes']<MIN_DISK else None)
            or ('rss_guard' if row['process_group_rss_kib']>MAX_RSS_KIB else None)
            or ('scratch_guard' if row['scratch_kib']>MAX_SCRATCH_KIB else None)
            or ('timeout_guard' if row['elapsed_seconds']>TIMEOUT else None))
    return row,reason
def admit():
    row,reason=sample(None,time.monotonic())
    if not reason and row['host']['estimated_reclaimable_percent']<=MIN_START:reason='admission_memory'
    return row,reason
def stop(proc):
    if proc.poll() is not None:return
    try:os.killpg(proc.pid,signal.SIGTERM)
    except ProcessLookupError:return
    try:proc.wait(timeout=2)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid,signal.SIGKILL);proc.wait(timeout=2)

def environment(target):
    env=dict(os.environ)
    for k in ('RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER'):
        env.pop(k,None)
    env.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
                'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_NET_OFFLINE':'true',
                'CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
                'CARGO_TARGET_DIR':str(target),
                'PATH':os.pathsep.join((str(RUST),str(TOOLS/'bin'),env.get('PATH',''))),
                'DYLD_LIBRARY_PATH':os.pathsep.join((str(RUST.parent/'lib'),
                  str(RUST.parent/'lib/rustlib/aarch64-apple-darwin/lib'),env.get('DYLD_LIBRARY_PATH','')))})
    return env

def fixture_layout(kind,oracle):
    root=WORK/kind
    shutil.copytree(HERE/'fixture',root)
    source=root/'src/shared.rs'
    entries=[]
    for rel in oracle['module_relative_paths']:
        path=root/rel;path.parent.mkdir(parents=True)
        if kind=='alias':path.symlink_to(oracle['alias_target'])
        else:shutil.copyfile(source,path)
        lst=path.lstat();st=path.stat();base=source.stat()
        entries.append({'relative_path':rel,'is_symlink':stat.S_ISLNK(lst.st_mode),
                        'link_text':os.readlink(path) if path.is_symlink() else None,
                        'source_sha256':sha(path.read_bytes()),'lstat_inode':lst.st_ino,
                        'target_dev':st.st_dev,'target_inode':st.st_ino,
                        'shared_dev':base.st_dev,'shared_inode':base.st_ino,
                        'resolved_path':str(path.resolve())})
    assert all(e['source_sha256']==oracle['fixture_sha256']['src/shared.rs'] for e in entries)
    assert (entries[0]['target_dev'],entries[0]['target_inode'])==(entries[1]['target_dev'],entries[1]['target_inode']) if kind=='alias' else entries[0]['target_inode']!=entries[1]['target_inode']
    return root,entries

def decode(path):
    raw=path.read_bytes();doc=json.loads(raw);translated=doc['translated']
    files=[]
    for f in translated['files']:
        files.append({'id':f['id'],'name':f['name'],'crate_name':f['crate_name'],
                      'contents':f['contents'],'contents_sha256':sha(f['contents'].encode()) if f['contents'] is not None else None})
    items=[]
    for kind,decls in (('function',translated['fun_decls']),('global',translated['global_decls']),('type',translated['type_decls'])):
        for d in decls:
            m=d.get('item_meta',{})
            if not m.get('is_local'):continue
            name='::'.join(part['Ident'][0] for part in m['name'] if 'Ident' in part)
            items.append({'kind':kind,'def_id':d.get('def_id'),'name':name,'file_id':m['span']['data']['file_id'],
                          'span':m['span'],'source_text':m.get('source_text')})
    return {'sha256':sha(raw),'bytes':len(raw),'has_errors':doc['has_errors'],
            'crate_name':translated['crate_name'],'dest_file':translated['options']['dest_file'],
            'files':files,'local_items':items,'item_names':translated['item_names']}

def run(kind,root):
    before,refusal=admit()
    out={'preflight':before,'status':'admission_denied' if refusal else 'running','stop_reason':refusal}
    if refusal:return out
    target=WORK/f'target-{kind}';dest=ART/f'{kind}.llbc';env=environment(target)
    argv=[str(CHARON),'cargo','--preset','aeneas','--dest-file',str(dest),'--',
          '--manifest-path',str(root/'Cargo.toml'),'--lib','--offline','--locked','-v','-j','1']
    out.update({'argv':argv,'cwd':str(root),'environment':{k:env[k] for k in
             ('RUSTUP_HOME','CARGO_HOME','CHARON_TOOLCHAIN_IS_IN_PATH','CARGO_NET_OFFLINE',
              'CARGO_BUILD_JOBS','CARGO_INCREMENTAL','RAYON_NUM_THREADS','CARGO_TARGET_DIR','PATH','DYLD_LIBRARY_PATH')},
             'started_utc':now(),'samples':[]})
    stdout=(RAW/f'{kind}.stdout').open('wb');stderr=(RAW/f'{kind}.stderr').open('wb')
    started=time.monotonic();proc=subprocess.Popen(argv,cwd=root,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
    out['pid']=proc.pid
    while True:
        row,reason=sample(proc.pid,started);out['samples'].append(row)
        if reason or proc.poll() is not None:break
        time.sleep(.05)
    if reason:stop(proc)
    proc.wait(timeout=3);stdout.close();stderr.close()
    out.update({'status':'guard_stopped' if reason else 'completed','stop_reason':reason,'exit':proc.returncode,
                'ended_utc':now(),'stdout_sha256':sha((RAW/f'{kind}.stdout').read_bytes()),
                'stderr_sha256':sha((RAW/f'{kind}.stderr').read_bytes()),
                'postrun_group_rss_kib':rss_kib(proc.pid),'dest_exists':dest.exists()})
    if dest.exists():out['decoded']=decode(dest)
    return out

def main():
    assert not any(p.exists() for p in (WORK,RAW,ART,RESULT)),'one-shot outputs already exist'
    oracle_raw=(HERE/'oracle.json').read_bytes();oracle=json.loads(oracle_raw)
    for name,expected in oracle['fixture_sha256'].items():
        assert sha((HERE/'fixture'/name).read_bytes())==expected
    pins={k:sha(p.read_bytes()) for k,p in [('charon',CHARON),('cargo',CARGO),('rustc',RUSTC)]}
    assert pins==PINS
    result={'schema':1,'observed_utc':now(),'status':'prepared','stop_reason':None,
            'oracle_prelaunch_sha256':sha(oracle_raw),'binary_sha256':pins,
            'limits':{'minimum_start_reclaimable_percent':MIN_START,'minimum_live_reclaimable_percent':MIN_LIVE,
                      'minimum_disk_bytes':MIN_DISK,'maximum_process_group_rss_kib':MAX_RSS_KIB,
                      'maximum_scratch_kib':MAX_SCRATCH_KIB,'timeout_seconds':TIMEOUT},
            'layouts':{},'runs':{}}
    initial,reason=admit();result['initial_preflight']=initial
    if reason:
        result['status']='admission_denied';result['stop_reason']=reason
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(result['status']);return
    WORK.mkdir();RAW.mkdir();ART.mkdir()
    try:
        for kind in ('alias','copy'):
            root,entries=fixture_layout(kind,oracle)
            result['layouts'][kind]={'root':str(root),'entries':entries,
                                     'shared_sha256':sha((root/'src/shared.rs').read_bytes())}
        for kind in ('alias','copy'):
            result['runs'][kind]=run(kind,WORK/kind)
            if result['runs'][kind]['status']!='completed' or result['runs'][kind]['exit']!=0:
                result['status']='stopped_after_'+kind
                result['stop_reason']=result['runs'][kind]['stop_reason'] or 'command_failed'
                return
        result['status']='completed'
    finally:
        result['postrun_host']=headroom()
        shutil.rmtree(WORK)
        result['cleanup']={'work_exists_after':WORK.exists()}
        RESULT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'status':result['status'],'stop_reason':result['stop_reason'],
                          'runs':{k:(v['status'],v.get('exit')) for k,v in result['runs'].items()}}))

if __name__=='__main__':main()
