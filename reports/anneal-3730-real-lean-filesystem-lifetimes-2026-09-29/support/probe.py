#!/usr/bin/env python3
"""Real Lean .olean lifetimes on APFS plus byte-level overlayfs readers."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import pwd
import shutil
import subprocess
import sys
import time
import uuid

HERE=Path(__file__).resolve().parent
FIX=HERE/'fixture'
ART=HERE/'artifacts'
OUT=HERE/'results.json'
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
DOCKER=Path('/usr/local/bin/docker')
IMAGE='ubuntu:24.04'


def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def wait_file(p,timeout=10):
    end=time.monotonic()+timeout
    while not p.exists():
        if time.monotonic()>end:raise TimeoutError(str(p))
        time.sleep(.02)


def env_base():
    e=dict(os.environ);e.setdefault('HOME',pwd.getpwuid(os.getuid()).pw_dir)
    e['LEAN_NUM_THREADS']='1'
    return e


def call(records,label,argv,cwd=None,env=None,timeout=15):
    start=time.monotonic()
    p=subprocess.run([str(x) for x in argv],cwd=cwd,env=env or env_base(),
                     capture_output=True,text=True,timeout=timeout)
    rec={'label':label,'argv':[str(x) for x in argv],
         'cwd':str(cwd) if cwd else None,'exit':p.returncode,
         'seconds':round(time.monotonic()-start,4),'stdout':p.stdout,'stderr':p.stderr}
    records.append(rec)
    return rec


def lean_batch(records,label,source,lean_path,cwd):
    e=env_base();e['LEAN_PATH']=str(lean_path)
    return call(records,label,[LEAN,'--json',source],cwd,e)


def stat_id(p):
    s=Path(p).stat();return {'device':s.st_dev,'inode':s.st_ino,'links':s.st_nlink,
                             'bytes':s.st_size,'sha256':sha(p)}


def docker(records,label,*args,timeout=15):
    return call(records,label,[DOCKER,*args],timeout=timeout)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);a=ap.parse_args()
    work=a.work.resolve()
    if work.exists():raise SystemExit('choose an absent --work path')
    if shutil.disk_usage(work.parent).free<15*(1<<30):raise SystemExit('disk guard: 15 GiB free required')
    if ART.exists():shutil.rmtree(ART)
    ART.mkdir();work.mkdir(parents=True)
    records=[];obs={}
    build7,build9=work/'build7',work/'build9'
    build7.mkdir();build9.mkdir()
    shutil.copyfile(FIX/'Dep7.lean',build7/'Dep.lean')
    shutil.copyfile(FIX/'Dep9.lean',build9/'Dep.lean')
    shutil.copyfile(FIX/'Plugin.lean',build7/'Plugin.lean')
    for label,src,dest in [('compile-dep7',build7/'Dep.lean',build7/'Dep.olean'),
                           ('compile-dep9',build9/'Dep.lean',build9/'Dep.olean'),
                           ('compile-plugin',build7/'Plugin.lean',build7/'Plugin.olean')]:
        r=call(records,label,[LEAN,'-o',dest,src],src.parent)
        assert r['exit']==0,(label,r)
    for src,name in [(build7/'Dep.olean','Dep7.olean'),(build9/'Dep.olean','Dep9.olean'),
                     (build7/'Plugin.olean','Plugin.olean')]:shutil.copyfile(src,ART/name)
    apfs=work/'apfs';live=apfs/'live';live.mkdir(parents=True)
    shutil.copyfile(build7/'Dep.olean',live/'Dep.olean')
    shutil.copyfile(build7/'Plugin.olean',live/'Plugin.olean')
    consumer7=FIX/'Consumer7.lean';consumer9=FIX/'Consumer9.lean'
    before=lean_batch(records,'apfs-batch7-before',consumer7,live,apfs)
    assert before['exit']==0 and '"data":"7"' in before['stdout']
    (apfs/'dir-link').symlink_to(live,target_is_directory=True)
    hard=apfs/'hard';hard.mkdir()
    os.link(live/'Dep.olean',hard/'Dep.olean')
    os.link(live/'Plugin.olean',hard/'Plugin.olean')
    alias_runs={}
    alias_runs['dir_symlink']=lean_batch(records,'apfs-symlink-root-before',consumer7,apfs/'dir-link',apfs)['exit']
    alias_runs['hardlink']=lean_batch(records,'apfs-hardlink-root-before',consumer7,hard,apfs)['exit']
    alias_runs['relative']=lean_batch(records,'apfs-relative-root-before',consumer7,Path('live'),apfs)['exit']
    case_dir=apfs/'Case';case_dir.mkdir()
    os.symlink(live/'Dep.olean',case_dir/'Dep.olean');os.symlink(live/'Plugin.olean',case_dir/'Plugin.olean')
    case_alias=apfs/'case';case_same=case_alias.exists() and os.path.samefile(case_dir,case_alias)
    if case_same:alias_runs['case_alias']=lean_batch(records,'apfs-case-root-before',consumer7,case_alias,apfs)['exit']
    nfc=apfs/'é';nfd=apfs/'e\u0301';nfc.mkdir()
    os.symlink(live/'Dep.olean',nfc/'Dep.olean');os.symlink(live/'Plugin.olean',nfc/'Plugin.olean')
    unicode_same=nfd.exists() and os.path.samefile(nfc,nfd)
    if unicode_same:alias_runs['unicode_alias']=lean_batch(records,'apfs-unicode-root-before',consumer7,nfd,apfs)['exit']
    assert all(x==0 for x in alias_runs.values())
    obs['apfs_aliases']={'case_same_directory':case_same,'unicode_same_directory':unicode_same,
       'case_directory_entries':sorted(x.name for x in apfs.iterdir()),'batch_exits':alias_runs,
       'live_before':stat_id(live/'Dep.olean'),'hard_before':stat_id(hard/'Dep.olean'),
       'symlink_resolves_to':str((apfs/'dir-link').resolve())}
    # Host reader holds both mmap and fd; resident Lean has imported Dep7.
    reader=subprocess.Popen([sys.executable,str(HERE/'host_reader.py'),str(live/'Dep.olean'),str(apfs)],
                            cwd=apfs,env=env_base(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    marker=apfs/'lean-ready'
    resident=apfs/'Resident.lean'
    resident.write_text('import Dep\nimport Plugin\nrun_cmd do\n  IO.FS.writeFile '+json.dumps(str(marker))+' "ready"\n  IO.sleep 4000\n#eval depValue\n')
    e=env_base();e['LEAN_PATH']=str(live)
    lean_res=subprocess.Popen([str(LEAN),'--json',str(resident)],cwd=apfs,env=e,
                              stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    wait_file(apfs/'host-ready');wait_file(marker)
    assert reader.poll() is None and lean_res.poll() is None
    original=stat_id(live/'Dep.olean')
    staged=live/'.Dep.olean.next';shutil.copyfile(build9/'Dep.olean',staged)
    os.replace(staged,live/'Dep.olean')
    after_replace=stat_id(live/'Dep.olean')
    batch9=lean_batch(records,'apfs-fresh-batch9-after-rename',consumer9,live,apfs)
    wrong7=lean_batch(records,'apfs-fresh-batch7-after-rename',consumer7,live,apfs)
    assert batch9['exit']==0 and '"data":"9"' in batch9['stdout'] and wrong7['exit']!=0
    (apfs/'host-go1').write_text('go');wait_file(apfs/'host-ack1')
    phase1=json.loads((apfs/'host-phase1.json').read_text())
    hard_after_replace=stat_id(hard/'Dep.olean')
    assert lean_res.poll() is None
    (live/'Dep.olean').unlink()
    missing=lean_batch(records,'apfs-fresh-batch-after-unlink',consumer9,live,apfs)
    assert missing['exit']!=0
    (apfs/'host-go2').write_text('go');wait_file(apfs/'host-ack2')
    phase2=json.loads((apfs/'host-phase2.json').read_text())
    shutil.copyfile(apfs/'host-phase1.json',ART/'apfs-reader-phase1.json')
    shutil.copyfile(apfs/'host-phase2.json',ART/'apfs-reader-phase2.json')
    reader_out,reader_err=reader.communicate(timeout=5)
    resident_out,resident_err=lean_res.communicate(timeout=6)
    records.append({'label':'apfs-open-mmap-reader','exit':reader.returncode,'stdout':reader_out,'stderr':reader_err})
    records.append({'label':'apfs-resident-lean','exit':lean_res.returncode,'stdout':resident_out,'stderr':resident_err})
    assert reader.returncode==lean_res.returncode==0 and '"data":"7"' in resident_out
    assert phase1['fd_sha256']==phase1['map_sha256']==original['sha256']
    assert phase1['path_sha256']==after_replace['sha256']
    assert phase2['fd_sha256']==phase2['map_sha256']==original['sha256'] and not phase2['path_exists']
    assert hard_after_replace['sha256']==original['sha256']
    shutil.copyfile(build9/'Dep.olean',live/'Dep.olean')
    republished=lean_batch(records,'apfs-fresh-batch-after-republish',consumer9,live,apfs)
    hard_old=lean_batch(records,'apfs-hardlink-old-after-republish',consumer7,hard,apfs)
    assert republished['exit']==hard_old['exit']==0
    obs['apfs_lifecycle']={'old':original,'replacement':after_replace,'hardlink_after_replace':hard_after_replace,
                           'reader_phase1':phase1,'reader_phase2':phase2,'resident_value7':True,
                           'fresh_value9_after_replace':True,'missing_after_unlink':True}
    shutil.copyfile(live/'Dep.olean',ART/'apfs-republished-Dep.olean')
    # Probe the cached Ubuntu image only. No bind mounts, network, pull, or install.
    info=docker(records,'docker-info','info','--format','{{.Driver}} {{.Architecture}} {{.MemTotal}}')
    img=docker(records,'cached-image-inspect','image','inspect',IMAGE,'--format','{{.Id}} {{.Architecture}} {{.Os}}')
    assert info['exit']==img['exit']==0
    cid='anneal-lean-life-'+uuid.uuid4().hex[:12]
    run=docker(records,'ubuntu-start','run','-d','--rm','--pull=never','--network=none',
               '--platform','linux/amd64','--memory=512m','--cpus=1','--name',cid,IMAGE,'sleep','120')
    assert run['exit']==0,run
    try:
        def dx(label,*args):return docker(records,label,'exec',cid,*args)
        assert dx('ubuntu-mkdir','mkdir','-p','/tmp/lean-life/hard')['exit']==0
        for src,dest in [(ART/'Dep7.olean','Dep.olean'),(ART/'Dep9.olean','Dep9.olean'),
                         (ART/'Plugin.olean','Plugin.olean'),(HERE/'overlay_reader.pl','overlay_reader.pl')]:
            assert docker(records,'ubuntu-copy-'+dest,'cp',src,f'{cid}:/tmp/lean-life/{dest}')['exit']==0
        assert dx('ubuntu-symlink-root','ln','-s','/tmp/lean-life','/tmp/lean-life-alias')['exit']==0
        assert dx('ubuntu-hardlink','ln','/tmp/lean-life/Dep.olean','/tmp/lean-life/hard/Dep.olean')['exit']==0
        fs=dx('ubuntu-fs','stat','-f','-c','%T','/tmp/lean-life')
        arch=dx('ubuntu-uname','uname','-m')
        release=dx('ubuntu-release','cat','/etc/os-release')
        alias_code='use utf8; mkdir("/tmp/lean-life/Case"); mkdir("/tmp/lean-life/é"); print "case=".(-d "/tmp/lean-life/case"?1:0)." unicode=".(-d "/tmp/lean-life/e\\x{301}"?1:0)."\\n";'
        aliases=dx('ubuntu-case-unicode','perl','-e',alias_code)
        initial=dx('ubuntu-initial-hash','sha256sum','/tmp/lean-life/Dep.olean','/tmp/lean-life/hard/Dep.olean')
        overlay_reader=subprocess.Popen([str(DOCKER),'exec',cid,'perl','/tmp/lean-life/overlay_reader.pl'],
                                        env=env_base(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        def dwait(path,seconds=10):
            end=time.monotonic()+seconds
            while time.monotonic()<end:
                if dx('ubuntu-wait-'+path.rsplit('/',1)[-1],'test','-e',path)['exit']==0:return
                if overlay_reader.poll() is not None:break
                time.sleep(.04)
            raise TimeoutError(path)
        dwait('/tmp/lean-life/ready')
        assert overlay_reader.poll() is None
        assert dx('ubuntu-atomic-replace','mv','-f','/tmp/lean-life/Dep9.olean','/tmp/lean-life/Dep.olean')['exit']==0
        replaced=dx('ubuntu-replaced-hash','sha256sum','/tmp/lean-life/Dep.olean','/tmp/lean-life/hard/Dep.olean')
        assert docker(records,'ubuntu-copy-roundtrip-new','cp',f'{cid}:/tmp/lean-life/Dep.olean',work/'linux-new-Dep.olean')['exit']==0
        assert docker(records,'ubuntu-copy-roundtrip-plugin','cp',f'{cid}:/tmp/lean-life/Plugin.olean',work/'linux-Plugin.olean')['exit']==0
        assert dx('ubuntu-go1','touch','/tmp/lean-life/go1')['exit']==0;dwait('/tmp/lean-life/ack1')
        assert dx('ubuntu-unlink','rm','/tmp/lean-life/Dep.olean')['exit']==0
        missing_linux=dx('ubuntu-missing','test','-e','/tmp/lean-life/Dep.olean')
        assert missing_linux['exit']!=0
        assert dx('ubuntu-go2','touch','/tmp/lean-life/go2')['exit']==0;dwait('/tmp/lean-life/ack2')
        overlay_out,overlay_err=overlay_reader.communicate(timeout=5)
        records.append({'label':'ubuntu-mmap-open-reader','exit':overlay_reader.returncode,
                        'stdout':overlay_out,'stderr':overlay_err})
        assert overlay_reader.returncode==0,(overlay_out,overlay_err)
        linux_snap=work/'linux-snapshots';linux_snap.mkdir()
        for name in ('phase1-map.bin','phase1-fd.bin','phase2-map.bin','phase2-fd.bin'):
            assert docker(records,'ubuntu-copy-'+name,'cp',f'{cid}:/tmp/lean-life/{name}',linux_snap/name)['exit']==0
        assert docker(records,'ubuntu-copy-roundtrip-old','cp',f'{cid}:/tmp/lean-life/hard/Dep.olean',work/'linux-old-Dep.olean')['exit']==0
        snap_hashes={name:sha(linux_snap/name) for name in ('phase1-map.bin','phase1-fd.bin','phase2-map.bin','phase2-fd.bin')}
        for name in snap_hashes:shutil.copyfile(linux_snap/name,ART/('overlayfs-'+name))
        assert all(h==original['sha256'] for h in snap_hashes.values())
        assert sha(work/'linux-new-Dep.olean')==after_replace['sha256']
        assert sha(work/'linux-old-Dep.olean')==original['sha256']
        round_new=work/'roundtrip-new';round_new.mkdir()
        shutil.copyfile(work/'linux-new-Dep.olean',round_new/'Dep.olean')
        shutil.copyfile(work/'linux-Plugin.olean',round_new/'Plugin.olean')
        round_old=work/'roundtrip-old';round_old.mkdir()
        shutil.copyfile(work/'linux-old-Dep.olean',round_old/'Dep.olean')
        shutil.copyfile(work/'linux-Plugin.olean',round_old/'Plugin.olean')
        batch_linux9=lean_batch(records,'host-lean-roundtrip-overlay-new',consumer9,round_new,work)
        batch_linux7=lean_batch(records,'host-lean-roundtrip-overlay-old-hardlink',consumer7,round_old,work)
        assert batch_linux9['exit']==batch_linux7['exit']==0
        obs['overlayfs']={'docker_info':info['stdout'].strip(),'image':img['stdout'].strip(),
            'filesystem':fs['stdout'].strip(),'uname_machine':arch['stdout'].strip(),
            'os_release':[x for x in release['stdout'].splitlines() if x.startswith(('PRETTY_NAME=','VERSION_ID='))],
            'alias_stdout':aliases['stdout'].strip(),
            'initial_sha256sum':initial['stdout'].strip(),'after_replace_sha256sum':replaced['stdout'].strip(),
            'mapped_fd_snapshot_sha256':snap_hashes,'missing_after_unlink':True,
            'host_batch_roundtrip_new_exit':batch_linux9['exit'],
            'host_batch_roundtrip_old_exit':batch_linux7['exit'],
            'linux_lean_executed':False}
        for src,name in [(work/'linux-new-Dep.olean','overlayfs-new-Dep.olean'),
                         (work/'linux-old-Dep.olean','overlayfs-old-hardlink-Dep.olean'),
                         (work/'linux-Plugin.olean','overlayfs-Plugin.olean')]:shutil.copyfile(src,ART/name)
    finally:
        docker(records,'ubuntu-stop','rm','-f',cid)
    disk=call(records,'apfs-diskutil',['diskutil','info','/System/Volumes/Data'],timeout=10)
    df=call(records,'apfs-df',['df','-P',apfs],timeout=10)
    assert disk['exit']==df['exit']==0 and 'File System Personality:   APFS' in disk['stdout']
    obs['environment']={'platform':platform.platform(),'python':sys.version,
                        'lean_sha256':sha(LEAN),'apfs_diskutil_excerpt':[line.strip() for line in disk['stdout'].splitlines()
                        if any(x in line for x in ('File System Personality','Type (Bundle)','Mount Point','Device Node'))],
                        'apfs_df':df['stdout'].strip()}
    def norm(s):return s.replace(str(work),'$WORK').replace(str(HERE),'$REPORT').replace(cid,'$CONTAINER')
    for r in records:
        for k in ('stdout','stderr','cwd'):
            if isinstance(r.get(k),str):r[k]=norm(r[k])
        if 'argv' in r:r['argv']=[norm(x) for x in r['argv']]
    OUT.write_text(json.dumps({'observations':obs,'records':records},indent=2,sort_keys=True)+'\n')
    print(json.dumps({'apfs':obs['apfs_lifecycle'],'overlay':obs['overlayfs'],
                      'records':len(records)},sort_keys=True))

if __name__=='__main__':main()
