#!/usr/bin/env python3
"""Disposable Darwin/APFS Lean .olean sharing probe. No network or new dependencies."""
import hashlib, json, os, pathlib, shutil, subprocess, sys, time

HERE = pathlib.Path(__file__).resolve().parent
WORK = HERE / 'work'
TOOLCHAIN = pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin')
LEAN, LAKE = TOOLCHAIN / 'lean', TOOLCHAIN / 'lake'
ENV = {**os.environ, 'ELAN_TOOLCHAIN':'leanprover/lean4:v4.30.0-rc2', 'LAKE_CACHE_DIR':'', 'LAKE_ARTIFACT_CACHE':'false', 'LEAN_NUM_THREADS':'1'}

def digest(p):
    h=hashlib.sha256()
    with open(p,'rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()

def run(cmd, cwd=None, env=None, timeout=45):
    t=time.monotonic()
    p=subprocess.run([str(x) for x in cmd], cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)
    return {'command':[str(x) for x in cmd], 'exit':p.returncode, 'stdout':p.stdout, 'stderr':p.stderr, 'elapsed_ms':round((time.monotonic()-t)*1000)}

def inventory(root):
    out=[]
    for p in sorted(root.rglob('*')):
        s=p.lstat()
        if p.is_dir() and not p.is_symlink(): continue
        item={'path':str(p.relative_to(root)), 'kind':'symlink' if p.is_symlink() else 'file', 'inode':s.st_ino, 'nlink':s.st_nlink, 'logical_bytes':s.st_size, 'allocated_bytes_by_st_blocks':s.st_blocks*512, 'mode':oct(s.st_mode & 0o777)}
        if p.is_symlink(): item['link_text']=os.readlink(p)
        else: item['sha256']=digest(p)
        out.append(item)
    return {'entries':out, 'file_count':sum(i['kind']=='file' for i in out), 'symlink_count':sum(i['kind']=='symlink' for i in out), 'logical_bytes':sum(i['logical_bytes'] for i in out if i['kind']=='file'), 'allocated_bytes_by_st_blocks':sum(i['allocated_bytes_by_st_blocks'] for i in out)}

def clean_run(r):
    s=json.dumps(r)
    s=s.replace(str(HERE),'$WORK').replace(str(TOOLCHAIN),'$LEAN_BIN').replace(str(TOOLCHAIN.parent),'$LEAN_HOME').replace(str(pathlib.Path.home()),'$HOME')
    return json.loads(s)

def main():
    if sys.platform!='darwin': raise SystemExit('Darwin only')
    if WORK.exists(): shutil.rmtree(WORK)
    WORK.mkdir()
    raw={'platform':run(['uname','-a']), 'fs':run(['diskutil','info','/System/Volumes/Data']), 'df':run(['df','-P',str(WORK)]), 'tools':{'lean_sha256':digest(LEAN),'lake_sha256':digest(LAKE)}, 'build':{}, 'modes':{}, 'open_reader':{}}
    for value in (7,9):
        package=WORK / f'prepared-{value}'
        package.mkdir()
        (package/'lean-toolchain').write_text('leanprover/lean4:v4.30.0-rc2\n')
        (package/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage Probe where\nlean_lib Dep\n')
        (package/'Dep.lean').write_text(f'def depValue : Nat := {value}\n')
        b=run([LAKE,'build','Dep','--keep-toolchain','--no-cache'],package,ENV,90)
        artifact=package/'.lake/build/lib/lean/Dep.olean'
        raw['build'][str(value)]={'result':b,'source_sha256':digest(package/'Dep.lean'),'lakefile_sha256':digest(package/'lakefile.lean'),'olean_sha256':digest(artifact) if artifact.exists() else None,'olean_bytes':artifact.stat().st_size if artifact.exists() else None}
        if b['exit']!=0 or not artifact.exists():
            (HERE/'raw.json').write_text(json.dumps(clean_run(raw),indent=2)+'\n')
            raise SystemExit('Lake build failed')
    source=WORK/'prepared-7/.lake/build/lib/lean/Dep.olean'
    source9=WORK/'prepared-9/.lake/build/lib/lean/Dep.olean'
    for mode in ('direct-readonly','symlink','hardlink','clone','full-copy'):
        root=WORK/mode
        producer=root/'producer'; alias=root/'alias'; consumer=root/'consumer'
        for d in (producer,alias,consumer): d.mkdir(parents=True)
        target=producer/'Dep.olean'; shutil.copy2(source,target)
        initial_source_hash=digest(target)
        if mode=='direct-readonly':
            os.chmod(target,0o444)
            lean_path=producer
            write_path=target
        else:
            write_path=alias/'Dep.olean'
            lean_path=alias
            if mode=='symlink': os.symlink(target,write_path)
            elif mode=='hardlink': os.link(target,write_path)
            elif mode=='clone':
                clone=run(['/bin/cp','-c',target,write_path])
                if clone['exit']!=0:
                    raw['modes'][mode]={'clone_command':clone,'status':'unavailable'}
                    continue
                os.chmod(write_path,0o644)
            else: shutil.copy2(target,write_path)
        (consumer/'Check.lean').write_text('import Dep\nexample : depValue = 7 := by decide\n#eval depValue\n')
        env={**ENV,'LEAN_PATH':str(lean_path)}
        before=run([LEAN,'Check.lean'],consumer,env)
        before_inventory={'producer':inventory(producer),'alias':inventory(alias)}
        write={'attempt':'overwrite first byte via alias r+b'}
        try:
            with open(write_path,'r+b') as f:
                original=f.read(1)
                f.seek(0)
                f.write(b'X' if original!=b'X' else b'Y')
                f.flush(); os.fsync(f.fileno())
            write['result']='succeeded'
        except OSError as e:
            write['result']=type(e).__name__; write['errno']=e.errno
        after=run([LEAN,'Check.lean'],consumer,env)
        raw['modes'][mode]={'status':'observed','initial_producer_sha256':initial_source_hash,'before':before,'before_inventory':before_inventory,'write':write,'after':after,'final_producer_sha256':digest(target),'final_alias_sha256':digest(write_path),'after_inventory':{'producer':inventory(producer),'alias':inventory(alias)}}
    # A Lean process imports the olean, signals readiness, sleeps, then reports the resident value.
    root=WORK/'open-reader'; root.mkdir()
    reader_file=root/'Read.lean'
    def reader_script(marker):
        reader_file.write_text('import Dep\n#eval (do\n  IO.FS.writeFile '+json.dumps(str(marker))+' "ready"\n  IO.sleep 1200\n  pure depValue : IO Nat)\n')
    live=root/'Dep.olean'; shutil.copy2(source,live)
    ren_marker=root/'rename-ready'; reader_script(ren_marker)
    env={**ENV,'LEAN_PATH':str(root)}
    def spawn_and_wait(marker):
        p=subprocess.Popen([str(LEAN),str(reader_file)],cwd=root,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        deadline=time.monotonic()+20
        while not marker.exists() and p.poll() is None and time.monotonic()<deadline: time.sleep(0.02)
        return p, marker.exists()
    p,ready=spawn_and_wait(ren_marker)
    staged=root/'Dep.olean.next'; shutil.copy2(source9,staged)
    old_hash=digest(live); next_hash=digest(staged)
    if ready: os.replace(staged,live)
    o,e=p.communicate(timeout=20)
    after_rename=run([LEAN,'Read.lean'],root,env)
    raw['open_reader']['rename']={'ready_before_replace':ready,'old_sha256':old_hash,'replacement_sha256':next_hash,'resident_exit':p.returncode,'resident_stdout':o,'resident_stderr':e,'fresh':after_rename,'final_sha256':digest(live)}
    unlink_marker=root/'unlink-ready'; reader_script(unlink_marker)
    p,ready=spawn_and_wait(unlink_marker)
    unlinked_hash=digest(live)
    if ready: live.unlink()
    o,e=p.communicate(timeout=20)
    after_unlink=run([LEAN,'Read.lean'],root,env)
    raw['open_reader']['unlink']={'ready_before_unlink':ready,'unlinked_sha256':unlinked_hash,'resident_exit':p.returncode,'resident_stdout':o,'resident_stderr':e,'fresh':after_unlink,'path_exists_after':live.exists()}
    # Explicit open file-descriptor control, separate from Lean's resident module state.
    fdroot=WORK/'open-fd'; fdroot.mkdir()
    fdpath=fdroot/'Dep.olean'; shutil.copy2(source,fdpath)
    with open(fdpath,'rb') as fd:
        replacement=fdroot/'next'; shutil.copy2(source9,replacement)
        os.replace(replacement,fdpath)
        raw['open_reader']['fd_rename']={'open_fd_sha256':hashlib.sha256(fd.read()).hexdigest(),'new_path_sha256':digest(fdpath)}
    with open(fdpath,'rb') as fd:
        fdpath.unlink()
        raw['open_reader']['fd_unlink']={'open_fd_sha256':hashlib.sha256(fd.read()).hexdigest(),'path_exists_after':fdpath.exists()}
    (HERE/'raw.json').write_text(json.dumps(clean_run(raw),indent=2)+'\n')
    print(json.dumps({'modes':{k:{'before_exit':v.get('before',{}).get('exit'),'write':v.get('write'),'producer_changed':v.get('initial_producer_sha256')!=v.get('final_producer_sha256'),'after_exit':v.get('after',{}).get('exit')} for k,v in raw['modes'].items()},'open_reader':{k:{'ready':v['ready_before_replace'] if k=='rename' else v['ready_before_unlink'],'resident_stdout':v['resident_stdout'],'fresh_exit':v['fresh']['exit'],'fresh_stdout':v['fresh']['stdout']} for k,v in raw['open_reader'].items() if k in ('rename','unlink')}},indent=2))

if __name__=='__main__': main()
