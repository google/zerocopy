#!/usr/bin/env python3
"""Lake controls over retained, real Aeneas base/reordered generated modules."""
import hashlib
import gzip
import json
import os
import re
import shutil
import subprocess
import tarfile
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
FIXTURE=ROOT/'fixture'
WORK=ROOT/'work'
LOGS=ROOT/'logs'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
LEAN_ROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LAKE=LEAN_ROOT/'bin/lake'
LEAN=LEAN_ROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
SOURCE_FILES=('Source/Types.lean','Source/Funs.lean','Source.lean')
PROOF=('import Source\n'
       'theorem inc0 : comparator_probe.inc 0#u32 = .ok 1#u32 := by rfl\n'
       'theorem twice0 : comparator_probe.twice 0#u32 = .ok 2#u32 := by rfl\n'
       'theorem choose0 : comparator_probe.choose 0#u32 = .ok 3#u32 := by rfl\n')
RESULT={'schema':1,'tools':{},'source_fixture':{},'builds':[]}

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def put(path,text):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
def input_files():
    return {variant:{name:{'sha256':sha(FIXTURE/variant/name),'bytes':(FIXTURE/variant/name).stat().st_size}
             for name in SOURCE_FILES} for variant in ('base','reorder')}
def setup(label,variant):
    root=WORK/label
    root.mkdir(parents=True)
    for name in SOURCE_FILES:
        dest=root/name;dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(FIXTURE/variant/name,dest)
    put(root/'Consumer.lean',PROOF)
    put(root/'lakefile.lean',f'import Lake\nopen Lake DSL\nrequire aeneas from "{BACKEND}"\n'
        'package m06_probe\nlean_lib Source\n@[default_target]\nlean_lib Consumer\n')
    manifest=json.loads((BACKEND/'lake-manifest.json').read_text())
    manifest['packages'].append({'type':'path','scope':'','name':'aeneas',
        'manifestFile':'lake-manifest.json','inherited':False,'dir':str(BACKEND),
        'configFile':'lakefile.lean'})
    manifest['name']='m06_probe'
    put(root/'lake-manifest.json',json.dumps(manifest,indent=2)+'\n')
    packages=root/'.lake/packages';packages.parent.mkdir(exist_ok=True)
    packages.symlink_to(BACKEND/'.lake/packages',target_is_directory=True)
    return root
def inventory(root):
    out={}
    for file in root.rglob('*'):
        if '.lake/packages' in str(file.relative_to(root)):continue
        if not file.is_file() or file.is_symlink():continue
        name=str(file.relative_to(root))
        st=file.stat()
        family=file.suffix or '<none>'
        out[name]={'family':family,'sha256':sha(file),'bytes':st.st_size,'mtime_ns':st.st_mtime_ns}
    return out
def build(label,root):
    start=time.monotonic()
    proc=subprocess.run([str(LAKE),'build','-v'],cwd=root,
        env=dict(os.environ,LEAN_NUM_THREADS='1',LAKE_NO_NET='1'),
        capture_output=True,text=True,timeout=90)
    LOGS.mkdir(exist_ok=True)
    stdout=proc.stdout.encode();stderr=proc.stderr.encode()
    (LOGS/(label+'.stdout.gz')).write_bytes(gzip.compress(stdout,mtime=0))
    (LOGS/(label+'.stderr.gz')).write_bytes(gzip.compress(stderr,mtime=0))
    assert proc.returncode==0,(label,proc.stdout[-1200:],proc.stderr[-1200:])
    local_lines=[line for line in proc.stdout.splitlines() if re.search(r'\b(?:Built|Replayed) (?:Source|Consumer)(?:\.|\b)',line)]
    record={'label':label,'root':root.name,'argv':['$LAKE','build','-v'],
            'returncode':proc.returncode,'elapsed_ms':round((time.monotonic()-start)*1000,2),
            'stdout_sha256':hashlib.sha256(stdout).hexdigest(),
            'stderr_sha256':hashlib.sha256(stderr).hexdigest(),
            'local_job_lines':local_lines,'files':inventory(root)}
    RESULT['builds'].append(record)
    return record

def main():
    assert not WORK.exists() and not LOGS.exists(),'copy package before regenerating retained evidence'
    assert shutil.disk_usage(ROOT).free>5*1024**3
    for path in (LEAN,LAKE,BACKEND/'lake-manifest.json',BACKEND/'.lake/build/lib/lean/Aeneas.olean'):
        assert path.is_file(),path
    RESULT['tools']={'lean_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
        'lake_version':subprocess.check_output([str(LAKE),'--version'],text=True).strip(),
        'lean_sha256':sha(LEAN),'lake_sha256':sha(LAKE),
        'aeneas_olean_sha256':sha(BACKEND/'.lake/build/lib/lean/Aeneas.olean'),
        'aeneas_manifest_sha256':sha(BACKEND/'lake-manifest.json')}
    RESULT['source_fixture']=input_files()
    assert RESULT['source_fixture']['base']['Source/Types.lean']['sha256']==RESULT['source_fixture']['reorder']['Source/Types.lean']['sha256']
    assert RESULT['source_fixture']['base']['Source.lean']['sha256']==RESULT['source_fixture']['reorder']['Source.lean']['sha256']
    assert RESULT['source_fixture']['base']['Source/Funs.lean']['sha256']!=RESULT['source_fixture']['reorder']['Source/Funs.lean']['sha256']
    WORK.mkdir()
    roots=[]
    try:
        fresh_base=setup('fresh-base','base');roots.append(fresh_base);build('fresh-base',fresh_base)
        fresh_reorder=setup('fresh-reorder','reorder');roots.append(fresh_reorder);build('fresh-reorder',fresh_reorder)
        same=setup('same','base');roots.append(same)
        build('same-base',same)
        build('same-noop',same)
        funs=same/'Source/Funs.lean'
        before=sha(funs);st=funs.stat()
        os.utime(funs,ns=(st.st_atime_ns,st.st_mtime_ns+2_000_000_000))
        assert sha(funs)==before
        build('same-mtime-only',same)
        for name in SOURCE_FILES:shutil.copyfile(FIXTURE/'reorder'/name,same/name)
        build('same-reorder',same)
        build('same-reorder-noop',same)
        for name in SOURCE_FILES:shutil.copyfile(FIXTURE/'base'/name,same/name)
        build('same-restore-base',same)
        build('same-restore-noop',same)
    finally:
        for root in roots:
            link=root/'.lake/packages'
            if link.is_symlink():link.unlink()
    raw=json.dumps(RESULT,indent=2,ensure_ascii=False)
    raw=raw.replace(str(WORK),'$WORK').replace(str(LAKE),'$LAKE')
    raw=raw.replace(str(BACKEND),'$AENEAS_BACKEND').replace(str(TOOLS),'$TOOLS')
    put(ROOT/'results.json',raw+'\n')
    with tarfile.open(ROOT/'work.tar.gz','w:gz') as archive:
        archive.add(WORK,arcname='work')
    shutil.rmtree(WORK)
    print(json.dumps({'builds':[{'label':b['label'],'local_lines':b['local_job_lines']}
        for b in RESULT['builds']]},indent=2))

if __name__=='__main__':main()
