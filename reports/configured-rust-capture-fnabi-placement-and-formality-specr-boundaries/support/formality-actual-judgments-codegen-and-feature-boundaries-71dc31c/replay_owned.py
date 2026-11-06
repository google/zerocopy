"""Rebuild/replay the20 owned cases in a fresh directory, with caller-supplied pinned tools/cache.

No installs or network access. This does not replay the budget-stopped cargo suite.
"""
import argparse, hashlib, json, pathlib, shutil, subprocess, tarfile

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--toolchain',type=pathlib.Path,required=True)
    ap.add_argument('--cargo-home-source',type=pathlib.Path,required=True)
    ap.add_argument('--workdir',type=pathlib.Path,required=True)
    ap.add_argument('--prepare-only',action='store_true',help='verify/copy inputs without compilation')
    a=ap.parse_args();support=pathlib.Path(__file__).resolve().parent
    out=a.workdir.absolute();tool=a.toolchain.resolve(strict=True)
    if out.exists() or out.resolve()!=out or out.parent.resolve()!=out.parent:
        raise ValueError('fresh physical workdir required')
    identities=json.loads((support/'execution-tool-identities.json').read_text())
    for row in identities['rows']:
        if sha(tool/'bin'/row['name'])!=row['sha256']:
            raise ValueError('selected exact tool identity differs: '+row['name'])
    driver=next(x for x in json.loads((support/'compiler-shared-runtime-identities.json').read_text())
                if x['name'].startswith('librustc_driver'))
    if sha(tool/'lib'/driver['name'])!=driver['sha256']:
        raise ValueError('compiler driver differs')
    acquisition=json.loads((support/'source-acquisition.json').read_text())
    archive=support/'source.tar.gz'
    if sha(archive)!=acquisition['archive_sha256']:
        raise ValueError('source archive differs')
    out.mkdir();source=out/'source';source.mkdir()
    expected={x['path']:x for x in acquisition['blobs']}
    seen=set()
    with tarfile.open(archive,'r:gz') as tf:
        for member in tf.getmembers():
            path=pathlib.Path(member.name)
            if path.is_absolute() or '..' in path.parts or not (member.isdir() or member.isfile()):
                raise ValueError('unsafe source archive entry')
            if member.isdir():continue
            name='/'.join(path.parts[1:]);data=tf.extractfile(member).read()
            if name not in expected or hashlib.sha256(data).hexdigest()!=expected[name]['sha256']:
                raise ValueError('source blob differs: '+name)
            dest=source/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);seen.add(name)
    if seen!=set(expected):raise ValueError('incomplete source archive')
    for name in ['owned_e07.rs','run_cases.py','run_phase.py','case-plan.json']:
        shutil.copyfile(support/name,out/name)
    shutil.copytree(support/'fixtures',out/'fixtures')
    shutil.copyfile(support/'owned_e07.rs',source/'examples/owned_e07.rs')
    cache=a.cargo_home_source.resolve(strict=True)/'registry'
    required=json.loads((support/'fetched-dependency-checks.json').read_text())['records']
    target=out/'cargo-home/registry/cache/index.crates.io-1949cf8c6b5b557f';target.mkdir(parents=True)
    for row in required:
        name=row['name']+'-'+row['version']+'.crate'
        matches=list((cache/'cache').glob('*/'+name))
        if not matches or sha(matches[0])!=row['checksum']:
            raise ValueError('exact cached dependency unavailable: '+name)
        shutil.copyfile(matches[0],target/name)
    index_matches=[p for p in (cache/'index').glob('*') if (p/'config.json').is_file()]
    if len(index_matches)!=1:raise ValueError('explicit source cache needs one sparse registry index')
    shutil.copytree(index_matches[0],out/'cargo-home/registry/index/index.crates.io-1949cf8c6b5b557f')
    if a.prepare_only:
        print(json.dumps({'prepared':True,'source_blobs':len(seen),'cached_locked_crates':len(required),
                          'build_performed':False},indent=2))
        return
    cmd=['python3','-B','run_phase.py','--toolchain',str(tool),'--phase','observer-build',
         '--','build','--locked','--offline','-j1','-p','a-mir-formality','--example','owned_e07']
    r=subprocess.run(cmd,cwd=out)
    if r.returncode:raise SystemExit('build failed or owned budget boundary reached; inspect retained logs')
    r=subprocess.run(['python3','-B','run_cases.py','--binary','target/debug/examples/owned_e07',
                      '--output','observed-cases'],cwd=out)
    raise SystemExit(r.returncode)

if __name__=='__main__':main()
