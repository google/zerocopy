#!/usr/bin/env python3
"""Pinned offline Charon/Cargo warm-target and materialized-snapshot probe."""
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
FIX = HERE/'fixture'
ART = HERE/'artifacts'
RAW = HERE/'results.json'
VERSIONS = HERE/'versions'
TOOLS = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUST_BIN = TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CHARON = TOOLS/'bin/charon'
CARGO = RUST_BIN/'cargo'
RUSTC = RUST_BIN/'rustc'
SENTINEL = b'NOT-AN-LLBC-FOR-THIS-REQUEST\n'

SOURCE_A = '''#![allow(dead_code)]
include!(concat!(env!("OUT_DIR"), "/generated.rs"));
/// proof-id: A
pub fn step(x: u32) -> u32 { x.wrapping_add(1) }
pub fn use_step(x: u32) -> u32 { step(x).wrapping_add(dep_path::delta(x)) }
pub fn payload_len() -> usize { include_str!("payload.txt").len() }
pub fn generated_value() -> u32 { SNAPSHOT_VALUE }
'''
SOURCE_B = SOURCE_A.replace('proof-id: A', 'proof-id: B').replace('x.wrapping_add(1)', 'x.wrapping_add(2)')


def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def byte_sha(b): return hashlib.sha256(b).hexdigest()


def env_base():
    e = dict(os.environ)
    e.update({'RUSTUP_HOME': str(TOOLS/'rustup'), 'CARGO_HOME': str(TOOLS/'cargo'),
              'CHARON_TOOLCHAIN_IS_IN_PATH': '1', 'CARGO_BUILD_JOBS': '1',
              'CARGO_INCREMENTAL': '0', 'RAYON_NUM_THREADS': '1',
              'CARGO_NET_OFFLINE': 'true',
              'PATH': os.pathsep.join((str(RUST_BIN),str(TOOLS/'bin'),e.get('PATH',''))),
              'DYLD_LIBRARY_PATH': os.pathsep.join((str(RUST_BIN.parent/'lib'),
                   str(RUST_BIN.parent/'lib/rustlib/aarch64-apple-darwin/lib'),e.get('DYLD_LIBRARY_PATH','')))})
    return e


def fixture():
    if FIX.exists(): shutil.rmtree(FIX)
    origin = FIX/'origin'
    (origin/'app/src').mkdir(parents=True)
    (origin/'dep/src').mkdir(parents=True)
    (origin/'Cargo.toml').write_text('[workspace]\nmembers = ["app", "dep"]\nresolver = "2"\n')
    (origin/'app/Cargo.toml').write_text('[package]\nname = "warm_probe"\nversion = "0.1.0"\nedition = "2021"\nbuild = "build.rs"\n[dependencies]\ndep_path = { path = "../dep" }\n')
    (origin/'dep/Cargo.toml').write_text('[package]\nname = "dep_path"\nversion = "0.1.0"\nedition = "2021"\n')
    (origin/'dep/src/lib.rs').write_text('pub fn delta(x: u32) -> u32 { x.wrapping_add(3) }\n')
    (origin/'app/build.rs').write_text('''use std::{env, fs, path::PathBuf};
fn main() {
  println!("cargo:rerun-if-env-changed=BUILD_VALUE");
  let explicit: u32 = env::var("BUILD_VALUE").unwrap_or_else(|_| "7".into()).parse().unwrap();
  let location = env::var("CARGO_MANIFEST_DIR").unwrap();
  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
  fs::write(out.join("generated.rs"), format!("pub const SNAPSHOT_VALUE: u32 = {};\\n", explicit + location.len() as u32)).unwrap();
}
''')
    (origin/'app/src/lib.rs').write_text(SOURCE_A)
    (origin/'app/src/payload.txt').write_text('payload-A\n')
    lock = subprocess.run([str(CARGO),'generate-lockfile','--offline','--manifest-path',str(origin/'Cargo.toml')],
                          cwd=origin,env=env_base(),capture_output=True,text=True,timeout=30)
    assert lock.returncode == 0, lock.stderr
    shadow = FIX/'shadow-copy-longer'
    shutil.copytree(origin,shadow)
    (shadow/'app/src/lib.rs').write_text(SOURCE_B)
    (shadow/'app/src/payload.txt').write_text('payload-BBBBB\n')
    VERSIONS.mkdir(exist_ok=True)
    (VERSIONS/'source-A.rs').write_text(SOURCE_A)
    (VERSIONS/'source-B.rs').write_text(SOURCE_B)
    (VERSIONS/'payload-A.txt').write_text('payload-A\n')
    (VERSIONS/'payload-B.txt').write_text('payload-BBBBB\n')
    return origin, shadow


def source_hashes(root):
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*')) if p.is_file() and 'target' not in p.parts}


def normalize(s):
    return s.replace(str(HERE),'$REPORT').replace(str(TOOLS),'$TOOLS')


def invoke(root,target,out,label,source_expect,prewrite=None,build_value='7', timeout=50):
    if prewrite is not None:
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_bytes(prewrite)
    before = {'exists':out.exists(),'sha256':sha(out) if out.exists() else None,
              'bytes':out.stat().st_size if out.exists() else None}
    e=env_base(); e['CARGO_TARGET_DIR']=str(target); e['BUILD_VALUE']=build_value
    argv=[CHARON,'cargo','--preset','aeneas','--dest-file',out,'--','--manifest-path',root/'Cargo.toml',
          '--package','warm_probe','--lib','--offline','--locked']
    start=time.monotonic()
    p=subprocess.run([str(x) for x in argv],cwd=root,env=e,capture_output=True,text=True,timeout=timeout)
    after={'exists':out.exists(),'sha256':sha(out) if out.exists() else None,
           'bytes':out.stat().st_size if out.exists() else None}
    llbc=None
    if out.exists():
        try:
            data=json.loads(out.read_text())
            tr=data['translated']
            funs=[]
            for item in tr['fun_decls']:
                if item is None: continue
                meta=item['item_meta']
                name='::'.join(x['Ident'][0] if 'Ident' in x else '<impl>' for x in meta['name'])
                body=item.get('body')
                funs.append({'id':item['def_id'],'name':name,'local':meta.get('is_local'),
                             'body_sha256':byte_sha(json.dumps(body,sort_keys=True).encode()) if body is not None else None,
                             'attributes':meta.get('attr_info',{}).get('attributes',[]),
                             'span':meta.get('span')})
            llbc={'crate_name':tr['crate_name'],'charon_version':data['charon_version'],
                  'has_errors':data['has_errors'],'functions':funs,
                  'files':[{'name':x['name'],'contents_sha256':byte_sha(x['contents'].encode()) if x.get('contents') is not None else None}
                           for x in tr['files']]}
        except (UnicodeDecodeError,json.JSONDecodeError,KeyError,TypeError) as error:
            llbc={'parse_error':type(error).__name__+': '+str(error)}
    generated=[{'path':str(x.relative_to(target)),'sha256':sha(x),'bytes':x.stat().st_size,
                'text':x.read_text() if x.name=='generated.rs' else None}
               for x in sorted(target.rglob('generated.rs'))]
    target_artifacts={str(p.relative_to(target)):{'sha256':sha(p),'bytes':p.stat().st_size}
                      for p in sorted(target.rglob('*')) if p.is_file()} if target.exists() else {}
    size=sum(x['bytes'] for x in target_artifacts.values())
    rec={'label':label,'subject':str(root.relative_to(FIX)),'source_expectation':source_expect,
         'source_hashes':source_hashes(root),'build_value':build_value,
         'target':str(target.relative_to(FIX)),'target_bytes':size,
         'output':str(out.relative_to(ART)),'pre_output':before,'post_output':after,
         'wall_seconds':round(time.monotonic()-start,5),'exit':p.returncode,
         'stdout':normalize(p.stdout),'stderr':normalize(p.stderr),
         'generated_files':generated,'target_artifacts':target_artifacts,'llbc':llbc,
         'command':[normalize(str(x)) for x in argv]}
    return rec


def local(rec,name):
    return next(x for x in rec['llbc']['functions'] if x['local'] and x['name'].endswith('::'+name))


def main():
    if shutil.disk_usage(HERE).free < 20*(1<<30): raise RuntimeError('disk guard: need 20 GiB free')
    if ART.exists(): shutil.rmtree(ART)
    ART.mkdir(parents=True)
    origin,shadow=fixture()
    targets=FIX/'targets'; targets.mkdir()
    t_shared=targets/'shared'; t_cold=targets/'separate-cold'; t_shadow=targets/'shadow'; t_b_disk=targets/'original-B'; t_cargo=targets/'cargo-prewarmed'
    records=[]
    def run(root,target,label,source,prewrite=None,out='current.llbc',build_value='7'):
        r=invoke(root,target,ART/out,label,source,prewrite,build_value)
        if r['exit']==0 and r['llbc'] and 'parse_error' not in r['llbc']:
            (ART/'cases').mkdir(exist_ok=True)
            shutil.copyfile(ART/out,ART/'cases'/f'{label}.llbc')
        records.append(r)
        RAW.write_text(json.dumps({'partial_records':records},indent=2,sort_keys=True)+'\n')
        return r
    cold=run(origin,t_shared,'origin-A-cold','A')
    warm_sentinel=run(origin,t_shared,'origin-A-warm-sentinel','A',SENTINEL)
    warm_absent=run(origin,t_shared,'origin-A-warm-absent','A',out='absent.llbc')
    separate=run(origin,t_cold,'origin-A-separate-cold','A',out='separate.llbc')
    separate_warm=run(origin,t_cold,'origin-A-separate-warm','A',SENTINEL,out='separate-warm.llbc')
    cargo_warm=[]
    for n in (1,2):
        e=env_base();e['CARGO_TARGET_DIR']=str(t_cargo);e['BUILD_VALUE']='7'
        argv=[CARGO,'build','-v','--manifest-path',origin/'Cargo.toml','--package','warm_probe','--lib','--offline','--locked']
        t=time.monotonic();p=subprocess.run([str(x) for x in argv],cwd=origin,env=e,text=True,capture_output=True,timeout=50)
        cargo_warm.append({'label':f'plain-cargo-{n}','exit':p.returncode,'seconds':round(time.monotonic()-t,5),
                           'command':[normalize(str(x)) for x in argv], 'stdout':normalize(p.stdout),'stderr':normalize(p.stderr)})
        assert p.returncode==0
    prewarmed=run(origin,t_cargo,'origin-A-after-plain-cargo-warm','A',out='prewarmed.llbc')
    shadow_b=run(shadow,t_shadow,'shadow-B-cold','B',out='shadow-B.llbc')
    shadow_shared=run(shadow,t_shared,'shadow-B-shared-target','B',out='shadow-shared.llbc')
    assert (origin/'app/src/lib.rs').read_text()==SOURCE_A
    assert (origin/'app/src/payload.txt').read_text()=='payload-A\n'
    # Compare the same intended B bytes at the original path with a distinct cold target.
    (origin/'app/src/lib.rs').write_text(SOURCE_B)
    (origin/'app/src/payload.txt').write_text('payload-BBBBB\n')
    try:
        original_b=run(origin,t_b_disk,'origin-B-cold','B',out='origin-B.llbc')
    finally:
        (origin/'app/src/lib.rs').write_text(SOURCE_A)
        (origin/'app/src/payload.txt').write_text('payload-A\n')
    restored=run(origin,t_shared,'origin-A-restored-warm','A',SENTINEL,out='restored.llbc')
    old_success=(ART/'current.llbc').read_bytes() if (ART/'current.llbc').exists() else b''
    (origin/'app/src/lib.rs').write_text('pub fn broken(\n')
    try:
        bad=run(origin,t_shared,'origin-malformed-warm','invalid',old_success,out='failed-old.llbc')
    finally:
        (origin/'app/src/lib.rs').write_text(SOURCE_A)
    assert cold['exit']==separate['exit']==separate_warm['exit']==prewarmed['exit']==shadow_b['exit']==shadow_shared['exit']==original_b['exit']==restored['exit']==0
    for r in records:
        if r['exit']==0:
            assert r['llbc']['has_errors'] is False
            assert sha(ART/'cases'/f"{r['label']}.llbc")==r['post_output']['sha256']
    assert cold['llbc']['crate_name']==shadow_b['llbc']['crate_name']==original_b['llbc']['crate_name']=='warm_probe'
    assert cold['source_hashes']==restored['source_hashes']
    assert shadow_b['source_hashes']==original_b['source_hashes']
    assert shadow_b['source_hashes']['app/src/lib.rs'] != cold['source_hashes']['app/src/lib.rs']
    assert local(shadow_b,'step')['body_sha256'] != local(cold,'step')['body_sha256']
    assert local(shadow_b,'SNAPSHOT_VALUE')['body_sha256'] != local(original_b,'SNAPSHOT_VALUE')['body_sha256']
    assert bad['exit']!=0 and bad['post_output']['sha256']==bad['pre_output']['sha256']
    assert (origin/'app/src/lib.rs').read_text()==SOURCE_A
    def body_map(r):
        return {x['name']:x['body_sha256'] for x in r['llbc']['functions'] if x['local']}
    assert body_map(cold)==body_map(warm_sentinel)==body_map(warm_absent)==body_map(separate)==body_map(separate_warm)==body_map(prewarmed)==body_map(restored)
    assert local(shadow_b,'step')['body_sha256']==local(shadow_shared,'step')['body_sha256']
    assert local(shadow_b,'SNAPSHOT_VALUE')['body_sha256']!=local(shadow_shared,'SNAPSHOT_VALUE')['body_sha256']
    assert shadow_shared['generated_files'][0]['sha256']==cold['generated_files'][0]['sha256']
    # A warm request may or may not invoke the producer at this pin; assert only recorded facts.
    result={'environment':{'platform':platform.platform(),'python':sys.version,
             'charon_sha256':sha(CHARON),'cargo_sha256':sha(CARGO),'rustc_sha256':sha(RUSTC),
             'cargo_version':subprocess.check_output([str(CARGO),'--version'],env=env_base(),text=True).strip(),
             'rustc_version':subprocess.check_output([str(RUSTC),'--version'],env=env_base(),text=True).strip()},
            'plain_cargo_warmups':cargo_warm,
            'sentinel_sha256':byte_sha(SENTINEL),'records':records,
            'controls':{'warm_sentinel_overwritten':warm_sentinel['post_output']['sha256']!=byte_sha(SENTINEL),
                        'warm_absent_created':warm_absent['post_output']['exists'],
                        'separate_target_created':separate['post_output']['exists'],
                        'separate_warm_sentinel_overwritten':separate_warm['post_output']['sha256']!=byte_sha(SENTINEL),
                        'plain_cargo_second_fresh': 'Fresh warm_probe' in cargo_warm[1]['stderr'],
                        'charon_after_plain_cargo_created_llbc':prewarmed['post_output']['exists'],
                        'shadow_shared_step_matches_private':local(shadow_b,'step')['body_sha256']==local(shadow_shared,'step')['body_sha256'],
                        'shadow_shared_generated_constant_stale':local(shadow_b,'SNAPSHOT_VALUE')['body_sha256']!=local(shadow_shared,'SNAPSHOT_VALUE')['body_sha256'],
                        'shadow_shared_generated_artifact_matches_origin':shadow_shared['generated_files'][0]['sha256']==cold['generated_files'][0]['sha256'],
                        'shadow_did_not_mutate_origin':cold['source_hashes']==restored['source_hashes'],
                        'shadow_and_original_B_same_source_tree':shadow_b['source_hashes']==original_b['source_hashes'],
                        'shadow_path_changes_generated_value':local(shadow_b,'SNAPSHOT_VALUE')['body_sha256']!=local(original_b,'SNAPSHOT_VALUE')['body_sha256'],
                        'A_body_projection_equal_across_target_modes':body_map(cold)==body_map(warm_sentinel)==body_map(warm_absent)==body_map(separate)==body_map(separate_warm)==body_map(prewarmed)==body_map(restored),
                        'failure_retained_old_llbc':bad['post_output']['sha256']==bad['pre_output']['sha256']}}
    RAW.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'exits':{x['label']:x['exit'] for x in records},'controls':result['controls'],
                      'target_bytes':{x['label']:x['target_bytes'] for x in records}},sort_keys=True))
    shutil.rmtree(targets)

if __name__=='__main__': main()
