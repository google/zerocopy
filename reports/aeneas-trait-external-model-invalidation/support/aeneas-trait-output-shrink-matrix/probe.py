#!/usr/bin/env python3
"""One-shot pinned Charon/Aeneas trait/external/shrink/reorder/error matrix."""
import hashlib, json, os, re, shutil, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent; WORK=HERE/'work'; OUT=HERE/'raw-results.json'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon'; AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'; LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry','-print-unknown-externals']
HEAD='#![allow(dead_code)]\n'
TRAIT='pub trait Step { fn step(self) -> u32; }\nimpl Step for u32 { fn step(self) -> u32 { self.wrapping_add(1) } }\n'
USE='pub fn use_step(x: u32) -> u32 { x.step() }\n'
OLD='pub fn old(x: u32) -> u32 { x.wrapping_add(2) }\n'
EXT='unsafe extern "C" { fn external_double(x: u32) -> u32; }\npub fn external_call(x: u32) -> u32 { unsafe { external_double(x) } }\n'
BAD='pub fn bad(p: *mut u32) -> u32 { unsafe { *p } }\n'
SOURCES={'base':HEAD+TRAIT+USE+OLD+EXT,
         'reorder':HEAD+OLD+TRAIT+EXT+USE,
         'shrink':HEAD+TRAIT+USE,
         'error':HEAD+TRAIT+USE+BAD}
EVENTS=[];START=time.monotonic()

def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),t_ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def run(label,argv,cwd,env=None,timeout=60):
    command=[str(x) for x in argv];t=time.monotonic()
    try:
        p=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True,timeout=timeout)
        r=dict(label=label,argv=command,rc=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_ms=round((time.monotonic()-t)*1000,1))
    except subprocess.TimeoutExpired as e:
        r=dict(label=label,argv=command,rc='timeout',stdout=str(e.stdout),stderr=str(e.stderr),elapsed_ms=round((time.monotonic()-t)*1000,1))
    log('command',**r);return r
def inventory(root):
    return {p.relative_to(root).as_posix():dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(root.rglob('*')) if p.is_file()}
def lean_env(compiled):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join(map(str,[compiled,*(p for p in libs if p.is_dir())]))
    env['LEAN_NUM_THREADS']='1'
    return env
def decl_manifest(llbc,generated):
    data=json.loads(llbc.read_text());charon=[];lean=[]
    for kind in ('type_decls','trait_decls','trait_impls','fun_decls'):
        for item in data['translated'][kind]:
            if not item:continue
            m=item['item_meta'];charon.append(dict(kind=kind,def_id=item['def_id'],name=m['name'],source_span=m.get('span'),is_local=m.get('is_local')))
    for p in sorted(generated.glob('*.lean')):
        raw=p.read_bytes();offset=0;source_comment=None
        for ln,line in enumerate(raw.splitlines(keepends=True),1):
            text=line.decode('utf-8',errors='replace')
            if 'Source:' in text:source_comment=text.strip()
            m=re.match(r'^\s*(?:def|structure|axiom|theorem|inductive|abbrev|class|instance)\s+([^\s(:]+)',text)
            if m:
                lean.append(dict(file=p.name,line=ln,byte_range=[offset,offset+len(line)],name=m.group(1),head=text.strip(),nearest_source_comment=source_comment,authenticated_charon_link=None))
            offset+=len(line)
    return dict(charon_version=data['charon_version'],crate=data['translated']['crate_name'],has_errors=data['has_errors'],
                charon_declarations=charon,lean_declarations=lean,proven_rust_to_lean_mapping=None,editable_proof_ranges=None)
def copy_generated(label,generated):
    dest=HERE/'outputs'/label
    shutil.copytree(generated,dest)
    return dest
def compile_fresh(label,generated,external_mode=None):
    root=WORK/f'compiled-{label}';root.mkdir();mod=root/'TraitProbe';mod.mkdir()
    for p in generated.glob('*.lean'):
        if p.name=='TraitProbe.lean':shutil.copyfile(p,root/p.name)
        elif p.name=='FunsExternal_Template.lean':
            if external_mode:
                txt=p.read_text()
                if external_mode=='concrete':
                    txt=txt.replace('axiom external_double : Std.U32 → Result Std.U32',
                        'def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)')
                (mod/'FunsExternal.lean').write_text(txt)
        else:shutil.copyfile(p,mod/p.name)
    chain=['TraitProbe/Types']
    if external_mode:chain.append('TraitProbe/FunsExternal')
    chain += ['TraitProbe/Funs','TraitProbe']
    outcomes=[];env=lean_env(root)
    for module in chain:
        x=run(f'{label}:compile:{module}',[LEAN,'-o',f'{module}.olean',f'{module}.lean'],root,env)
        outcomes.append(x)
        if x['rc']:break
    return root,outcomes
def consume(label,root,text):
    p=root/'Consumer.lean';p.write_text(text)
    return run(f'{label}:consumer',[LEAN,p.name],root,lean_env(root))

def main():
    assert all(p.is_file() for p in [CHARON,AENEAS,LEAN])
    assert (BACKEND/'.lake/build/lib/lean/Aeneas.olean').is_file()
    assert shutil.disk_usage(HERE).free>2*1024**3
    for name in ['work','inputs','outputs']:
        p=HERE/name
        if p.exists():shutil.rmtree(p)
        p.mkdir()
    rustenv=dict(os.environ,RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),CHARON_TOOLCHAIN_IS_IN_PATH='1')
    rustenv['PATH']=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),rustenv.get('PATH','')])
    log('subjects',charon_sha256=sha(CHARON),aeneas_sha256=sha(AENEAS),lean_sha256=sha(LEAN),
        aeneas_runtime_olean_sha256=sha(BACKEND/'.lake/build/lib/lean/Aeneas.olean'),
        lean_version=run('lean-version',[LEAN,'--version'],WORK)['stdout'],
        aeneas_version=run('aeneas-version',[AENEAS,'-version'],WORK)['stdout'])
    manifests={};inventories={};translation={}
    source_path=WORK/'trait_probe.rs';llbc=WORK/'trait_probe.llbc';generated=WORK/'generated'
    for label,source in SOURCES.items():
        source_path.write_text(source)
        if llbc.exists():llbc.unlink()
        if generated.exists():shutil.rmtree(generated)
        generated.mkdir()
        c=run(f'{label}:charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,'--',source_path,
                                 '--crate-type','lib','--crate-name','trait_probe','--edition','2021'],WORK,rustenv)
        assert c['rc']==0 and llbc.exists(),c
        a=run(f'{label}:aeneas',[AENEAS,*FLAGS,'-dest',generated,llbc],WORK)
        expected=1 if label=='error' else 0
        assert (a['rc']!=0 if expected else a['rc']==0),a
        dest=HERE/'inputs'/label;dest.mkdir();shutil.copyfile(source_path,dest/source_path.name);shutil.copyfile(llbc,dest/llbc.name)
        copy_generated(label,generated)
        manifests[label]=decl_manifest(llbc,generated)
        inventories[label]=dict(source_sha256=sha(source_path),llbc_sha256=sha(llbc),files=inventory(generated))
        translation[label]=dict(charon_rc=c['rc'],aeneas_rc=a['rc'])
    assert 'FunsExternal_Template.lean' in inventories['base']['files']
    assert 'FunsExternal_Template.lean' not in inventories['shrink']['files']
    assert len(manifests['shrink']['lean_declarations'])<len(manifests['base']['lean_declarations'])
    assert inventories['base']['files']['Funs.lean']['sha256']!=inventories['reorder']['files']['Funs.lean']['sha256']
    consumers={}
    for label in ['base','reorder','shrink']:
        root,chain=compile_fresh(label,HERE/'outputs'/label,'axiom' if label!='shrink' else None)
        assert all(x['rc']==0 for x in chain),chain
        text='import TraitProbe\n#check trait_probe.use_step\nexample : trait_probe.use_step 1#u32 = .ok 2#u32 := by rfl\n'
        if label!='shrink':text+='#check trait_probe.old\n#check trait_probe.external_call\n'
        x=consume(label,root,text);consumers[label]=dict(compile=[z['rc'] for z in chain],check_rc=x['rc'],check_stdout=x['stdout'])
        assert x['rc']==0,x
        if label=='shrink':
            miss=consume('shrink-removed',root,'import TraitProbe\n#check trait_probe.old\n#check trait_probe.external_call\n')
            consumers['shrink-removed']=dict(rc=miss['rc'],stdout=miss['stdout'])
            assert miss['rc']!=0 and 'unknown identifier' in miss['stdout'].lower(),miss
    # Fresh concrete external model checks the dependency rather than relying on an axiom.
    root,chain=compile_fresh('base-concrete',HERE/'outputs'/'base','concrete')
    assert all(x['rc']==0 for x in chain),chain
    x=consume('base-concrete',root,'import TraitProbe\n#print axioms trait_probe.external_call\nexample : trait_probe.external_call 1#u32 = .ok 2#u32 := by rfl\n')
    consumers['base-concrete']=dict(rc=x['rc'],stdout=x['stdout'])
    assert x['rc']==0 and 'does not depend on any axioms' in x['stdout'],x
    # A failed translation can still leave Lean-compilable partial output.
    root,chain=compile_fresh('error',HERE/'outputs'/'error')
    assert all(x['rc']==0 for x in chain),chain
    x=consume('error',root,'import TraitProbe\n#check trait_probe.bad\n#print axioms trait_probe.bad\n')
    consumers['error']=dict(compile=[z['rc'] for z in chain],rc=x['rc'],stdout=x['stdout'])
    assert x['rc']==0 and 'sorryAx' in x['stdout'],x
    # Reuse one output directory: successful shrink does not remove old template.
    reused=WORK/'reused';shutil.copytree(HERE/'outputs'/'base',reused)
    shutil.copyfile(HERE/'inputs'/'shrink'/'trait_probe.llbc',llbc)
    x=run('shrink:reused-destination',[AENEAS,*FLAGS,'-dest',reused,llbc],WORK)
    assert x['rc']==0,x
    reused_inventory=inventory(reused)
    assert 'FunsExternal_Template.lean' in reused_inventory and 'FunsExternal_Template.lean' not in inventories['shrink']['files']
    # A failed request may emit partial output; keep its private inventory separate.
    assert translation['error']['aeneas_rc']!=0
    results=dict(subjects=dict(charon_sha256=sha(CHARON),aeneas_sha256=sha(AENEAS),lean_sha256=sha(LEAN)),
                 translations=translation,inventories=inventories,manifests=manifests,consumers=consumers,
                 reused_after_shrink=reused_inventory,elapsed_ms=round((time.monotonic()-START)*1000,1),events=EVENTS,
                 limits=['one-shot CLI only','lexical Lean source-comment linkage, no authenticated item mapping','no same-process OCaml API'])
    OUT.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(dict(status='passed',cases=list(SOURCES),commands=sum(e['kind']=='command' for e in EVENTS),elapsed_ms=results['elapsed_ms'])))

try:main()
except Exception as exc:
    log('fatal',error=repr(exc));OUT.write_text(json.dumps(dict(events=EVENTS,fatal=repr(exc)),indent=2)+'\n');raise
