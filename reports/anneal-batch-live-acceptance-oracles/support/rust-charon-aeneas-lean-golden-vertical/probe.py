#!/usr/bin/env python3
"""Pinned Cargo/Charon/Aeneas/Lean vertical, with exact negative controls.

Rerunning replaces only this package's support/work and support/results.json.
No network resolution, installation, or Anneal implementation is involved.
"""
from __future__ import annotations
import hashlib,json,os,re,shutil,subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE/'work'
T=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=T/'bin/charon'; AENEAS=T/'bin/aeneas'
RUSTBIN=T/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CARGO=RUSTBIN/'cargo'; LEANROOT=T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN=LEANROOT/'bin/lean'; BACKEND=T/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
SOURCE='''#![allow(dead_code)]
/// manually chosen obligation: obl_inc
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
/// manually chosen obligation: obl_twice
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
/// manually chosen obligation: obl_choose
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
'''
MUTATED=SOURCE.replace('wrapping_add(1)','wrapping_add(2)')
MANIFEST='[package]\nname = "golden_vertical"\nversion = "0.1.0"\nedition = "2021"\n'
REQUIRED=['obl_inc','obl_twice','obl_choose']
RESULT={'commands':[],'cases':{},'controls':{},'subjects':{},'limits':[]}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,s):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def call(label,args,cwd,env=None,timeout=180):
    p=subprocess.run(list(map(str,args)),cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
    d={'label':label,'argv':list(map(str,args)),'cwd':str(cwd),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    RESULT['commands'].append(d);return d
def inv(root):
    return {p.relative_to(root).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(root.rglob('*')) if p.is_file()}
def lean_env(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_PATH']=os.pathsep.join(map(str,[comp,*(p for p in libs if p.is_dir())]));return e
def lean(label,comp,src,out=None):
    args=[LEAN]
    if out:args+=['-o',out]
    args += [src]
    return call(label,args,comp,lean_env(comp))
def rust_env():
    e=dict(os.environ);e.update({'RUSTUP_HOME':str(T/'rustup'),'CARGO_HOME':str(T/'cargo'),
       'CHARON_TOOLCHAIN_IS_IN_PATH':'1','CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0',
       'CARGO_NET_OFFLINE':'true','PATH':os.pathsep.join([str(RUSTBIN),str(T/'bin'),e.get('PATH','')])});return e

def build(label,source,target):
    case=WORK/label;case.mkdir()
    target_was_prepared=target.exists()
    llbc=case/'current.llbc';gen=case/'generated';gen.mkdir()
    crate=WORK/'crate';put(crate/'src/lib.rs',source)
    cmd=[CHARON,'cargo','--preset','aeneas','--dest-file',llbc,'--','--manifest-path',crate/'Cargo.toml',
         '--package','golden_vertical','--lib','--offline','--locked']
    e=rust_env();e['CARGO_TARGET_DIR']=str(target)
    r=call(label+':charon-cargo',cmd,case,e,300);assert r['exit']==0,r
    r=call(label+':aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential',
          '-split-files','-gen-lib-entry','-dest',gen,llbc],case);assert r['exit']==0,r
    capture=case/'inputs';capture.mkdir();shutil.copyfile(crate/'src/lib.rs',capture/'lib.rs')
    shutil.copyfile(crate/'Cargo.toml',capture/'Cargo.toml');shutil.copyfile(crate/'Cargo.lock',capture/'Cargo.lock')
    comp=case/'consumer';(comp/'Current').mkdir(parents=True)
    for f in ['Types.lean','Funs.lean']:shutil.copyfile(gen/f,comp/'Current'/f)
    shutil.copyfile(gen/'Current.lean',comp/'Current.lean')
    for m in ['Current/Types','Current/Funs','Current']:
        r=lean(label+':compile:'+m,comp,m+'.lean',m+'.olean');assert r['exit']==0,r
    expected=(1,2,3) if source==SOURCE else (2,4,5)
    proof='import Current\n' + ''.join(
        f'theorem {n} : golden_vertical.{fn} 0#u32 = .ok {v}#u32 := by rfl\n#print axioms {n}\n'
        for n,fn,v in zip(REQUIRED,['inc','twice','choose'],expected))
    put(comp/'Proof.lean',proof)
    r=lean(label+':proof',comp,'Proof.lean');assert r['exit']==0 and 'sorryAx' not in r['stdout'],r
    if label in ('base-cold','mutated-clean'):
        rust_test=f'''use golden_vertical::{{inc, twice, choose}};
#[test] fn selected_values() {{
    assert_eq!(inc(0), {expected[0]});
    assert_eq!(twice(0), {expected[1]});
    assert_eq!(choose(0), {expected[2]});
}}
'''
        put(crate/'tests/behavior.rs',rust_test)
        shutil.copyfile(crate/'tests/behavior.rs',capture/'behavior.rs')
        test=call(label+':cargo-test',[CARGO,'test','--offline','--locked','--test','behavior'],crate,e,300)
        assert test['exit']==0 and '1 passed' in test['stdout'],test
    RESULT['cases'][label]={'inputs':inv(capture),'llbc':{'sha256':sha(llbc),'bytes':llbc.stat().st_size},
       'generated':inv(gen),'consumer':inv(comp),'expected_values':expected,'proof_stdout':r['stdout'],
       'target_was_prepared':target_was_prepared}
    return case

def manifest(case):
    source=(case/'inputs/lib.rs').read_text().splitlines()
    obj=json.loads((case/'current.llbc').read_text())
    funs=(case/'generated/Funs.lean').read_text().splitlines()
    rows=[]
    for name,ob in zip(['inc','twice','choose'],REQUIRED):
        sl=next(i for i,line in enumerate(source,1) if line.startswith('pub fn '+name+'('))
        decl=next(d for d in obj['translated']['fun_decls'] if d and d['item_meta']['name'][-1].get('Ident',[None])[0]==name)
        fl=next(i for i,line in enumerate(funs,1) if re.match(r'^def '+name+r'\b',line))
        rows.append({'rust_function':name,'manual_obligation':ob,'rust_line':sl,
            'rust_text':source[sl-1],'charon_def_id':decl['def_id'],
            'charon_span':decl['item_meta']['span'],'aeneas_file':'Current/Funs.lean',
            'aeneas_def_line':fl,'aeneas_source_comment':next((funs[j].strip() for j in range(fl-2,-1,-1) if 'Source:' in funs[j]),None)})
    return {'basis':'manually checked name, Charon span, generated comment and declaration line; no authenticated producer map',
            'source_sha256':sha(case/'inputs/lib.rs'),'llbc_sha256':sha(case/'current.llbc'),
            'funs_sha256':sha(case/'generated/Funs.lean'),'rows':rows,
            'proven_def_id_to_lean_range':None,'anneal_obligation_mapping':None}

def check_obligations(text):
    found=re.findall(r'^theorem\s+(obl_\w+)\b',text,re.M)
    return {'declared':found,'required':REQUIRED,'accepted':found==REQUIRED}

def normalized_llbc(path):
    obj=json.loads(Path(path).read_text())
    obj['translated']['options']['dest_file']=None
    obj['translated']['short_names'].sort(key=lambda x:json.dumps(x,sort_keys=True))
    return obj

def main():
    assert shutil.disk_usage(HERE).free>10*1024**3
    for p in [CHARON,AENEAS,CARGO,LEAN,BACKEND/'.lake/build/lib/lean/Aeneas.olean']:assert p.is_file(),p
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();crate=WORK/'crate';put(crate/'Cargo.toml',MANIFEST);put(crate/'src/lib.rs',SOURCE)
    e=rust_env();r=call('cargo-lock',[CARGO,'generate-lockfile','--offline'],crate,e);assert r['exit']==0,r
    target=WORK/'target-prepared'
    base=build('base-cold',SOURCE,target)
    warm=build('base-prepared',SOURCE,target)
    clean=build('base-clean',SOURCE,WORK/'target-clean')
    mutated=build('mutated-clean',MUTATED,WORK/'target-mutated')
    # Fresh batch checker against the wrong claim from the old generation.
    comp=mutated/'consumer'
    put(comp/'WrongClaim.lean','import Current\ntheorem wrong_inc : golden_vertical.inc 0#u32 = .ok 1#u32 := by rfl\n')
    r=lean('control:wrong-claim',comp,'WrongClaim.lean');assert r['exit']!=0 and 'rfl' in r['stdout'],r
    RESULT['controls']['wrong_claim']={'exit':r['exit'],'detected':True,'file_sha256':sha(comp/'WrongClaim.lean')}
    # A missing theorem can batch-check; a separate explicit completeness gate catches it.
    missing='import Current\ntheorem obl_inc : golden_vertical.inc 0#u32 = .ok 2#u32 := by rfl\ntheorem obl_twice : golden_vertical.twice 0#u32 = .ok 4#u32 := by rfl\n'
    put(comp/'Missing.lean',missing);r=lean('control:missing-obligation',comp,'Missing.lean')
    assert r['exit']==0 and not check_obligations(missing)['accepted'],r
    RESULT['controls']['missing_obligation']={'batch_exit':r['exit'],**check_obligations(missing),'file_sha256':sha(comp/'Missing.lean')}
    # A sorry is admitted by Lean but taints the theorem's axiom inventory.
    admitted='import Current\ntheorem obl_inc : golden_vertical.inc 0#u32 = .ok 99#u32 := by sorry\n#print axioms obl_inc\n'
    put(comp/'Admitted.lean',admitted);r=lean('control:admitted-claim',comp,'Admitted.lean')
    assert r['exit']==0 and 'sorryAx' in r['stdout'],r
    RESULT['controls']['admitted_claim']={'batch_exit':r['exit'],'sorryAx_detected':True,'file_sha256':sha(comp/'Admitted.lean')}
    # Import from the stale generation still compiles its old proof; a source/LLBC identity gate must catch it.
    old=base/'consumer';r=lean('control:stale-old-import',old,'Proof.lean');assert r['exit']==0,r
    stale=(sha(mutated/'inputs/lib.rs')!=sha(base/'inputs/lib.rs'))
    RESULT['controls']['stale_import']={'batch_exit':r['exit'],'current_source_sha256':sha(mutated/'inputs/lib.rs'),
        'imported_generation_source_sha256':sha(base/'inputs/lib.rs'),'identity_gate_rejects':stale}
    assert stale
    # Import tamper: copy B's generated function module into A's private consumer; recompile fresh.
    tamper=WORK/'tampered-consumer';shutil.copytree(base/'consumer',tamper)
    shutil.copyfile(mutated/'generated/Funs.lean',tamper/'Current/Funs.lean')
    for m in ['Current/Funs','Current']:
        r=lean('control:tampered-import-compile:'+m,tamper,m+'.lean',m+'.olean');assert r['exit']==0,r
    r=lean('control:tampered-import-proof',tamper,'Proof.lean');assert r['exit']!=0 and 'rfl' in r['stdout'],r
    RESULT['controls']['tampered_import']={'proof_exit':r['exit'],'changed_funs_sha256':sha(tamper/'Current/Funs.lean'),
       'base_funs_sha256':sha(base/'generated/Funs.lean'),'detected':True}
    # Compare complete relevant output sets, without treating absolute path bytes as semantic proof.
    keys=['base-cold','base-prepared','base-clean']
    assert all(RESULT['cases'][k]['generated']==RESULT['cases'][keys[0]]['generated'] for k in keys[1:])
    assert all(normalized_llbc(WORK/k/'current.llbc')==normalized_llbc(WORK/keys[0]/'current.llbc') for k in keys[1:])
    RESULT['cold_prepared_clean_comparison']={'llbc_bytes_equal':False,
      'llbc_normalized_equal':True,'llbc_normalization':['options.dest_file locator removed','short_names array sorted'],
      'generated_bytes_equal':True}
    RESULT['cross_layer_manifest']=manifest(base)
    RESULT['subjects']={'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'cargo_sha256':sha(CARGO),
      'lean_sha256':sha(LEAN),'aeneas_olean_sha256':sha(BACKEND/'.lake/build/lib/lean/Aeneas.olean')}
    RESULT['limits']=['Manual fixture obligations are not Anneal annotation syntax or generated service output.',
      'Source-to-declaration association is a manually inspected lexical mapping, not an authenticated producer-issued map.',
      'Cached Lean dependencies were reused; clean means private Cargo target and consumer generation, not rebuilding toolchains or dependencies.',
      'The same local Mac, installed tool pins, and author performed both clean and prepared runs.']
    # Cargo build products are not the subject; retain their size and remove to bound disk consumption.
    RESULT['target_bytes_before_cleanup']={p.name:sum(x.stat().st_size for x in p.rglob('*') if x.is_file()) for p in [target,WORK/'target-clean',WORK/'target-mutated']}
    for p in [target,WORK/'target-clean',WORK/'target-mutated']:shutil.rmtree(p)
    (HERE/'results.json').write_text(json.dumps(RESULT,indent=2)+'\n')
    print(json.dumps({'commands':len(RESULT['commands']),'cases':list(RESULT['cases']),
      'controls':list(RESULT['controls']),'cold_prepared_clean_comparison':RESULT['cold_prepared_clean_comparison']}))
if __name__=='__main__':main()
