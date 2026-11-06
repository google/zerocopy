#!/usr/bin/env python3
"""Pinned source/LLBC/generated-Lean/proof comparator mutants and oracle controls."""
from __future__ import annotations
import hashlib,json,os,re,shutil,subprocess
from pathlib import Path
H=Path(__file__).resolve().parent;W=H/'work';T=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=T/'bin/charon';AENEAS=T/'bin/aeneas'
RB=T/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin';RUSTC=RB/'rustc'
LR=T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=LR/'bin/lean'
BACK=T/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
BASE='''#![allow(dead_code)]
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
'''
REORDER='''#![allow(dead_code)]
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
'''
CHANGED=BASE.replace('wrapping_add(1)','wrapping_add(2)')
EXTERNAL='''#![allow(dead_code)]
unsafe extern "C" { fn external_double(x: u32) -> u32; }
pub fn call(x: u32) -> u32 { unsafe { external_double(x) } }
'''
REQUIRED={'obl_inc':('inc',1),'obl_twice':('twice',2),'obl_choose':('choose',3)}
R={'commands':[],'cases':{},'controls':{},'subjects':{},'comparison':{},'boundaries':[]}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def put(p,s):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def inv(root):return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.rglob('*')) if p.is_file()}
def call(label,argv,cwd,env=None,timeout=150):
    p=subprocess.run(list(map(str,argv)),cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
    x={'label':label,'argv':list(map(str,argv)),'cwd':str(cwd),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
    R['commands'].append(x);return x
def rustenv():
    e=dict(os.environ);e.update({'RUSTUP_HOME':str(T/'rustup'),'CARGO_HOME':str(T/'cargo'),
      'CHARON_TOOLCHAIN_IS_IN_PATH':'1','PATH':os.pathsep.join([str(RB),str(T/'bin'),e.get('PATH','')])});return e
def leanenv(root):
    deps=[BACK/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    deps += [BACK/'.lake/build/lib/lean',LR/'lib/lean']
    e=dict(os.environ);e['LEAN_PATH']=os.pathsep.join(map(str,[root,*(p for p in deps if p.is_dir())]));return e
def lean(label,root,src,out=None):
    args=[LEAN]
    if out:args+=['-o',out]
    return call(label,args+[src],root,leanenv(root))
def generate(label,source):
    case=W/label;case.mkdir();put(case/'source.rs',source);gen=case/'generated';gen.mkdir()
    llbc=case/'Source.llbc'
    a=call(label+':charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,
          '--',case/'source.rs','--crate-type','lib','--crate-name','comparator_probe','--edition','2021'],case,rustenv())
    assert a['exit']==0,a
    b=call(label+':aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential',
          '-split-files','-gen-lib-entry','-dest',gen,llbc],case)
    assert b['exit']==0,b
    obj=json.loads(llbc.read_text());assert not obj['has_errors']
    R['cases'][label]={'source_sha256':sha(case/'source.rs'),'llbc_sha256':sha(llbc),
      'llbc_bytes':llbc.stat().st_size,'generated':inv(gen),
      'charon_version':obj['charon_version'],'local_declarations':[
        {'def_id':d['def_id'],'name':d['item_meta']['name'][-1].get('Ident',[None])[0],
         'span':d['item_meta']['span']} for d in obj['translated']['fun_decls'] if d and d['item_meta']['is_local']]}
    return case
def consumer(label,case,model=None):
    root=W/('consumer-'+label);(root/'Source').mkdir(parents=True)
    gen=case/'generated'
    for n in ['Types.lean','Funs.lean']:shutil.copyfile(gen/n,root/'Source'/n)
    shutil.copyfile(gen/'Source.lean',root/'Source.lean')
    mods=['Source/Types']
    if model is not None:
        put(root/'Source/FunsExternal.lean',model);mods.append('Source/FunsExternal')
    mods+=['Source/Funs','Source']
    for m in mods:
        r=lean(label+':compile:'+m,root,m+'.lean',m+'.olean');assert r['exit']==0,r
    return root
def strong_text(vals=(1,2,3)):
    return 'import Source\n'+''.join(
      f'theorem {name} : comparator_probe.{fn} 0#u32 = .ok {v}#u32 := by rfl\n#check {name}\n#print axioms {name}\n'
      for (name,(fn,_)),v in zip(REQUIRED.items(),vals))
def accepted(text,proof_output,source_hash,expected_source_hash,model_hash,expected_model_hash):
    declarations=re.findall(r'^theorem\s+(obl_\w+)\s*:\s*(.*?)\s*:=',text,re.M)
    expected=[(name,f'comparator_probe.{fn} 0#u32 = .ok {v}#u32') for name,(fn,v) in REQUIRED.items()]
    reasons=[]
    if declarations!=expected:reasons.append('obligation/proposition mismatch')
    if source_hash!=expected_source_hash:reasons.append('source generation mismatch')
    if model_hash!=expected_model_hash:reasons.append('imported model mismatch')
    if 'sorryAx' in proof_output:reasons.append('admission axiom')
    return {'accepted':not reasons,'reasons':reasons,'actual_propositions':declarations,'expected_propositions':expected}
def model_manifest(case):
    obj=json.loads((case/'Source.llbc').read_text());lines=(case/'generated/Funs.lean').read_text().splitlines()
    rows=[]
    for d in obj['translated']['fun_decls']:
        if not d or not d['item_meta']['is_local']:continue
        name=d['item_meta']['name'][-1].get('Ident',[None])[0]
        pos=next((i for i,s in enumerate(lines,1) if re.match(r'^def '+re.escape(name)+r'\b',s)),None)
        rows.append({'name':name,'charon_def_id':d['def_id'],'source_span':d['item_meta']['span'],
          'generated_lean_def_line':pos})
    return {'input_source_sha256':sha(case/'source.rs'),'llbc_sha256':sha(case/'Source.llbc'),
      'generated_files':inv(case/'generated'),'rows':rows,
      'proven_cross_layer_map':None,'manual_obligations':list(REQUIRED)}
def main():
    assert shutil.disk_usage(H).free>10*(1<<30)
    for p in [CHARON,AENEAS,RUSTC,LEAN,BACK/'.lake/build/lib/lean/Aeneas.olean']:assert p.is_file(),p
    if W.exists():shutil.rmtree(W)
    W.mkdir()
    cases={name:generate(name,s) for name,s in [('base',BASE),('reorder',REORDER),('changed',CHANGED),('clean-rerun',BASE),('external',EXTERNAL)]}
    for name,vals in [('base',(1,2,3)),('reorder',(1,2,3)),('changed',(2,4,5)),('clean-rerun',(1,2,3))]:
        case=cases[name]
        check='#[path = "source.rs"] mod subject;\nfn main() {\n'+''.join(
          f'  assert_eq!(subject::{fn}(0), {v});\n' for fn,v in zip(['inc','twice','choose'],vals))+'}\n'
        put(case/'RustOracle.rs',check)
        binary=case/'rust-oracle'
        rc=call(name+':rustc-oracle-build',[RUSTC,'--edition=2021',case/'RustOracle.rs','-o',binary],case,rustenv())
        assert rc['exit']==0,rc
        run=call(name+':rust-oracle-run',[binary],case)
        assert run['exit']==0,run
        R['cases'][name]['rust_oracle']={'source_sha256':sha(case/'RustOracle.rs'),
          'binary_sha256':sha(binary),'binary_bytes':binary.stat().st_size,'exit':run['exit']}
        binary.unlink()
    roots={name:consumer(name,cases[name]) for name in ['base','reorder','changed','clean-rerun']}
    for name,vals in [('base',(1,2,3)),('reorder',(1,2,3)),('changed',(2,4,5)),('clean-rerun',(1,2,3))]:
        root=roots[name];put(root/'Proof.lean',strong_text(vals));r=lean(name+':proof',root,'Proof.lean')
        assert r['exit']==0 and 'sorryAx' not in r['stdout'],r
        R['cases'][name]['consumer']=inv(root);R['cases'][name]['proof_stdout']=r['stdout']
    base=roots['base'];changed=roots['changed'];sourcehash=sha(cases['base']/'source.rs');modelhash=sha(base/'Source/Funs.olean')
    mainstrong=strong_text();x=accepted(mainstrong,R['cases']['base']['proof_stdout'],sourcehash,sourcehash,modelhash,modelhash)
    assert x['accepted'];R['controls']['strong']={'lean_exit':0,'manifest':x}
    weak='import Source\ntheorem obl_inc : True := by trivial\ntheorem obl_twice : comparator_probe.twice 0#u32 = .ok 2#u32 := by rfl\ntheorem obl_choose : comparator_probe.choose 0#u32 = .ok 3#u32 := by rfl\n#check obl_inc\n#print axioms obl_inc\n'
    put(base/'Weak.lean',weak);r=lean('weak-proposition',base,'Weak.lean');assert r['exit']==0,r
    x=accepted(weak,r['stdout'],sourcehash,sourcehash,modelhash,modelhash);assert not x['accepted']
    R['controls']['weaker_proposition']={'lean_exit':r['exit'],'stdout':r['stdout'],'manifest':x,'file_sha256':sha(base/'Weak.lean')}
    missing=mainstrong.replace('theorem obl_choose : comparator_probe.choose 0#u32 = .ok 3#u32 := by rfl\n#check obl_choose\n#print axioms obl_choose\n','')
    put(base/'Missing.lean',missing);r=lean('missing-obligation',base,'Missing.lean');assert r['exit']==0,r
    x=accepted(missing,r['stdout'],sourcehash,sourcehash,modelhash,modelhash);assert not x['accepted']
    R['controls']['missing_obligation']={'lean_exit':r['exit'],'manifest':x,'file_sha256':sha(base/'Missing.lean')}
    sorry='import Source\ntheorem obl_inc : comparator_probe.inc 0#u32 = .ok 99#u32 := by sorry\n#print axioms obl_inc\n'
    put(base/'Sorry.lean',sorry);r=lean('admitted-claim',base,'Sorry.lean');assert r['exit']==0 and 'sorryAx' in r['stdout'],r
    x=accepted(sorry,r['stdout'],sourcehash,sourcehash,modelhash,modelhash);assert not x['accepted']
    R['controls']['admitted_claim']={'lean_exit':r['exit'],'stdout':r['stdout'],'manifest':x,'file_sha256':sha(base/'Sorry.lean')}
    # A complete strong proof against the old import is still accepted by Lean after
    # the source changes. The explicit source-generation fence catches that case.
    r=lean('stale-source-old-import',base,'Proof.lean');assert r['exit']==0,r
    x=accepted(mainstrong,r['stdout'],sha(cases['changed']/'source.rs'),sourcehash,modelhash,modelhash)
    assert not x['accepted'] and 'source generation mismatch' in x['reasons']
    R['controls']['stale_source']={'lean_exit':r['exit'],'manifest':x}
    # Swap a private model import while retaining the base proposition/proof bytes.
    swap=W/'consumer-swapped';shutil.copytree(base,swap)
    shutil.copyfile(cases['changed']/'generated/Funs.lean',swap/'Source/Funs.lean')
    for m in ['Source/Funs','Source']:
        r=lean('swap-compile:'+m,swap,m+'.lean',m+'.olean');assert r['exit']==0,r
    r=lean('swapped-import-old-proof',swap,'Proof.lean');assert r['exit']!=0 and 'rfl' in r['stdout'],r
    # Even a weak theorem can pass on that swapped import; only imported-model
    # identity blocks it from being confused with the base generation.
    weak_only='import Source\ntheorem obl_inc : True := by trivial\n#check obl_inc\n'
    put(swap/'WeakOnly.lean',weak_only)
    rweak=lean('swapped-import-weak-proof',swap,'WeakOnly.lean');assert rweak['exit']==0,rweak
    x=accepted(weak_only,rweak['stdout'],sourcehash,sourcehash,sha(swap/'Source/Funs.olean'),modelhash)
    assert not x['accepted'] and 'imported model mismatch' in x['reasons']
    R['controls']['swapped_import']={'old_proof_exit':r['exit'],'weak_proof_exit':rweak['exit'],
      'manifest':x,'base_import_sha256':modelhash,'swapped_import_sha256':sha(swap/'Source/Funs.olean')}
    # External user model: generated Aeneas files are held fixed while the model
    # source and compiled imported Funs object differ.
    ext=cases['external'];template=(ext/'generated/FunsExternal_Template.lean').read_text()
    ax=consumer('external-axiom',ext,template)
    concrete=template.replace('axiom external_double : Std.U32 → Result Std.U32',
      'def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)')
    assert concrete!=template
    co=consumer('external-concrete',ext,concrete)
    put(ax/'AxiomCheck.lean','import Source\n#print axioms comparator_probe.call\n')
    ar=lean('external-axiom-inventory',ax,'AxiomCheck.lean');assert ar['exit']==0 and 'external_double' in ar['stdout'],ar
    put(co/'ConcreteCheck.lean','import Source\n#print axioms comparator_probe.call\ntheorem call_one : comparator_probe.call 1#u32 = .ok 2#u32 := by rfl\n')
    cr=lean('external-concrete-oracle',co,'ConcreteCheck.lean');assert cr['exit']==0 and 'does not depend on any axioms' in cr['stdout'],cr
    same_generated=all(sha(ax/f)==sha(co/f) for f in ['Source.lean','Source/Types.lean','Source/Funs.lean'])
    assert same_generated
    R['controls']['external_model']={'generated_equal':same_generated,
      'axiom_model_source_sha256':sha(ax/'Source/FunsExternal.lean'),
      'concrete_model_source_sha256':sha(co/'Source/FunsExternal.lean'),
      'axiom_import_sha256':sha(ax/'Source/Funs.olean'),
      'concrete_import_sha256':sha(co/'Source/Funs.olean'),
      'axiom_stdout':ar['stdout'],'concrete_stdout':cr['stdout'],
      'axiom_exit':ar['exit'],'concrete_exit':cr['exit']}
    assert R['controls']['external_model']['axiom_import_sha256']!=R['controls']['external_model']['concrete_import_sha256']
    # Scope of equality: exact source and selected Lean proof semantics, not raw
    # LLBC/Lean byte equality across distinct paths or a Rust correctness proof.
    R['comparison']={'base_vs_reorder_source_bytes_equal':sha(cases['base']/'source.rs')==sha(cases['reorder']/'source.rs'),
      'base_vs_reorder_llbc_bytes_equal':sha(cases['base']/'Source.llbc')==sha(cases['reorder']/'Source.llbc'),
      'base_vs_reorder_funs_bytes_equal':sha(cases['base']/'generated/Funs.lean')==sha(cases['reorder']/'generated/Funs.lean'),
      'base_vs_reorder_selected_proof_stdout_equal':R['cases']['base']['proof_stdout']==R['cases']['reorder']['proof_stdout'],
      'base_vs_clean_source_bytes_equal':sha(cases['base']/'source.rs')==sha(cases['clean-rerun']/'source.rs'),
      'base_vs_clean_selected_proof_stdout_equal':R['cases']['base']['proof_stdout']==R['cases']['clean-rerun']['proof_stdout'],
      'base_vs_changed_source_bytes_equal':sha(cases['base']/'source.rs')==sha(cases['changed']/'source.rs'),
      'base_vs_changed_import_bytes_equal':modelhash==sha(changed/'Source/Funs.olean')}
    assert not R['comparison']['base_vs_reorder_source_bytes_equal'] and R['comparison']['base_vs_reorder_selected_proof_stdout_equal']
    assert R['comparison']['base_vs_clean_source_bytes_equal'] and R['comparison']['base_vs_clean_selected_proof_stdout_equal']
    R['model_manifest']={name:model_manifest(cases[name]) for name in cases}
    R['subjects']={'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'rustc_sha256':sha(RUSTC),
      'lean_sha256':sha(LEAN),'aeneas_olean_sha256':sha(BACK/'.lake/build/lib/lean/Aeneas.olean')}
    R['boundaries']=['Manually chosen obligations and comparator, not Anneal-generated service.',
      'Selected rfl/cargo-independent values do not prove Rust-to-Lean soundness.',
      'External concrete model is a user assumption, not verified foreign implementation.',
      'Cross-layer name/span/comment links are lexical; no authenticated producer map.',
      'Fresh rerun shares host, toolchain pins and prebuilt Lean dependencies.']
    (H/'results.json').write_text(json.dumps(R,indent=2)+'\n')
    print(json.dumps({'commands':len(R['commands']),'cases':list(R['cases']),
      'controls':list(R['controls']),'comparison':R['comparison']}))
if __name__=='__main__':main()
