#!/usr/bin/env python3
"""Bounded pinned Charon -> one-shot Aeneas -> batch Lean oracle.

No installation, package resolution, or Aeneas library call is performed.
Running this script replaces only this report's support/work and result files.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon'
AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph',
          'LeanSearchClient','plausible','mathlib']
BASE='''#![allow(dead_code)]
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }
'''
MUTATED=BASE.replace('wrapping_add(1)','wrapping_add(2)')
EXTERNAL='''#![allow(dead_code)]
unsafe extern "C" { fn external_double(x: u32) -> u32; }
pub fn call(x: u32) -> u32 { unsafe { external_double(x) } }
'''
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files',
       '-gen-lib-entry','-print-unknown-externals']

def sha(path:Path)->str:return hashlib.sha256(path.read_bytes()).hexdigest()
def run(label:str, argv:list[Path|str], cwd:Path, env:dict[str,str]|None=None)->dict:
    command=[str(x) for x in argv]
    p=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True,timeout=150)
    return {'label':label,'argv':command,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
def write(path:Path,content:str)->None:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
def inventory(root:Path)->dict:
    return {p.relative_to(root).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
            for p in sorted(root.rglob('*')) if p.is_file()}
def lean_path(compiled:Path)->str:
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    assert all(p.is_dir() for p in libs[-2:])
    return os.pathsep.join(map(str,[compiled,*(p for p in libs if p.is_dir())]))
def lean_run(label:str,compiled:Path,input_name:str,output_name:str|None=None)->dict:
    env=dict(os.environ);env['LEAN_PATH']=lean_path(compiled)
    argv=[LEAN]
    if output_name:argv += ['-o',output_name]
    argv += [input_name]
    return run(label,argv,compiled,env)
def setup_compiled(label:str, generated:Path, external_model:str|None=None)->Path:
    compiled=WORK/f'compiled-{label}'
    entry=label.split('-')[0].capitalize()
    module=compiled/entry
    module.mkdir(parents=True)
    for name in ('Types','Funs'):
        shutil.copyfile(generated/f'{name}.lean',module/f'{name}.lean')
    shutil.copyfile(generated/f'{entry}.lean',compiled/f'{entry}.lean')
    if external_model is not None:
        write(module/'FunsExternal.lean',external_model)
    return compiled
def compile_chain(label:str,compiled:Path,with_external:bool=False)->list[dict]:
    entry=label.split('-')[0].capitalize()
    modules=[f'{entry}/Types']
    if with_external:modules.append(f'{entry}/FunsExternal')
    modules.extend([f'{entry}/Funs',entry])
    records=[]
    for module in modules:
        result=lean_run(f'{label}:{module}',compiled,f'{module}.lean',f'{module}.olean')
        records.append(result)
        if result['exit']:break
    return records
def declaration_inventory(llbc:Path, generated:Path)->dict:
    data=json.loads(llbc.read_text())
    translated=data['translated']
    charon=[]
    for kind in ('type_decls','trait_decls','trait_impls','fun_decls'):
        for item in translated[kind]:
            if not item:continue
            meta=item['item_meta']
            charon.append({'kind':kind,'def_id':item['def_id'],
                           'name_parts':meta['name'],'span':meta.get('span'),
                           'is_local':meta.get('is_local')})
    lean=[]
    for p in sorted(generated.glob('*.lean')):
        last_source=None
        for line_number,line in enumerate(p.read_text().splitlines(),1):
            if 'Source:' in line:last_source=line.strip()
            match=re.match(r'^\s*(?:def|structure|axiom|theorem|inductive|abbrev)\s+([^\s(:]+)',line)
            if match:
                lean.append({'file':p.name,'line':line_number,'head':line.strip(),
                             'name':match.group(1),'nearest_source_comment':last_source})
    return {'charon_version':data['charon_version'],'crate_name':translated['crate_name'],
            'has_errors':data['has_errors'],'charon_declarations':charon,
            'lean_declarations':lean,'proven_def_id_to_lean_range':None,
            'anneal_obligation_mapping':None}

def main()->None:
    assert shutil.disk_usage(HERE).free>10*1024**3,'less than 10 GiB free'
    assert all(p.is_file() for p in (CHARON,AENEAS,LEAN))
    assert (BACKEND/'.lake/build/lib/lean/Aeneas.olean').is_file()
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    rustenv=dict(os.environ)
    rustenv.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
                    'CHARON_TOOLCHAIN_IS_IN_PATH':'1',
                    'PATH':os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),rustenv.get('PATH','')])})
    records=[];manifests={};outputs={}
    for label,source in [('base',BASE),('mutated',MUTATED),('external',EXTERNAL)]:
        case=WORK/label;case.mkdir()
        write(case/'source.rs',source)
        llbc=case/f'{label}.llbc'
        result=run(label+':charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,
                   '--',case/'source.rs','--crate-type','lib','--crate-name','oracle_probe','--edition','2021'],case,rustenv)
        records.append(result);assert result['exit']==0,result
        generated=case/'generated';generated.mkdir()
        result=run(label+':aeneas',[AENEAS,*FLAGS,'-dest',generated,llbc],case)
        records.append(result);assert result['exit']==0,result
        manifests[label]=declaration_inventory(llbc,generated)
        outputs[label]={'source_sha256':sha(case/'source.rs'),'llbc_sha256':sha(llbc),
                        'generated':inventory(generated)}
    # Exact schema marker rejection; no second real Charon version is implied.
    bad=json.loads((WORK/'base/base.llbc').read_text());bad['charon_version']='0.1.999'
    write(WORK/'schema-bad.llbc',json.dumps(bad,separators=(',',':')))
    schema_dest=WORK/'schema-output';schema_dest.mkdir()
    result=run('schema:aeneas',[AENEAS,*FLAGS,'-dest',schema_dest,WORK/'schema-bad.llbc'],WORK)
    records.append(result);assert result['exit']!=0 and not list(schema_dest.iterdir())

    # The generated source's module names are tied to its LLBC basename.
    for label,expected_inc,expected_twice in [('base',1,2),('mutated',2,4)]:
        generated=WORK/label/'generated'
        compiled=setup_compiled(label,generated)
        chain=compile_chain(label,compiled);records+=chain
        assert all(x['exit']==0 for x in chain),chain
        entry=label.capitalize()
        write(compiled/'Check.lean',f'''import {entry}\n#eval oracle_probe.inc 0#u32\n#eval oracle_probe.twice 0#u32\nexample : oracle_probe.inc 0#u32 = .ok {expected_inc}#u32 := by rfl\nexample : oracle_probe.twice 0#u32 = .ok {expected_twice}#u32 := by rfl\n#print axioms oracle_probe.inc\n''')
        result=lean_run(label+':oracle',compiled,'Check.lean');records.append(result)
        assert result['exit']==0 and 'sorryAx' not in result['stdout'],result
        write(compiled/'CheckWrong.lean',f'import {entry}\nexample : oracle_probe.inc 0#u32 = .ok {expected_inc+1}#u32 := by rfl\n')
        result=lean_run(label+':wrong-oracle',compiled,'CheckWrong.lean');records.append(result)
        assert result['exit']!=0 and 'Tactic `rfl` failed' in result['stdout'],result

    generated=WORK/'external/generated'
    template=(generated/'FunsExternal_Template.lean').read_text()
    assert 'axiom external_double : Std.U32 → Result Std.U32' in template
    missing=setup_compiled('external-missing',generated)
    chain=compile_chain('external-missing',missing);records+=chain
    assert chain[-1]['exit']!=0 and 'FunsExternal.olean' in chain[-1]['stdout']
    axiom=setup_compiled('external-axiom',generated,template)
    chain=compile_chain('external-axiom',axiom,True);records+=chain
    assert all(x['exit']==0 for x in chain),chain
    write(axiom/'Check.lean','import External\n#check oracle_probe.call\n#print axioms oracle_probe.call\n')
    result=lean_run('external-axiom:oracle',axiom,'Check.lean');records.append(result)
    assert result['exit']==0 and '[external_double]' in result['stdout'],result
    concrete_text=template.replace('axiom external_double : Std.U32 → Result Std.U32',
        'def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)')
    concrete=setup_compiled('external-concrete',generated,concrete_text)
    chain=compile_chain('external-concrete',concrete,True);records+=chain
    assert all(x['exit']==0 for x in chain),chain
    write(concrete/'Check.lean','''import External\n#eval oracle_probe.call 1#u32\n#print axioms oracle_probe.call\nexample : oracle_probe.call 1#u32 = .ok 2#u32 := by rfl\n''')
    result=lean_run('external-concrete:oracle',concrete,'Check.lean');records.append(result)
    assert result['exit']==0 and 'does not depend on any axioms' in result['stdout'],result

    (HERE/'declaration-manifest.json').write_text(json.dumps(manifests,indent=2)+'\n')
    results={'subjects':{'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),
                         'lean_sha256':sha(LEAN),'aeneas_olean_sha256':sha(BACKEND/'.lake/build/lib/lean/Aeneas.olean')},
             'outputs':outputs,'records':records,
             'external_generated_same_for_axiom_and_concrete':True,
             'external_model_sha256':{'axiom':sha(axiom/'External/FunsExternal.lean'),
                                       'concrete':sha(concrete/'External/FunsExternal.lean')},
             'model_limits':['no registered Aeneas registry mutation','no same-process Aeneas API',
                             'no authenticated Charon def_id to Lean range relation']}
    (HERE/'results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'assertions':'passed','record_count':len(records),
                      'generated_cases':list(outputs),'schema_exit':next(x['exit'] for x in records if x['label']=='schema:aeneas')}))

if __name__=='__main__':main()
