#!/usr/bin/env python3
"""Pinned one-shot Charon/Aeneas module-move and fresh-Lean proof control."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

S = Path(__file__).resolve().parent
T = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON, AENEAS = T/'bin/charon', T/'bin/aeneas'
RUST = T/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEAN_ROOT = T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN = LEAN_ROOT/'bin/lean'
BACKEND = T/'aeneas-release/backends/lean'
PKGS = ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
BASE = '''#![allow(dead_code)]
pub mod core {
    pub fn use_step(x: u32) -> u32 { x.wrapping_add(1) }
}
pub fn caller(x: u32) -> u32 { core::use_step(x) }
'''
MOVED = '''#![allow(dead_code)]
pub mod moved {
    pub mod core {
        pub fn use_step(x: u32) -> u32 { x.wrapping_add(1) }
    }
}
pub fn caller(x: u32) -> u32 { moved::core::use_step(x) }
'''

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def call(label, args, cwd, env=None):
    p = subprocess.run([str(a) for a in args], cwd=cwd, env=env, capture_output=True, text=True, timeout=90)
    return dict(label=label, argv=[str(a) for a in args], cwd=str(cwd), exit=p.returncode,
                stdout=p.stdout, stderr=p.stderr)
def rustenv():
    e = dict(os.environ)
    e.update(RUSTUP_HOME=str(T/'rustup'), CARGO_HOME=str(T/'cargo'), CHARON_TOOLCHAIN_IS_IN_PATH='1',
             PATH=os.pathsep.join([str(RUST), str(T/'bin'), e.get('PATH','')]))
    return e
def leanenv(root):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PKGS]
    libs += [BACKEND/'.lake/build/lib/lean', LEAN_ROOT/'lib/lean']
    e=dict(os.environ, LEAN_NUM_THREADS='1')
    e['LEAN_PATH']=os.pathsep.join(map(str, [root, *(p for p in libs if p.is_dir())]))
    return e
def files(root):
    return {p.name:dict(size=p.stat().st_size, sha256=sha(p)) for p in sorted(root.glob('*.lean'))}
def main():
    assert all(p.is_file() for p in [CHARON,AENEAS,LEAN,BACKEND/'.lake/build/lib/lean/Aeneas.olean'])
    work=S/'work'
    if work.exists(): shutil.rmtree(work)
    work.mkdir()
    out=dict(schema='anneal-aeneas-namespace-move-v1', tool_sha256={k:sha(v) for k,v in
        {'charon':CHARON,'aeneas':AENEAS,'lean':LEAN}.items()}, cases={})
    for name,src in [('base',BASE),('moved',MOVED)]:
        d=work/name;d.mkdir();(d/'fixture.rs').write_text(src)
        llbc=d/'fixture.llbc';gen=d/'generated';gen.mkdir()
        c=call(name+':charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,'--',d/'fixture.rs',
            '--crate-type','lib','--crate-name','move_probe','--edition','2021'],d,rustenv())
        assert c['exit']==0 and llbc.is_file(), c
        a=call(name+':aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential','-split-files',
            '-gen-lib-entry','-dest',gen,llbc],d)
        assert a['exit']==0,a
        modules=[('Types','Fixture/Types'),('Funs','Fixture/Funs'),('Fixture','Fixture')]
        (d/'Fixture').mkdir()
        for source,mod in modules:
            sourcefile=gen/(source+'.lean'); assert sourcefile.is_file(),files(gen)
            dest=d/(mod+'.lean');dest.parent.mkdir(exist_ok=True)
            shutil.copyfile(sourcefile,dest)
        env=leanenv(d); comp=[]
        for _,mod in modules:
            r=call(name+':compile:'+mod,[LEAN,'-o',mod+'.olean',mod+'.lean'],d,env);comp.append(r)
            assert r['exit']==0,r
        proof='import Fixture\ntheorem caller : move_probe.caller 1#u32 = .ok 2#u32 := by rfl\n'
        helper=('move_probe.core.use_step' if name=='base' else 'move_probe.moved.core.use_step')
        proof+=f'theorem helper : {helper} 1#u32 = .ok 2#u32 := by rfl\n#print axioms caller\n#print axioms helper\n'
        (d/'Proof.lean').write_text(proof)
        oracle=call(name+':proof',[LEAN,'Proof.lean'],d,env)
        assert oracle['exit']==0 and 'sorryAx' not in oracle['stdout'],oracle
        out['cases'][name]=dict(source_sha256=sha(d/'fixture.rs'),llbc_sha256=sha(llbc),
            generated=files(gen),commands=[c,a,*comp,oracle],proof_sha256=sha(d/'Proof.lean'))
    moved=work/'moved';env=leanenv(moved)
    (moved/'OldProof.lean').write_text('import Fixture\n#check move_probe.core.use_step\n')
    negative=call('moved:old-name-negative',[LEAN,'OldProof.lean'],moved,env)
    assert negative['exit']!=0 and 'Unknown identifier' in (negative['stdout']+negative['stderr']),negative
    out['old_name_negative']=negative
    assert out['cases']['base']['generated']['Funs.lean']['sha256']!=out['cases']['moved']['generated']['Funs.lean']['sha256']
    (S/'raw-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'base_proof_exit':0,'moved_proof_exit':0,'old_name_exit':negative['exit']}))
if __name__=='__main__':main()
