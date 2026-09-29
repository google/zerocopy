#!/usr/bin/env python3
"""Oracle-guided module reuse around one-shot Aeneas; not an Aeneas API."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE=Path(__file__).resolve().parent
WORK=HERE/'work';INPUTS=HERE/'inputs';OUTPUTS=HERE/'outputs'
T=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=T/'bin/charon';AENEAS=T/'bin/aeneas'
RUST=T/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=T/'elan/toolchains/leanprover--lean4---v4.30.0-rc2'
LEAN=LEANROOT/'bin/lean';BACKEND=T/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
NAMES=['Fixture/Types','Fixture/Funs','Fixture']
FILES={'Fixture/Types':'Types.lean','Fixture/Funs':'Funs.lean','Fixture':'Fixture.lean'}
DEPS={'Fixture/Types':[],'Fixture/Funs':['Fixture/Types'],'Fixture':['Fixture/Funs']}
RESULT={'tools':{},'commands':[],'variants':{},'policy':{},'controls':{}}

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inventory(root):return {p.name:{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(root.glob('*.lean'))}
def call(label,args,cwd,env=None,timeout=45):
    argv=list(map(str,args));t=time.monotonic()
    try:
        p=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
        row={'label':label,'argv':argv,'cwd':str(cwd),'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'seconds':round(time.monotonic()-t,3)}
    except subprocess.TimeoutExpired as e:
        row={'label':label,'argv':argv,'cwd':str(cwd),'exit':'timeout','stdout':str(e.stdout),'stderr':str(e.stderr),'seconds':round(time.monotonic()-t,3)}
    RESULT['commands'].append(row);return row
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(T/'rustup'),CARGO_HOME=str(T/'cargo'),CHARON_TOOLCHAIN_IS_IN_PATH='1',
        PATH=os.pathsep.join([str(RUST),str(T/'bin'),e.get('PATH','')]))
    return e
def leanenv(root):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ,LEAN_NUM_THREADS='1');e['LEAN_PATH']=os.pathsep.join(map(str,[root,*(p for p in libs if p.is_dir())]));return e
def generated_graph(root):
    # Parse only generated-module import edges; Aeneas is a fixed external root.
    lookup={m.replace('/','.'):m for m in NAMES};graph={}
    for module in NAMES:
        lines=(root/FILES[module]).read_text().splitlines()
        graph[module]=[lookup[x] for line in lines if line.startswith('import ')
                       for x in line.split()[1:] if x in lookup]
    return graph
def prepare_case(label):
    source=HERE/f'source-{label}.rs';fixture=WORK/'fixture.rs';llbc=WORK/'fixture.llbc'
    shutil.copyfile(source,fixture)
    if llbc.exists():llbc.unlink()
    output=OUTPUTS/label;output.mkdir()
    c=call(label+':charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,'--',fixture,
        '--crate-type','lib','--crate-name','trait_reuse','--edition','2021'],WORK,rustenv())
    assert c['exit']==0 and llbc.is_file(),c
    a=call(label+':aeneas',[AENEAS,'-backend','lean','-no-progress-bar','-sequential','-split-files',
        '-gen-lib-entry','-dest',output,llbc],WORK)
    assert a['exit']==0,a
    inp=INPUTS/label;inp.mkdir();shutil.copyfile(source,inp/'fixture.rs');shutil.copyfile(llbc,inp/'fixture.llbc')
    RESULT['variants'][label]={'rust_sha256':sha(source),'llbc_sha256':sha(llbc),'generated':inventory(output),
        'aeneas_seconds':a['seconds'],'charon_seconds':c['seconds']}
def layout(root,case,source_reuse=None):
    root.mkdir();(root/'Fixture').mkdir()
    for module in NAMES:
        name=FILES[module]
        src=(OUTPUTS/('base' if source_reuse and module in source_reuse else case)/name)
        dest=(root/name if module=='Fixture' else root/'Fixture'/name)
        shutil.copyfile(src,dest)
def compile_chain(label,root,skip=()):
    env=leanenv(root);before=len(RESULT['commands']);start=time.monotonic()
    for module in NAMES:
        if module in skip:continue
        r=call(label+':compile:'+module,[LEAN,'-o',module+'.olean',module+'.lean'],root,env)
        if r['exit']!=0:break
    rows=RESULT['commands'][before:]
    return {'seconds':round(time.monotonic()-start,3),'exits':[r['exit'] for r in rows],
            'compiled':[r['label'].split(':compile:')[1] for r in rows]}
def proof(label,root,case):
    use,combine=(3,14) if case=='body' else (2,13)
    text=('import Fixture\n'
        f'theorem caller : trait_reuse.core.use_step 1#u32 = .ok {use}#u32 := by rfl\n'
        f'theorem combined : trait_reuse.combine 1#u32 = .ok {combine}#u32 := by rfl\n'
        'theorem side : trait_reuse.side.untouched 1#u32 = .ok 11#u32 := by rfl\n'
        '#print axioms caller\n#print axioms combined\n#print axioms side\n')
    (root/'Proof.lean').write_text(text)
    r=call(label+':proof',[LEAN,'Proof.lean'],root,leanenv(root))
    return {'exit':r['exit'],'stdout':r['stdout'],'proof_sha256':sha(root/'Proof.lean')}
def main():
    assert shutil.disk_usage(HERE).free>2*1024**3
    for name,p in {'charon':CHARON,'aeneas':AENEAS,'lean':LEAN,
        'aeneas_olean':BACKEND/'.lake/build/lib/lean/Aeneas.olean'}.items():
        assert p.is_file(),p;RESULT['tools'][name]={'path':str(p),'sha256':sha(p)}
    for p in (WORK,INPUTS,OUTPUTS):
        if p.exists():shutil.rmtree(p)
        p.mkdir()
    for case in ['base','body','signature']:prepare_case(case)
    RESULT['generated_import_graph']={case:generated_graph(OUTPUTS/case) for case in ['base','body','signature']}
    assert all(graph==DEPS for graph in RESULT['generated_import_graph'].values())
    for case in ['base','body','signature']:
        root=WORK/('full-'+case);layout(root,case)
        compiled=compile_chain('full-'+case,root);assert compiled['exits']==[0,0,0],compiled
        checked=proof('full-'+case,root,case);assert checked['exit']==0 and 'sorryAx' not in checked['stdout'],checked
        RESULT['variants'][case]['fresh_lean']={'compile':compiled,'proof':checked}
    for case in ['body','signature']:
        old=RESULT['variants']['base']['generated'];new=RESULT['variants'][case]['generated']
        source_equal={m:old[FILES[m]]['sha256']==new[FILES[m]]['sha256'] for m in NAMES}
        artifact_reuse={}
        for m in NAMES:artifact_reuse[m]=source_equal[m] and all(artifact_reuse[d] for d in DEPS[m])
        RESULT['policy'][case]={'source_equal':source_equal,'artifact_reuse':artifact_reuse,
            'graph':DEPS,'rule':'reuse compiled OLean only if module source bytes and all imported generated module artifacts are unchanged'}
        root=WORK/('hybrid-'+case);layout(root,case,[m for m in NAMES if source_equal[m]])
        for m,reuse in artifact_reuse.items():
            if reuse:
                old_file=WORK/'full-base'/(m+'.olean')
                new_file=root/(m+'.olean');new_file.parent.mkdir(parents=True,exist_ok=True)
                shutil.copyfile(old_file,new_file)
        compiled=compile_chain('hybrid-'+case,root,[m for m in NAMES if artifact_reuse[m]])
        assert compiled['exits']==[0]*len(compiled['exits']),compiled
        checked=proof('hybrid-'+case,root,case);assert checked['exit']==0 and 'sorryAx' not in checked['stdout'],checked
        RESULT['policy'][case]['hybrid']={'compile':compiled,'proof':checked,
            'copied_source':[m for m in NAMES if source_equal[m]],
            'copied_olean':[m for m in NAMES if artifact_reuse[m]]}
    assert RESULT['policy']['body']['artifact_reuse']=={'Fixture/Types':True,'Fixture/Funs':False,'Fixture':False}
    assert not any(RESULT['policy']['signature']['artifact_reuse'].values())
    # Negative controls deliberately violate the computed dependency fence.
    stale=WORK/'unsafe-body-funs';layout(stale,'body')
    for m in ['Fixture/Types','Fixture/Funs']:
        dst=stale/(m+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(WORK/'full-base'/(m+'.olean'),dst)
    c=compile_chain('unsafe-body-funs',stale,['Fixture/Types','Fixture/Funs'])
    q=proof('unsafe-body-funs',stale,'body')
    assert c['exits']==[0] and q['exit']!=0,q
    RESULT['controls']['stale_funs']={'compile':c,'proof':q}
    stale=WORK/'unsafe-signature-types';layout(stale,'signature')
    dst=stale/'Fixture/Types.olean';shutil.copyfile(WORK/'full-base/Fixture/Types.olean',dst)
    c=compile_chain('unsafe-signature-types',stale,['Fixture/Types'])
    assert c['exits'] and c['exits'][0]!=0,c
    RESULT['controls']['stale_types']={'compile':c}
    RESULT['limits']=['one-shot whole-crate Aeneas CLI on every variant','oracle compares fresh generated bytes before allowing reuse',
        'no Aeneas internal incremental API','module-level rather than declaration-level granularity',
        'fresh Lean acceptance checks selected claims, not Rust-to-Lean semantic equivalence']
    (HERE/'results.json').write_text(json.dumps(RESULT,indent=2)+'\n')
    print(json.dumps({'body_reuse':RESULT['policy']['body']['artifact_reuse'],
        'signature_reuse':RESULT['policy']['signature']['artifact_reuse'],
        'negative_controls':{k:v['compile']['exits'] for k,v in RESULT['controls'].items()},
        'commands':len(RESULT['commands'])}))
if __name__=='__main__':main()
