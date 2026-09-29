#!/usr/bin/env python3
"""Direct Lean resident/fresh worker split for imported instance and notation edits."""
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
WORK = HERE/'work'
HARNESS = REPORTS/'anneal-3730-lean-uri-history-import-boundaries-2026-09-29/support/probe.py'
spec = importlib.util.spec_from_file_location('cached_uri_harness',HARNESS)
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)
LEAN = harness.LEAN
PROOF = 'import Model\ntheorem q : selected = 7 := by\n  rfl\n'
CASES = {
    'instance': (
        'class Carrier where\n  number : Nat\ninstance : Carrier := ⟨7⟩\ndef selected : Nat := Carrier.number\n',
        'class Carrier where\n  number : Nat\ninstance : Carrier := ⟨9⟩\ndef selected : Nat := Carrier.number\n'),
    'notation': (
        'def left : Nat := 7\ndef right : Nat := 9\nnotation "selected" => left\n',
        'def left : Nat := 7\ndef right : Nat := 9\nnotation "selected" => right\n'),
}


def sha(x):
    if isinstance(x,Path):x=x.read_bytes()
    if isinstance(x,str):x=x.encode()
    return hashlib.sha256(x).hexdigest()


def command(label,args,root,env):
    p=subprocess.run([str(x) for x in args],cwd=root,env=env,capture_output=True,text=True,timeout=20)
    return dict(label=label,argv=[str(x) for x in args],rc=p.returncode,
                stdout=p.stdout,stderr=p.stderr)


def goal(server,uri):
    return server.request('$/lean/plainGoal',dict(textDocument=dict(uri=uri),
                          position=dict(line=2,character=4)),8)


def run_case(label,old,new):
    root=WORK/label
    root.mkdir()
    library=root/'.lake/build/lib/lean'
    library.mkdir(parents=True)
    model=root/'Model.lean';model.write_text(old)
    for name in ('Proof.lean','New.lean'):(root/name).write_text(PROOF)
    env=dict(harness.ENV,LEAN_PATH=str(library))
    build_old=command('build-old',[LEAN,'-o',library/'Model.olean','Model.lean'],root,env)
    batch_old=command('batch-old',[LEAN,'--json','Proof.lean'],root,env)
    assert build_old['rc']==0 and batch_old['rc']==0
    old_hash=sha(library/'Model.olean')
    server=harness.Server(label,root,'direct')
    server.n=1000
    try:
        old_uri=(root/'Proof.lean').as_uri()
        old_wait=harness.open_uri(server,old_uri,PROOF)
        old_goal=goal(server,old_uri)
        old_diags=server.diags.get(old_uri)
        model.write_text(new)
        build_new=command('build-new',[LEAN,'-o',library/'Model.olean','Model.lean'],root,env)
        assert build_new['rc']==0
        new_hash=sha(library/'Model.olean')
        resident_goal=goal(server,old_uri)
        resident_diags=server.diags.get(old_uri)
        new_uri=(root/'New.lean').as_uri()
        new_wait=harness.open_uri(server,new_uri,PROOF)
        new_goal=goal(server,new_uri)
        new_diags=server.diags.get(new_uri)
        old_after_new=goal(server,old_uri)
    finally:server.stop()
    batch_new=command('batch-new',[LEAN,'--json','Proof.lean'],root,env)
    assert batch_new['rc']!=0
    assert 'no goals' in str(old_goal) and 'no goals' in str(resident_goal)
    assert 'no goals' in str(old_after_new) and '⊢ selected = 7' in str(new_goal)
    assert not old_diags['diagnostics'] and not resident_diags['diagnostics']
    assert new_diags['diagnostics']
    return dict(label=label,old_source=old,new_source=new,proof=PROOF,
                old_source_sha256=sha(old),new_source_sha256=sha(new),
                old_olean_sha256=old_hash,new_olean_sha256=new_hash,
                build_old=build_old,batch_old=batch_old,old_wait=old_wait,
                old_goal=old_goal,old_diagnostics=old_diags,
                build_new=build_new,resident_goal=resident_goal,
                resident_diagnostics=resident_diags,new_wait=new_wait,
                new_goal=new_goal,new_diagnostics=new_diags,
                old_after_new=old_after_new,batch_new=batch_new)


def main():
    pressure=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
    found=re.search(r'System-wide memory free percentage: (\d+)%',pressure.stdout)
    assert found and int(found.group(1))>=25
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    rows=[run_case(name,*pair) for name,pair in CASES.items()]
    result=dict(subject=dict(lean_sha256=sha(LEAN),harness_sha256=sha(HARNESS),
                             probe_sha256=sha(Path(__file__)),host_free_percent=int(found.group(1))),
                cases=rows,wire_events=harness.prior.EVENTS)
    (HERE/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({r['label']:{'old_batch':r['batch_old']['rc'],
                                   'new_batch':r['batch_new']['rc']} for r in rows}))


if __name__=='__main__':main()
