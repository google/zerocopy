#!/usr/bin/env python3
"""Bounded cached Lean URI, historical-query and import-invalidation controls."""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path
from types import ModuleType

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
WORK = HERE / 'work'
LEAN = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
LAKE = LEAN.with_name('lake')
TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2'
os.environ['LEAN_BIN'] = str(LEAN)
source = REPORTS / 'anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2' / 'support' / 'probe.py'
# The published harness runs its own experiment at module load. Reuse only its
# function/class definitions, never that unguarded bottom-level main block.
definitions, separator, _ = source.read_text().partition('\ntry:main()')
assert separator, 'published harness footer changed'
prior = ModuleType('prior_lsp_harness_definitions')
prior.__file__ = str(source)
exec(compile(definitions, str(source), 'exec'), prior.__dict__)
Server = prior.Server
ENV = dict(prior.ENV)
EVENTS = []

def sha(p):
    b = p.read_bytes() if isinstance(p, Path) else p.encode()
    return hashlib.sha256(b).hexdigest()

def cmd(label, args, root, env=None, timeout=35):
    start = time.monotonic()
    p = subprocess.run([str(a) for a in args], cwd=root, env=env or ENV,
                       capture_output=True, text=True, timeout=timeout)
    result = dict(label=label, argv=[str(a) for a in args], rc=p.returncode,
                  stdout=p.stdout, stderr=p.stderr,
                  ms=round((time.monotonic()-start)*1000, 1))
    EVENTS.append(result)
    return result

def open_uri(s, uri, text, version=1):
    s.send(dict(jsonrpc='2.0', method='textDocument/didOpen', params={
        'textDocument': dict(uri=uri, languageId='lean', version=version, text=text)}))
    return s.request('textDocument/waitForDiagnostics', dict(uri=uri, version=version), 8)

def goal_uri(s, uri, line=2, col=2):
    return s.request('$/lean/plainGoal', dict(textDocument=dict(uri=uri),
                                               position=dict(line=line, character=col)), 8)

def make(root):
    root.mkdir(parents=True)
    (root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage uri_probe\n@[default_target]\nlean_lib Dep\n')
    (root/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    (root/'Dep.lean').write_text('def selected : Nat := 7\n')
    assert cmd('build-dep', [LAKE,'--keep-toolchain','--no-cache','build','Dep'], root)['rc']==0

def uri_suite():
    root=WORK/'uri';make(root)
    src='import Dep\ntheorem q : selected = 7 := by\n  exact ?_\n'
    (root/'Shell.lean').write_text(src)
    out=[]
    for mode in ('direct','lake-serve'):
        s=Server('uri-'+mode,root,mode)
        try:
            cases=[('shell',(root/'Shell.lean').as_uri()),
                   ('file-absent',(root/'Absent.lean').as_uri()),
                   ('custom','anneal://project/Projected.lean'),
                   ('untitled','untitled:Projected.lean')]
            for label,uri in cases:
                wait=open_uri(s,uri,src)
                goal=goal_uri(s,uri)
                diags=s.diags.get(uri)
                out.append(dict(mode=mode,case=label,uri=uri,physical_exists=(root/('Shell.lean' if label=='shell' else 'Absent.lean')).exists() if label in ('shell','file-absent') else None,
                                wait=wait,goal=goal,diagnostics=diags,source_sha256=sha(src)))
                s.send(dict(jsonrpc='2.0',method='textDocument/didClose',params={'textDocument':{'uri':uri}}))
        finally:s.stop()
    setup=[]
    for name in ('Shell.lean','Absent.lean'):
        setup.append(cmd('setup-'+name,[LAKE,'--keep-toolchain','--no-cache','setup-file',name],root))
    return dict(cases=out,setup=setup,dep_sha256=sha(root/'Dep.lean'))

def history_suite():
    root=WORK/'history';make(root)
    src=lambda n:f'import Dep\ntheorem historic : {n} = {n} := by\n  exact ?_\n'
    old=(root/'Rev1.lean').as_uri();live=(root/'Rev.lean').as_uri()
    s=Server('history',root,'direct')
    result=None
    try:
        first=open_uri(s,live,src(1));initial=goal_uri(s,live)
        oldwait=open_uri(s,old,src(1))
        resident_start=time.monotonic();oldgoal=goal_uri(s,old)
        resident_ms=round((time.monotonic()-resident_start)*1000,1)
        rss_before=prior.tree(s.p.pid)
        for version in (2,3):
            s.send(dict(jsonrpc='2.0',method='textDocument/didChange',params={
                'textDocument':{'uri':live,'version':version},
                'contentChanges':[{'text':src(version)}]}))
        start=time.monotonic()
        wait2=s.request('textDocument/waitForDiagnostics',{'uri':live,'version':2},8)
        wait3=s.request('textDocument/waitForDiagnostics',{'uri':live,'version':3},8)
        elapsed=round((time.monotonic()-start)*1000,1)
        latest=goal_uri(s,live);stillold=goal_uri(s,old)
        rss_after=prior.tree(s.p.pid)
        s.send(dict(jsonrpc='2.0',method='textDocument/didClose',params={'textDocument':{'uri':old}}))
        afterclose=goal_uri(s,old)
        reopen_start=time.monotonic();reopened_wait=open_uri(s,old,src(1))
        reopened_goal=goal_uri(s,old)
        reopened_ms=round((time.monotonic()-reopen_start)*1000,1)
        result=dict(first=first,initial=initial,oldwait=oldwait,oldgoal=oldgoal,
                    wait2=wait2,wait3=wait3,latest=latest,stillold=stillold,
                    afterclose=afterclose,reopened_wait=reopened_wait,reopened_goal=reopened_goal,
                    resident_old_goal_ms=resident_ms,reopened_old_wait_and_goal_ms=reopened_ms,
                    waits_ms=elapsed,rss_before=rss_before,
                    rss_after=rss_after,source_hashes={str(i):sha(src(i)) for i in (1,2,3)})
    finally:s.stop()
    fresh_start=time.monotonic()
    fresh=Server('history-fresh',root,'direct')
    try:
        result['fresh_wait']=open_uri(fresh,old,src(1))
        result['fresh_goal']=goal_uri(fresh,old)
        result['fresh_start_wait_goal_ms']=round((time.monotonic()-fresh_start)*1000,1)
        result['fresh_rss']=prior.tree(fresh.p.pid)
    finally:fresh.stop()
    return result

def import_suite():
    root=WORK/'imports';root.mkdir()
    (root/'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage import_probe\nlean_lib Model\nlean_lib Helper\n')
    (root/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    model=root/'Model.lean';helper=root/'Helper.lean';proof=root/'Proof.lean';proof2=root/'Proof2.lean'
    model.write_text('def model : Nat := 7\n')
    helper.write_text('import Model\ndef helper : Nat := model\n')
    baseline='import Helper\ntheorem checked : helper = 7 := by\n  rfl\n'
    proof.write_text(baseline);proof2.write_text(baseline.replace('checked','checked2'))
    rows=[]
    env=dict(ENV,LEAN_PATH=str(root/'.lake/build/lib/lean'))
    def cell(label,rebuild=True):
        build=cmd(label+'-build',[LAKE,'--keep-toolchain','--no-cache','build','Helper'],root) if rebuild else None
        a=cmd(label+'-proof',[LEAN,'--json','Proof.lean'],root,env)
        b=cmd(label+'-proof2',[LEAN,'--json','Proof2.lean'],root,env)
        rows.append(dict(label=label,build=build,proof=a,proof2=b,
                         source_hashes={p.name:sha(p) for p in (model,helper,proof,proof2)},
                         artifact_hashes={p.name:sha(p) for p in (root/'.lake/build/lib/lean/Model.olean',root/'.lake/build/lib/lean/Helper.olean') if p.exists()}))
    cell('base')
    proof.write_text(baseline.replace('  rfl','  decide'));cell('proof-body',False)
    proof.write_text(baseline.replace('helper = 7','helper = 8'));cell('statement',False)
    proof.write_text(baseline)
    helper.write_text('import Model\ndef helper : Nat := model + 1\n');cell('helper-change')
    helper.write_text('import Model\ndef helper : Nat := model\n')
    model.write_text('def model : Nat := 8\n');cell('model-change')
    proof.write_text(baseline.replace('helper = 7','helper = 8'))
    proof2.write_text(baseline.replace('checked','checked2').replace('helper = 7','helper = 8'))
    cell('updated-obligations',False)
    fanout=[]
    for i in range(8):
        p=root/f'Fan{i}.lean'
        p.write_text(f'import Helper\ntheorem fan{i} : helper = 8 := by\n  rfl\n')
    def fan_cell(label):
        checks=[]
        for i in range(8):
            p=root/f'Fan{i}.lean'
            r=cmd(f'{label}-fan{i}',[LEAN,'--json',p.name],root,env)
            checks.append(dict(name=p.name,source_sha256=sha(p),rc=r['rc'],stdout=r['stdout'],stderr=r['stderr']))
        fanout.append(dict(label=label,checks=checks,
                           model_sha256=sha(model),helper_sha256=sha(helper),
                           model_olean_sha256=sha(root/'.lake/build/lib/lean/Model.olean'),
                           helper_olean_sha256=sha(root/'.lake/build/lib/lean/Helper.olean')))
    fan_cell('eight-current')
    model.write_text('def model : Nat := 7\n')
    assert cmd('eight-model-change-build',[LAKE,'--keep-toolchain','--no-cache','build','Helper'],root)['rc']==0
    fan_cell('eight-stale')
    for i in range(8):
        p=root/f'Fan{i}.lean'
        p.write_text(p.read_text().replace('helper = 8','helper = 7'))
    fan_cell('eight-updated')
    return dict(rows=rows,fanout=fanout)

def main():
    assert LEAN.is_file() and LAKE.is_file()
    q=subprocess.run(['memory_pressure','-Q'],capture_output=True,text=True,timeout=5)
    m=re.search(r'System-wide memory free percentage: (\d+)%',q.stdout)
    assert m and int(m.group(1))>=25
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir()
    subject=dict(lean_sha256=sha(LEAN),lake_sha256=sha(LAKE),
                 lean_version=cmd('lean-version',[LEAN,'--version'],WORK)['stdout'].strip(),
                 free_percent=int(m.group(1)),source_harness_sha256=sha(source))
    result=dict(subject=subject,uri=uri_suite(),history=history_suite(),imports=import_suite(),commands=EVENTS)
    (HERE/'results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    # Retain source fixtures and hashes, not generated C/OLean build products.
    for fixture in ('uri','history','imports'):
        shutil.rmtree(WORK/fixture/'.lake')
    print('wrote',HERE/'results.json')

if __name__=='__main__':main()
