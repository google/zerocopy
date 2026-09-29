#!/usr/bin/env python3
"""Causally gated synthetic generation publication, SIGKILL, GC, and recovery probes.

All source/artifact bytes here are invented small fixtures. This is not Anneal,
Lean, Lake, Charon, or Aeneas. Set ANNEAL_PROBE_SCRATCH to an owned scratch root.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import platform
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

SCRIPT=Path(__file__).resolve()
OUT=SCRIPT.parent/'results.json'
PHASES=('model-source','proof-source','model-artifact','proof-artifact',
        'manifest','validated','lock-acquired','after-move','after-pointer')

def canonical(obj):
    return json.dumps(obj,sort_keys=True,separators=(',',':')).encode()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def atomic_json(path,obj):
    tmp=path.with_name(path.name+'.tmp.'+str(os.getpid()))
    tmp.write_bytes(canonical(obj)+b'\n')
    os.replace(tmp,path)

def authority(root):
    return json.loads((root/'authority.json').read_text())

def set_authority(root,epoch,cancelled=()):
    atomic_json(root/'authority.json',{'epoch':epoch,'cancelled':sorted(cancelled)})

def init(root):
    for name in ('staging','generations','markers'):
        (root/name).mkdir(parents=True,exist_ok=True)

def marker(root,label,phase,suffix):
    return root/'markers'/f'{label}.{phase}.{suffix}'

def gate(root,label,phase,hold):
    if hold!=phase:return
    marker(root,label,phase,'ready').write_text('ready\n')
    go=marker(root,label,phase,'go')
    while not go.exists():time.sleep(0.005)

def bytes_for(variant,name):
    variants={
      'A':{'Model.lean':b'def value := 1\n','Proof.lean':b'-- A proof\n',
           'Legacy.lean':b'def legacy := 1\n',
           'Model.olean':b'FAKE-OLEAN-model-A\n','Proof.olean':b'FAKE-OLEAN-proof-A\n'},
      'B':{'Model.lean':b'def value := 2\n','Proof.lean':b'-- B proof\n',
           'Model.olean':b'FAKE-OLEAN-model-B\n','Proof.olean':b'FAKE-OLEAN-proof-B\n'},
      'Old':{'Model.lean':b'def value := 0\n','Proof.lean':b'-- old proof\n',
           'Model.olean':b'FAKE-OLEAN-model-old\n','Proof.olean':b'FAKE-OLEAN-proof-old\n'},
    }
    return variants[variant][name]

def expected_files(variant):
    return ['Model.lean','Proof.lean','Model.olean','Proof.olean'] + (['Legacy.lean'] if variant=='A' else [])

def validate_tree(path):
    mp=path/'manifest.json'
    if not mp.is_file():return {'valid':False,'reason':'manifest-missing'}
    try:m=json.loads(mp.read_text())
    except (OSError,ValueError):return {'valid':False,'reason':'manifest-invalid'}
    required=set(m.get('files',{}))
    present={p.name for p in path.iterdir() if p.is_file() and p.name not in ('manifest.json','lease.lock')}
    if present!=required:return {'valid':False,'reason':'file-set-mismatch'}
    for name,digest in m['files'].items():
        if sha((path/name).read_bytes())!=digest:return {'valid':False,'reason':'hash-mismatch'}
    if m.get('variant')=='B' and 'Legacy.lean' in present:
        return {'valid':False,'reason':'stale-legacy'}
    return {'valid':True,'variant':m['variant'],'epoch':m['epoch'],
            'files':sorted(required),'manifest_sha256':sha(mp.read_bytes())}

def selected(root):
    pointer=root/'current'
    if not pointer.is_symlink():return {'selected':None,'valid':False,'reason':'pointer-missing'}
    target=os.readlink(pointer)
    if not target.startswith('generations/') or '/' in target[len('generations/'):]:
        return {'selected':None,'valid':False,'reason':'pointer-outside-generations'}
    name=target[len('generations/'):]
    value=validate_tree(root/target)
    return {'selected':name,**value}

def worker(root,label,variant,epoch,hold):
    init(root)
    stage=root/'staging'/label
    stage.mkdir(exist_ok=False)
    for filename,phase in [('Model.lean','model-source'),('Proof.lean','proof-source'),
                           ('Model.olean','model-artifact'),('Proof.olean','proof-artifact')]:
        (stage/filename).write_bytes(bytes_for(variant,filename))
        gate(root,label,phase,hold)
    if variant=='A':(stage/'Legacy.lean').write_bytes(bytes_for(variant,'Legacy.lean'))
    files={name:sha((stage/name).read_bytes()) for name in expected_files(variant)}
    atomic_json(stage/'manifest.json',{'variant':variant,'epoch':epoch,'files':files,
                                       'source_sha256':sha(bytes_for(variant,'Model.lean'))})
    gate(root,label,'manifest',hold)
    validity=validate_tree(stage)
    if not validity['valid']:raise RuntimeError(validity)
    gate(root,label,'validated',hold)
    with (root/'publication.lock').open('a+b') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        gate(root,label,'lock-acquired',hold)
        auth=authority(root)
        if auth['epoch']!=epoch or label in auth['cancelled']:
            atomic_json(root/'markers'/f'{label}.result.json',{'status':'obsolete','authority':auth})
            return
        destination=root/'generations'/label
        os.replace(stage,destination)
        (destination/'lease.lock').touch()
        gate(root,label,'after-move',hold)
        temp_link=root/f'current.tmp.{os.getpid()}'
        temp_link.symlink_to('generations/'+label)
        os.replace(temp_link,root/'current')
        gate(root,label,'after-pointer',hold)
        atomic_json(root/'markers'/f'{label}.result.json',{'status':'published','selected':label})

def wait_for(path,timeout=10):
    deadline=time.monotonic()+timeout
    while time.monotonic()<deadline:
        if path.exists():return
        time.sleep(0.005)
    raise TimeoutError(path.name)

def spawn_worker(root,label,variant,epoch,hold=''):
    return subprocess.Popen([sys.executable,str(SCRIPT),'worker',str(root),label,variant,str(epoch),hold],
                            stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)

def finish(proc):
    out,err=proc.communicate(timeout=10)
    return {'exit':proc.returncode,'stdout':out,'stderr':err[-500:]}

def build_base(root):
    init(root);set_authority(root,1)
    p=spawn_worker(root,'A','A',1)
    r=finish(p)
    assert r['exit']==0,r
    s=selected(root)
    assert s['valid'] and s['selected']=='A'

def publish_B(root,label='B'):
    set_authority(root,2)
    p=spawn_worker(root,label,'B',2)
    r=finish(p)
    assert r['exit']==0,r
    s=selected(root)
    assert s['valid'] and s['selected']==label
    return r

def gc(root):
    sel=selected(root)
    current=sel['selected']
    removed=[];held=[]
    for path in sorted((root/'generations').iterdir()):
        if path.name==current:continue
        lease=path/'lease.lock'
        with lease.open('a+b') as fd:
            try:fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                held.append(path.name);continue
            shutil.rmtree(path)
            removed.append(path.name)
    for path in sorted((root/'staging').iterdir()):
        shutil.rmtree(path)
        removed.append('staging/'+path.name)
    return {'removed':removed,'held':held,'selected':current}

def crash_matrix(scratch):
    rows=[]
    for phase in PHASES:
        with tempfile.TemporaryDirectory(prefix='generation-'+phase+'-',dir=scratch) as t:
            root=Path(t);build_base(root);set_authority(root,2)
            p=spawn_worker(root,'B','B',2,phase)
            wait_for(marker(root,'B',phase,'ready'))
            before=selected(root)
            p.kill();r=finish(p)
            after=selected(root)
            cleanup=gc(root)
            final=selected(root)
            expect='B' if phase=='after-pointer' else 'A'
            assert r['exit']==-signal.SIGKILL and before['selected']==expect
            assert after['selected']==expect and final['selected']==expect
            assert before['valid'] and after['valid'] and final['valid']
            assert (after['files']==['Model.lean','Model.olean','Proof.lean','Proof.olean']) if expect=='B' else 'Legacy.lean' in after['files']
            rows.append({'phase':phase,'before_kill':before,'after_kill':after,'restart_gc':cleanup,
                         'reconstructed':final,'child_exit':r['exit']})
    return rows

def stale_completion(scratch):
    with tempfile.TemporaryDirectory(prefix='late-',dir=scratch) as t:
        root=Path(t);build_base(root)
        old=spawn_worker(root,'Old','Old',1,'validated')
        wait_for(marker(root,'Old','validated','ready'))
        set_authority(root,2,['Old'])
        newest=spawn_worker(root,'B','B',2)
        new_result=finish(newest)
        assert new_result['exit']==0 and selected(root)['selected']=='B'
        marker(root,'Old','validated','go').write_text('go\n')
        old_result=finish(old)
        old_status=json.loads((root/'markers'/'Old.result.json').read_text())
        state=selected(root);cleanup=gc(root)
        assert old_result['exit']==0 and old_status['status']=='obsolete'
        assert state['selected']=='B' and state['valid']
        return {'new_child_exit':new_result['exit'],'old_child_exit':old_result['exit'],
                'old_result':old_status,'current':state,'restart_gc':cleanup}

def reader(root,mode):
    target=os.readlink(root/'current')
    path=root/target
    fd=None
    if mode=='leased':
        fd=(path/'lease.lock').open('a+b')
        fcntl.flock(fd,fcntl.LOCK_SH)
    marker(root,mode,'pinned','ready').write_text(target+'\n')
    wait_for(marker(root,mode,'pinned','go'))
    try:value=(path/'Proof.lean').read_bytes();out={'result':'read','sha256':sha(value)}
    except FileNotFoundError:out={'result':'missing'}
    if fd:fd.close()
    atomic_json(root/'markers'/f'{mode}.result.json',out)

def gc_reader_cases(scratch):
    rows=[]
    for mode in ('leased','unleased'):
        with tempfile.TemporaryDirectory(prefix='reader-'+mode+'-',dir=scratch) as t:
            root=Path(t);build_base(root)
            p=subprocess.Popen([sys.executable,str(SCRIPT),'reader',str(root),mode],
                               stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            wait_for(marker(root,mode,'pinned','ready'))
            publish_B(root)
            first_gc=gc(root)
            marker(root,mode,'pinned','go').write_text('go\n')
            child=finish(p)
            reading=json.loads((root/'markers'/f'{mode}.result.json').read_text())
            second_gc=gc(root)
            assert child['exit']==0
            if mode=='leased':
                assert 'A' in first_gc['held'] and reading['result']=='read' and 'A' in second_gc['removed']
            else:
                assert 'A' in first_gc['removed'] and reading['result']=='missing'
            rows.append({'mode':mode,'first_gc':first_gc,'reader':reading,'second_gc':second_gc})
    return rows

def gc_crashed_reader(scratch):
    with tempfile.TemporaryDirectory(prefix='reader-crash-',dir=scratch) as t:
        root=Path(t);build_base(root)
        p=subprocess.Popen([sys.executable,str(SCRIPT),'reader',str(root),'leased'],
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        wait_for(marker(root,'leased','pinned','ready'))
        publish_B(root)
        before=gc(root)
        p.kill();dead=finish(p)
        after=gc(root)
        assert dead['exit']==-signal.SIGKILL
        assert 'A' in before['held'] and 'A' in after['removed']
        return {'before_crash_gc':before,'reader_exit':dead['exit'],'after_crash_gc':after}

def lock_holder(root):
    with (root/'publication.lock').open('a+b') as fd:
        fcntl.flock(fd,fcntl.LOCK_EX)
        marker(root,'holder','lock','ready').write_text('ready\n')
        wait_for(marker(root,'holder','lock','go'),timeout=60)

def lock_recovery(scratch):
    with tempfile.TemporaryDirectory(prefix='lock-',dir=scratch) as t:
        root=Path(t);build_base(root)
        p=subprocess.Popen([sys.executable,str(SCRIPT),'lock-holder',str(root)],
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        wait_for(marker(root,'holder','lock','ready'))
        p.kill();holder=finish(p)
        publish_B(root)
        state=selected(root)
        assert holder['exit']==-signal.SIGKILL and state['selected']=='B' and state['valid']
        return {'holder_exit':holder['exit'],'recovered_selected':state}

def repeated_restart(scratch):
    with tempfile.TemporaryDirectory(prefix='repeated-restart-',dir=scratch) as t:
        root=Path(t);build_base(root)
        cycles=[]
        for epoch in (2,3,4):
            label='B'+str(epoch)
            set_authority(root,epoch)
            p=spawn_worker(root,label,'B',epoch,'after-move')
            wait_for(marker(root,label,'after-move','ready'))
            p.kill();dead=finish(p)
            first=gc(root);second=gc(root);state=selected(root)
            assert dead['exit']==-signal.SIGKILL and state['selected']=='A' and state['valid']
            assert label in first['removed'] and not second['removed']
            cycles.append({'epoch':epoch,'killed_exit':dead['exit'],'first_gc':first,
                           'second_gc':second,'reconstructed':state['selected']})
        set_authority(root,5)
        p=spawn_worker(root,'B5','B',5)
        succeeded=finish(p)
        clean=gc(root);state=selected(root)
        assert succeeded['exit']==0 and state['selected']=='B5' and state['valid']
        assert 'A' in clean['removed']
        return {'cycles':cycles,'final_publish_exit':succeeded['exit'],
                'final_gc':clean,'final_selected':state}

def watcher_reconcile(scratch):
    with tempfile.TemporaryDirectory(prefix='watcher-',dir=scratch) as t:
        root=Path(t);build_base(root)
        observed={'epoch':1,'selected':'A'}
        publish_B(root)
        # Deliberately drop B's notification. A delayed duplicate A notice is also
        # no authority: reconciliation rereads the selected complete tree.
        event={'epoch':1,'selected':'A'}
        actual=selected(root)
        reconciled={'epoch':actual['epoch'],'selected':actual['selected']}
        assert observed==event and reconciled=={'epoch':2,'selected':'B'}
        return {'observed_before':observed,'late_duplicate_event':event,
                'selected_manifest':actual,'reconciled':reconciled}

def main():
    scratch=Path(os.environ.get('ANNEAL_PROBE_SCRATCH',tempfile.gettempdir()))
    if not scratch.is_dir():raise ValueError('scratch directory missing')
    result={'host':{'system':platform.platform(),'machine':platform.machine(),
                    'python':platform.python_version()},
            'phases':list(PHASES),
            'crash_matrix':crash_matrix(scratch),
            'stale_completion':stale_completion(scratch),
            'gc_readers':gc_reader_cases(scratch),
            'gc_crashed_reader':gc_crashed_reader(scratch),
            'lock_recovery':lock_recovery(scratch),
            'repeated_restart':repeated_restart(scratch),
            'watcher_reconcile':watcher_reconcile(scratch)}
    OUT.write_bytes(json.dumps(result,indent=2,sort_keys=True).encode()+b'\n')
    print(json.dumps({'crash_phases':len(result['crash_matrix']),
                      'selected_after_pointer_kill':result['crash_matrix'][-1]['after_kill']['selected'],
                      'late_old':result['stale_completion']['old_result']['status'],
                      'leased_reader':result['gc_readers'][0]['reader']['result'],
                      'unleased_reader':result['gc_readers'][1]['reader']['result']}))

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',nargs='?',default='probe',choices=['probe','worker','reader','lock-holder'])
    parser.add_argument('args',nargs='*')
    args=parser.parse_args()
    if args.mode=='worker':
        root,label,variant,epoch,hold=args.args
        worker(Path(root),label,variant,int(epoch),hold)
    elif args.mode=='reader':
        root,mode=args.args
        reader(Path(root),mode)
    elif args.mode=='lock-holder':lock_holder(Path(args.args[0]))
    else:main()
