#!/usr/bin/env python3
"""One bounded full-chain replay with workspace file accounting."""
import hashlib, importlib.util, json, os, re, shutil, stat, subprocess, sys, threading, time
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PUBLISH = Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish')
BASE = PUBLISH/'reports/anneal-3730-full-lake-server-chain-2026-09-29/support'
PRIOR = json.loads((BASE/'results.json').read_text())
spec = importlib.util.spec_from_file_location('r48_i113', BASE/'probe.py')
r48 = importlib.util.module_from_spec(spec); spec.loader.exec_module(r48)
r46 = r48.r46
WORK = HERE/'work'; TEMP = HERE/'tmp'; LOGS = HERE/'logs'
MiB = 1024**2; GiB = 1024**3

def family(rel):
    p = rel.parts
    if not p: return 'root'
    if p[0] == 'tmp': return 'redirected_temp'
    if p[0] == 'logs': return 'logs'
    if p[:3] == ('work','one','u0'):
        q=p[3:]
        if not q: return 'worker_root'
        if q[0]=='crate': return 'rust_target' if len(q)>1 and q[1]=='target' else 'rust_source'
        if q[0]=='target': return 'rust_target'
        if q[0]=='current.llbc': return 'llbc'
        if q[0]=='generated': return 'aeneas_source'
        if q[0]=='consumer': return 'direct_lean'
        if q[0]=='lake': return 'lake_build' if len(q)>1 and q[1]=='.lake' else 'lake_source'
    return 'other'

def snapshot(detail=False):
    rows={}; totals={}; errors=[]
    stack=[HERE]
    while stack:
        parent=stack.pop()
        try: entries=list(os.scandir(parent))
        except OSError as e: errors.append([str(parent.relative_to(HERE)),e.errno]); continue
        for ent in entries:
            p=Path(ent.path); rel=p.relative_to(HERE)
            if rel.parts[0] in ('probe.py','results.json','check.py'): continue
            try: s=ent.stat(follow_symlinks=False)
            except OSError as e: errors.append([str(rel),e.errno]); continue
            mode=s.st_mode
            if stat.S_ISDIR(mode): stack.append(p); continue
            kind='file' if stat.S_ISREG(mode) else ('symlink' if stat.S_ISLNK(mode) else 'special')
            alloc=s.st_blocks*512
            f=family(rel); t=totals.setdefault(f,{'files':0,'symlinks':0,'logical_bytes':0,'allocated_bytes':0})
            t['files' if kind=='file' else 'symlinks']+=1
            t['logical_bytes']+=s.st_size if kind=='file' else 0; t['allocated_bytes']+=alloc
            if detail: rows[str(rel)]={'kind':kind,'size':s.st_size,'allocated':alloc,'inode':s.st_ino,'device':s.st_dev}
    total={'files':sum(x['files'] for x in totals.values()),'symlinks':sum(x['symlinks'] for x in totals.values()),
           'logical_bytes':sum(x['logical_bytes'] for x in totals.values()),
           'allocated_bytes':sum(x['allocated_bytes'] for x in totals.values())}
    return {'totals':total,'families':totals,'rows':rows if detail else None,'errors':errors}

def outside_state():
    roots={'cargo_home':r46.T/'cargo','rustup_home':r46.T/'rustup','aeneas_backend':r46.BACKEND,'lean_toolchain':r46.LEANROOT}
    out={}
    for name,root in roots.items():
        p=subprocess.run(['/usr/bin/du','-sk',str(root)],capture_output=True,text=True,timeout=30)
        try: kb=int(p.stdout.split()[0])
        except (ValueError,IndexError): kb=None
        s=root.stat()
        out[name]={'root':str(root),'du_kib':kb,'root_mtime_ns':s.st_mtime_ns,'root_ctime_ns':s.st_ctime_ns,'du_exit':p.returncode}
    return out

def main():
    if WORK.exists() or TEMP.exists() or LOGS.exists() or (HERE/'results.json').exists(): raise RuntimeError('fresh scratch required')
    pre_mem=r46.pressure(); pre_disk=shutil.disk_usage(HERE).free
    if pre_mem is None or pre_mem<25 or pre_disk<10*GiB: raise RuntimeError(f'gate memory={pre_mem} disk={pre_disk}')
    prior_tools=PRIOR['tools']; current={n:r48.sha(Path(x['path'])) for n,x in prior_tools.items()}
    if any(current[n]!=x['sha256'] for n,x in prior_tools.items()): raise RuntimeError('pinned tool hash changed')
    # Keep child temporary files in this disposable workspace when tools honor TMPDIR.
    TEMP.mkdir(); os.environ['TMPDIR']=str(TEMP); os.environ['TMP']=str(TEMP); os.environ['TEMP']=str(TEMP)
    os.environ['XDG_CACHE_HOME']=str(TEMP/'xdg-cache')
    r48.WORK=WORK; r48.LOGS=LOGS; r46.WORK=WORK
    raw={'preflight':{'memory_free_percent':pre_mem,'disk_free_bytes':pre_disk},
         'pins':current,'prior_results_sha256':hashlib.sha256((BASE/'results.json').read_bytes()).hexdigest(),
         'observer':'unavailable: previously compiled dylib not retained',
         'outside_before':outside_state(),'boundaries':[],'samples':[]}
    lock=threading.Lock(); stop=threading.Event(); failure=[]
    def boundary(label,phase):
        s=snapshot(detail=True)
        with lock: raw['boundaries'].append({'label':label,'phase':phase,'monotonic_ns':time.monotonic_ns(),**s})
        if s['errors']: failure.append('snapshot error')
    orig_run=r46.Group.run
    def tracked_run(self,label,argv,cwd,env,timeout=40):
        boundary(label,'before')
        try: return orig_run(self,label,argv,cwd,env,timeout)
        finally: boundary(label,'after')
    r46.Group.run=tracked_run
    orig_setup=r48.setup_lake
    def tracked_setup(root):
        boundary('lake-setup','before')
        try:return orig_setup(root)
        finally:boundary('lake-setup','after')
    r48.setup_lake=tracked_setup
    orig_server=r48.server_case
    def tracked_server(root,group,label):
        boundary('live-server','before')
        try:return orig_server(root,group,label)
        finally:boundary('live-server','after')
    r48.server_case=tracked_server
    def sample_loop(group):
        while not stop.wait(.20):
            s=snapshot(False); disk=shutil.disk_usage(HERE).free
            with lock: raw['samples'].append({'monotonic_ns':time.monotonic_ns(),'total':s['totals'],'families':s['families'],'errors':s['errors'],'disk_free_bytes':disk})
            if disk<10*GiB:
                group.abort='disk floor'; failure.append('disk floor')
            if s['errors']: failure.append('sample error')
    WORK.mkdir(); cell=WORK/'one'; cell.mkdir()
    boundary('setup','before')
    units=r46.setup(cell,1)
    boundary('setup','after')
    group=r46.Group('one'); mon_stop=threading.Event()
    monitor=threading.Thread(target=group.monitor,args=(mon_stop,),daemon=True)
    sample=threading.Thread(target=sample_loop,args=(group,),daemon=True)
    monitor.start(); sample.start()
    outcome=None; err=None
    try:
        outcome=r48.workflow(group,units[0])
    except Exception as e: err=repr(e)
    finally:
        stop.set(); sample.join(timeout=5); mon_stop.set(); monitor.join(timeout=8)
        boundary('pre-target-cleanup','after')
        shutil.rmtree(units[0][0]/'target',ignore_errors=True)
        boundary('target-cleanup','after')
    raw['outside_after']=outside_state()
    raw['runtime']={'wall_seconds':round(time.monotonic()-group.start,3),'sample_count':group.samples,
                    'sampled_peak_rss_kib':group.peak['rss_kib'],'minimum_free_percent':group.min_free,
                    'abort':group.abort,'error':err,'snapshot_failures':failure,
                    'cleanup_processes':r46.tree(group.all_roots)['processes']}
    if outcome:
        raw['outcome']={'direct_exit':[q['exit'] for q in outcome['direct']['commands']],
                        'lake_exit':outcome['lake']['exit'],'lake_local_jobs':outcome['lake']['local_jobs'],
                        'fresh_exit':outcome['fresh']['exit'],'live_goal':outcome['server']['goal']['result']['goals'],
                        'live_wait':outcome['server']['wait']['result'],
                        'llbc_sha256':outcome['direct']['hashes']['llbc'],
                        'proof_olean_sha256':outcome['lake']['proof_olean_sha256']}
    (HERE/'results.json').write_text(json.dumps(raw,indent=2)+'\n')
    print(json.dumps({'error':err,'abort':group.abort,'boundaries':len(raw['boundaries']),'samples':len(raw['samples']),
                      'peak_allocated':max([x['totals']['allocated_bytes'] for x in raw['boundaries']]+[x['total']['allocated_bytes'] for x in raw['samples']]),
                      'outside_du_kib_delta':{k:raw['outside_after'][k]['du_kib']-v['du_kib'] for k,v in raw['outside_before'].items()}},indent=2))
    if err or group.abort or failure or not outcome: raise SystemExit(1)
if __name__=='__main__':main()
