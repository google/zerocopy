#!/usr/bin/env python3
"""Run one probe in a bounded process group; append resource/outcome evidence."""
import argparse, ctypes, json, os, re, shutil, signal, subprocess, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LIB = ctypes.CDLL(None, use_errno=True)
def host_sample():
    p = subprocess.run(['/usr/bin/memory_pressure', '-Q'], capture_output=True, text=True)
    m = re.search(r'System-wide memory free percentage:\s*(\d+)%', p.stdout)
    v = subprocess.run(['/usr/bin/vm_stat'], capture_output=True, text=True).stdout
    values = {k: int(n) for k,n in re.findall(r'^([^:]+):\s+(\d+)\.', v, re.M)}
    return {'memory_free_pct': int(m[1]) if m else None,
            'disk_free_bytes': shutil.disk_usage(ROOT).free,
            'compressor_pages': values.get('Pages occupied by compressor'),
            'swapouts': values.get('Swapouts'), 'swapins': values.get('Swapins')}
def processes(root_pid):
    # The harness denies executing ps. Query only this probe's known PID and
    # its descendants via the standard macOS process resource API instead.
    rows=[]; pending=[root_pid]; seen=set()
    while pending:
        pid=pending.pop()
        if pid in seen:continue
        seen.add(pid)
        if len(seen)>512:raise RuntimeError('Unexpected probe process fan-out')
        data=(ctypes.c_uint64*64)()
        result=LIB.proc_pid_rusage(pid,0,ctypes.byref(data))
        if result==0:
            rows.append({'pid':pid,'rss_kib':int(data[8])//1024,'footprint_kib':int(data[9])//1024,'user_ns':int(data[2]),'system_ns':int(data[3])})
        elif ctypes.get_errno() not in (3,22):
            raise RuntimeError(f'Probe resource query failed: pid={pid}, errno={ctypes.get_errno()}')
        children=(ctypes.c_int*512)()
        count=LIB.proc_listchildpids(pid,ctypes.byref(children),ctypes.sizeof(children))
        if count>0:pending.extend(int(p) for p in list(children)[:count] if p>0)
    return rows
def run(label,cmd,cwd=None,env=None,timeout=90,rss_mib=1536,admission_memory_pct=25,memory_floor_pct=20):
    sample=host_sample()
    if sample['memory_free_pct'] is None or sample['memory_free_pct']<admission_memory_pct or sample['disk_free_bytes']<10*1024**3:
        raise RuntimeError(f'Admission refused: {sample}')
    records=ROOT/'records'; records.mkdir(exist_ok=True)
    stdout=records/(label+'.stdout'); stderr=records/(label+'.stderr')
    record={'label':label,'cmd':list(cmd),'cwd':str(cwd) if cwd else None,'limits':{'timeout_s':timeout,'rss_mib':rss_mib,'disk_floor_gib':10,'memory_floor_pct':memory_floor_pct,'admission_memory_pct':admission_memory_pct},'samples':[],'abort':None}
    start=time.monotonic()
    with stdout.open('wb') as out,stderr.open('wb') as err:
        child=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=out,stderr=err,start_new_session=True)
        record['pid']=child.pid
        (records/(label+'.pid')).write_text(str(child.pid))
        next_host=0
        while True:
            elapsed=time.monotonic()-start
            rows=processes(child.pid)
            if elapsed>=next_host:
                sample=host_sample();next_host=elapsed+1
            row={'elapsed_s':round(elapsed,3),'rss_kib':sum(r['rss_kib'] for r in rows),'processes':rows,**sample}
            record['samples'].append(row)
            reason=None
            if elapsed>timeout:reason='timeout'
            if row['rss_kib']>rss_mib*1024:reason='process-group RSS'
            if row['disk_free_bytes']<10*1024**3:reason='disk floor'
            if row['memory_free_pct'] is None or row['memory_free_pct']<memory_floor_pct:reason='host memory pressure'
            if reason:
                record['abort']=reason
                try:os.killpg(child.pid,signal.SIGTERM)
                except ProcessLookupError:pass
                try:child.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid,signal.SIGKILL);child.wait()
                break
            if child.poll() is not None:break
            time.sleep(.2)
        record['exit']=child.wait();record['elapsed_s']=round(time.monotonic()-start,3)
        # Terminate descendants that survived their root process.
        remaining=processes(child.pid)
        if remaining:
            record['surviving_processes']=remaining
            try:os.killpg(child.pid,signal.SIGTERM)
            except ProcessLookupError:pass
    record['stdout']=str(stdout);record['stderr']=str(stderr)
    record['final_host']=host_sample()
    with (ROOT/'runs.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
    print(json.dumps({'label':label,'exit':record['exit'],'abort':record['abort'],'elapsed_s':record['elapsed_s'],'peak_sampled_rss_mib':round(max(s['rss_kib'] for s in record['samples'])/1024,1),'min_memory_free_pct':min(s['memory_free_pct'] for s in record['samples']),'min_disk_free_gib':round(min(s['disk_free_bytes'] for s in record['samples'])/1024**3,2)}),flush=True)
    return record
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--label',required=True);parser.add_argument('--cwd');parser.add_argument('--timeout',type=int,default=90);parser.add_argument('--rss-mib',type=int,default=1536);parser.add_argument('cmd',nargs=argparse.REMAINDER)
    a=parser.parse_args();cmd=a.cmd[1:] if a.cmd[:1]==['--'] else a.cmd
    r=run(a.label,cmd,a.cwd,timeout=a.timeout,rss_mib=a.rss_mib)
    raise SystemExit(r['exit'] if not r['abort'] else 124)
