#!/usr/bin/env python3
"""Concurrent Aeneas process comparison on a fixed split Lean output."""
import concurrent.futures,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FIXTURE=ROOT/'fixture'/'probe.llbc'
AENEAS=Path(os.environ['AENEAS_BIN']).resolve()
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(d):
 return {p.relative_to(d).as_posix():{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(d.rglob('*')) if p.is_file()}
def run(dest,label,barrier=None):
 if barrier: barrier.wait()
 start=time.monotonic_ns()
 p=subprocess.run([str(AENEAS),*FLAGS,'-dest',str(dest),str(FIXTURE)],cwd=ROOT.parent.parent.parent.parent,env=dict(os.environ,LC_ALL='C',TZ='UTC'),capture_output=True,text=True,timeout=30)
 end=time.monotonic_ns()
 return {'label':label,'destination':dest.name,'argv_flags':FLAGS,'started_ns':start,'ended_ns':end,'elapsed_ms':round((end-start)/1e6,3),'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'inventory':inventory(dest) if dest.exists() else {}}
try:
 parallel_root=ROOT/'parallel-independent'; shutil.rmtree(parallel_root,ignore_errors=True); parallel_root.mkdir()
 barrier=__import__('threading').Barrier(4)
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
  independent=list(pool.map(lambda i:run(parallel_root/f'worker-{i}',f'worker-{i}',barrier),range(4)))
 shared=ROOT/'parallel-shared-dest'; shutil.rmtree(shared,ignore_errors=True); shared.mkdir()
 barrier=__import__('threading').Barrier(3)
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
  same=list(pool.map(lambda i:run(shared,f'shared-{i}',barrier),range(3)))
 all_independent=[r['inventory'] for r in independent]
 success_independent=all(r['returncode']==0 for r in independent)
 identical_independent=success_independent and all(x==all_independent[0] for x in all_independent[1:])
 success_shared=all(r['returncode']==0 for r in same)
 same_dest_inventories=[r['inventory'] for r in same]
 result={'aeneas_sha256':sha(AENEAS.read_bytes()),'input_sha256':sha(FIXTURE.read_bytes()),'input_bytes':FIXTURE.stat().st_size,'cwd':'repository root (recorded relative to report fixture)','processes':{'independent_destination':independent,'same_writable_destination':same},'summary':{'independent_all_exit_0':success_independent,'independent_outputs_identical':identical_independent,'independent_inventory':all_independent[0] if all_independent else {},'shared_all_exit_0':success_shared,'shared_final_inventory':inventory(shared),'shared_process_inventories_identical':all(x==same_dest_inventories[0] for x in same_dest_inventories[1:]),'shared_outputs_complete':bool(inventory(shared)) and all(v['bytes']>0 for v in inventory(shared).values()),'independent_runs_overlapped':max(r['started_ns'] for r in independent)<min(r['ended_ns'] for r in independent),'shared_runs_overlapped':max(r['started_ns'] for r in same)<min(r['ended_ns'] for r in same)}}
 assert success_independent and identical_independent and success_shared and result['summary']['shared_outputs_complete']
 raw=json.dumps(result,indent=2)+'\n'
 raw=raw.replace(str(ROOT),'$REPORT_SUPPORT').replace(str(AENEAS),'$AENEAS_BIN')
 (ROOT/'concurrency-transcript.json').write_text(raw)
 print(json.dumps({'aeneas_sha256':result['aeneas_sha256'],'input_sha256':result['input_sha256'],'summary':result['summary']},indent=2))
except Exception as e:
 (ROOT/'concurrency-transcript.json').write_text(json.dumps({'error':repr(e)},indent=2)+'\n')
 raise
