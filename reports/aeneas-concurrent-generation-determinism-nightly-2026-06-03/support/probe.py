#!/usr/bin/env python3
"""Concurrent Aeneas process comparison on a fixed split Lean output."""
import concurrent.futures,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
FIXTURE=ROOT/'fixture'/'probe.llbc'
AENEAS=Path(os.environ['AENEAS_BIN']).resolve()
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
EXPECTED_BINARY='f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03'
EXPECTED_INPUT='b98023ca3d222796ed4f08e9331e8ffa750c8971daeb786fea37a888b8c8d098'
EXPECTED_FILES={'Funs.lean','Probe.lean','Types.lean'}
def sha(b): return hashlib.sha256(b).hexdigest()
def inventory(d):
 return {p.relative_to(d).as_posix():{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(d.rglob('*')) if p.is_file()}
def run(dest,label,barrier=None):
 if barrier: barrier.wait()
 start=time.monotonic_ns()
 p=subprocess.Popen([str(AENEAS),*FLAGS,'-dest',str(dest),str(FIXTURE)],cwd=ROOT.parents[3],env=dict(os.environ,LC_ALL='C',TZ='UTC'),stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
 spawned=time.monotonic_ns()
 spawned_alive=p.poll() is None
 try:
  stdout,stderr=p.communicate(timeout=30)
 except subprocess.TimeoutExpired:
  p.kill()
  p.communicate()
  raise
 end=time.monotonic_ns()
 return {'label':label,'destination':dest.name,'argv_flags':FLAGS,'started_ns':start,'spawned_ns':spawned,'spawned_alive':spawned_alive,'pid':p.pid,'ended_ns':end,'elapsed_ms':round((end-start)/1e6,3),'returncode':p.returncode,'stdout':stdout,'stderr':stderr,'inventory':inventory(dest) if dest.exists() else {}}
try:
 assert sha(AENEAS.read_bytes())==EXPECTED_BINARY
 assert sha(FIXTURE.read_bytes())==EXPECTED_INPUT
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
 result={'aeneas_sha256':sha(AENEAS.read_bytes()),'input_sha256':sha(FIXTURE.read_bytes()),'input_bytes':FIXTURE.stat().st_size,'cwd':'parent of reference-publish checkout (resolved from report fixture)','processes':{'independent_destination':independent,'same_writable_destination':same},'summary':{'independent_all_exit_0':success_independent,'independent_outputs_identical':identical_independent,'independent_inventory':all_independent[0] if all_independent else {},'shared_all_exit_0':success_shared,'shared_final_inventory':inventory(shared),'shared_process_inventories_identical':all(x==same_dest_inventories[0] for x in same_dest_inventories[1:]),'shared_outputs_complete':set(inventory(shared))==EXPECTED_FILES and all(v['bytes']>0 for v in inventory(shared).values()),'shared_final_matches_independent':inventory(shared)==all_independent[0],'independent_runs_overlapped':all(r['spawned_alive'] for r in independent) and max(r['spawned_ns'] for r in independent)<min(r['ended_ns'] for r in independent),'shared_runs_overlapped':all(r['spawned_alive'] for r in same) and max(r['spawned_ns'] for r in same)<min(r['ended_ns'] for r in same)}}
 assert set(all_independent[0])==EXPECTED_FILES and all(v['bytes']>0 for v in all_independent[0].values())
 assert all((success_independent,identical_independent,success_shared,result['summary']['shared_outputs_complete'],result['summary']['shared_final_matches_independent'],result['summary']['independent_runs_overlapped'],result['summary']['shared_runs_overlapped']))
 raw=json.dumps(result,indent=2)+'\n'
 raw=raw.replace(str(ROOT),'$REPORT_SUPPORT').replace(str(AENEAS),'$AENEAS_BIN')
 (ROOT/'concurrency-transcript.json').write_text(raw)
 print(json.dumps({'aeneas_sha256':result['aeneas_sha256'],'input_sha256':result['input_sha256'],'summary':result['summary']},indent=2))
except Exception as e:
 (ROOT/'concurrency-transcript.json').write_text(json.dumps({'error':repr(e)},indent=2)+'\n')
 raise
