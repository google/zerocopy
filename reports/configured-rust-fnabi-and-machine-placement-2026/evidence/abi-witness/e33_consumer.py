"""Caller-fixed ABI capture consumer. Implementation only: check mode NOT RUN.
There is no producer-selectable reference/request/flags/tool hash argument.
preflight performs data/hash reads only; check would launch exactly one selected
reviewed observer after parent authorization, generate a fresh reference, compare
all candidate fields, and retain status separately from semantic rejection.
"""
from pathlib import Path
import argparse,json,sys
import e33_data as D
import build_control_v2 as C
ROOT=Path(__file__).resolve().parent
class Operational(RuntimeError):pass
def file_sha(p):return C.h(Path(p))
def preflight(toolchain,profile):
 request=D.load_request(ROOT,profile);toolchain=Path(toolchain).resolve()
 ids=D.parse(D.read(ROOT/'source-identities.json'))
 for x in ids['readonly_tools']:
  p=toolchain/x['toolchain_relative_path'];D.require(p.is_file() and not p.is_symlink() and p.stat().st_size==x['bytes'] and file_sha(p)==x['sha256'],'readonly tool identity')
 # This compiled observer's approved LC_RPATH is relative to its own directory.
 # Hash the actual resolved driver independently from the --sysroot selection.
 actual=ROOT.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib/librustc_driver-16d1e96e5b674978.dylib'
 D.require(actual.is_file() and not actual.is_symlink() and file_sha(actual)=='dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d','actual observer-resolved driver identity')
 return request,toolchain

def capture_fixed(toolchain,profile,run_path):
 request,toolchain=preflight(toolchain,profile)
 run_path=Path(run_path)
 D.require(run_path.is_absolute() and run_path.parent.resolve().is_relative_to(ROOT) and not run_path.exists(),'fresh owned run directory')
 p=request['profile'];source=ROOT/p['source']['path'];output=run_path/'reference.json'
 args=[str(ROOT/'observer-v2'),str(ROOT/p['selectors']['path']),str(output),'--',str(source),'--sysroot',str(toolchain),'--edition=2021','--crate-type=lib','--crate-name='+p['crate_name'],'--target='+p['target'],'-Copt-level='+str(p['optimization']),'-Cpanic=abort','-Ctarget-cpu='+p['target_cpu'],'-Zthreads=1','-Ccodegen-units=1','--emit=metadata','--out-dir',str(run_path)]
 env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','TMPDIR':str(run_path/'tmp'),'LC_ALL':'C','LANG':'C'}
 result=C.run_owned(run_path,args,env,C.ScopedMonitor(),seconds=60)
 (run_path/'effective-request.json').write_text(json.dumps(request['effective_request'],indent=2)+'\n')
 # All monitor/runtime/query failures stop this path; never call these semantic
 # mismatch or expected candidate rejection. In particular status65 is not success.
 # Re-read current locked inputs/tools after actual observation, preserving all
 # hashes. This is an operational boundary check, not a filesystem-race theorem.
 try:again,_=preflight(toolchain,profile)
 except D.Reject as e:raise Operational('input/runtime identity failed after capture') from e
 if again['effective_request_sha256']!=request['effective_request_sha256']:raise Operational('caller input changed during capture')
 if result['controller_failure'] or result['stop_reason'] or result['exit_code']!=0:
  raise Operational('fresh observation failed; inspect exact retained status/streams')
 if not output.is_file():raise Operational('observer exited without full fresh reference')
 try:reference=D.read(output);D.validate_observation(D.parse(reference),request)
 except D.Reject as e:raise Operational('independent observer output outside reviewed grammar; stop before acceptance') from e
 return request,reference

def check(toolchain,profile,candidate_path,run_path):
 # Candidate syntax/root/source/config grammar is checked before invoking compiler.
 request,_=preflight(toolchain,profile);candidate=D.read(candidate_path);D.validate_observation(D.parse(candidate),request)
 fresh,reference=capture_fixed(toolchain,profile,run_path)
 if fresh['effective_request_sha256']!=request['effective_request_sha256']:raise Operational('request changed before fresh observation')
 run_path=Path(run_path)
 try:receipt=D.compare_data(candidate,reference,request)
 except D.Reject as e:
  (run_path/'comparison.json').write_text(json.dumps({'status':'rejected_data','reason':str(e),'effective_request_sha256':request['effective_request_sha256']},indent=2)+'\n');raise
 receipt['status']='accepted_against_fresh_pinned_compiler_observation'
 receipt['scope']='Trusted compiler/observer ABI witness equality for this selected source/target/profile/instance. No verified classification, full dependency closure, source safety, IR/machine placement or correspondence theorem.'
 (run_path/'comparison.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt

def main():
 parser=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
 parser.add_argument('mode',choices=['preflight','capture','check']);parser.add_argument('--toolchain',required=True);parser.add_argument('--profile',required=True,choices=['host-subjects-opt0','host-subjects-opt2','host-vectors-opt0','host-vectors-opt2']);parser.add_argument('--candidate');parser.add_argument('--run-dir')
 a=parser.parse_args()
 try:
  if a.mode=='preflight':
   D.require(a.candidate is None and a.run_dir is None,'preflight accepts no candidate/run path');r,_=preflight(a.toolchain,a.profile);value={'status':'preflight_only','effective_request_sha256':r['effective_request_sha256'],'observer_invocations':0}
  elif a.mode=='capture':
   D.require(a.candidate is None and a.run_dir is not None,'capture takes no producer candidate');r,reference=capture_fixed(a.toolchain,a.profile,a.run_dir);value={'status':'captured_consumer_reference','effective_request_sha256':r['effective_request_sha256'],'reference_sha256':D.sha(reference),'accepted_candidates':0}
  else:
   D.require(a.candidate is not None and a.run_dir is not None,'candidate and fresh run-dir required');value=check(a.toolchain,a.profile,a.candidate,a.run_dir)
  print(json.dumps(value,indent=2));return 0
 except D.Reject as e:print(json.dumps({'status':'rejected_data','reason':str(e)}));return 64
 except Operational as e:print(json.dumps({'status':'operational_stop','reason':str(e)}));return 70
if __name__=='__main__':raise SystemExit(main())
