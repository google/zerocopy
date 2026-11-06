"""Execute one of exactly four reviewed host compile-only commands. No link/run."""
from pathlib import Path
import hashlib, importlib.util, json, os, sys
S=Path(__file__).resolve().parent
B=S.parent
T=B.parent/'toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin'
PLAN_SHA='b805597d4b38d3022bffbc17d4b322a241bcfb785ec9bf8ed916daebf92763dc'
STAGE4_SHA='ec647915a8430be9c262630fd88bffc6fe4ce19c8a71c86d26648f47d8e1c97d'
CONTROLLER_SHA='22714dad1a3cae8913c4cf4a334934f6a8901097e8df975f1bc23c74f8d62bed'
VECTOR_STDERR='79b0bff29ae803e776d901c83d6f577c970498f5566aab0445bec062e126c3ec'
EMPTY='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,z):
 with p.open('x') as f:json.dump(z,f,indent=2);f.write('\n')
def verify_inputs():
 assert B.resolve()==B and S.resolve()==S
 assert h(B/'stage4-manifest.json')==STAGE4_SHA
 for f in json.loads((B/'stage4-manifest.json').read_text())['files']:
  p=B/f['path'];assert p.stat().st_size==f['bytes'] and h(p)==f['sha256'],f['path']
 assert h(B/'stage4/CODEGEN-WINDOWS-PLAN.json')==PLAN_SHA
 assert h(B/'build_control_v3.py')==CONTROLLER_SHA
 rows=[]
 for f in json.loads((B/'source-identities.json').read_text())['readonly_tools']:
  p=T/f['toolchain_relative_path'];assert p.stat().st_size==f['bytes'] and h(p)==f['sha256'],str(p)
  rows.append({'path':str(p),'sha256':h(p),'bytes':p.stat().st_size})
 for f in json.loads((S/'tools/identities-before.json').read_text())['reader_tools']:
  p=Path(f['selected_path']);assert str(p.resolve())==f['resolved_path']
  assert p.stat().st_size==f['bytes'] and h(p)==f['sha256_before_after'],str(p)
  rows.append({'path':str(p),'resolved_path':str(p.resolve()),'sha256':h(p),'bytes':p.stat().st_size})
 backend=json.loads((S/'tools/identities-before.json').read_text())['backend']
 p=Path(backend['enclosing_native_image']);assert p.stat().st_size==backend['bytes'] and h(p)==backend['sha256']
 return rows

def main():
 if len(sys.argv)!=2:raise SystemExit('one exact approved host profile required')
 profile=sys.argv[1]
 plan=json.loads((B/'stage4/CODEGEN-WINDOWS-PLAN.json').read_text())
 matches=[x for x in plan['host_commands'] if x['profile']==profile]
 assert len(matches)==1,'profile outside approved four'
 before=verify_inputs()
 R=S/'codegen'/profile
 assert not R.exists()
 (S/'codegen').mkdir(exist_ok=True)
 variables={'${PINNED_MAY1_TOOLCHAIN}':str(T),'${E33_ROOT}':str(B),'${FRESH_CODEGEN_ROOT}':str(S/'codegen')}
 argv=[]
 for a in matches[0]['argv']:
  for k,v in variables.items():a=a.replace(k,v)
  assert '${' not in a
  argv.append(a)
 assert argv[-1]==str(R) and '--emit=llvm-ir,asm,obj' in argv
 assert h(Path(argv[1]))==matches[0]['source_sha256']
 assert sum(p.stat().st_size for p in S.rglob('*') if p.is_file())<268435456
 spec=importlib.util.spec_from_file_location('reviewed_controller',B/'build_control_v3.py')
 c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
 env={'PATH':'/usr/bin:/bin:/usr/sbin:/sbin','TMPDIR':str(R/'tmp'),'LC_ALL':'C','LANG':'C'}
 result=c.run_owned(R,argv,env,c.ScopedMonitor(),seconds=600)
 after=verify_inputs()
 result['readonly_bindings_before']=before;result['readonly_bindings_after']=after
 result['source_sha256']=h(Path(argv[1]));result['plan_sha256']=PLAN_SHA
 result['host_codegen_harness_sha256']=h(Path(__file__))
 result['profile']=profile
 result['additional_stage5_bytes']=sum(p.stat().st_size for p in S.rglob('*') if p.is_file())
 expected=VECTOR_STDERR if 'vectors' in profile else EMPTY
 result['expected_stderr_sha256']=expected
 result['classified_warning_scope']='Exact five experimental SIMD warnings retained; not FFI safety' if 'vectors' in profile else 'No diagnostics expected'
 good=(result['exit_code']==0 and result['controller_failure'] is None and result['stop_reason'] is None and not result['remaining_group_after_parent_wait'] and result['stdout_sha256']==EMPTY and result['stderr_sha256']==expected and result['additional_stage5_bytes']<268435456)
 outputs=[]
 for suffix in ['ll','s','o']:
  ps=list(R.glob('*.'+suffix));good=good and len(ps)==1
  outputs.extend({'path':str(p.relative_to(S)),'bytes':p.stat().st_size,'sha256':h(p)} for p in ps)
 result['outputs']=outputs;result['gates']='PASS' if good else 'STOP'
 result['fixture_link_or_execution_count']=0
 save(R/'reviewed-result.json',result)
 print(json.dumps(result,indent=2))
 if not good:raise SystemExit(70)
if __name__=='__main__':main()
