#!/usr/bin/env python3
"""Pinned Cargo/Charon saved subject versus private materialized overlay."""
import argparse,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent;FIX=HERE/'fixture';OUT=HERE/'results.json';ART=HERE/'artifacts';GRAPHS=HERE/'graphs'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
BIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LIB=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
CHARON=TOOLS/'bin/charon'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def jhash(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def tree(p):return {str(f.relative_to(p)):sha(f) for f in sorted(p.rglob('*')) if f.is_file()}
def projection(p):
 doc=json.loads(p.read_text());tr=doc['translated'];bodies={};names=[]
 for f in tr.get('fun_decls',[]):
  if not f:continue
  name='::'.join(part['Ident'][0] for part in f['item_meta']['name'] if 'Ident' in part)
  names.append(name);bodies[name]=jhash(f.get('body'))
 return {'crate_name':tr['crate_name'],'has_errors':doc['has_errors'],'body_sha256':bodies,'function_names':names,
         'files':[f['name'] for f in tr.get('files',[])]}
def norm(s,work):return s.replace(str(work),'$WORK').replace(str(TOOLS),'$TOOLS')
def reject(record,expected_key,expected_crate):
 if record['subject_sha256']!=expected_key:raise ValueError('stale or foreign subject manifest')
 if record['projection']['crate_name']!=expected_crate:raise ValueError('wrong compilation unit: '+record['projection']['crate_name'])

def run_case(work,index,label,edit=None,extra=None,unit='lib'):
 src=work/f'overl-{index:02d}' if index else work/'saved-00'
 shutil.copytree(FIX,src)
 if edit:
  rel,old,new=edit;p=src/rel;before=p.read_text();assert old in before;p.write_text(before.replace(old,new))
 target=work/f'target-{index:02d}';dest=ART/f'{label}.llbc'
 inputs={'BUILD_VALUE':'7','PROC_VALUE':'3','PROBE_ENV':'A'};inputs.update(extra or {})
 env=dict(os.environ);env.update(inputs);env.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
  'CARGO_TARGET_DIR':str(target),'CARGO_BUILD_JOBS':'1','CARGO_INCREMENTAL':'0','RAYON_NUM_THREADS':'1',
  'CHARON_TOOLCHAIN_IS_IN_PATH':'1','PATH':os.pathsep.join([str(BIN),str(TOOLS/'bin'),env.get('PATH','')]),
  'DYLD_LIBRARY_PATH':os.pathsep.join([str(LIB),str(LIB/'rustlib/aarch64-apple-darwin/lib')])})
 cargo_flags=(['--manifest-path',str(src/'Cargo.toml'),'--package','app_closure']
  + (['--lib'] if unit=='lib' else ['--bin','app_closure_cli']) + ['--offline','--locked'])
 graph_cmd=[str(BIN/'cargo'),'build','-Z','unstable-options','--unit-graph']+cargo_flags
 gp=subprocess.run(graph_cmd,cwd=src,env=env,capture_output=True,text=True,timeout=30)
 assert gp.returncode==0,(label,gp.stderr)
 graph=json.loads(gp.stdout)
 graph_text=json.dumps(graph,indent=2,sort_keys=True).replace(str(src),'$SOURCE')+'\n'
 (GRAPHS/f'{label}.json').write_text(graph_text)
 manifest={'source_files_sha256':tree(src),'environment_inputs':inputs,
           'unit_graph_sha256':hashlib.sha256(graph_text.encode()).hexdigest(),
           'requested_package':'app_closure','requested_unit':unit,
           'tool_sha256':{'charon':sha(CHARON),'cargo':sha(BIN/'cargo'),'rustc':sha(BIN/'rustc')}}
 subject=jhash(manifest)
 cmd=[str(CHARON),'cargo','--preset','aeneas','--dest-file',str(dest),'--']+cargo_flags+['-v']
 start=time.monotonic();p=subprocess.run(cmd,cwd=src,env=env,capture_output=True,text=True,timeout=60)
 generated=[f.read_text() for f in target.rglob('generated.rs')]
 record={'label':label,'source_dir':src.name,'target_dir':target.name,'subject_manifest':manifest,'subject_sha256':subject,
         'unit_graph_path':f'graphs/{label}.json','unit_graph_units':len(graph['units']),
         'unit_graph_targets':[{'name':u['target']['name'],'kind':u['target']['kind'],'mode':u['mode'],
           'platform':u.get('platform'),'dependencies':u['dependencies']} for u in graph['units']],
         'cargo_unit_graph_argv':[norm(a,work) for a in graph_cmd],
         'charon_argv':[norm(a,work) for a in cmd],
         'seconds':round(time.monotonic()-start,3),'exit':p.returncode,
         'stdout':norm(p.stdout,work),'stderr':norm(p.stderr,work),
         'driver_units':re.findall(r'Running `[^\n]*charon-driver rustc --crate-name ([^ ]+)',p.stderr),
         'generated_rs':generated,'llbc_sha256':sha(dest) if dest.exists() else None,
         'projection':projection(dest) if dest.exists() else None}
 assert p.returncode==0 and record['projection'] and not record['projection']['has_errors'],label
 return record

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
 assert not work.exists();assert shutil.disk_usage(work.parent).free>=15*(1<<30)
 work.mkdir();ART.mkdir(exist_ok=True);GRAPHS.mkdir(exist_ok=True)
 for p in ART.glob('*.llbc'):p.unlink()
 for p in GRAPHS.glob('*.json'):p.unlink()
 cases=[
  run_case(work,0,'saved'),
  run_case(work,1,'overlay-clean'),
  run_case(work,2,'overlay-build-env',extra={'BUILD_VALUE':'8'}),
  run_case(work,3,'overlay-proc-env',extra={'PROC_VALUE':'4'}),
  run_case(work,4,'overlay-include',edit=('app/src/payload.txt','payload-A','payload-AB')),
  run_case(work,5,'overlay-pathdep',edit=('dep_path/src/lib.rs','wrapping_add(11)','wrapping_add(12)')),
  run_case(work,6,'overlay-proc-source',edit=('proc_local/src/lib.rs','x.wrapping_add({delta})','x.wrapping_mul({delta})')),
  run_case(work,7,'overlay-build-source',edit=('app/build.rs','{value} + {path_len}','{value} * 2 + {path_len}')),
  run_case(work,8,'overlay-rustc-env',extra={'PROBE_ENV':'AA'}),
  run_case(work,9,'overlay-wrong-unit',unit='bin'),
 ]
 saved=cases[0];clean=cases[1]
 assert saved['subject_manifest']['source_files_sha256']==clean['subject_manifest']['source_files_sha256']
 assert saved['projection']['body_sha256']==clean['projection']['body_sha256']
 assert {'build_script_build','proc_local','dep_path','app_closure'}.issubset(set(saved['driver_units']))
 assert saved['projection']['crate_name']=='app_closure'
 assert cases[-1]['projection']['crate_name']=='app_closure_cli'
 assert cases[2]['generated_rs']!=saved['generated_rs']
 assert cases[3]['projection']['body_sha256']['app_closure::macro_generated']!=saved['projection']['body_sha256']['app_closure::macro_generated']
 assert cases[4]['projection']['body_sha256']['app_closure::root']!=saved['projection']['body_sha256']['app_closure::root']
 assert cases[5]['projection']['body_sha256']['app_closure::root']==saved['projection']['body_sha256']['app_closure::root']
 assert cases[5]['subject_sha256']!=saved['subject_sha256']
 assert 'core::num::wrapping_mul' in cases[6]['projection']['function_names']
 assert cases[7]['generated_rs']!=saved['generated_rs']
 assert cases[8]['projection']['body_sha256']['app_closure::root']!=saved['projection']['body_sha256']['app_closure::root']
 controls={}
 for label,record,key,crate in [('stale_changed_overlay',cases[4],saved['subject_sha256'],'app_closure'),
                                 ('opaque_pathdep_stale',cases[5],saved['subject_sha256'],'app_closure'),
                                 ('wrong_unit',cases[9],cases[9]['subject_sha256'],'app_closure')]:
  try:reject(record,key,crate)
  except ValueError as e:controls[label]=str(e)
  else:raise AssertionError(label)
 result={'tool_sha256':saved['subject_manifest']['tool_sha256'],'cases':cases,'controls':controls,
  'artifact_sha256':{p.name:sha(p) for p in sorted(ART.glob('*.llbc'))},
  'graph_sha256':{p.name:sha(p) for p in sorted(GRAPHS.glob('*.json'))}}
 OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'cases':len(cases),'unit_graph_units':{c['label']:c['unit_graph_units'] for c in cases},
  'controls':controls,'saved_vs_clean_projection_equal':saved['projection']['body_sha256']==clean['projection']['body_sha256']},indent=2))
if __name__=='__main__':main()
