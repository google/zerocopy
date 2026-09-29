#!/usr/bin/env python3
"""Validate saved/overlay Charon evidence without running the tools."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'results.json').read_text());c={r['label']:r for r in x['cases']}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def jhash(o):return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()

assert len(c)==10 and len({r['target_dir'] for r in c.values()})==10
for name,h in x['artifact_sha256'].items():assert sha(HERE/'artifacts'/name)==h,name
for name,h in x['graph_sha256'].items():assert sha(HERE/'graphs'/name)==h,name
for r in c.values():
 assert r['exit']==0 and r['llbc_sha256']==x['artifact_sha256'][r['label']+'.llbc']
 assert not r['projection']['has_errors']
 assert r['subject_sha256']==jhash(r['subject_manifest'])
 assert sha(HERE/r['unit_graph_path'])==r['subject_manifest']['unit_graph_sha256']
 g=json.loads((HERE/r['unit_graph_path']).read_text())
 assert r['unit_graph_units']==len(g['units'])
 assert len(r['unit_graph_targets'])==len(g['units'])
 assert '--offline' in r['charon_argv'] and '--locked' in r['charon_argv']
 assert len(r['driver_units'])>=4
assert c['saved']['subject_manifest']['source_files_sha256']==c['overlay-clean']['subject_manifest']['source_files_sha256']
assert c['saved']['subject_sha256']==c['overlay-clean']['subject_sha256']
assert c['saved']['projection']['body_sha256']==c['overlay-clean']['projection']['body_sha256']
assert c['saved']['llbc_sha256']!=c['overlay-clean']['llbc_sha256']
assert c['saved']['unit_graph_units']==5 and c['overlay-wrong-unit']['unit_graph_units']==6
assert {'app_closure','dep_path','proc_local','build_script_build'}.issubset(set(c['saved']['driver_units']))
assert c['overlay-build-env']['generated_rs']!=c['saved']['generated_rs']
assert c['overlay-build-source']['generated_rs']!=c['saved']['generated_rs']
assert c['overlay-proc-env']['projection']['body_sha256']['app_closure::macro_generated']!=c['saved']['projection']['body_sha256']['app_closure::macro_generated']
assert c['overlay-include']['projection']['body_sha256']['app_closure::root']!=c['saved']['projection']['body_sha256']['app_closure::root']
assert c['overlay-rustc-env']['projection']['body_sha256']['app_closure::root']!=c['saved']['projection']['body_sha256']['app_closure::root']
assert c['overlay-pathdep']['subject_sha256']!=c['saved']['subject_sha256']
assert c['overlay-pathdep']['projection']['body_sha256']['app_closure::root']==c['saved']['projection']['body_sha256']['app_closure::root']
assert 'core::num::wrapping_mul' in c['overlay-proc-source']['projection']['function_names']
assert c['overlay-wrong-unit']['projection']['crate_name']=='app_closure_cli'
assert x['controls']=={'stale_changed_overlay':'stale or foreign subject manifest',
 'opaque_pathdep_stale':'stale or foreign subject manifest',
 'wrong_unit':'wrong compilation unit: app_closure_cli'}
print('PASS: 10 private Cargo/Charon units, saved/overlay equivalence, input closure and rejection controls')
