#!/usr/bin/env python3
"""Offline validation of retained R15 data and copied artifact bytes."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
R=json.loads((HERE/'results.json').read_text());C=R['cases']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert len(R['commands'])==39 and len(C)==11
assert R['environment']['max_concurrent_commands']==1
assert R['environment']['free_percent_preflight']>=35
for name,info in R['retained_inventory'].items():
 p=HERE/'artifacts'/name
 assert p.is_file() and p.stat().st_size==info['bytes'] and sha(p)==info['sha256'],name
base=C['base'];path=C['path-copy'];nine=C['source-nine'];extra=C['source-extra'];option=C['option'];manifest=C['manifest']
keys=lambda x:set(x['cache_maps'])
assert keys(base)==keys(path) and len(keys(base))==1
assert len(keys(nine)-keys(path))==1 and len(keys(extra)-keys(nine))==1
assert len(keys(option)-keys(extra))==1 and keys(manifest)==keys(option)
assert base['source_sha256']==path['source_sha256']==option['source_sha256']==manifest['source_sha256']
assert nine['source_sha256']!=base['source_sha256'] and extra['source_sha256']!=base['source_sha256']
assert base['producer_config_sha256']!=option['producer_config_sha256']
assert base['consumer_manifest_sha256']!=manifest['consumer_manifest_sha256']
assert base['artifacts']['olean']['sha256']==option['artifacts']['olean']['sha256']
assert base['artifacts']['c']['sha256']==option['artifacts']['c']['sha256']
assert base['artifacts']['setup']['sha256']!=option['artifacts']['setup']['sha256']
assert base['artifacts']['ilean']['sha256']==nine['artifacts']['ilean']['sha256']
assert base['artifacts']['ilean']['sha256']!=extra['artifacts']['ilean']['sha256']
assert base['artifacts']['olean']['sha256']!=nine['artifacts']['olean']['sha256']
assert base['artifacts']['c']['sha256']!=nine['artifacts']['c']['sha256']
assert base['batch']==option['batch']==extra['batch']==0
assert path['batch']==manifest['batch']==nine['batch']==1
assert path['artifacts']['olean'] is None and manifest['artifacts']['olean'] is None
for family in ('olean','ilean','c','setup'):
 x=C['mixed-'+family]
 assert x['before_artifact_sha256']==x['after_artifact_sha256']
 assert x['before_artifact_sha256'][family]!=base['artifacts'][family]['sha256']
 assert x['no_build_exit']==x['setup_exit']==x['setup_import_batch_exit']==0
 assert x['setup_import_olean_sha256']==base['artifacts']['olean']['sha256']
 assert sha(HERE/'artifacts'/'retained'/('mixed-'+family)/('Dep.'+family))==x['before_artifact_sha256'][family]
 if family=='olean':
  assert x['batch_exit']==1
  diags=[d.get('message','') for row in x['server']['diagnostics'] for d in row.get('diagnostics',[])]
  assert any('is false' in d for d in diags) and '10' in diags
 else:
  assert x['batch_exit']==0
  if x['server']:
   diags=[d.get('message','') for row in x['server']['diagnostics'] for d in row.get('diagnostics',[])]
   assert not any('is false' in d for d in diags) and '8' in diags
for version in ('v1','v2'):
 p=C['plugin']['fresh_batch'][version]
 assert p['exit']==0 and p['marker']=='plugin-'+version
 assert p['dylib_sha256']==sha(HERE/'artifacts'/version/'plugin__probe_Plugin.dylib')
assert C['plugin']['fresh_batch']['v1']['dylib_sha256']!=C['plugin']['fresh_batch']['v2']['dylib_sha256']
print('OK: 6 input variants, 4 valid mixed artifact families, batch/setup/direct-server oracles, 2 valid plugin generations; 39 command records')
