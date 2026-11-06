#!/usr/bin/env python3
"""Offline validation of R19 retained commands, identities and specimens."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
R=json.loads((HERE/'results.json').read_text());C=R['cases'];A=HERE/'artifacts'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert len(R['commands'])==57 and len(C)==12
assert R['environment']['max_concurrent_commands']==1 and R['environment']['free_memory_preflight_percent']>=35
for name,info in R['retained_inventory'].items():
 p=A/name
 assert p.is_file() and p.stat().st_size==info['bytes'] and sha(p)==info['sha256'],name
def h(case,file):return C[case]['snapshot']['files'][file]['sha256'] if C[case]['snapshot']['files'][file] else None
a,b,t7,t9,opt=(C[x] for x in ('dynamic-a','dynamic-b','toml-seven','toml-nine','lean-option'))
assert h('dynamic-a','source')==h('toml-seven','source')==h('lean-option','source')
assert h('dynamic-b','source')==h('toml-nine','source')!=h('dynamic-a','source')
assert h('dynamic-a','olean')==h('toml-seven','olean')==h('lean-option','olean')
assert h('dynamic-b','olean')==h('toml-nine','olean')!=h('dynamic-a','olean')
assert h('dynamic-a','trace')!=h('toml-seven','trace')
assert h('dynamic-a','setup')!=h('lean-option','setup')
for name in ('dynamic-a','dynamic-b','toml-seven','toml-nine','lean-option'):
 x=C[name];assert x['setup_batch']['setup_exit']==0
 assert x['setup_batch']['setup_import_sha256']==h(name,'olean')
 assert x['setup_batch']['exit']==x['local_batch_exit']==(1 if name in ('dynamic-b','toml-nine') else 0)
 assert sha(A/name/'source')==h(name,'source') and sha(A/name/'trace')==h(name,'trace')
assert C['env-b-stale']['no_build_exit']==0
assert h('env-b-stale','source')==h('dynamic-a','source')
assert h('env-b-stale','olean')==h('dynamic-a','olean')
assert C['env-b-stale']['setup_batch']['setup_import_sha256']==h('dynamic-a','olean')
assert C['env-b-stale']['local_batch_exit']==C['env-b-stale']['setup_batch']['exit']==0
base=C['env-b-stale']['snapshot']['files']
for name,key,delta in [('source-older','source',-86_400_000_000_000),('source-newer','source',86_400_000_000_000),('trace-newer','trace',86_400_000_000_000)]:
 x=C[name];f=x['snapshot']['files']
 assert x['no_build_exit']==x['local_batch_exit']==x['setup_batch']['exit']==0
 assert f[key]['mtime_ns']-base[key]['mtime_ns']==delta
 assert f[key]['sha256']==base[key]['sha256']
 assert x['setup_batch']['setup_import_sha256']==h('dynamic-a','olean')
wrong=C['wrong-trace'];assert wrong['no_build_exit']==wrong['setup_batch']['exit']==0
assert h('wrong-trace','trace')!=h('dynamic-a','trace') and h('wrong-trace','olean') is None
assert wrong['local_batch_exit']==1 and wrong['setup_batch']['setup_import_sha256']==h('dynamic-a','olean')
setup=C['wrong-setup'];assert setup['no_build_exit']==setup['setup_batch']['exit']==setup['local_batch_exit']==0
assert h('wrong-setup','setup')==h('lean-option','setup')!=h('dynamic-a','setup')
assert h('wrong-setup','olean')==h('dynamic-a','olean') and setup['setup_batch']['setup_import_sha256']==h('dynamic-a','olean')
edit=C['same-mtime-source-edit'];assert edit['no_build_exit']==0
assert h('same-mtime-source-edit','source')==h('dynamic-b','source')
assert edit['snapshot']['files']['source']['mtime_ns']==base['source']['mtime_ns']
assert h('same-mtime-source-edit','olean') is None and edit['local_batch_exit']==1
assert edit['setup_batch']['exit']==1 and edit['setup_batch']['setup_import_sha256']==h('dynamic-b','olean')
for name,value in [('dynamic-a','8'),('dynamic-b','10'),('toml-seven','8'),('env-b-stale','8')]:
 s=C[name]['server'];assert s['wait_completed'] and s['olean_sha256']==h(name if name!='env-b-stale' else 'dynamic-a','olean')
 msg=[d.get('message','') for row in s['diagnostics'] for d in row.get('diagnostics',[])]
 assert value in msg
 assert any('is false' in x for x in msg)==(value=='10')
 assert s['process_exit']==-9
print('OK: 5 clean config cells, stale dynamic environment, 3 mtime controls, valid wrong trace/setup, same-mtime source edit, 4 direct servers; 57 commands')
