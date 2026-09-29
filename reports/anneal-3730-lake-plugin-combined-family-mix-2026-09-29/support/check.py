#!/usr/bin/env python3
"""Offline integrity and result assertions for the R21 specimen."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
T=json.loads((HERE/'transcript.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def one(kind,label):
    rows=[x for x in T if x['kind']==kind and x.get('label')==label]
    assert len(rows)==1,(kind,label,len(rows))
    return rows[0]
ret=[x for x in T if x['kind']=='retained'];assert len(ret)==1
for label,items in ret[0]['inventory'].items():
    for key,info in items.items():
        p=HERE/'artifacts'/label/key
        assert p.is_file() and p.stat().st_size==info['bytes'] and sha(p)==info['sha256'],(label,key)
def h(label,key):return ret[0]['inventory'][label][key]['sha256']
assert h('v1','source')==h('mix','source')!=h('v2','source')
assert h('v1','olean')==h('mix','olean')!=h('v2','olean')
assert h('v1','ilean')==h('mix','ilean')==h('v2','ilean')
assert h('v2','c')==h('mix','c')!=h('v1','c')
assert h('v2','plugin')==h('mix','plugin')!=h('v1','plugin')
assert h('v2','setup')==h('mix','setup')!=h('v1','setup')
for label,value,marker in [('v1','7','plugin-v1'),('v2','9','plugin-v2'),('mix','7','plugin-v2')]:
    s=one('server_outcome',label)
    assert s['rc']==0 and 'error' not in s and s['marker']==marker,(label,s.get('error'),s['rc'],s['marker'])
    assert s['wait']['result']=={} and s['goal']['result']['rendered']=='no goals'
    msgs=[d.get('message','') for row in s['diagnostics'] for d in row['diagnostics']]
    assert value in msgs and not any('error' in d for d in msgs),(label,msgs)
    b=one('command','batch-'+label)
    assert b['rc']==0 and b['stdout'].strip()==value
    setup=one('command','setup-'+label)
    assert setup['rc']==0
    parsed=json.loads(setup['stdout'])
    assert parsed['plugins'] and parsed['plugins'][0].endswith('/plugin__probe_Plugin.dylib')
    assert parsed['importArts']['Dep'][0].endswith('/Dep.olean')
    assert parsed['options']==({'pp.universes':True} if label!='v1' else {})
for stage in ('mix-before','mix-after-setup','mix-after-server'):
    i=one('inventory',stage)['artifacts']
    for key in ('source','olean','ilean','c','plugin','setup'):
        assert i[key]['sha256']==h('mix',key),(stage,key)
assert one('command','setup-mix')['rc']==0
assert one('command','batch-mix')['rc']==0
assert one('command','batch-mix')['stdout'].strip()=='7'
print('OK: retained byte hashes, setup paths/options, 3 fresh Lake servers, initializer markers, imported-value diagnostics, batches and unchanged mixed artifacts')
