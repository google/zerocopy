#!/usr/bin/env python3
"""Offline check for the resource-denied I102 cache probe."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
x=json.loads((P/'results.json').read_text())
meta=json.loads((P/'REPORT.json').read_text())
assert meta['subjects'][0]['identity']['results_sha256']==sha((P/'results.json').read_bytes())
assert x['status']=='stopped' and x['error']=="RuntimeError('prebuild-b:fresh_admission_denied')"
assert len(x['runs'])==1 and len(x['admissions'])==2 and x['cases']=={}
a,b=x['admissions']
assert a['label']=='prebuild-a' and a['memory_fraction']>.30 and a['disk_free']>10*1024**3
assert b['label']=='prebuild-b' and b['memory_fraction']<=.30 and b['disk_free']>10*1024**3
r=x['runs'][0]
assert r['label']=='prebuild-a' and r['exit']==0 and r['abort'] is None and r['elapsed']<30
assert r['argv'][-2:]==['build','Dep'] and r['env_overrides']['LAKE_ARTIFACT_CACHE']=='false'
assert r['env_overrides']['LAKE_NO_NET']=='1' and r['env_overrides']['LEAN_PATH'] is None
assert min(s['memory_fraction'] for s in r['resource_samples'])>.20
assert max(s['group_rss_kib'] for s in r['resource_samples'])<2200*1024
for stream in ('stdout','stderr'):
 raw=(P/'raw'/f'prebuild-a.{stream}').read_bytes()
 assert sha(raw)==r[f'{stream}_sha256']
assert 'image_attach' not in x and 'devices' not in x
assert not (P/'work/cache.sparseimage').exists()
assert (P/'work/a/producer/.lake').is_dir()
assert (P/'work/b/producer').is_dir()
print('PASS: I102 refusal boundary, one prebuild and denied second admission')
