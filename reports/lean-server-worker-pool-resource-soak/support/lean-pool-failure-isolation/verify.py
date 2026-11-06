#!/usr/bin/env python3
"""Validate retained direct Lean pool and separate fencing-model observations."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
x=json.loads((HERE/'transcript.json').read_text())
assert x['abort']==[] and x['final_live_groups']==[]
assert x['preflight']['physical_bytes']==8589934592
assert x['preflight']['free_percent']>=40
assert x['admission']['eight_admitted']==False
assert len(x['cells'])==1 and x['cells'][0]['workers']==4
c=x['cells'][0]
assert len(c['started'])==4 and {z['index'] for z in c['started']}==set(range(4))
assert all(z['diagnostics']==[] and z['barrier']['result']=={} and '⊢ True' in str(z['goal']) for z in c['started'])
assert c['malformed']['disk_sha256']==c['started'][0]['source_sha256']
assert c['malformed']['buffer_sha256']!=c['malformed']['disk_sha256']
assert len(c['malformed']['diagnostics'])==1
assert c['malformed']['diagnostics'][0]['severity']==1
assert c['malformed']['diagnostics'][0]['message']=='numerals are data in Lean, but the expected type is a proposition\n  True : Prop'
before=[z for z in c['peer_checks'] if not z.get('after_crash')]
after=[z for z in c['peer_checks'] if z.get('after_crash')]
assert {z['index'] for z in before}=={1,2,3}
assert {z['index'] for z in after}=={0,2,3}
assert all(z['diagnostics']==[] and '⊢ True' in str(z['goal']) for z in before)
assert all(z['diagnostics']==[] and '⊢ True' in str(z['goal']) for z in after if z['index'] in (2,3))
assert c['crash']['cancel_sent'] and c['crash']['exit']==-9 and c['crash']['process_group_after']==[]
assert c['restart']['old_pid']!=c['restart']['new_pid']
assert c['restart']['diagnostics']==[] and '⊢ True' in str(c['restart']['goal'])
assert c['model_fence']['old_accepted'] is False and c['model_fence']['fresh_accepted'] is True
assert c['model_fence']['old_candidate']['worker_epoch']!=c['model_fence']['restart_current']['worker_epoch']
assert c['post_cleanup']['process_rows']==[] and c['post_cleanup']['resources']['rss_bytes']==0
samples=[z['value'] for z in x['events'] if z['kind']=='resource']
assert samples and all(s['rss_bytes']<=x['limits']['rss_bytes'] and s['disk_blocks_bytes']<=x['limits']['disk_blocks_bytes']
                       and s['free_percent']>=x['limits']['free_percent_floor'] and s['elapsed_seconds']<=x['limits']['duration_seconds'] for s in samples)
print('PASS: admitted four-worker fault/crash isolation, restart, fence model and resource cleanup; eight denied by admission')
