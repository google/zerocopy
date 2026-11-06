#!/usr/bin/env python3
"""Offline validation of two shared-tree conflicting Lake writer schedules."""
import hashlib,json
from pathlib import Path

s=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for filename,work,victim,pre in [
 ('results.json','work','A',(0,0,1)),
 ('results-kill-B.json','work-kill-B','B',(3,1,0)),
]:
 r=json.loads((s/filename).read_text());p=s/work/'probe'
 assert r['schema']=='anneal-shared-lake-tree-conflict-v1'
 assert r['source_a_sha256']!=r['source_b_sha256']
 assert sha(p/'Dep.lean')==r['source_b_sha256']==r['source_final_sha256']
 kinds=[e['kind'] for e in r['events']]
 assert kinds==['launch_A','A_entered','source_changed_to_9','launch_B','B_entered',
                'kill_'+victim,'release_'+('B' if victim=='A' else 'A')]
 assert (s/work/'A.entered').is_file() and (s/work/'B.entered').is_file()
 assert r['B_gate']['peak_sampled_rss_kib']<4400000
 records={x['label']:x for x in r['records']}
 assert records[victim]['exit']==-9
 assert records['A' if victim=='B' else 'B']['exit']==0
 assert records['fresh_no_build']['exit']==pre[0]
 assert records['pre_retry_lean_9']['exit']==pre[1]
 assert records['pre_retry_lean_7']['exit']==pre[2]
 assert records['ordinary_retry']['exit']==records['post_retry_no_build']['exit']==0
 assert records['fresh_lean_9']['exit']==0 and records['fresh_lean_7_negative']['exit']!=0
 assert '9\n' in records['fresh_lean_9']['stdout']
 if victim=='B':
  assert '7\n' in records['pre_retry_lean_7']['stdout']
  assert 'out-of-date' in records['fresh_no_build']['stdout']
 for name,meta in r['final_inventory'].items():
  q=p/name
  assert q.stat().st_size==meta['bytes'] and sha(q)==meta['sha256']
print('PASS: shared-tree A/B writer overlap, reverse kills, stale pre-retry and repaired fresh Lean oracle')
