#!/usr/bin/env python3
"""Validate preserved R10 observations and exact acquired artifact bytes."""
import hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parent
A=json.loads((P/'results.json').read_text())
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def inv(root):
    return {p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
            for p in sorted(root.rglob('*')) if p.is_file()}
assert A['environment']['max_concurrent_consumers']==2
assert A['environment']['initial_memory_free_percent']>=35
assert A['environment']['rss_cap_kib']==3_800_000
G=A['cases']['golden']['cache']
assert G==inv(P/'artifacts/golden-cache')
for i in range(3):
    c=A['cases'][f'pair-{i}']
    assert c['markers']==[True,True] and c['exits']==[0,0]
    assert c['map_valid_before_repair'] and c['cache_matches_golden_before_repair']
    assert not c['repair_needed'] and c['fresh_setup_exit']==c['fresh_import_exit']==0
    assert c['peak_sampled']['rss_kib_sum']<A['environment']['rss_cap_kib']
    assert c['cache_after']==G==inv(P/f'artifacts/pair-cache-{i}')
for ext,bytes_ in [('olean',2448),('ilean',404),('c',764)]:
    c=A['cases'][f'interrupt-{ext}']
    part=P/f'artifacts/partial-{ext}.bin'
    assert c['failed_exit']==-25 and c['partial_observed']
    assert c['partial_bytes']==bytes_==part.stat().st_size and c['partial_sha256']==sha(part)
    assert c['no_build_exit_after_failure']==3
    assert c['retry_with_partial_present_exit']==0
    assert c['partial_present_integrity_matches_golden'] is False
    assert c['fresh_setup_with_partial_present_exit']==0
    assert c['fresh_import_with_partial_present_exit']==(-11 if ext=='olean' else 0)
    assert c['cache_after_present_retry']==inv(P/f'artifacts/partial-present-cache-{ext}')
    assert c['fresh_setup_exit']==c['fresh_import_exit']==0
    assert c['cache_after_repair']==G==inv(P/f'artifacts/repaired-cache-{ext}')
    target=f'artifacts/{c["target_file"]}'
    assert c['cache_after_present_retry'][target]['sha256']==c['partial_sha256']
    assert c['cache_after_present_retry'][target]['sha256']!=G[target]['sha256']
print('OK: 3 overlapping same-key pairs; 3 genuine partial artifact writes; false-hit and repair oracles validated')
