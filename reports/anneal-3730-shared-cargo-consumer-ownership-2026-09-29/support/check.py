#!/usr/bin/env python3
"""Offline consistency check for retained shared-Cargo ownership run."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
x=json.loads((ROOT/'results.json').read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert x['preflight']['free_disk_bytes']>=2_000_000_000
assert x['preflight']['free_memory_percent']>=25
assert len(x['cases'])==3
assert [c['name'] for c in x['cases']]==['cancel-one','cancel-both','failure']
for rel,digest in x['fixture_sha256'].items(): assert sha(ROOT/'fixture'/rel)==digest
for c in x['cases']:
    assert c['fixture_sha256']==x['fixture_sha256']
    assert c['first']['group_after']==[]
    assert c['events'][0]['kind']=='start' and c['events'][1]['kind']=='marker'
    assert c['events'][1]['sampled_rss_kib']<2_000_000
    group=c['events'][1]['group']
    assert len(group)>=3 and any('cargo' in p['comm'] for p in group)
    assert any('build-script-build' in p['comm'] for p in group)
    assert any('/bin/sleep' in p['comm'] for p in group)
    assert c['marker'].split()==[str(p['pid']) for p in group if 'build-script-build' in p['comm'] or '/bin/sleep' in p['comm']]
    for rel,digest in c['fixture_sha256'].items(): assert sha(ROOT/'work'/c['name']/rel)==digest
one,both,fail=x['cases']
assert one['first']['exit']==0 and one['first']['artifact_exists'] and one['retry'] is None
assert one['consumer_results']=={'editor':'cancelled','agent':'success'}
assert one['events'][2]['kind']=='cancel_editor' and one['events'][2]['backend_poll'] is None
assert sha(ROOT/'work/cancel-one/target/debug/libshared_job_probe.rlib')==one['first']['artifact_sha256']
assert both['first']['exit']==-15 and not both['first']['artifact_exists']
assert both['consumer_results']=={'editor':'cancelled','agent':'cancelled'}
assert [e['kind'] for e in both['events']][2:5]==['cancel_editor','cancel_agent','signal_last_owner']
assert both['retry']['exit']==0 and both['retry']['group_after']==[]
assert sha(ROOT/'work/cancel-both/target/debug/libshared_job_probe.rlib')==both['retry']['artifact_sha256']
assert fail['first']['exit']!=0 and not fail['first']['artifact_exists']
assert 'injected build-script failure' in fail['first']['stderr']
assert fail['consumer_results']=={'editor':'failed','agent':'failed'}
assert fail['retry']['exit']==0 and fail['retry']['group_after']==[]
assert sha(ROOT/'work/failure/target/debug/libshared_job_probe.rlib')==fail['retry']['artifact_sha256']
assert len({one['first']['artifact_sha256'],both['retry']['artifact_sha256'],fail['retry']['artifact_sha256']})==3  # distinct private path/metadata bytes
print('PASS: one real shared Cargo job, individual/last-owner cancellation, failure fan-out and retry')
