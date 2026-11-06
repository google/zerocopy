#!/usr/bin/env python3
"""Offline retained R48 chain consistency checks; no tool invocation."""
import gzip,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parent
x=json.loads((R/'results.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
assert x['preflight']['ram_bytes']==8589934592
assert x['preflight']['memory_free_percent']>=40
assert x['preflight']['disk_free_bytes']>=10*1024**3
assert x['caps']['sampled_rss_kib']==4_500_000
assert len(x['cells'])==2
one,second=x['cells']
assert one['label']=='one' and one['workers']==1 and one['parallel'] is False
assert one['abort'] is None and one['errors']==[] and len(one['units'])==1
assert one['sampled_peak_rss_kib']<x['caps']['sampled_rss_kib']
assert one['wall_seconds']<x['caps']['duration_s'] and one['cleanup_tree']['processes']==[]
u=one['units'][0];d=u['direct']
assert len(d['commands'])==6 and all(q['exit']==0 for q in d['commands'])
assert "'obl_inc' depends on axioms: [propext, Classical.choice, Quot.sound]" in d['axiom_stdout']
assert "'obl_twice' depends on axioms: [propext, Classical.choice, Quot.sound]" in d['axiom_stdout']
assert "'obl_choose' depends on axioms: [propext, Classical.choice, Quot.sound]" in d['axiom_stdout']
assert 'sorryAx' not in d['axiom_stdout']
root=R/'work/one/u0';lake=root/'lake'
for name,digest in u['source_hashes'].items():assert sha((lake/name).read_bytes())==digest
for name,key in [('Types.lean','types'),('Funs.lean','funs'),('Current.lean','entry')]:
    assert sha((root/'generated'/name).read_bytes())==d['hashes'][key]
assert u['lake']['exit']==0 and len(u['lake']['local_jobs'])>=4
assert all('Built' in line for line in u['lake']['local_jobs'][-4:])
assert sha((lake/'.lake/build/lib/lean/Proof.olean').read_bytes())==u['lake']['proof_olean_sha256']
for label,meta in [('u0-lake',u['lake']['logs']),('u0-batch',u['fresh']['logs'])]:
    for stream in ('stdout','stderr'):
        data=gzip.decompress((R/'logs'/f'{label}.{stream}.gz').read_bytes())
        assert sha(data)==meta[stream+'_sha256']
assert u['fresh']['exit']==0
batch=gzip.decompress((R/'logs/u0-batch.stdout.gz').read_bytes()).decode()
assert '⊢ pipeline_workload.inc 0#u32 = Aeneas.Std.Result.ok 1#u32' in batch
assert "'goal_inc' depends on axioms: [propext, Classical.choice, Quot.sound]" in batch
assert 'sorryAx' not in batch
assert u['server']['wait']['result']=={}
goals=u['server']['goal']['result']['goals']
assert len(goals)==1 and 'pipeline_workload.inc 0#u32' in goals[0] and '1#u32' in goals[0]
msgs=u['server']['messages']
assert any(q['direction']=='client' and q['message'].get('method')=='textDocument/didOpen' for q in msgs)
assert any(q['direction']=='server' and q['message'].get('method')=='textDocument/publishDiagnostics' for q in msgs)
assert any(q['direction']=='server' and 'uses `sorry`' in str(q['message']) for q in msgs) # dependency warning, not theorem axiom
assert second['label']=='two-parallel' and second['admission']['allowed'] is False
assert second['admission']['one_peak_rss_kib']==one['sampled_peak_rss_kib']
assert second['admission']['current_free_percent']<45 or one['sampled_peak_rss_kib']>=1_500_000
print('PASS: one full pinned chain through Lake and server; two-worker admission skipped under cap')
