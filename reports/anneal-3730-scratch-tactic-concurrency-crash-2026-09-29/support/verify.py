#!/usr/bin/env python3
"""Verify retained two-writer CAS, crash recovery and reader-pinning evidence."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
d=json.loads((HERE/'results.json').read_text());assert d['prototype_only']
competition=d['competition'];assert len(competition['checked'])==2 and len(competition['applied'])==2
assert all(x['batch_exit']==0 for x in competition['checked'])
assert sorted(x['decision']['result'] for x in competition['applied'])==['accepted','rejected']
assert next(x for x in competition['applied'] if x['decision']['result']=='rejected')['decision']['reason']=='stale_proof'
assert competition['after_version']==2 and competition['winner']!=competition['loser']
crashes=d['crashes'];assert [x['phase'] for x in crashes]==['materialized','checked','pre_swap','post_swap']
assert [x['exit'] for x in crashes]==[71,72,73,74]
assert [x['recovered_version'] for x in crashes]==[2,2,2,3]
assert all(x['fresh_batch']['exit']==0 for x in crashes)
assert all(x['marker']['phase']==x['phase'] for x in crashes)
orphan=json.loads((HERE/'artifacts/orphan-MANIFEST.json').read_text())
assert orphan['complete'] and orphan['generation']==crashes[2]['marker']['created_generation']
assert orphan['generation']!=crashes[2]['recovered_generation']
assert crashes[3]['marker']['created_generation']==crashes[3]['recovered_generation']
for kind,reason in [('proof','candidate_proof_mutated'),('import','candidate_import_mutated')]:
    x=d['mutation_controls'][kind]
    assert x['batch_exit']==0 and x['decision']['result']=='rejected' and x['decision']['reason']==reason
reader=d['reader'];assert reader['observed']['sha256']==reader['pinned_sha256']
assert reader['observed']['path_exists'] and reader['publish']['result']=='accepted'
assert d['final']['version']==4 and d['final_batch']['exit']==0 and d['generation_count']==5
final_manifest=json.loads((HERE/'artifacts/final-MANIFEST.json').read_text())
assert final_manifest==d['final'] and final_manifest['complete']
for name,digest in d['artifact_sha256'].items():assert sha(HERE/'artifacts'/name)==digest
assert sha(HERE/'artifacts/final-Proof.lean')==d['final']['proof_sha256']
assert sha(HERE/'artifacts/final-ProbeEnv.lean')==d['final']['env_sha256']
print('verified two-writer CAS, four crash phases, two mutation rejects, pinned reader and final batch')
