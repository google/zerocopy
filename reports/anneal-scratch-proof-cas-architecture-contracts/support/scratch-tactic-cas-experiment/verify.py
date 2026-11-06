#!/usr/bin/env python3
"""Check retained candidate decisions, pointer hashes, and final proof bytes."""
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
data=json.loads((HERE/'results.json').read_text())
assert data['prototype_only'] and data['canonical_generation_count']==4
events=data['events'];labels=[e['label'] for e in events]
assert labels==['accept','duplicate_retry','stale_source','partial_tactic','failed_tactic','sorry_tactic',
                'statement_changed','candidate_mutated','environment_changed','cancelled','reuse_accept']
expected={'accept':('accepted',None,2),'duplicate_retry':('duplicate',None,2),
          'stale_source':('rejected','stale_source',2),'partial_tactic':('rejected','invalid',2),
          'failed_tactic':('rejected','invalid',2),'sorry_tactic':('rejected','invalid',2),
          'statement_changed':('rejected','invalid_context',2),
          'candidate_mutated':('rejected','candidate_source_changed',2),
          'environment_changed':('rejected','environment_changed',3),
          'cancelled':('rejected','cancelled',3),'reuse_accept':('accepted',None,4)}
for e in events:
    result,reason,version=expected[e['label']]
    assert e['decision']['result']==result and e['decision'].get('reason')==reason
    assert e['current']['version']==version
    pointer=(json.dumps(e['current'],indent=2,sort_keys=True)+'\n').encode()
    assert hashlib.sha256(pointer).hexdigest()==e['decision']['pointer_sha256']
assert events[5]['candidate']['batch']['exit']==0 and events[5]['candidate']['status']=='invalid'
assert events[6]['candidate']['batch']['exit']==0 and events[6]['candidate']['status']=='invalid_context'
assert events[9]['candidate']['batch']['exit']==-9 and not events[9]['candidate']['batch']['remaining_group']
assert data['final_batch']['exit']==0 and data['final_batch']['matches_reuse_candidate_batch']
assert data['journal']=={'good-A':2,'reuse-after-cancel':4}
for name,digest in data['artifact_sha256'].items():assert sha(HERE/'artifacts'/name)==digest
assert sha(HERE/'artifacts/final-Proof.lean')==data['final']['source_sha256']
assert sha(HERE/'artifacts/final-ProbeEnv.lean')==data['final']['env_source_sha256']
assert ':= 8' in (HERE/'artifacts/final-ProbeEnv.lean').read_text()
assert 'exact Nat.add_zero n' in (HERE/'artifacts/final-Proof.lean').read_text()
print('verified 11 candidate decisions, four generations, exact pointer CAS, and fresh final batch result')
