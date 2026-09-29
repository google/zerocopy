#!/usr/bin/env python3
"""Compare independently regenerated run with the preserved vertical report transcript."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ORIGINAL=HERE.parent.parent/'anneal-3730-vertical-acceptance-v4-30-0-rc2'/'support'/'transcript-run3.json'
NEW=HERE/'reproduction-run2.json'
OUT=HERE/'comparison.json'

old=json.loads(ORIGINAL.read_text())
new=json.loads(NEW.read_text())
def first(kind,name=None):
    return next(x for x in old if x.get('kind')==kind and (name is None or x.get('name')==name))
def old_snapshot(name):return first('snapshot',name)
def new_snapshot(name):return next(x for x in new['events'] if x.get('kind')=='snapshot' and x.get('name')==name)
rows=[]
def row(label,original,reproduced,expect_equal=True):
    rows.append({'comparison':label,'original':original,'reproduced':reproduced,
                 'equal':original==reproduced,'expected_exact':expect_equal})

for name,other in [('A-initial','initial'),('A','A'),('B','B'),('F-invalid','F')]:
    o=old_snapshot(name);n=new['snapshots'][other]
    for a,b in [('rust_sha256','host_sha256'),('generated_sha256','model_sha256'),('proof_sha256','proof_sha256')]:
        row(name+' '+a,o[a],n[b])
for name in ('A','B'):
    o=first('generated_build',name);n=new['models'][name]
    row(name+' model artifact',o['artifact_sha256'],n['artifact_sha256'])
    o=first('claim_comparison',name);n=new['checks'][name]
    for a,b in [('batch_rc','proof_rc'),('compiled_rc','artifact_rc'),
                ('oracle_rc','oracle_rc'),('oracle_sha256','oracle_sha256'),
                ('proof_artifact_sha256','proof_artifact_sha256')]:
        row(name+' '+a,o[a],n[b])
for name in ('weak-on-B','admitted-on-B'):
    o=first('claim_comparison',name);n=new['checks'][name]
    for a,b in [('batch_rc','proof_rc'),('oracle_rc','oracle_rc')]:
        row(name+' '+a,o[a],n[b])
    row(name+' proof source',o['proof_sha256'],new_snapshot(name)['proof_sha256'],False)
row('F generated compile exit',first('generated_build','F-invalid')['rc'],new['models']['F']['rc'])
row('old proof on B batch exit',first('stale_proof_comparison')['rc'],new['checks']['stale-on-B']['proof_rc'])
row('old proof on B live goal',first('B_stale_goal')['response']['result']['goals'],
    new['live']['stale-on-B']['initial_goal']['result']['goals'])
row('late A publication decision','reject-stale',new['late']['decision'])
row('final selected generation',first('publication_rejected_stale')['current']['name'],new['final_selected']['name'])
row('late A model source',old_snapshot('A-late')['generated_sha256'],new['snapshots']['A-late']['model_sha256'],False)
row('late A proof source',old_snapshot('A-late')['proof_sha256'],new['snapshots']['A-late']['proof_sha256'],False)
old_order=[first(kind)['seq'] for kind in ('late_build_entered_gate','provisional_failure','late_build_gate_released','late_build_finished','publication_rejected_stale')]
new_events=new['events']
new_order=[next(x['seq'] for x in new_events if x['kind']==kind) for kind in
           ('late_gate_entered','failed_generation','late_completed','late_disposition')]
old_b=max(x['seq'] for x in old if x.get('kind')=='published' and x.get('state',{}).get('name')=='B')
new_b=max(x['seq'] for x in new_events if x.get('kind')=='publish' and x.get('selected',{}).get('name')=='B')
assert old_order[0]<old_order[1]<old_b<old_order[2]<old_order[3]<old_order[4]
assert new_order[0]<new_order[1]<new_b<new_order[2]<new_order[3]
assert all(x['equal'] for x in rows if x['expected_exact'])
out={'original_path':'reports/anneal-3730-vertical-acceptance-v4-30-0-rc2/support/transcript-run3.json',
     'new_path':'reports/anneal-3730-independent-vertical-reproduction-2026-09-29/support/reproduction-run2.json',
     'causal_order':{'original':old_order,'original_B_publication':old_b,
                     'reproduced':new_order,'reproduced_B_publication':new_b,
                     'both_gate_before_failure_before_B_before_old_completion':True},
     'exact_matches':sum(x['equal'] and x['expected_exact'] for x in rows),
     'expected_exact':sum(x['expected_exact'] for x in rows),
     'intentional_differences':[x for x in rows if not x['equal'] and not x['expected_exact']],
     'rows':rows}
OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(f"{out['exact_matches']}/{out['expected_exact']} exact comparisons matched; "
      f"{len(out['intentional_differences'])} intentional source-layout differences")
