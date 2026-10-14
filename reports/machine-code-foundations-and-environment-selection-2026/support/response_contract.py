"""Finite shape of a nonempty, universal environment contract; not Coq execution."""
from itertools import combinations
import json
universe=[0,7,42]
def response_contract(allowed,post):return bool(allowed) and all(post(v) for v in allowed)
sets=[list(c) for n in range(4) for c in combinations(universe,n)]
rows=[{'allowed':s,'accepted':response_contract(s,lambda v:v==7)} for s in sets]
if [x['allowed'] for x in rows if x['accepted']] != [[7]]:raise SystemExit('response quantifier control failed')
def candidate_result_contract(observed):
 return (observed['value']==7 and observed['events']==['MMIOREAD']
         and observed['memory'].get(256)==42)
good={'value':7,'events':['MMIOREAD'],'memory':{256:42}}
no_event={'value':7,'events':[],'memory':{256:42}}
no_memory={'value':7,'events':['MMIOREAD'],'memory':{}}
controls={'empty_rejected':not response_contract([],lambda v:True),
 'one_good_does_not_cover_bad':7 in [7,42] and not response_contract([7,42],lambda v:v==7),
 'candidate_result_accepted':candidate_result_contract(good),
 'omitted_event_rejected':not candidate_result_contract(no_event),
 'omitted_memory_update_rejected':not candidate_result_contract(no_memory)}
if not all(controls.values()):raise SystemExit('environment effect control failed')
print(json.dumps({'response_sets':rows,'controls':controls,'scope':'Owned finite quantifier/effect fixtures only; not upstream Coq or hardware execution'},indent=2))
