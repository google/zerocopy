"""Owned bounded certificate/domain/resource controls; no Rust proof importer."""
from dataclasses import dataclass, replace
import json

@dataclass(frozen=True)
class Subject:
    declaration:str='decode'
    body:str='body-A'
    impl:str='impl-bool'
    ty:str='bool'
    const:int=1
    lifetime:str='forall-a'
    target:str='word64-le'
    config:str='feature-off'
    generated_owner:str='derive-A'
    abi:str='Rust'

# The subject is supplied independently of the certificate: a proof must bind the
# callable actually selected by elaboration, not an arbitrary claimed subject.
required=Subject()
certificate={'subject':required,'law_domain':frozenset([0,1]),'predicate':lambda x:x in [0,1]}
def admits(actual, cert, required_domain):
    return actual==cert['subject'] and cert['law_domain']==required_domain and all(cert['predicate'](x) for x in required_domain)
mutations={'declaration':'other','body':'body-B','impl':'impl-u8','ty':'u8','const':2,
    'lifetime':'static-only','target':'word32-le','config':'feature-on','generated_owner':'derive-B','abi':'C'}
identity=[]
assert admits(required,certificate,frozenset([0,1]))
for field,value in mutations.items():
    wrong=replace(required,**{field:value})
    identity.append({'field':field,'wrong_subject_admitted':admits(wrong,certificate,frozenset([0,1]))})
assert all(not x['wrong_subject_admitted'] for x in identity)

# A name-only certificate cache would reuse the postcondition result=11 for B
# or const=2, although the independently selected bodies actually return21/12.
dispatch={'A':10,'B':20}
instances=[{'impl':impl,'const':n,'result':dispatch[impl]+n,'claimed_11':dispatch[impl]+n==11}
           for impl,n in [('A',1),('B',1),('A',2)]]
assert [x['claimed_11'] for x in instances]==[True,False,False]

# The selected unsafe-trait premise must cover every accepted byte, independently
# of the implementation-supplied predicate. Mutating it to True admits 254 bad
# bool representations if the external domain requirement is dropped.
raw=frozenset(range(256)); valid=frozenset([0,1])
bad_trait={'subject':required,'law_domain':raw,'predicate':lambda _:True}
good_accepts=[x for x in range(256) if x in valid]
bad_accepts=[x for x in range(256) if bad_trait['predicate'](x)]
assert len(set(bad_accepts)-valid)==254
assert not admits(required,bad_trait,valid)
vacuous={'subject':required,'law_domain':frozenset(),'predicate':lambda _:True}
assert not admits(required,vacuous,valid)

# Candidate Vec-like storage: capacity alone does not witness initialized len.
# A lying implementation-side premise can expose an invalid state to an
# otherwise safe indexed client; this is not an unsafe caller precondition.
storage=[10,11,12,'Uninit','Uninit']
def safe_get(promised_len,index):
    return storage[index] if 0<=index<promised_len else None
vec_like={'truthful_get3':safe_get(3,3),'lying_get4':safe_get(5,4),
          'truthful_prefix':[safe_get(3,i) for i in range(3)]}
assert vec_like['truthful_get3'] is None and vec_like['lying_get4']=='Uninit'

# Finite token protocol for a disjoint callback and a returned mutable resource.
# This is an explicit candidate contract, not a Tree Borrows transition model.
def exit_valid(state):
    return (set(state['caller'])|set(state['returned'])==set(range(6)) and
      not set(state['caller'])&set(state['returned']) and not state['active'] and
      not state['callback_retained'] and state['invariant'])
normal={'caller':[0,1],'returned':[2,3,4,5],'active':False,'callback_retained':[], 'invariant':True}
cases=[('normal',normal,True),('exceptional-restored',{**normal,'returned':[],'caller':list(range(6))},True),
  ('premature-recovery',{**normal,'active':True},False),
  ('retained-mutable-alias',{**normal,'callback_retained':[0]},False),
  ('overlapping-return',{**normal,'returned':[1,2,3,4,5]},False),
  ('lost-resource',{**normal,'returned':[3,4,5]},False),
  ('broken-invariant',{**normal,'invariant':False},False)]
resources=[]
for name,state,expected in cases:
    result=exit_valid(state);assert result==expected,name
    resources.append({'case':name,'accepted':result})

print(json.dumps({'identity_controls':identity,'selected_instance_results':instances,'valid_bool_domain':good_accepts,
    'mutated_unsafe_trait_extra_invalid_values':254,'wrong_law_domain_rejected':True,
    'vacuous_domain_rejected':True,'vec_like_initialization_control':vec_like,'callback_resource_controls':resources,
    'scope':'Owned candidate contract checks; no full Rust/MiniRust linking theorem'},indent=2))
