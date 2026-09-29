#!/usr/bin/env python3
"""Small executable counterexamples for identity, projection, and publication."""
import hashlib, itertools, json, random
from pathlib import Path

OUT = Path(__file__).resolve().parents[1]

def sha(s): return hashlib.sha256(s.encode()).hexdigest()

# 1. Identity ablation. This is a finite model, not implementation evidence.
base = dict(workspace='w1', cargo_subject='lib:default:aarch64', source='srcA', charon='c1/cfg1', llbc='l1', aeneas='a1/cfg1', generated='g1', env='lake1', imports='i1', projection='p1', uri='lean://w1/proof', doc_version=7, worker=4, rpc=9)
scenarios = [
 ('same paths, Rust bytes change', {'source':'srcB'}),
 ('same document URI/version, proof bytes change', {'projection':'p2'}),
 ('same proof, imported artifact changes', {'imports':'i2'}),
 ('same source path, Cargo target changes', {'cargo_subject':'test:featureX:x86_64'}),
 ('same code, Charon configuration changes', {'charon':'c1/cfg2'}),
 ('same LLBC, Aeneas configuration changes', {'aeneas':'a1/cfg2'}),
 ('same generated source, Lake environment changes', {'env':'lake2'}),
 ('same bytes, later worker epoch', {'worker':5}),
 ('same generated output path, LLBC identity changes', {'llbc':'l2'}),
 ('same worker, RPC session reconnected', {'rpc':10}),
]
assert len({tuple(sorted(delta.items())) for _, delta in scenarios}) == len(scenarios)
keys = {
 'path': ('workspace', 'uri'),
 'uri_version': ('workspace', 'uri', 'doc_version'),
 'proof_hash': ('projection',),
 'document_imports': ('workspace','cargo_subject','source','projection','imports'),
 'semantic_content': ('cargo_subject','source','charon','llbc','aeneas','generated','env','imports','projection'),
 'causal_response': ('workspace','cargo_subject','source','charon','llbc','aeneas','generated','env','imports','projection','uri','doc_version','worker','rpc'),
}
def ktuple(row, fields): return tuple(row[x] for x in fields)
identity_rows=[]
for name, delta in scenarios:
 changed=base | delta
 collisions=[]
 for kn, fields in keys.items():
  if ktuple(base,fields)==ktuple(changed,fields): collisions.append(kn)
 identity_rows.append({'scenario':name,'changed_fields':sorted(delta),'insufficient_keys_colliding':collisions,'full_causal_identity_changes':ktuple(base,keys['causal_response']) != ktuple(changed,keys['causal_response'])})
assert all(row['full_causal_identity_changes'] for row in identity_rows)
assert 'path' in identity_rows[0]['insufficient_keys_colliding']
assert 'uri_version' in identity_rows[1]['insufficient_keys_colliding']
assert 'proof_hash' in identity_rows[2]['insufficient_keys_colliding']

# Byte-identical content may be reusable as an artifact, but the returned result
# must still carry the current causal generation.
content_a=('sourceA','llbcA','generatedA','importsA','toolTupleA')
content_b=('sourceB','llbcB','generatedB','importsB','toolTupleA')
content_a_again=('sourceA','llbcA','generatedA','importsA','toolTupleA')
causal_tag_a=('workspace1',12,3,8)
causal_tag_b=('workspace1',13,4,10)
causal_tag_a_again=('workspace1',14,5,11)
assert content_a != content_b and content_a == content_a_again
assert len({causal_tag_a,causal_tag_b,causal_tag_a_again})==3

# 2. UTF-8 bytes, Unicode scalar, and UTF-16 positions. Round-trip only at valid
# scalar boundaries; UTF-16 midpoint of a supplementary character is invalid.
def utf16_units(s): return sum(2 if ord(c)>0xFFFF else 1 for c in s)
def byte_offset(s, scalar_index): return len(s[:scalar_index].encode('utf-8'))
def utf16_offset(s, scalar_index): return utf16_units(s[:scalar_index])
corpus=['', 'abc', 'é', 'e\u0301', '𐐷', 'a𐐷b', '\tλ\r\n', 'x\r\ny\n', '🧪\tcombining:e\u0301']
for seed in range(50):
 r=random.Random(seed)
 alphabet=['a','Z','λ','e','\u0301','𐐷','🧪','\t','\n','\r']
 corpus.append(''.join(r.choice(alphabet) for _ in range(40)))
coordinate_rows=[]
for s in corpus:
 for i in range(len(s)+1):
  b=byte_offset(s,i); u=utf16_offset(s,i)
  assert s.encode('utf-8')[:b].decode('utf-8') == s[:i]
  assert utf16_units(s[:i]) == u
  coordinate_rows.append({'text_sha256':sha(s),'scalar_index':i,'utf8_byte':b,'utf16_units':u})

# Projection segments are authored spans separated by synthetic scaffolding.
# Every authored point maps; points in synthetic gaps and cross-segment edits do not.
segments=[{'source_start':10,'source_end':16,'projected_start':3,'projected_end':9},
          {'source_start':30,'source_end':36,'projected_start':20,'projected_end':26}]
def map_pos(p):
 for seg in segments:
  if seg['projected_start'] <= p <= seg['projected_end']:
   return seg['source_start'] + p - seg['projected_start']
 return None
assert map_pos(5)==12 and map_pos(22)==32 and map_pos(14) is None
patch_expected={'host_sha256':'hA','projection_sha256':'pA','document_version':5}
patch_current=patch_expected.copy()
def apply_patch(start,end,expected,current):
 if expected != current: return False
 return any(seg['projected_start'] <= start <= end <= seg['projected_end'] for seg in segments)
patch_cases=[]
for name,start,end,observed in [
 ('inside one segment',4,6,patch_expected),
 ('touches synthetic prefix',2,4,patch_expected),
 ('crosses synthetic gap',8,21,patch_expected),
 ('stale host digest',4,6,{'host_sha256':'hB','projection_sha256':'pB','document_version':6}),
]:
 accepted=apply_patch(start,end,patch_expected,observed)
 patch_cases.append({'name':name,'start':start,'end':end,'accepted':accepted})
assert [x['accepted'] for x in patch_cases]==[True,False,False,False]

# 3. Generation publication model: staged output is visible only after complete
# generation and current-token check. Enumerate all event orderings for two jobs.
events=['stageA','stageB','cancelA','publishA','publishB']
valid=0; rejected=0; unsafe_naive=0; counterexamples=[]
for order in itertools.permutations(events):
 current='A'; staged=set(); canceled=set(); published=[]; naive_published=[]
 for event in order:
  if event.startswith('stage'): staged.add(event[-1])
  elif event.startswith('cancel'): canceled.add(event[-1])
  elif event.startswith('publish'):
   g=event[-1]
   if g in staged and g not in canceled and g==current:
    published.append(g)
   elif g in staged and g not in canceled:
    naive_published.append((g,current))
    rejected+=1
  if event=='stageB': current='B'
 # Safe protocol never publishes stale A after B is current.
 assert not any(g=='A' for g in published[1:]) or current=='A'
 # Naive path/last-writer behavior would accept any complete uncancelled stage.
 if any(g=='A' and current_at_publish=='B' for g,current_at_publish in naive_published):
  unsafe_naive += 1
  if len(counterexamples)<5: counterexamples.append(list(order))
 valid += 1
assert valid==120 and rejected>0 and unsafe_naive>0

result={
 'identity_ablation':{'cases':identity_rows,'cache_content_identity_example':{'a_to_b_content_changes':content_a!=content_b,'a_to_b_to_a_content_recurs':content_a==content_a_again,'causal_tags_all_distinct':len({causal_tag_a,causal_tag_b,causal_tag_a_again})==3,'content_keys':[content_a,content_b,content_a_again],'causal_tags':[causal_tag_a,causal_tag_b,causal_tag_a_again]}},
 'projection_coordinates':{'corpus_strings':len(corpus),'valid_scalar_boundaries_checked':len(coordinate_rows),'coordinate_sample':coordinate_rows[:12],'all_utf8_utf16_roundtrips':True,'projection_segments':segments,'mapped_positions':[map_pos(x) for x in [3,5,9,10,19,20,22,26,27]],'patch_cases':patch_cases,'stale_patch_cas_rejected':not patch_cases[-1]['accepted']},
 'generation_schedule_model':{'permutations':valid,'stale_publish_rejections':rejected,'naive_late_publish_counterexample_count':unsafe_naive,'counterexample_orders':counterexamples,'safe_current_generation_guard':True},
 'limits':['Finite illustrative model only; it does not establish implementation behavior.','Projection segments are a test oracle fixture, not an implemented Rust parser or Lean projection engine.','UTF-16 positions inside a surrogate pair are not invertible; test only source scalar boundaries.']
}
(OUT/'support'/'model-probes.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:(v if k=='identity_ablation' else {kk:vv for kk,vv in v.items() if kk not in ('coordinate_sample','counterexample_orders')}) for k,v in result.items() if k!='limits'},indent=2))
