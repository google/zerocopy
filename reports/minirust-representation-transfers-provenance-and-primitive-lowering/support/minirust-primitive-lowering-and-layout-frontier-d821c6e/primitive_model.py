"""Owned finite discriminators, not a MiniRust import or a Rust executor."""
import json
from itertools import product

def bounded(n, bits, signed=False):
    n %= 1 << bits
    return n - (1 << bits) if signed and n >= (1 << (bits-1)) else n

def shift_valid(count,bits):
    return 0 <= count < bits

def metadata(bits, kind, value, trait='A'):
    if kind == 'slice': return isinstance(value, int) and 0 <= value < 1 << bits
    if kind == 'dyn': return isinstance(value, dict) and value.get('allocated') and value.get('trait') == trait
    return value is None

def pointer(bits, kind, meta, addr, elem=1, align=1, safe=True, provenance=True, live=True, allocation=8):
    # Selected check_ptr + BasicMemory rules, with a single allocation at 16.
    if not 0 <= addr < 1 << bits or not metadata(bits, kind, meta): return False
    if not safe: return True
    size = meta * elem if kind == 'slice' else meta['size'] if kind == 'dyn' else elem
    align = meta['align'] if kind == 'dyn' else align
    return (size < 1 << (bits-1) and addr != 0 and addr % align == 0 and
            (size == 0 or (provenance and live and 16 <= addr and addr+size <= 16+allocation)))

arithmetic=[]
for bits, signed in product([4,8,32,64], [False,True]):
    lo = -(1 << (bits-1)) if signed else 0
    hi = (1 << (bits-1))-1 if signed else (1 << bits)-1
    arithmetic.append({'bits':bits,'signed':signed,'max_plus_one':bounded(hi+1,bits,signed),
        'unchecked_add_reject':not lo <= hi+1 <= hi,
        'normal_shift_at_width':bounded(1 << (bits % bits),bits,signed),
        'unchecked_shift_at_width_reject':not shift_valid(bits,bits)})
    assert bounded(hi+1,bits,signed) == lo
    assert shift_valid(0,bits) and shift_valid(bits-1,bits) and not shift_valid(-1,bits) and not shift_valid(bits,bits)

dst=[]
for bits in [32,64]:
    cases=[('valid-slice',dict(kind='slice',meta=3,addr=16),True),
      ('oversize-slice',dict(kind='slice',meta=1 << (bits-1),addr=16),False),
      ('usize-overflow-meta',dict(kind='slice',meta=1 << bits,addr=16),False),
      ('zst-no-provenance',dict(kind='slice',meta=(1 << bits)-1,addr=16,elem=0,provenance=False),True),
      ('zst-null',dict(kind='slice',meta=0,addr=0,elem=0),False),
      ('valid-meta-no-provenance',dict(kind='slice',meta=3,addr=16,provenance=False),False),
      ('valid-meta-dead',dict(kind='slice',meta=3,addr=16,live=False),False),
      ('valid-meta-unaligned',dict(kind='slice',meta=1,addr=17,elem=2,align=2),False),
      ('raw-null-valid-meta',dict(kind='slice',meta=3,addr=0,safe=False),True),
      ('wrong-kind',dict(kind='slice',meta={'allocated':True,'trait':'A'} ,addr=16),False),
      ('dyn-good',dict(kind='dyn',meta={'allocated':True,'trait':'A','size':4,'align':4},addr=16),True),
      ('dyn-wrong-trait',dict(kind='dyn',meta={'allocated':True,'trait':'B','size':4,'align':4},addr=16),False),
      ('dyn-good-meta-bad-data',dict(kind='dyn',meta={'allocated':True,'trait':'A','size':4,'align':4},addr=16,provenance=False),False)]
    for name,args,expected in cases:
        result=bool(pointer(bits,**args)); assert result == expected,(bits,name)
        dst.append({'bits':bits,'case':name,'accepted':result})

overlap={'cases':0,'streaming_mutant_disagreements':0,'zero_cases':0,'first_counterexample':None}
memory=[('byte',i,'prov'+str(i//2)) for i in range(8)]
for n in range(9):
    for src,dest in product(range(9-n), repeat=2):
        reference=memory[:]; reference[dest:dest+n]=memory[src:src+n]
        snapshot=memory[:]; saved=snapshot[src:src+n]; snapshot[dest:dest+n]=saved
        mutant=memory[:]
        for i in range(n): mutant[dest+i]=mutant[src+i]
        assert snapshot == reference
        overlap['cases']+=1; overlap['zero_cases'] += n == 0
        if mutant != reference:
            overlap['streaming_mutant_disagreements']+=1
            if overlap['first_counterexample'] is None:
                overlap['first_counterexample']={'src':src,'dest':dest,'length':n}

union=[]
for word,endian in product([4,8], ['little','big']):
    data=[('ptr-fragment', 'alloc1', i) for i in range(word)]
    encoded=data+list((3).to_bytes(word,endian))
    # Exact selected calc_chunks pointer arm marks only one word.
    bad=encoded[:word]+['Uninit']*word
    coherent=encoded[:]
    assert bad[word:] != encoded[word:] and coherent[word:] == encoded[word:]
    union.append({'word_bytes':word,'endian':endian,'imported_chunks':[[0,word]],
        'wide_layout_size':word*2,'metadata_after_union_copy':bad[word:],
        'coherent_chunks':[[0,word*2]],'coherent_length':int.from_bytes(bytes(coherent[word:]),endian)})

# Discriminator range controls, not compiler-produced niche layouts.
def decode_tag(x, start, end, niche, untagged):
    valid=start <= x <= end if start <= end else x >= start or x <= end
    if not valid:return 'invalid'
    return niche.get(x,untagged)
niche=[{'tag':x,'result':decode_tag(x,250,5,{0:'None'},'Some')} for x in range(256)]
assert sum(x['result']=='invalid' for x in niche)==244
assert decode_tag(0,250,5,{0:'None'},'Some')=='None'

# A candidate GlobalAlloc contract, distinct from MiniRust Allocate (which has
# no satisfactory exhaustion branch). A successful realloc invalidates the old
# capability even if the numeric address is unchanged.
def realloc_contract(old, new_size, outcome):
    if new_size <= 0:return {'rejected_precondition':True}
    if outcome=='fail':return {'old_live':True,'old_bytes':old[:],'new':None}
    return {'old_live':False,'new_id':2,'old_id':1,'same_address':outcome=='in-place',
        'new_bytes':old[:new_size]+['Uninit']*max(0,new_size-len(old))}
alloc=[]
for name,size,outcome in [('failure',6,'fail'),('in-place',6,'in-place'),('moved',6,'moved'),
                           ('shrink',2,'moved'),('zero-size',0,'fail')]:
    result=realloc_contract([1,2,3,4],size,outcome)
    alloc.append({'case':name,**result})
assert alloc[0]['old_live'] and alloc[0]['old_bytes']==[1,2,3,4]
assert not alloc[1]['old_live'] and alloc[1]['same_address'] and alloc[1]['new_id']!=alloc[1]['old_id']
assert alloc[1]['new_bytes']==[1,2,3,4,'Uninit','Uninit']
assert alloc[3]['new_bytes']==[1,2] and alloc[4]['rejected_precondition']

print(json.dumps({'arithmetic':arithmetic,'dst':dst,'overlap':overlap,'union_wide_pointer':union,
    'wrapped_niche_domain':{'invalid_count':244,'valid_count':12,'tag0':'None','fallback':'Some'},
    'candidate_realloc_contract':alloc,
    'scope':'Owned selected-rule models; no MiniRust interpreter or compiler import executed'},indent=2))
