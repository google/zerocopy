#!/usr/bin/env python3
"""Owned transcription of selected MiniRust representation equations.
Not the MiniRust interpreter, rustc, Miri, or a Rust execution.
"""
import itertools, json, platform, sys
from pathlib import Path

# Uninit is None. Init is (data, provenance fragment or None).
# A fragment is (provenance ID, original pointer-byte index).
def init(data, frag=None): return (data, frag)
def byte_le(a, b):
    if a is None: return True
    if b is None or a[0] != b[0]: return False
    return a[1] is None or a[1] == b[1]
def bytes_le(a,b): return len(a)==len(b) and all(map(lambda p: byte_le(*p),zip(a,b)))
def ptr_decode(bs):
    if any(b is None for b in bs): return None
    addr=sum(b[0] << (8*i) for i,b in enumerate(bs))
    p=bs[0][1][0] if bs[0][1] is not None else None
    for i,b in enumerate(bs):
        if b[1] is None or b[1][1] != i or b[1][0] != p: p=None
    return (addr,p)
def ptr_encode(p):
    a,prov=p
    return tuple(init((a>>(8*i))&255,None if prov is None else (prov,i)) for i in range(2))
def decode(ty,bs):
    if ty=="bool":
        return ("bool",bs[0][0]==1) if bs[0] is not None and bs[0][0] in (0,1) else None
    if ty=="u8":
        return ("int",bs[0][0]) if bs[0] is not None else None
    if ty=="ptr":
        p=ptr_decode(bs); return None if p is None else ("ptr",p)
    if ty=="padded": return decode("u8",bs[:1])
    if ty=="array":
        vals=[decode("u8",bs[i:i+1]) for i in range(2)]
        return None if None in vals else ("array",tuple(vals))
    if ty=="union": return ("union",(bs[0],)) # one preserved chunk, one gap
    if ty=="enum":
        if bs[0] is None or bs[0][0] not in (0,1): return None
        tag=bs[0][0]; val=decode("u8" if tag==0 else "bool",bs[1:])
        return None if val is None else ("enum",tag,val)
    raise ValueError(ty)
def encode(ty,v):
    if ty=="bool": return (init(int(v[1])),)
    if ty=="u8": return (init(v[1]),)
    if ty=="ptr": return ptr_encode(v[1])
    if ty=="padded": return encode("u8",v)+(None,)
    if ty=="array": return tuple(b for x in v[1] for b in encode("u8",x))
    if ty=="union": return (v[1][0],None)
    if ty=="enum": return (init(v[1]),)+encode("u8" if v[1]==0 else "bool",v[2])
    raise ValueError(ty)
def value_le(a,b):
    if a is None: return True
    if b is None or a[0]!=b[0]: return False
    if a[0]=="ptr": return a[1][0]==b[1][0] and (a[1][1] is None or a[1][1]==b[1][1])
    if a[0]=="union": return bytes_le(a[1],b[1])
    if a[0]=="array": return all(value_le(x,y) for x,y in zip(a[1],b[1]))
    if a[0]=="enum": return a[1]==b[1] and value_le(a[2],b[2])
    return a==b

alphabet=[None]+[init(d,p) for d in (0,1,2,255)
               for p in (None,("A",0),("A",1),("B",0),("B",1))]
types={"bool":1,"u8":1,"ptr":2,"padded":2,"array":2,"union":2,"enum":2}
results={"kind":"owned-equation-model","python":sys.version.split()[0],
         "platform":platform.platform(),"alphabet_size":len(alphabet),
         "checks":{},"counterexamples":{},"mutants":{}}
failures=[]
for ty,n in types.items():
    vectors=list(itertools.product(alphabet,repeat=n))
    accepted=0
    for bs in vectors:
        v=decode(ty,bs)
        if v is not None:
            accepted+=1
            enc=encode(ty,v)
            if not bytes_le(enc,bs): failures.append([ty,"deflation",repr(bs)])
            if decode(ty,enc)!=v: failures.append([ty,"roundtrip",repr(v)])
    # Exhaust exactly all pointwise ordered pairs over the stated alphabet.
    pairs=[(a,b) for a in alphabet for b in alphabet if byte_le(a,b)]
    order_pairs=0
    for ps in itertools.product(pairs,repeat=n):
        lo=tuple(p[0] for p in ps); hi=tuple(p[1] for p in ps)
        if not value_le(decode(ty,lo),decode(ty,hi)):
            failures.append([ty,"decode-monotone",repr(lo),repr(hi)])
        order_pairs+=1
    results["checks"][ty]={"byte_vectors":len(vectors),"accepted":accepted,
                           "ordered_pairs":order_pairs,
                           "laws":["decode(encode(decoded_value))=decoded_value",
                                   "encode(decode(bytes))<=bytes",
                                   "decode monotone"]}
# Complete one-byte Boolean validity, not just the small alphabet.
fullbool=[init(d,p) for d in range(256) for p in (None,("A",0),("B",0))]
results["checks"]["bool_full"]={"initialized_cases":len(fullbool),
  "valid":sum(decode("bool",(b,)) is not None for b in fullbool),
  "uninit_valid":decode("bool",(None,)) is not None}
# Complete 16-bit value roundtrip for three provenance choices.
ptrround=0
for a in range(65536):
    for p in (None,"A","B"):
        if ptr_decode(ptr_encode((a,p))) != (a,p):
            failures.append(["ptr","full-roundtrip",a,p])
        ptrround+=1
results["checks"]["ptr_full_value_roundtrips"]=ptrround

pointer=ptr_encode((0x0101,"A"))
missing=(pointer[0],init(pointer[1][0]))
reordered=(pointer[1],pointer[0])
mixed=(pointer[0],init(pointer[1][0],("B",1)))
integer_route=tuple(init(b[0]) for b in pointer)
results["counterexamples"]["pointer_routes"]={
 "original":ptr_decode(pointer),"missing":ptr_decode(missing),
 "reordered":ptr_decode(reordered),"mixed":ptr_decode(mixed),
 "integer_load_store":ptr_decode(integer_route),
 "byte_copy":ptr_decode(tuple(pointer))}
padded=(init(7),init(99))
typed=encode("padded",decode("padded",padded))
results["counterexamples"]["padding"]={
 "typed_value_equal":decode("padded",padded)==decode("padded",typed),
 "byte_copy_then_u8_padding":decode("u8",padded[1:]),
 "typed_copy_then_u8_padding":decode("u8",typed[1:]),
 "typed_bytes_le_original":bytes_le(typed,padded)}
# Negative controls detect tempting incorrect equations.
results["mutants"]["require_byte_roundtrip_equality_killed"]=typed != padded
results["mutants"]["ignore_fragment_positions_killed"]=(
    ptr_decode(reordered)[1] is None and reordered[0][1][0]==reordered[1][1][0])
results["mutants"]["integer_route_preserves_provenance_killed"]=(
    ptr_decode(integer_route)[1] is None and ptr_decode(pointer)[1]=="A")
results["mutants"]["all_initialized_bytes_valid_bool_killed"]=decode("bool",(init(2),)) is None
# Toy exposed provenance compatibility: both IDs have the same numeric address.
permissions={"A":False,"B":True,None:False}
results["counterexamples"]["exposed_tags"]={
 "address":257,"tags":["A","B"],"existential_usable":any(permissions[p] for p in ("A","B")),
 "all_usable":all(permissions[p] for p in ("A","B")),
 "only_invalidated_exposed":permissions["A"],
 "wildcard_address_only_would_accept":True}
results["failures"]=failures
results["status"]="pass" if not failures and all(results["mutants"].values()) else "fail"
Path("results.json").write_text(json.dumps(results,indent=2)+"\n")
print(json.dumps({"status":results["status"],"checks":results["checks"],"mutants":results["mutants"]},indent=2))
sys.exit(0 if results["status"]=="pass" else 1)

