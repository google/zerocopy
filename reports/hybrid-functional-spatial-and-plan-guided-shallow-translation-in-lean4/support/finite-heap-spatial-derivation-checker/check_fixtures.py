#!/usr/bin/env python3
"""Data-only grammar loader: generates only fixed constructors and bounded literals."""
import copy, hashlib, json, os, subprocess, time
from pathlib import Path
HERE=Path(__file__).resolve().parent
LEAN=Path(os.environ['LEAN_BINARY']).resolve()
# The caller explicitly selects the checker; the helper installs no toolchain.
def nat(x):
    if type(x)!=int or not 0<=x<=1000000:raise ValueError('bounded natural required')
    return str(x)
def vector(v):
    if type(v)!=list or len(v)!=3:raise ValueError('exact vector length 3 required')
    return '#v['+','.join('none' if x is None else '(some '+nat(x)+')' for x in v)+']'
def addr(a):
    if type(a)!=int or not 0<=a<3:raise ValueError('address outside selected domain')
    return str(a)
def term(c,depth=0):
    if depth>16 or type(c)!=list or not c:raise ValueError('grammar/depth')
    tag=c[0]
    if tag=='split' and len(c)==4:return '(.split '+vector(c[1])+' '+vector(c[2])+' '+vector(c[3])+')'
    if tag=='pair' and len(c)==6:return '(.unfoldPair '+addr(c[1])+' '+addr(c[2])+' '+nat(c[3])+' '+nat(c[4])+' '+vector(c[5])+')'
    if tag=='update' and len(c)==8:
        return '(.update ⟨'+','.join([*(vector(x) for x in c[1:5]),addr(c[5]),nat(c[6]),nat(c[7])])+'⟩)'
    if tag=='seq' and len(c)==3:return '(.seq '+term(c[1],depth+1)+' '+term(c[2],depth+1)+')'
    raise ValueError('unknown constructor/arity')
before=[7,11,99];after=[7,12,99];owned=[None,11,None];frame=[7,None,99]
update=['update',before,after,owned,frame,1,11,12]
split=['split',owned,frame,before]
fixtures=[('good-update',update,True),('good-chain',['seq',split,update],True)]
for name,index,value in [('overlap',4,before),('damaged-frame',2,[8,12,99]),('wrong-old',6,10),('missing-owned',3,[None,None,None]),('out-of-domain',5,3)]:
    mutant=copy.deepcopy(update);mutant[index]=value;fixtures.append((name,mutant,False))
fixtures += [('unlinked',['seq',['pair',0,1,7,11,[7,11,None]],update],False),('wrong-original', ['update',[7,11,0],[7,12,0],owned,[7,None,0],1,11,12],False),('unknown',['axiom','False'],False)]
env={**os.environ,'LEAN_PATH':str(HERE)}
base=subprocess.run([str(LEAN),'-o','Heap.olean','Heap.lean'],cwd=HERE,capture_output=True,text=True)
(HERE/'heap-build.stdout').write_text(base.stdout);(HERE/'heap-build.stderr').write_text(base.stderr)
assert base.returncode==0 and 'sorryAx' not in base.stdout
results=[]
for name,data,expected in fixtures:
    (HERE/(name+'.json')).write_text(json.dumps(data)+'\n')
    try:body=term(data)
    except ValueError as e:
        assert not expected
        results.append({'case':name,'status':'loader-rejected','reason':str(e)});continue
    src='''import Heap
open FiniteHeap
def candidate : Cert 3 := BODY
def acceptDecision : Bool := check candidate && writesOnly 1 candidate && decide (input candidate = meaning before ∧ output candidate = meaning after)
theorem observed : acceptDecision = EXPECTED := by decide
#print axioms observed
#eval acceptDecision
'''.replace('BODY',body).replace('EXPECTED','true' if expected else 'false')
    if expected:src+='''theorem consumer_frame : Unchanged (meaning before) (meaning after) 1 := by
  have core := certificate_frame candidate 1 (by decide) (by decide)
  have i : input candidate = meaning before := by decide
  have o : output candidate = meaning after := by decide
  simpa only [i,o] using core
#print axioms consumer_frame
'''
    file=HERE/(name+'.lean');file.write_text(src)
    t=time.perf_counter();r=subprocess.run([str(LEAN),file.name],cwd=HERE,env=env,capture_output=True,text=True)
    (HERE/(name+'.stdout')).write_text(r.stdout);(HERE/(name+'.stderr')).write_text(r.stderr)
    assert r.returncode==0 and 'sorryAx' not in r.stdout,(name,r.stdout,r.stderr)
    results.append({'case':name,'status':'kernel-observation','expected':expected,'returncode':r.returncode,'elapsed_ms':round(1000*(time.perf_counter()-t),3),'stdout':r.stdout,'stderr':r.stderr,'generated_sha256':hashlib.sha256(src.encode()).hexdigest()})
(HERE/'fixture-results.json').write_text(json.dumps({'lean':str(LEAN),'results':results,'kernel_frontier':'4.31 omitted nested-parameter validation path known; controlled generated data observations only, no arbitrary-producer assurance.'},indent=2)+'\n')
print(json.dumps({'cases':len(results),'loader_rejected':sum(r['status']=='loader-rejected' for r in results),'kernel_observations':sum(r['status']=='kernel-observation' for r in results)},indent=2))
