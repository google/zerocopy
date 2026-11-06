"""Bounded source-formula and toy litmus probes, not upstream executions."""
import itertools,json,platform
def races(x,y):
 a,n,w,atomic=x;b,m,v,atomic2=y
 if not w and not v:return False
 if atomic and atomic2:return False
 return a+n>b and b+m>a
def set_race(x,y):
 a,n,w,atomic=x;b,m,v,atomic2=y
 return (w or v) and not (atomic and atomic2) and bool(set(range(a,a+n)) & set(range(b,b+m)))
accesses=list(itertools.product(range(5),range(4),(False,True),(False,True)))
diff=[]
for x in accesses:
 for y in accesses:
  if races(x,y)!=set_race(x,y):diff.append([x,y])
# Every linear extension of Wx;Wf and Rf;Rx under a single latest-value SC heap.
sc=set();schedules=0
for seq in itertools.permutations(("Wx","Wf","Rf","Rx")):
 if seq.index("Wx")>seq.index("Wf") or seq.index("Rf")>seq.index("Rx"):continue
 x=f=0;rf=rx=None
 for op in seq:
  if op=="Wx":x=42
  elif op=="Wf":f=1
  elif op=="Rf":rf=f
  else:rx=x
 sc.add((rf,rx));schedules+=1
# Explicit toy view model: choosing flag=1 observes producer data iff rel/acq.
# Coherence plus the imported view lower-bound constrains the subsequent data read.
def toy(rel,acq):
 return [(1,data) for data in (0,42) if not (rel and acq and data==0)]
# Current one-step detector sees only adjacent access steps:
separated=[(0,(1,1,True,False)),(1,(4,1,False,False)),(2,(1,1,False,False))]
adjacent=[races(separated[i][1],separated[i+1][1]) for i in range(2)]
print(json.dumps({"python":platform.python_version(),"access_domain":len(accesses),
 "ordered_access_pairs_checked":len(accesses)**2,"byte_set_overlap_disagreements":len(diff),
 "every_disagreement_has_an_empty_interval":all(x[1]==0 or y[1]==0 for x,y in diff),
 "first_disagreement":diff[0],
 "examples":{"zero_interior":races((2,0,False,False),(1,2,True,False)),
 "zero_boundary":races((1,0,False,False),(1,2,True,False)),
 "mixed_atomic_nonatomic_reads":races((1,1,False,True),(1,1,False,False)),
 "both_atomic_partial_overlap":races((1,2,True,True),(2,2,True,True))},
 "sc_message_passing":{"schedules":schedules,"outcomes":sorted(sc),"flag1_data0":(1,0) in sc},
 "toy_view_message_passing":{"rlx_rlx":toy(False,False),"release_acquire":toy(True,True),
 "scope":"illustrates one view-transfer premise; not an ORC11/RC11 interpreter"},
 "previous_step_only":{"separated_conflicts":separated,"adjacent_races":adjacent,
 "nonadjacent_pair_races":races(separated[0][1],separated[2][1]),
 "scope":"per-schedule observation; not a universal counterexample to all scheduler choices"}},
 indent=2))

