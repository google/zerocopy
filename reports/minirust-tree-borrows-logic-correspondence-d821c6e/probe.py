"""Owned table transcription, not execution/import of MiniRust or Miri."""
import itertools, json, platform

ACTIONS = ("LR", "LW", "FR", "FW")

# MiniRust's explicitly split protected/unprotected transition tables.
def mini(s, a):
    perm, prot, used, conflict = s
    if not prot:
        if a == "LR": p = None if perm == "D" else perm
        elif a == "LW": p = None if perm in ("D","F") else ("C" if perm == "C" else "U")
        elif a == "FR": p = "F" if perm == "U" else perm
        else: p = perm if perm in ("C","I") else "D"
        return None if p is None else (p,False,False,False)
    if a == "LR":
        return None if perm == "D" else (perm,True, used or perm in ("R","F"), conflict)
    if a == "LW":
        if perm in ("F","D") or (perm == "R" and conflict): return None
        return ("C",True,False,False) if perm == "C" else ("U",True,True,False)
    if a == "FR":
        if perm == "U": return None
        return (perm,True,used,conflict or perm == "R")
    if perm == "U" or (perm in ("R","F") and used): return None
    return ("C",True,False,False) if perm == "C" else ("D",True,False,False)

# Independent Miri Permission + LocationState reconstruction:
# Permission transition first; accessed bit and ProtectedDisabled check afterward.
def miri(s, a):
    p, protected, accessed, conflicted = s
    local, write = a[0] == "L", a[1] == "W"
    if local:
        if p == "D" or (write and p == "F"): return None
        if write and p == "R" and conflicted and protected: return None
        q = p if not write or p == "C" else "U"
    elif not write:
        q = ("D" if protected else "F") if p == "U" else p
    else:
        q = p if p in ("C","I") else "D"
    now_accessed = accessed or local
    if protected and now_accessed and q == "D": return None
    c = conflicted or (protected and p == "R" and a == "FR")
    return q, protected, now_accessed, c

def normalize(s):
    if s is None: return None
    p, prot, used, conflict = s
    return p, prot, (used if prot and p in ("R","F") else p == "U" and prot), (conflict if prot and p == "R" else False)

initial = [(p,False,False,False) for p in ("C","R","I","U","F","D")]
initial += [("C",True,False,False), ("U",True,True,False), ("D",True,False,False)]
initial += [("R",True,u,c) for u in (False,True) for c in (False,True)]
initial += [("F",True,u,False) for u in (False,True)]
count = 0
for s in initial:
    for n in range(7):
        for trace in itertools.product(ACTIONS, repeat=n):
            x = y = s
            for a in trace:
                x = None if x is None else mini(x,a)
                y = None if y is None else miri(y,a)
                if normalize(x) != normalize(y):
                    raise SystemExit(json.dumps({"unexpected_difference":[s,trace,x,y]}))
            count += 1

def run(s,trace):
    for a in trace: s = None if s is None else mini(s,a)
    return normalize(s)
cells=[(1,2)] # offset,length
frozen=[not any(start <= i < start+length for start,length in cells) for i in range(4)]
permissions=["Frozen" if f else "Cell" for f in frozen]
out = {
 "python":platform.python_version(),
 "scope":"one location, explicit local/foreign actions; no tree traversal, retag, wildcard, release or memory execution",
 "initial_states":len(initial),"traces_per_initial_state":sum(4**n for n in range(7)),
 "traces_checked":count,"differences":0,
 "negative_controls":{
  "protected_reserved_foreign_read_then_write":run(("R",True,True,False),["FR","LW"]),
  "unprotected_reserved_foreign_read_then_write":run(("R",False,False,False),["FR","LW"]),
  "unprotected_reserved_im_foreign_write_then_local_write":run(("I",False,False,False),["FW","LW"]),
  "unprotected_reserved_foreign_write_then_local_write":run(("R",False,False,False),["FW","LW"])
 },
 "freeze_mask":{"size":4,"unsafe_cells":cells,"frozen":frozen,
 "shared_initial_permissions":permissions}
}
print(json.dumps(out,indent=2))

