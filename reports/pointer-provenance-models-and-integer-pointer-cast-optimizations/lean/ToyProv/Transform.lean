import ToyProv.Basic

/-!
# Program points, transformations, and soundness

A *transformation* is a relation `T m src tgt` saying that, in model `m`, an optimizer may
rewrite `src` into `tgt`. Side conditions that depend on run-time values are stated
semantically, over every UB-free state reachable at the rewrite point (`AllAfter`), and are
therefore evaluated in the same model as the soundness question. A transformation is *sound* in
`m` if every rewrite it allows is a refinement in `m`.
-/

namespace Toy.Prov

/-- UB-free states reachable by running `pre` from `init` (all resolutions of nondeterminism). -/
def after (m : Model) (pre : Prog) : List St :=
  (exec m pre init).filterMap id

/-- The state predicate `c` holds in every UB-free state reachable after `pre`. This is how a
transformation's run-time side condition at the point between `pre` and the rewritten
instruction is expressed. -/
def AllAfter (m : Model) (pre : Prog) (c : St → Bool) : Prop :=
  ∀ s ∈ after m pre, c s = true

instance (m : Model) (pre : Prog) (c : St → Bool) : Decidable (AllAfter m pre c) := by
  unfold AllAfter; infer_instance

/-! ## State predicates used as side conditions -/

/-- Registers `p` and `q` both hold pointers with the same address (what `ptrEq` tests). -/
def addrEqC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some (.ptr x), some (.ptr y) => x.addr == y.addr
  | _, _ => false

/-- Registers `p` and `q` both hold pointers whose provenances (if any) are in the exposed
set. -/
def bothExposedC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some (.ptr x), some (.ptr y) =>
    x.prov.toList.all (s.exposed.contains ·) && y.prov.toList.all (s.exposed.contains ·)
  | _, _ => false

/-- Registers `p` and `q` hold identical values (same kind, same address, same provenance). -/
def sameValC (p q : Reg) (s : St) : Bool :=
  match s.regs p, s.regs q with
  | some v, some w => decide (v = w)
  | _, _ => false

/-- Register `k` holds the integer equal to the address of the pointer in register `p`
(what `intEq k (ptr2int p)` would test). -/
def intIsAddrOfC (k p : Reg) (s : St) : Bool :=
  match s.regs k, s.regs p with
  | some (.int a), some (.ptr x) => a == x.addr
  | _, _ => false

/-- The `int2ptr` candidates for `p`'s address are exactly `p`'s own provenance: either `[A]`
when `p` has provenance `A`, or `[]` when `p` has none. -/
def candEqProvC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) => decide (candidates s x.addr = x.prov.toList)
  | _ => false

/-- Every `int2ptr` candidate for `p`'s address is `p`'s own provenance (there may be none). -/
def candSubProvC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) => (candidates s x.addr).all (fun c => decide (some c = x.prov))
  | _ => false

/-- `p` has a provenance that is itself an `int2ptr` candidate for `p`'s address (exposed, live,
address in its closed range). -/
def provIsCandC (p : Reg) (s : St) : Bool :=
  match s.regs p with
  | some (.ptr x) =>
    match x.prov with
    | some A => (candidates s x.addr).contains A
    | none => false
  | _ => false

/-- Register `r` holds a pointer. -/
def isPtrC (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.ptr _) => true
  | _ => false

/-- Register `r` holds an integer. -/
def isIntC (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.int _) => true
  | _ => false

/-- Registers `r` and `a` hold pointers with different provenance (`none` counts as a
provenance value, so two provenance-less pointers do *not* satisfy this). This is the
judgement of a provenance-based alias analysis: accesses through pointers of different
provenance cannot touch the same byte unless one of them is UB. -/
def provNeC (r a : Reg) (s : St) : Bool :=
  match s.regs r, s.regs a with
  | some (.ptr x), some (.ptr y) => decide (x.prov ≠ y.prov)
  | _, _ => false

/-- Register `r` holds a pointer through which a one-byte access is allowed in model `m`: in
`strict`/`exposed` its provenance is a live allocation with `base ≤ address < base + size` (the
start is included, one-past-the-end excluded); in `flat`, some live allocation meets those bounds. -/
def inBoundsC (m : Model) (r : Reg) (s : St) : Bool :=
  match s.regs r with
  | some (.ptr x) => canAccess m s x 1
  | _ => false

/-! ## Syntactic operations on instructions -/

/-- Register renaming used by `Instr.substUse`. -/
def subReg (q p r : Reg) : Reg := if r = q then p else r

/-- Replace every *read* of register `q` by a read of `p`; destination registers are unchanged. -/
def Instr.substUse (q p : Reg) : Instr → Instr
  | .alloc d n => .alloc d n
  | .free r => .free (subReg q p r)
  | .load d ty r => .load d ty (subReg q p r)
  | .store r v => .store (subReg q p r) (subReg q p v)
  | .memcpy d r n => .memcpy (subReg q p d) (subReg q p r) n
  | .ptr2int d r => .ptr2int d (subReg q p r)
  | .int2ptr d r => .int2ptr d (subReg q p r)
  | .ptrEq d r t => .ptrEq d (subReg q p r) (subReg q p t)
  | .intEq d r t => .intEq d (subReg q p r) (subReg q p t)
  | .offset d r k => .offset d (subReg q p r) k
  | .const d n => .const d n
  | .copy d r => .copy d (subReg q p r)
  | .obs r => .obs (subReg q p r)

/-- Does the instruction read register `x`? -/
def Instr.reads (x : Reg) : Instr → Bool
  | .alloc _ _ => false
  | .free r => r == x
  | .load _ _ r => r == x
  | .store r v => r == x || v == x
  | .memcpy d r _ => d == x || r == x
  | .ptr2int _ r => r == x
  | .int2ptr _ r => r == x
  | .ptrEq _ r t => r == x || t == x
  | .intEq _ r t => r == x || t == x
  | .offset _ r _ => r == x
  | .const _ _ => false
  | .copy _ r => r == x
  | .obs r => r == x

/-! ## Transformations

Each is stated with an explicit split `src = pre ++ i :: post` of the source program; `pre` is
the code before the rewrite point and the side condition is checked on every state reachable
after `pre`. -/

/-- Soundness of a transformation in a model: every rewrite it allows is a refinement. -/
def Sound (m : Model) (T : Model → Prog → Prog → Prop) : Prop :=
  ∀ src tgt, T m src tgt → Refines m tgt src

/-- **Address-equality substitution** (GVN on pointers justified by `p == q`): replace the reads
of `q` in one instruction by reads of `p`, when `p` and `q` hold pointers with equal addresses in
every reachable state at that point. -/
def SubstAddrEq (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (addrEqC p q)

/-- **Integer-equality substitution of pointers**: as `SubstAddrEq`, but additionally both
pointers' provenances are exposed at that point, as they are after the program has cast both
to integers and found the integers equal (`(int)p == (int)q`). -/
def SubstIntEq (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (fun s => addrEqC p q s && bothExposedC p q s)

/-- **Identical-value substitution**: replace reads of `q` by reads of `p` when the two
registers hold identical values (for integers this is integer GVN; for pointers it requires
equal provenance as well as equal address). -/
def SubstSameVal (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (sameValC p q)

/-- **In-bounds address-equality substitution**: as `SubstAddrEq`, but additionally both
pointers are in bounds of a live allocation (`inBoundsC`: `base ≤ address < base + size`) in
every reachable state at that point. -/
def SubstAddrEqInBounds (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre i post q p, src = pre ++ i :: post ∧ tgt = pre ++ i.substUse q p :: post ∧
    AllAfter m pre (fun s => addrEqC p q s && inBoundsC m p s && inBoundsC m q s)

/-- **Cast folding** `d := int2ptr k` ⟶ `d := p`, justified by `k == (int)p` at that point
(this covers the round-trip fold `int2ptr(ptr2int p) ⟶ p`). -/
def Int2ptrToCopy (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .int2ptr d k :: post ∧ tgt = pre ++ .copy d p :: post ∧
    AllAfter m pre (intIsAddrOfC k p)

/-- **Cast introduction** `d := p` ⟶ `d := int2ptr k`, justified by `k == (int)p` (the reverse
of `Int2ptrToCopy`: replacing a pointer by the round trip through an equal integer). -/
def CopyToInt2ptr (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .copy d p :: post ∧ tgt = pre ++ .int2ptr d k :: post ∧
    AllAfter m pre (intIsAddrOfC k p)

/-- **Cast introduction with a candidate** `d := p` ⟶ `d := int2ptr k`: as `CopyToInt2ptr`, but
additionally `p`'s provenance is an `int2ptr` candidate for its address (`provIsCandC`: exposed,
live, address in its closed range) in every reachable state at that point. -/
def CopyToInt2ptrIfCand (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d k p, src = pre ++ .copy d p :: post ∧ tgt = pre ++ .int2ptr d k :: post ∧
    AllAfter m pre (intIsAddrOfC k p) ∧ AllAfter m pre (provIsCandC p)

/-- **Dead-cast elimination**: delete `d := ptr2int p` when `p` holds a pointer at that point
(so the cast itself is not UB) and no later instruction reads `d`. -/
def DropUnusedPtr2int (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post d p, src = pre ++ .ptr2int d p :: post ∧ tgt = pre ++ post ∧
    (∀ i ∈ post, i.reads d = false) ∧ AllAfter m pre (isPtrC p)

/-- **Store-to-load forwarding across a store through a freshly cast pointer**:
`r := int2ptr k; store a v; store r w; x := load int a` ⟶ the same with the load replaced by
`x := v`, when `v` holds an integer. The optimizer's assumption is that a pointer obtained from
an integer does not alias `a`. -/
def ForwardAcrossCast (m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post r k a v w x, r ≠ a ∧ r ≠ v ∧
    src = pre ++ [.int2ptr r k, .store a v, .store r w, .load x .int a] ++ post ∧
    tgt = pre ++ [.int2ptr r k, .store a v, .store r w, .copy x v] ++ post ∧
    AllAfter m pre (isIntC v)

/-- **Dead-store elimination across a load through a freshly cast pointer**:
`r := int2ptr k; store a v; x := load ty r; store a w` ⟶ the same without `store a v`. The
optimizer's assumption is that the load through `r` cannot observe the first store. -/
def DSEAcrossCast (_m : Model) (src tgt : Prog) : Prop :=
  ∃ pre post r k a v x ty w, r ≠ a ∧ r ≠ v ∧ x ≠ a ∧
    src = pre ++ [.int2ptr r k, .store a v, .load x ty r, .store a w] ++ post ∧
    tgt = pre ++ [.int2ptr r k, .load x ty r, .store a w] ++ post

/-- Semantic ordering of models on one program: `m₁`'s behaviour of `P` refines `m₂`'s (either
`P` has UB in `m₂`, or every `m₁` behaviour is an `m₂` behaviour). "`m₂` has more UB." -/
def SemRefines (m₁ m₂ : Model) (P : Prog) : Prop :=
  Outcome.ub ∈ beh m₂ P ∨ ∀ o ∈ beh m₁ P, o ∈ beh m₂ P

instance (m₁ m₂ : Model) (P : Prog) : Decidable (SemRefines m₁ m₂ P) := by
  unfold SemRefines; infer_instance

end Toy.Prov
