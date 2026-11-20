import ToyWMM.Rel

/-!
# Events, candidate executions, and axiomatic consistency predicates

A *candidate execution* is a finite set of events `Fin n` together with program order `po`,
reads-from `rf` and coherence `co`; from-reads `fr := rf⁻¹ ; co` is derived. This is the
axiomatic ("execution graph") style of Alglave, Maranget and Tautschnig (*Herding cats*,
TOPLAS 2014), cut down to a toy: one access size, no read-modify-write instructions, no
dependencies, and a single kind of fence (a full fence, modelling x86 `MFENCE`).

Initial values are explicit *initialisation writes* (kind `init`), one per location, which
belong to no thread.
-/

namespace Toy.WMM

/-- Event kinds. `init` is the initialisation write of a location; `fence` is a full fence. -/
inductive Kind where
  | init
  | read
  | write
  | fence
  deriving DecidableEq, Repr, Inhabited

/-- An event: kind, thread id, location and value. For fences, `loc` and `val` are ignored;
for `init` events, `tid` is ignored. For reads, `val` is the value read. -/
structure Event where
  kind : Kind
  tid : Nat
  loc : Nat
  val : Nat
  deriving DecidableEq, Repr, Inhabited

namespace Event

/-- Initialisation write. -/
def isInit (e : Event) : Bool := match e.kind with | .init => true | _ => false
/-- Read. -/
def isRead (e : Event) : Bool := match e.kind with | .read => true | _ => false
/-- Write, including initialisation writes. -/
def isWrite (e : Event) : Bool := match e.kind with | .write | .init => true | _ => false
/-- Fence. -/
def isFence (e : Event) : Bool := match e.kind with | .fence => true | _ => false
/-- Memory access: anything but a fence. -/
def isAccess (e : Event) : Bool := !e.isFence

end Event

/-- A candidate execution with `n` events. No well-formedness is built in; each
well-formedness condition is a separate predicate below, so theorems can name exactly the
conditions they use. -/
structure Exec (n : Nat) where
  /-- The events. -/
  ev : Fin n → Event
  /-- Program order. -/
  po : Rel n
  /-- Reads-from: `rf w r` means read `r` takes its value from write `w`. -/
  rf : Rel n
  /-- Coherence: per-location order of writes. -/
  co : Rel n

namespace Exec

variable {n : Nat} (X : Exec n)

/-! ## Derived relations -/

/-- Same location. -/
def sameLoc (a b : Fin n) : Bool := (X.ev a).loc == (X.ev b).loc

/-- Same thread: both events are non-initialisation events with the same thread id. -/
def sameThread (a b : Fin n) : Bool :=
  !(X.ev a).isInit && !(X.ev b).isInit && (X.ev a).tid == (X.ev b).tid

/-- From-reads `fr := rf⁻¹ ; co`: `fr r w` iff `r` reads from a write `co`-before `w`. -/
def fr : Rel n := fun a b => decide (∃ w : Fin n, X.rf w a = true ∧ X.co w b = true)

/-- External reads-from: `rf` between events not in the same thread (reads from
initialisation writes are external). -/
def rfe : Rel n := fun a b => X.rf a b && !X.sameThread a b

/-- Preserved program order of x86-TSO: `po` between memory accesses, minus all write→read
pairs (`[RW] ; po ; [RW] \ (W × R)`). Fence events are not endpoints of `ppo`; their ordering
effect is carried by `fenceOrd`. -/
def ppo : Rel n := fun a b =>
  X.po a b && (X.ev a).isAccess && (X.ev b).isAccess && !((X.ev a).isWrite && (X.ev b).isRead)

/-- Fence order `[RW] ; po ; [F] ; po ; [RW]`: pairs of memory accesses separated in program
order by a fence. -/
def fenceOrd : Rel n :=
  fun a b => (X.ev a).isAccess && (X.ev b).isAccess &&
    decide (∃ f : Fin n, X.po a f = true ∧ (X.ev f).isFence = true ∧ X.po f b = true)

/-- Program order restricted to memory accesses to the same location. -/
def poLoc : Rel n :=
  fun a b => X.po a b && X.sameLoc a b && (X.ev a).isAccess && (X.ev b).isAccess

/-- The SC relation `po ∪ rf ∪ co ∪ fr`. -/
def scRel : Rel n := fun a b => X.po a b || X.rf a b || X.co a b || X.fr a b

/-- The per-location SC relation `po-loc ∪ rf ∪ co ∪ fr`. -/
def uniprocRel : Rel n := fun a b => X.poLoc a b || X.rf a b || X.co a b || X.fr a b

/-- The x86-TSO global-happens-before relation `ppo ∪ rfe ∪ co ∪ fr ∪ fence`. -/
def tsoRel : Rel n :=
  fun a b => X.ppo a b || X.rfe a b || X.co a b || X.fr a b || X.fenceOrd a b

/-- Restrict a relation to memory accesses: the relation of the execution with its fence
events erased. -/
def eraseFences (r : Rel n) : Rel n := Rel.restrict (fun a => (X.ev a).isAccess) r

/-! ## Consistency predicates -/

/-- Sequential consistency (axiomatic form): `po ∪ rf ∪ co ∪ fr` is acyclic. -/
def SCConsistent : Prop := Rel.Acyclic X.scRel

/-- SC after erasing fence events: the SC relation restricted to memory accesses is acyclic. -/
def SCConsistentErased : Prop := Rel.Acyclic (X.eraseFences X.scRel)

/-- SC per location ("uniproc"): `po-loc ∪ rf ∪ co ∪ fr` is acyclic. -/
def PerLocSC : Prop := Rel.Acyclic X.uniprocRel

/-- The x86-TSO ordering axiom: `ppo ∪ rfe ∪ co ∪ fr ∪ fence` is acyclic. -/
def TsoGhbAcyclic : Prop := Rel.Acyclic X.tsoRel

/-- x86-TSO consistency (axiomatic form): SC per location and the TSO ordering axiom. -/
def TSOConsistent : Prop := X.PerLocSC ∧ X.TsoGhbAcyclic

instance : Decidable X.SCConsistent := inferInstanceAs (Decidable (Rel.Acyclic _))
instance : Decidable X.SCConsistentErased := inferInstanceAs (Decidable (Rel.Acyclic _))
instance : Decidable X.PerLocSC := inferInstanceAs (Decidable (Rel.Acyclic _))
instance : Decidable X.TsoGhbAcyclic := inferInstanceAs (Decidable (Rel.Acyclic _))
instance : Decidable X.TSOConsistent := inferInstanceAs (Decidable (_ ∧ _))

/-! ### A rejected variant: keeping same-location write→read pairs in `ppo` -/

/-- Variant of `ppo` that drops only write→read pairs to *different* locations (it keeps
same-location write→read pairs between memory accesses). -/
def ppoKeepSameLocWR : Rel n :=
  fun a b => X.po a b && (X.ev a).isAccess && (X.ev b).isAccess &&
    !((X.ev a).isWrite && (X.ev b).isRead && !X.sameLoc a b)

/-- TSO-style consistency with `ppoKeepSameLocWR` in place of `ppo`. It implies
`TSOConsistent` (`tsoConsistent_of_tsoConsistentKeepSameLocWR`) and rejects the n6
store-forwarding execution, which is `TSOConsistent`
(`Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden`). -/
def TSOConsistentKeepSameLocWR : Prop :=
  X.PerLocSC ∧ Rel.Acyclic (fun a b =>
    X.ppoKeepSameLocWR a b || X.rfe a b || X.co a b || X.fr a b || X.fenceOrd a b)

instance : Decidable X.TSOConsistentKeepSameLocWR := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Well-formedness conditions (each separate) -/

/-- `po` is irreflexive. -/
def PoIrrefl : Prop := ∀ a, X.po a a = false
/-- `po` is transitive. -/
def PoTrans : Prop := ∀ a b c, X.po a b = true → X.po b c = true → X.po a c = true
/-- `po` only relates events of the same thread (so never initialisation writes). -/
def PoWithinThread : Prop := ∀ a b, X.po a b = true → X.sameThread a b = true
/-- `po` is total on each thread. -/
def PoTotal : Prop :=
  ∀ a b, a ≠ b → X.sameThread a b = true → X.po a b = true ∨ X.po b a = true
/-- `rf` relates events at the same location. -/
def RfSameLoc : Prop := ∀ a b, X.rf a b = true → X.sameLoc a b = true
/-- `rf` goes from a write to a read. -/
def RfKinds : Prop := ∀ a b, X.rf a b = true → (X.ev a).isWrite = true ∧ (X.ev b).isRead = true
/-- A read returns the value of the write it reads from. -/
def RfSameVal : Prop := ∀ a b, X.rf a b = true → (X.ev a).val = (X.ev b).val
/-- Every read reads from some write. -/
def RfTotal : Prop := ∀ b, (X.ev b).isRead = true → ∃ a, X.rf a b = true
/-- Every read reads from at most one write. -/
def RfFunctional : Prop := ∀ a a' b, X.rf a b = true → X.rf a' b = true → a = a'
/-- `co` relates writes at the same location. -/
def CoKinds : Prop :=
  ∀ a b, X.co a b = true →
    (X.ev a).isWrite = true ∧ (X.ev b).isWrite = true ∧ X.sameLoc a b = true
/-- `co` is irreflexive. -/
def CoIrrefl : Prop := ∀ a, X.co a a = false
/-- `co` is transitive. -/
def CoTrans : Prop := ∀ a b c, X.co a b = true → X.co b c = true → X.co a c = true
/-- `co` is total on the writes to each location. -/
def CoTotal : Prop :=
  ∀ a b, a ≠ b → (X.ev a).isWrite = true → (X.ev b).isWrite = true → X.sameLoc a b = true →
    X.co a b = true ∨ X.co b a = true
/-- An initialisation write is `co`-before every other write to its location. -/
def CoInitFirst : Prop :=
  ∀ a b, (X.ev a).isInit = true → (X.ev b).isWrite = true → X.sameLoc a b = true → a ≠ b →
    X.co a b = true

/-- Full well-formedness of a candidate execution: the conjunction of all conditions above. -/
def Wf : Prop :=
  X.PoIrrefl ∧ X.PoTrans ∧ X.PoWithinThread ∧ X.PoTotal ∧
  X.RfSameLoc ∧ X.RfKinds ∧ X.RfSameVal ∧ X.RfTotal ∧ X.RfFunctional ∧
  X.CoKinds ∧ X.CoIrrefl ∧ X.CoTrans ∧ X.CoTotal ∧ X.CoInitFirst

instance : Decidable X.PoIrrefl := inferInstanceAs (Decidable (∀ _, _))
instance : Decidable X.PoTrans := inferInstanceAs (Decidable (∀ _ _ _, _))
instance : Decidable X.PoWithinThread := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.PoTotal := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.RfSameLoc := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.RfKinds := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.RfSameVal := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.RfTotal := inferInstanceAs (Decidable (∀ _, _))
instance : Decidable X.RfFunctional := inferInstanceAs (Decidable (∀ _ _ _, _))
instance : Decidable X.CoKinds := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.CoIrrefl := inferInstanceAs (Decidable (∀ _, _))
instance : Decidable X.CoTrans := inferInstanceAs (Decidable (∀ _ _ _, _))
instance : Decidable X.CoTotal := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.CoInitFirst := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.Wf := inferInstanceAs (Decidable (_ ∧ _))

/-- The well-formedness conditions on `rf` and `co`: all `Wf` conjuncts except the four `po`
conditions (which `po` being the program order of a program, `ExecOf`, implies) and `CoIrrefl`
(which SC per location implies, `coIrrefl_of_perLocSC`). The nine conjuncts are not independent
in the presence of SC per location: together with `PerLocSC`, `RfFunctional` follows from
`RfSameLoc`, `RfKinds` and `CoTotal` (`Exec.rfFunctional_of_perLocSC`), and `CoTrans` follows
from `CoKinds` and `CoTotal` (`Exec.coTrans_of_perLocSC`). -/
def RfCoWf : Prop :=
  X.RfSameLoc ∧ X.RfKinds ∧ X.RfSameVal ∧ X.RfTotal ∧ X.RfFunctional ∧
  X.CoKinds ∧ X.CoTrans ∧ X.CoTotal ∧ X.CoInitFirst

instance : Decidable X.RfCoWf := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Fencing conditions -/

/-- Every `po`-ordered write→read pair is separated in `po` by a fence. -/
def FenceBetweenWR : Prop :=
  ∀ a b, X.po a b = true → (X.ev a).isWrite = true → (X.ev b).isRead = true →
    X.fenceOrd a b = true

/-- Location `l` is accessed (read or written, not counting initialisation writes) by at most
one thread. -/
def LocalLoc (l : Nat) : Prop :=
  ∀ a b, (X.ev a).isAccess = true → (X.ev b).isAccess = true → (X.ev a).isInit = false →
    (X.ev b).isInit = false → (X.ev a).loc = l → (X.ev b).loc = l → (X.ev a).tid = (X.ev b).tid

/-- Every `po`-ordered write→read pair whose write is to a location accessed (excluding
initialisation) by two or more threads is separated in `po` by a fence. -/
def FenceBetweenSharedWR : Prop :=
  ∀ a b, X.po a b = true → (X.ev a).isWrite = true → (X.ev b).isRead = true →
    ¬ X.LocalLoc (X.ev a).loc → X.fenceOrd a b = true

/-- Every `po`-ordered write→read pair whose write *and* read are both to locations accessed
(excluding initialisation) by two or more threads is separated in `po` by a fence. Implied by
`FenceBetweenSharedWR` (`fenceBetweenBothSharedWR_of_fenceBetweenSharedWR`). -/
def FenceBetweenBothSharedWR : Prop :=
  ∀ a b, X.po a b = true → (X.ev a).isWrite = true → (X.ev b).isRead = true →
    ¬ X.LocalLoc (X.ev a).loc → ¬ X.LocalLoc (X.ev b).loc → X.fenceOrd a b = true

/-- `co` relates events at the same location (the location part of `CoKinds`). -/
def CoSameLoc : Prop := ∀ a b, X.co a b = true → X.sameLoc a b = true

instance (l : Nat) : Decidable (X.LocalLoc l) := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.FenceBetweenWR := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.FenceBetweenSharedWR := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.FenceBetweenBothSharedWR := inferInstanceAs (Decidable (∀ _ _, _))
instance : Decidable X.CoSameLoc := inferInstanceAs (Decidable (∀ _ _, _))

theorem fenceBetweenBothSharedWR_of_fenceBetweenSharedWR (h : X.FenceBetweenSharedWR) :
    X.FenceBetweenBothSharedWR :=
  fun a b hab hw hr hsa _ => h a b hab hw hr hsa

theorem coSameLoc_of_coKinds (h : X.CoKinds) : X.CoSameLoc := fun a b hab => (h a b hab).2.2

end Exec

/-! ## Building concrete executions -/

/-- A relation given by an explicit list of index pairs. -/
def mkRel (n : Nat) (edges : List (Nat × Nat)) : Rel n :=
  fun a b => edges.contains (a.val, b.val)

/-- The execution whose events are listed in `evs` (threads listed in program order),
whose `po` is "same thread and earlier in the list", and whose `rf` and `co` are given by
explicit index pairs (`co` must be listed transitively closed). -/
def Exec.ofList (evs : List Event) (rf co : List (Nat × Nat)) : Exec evs.length where
  ev i := evs[i]
  po a b := decide (a.val < b.val) && !(evs[a]).isInit && !(evs[b]).isInit &&
    (evs[a]).tid == (evs[b]).tid
  rf := mkRel _ rf
  co := mkRel _ co

/-- Like `Exec.ofList`, but with `po` also given by explicit index pairs (used for executions
whose `po` is deliberately ill-formed). -/
def Exec.ofListPo (evs : List Event) (po rf co : List (Nat × Nat)) : Exec evs.length where
  ev i := evs[i]
  po := mkRel _ po
  rf := mkRel _ rf
  co := mkRel _ co

/-- Initialisation write of location `l` with value `0`. -/
def Event.initW (l : Nat) : Event := ⟨.init, 0, l, 0⟩
/-- Write by thread `t` of value `v` to location `l`. -/
def Event.W (t l v : Nat) : Event := ⟨.write, t, l, v⟩
/-- Read by thread `t` of location `l`, returning `v`. -/
def Event.R (t l v : Nat) : Event := ⟨.read, t, l, v⟩
/-- Fence in thread `t`. -/
def Event.F (t : Nat) : Event := ⟨.fence, t, 0, 0⟩

end Toy.WMM
