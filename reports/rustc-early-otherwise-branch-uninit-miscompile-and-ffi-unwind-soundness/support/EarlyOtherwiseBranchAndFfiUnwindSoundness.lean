import Lean

/-!
# Read hoisting in `EarlyOtherwiseBranch`, `SimplifyComparisonIntegral`, and
# `required_panic_strategy` linking: a small mechanized model

This file is a self-contained Lean 4 development (it imports only the `Lean`
package, and uses that import solely for the audit command at the very end).
It models three rustc mechanisms at the level of detail needed to state, and
kernel-check, the following facts.

* **Part 1 (`EarlyOtherwiseBranch`).** The pass rewrites

  ```text
  parent: switchInt(Q) -> [c1: child1, ..., otherwise: dest]
  childi: switchInt(copy P) -> [ci: thenBlocki, otherwise: dest]
  ```

  into

  ```text
  parent: _t = Ne(Q, copy P); switchInt(move _t) -> [0: bbEq, otherwise: dest]
  bbEq:   switchInt(Q) -> [c1: thenBlock1, ..., otherwise: dest]
  ```

  The rewritten parent reads `P` on every path, including the path on which
  `Q` matches no arm. The original program reads `P` only when `Q` matches an
  arm. `eob_refines_iff` shows that, for one machine state, the rewrite is a
  refinement exactly when `P` is initialized or `Q` matches an arm;
  `eob_repaired_definite_init_sound_iff` lifts this to a set of reachable
  states; `eob_current_guard_introduces_uninit_and_deadLocal_ub` exhibits the
  concrete counterexample that the syntactic "stable offset" guard accepts.

* **Part 2 (`SimplifyComparisonIntegral`).** The pass rewrites
  `_t = Eq/Ne(move _x, const K); ...; switchInt(_t)` into
  `_t = Eq/Ne(copy _x, const K); ...; switchInt(copy _x)`.
  `simplifyComparisonIntegral_sound_iff` shows the rewrite refines the
  original exactly when no storage marker of `_x` sits between the comparison
  and the terminator. Two further theorems treat the variant that keeps the
  `move`: it is unsound when a move de-initializes its source, and sound when
  it does not.

* **Part 3 (`required_panic_strategy`).** A link is a list of crates, each
  compiled with one panic strategy. `crossCrateLink_no_uncaught_foreign_unwind_in_abort_crate`
  shows that when the final strategy is `abort`, a panic-runtime crate is
  part of the link, and the link check accepts, no function body lets an
  unwind escape and no unwind reaches a call site compiled as non-unwinding.
  Two counterexamples show what happens when the check is skipped.

Everything here is a model. Each definition states which rustc behavior it
abstracts; none of it is extracted from rustc.
-/

set_option autoImplicit false

namespace EobFfi

/-! ## Part 0. Shared vocabulary -/

/-- Why an execution has undefined behavior. -/
inductive Ub where
  /-- A scalar operand was read from storage that is live but not initialized. -/
  | uninitRead
  /-- A local without live storage was accessed. -/
  | deadLocal
  /-- A value that is not valid at its type was read (for instance an enum
  whose tag byte is not a declared discriminant). -/
  | invalidValue
  /-- A load went through a pointer that is not dereferenceable. -/
  | danglingDeref
  /-- An `Unreachable` terminator was executed. -/
  | unreachableExecuted
  deriving DecidableEq

/-- The state of the memory a scalar place denotes. -/
inductive Slot where
  /-- The local has no live storage. -/
  | dead
  /-- Storage is live, contents are not initialized. -/
  | uninit
  /-- Storage holds bytes that are not a valid value at the place's type. -/
  | invalid
  /-- The place is `*ptr` and `ptr` is not dereferenceable. -/
  | dangling
  /-- Storage holds the valid scalar `v`. -/
  | init (v : Nat)
  deriving DecidableEq

/-- Result of running a fragment: undefined behavior, or a value. -/
inductive Outcome (α : Type) where
  | ub (why : Ub)
  | ok (a : α)

/-- Reading a place as a scalar operand. -/
def Slot.read : Slot → Outcome Nat
  | .dead => .ub .deadLocal
  | .uninit => .ub .uninitRead
  | .invalid => .ub .invalidValue
  | .dangling => .ub .danglingDeref
  | .init v => .ok v

/-- Whether the slot holds a valid value. -/
def Slot.isInit : Slot → Bool
  | .init _ => true
  | _ => false

/-- `Refines src tgt`: the transformed fragment `tgt` is an acceptable
replacement for `src`. If the source has undefined behavior, anything goes;
otherwise the target must produce the same result. -/
def Refines {α : Type} (src tgt : Outcome α) : Prop :=
  match src with
  | .ub _ => True
  | .ok a => tgt = .ok a

theorem Refines.refl {α : Type} (o : Outcome α) : Refines o o := by
  cases o with
  | ub u => exact True.intro
  | ok a => exact rfl

theorem Refines.trans {α : Type} {a b c : Outcome α}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c := by
  cases a with
  | ub u => exact True.intro
  | ok x =>
    have hb : b = .ok x := hab
    subst hb
    exact hbc

theorem refines_of_source_ub {α : Type} (u : Ub) (t : Outcome α) :
    Refines (.ub u) t := True.intro

/-- A defined source run is never refined by an undefined target run. -/
theorem not_refines_ok_ub {α : Type} {a : α} {u : Ub} :
    ¬ Refines (Outcome.ok a) (Outcome.ub u) := by
  intro h
  cases h

theorem Slot.read_init (v : Nat) : (Slot.init v).read = .ok v := rfl

theorem Slot.isInit_iff {s : Slot} : s.isInit = true ↔ ∃ v, s = .init v := by
  cases s with
  | init v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩
  | dead => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | uninit => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | invalid => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | dangling => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩

/-- Reading a slot that does not hold a valid value is undefined. -/
theorem Slot.read_ub_of_not_init {s : Slot} (h : s.isInit = false) :
    ∃ u, s.read = .ub u := by
  cases s with
  | init v => cases h
  | dead => exact ⟨_, rfl⟩
  | uninit => exact ⟨_, rfl⟩
  | invalid => exact ⟨_, rfl⟩
  | dangling => exact ⟨_, rfl⟩

/-! ## Part 1. `EarlyOtherwiseBranch` -/

/-- Basic-block names. -/
abbrev Block := Nat

/-- The arms of the parent `switchInt`. An entry `(c, tgt)` stands for the
parent arm `c => child_c` together with the child block
`child_c: switchInt(copy P) -> [c: tgt, otherwise: dest]`. The pass requires
each child to have exactly one arm whose value equals the parent arm's value. -/
abbrev Arms := List (Nat × Block)

/-- The block reached when the parent value `q` selects an arm and the child
value also equals `q`; `none` when `q` selects the parent's `otherwise`. -/
def armTarget (arms : Arms) (q : Nat) : Option Block := arms.lookup q

/-- The original control flow when the parent's `otherwise` edge is a
reachable block `dest`. `q` is the value of the parent operand `Q`; `p` is the
state of the child place `P` at the end of the parent block. `P` is read only
when `q` selects an arm. -/
def runOrig (arms : Arms) (dest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match armTarget arms q with
  | none => .ok dest
  | some tgt =>
    match p.read with
    | .ub u => .ub u
    | .ok v => if v = q then .ok tgt else .ok dest

/-- The control flow after the pass. `P` is read unconditionally at the end
of the parent block to compute `_t = Ne(Q, copy P)`. -/
def runEob (arms : Arms) (dest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match p.read with
  | .ub u => .ub u
  | .ok v =>
    if v = q then
      match armTarget arms q with
      | none => .ok dest
      | some tgt => .ok tgt
    else .ok dest

/-- When `P` holds a valid value the two control flows agree. -/
theorem eob_agree_on_init (arms : Arms) (dest : Block) (q v : Nat) :
    runEob arms dest q (.init v) = runOrig arms dest q (.init v) := by
  unfold runEob runOrig
  simp only [Slot.read]
  cases armTarget arms q with
  | none =>
    cases Nat.decEq v q with
    | isTrue h => simp [h]
    | isFalse h => simp [h]
  | some tgt => rfl

/-- On the `otherwise` path with `P` not initialized, the original program
reaches `dest` and the transformed program has undefined behavior. -/
theorem eob_otherwise_path_not_init (arms : Arms) (dest : Block) (q : Nat) (p : Slot)
    (hq : armTarget arms q = none) (hp : p.isInit = false) :
    runOrig arms dest q p = .ok dest ∧ ∃ u, runEob arms dest q p = .ub u := by
  obtain ⟨u, hu⟩ := Slot.read_ub_of_not_init hp
  refine ⟨?_, u, ?_⟩
  · simp [runOrig, hq]
  · simp [runEob, hu]

/-- Pointwise characterization: for one state `(q, p)`, the transformed
control flow refines the original exactly when `p` is initialized or `q`
selects an arm. -/
theorem eob_refines_iff (arms : Arms) (dest : Block) (q : Nat) (p : Slot) :
    Refines (runOrig arms dest q p) (runEob arms dest q p) ↔
      (armTarget arms q = none → p.isInit = true) := by
  constructor
  · intro h hq
    cases hp : p.isInit with
    | true => rfl
    | false =>
      obtain ⟨hO, u, hE⟩ := eob_otherwise_path_not_init arms dest q p hq hp
      rw [hO, hE] at h
      exact absurd h not_refines_ok_ub
  · intro h
    cases hp : p.isInit with
    | true =>
      obtain ⟨v, hv⟩ := Slot.isInit_iff.mp hp
      subst hv
      rw [eob_agree_on_init]
      exact Refines.refl _
    | false =>
      obtain ⟨u, hu⟩ := Slot.read_ub_of_not_init hp
      cases hq : armTarget arms q with
      | none =>
        have hinit := h hq
        rw [hp] at hinit
        cases hinit
      | some tgt =>
        have hO : runOrig arms dest q p = .ub u := by simp [runOrig, hq, hu]
        rw [hO]
        exact True.intro

/-- **Repaired pass, bidirectional soundness.** Let `R q p` describe the
states that can reach the end of the parent block (`q` the parent operand,
`p` the state of the child place). The rewrite refines the original program
on every reachable state if and only if the child place is initialized on
every reachable state that takes the parent's `otherwise` edge. -/
theorem eob_repaired_definite_init_sound_iff (arms : Arms) (dest : Block)
    (R : Nat → Slot → Prop) :
    (∀ q p, R q p → Refines (runOrig arms dest q p) (runEob arms dest q p)) ↔
      (∀ q p, R q p → armTarget arms q = none → p.isInit = true) := by
  constructor
  · intro h q p hR
    exact (eob_refines_iff arms dest q p).mp (h q p hR)
  · intro h q p hR
    exact (eob_refines_iff arms dest q p).mpr (h q p hR)

/-- The static condition a dataflow analysis can establish: the child place
is initialized (with live storage) on every state reaching the end of the
parent block. -/
def DefinitelyInitAtParentEnd (R : Nat → Slot → Prop) : Prop :=
  ∀ q p, R q p → p.isInit = true

/-- Definite initialization at the end of the parent block is sufficient. -/
theorem eob_sound_of_definitely_init (arms : Arms) (dest : Block)
    (R : Nat → Slot → Prop) (h : DefinitelyInitAtParentEnd R) :
    ∀ q p, R q p → Refines (runOrig arms dest q p) (runEob arms dest q p) :=
  (eob_repaired_definite_init_sound_iff arms dest R).mpr (fun q p hR _ => h q p hR)

/-- Without it, any reachable `otherwise`-path state with a non-initialized
child place is a miscompilation witness. -/
theorem eob_unsound_of_reachable_noninit_otherwise (arms : Arms) (dest : Block)
    (R : Nat → Slot → Prop) (q : Nat) (p : Slot) (hR : R q p)
    (hq : armTarget arms q = none) (hp : p.isInit = false) :
    ¬ ∀ q p, R q p → Refines (runOrig arms dest q p) (runEob arms dest q p) := by
  intro h
  have hinit := (eob_repaired_definite_init_sound_iff arms dest R).mp h q p hR hq
  rw [hp] at hinit
  cases hinit

/-! ### The exhaustive case

When the parent's `otherwise` target is an empty `unreachable` block, a value
of `Q` outside the arms is already undefined behavior in the original
program, so reading `P` early cannot make things worse. Mismatching children
then go to the children's common `otherwise` block. -/

def runOrigExh (arms : Arms) (childDest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match armTarget arms q with
  | none => .ub .unreachableExecuted
  | some tgt =>
    match p.read with
    | .ub u => .ub u
    | .ok v => if v = q then .ok tgt else .ok childDest

def runEobExh (arms : Arms) (childDest : Block) (q : Nat) (p : Slot) : Outcome Block :=
  match p.read with
  | .ub u => .ub u
  | .ok v =>
    if v = q then
      match armTarget arms q with
      | none => .ub .unreachableExecuted
      | some tgt => .ok tgt
    else .ok childDest

/-- With an exhaustive parent switch the rewrite is a refinement in every
state, whatever the state of the child place. -/
theorem eob_exhaustive_parent_refines (arms : Arms) (childDest : Block) (q : Nat) (p : Slot) :
    Refines (runOrigExh arms childDest q p) (runEobExh arms childDest q p) := by
  unfold runOrigExh runEobExh
  cases hq : armTarget arms q with
  | none => exact True.intro
  | some tgt =>
    cases hr : p.read with
    | ub u => exact True.intro
    | ok v =>
      cases Nat.decEq v q with
      | isTrue h => simp [h, Refines]
      | isFalse h => simp [h, Refines]

/-! ### The syntactic guards

The pass decides legality from the shape of the candidate, not from the
state of `P`. Three generations of the guard are modeled. -/

/-- Place projection elements, with the classification used by rustc's
`ProjectionElem::is_stable_offset`. -/
inductive Proj where
  | deref
  | field (idx : Nat) (ownerIsStructOrTuple : Bool)
  | index (indexLocal : Nat)
  | constantIndex
  | subslice
  | downcast (variant : Nat)
  | opaqueCast
  | unwrapUnsafeBinder
  | phantomDeref

/-- `Deref` and `Index` are the two projections whose target depends on
program state. -/
def Proj.isStableOffset : Proj → Bool
  | .deref => false
  | .index _ => false
  | _ => true

def Proj.isDeref : Proj → Bool
  | .deref => true
  | _ => false

/-- A field projection out of a struct or tuple (as opposed to a union or an
enum variant). -/
def Proj.isStructOrTupleField : Proj → Bool
  | .field _ b => b
  | _ => false

structure Place where
  loc : Nat
  proj : List Proj

/-- rustc's `Place::is_stable_offset`. -/
def Place.isStableOffset (pl : Place) : Bool := pl.proj.all Proj.isStableOffset

/-- The parts of a candidate the legality guards look at. -/
structure Candidate where
  /-- The children compute `discriminant(P)` before switching. -/
  needHoistDiscriminant : Bool
  /-- The parent's `otherwise` target is an empty `unreachable` block. -/
  otherwiseIsEmptyUnreachable : Bool
  /-- The child place `P`. -/
  place : Place

/-- Whole-body facts about the base local of `P`. -/
structure LocalFacts where
  isArgument : Bool
  /-- Assigned at most once, by a definition dominating all uses. -/
  isSsa : Bool
  isBorrowed : Bool
  isMovedFrom : Bool
  hasStorageMarker : Bool

def LocalFacts.unchangedArgument (f : LocalFacts) : Bool :=
  f.isArgument && f.isSsa && !f.isBorrowed && !f.isMovedFrom && !f.hasStorageMarker

/-- Oldest guard modeled: with a reachable `otherwise`, only refuse to hoist a
`discriminant(P)` computation. -/
def guardDiscriminantOnly (c : Candidate) : Bool :=
  c.otherwiseIsEmptyUnreachable || !c.needHoistDiscriminant

/-- Middle guard: additionally require `P` to be a stable-offset place. -/
def guardStableOffset (c : Candidate) : Bool :=
  c.otherwiseIsEmptyUnreachable || (!c.needHoistDiscriminant && c.place.isStableOffset)

/-- Newest guard modeled: with a reachable `otherwise`, `P` must be an
unchanged argument, projected only through struct or tuple fields. -/
def guardUnchangedArgument (c : Candidate) (f : LocalFacts) : Bool :=
  c.otherwiseIsEmptyUnreachable ||
    (!c.needHoistDiscriminant && f.unchangedArgument && c.place.proj.all Proj.isStructOrTupleField)

/-- Each guard is at least as strict as its predecessor on stable-offset
places: the middle guard implies the oldest. -/
theorem guardStableOffset_implies_guardDiscriminantOnly (c : Candidate)
    (h : guardStableOffset c = true) : guardDiscriminantOnly c = true := by
  unfold guardStableOffset at h
  unfold guardDiscriminantOnly
  cases hu : c.otherwiseIsEmptyUnreachable with
  | true => rfl
  | false =>
    rw [hu] at h
    cases hn : c.needHoistDiscriminant with
    | false => rfl
    | true =>
      rw [hn] at h
      cases h

/-- A machine state for place evaluation: the state of each local's own
storage, and what a dereference of each (pointer-typed) local denotes. -/
structure Env where
  localSlot : Nat → Slot
  pointee : Nat → Slot

/-- A local's own storage is never "dangling"; only a dereference can be. -/
def Env.WellFormed (env : Env) : Prop := ∀ l, env.localSlot l ≠ .dangling

/-- What a place denotes. A place with a `Deref` denotes the pointee of its
base local; any other place denotes (part of) the local's own storage. -/
def evalPlace (env : Env) (pl : Place) : Slot :=
  if pl.proj.any Proj.isDeref then env.pointee pl.loc else env.localSlot pl.loc

theorem stableOffset_no_deref (pl : Place) (h : pl.isStableOffset = true) :
    pl.proj.any Proj.isDeref = false := by
  unfold Place.isStableOffset at h
  rw [List.all_eq_true] at h
  rw [List.any_eq_false]
  intro e he hd
  have hs := h e he
  cases e with
  | deref => cases hs
  | field i b => cases hd
  | index l => cases hs
  | constantIndex => cases hd
  | subslice => cases hd
  | downcast v => cases hd
  | opaqueCast => cases hd
  | unwrapUnsafeBinder => cases hd
  | phantomDeref => cases hd

/-- What the stable-offset guard buys: a stable-offset place is never a
dangling dereference. -/
theorem stableOffset_place_never_dangling (env : Env) (hw : env.WellFormed) (pl : Place)
    (h : pl.isStableOffset = true) : evalPlace env pl ≠ .dangling := by
  unfold evalPlace
  rw [stableOffset_no_deref pl h]
  exact hw pl.loc

/-- What it does not buy: a stable-offset place can be in any other state,
in particular dead, uninitialized, or invalid. -/
theorem stableOffset_place_can_be_any_non_dangling_state (s : Slot) (hs : s ≠ .dangling) :
    ∃ (env : Env) (pl : Place),
      env.WellFormed ∧
      guardStableOffset ⟨false, false, pl⟩ = true ∧
      evalPlace env pl = s :=
  ⟨⟨fun _ => s, fun _ => .dangling⟩, ⟨2, []⟩, fun _ => hs, rfl, rfl⟩

/-- A `Deref` place can dangle, which is the case the stable-offset
requirement removes. -/
theorem deref_place_can_dangle :
    ∃ (env : Env) (pl : Place),
      env.WellFormed ∧ pl.isStableOffset = false ∧ evalPlace env pl = .dangling :=
  ⟨⟨fun _ => .init 0, fun _ => .dangling⟩, ⟨2, [.deref]⟩,
    fun _ h => (by cases h), rfl, rfl⟩

/-- The middle guard never inspects the state of `P`: whenever it accepts a
candidate with a reachable `otherwise`, every `otherwise`-path state in which
`P` is not initialized is a miscompilation witness. -/
theorem guardStableOffset_does_not_constrain_initialization (c : Candidate) :
    guardStableOffset c = true ∧ c.otherwiseIsEmptyUnreachable = false →
    ∀ (arms : Arms) (dest : Block) (q : Nat) (p : Slot),
      armTarget arms q = none → p.isInit = false →
      ¬ Refines (runOrig arms dest q p) (runEob arms dest q p) := by
  intro _ arms dest q p hq hp h
  have hinit := (eob_refines_iff arms dest q p).mp h hq
  rw [hp] at hinit
  cases hinit

/-! ### The concrete counterexample

`switchInt(q) -> [1: bb1, 2: bb2, otherwise: bb5]`, with
`bb1: switchInt(copy _2) -> [1: bb3, otherwise: bb5]` and
`bb2: switchInt(copy _2) -> [2: bb4, otherwise: bb5]`, run with `q = 99`. -/

def witnessArms : Arms := [(1, 3), (2, 4)]

/-- No discriminant hoist, reachable `otherwise`, child place `_2`. -/
def witnessCandidate : Candidate := ⟨false, false, ⟨2, []⟩⟩

/-- `_2` is a plain local, not an argument. -/
def witnessFacts : LocalFacts := ⟨false, true, false, false, false⟩

/-- **Refutation of the stable-offset guard.** The oldest and the middle
guard both accept the witness candidate. With `q = 99` and `_2`
uninitialized (respectively without live storage) the original program
reaches block 5 without undefined behavior, while the transformed program
performs an uninitialized read (respectively accesses a dead local). The
newest guard rejects the candidate. -/
theorem eob_current_guard_introduces_uninit_and_deadLocal_ub :
    guardDiscriminantOnly witnessCandidate = true ∧
    guardStableOffset witnessCandidate = true ∧
    guardUnchangedArgument witnessCandidate witnessFacts = false ∧
    runOrig witnessArms 5 99 .uninit = .ok 5 ∧
    runEob witnessArms 5 99 .uninit = .ub .uninitRead ∧
    runOrig witnessArms 5 99 .dead = .ok 5 ∧
    runEob witnessArms 5 99 .dead = .ub .deadLocal ∧
    ¬ Refines (runOrig witnessArms 5 99 .uninit) (runEob witnessArms 5 99 .uninit) ∧
    ¬ Refines (runOrig witnessArms 5 99 .dead) (runEob witnessArms 5 99 .dead) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show ¬ Refines (Outcome.ok 5) (Outcome.ub Ub.uninitRead)
    exact not_refines_ok_ub
  · show ¬ Refines (Outcome.ok 5) (Outcome.ub Ub.deadLocal)
    exact not_refines_ok_ub

/-- The same shape with an invalid (rather than uninitialized) child place:
the hazard the oldest guard was written for. -/
theorem eob_invalid_value_on_otherwise_path :
    runOrig witnessArms 5 99 .invalid = .ok 5 ∧
    runEob witnessArms 5 99 .invalid = .ub .invalidValue := ⟨rfl, rfl⟩

/-- On the arms the witness behaves identically before and after. -/
theorem eob_witness_agrees_when_initialized (q v : Nat) :
    runEob witnessArms 5 q (.init v) = runOrig witnessArms 5 q (.init v) :=
  eob_agree_on_init witnessArms 5 q v

/-! ### Why an unchanged argument is safe

The effect of one statement on the child place, and the state of the place
along a path of statements. -/

inductive Eff where
  /-- The statement does not write, move, borrow, or re-allocate the place. -/
  | none
  | assign (v : Nat)
  /-- A `move` out of the place, under a semantics where moves de-initialize. -/
  | moveOut
  | storageLive
  | storageDead
  /-- A write through a pointer obtained by borrowing the place. -/
  | writeViaBorrow (s : Slot)

def Eff.apply : Eff → Slot → Slot
  | .none, s => s
  | .assign v, _ => .init v
  | .moveOut, _ => .uninit
  | .storageLive, _ => .uninit
  | .storageDead, _ => .dead
  | .writeViaBorrow s, _ => s

def Eff.isNone : Eff → Bool
  | .none => true
  | _ => false

/-- The state of the place after a path. -/
def runPath (es : List Eff) (s : Slot) : Slot := es.foldl (fun s e => e.apply s) s

/-- A path without any effect on the place leaves it unchanged. -/
theorem runPath_unchanged (es : List Eff) (h : es.all Eff.isNone = true) (s : Slot) :
    runPath es s = s := by
  induction es generalizing s with
  | nil => rfl
  | cons e rest ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    have h1 := h.1
    have he : e.apply s = s := by
      cases e with
      | none => rfl
      | assign v => cases h1
      | moveOut => cases h1
      | storageLive => cases h1
      | storageDead => cases h1
      | writeViaBorrow t => cases h1
    show runPath rest (e.apply s) = s
    rw [he]
    exact ih h.2 s

/-- An argument holds a valid value on function entry. If no statement on the
path to the parent block affects it, hoisting the read is a refinement. -/
theorem eob_unchangedArgument_sound (arms : Arms) (dest : Block) (es : List Eff)
    (hes : es.all Eff.isNone = true) (q v : Nat) :
    Refines (runOrig arms dest q (runPath es (.init v)))
      (runEob arms dest q (runPath es (.init v))) := by
  rw [runPath_unchanged es hes, eob_agree_on_init]
  exact Refines.refl _

/-- A non-argument local that is never written is uninitialized on every
path, so hoisting its read is unsound on every `otherwise` path. -/
theorem eob_unchanged_nonargument_local_unsound (arms : Arms) (dest : Block) (es : List Eff)
    (hes : es.all Eff.isNone = true) (q : Nat) (hq : armTarget arms q = none) :
    ¬ Refines (runOrig arms dest q (runPath es .uninit))
      (runEob arms dest q (runPath es .uninit)) := by
  rw [runPath_unchanged es hes]
  intro h
  have hinit := (eob_refines_iff arms dest q .uninit).mp h hq
  cases hinit

/-- The two paths of the dead-local probe: storage is made live and written
on one path, and left dead on the other. -/
theorem deadLocal_probe_paths (q : Nat) :
    runPath [.storageLive, .assign q] .dead = .init q ∧ runPath [] .dead = .dead :=
  ⟨rfl, rfl⟩

/-! ## Part 2. `SimplifyComparisonIntegral` -/

inductive Mode where
  | copy
  | move
  deriving DecidableEq

inductive CmpOp where
  | eq
  | ne
  deriving DecidableEq

/-- A statement between the comparison and the terminator, as seen by the
compared local `x`. The pass requires `x` to be SSA, so no statement here
assigns `x`; the only statements that can change its state are its storage
markers. -/
inductive Mid where
  | other
  | storageLive
  | storageDead

def Mid.isMarker : Mid → Bool
  | .other => false
  | _ => true

/-- `StorageLive` gives fresh uninitialized storage (also when the local was
already live); `StorageDead` removes the storage. -/
def Mid.apply : Mid → Slot → Slot
  | .other, s => s
  | .storageLive, _ => .uninit
  | .storageDead, _ => .dead

def runMid (mid : List Mid) (s : Slot) : Slot := mid.foldl (fun s m => m.apply s) s

theorem runMid_cons (m : Mid) (rest : List Mid) (s : Slot) :
    runMid (m :: rest) s = runMid rest (m.apply s) := rfl

/-- Without markers the state of `x` is unchanged. -/
theorem runMid_no_marker (mid : List Mid) (h : mid.any Mid.isMarker = false) (s : Slot) :
    runMid mid s = s := by
  induction mid generalizing s with
  | nil => rfl
  | cons m rest ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [runMid_cons]
    have hm : m.apply s = s := by
      cases m with
      | other => rfl
      | storageLive => cases h.1
      | storageDead => cases h.1
    rw [hm]
    exact ih h.2 s

/-- With at least one marker, `x` does not hold a value afterwards. -/
theorem runMid_marker_not_init (mid : List Mid) (h : mid.any Mid.isMarker = true) (s : Slot) :
    (runMid mid s).isInit = false := by
  induction mid generalizing s with
  | nil => cases h
  | cons m rest ih =>
    rw [runMid_cons]
    cases hr : rest.any Mid.isMarker with
    | true => exact ih hr (m.apply s)
    | false =>
      rw [runMid_no_marker rest hr]
      rw [List.any_cons, hr, Bool.or_false] at h
      cases m with
      | other => cases h
      | storageLive => rfl
      | storageDead => rfl

/-- The state of `x` after an operand read of the value `v`. `deinit` selects
the semantics of `move`: `true` if a move leaves its source uninitialized,
`false` if a move leaves it untouched. -/
def afterRead (deinit : Bool) (m : Mode) (v : Nat) : Slot :=
  match m, deinit with
  | .move, true => .uninit
  | _, _ => .init v

def cmp (op : CmpOp) (k v : Nat) : Bool :=
  match op with
  | .eq => decide (v = k)
  | .ne => !decide (v = k)

/-- What a block run exposes: the successor, the value left in the
comparison temporary `_t`, and the state of `x`. -/
structure BlockResult where
  target : Block
  flag : Bool
  xAfter : Slot

/-- `uninit` may be replaced by any value; otherwise the states must agree. -/
def SlotRefines (s t : Slot) : Prop := s = t ∨ (s = .uninit ∧ ∃ v, t = .init v)

def ResultRefines (a b : BlockResult) : Prop :=
  a.target = b.target ∧ a.flag = b.flag ∧ SlotRefines a.xAfter b.xAfter

/-- Refinement of block runs, up to `SlotRefines` on the state of `x`. -/
def BlockRefines (src tgt : Outcome BlockResult) : Prop :=
  match src with
  | .ub _ => True
  | .ok a => ∃ b, tgt = .ok b ∧ ResultRefines a b

/-- The original block:
`_t = op(<m> x, const k); mid; switchInt(_t) -> [0: bbFalse, otherwise: bbTrue]`. -/
def sciOrig (deinit : Bool) (op : CmpOp) (m : Mode) (k : Nat) (mid : List Mid)
    (bbTrue bbFalse : Block) (s : Slot) : Outcome BlockResult :=
  match s.read with
  | .ub u => .ub u
  | .ok v =>
    .ok ⟨if cmp op k v then bbTrue else bbFalse, cmp op k v, runMid mid (afterRead deinit m v)⟩

/-- The successor chosen by `switchInt(copy x) -> [k: .., otherwise: ..]` after
the pass has arranged the two targets according to the comparison operator. -/
def switchOnOperand (op : CmpOp) (k v : Nat) (bbTrue bbFalse : Block) : Block :=
  match op with
  | .eq => if v = k then bbTrue else bbFalse
  | .ne => if v = k then bbFalse else bbTrue

/-- The block after the pass:
`_t = op(copy x, const k); mid; switchInt(copy x) -> [k: .., otherwise: ..]`.
`readMode` is the operand mode left in the comparison: the pass uses `copy`. -/
def sciRewritten (deinit : Bool) (readMode : Mode) (op : CmpOp) (k : Nat) (mid : List Mid)
    (bbTrue bbFalse : Block) (s : Slot) : Outcome BlockResult :=
  match s.read with
  | .ub u => .ub u
  | .ok v =>
    match (runMid mid (afterRead deinit readMode v)).read with
    | .ub u => .ub u
    | .ok v' =>
      .ok ⟨switchOnOperand op k v' bbTrue bbFalse, cmp op k v,
        runMid mid (afterRead deinit readMode v)⟩

/-- The pass as implemented: the comparison operand becomes a `copy`. -/
def sciPass (deinit : Bool) (op : CmpOp) (k : Nat) (mid : List Mid)
    (bbTrue bbFalse : Block) (s : Slot) : Outcome BlockResult :=
  sciRewritten deinit .copy op k mid bbTrue bbFalse s

/-- The variant that would keep `move` in the comparison. -/
def sciKeepMove (deinit : Bool) (op : CmpOp) (k : Nat) (mid : List Mid)
    (bbTrue bbFalse : Block) (s : Slot) : Outcome BlockResult :=
  sciRewritten deinit .move op k mid bbTrue bbFalse s

theorem afterRead_copy (deinit : Bool) (v : Nat) : afterRead deinit .copy v = .init v := by
  cases deinit <;> rfl

theorem slotRefines_afterRead (deinit : Bool) (m : Mode) (v : Nat) :
    SlotRefines (afterRead deinit m v) (.init v) := by
  cases m with
  | copy => exact Or.inl (afterRead_copy deinit v)
  | move =>
    cases deinit with
    | false => exact Or.inl rfl
    | true => exact Or.inr ⟨rfl, v, rfl⟩

/-- Switching on the operand agrees with switching on the comparison flag. -/
theorem switchOnOperand_eq_flag (op : CmpOp) (k v : Nat) (bbTrue bbFalse : Block) :
    switchOnOperand op k v bbTrue bbFalse = if cmp op k v then bbTrue else bbFalse := by
  cases op with
  | eq =>
    cases Nat.decEq v k with
    | isTrue h => simp [switchOnOperand, cmp, h]
    | isFalse h => simp [switchOnOperand, cmp, h]
  | ne =>
    cases Nat.decEq v k with
    | isTrue h => simp [switchOnOperand, cmp, h]
    | isFalse h => simp [switchOnOperand, cmp, h]

/-- **`SimplifyComparisonIntegral`, bidirectional soundness.** For either
semantics of `move`, either comparison operator, either original operand
mode, and any constant and targets: the rewritten block refines the original
block from every initial state of `x` if and only if no `StorageLive` or
`StorageDead` of `x` sits between the comparison and the terminator. -/
theorem simplifyComparisonIntegral_sound_iff (deinit : Bool) (op : CmpOp) (m : Mode) (k : Nat)
    (mid : List Mid) (bbTrue bbFalse : Block) :
    (∀ s, BlockRefines (sciOrig deinit op m k mid bbTrue bbFalse s)
        (sciPass deinit op k mid bbTrue bbFalse s)) ↔
      mid.any Mid.isMarker = false := by
  constructor
  · intro h
    cases hm : mid.any Mid.isMarker with
    | false => rfl
    | true =>
      have hk := h (.init k)
      have hni : (runMid mid (.init k)).isInit = false := runMid_marker_not_init mid hm _
      obtain ⟨u, hu⟩ := Slot.read_ub_of_not_init hni
      have hP : sciPass deinit op k mid bbTrue bbFalse (.init k) = .ub u := by
        simp [sciPass, sciRewritten, Slot.read_init, afterRead_copy, hu]
      rw [hP] at hk
      obtain ⟨b, hb, _⟩ := hk
      cases hb
  · intro hm s
    cases hs : s.read with
    | ub u =>
      have hO : sciOrig deinit op m k mid bbTrue bbFalse s = .ub u := by simp [sciOrig, hs]
      rw [hO]
      exact True.intro
    | ok v =>
      have hO : sciOrig deinit op m k mid bbTrue bbFalse s =
          .ok ⟨if cmp op k v then bbTrue else bbFalse, cmp op k v, afterRead deinit m v⟩ := by
        simp [sciOrig, hs, runMid_no_marker mid hm]
      have hP : sciPass deinit op k mid bbTrue bbFalse s =
          .ok ⟨switchOnOperand op k v bbTrue bbFalse, cmp op k v, .init v⟩ := by
        simp [sciPass, sciRewritten, hs, runMid_no_marker mid hm, afterRead_copy, Slot.read_init]
      rw [hO, hP]
      exact ⟨_, rfl, (switchOnOperand_eq_flag op k v bbTrue bbFalse).symm, rfl,
        slotRefines_afterRead deinit m v⟩

/-- **Counterexample without the `Move -> Copy` downgrade.** If a move
de-initializes its source, keeping `move` in the comparison makes the
terminator read an uninitialized local in every run in which the original
block is defined. -/
theorem sciKeepMove_ub_under_move_deinit (op : CmpOp) (k v : Nat) (bbTrue bbFalse : Block) :
    sciKeepMove true op k [] bbTrue bbFalse (.init v) = .ub .uninitRead ∧
    ¬ BlockRefines (sciOrig true op .move k [] bbTrue bbFalse (.init v))
        (sciKeepMove true op k [] bbTrue bbFalse (.init v)) := by
  have hK : sciKeepMove true op k [] bbTrue bbFalse (.init v) = .ub .uninitRead := rfl
  refine ⟨hK, ?_⟩
  rw [hK]
  intro h
  obtain ⟨b, hb, _⟩ := h
  cases hb

/-- The concrete instance used by the probe: `_t = Eq(move _x, const 43);
switchInt(move _x)` with `_x = 43`. -/
theorem sciKeepMove_concrete :
    sciOrig true .eq .move 43 [] 1 2 (.init 43) = .ok ⟨1, true, .uninit⟩ ∧
    sciKeepMove true .eq 43 [] 1 2 (.init 43) = .ub .uninitRead ∧
    sciPass true .eq 43 [] 1 2 (.init 43) = .ok ⟨1, true, .init 43⟩ := ⟨rfl, rfl, rfl⟩

/-- If a move leaves its source untouched, keeping the `move` is harmless:
the variant then coincides with the pass. -/
theorem sciKeepMove_eq_sciPass_without_move_deinit (op : CmpOp) (k : Nat) (mid : List Mid)
    (bbTrue bbFalse : Block) (s : Slot) :
    sciKeepMove false op k mid bbTrue bbFalse s = sciPass false op k mid bbTrue bbFalse s := rfl

/-- A `StorageDead` between comparison and terminator, concretely: the
original block is defined, the rewritten block reads a dead local. -/
theorem sciPass_storageDead_between_concrete :
    sciOrig false .eq .move 43 [.storageDead] 1 2 (.init 43) = .ok ⟨1, true, .dead⟩ ∧
    sciPass false .eq 43 [.storageDead] 1 2 (.init 43) = .ub .deadLocal := ⟨rfl, rfl⟩

/-! ## Part 3. `required_panic_strategy` and cross-crate linking -/

inductive Strategy where
  | unwind
  | abort
  deriving DecidableEq

/-- The ABI of a function defined in Rust, as far as unwinding is concerned. -/
inductive BodyAbi where
  /-- A rustic ABI. -/
  | rust
  /-- A non-rustic ABI that permits unwinding, such as `"C-unwind"`. -/
  | cUnwind
  /-- A non-rustic ABI that does not permit unwinding, such as `"C"`. -/
  | c
  deriving DecidableEq

/-- A call site. Functions are named by `(crate index, function index)`. -/
inductive Call where
  /-- A call with a rustic ABI to a function defined in Rust. -/
  | rustic (callee : Nat × Nat)
  /-- A call with a non-rustic ABI to a function defined in Rust. -/
  | rustDefinedNonRustic (callee : Nat × Nat) (unwindAbi : Bool)
  /-- A call to an item declared in an `extern` block. -/
  | foreignItem (unwindAbi : Bool)
  /-- A call through a function pointer with a non-rustic ABI. -/
  | fnPointer (unwindAbi : Bool)
  | inlineAsm (mayUnwind : Bool)

structure Fn where
  abi : BodyAbi
  calls : List Call

structure Crate where
  /-- The `-C panic` strategy the crate was compiled with. -/
  strategy : Strategy
  isPanicRuntime : Bool
  isCompilerBuiltins : Bool
  fns : List Fn

/-- The crates of one link. -/
abbrev Link := List Crate

/-- Whether a function *defined in Rust* may unwind, as rustc's
`fn_can_unwind` decides for the defining crate: never with `panic=abort`,
and with `panic=unwind` exactly when the ABI permits it. -/
def bodyCanUnwind : Strategy → BodyAbi → Bool
  | .unwind, .rust => true
  | .unwind, .cUnwind => true
  | _, _ => false

/-- Whether the crate containing a call site treats that call as possibly
unwinding. For a callee defined in Rust this depends on the *caller's*
strategy; for foreign items, function pointers and inline assembly it depends
only on the ABI or the `may_unwind` option. -/
def callCanUnwindAsSeenBy : Strategy → Call → Bool
  | .unwind, .rustic _ => true
  | .abort, .rustic _ => false
  | .unwind, .rustDefinedNonRustic _ u => u
  | .abort, .rustDefinedNonRustic _ _ => false
  | _, .foreignItem u => u
  | _, .fnPointer u => u
  | _, .inlineAsm m => m

/-- The call sites `has_ffi_unwind_calls` flags: a foreign unwind can enter
Rust here. Calls to functions defined in Rust are never flagged. -/
def Call.leaksForeignUnwind : Call → Bool
  | .foreignItem u => u
  | .fnPointer u => u
  | .inlineAsm m => m
  | _ => false

def Call.rustCallee : Call → Option (Nat × Nat)
  | .rustic r => some r
  | .rustDefinedNonRustic r _ => some r
  | _ => none

/-- rustc's `has_ffi_unwind_calls` for one body: the body itself can unwind
and contains a flagged call site. -/
def hasFfiUnwindCalls (s : Strategy) (f : Fn) : Bool :=
  bodyCanUnwind s f.abi && f.calls.any Call.leaksForeignUnwind

/-- rustc's `required_panic_strategy` for one crate. -/
def requiredPanicStrategy (c : Crate) : Option Strategy :=
  if c.isPanicRuntime then some c.strategy
  else
    match c.strategy with
    | .abort => some .abort
    | .unwind => if c.fns.any (hasFfiUnwindCalls .unwind) then some .unwind else none

def strategyCompatible (final : Strategy) : Option Strategy → Bool
  | none => true
  | some s => decide (s = final)

/-- The link-time check. It only runs when a panic-runtime crate is part of
the link, and it skips the `compiler_builtins` crate. -/
def linkOk (p : Link) (final : Strategy) : Bool :=
  if p.any (fun c => c.isPanicRuntime) then
    p.all (fun c => c.isCompilerBuiltins || strategyCompatible final (requiredPanicStrategy c))
  else true

/-- Name resolution for calls. -/
def Resolves (p : Link) (r : Nat × Nat) (c : Crate) (f : Fn) : Prop :=
  p[r.1]? = some c ∧ c.fns[r.2]? = some f

/-- `MayUnwindOut final p c f`: an unwind can propagate out of the body `f`
of crate `c`. A body lets an unwind out only if it was compiled as able to
unwind; otherwise the abort guard at the call site stops it. -/
inductive MayUnwindOut (final : Strategy) (p : Link) : Crate → Fn → Prop where
  /-- A foreign exception enters at a flagged call site. -/
  | foreign {c : Crate} {f : Fn} :
      c ∈ p → f ∈ c.fns → bodyCanUnwind c.strategy f.abi = true →
      f.calls.any Call.leaksForeignUnwind = true → MayUnwindOut final p c f
  /-- A Rust panic unwinds, which requires the unwinding panic runtime. -/
  | rustPanic {c : Crate} {f : Fn} :
      c ∈ p → f ∈ c.fns → bodyCanUnwind c.strategy f.abi = true →
      final = .unwind → MayUnwindOut final p c f
  /-- An unwind out of a Rust callee continues through a call site that was
  compiled with a landing pad. -/
  | propagate {c : Crate} {f : Fn} {call : Call} {r : Nat × Nat} {c' : Crate} {f' : Fn} :
      c ∈ p → f ∈ c.fns → bodyCanUnwind c.strategy f.abi = true →
      call ∈ f.calls → call.rustCallee = some r →
      callCanUnwindAsSeenBy c.strategy call = true →
      Resolves p r c' f' → MayUnwindOut final p c' f' → MayUnwindOut final p c f

/-- An unwind arrives at a call site that the caller's crate compiled as
non-unwinding (`unwind unreachable`). This is undefined behavior. -/
def UnwindReachesNounwindSite (final : Strategy) (p : Link) (c : Crate) (f : Fn) : Prop :=
  c ∈ p ∧ f ∈ c.fns ∧
    ∃ (call : Call) (r : Nat × Nat) (c' : Crate) (f' : Fn),
      call ∈ f.calls ∧ call.rustCallee = some r ∧ Resolves p r c' f' ∧
      callCanUnwindAsSeenBy c.strategy call = false ∧ MayUnwindOut final p c' f'

theorem bodyCanUnwind_strategy {s : Strategy} {abi : BodyAbi}
    (h : bodyCanUnwind s abi = true) : s = .unwind := by
  cases s with
  | unwind => rfl
  | abort => cases abi <;> cases h

/-- A crate with a flagged site in a body that can unwind requires the
`unwind` strategy, whether or not it is a panic runtime. -/
theorem required_unwind_of_ffi_unwind_call (c : Crate) (f : Fn) (hf : f ∈ c.fns)
    (hb : bodyCanUnwind c.strategy f.abi = true)
    (hl : f.calls.any Call.leaksForeignUnwind = true) :
    requiredPanicStrategy c = some .unwind := by
  have hs : c.strategy = .unwind := bodyCanUnwind_strategy hb
  have hff : hasFfiUnwindCalls .unwind f = true := by
    unfold hasFfiUnwindCalls
    rw [← hs, hb, hl]
    rfl
  have hany : c.fns.any (hasFfiUnwindCalls .unwind) = true :=
    List.any_eq_true.mpr ⟨f, hf, hff⟩
  unfold requiredPanicStrategy
  cases hr : c.isPanicRuntime with
  | true => simp [hs]
  | false => simp [hs, hany]

/-- Membership form of an accepted link with a panic runtime. -/
theorem linkOk_mem (p : Link) (final : Strategy)
    (hrt : p.any (fun c => c.isPanicRuntime) = true) (hok : linkOk p final = true)
    (c : Crate) (hc : c ∈ p) :
    c.isCompilerBuiltins = true ∨
      strategyCompatible final (requiredPanicStrategy c) = true := by
  unfold linkOk at hok
  rw [hrt] at hok
  have hall := List.all_eq_true.mp hok c hc
  cases hcb : c.isCompilerBuiltins with
  | true => exact Or.inl rfl
  | false =>
    rw [hcb] at hall
    exact Or.inr hall

/-- Under an accepted `abort` link no body lets an unwind out. -/
theorem linkOk_abort_no_unwind_out (p : Link)
    (hrt : p.any (fun c => c.isPanicRuntime) = true)
    (hcb : ∀ c, c ∈ p → c.isCompilerBuiltins = true →
      ∀ f, f ∈ c.fns → hasFfiUnwindCalls c.strategy f = false)
    (hok : linkOk p .abort = true) (c : Crate) (f : Fn) :
    ¬ MayUnwindOut .abort p c f := by
  intro h
  induction h with
  | foreign hc hf hb hl =>
    rename_i c f
    have hreq := required_unwind_of_ffi_unwind_call c f hf hb hl
    cases linkOk_mem p .abort hrt hok c hc with
    | inl hx =>
      have hno := hcb c hc hx f hf
      unfold hasFfiUnwindCalls at hno
      rw [hb, hl] at hno
      cases hno
    | inr hcompat =>
      rw [hreq] at hcompat
      cases hcompat
  | rustPanic _ _ _ hfin => cases hfin
  | propagate _ _ _ _ _ _ _ _ ih => exact ih

/-- **Cross-crate linking soundness.** Assume the final panic strategy is
`abort`, a panic-runtime crate is part of the link, the exempted
`compiler_builtins` crate has no flagged call site in a body that can unwind,
and the link check accepts. Then no body in the link lets an unwind out, and
no unwind reaches a call site compiled as non-unwinding. In particular no
foreign unwind enters a frame of a crate compiled with `panic=abort`. -/
theorem crossCrateLink_no_uncaught_foreign_unwind_in_abort_crate (p : Link)
    (hrt : p.any (fun c => c.isPanicRuntime) = true)
    (hcb : ∀ c, c ∈ p → c.isCompilerBuiltins = true →
      ∀ f, f ∈ c.fns → hasFfiUnwindCalls c.strategy f = false)
    (hok : linkOk p .abort = true) :
    (∀ c f, ¬ MayUnwindOut .abort p c f) ∧
    (∀ c f, ¬ UnwindReachesNounwindSite .abort p c f) := by
  have h1 : ∀ c f, ¬ MayUnwindOut .abort p c f := linkOk_abort_no_unwind_out p hrt hcb hok
  refine ⟨h1, ?_⟩
  intro c f h
  obtain ⟨_, _, _, _, c', f', _, _, _, _, hm⟩ := h
  exact h1 c' f' hm

/-- A crate compiled with `panic=unwind` that is not a panic runtime and has
no flagged call site requires no particular final strategy. -/
theorem pureRust_unwind_crate_requires_nothing (c : Crate)
    (hr : c.isPanicRuntime = false) (hs : c.strategy = .unwind)
    (hf : ∀ f, f ∈ c.fns → f.calls.any Call.leaksForeignUnwind = false) :
    requiredPanicStrategy c = none := by
  have hany : c.fns.any (hasFfiUnwindCalls .unwind) = false := by
    rw [List.any_eq_false]
    intro f hfm hff
    unfold hasFfiUnwindCalls at hff
    rw [hf f hfm, Bool.and_false] at hff
    cases hff
  unfold requiredPanicStrategy
  simp [hr, hs, hany]

/-- Such a crate is therefore compatible with both final strategies. -/
theorem pureRust_unwind_crate_links_with_either (c : Crate)
    (hr : c.isPanicRuntime = false) (hs : c.strategy = .unwind)
    (hf : ∀ f, f ∈ c.fns → f.calls.any Call.leaksForeignUnwind = false)
    (final : Strategy) :
    strategyCompatible final (requiredPanicStrategy c) = true := by
  rw [pureRust_unwind_crate_requires_nothing c hr hs hf]
  rfl

/-- A crate compiled with `panic=abort` always requires `abort`. -/
theorem abort_crate_requires_abort (c : Crate) (hs : c.strategy = .abort) :
    requiredPanicStrategy c = some .abort := by
  unfold requiredPanicStrategy
  cases hr : c.isPanicRuntime with
  | true => simp [hs]
  | false => simp [hs]

/-- In an accepted `unwind` link every crate other than the exempted
`compiler_builtins` was compiled with `panic=unwind`. -/
theorem linkOk_unwind_all_crates_unwind (p : Link)
    (hrt : p.any (fun c => c.isPanicRuntime) = true) (hok : linkOk p .unwind = true)
    (c : Crate) (hc : c ∈ p) (hx : c.isCompilerBuiltins = false) :
    c.strategy = .unwind := by
  cases hs : c.strategy with
  | unwind => rfl
  | abort =>
    cases linkOk_mem p .unwind hrt hok c hc with
    | inl hcb =>
      rw [hx] at hcb
      cases hcb
    | inr hcompat =>
      rw [abort_crate_requires_abort c hs] at hcompat
      cases hcompat

/-! ### Concrete links -/

/-- A panic-runtime crate for the given strategy. -/
def runtimeCrate (s : Strategy) : Crate := ⟨s, true, false, []⟩

/-- An upstream library crate with a single function `entry` (function 0). -/
def upCrate (s : Strategy) (abi : BodyAbi) (calls : List Call) : Crate :=
  ⟨s, false, false, [⟨abi, calls⟩]⟩

/-- A downstream binary crate whose `main` (function 0) calls `entry` of the
crate at index 1 with the Rust ABI. -/
def downCrate (s : Strategy) : Crate := ⟨s, false, false, [⟨.rust, [.rustic (1, 0)]⟩]⟩

/-- The link `[panic runtime, upstream rlib, downstream binary]`. -/
def stdLink (up : Crate) (final : Strategy) : Link := [runtimeCrate final, up, downCrate final]

/-- The upstream crate with a wrapper: `entry` (Rust ABI) calls `guarded`
(function 1, `extern "C"`), which makes the flagged foreign call. -/
def upGuardedCrate : Crate :=
  ⟨.unwind, false, false,
    [⟨.rust, [.rustDefinedNonRustic (1, 1) false]⟩, ⟨.c, [.foreignItem true]⟩]⟩

/-- **The link matrix.** The decisions of the model for the twelve
upstream/downstream pairings exercised by the probe. -/
theorem linkMatrix :
    -- upstream `panic=unwind`, downstream `panic=abort`
    linkOk (stdLink (upCrate .unwind .rust []) .abort) .abort = true ∧
    linkOk (stdLink (upCrate .unwind .rust [.foreignItem true]) .abort) .abort = false ∧
    linkOk (stdLink (upCrate .unwind .rust [.foreignItem false]) .abort) .abort = true ∧
    linkOk (stdLink upGuardedCrate .abort) .abort = true ∧
    linkOk (stdLink (upCrate .unwind .rust [.fnPointer true]) .abort) .abort = false ∧
    linkOk (stdLink (upCrate .unwind .rust [.rustDefinedNonRustic (1, 0) true]) .abort) .abort
      = true ∧
    linkOk (stdLink (upCrate .unwind .rust [.inlineAsm true]) .abort) .abort = false ∧
    -- matching strategies
    linkOk (stdLink (upCrate .unwind .rust [.foreignItem true]) .unwind) .unwind = true ∧
    linkOk (stdLink (upCrate .abort .rust [.foreignItem true]) .abort) .abort = true ∧
    -- upstream `panic=abort`, downstream `panic=unwind`
    linkOk (stdLink (upCrate .abort .rust [.foreignItem true]) .unwind) .unwind = false ∧
    linkOk (stdLink (upCrate .abort .rust []) .unwind) .unwind = false ∧
    linkOk (stdLink (upCrate .abort .rust []) .abort) .abort = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The upstream crate of the unsound pairing: compiled with `panic=unwind`,
its Rust-ABI `entry` calls a foreign `"C-unwind"` item. -/
def leakyUp : Crate := upCrate .unwind .rust [.foreignItem true]

/-- **What the check prevents.** Take the pairing "upstream `panic=unwind`
with a flagged foreign call, downstream `panic=abort`". The check rejects it.
If it were linked anyway, an unwind could leave the upstream `entry` and
reach the downstream call site, which was compiled as non-unwinding. -/
theorem unchecked_link_admits_foreign_unwind_into_abort_crate :
    linkOk (stdLink leakyUp .abort) .abort = false ∧
    MayUnwindOut .abort (stdLink leakyUp .abort) leakyUp ⟨.rust, [.foreignItem true]⟩ ∧
    UnwindReachesNounwindSite .abort (stdLink leakyUp .abort) (downCrate .abort)
      ⟨.rust, [.rustic (1, 0)]⟩ := by
  have hup : leakyUp ∈ stdLink leakyUp .abort :=
    List.Mem.tail _ (List.Mem.head _)
  have hdown : downCrate .abort ∈ stdLink leakyUp .abort :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have hm : MayUnwindOut .abort (stdLink leakyUp .abort) leakyUp ⟨.rust, [.foreignItem true]⟩ :=
    MayUnwindOut.foreign hup (List.Mem.head _) rfl rfl
  exact ⟨rfl, hm, hdown, List.Mem.head _,
    ⟨.rustic (1, 0), (1, 0), leakyUp, ⟨.rust, [.foreignItem true]⟩,
      List.Mem.head _, rfl, ⟨rfl, rfl⟩, rfl, hm⟩⟩

/-- The same two crates without any panic-runtime crate in the link (the
upstream at index 1 as before, preceded by an unrelated crate). -/
def noRuntimeLink : Link := [upCrate .unwind .rust [], leakyUp, downCrate .abort]

/-- **The check is conditional on a panic runtime.** Without a panic-runtime
crate in the link the check accepts everything, including the unsound
pairing. -/
theorem no_panic_runtime_link_is_unchecked :
    noRuntimeLink.any (fun c => c.isPanicRuntime) = false ∧
    linkOk noRuntimeLink .abort = true ∧
    UnwindReachesNounwindSite .abort noRuntimeLink (downCrate .abort)
      ⟨.rust, [.rustic (1, 0)]⟩ := by
  have hup : leakyUp ∈ noRuntimeLink := List.Mem.tail _ (List.Mem.head _)
  have hdown : downCrate .abort ∈ noRuntimeLink :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have hm : MayUnwindOut .abort noRuntimeLink leakyUp ⟨.rust, [.foreignItem true]⟩ :=
    MayUnwindOut.foreign hup (List.Mem.head _) rfl rfl
  exact ⟨rfl, rfl, hdown, List.Mem.head _,
    ⟨.rustic (1, 0), (1, 0), leakyUp, ⟨.rust, [.foreignItem true]⟩,
      List.Mem.head _, rfl, ⟨rfl, rfl⟩, rfl, hm⟩⟩

/-- The unsound upstream crate again, this time flagged as the exempted
`compiler_builtins` crate. -/
def exemptLeakyUp : Crate := ⟨.unwind, false, true, [⟨.rust, [.foreignItem true]⟩]⟩

/-- **The `compiler_builtins` exemption is a trusted assumption.** The check
skips the exempted crate, so the soundness theorem needs its hypothesis about
that crate: with a flagged call site inside it, the link is accepted and an
unwind still reaches a non-unwinding call site. -/
theorem compilerBuiltins_exemption_is_trusted :
    linkOk (stdLink exemptLeakyUp .abort) .abort = true ∧
    UnwindReachesNounwindSite .abort (stdLink exemptLeakyUp .abort) (downCrate .abort)
      ⟨.rust, [.rustic (1, 0)]⟩ := by
  have hup : exemptLeakyUp ∈ stdLink exemptLeakyUp .abort :=
    List.Mem.tail _ (List.Mem.head _)
  have hdown : downCrate .abort ∈ stdLink exemptLeakyUp .abort :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have hm : MayUnwindOut .abort (stdLink exemptLeakyUp .abort) exemptLeakyUp
      ⟨.rust, [.foreignItem true]⟩ :=
    MayUnwindOut.foreign hup (List.Mem.head _) rfl rfl
  exact ⟨rfl, hdown, List.Mem.head _,
    ⟨.rustic (1, 0), (1, 0), exemptLeakyUp, ⟨.rust, [.foreignItem true]⟩,
      List.Mem.head _, rfl, ⟨rfl, rfl⟩, rfl, hm⟩⟩

/-- The abort guard: a flagged foreign call inside a body that cannot unwind
(here an `extern "C"` function) does not let the unwind out, and such a crate
requires no particular strategy. -/
theorem guarded_foreign_call_does_not_leak :
    hasFfiUnwindCalls .unwind ⟨.c, [.foreignItem true]⟩ = false ∧
    requiredPanicStrategy upGuardedCrate = none := ⟨rfl, rfl⟩

end EobFfi

/-! ## Axioms of the headline theorems -/

#print axioms EobFfi.eob_current_guard_introduces_uninit_and_deadLocal_ub
#print axioms EobFfi.eob_repaired_definite_init_sound_iff
#print axioms EobFfi.eob_exhaustive_parent_refines
#print axioms EobFfi.eob_unchangedArgument_sound
#print axioms EobFfi.simplifyComparisonIntegral_sound_iff
#print axioms EobFfi.sciKeepMove_ub_under_move_deinit
#print axioms EobFfi.crossCrateLink_no_uncaught_foreign_unwind_in_abort_crate
#print axioms EobFfi.unchecked_link_admits_foreign_unwind_into_abort_crate
#print axioms EobFfi.no_panic_runtime_link_is_unchecked
#print axioms EobFfi.compilerBuiltins_exemption_is_trusted
#print axioms EobFfi.linkMatrix

/-! ## Audit

The command below fails (and with it the whole file) unless

* every declaration of this module in the `EobFfi` namespace depends on no
  axiom other than `propext` and `Quot.sound`;
* no constant declared by this module, and no imported constant in the
  `EobFfi` namespace, is a compiler-generated unsafe recursion helper.

`Environment.constants.map₂` holds the constants declared by the current
module; `map₁` holds the imported ones. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let ns : Name := `EobFfi
  let helperSuffix : String := "_unsafe" ++ "_rec"
  let isHelper (n : Name) : Bool := (n.toString.splitOn helperSuffix).length > 1
  let localNames : List Name := env.constants.map₂.toList.map (·.1)
  let importedNames : List Name := env.constants.map₁.toList.map (·.1)
  let importedInNs : List Name := importedNames.filter (fun n => ns.isPrefixOf n)
  let localHelpers := localNames.filter isHelper
  let importedHelpers := importedInNs.filter isHelper
  let allowed : List Name := [``propext, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut usedAxioms : List Name := []
  for n in localNames do
    if ns.isPrefixOf n then
      declarations := declarations + 1
      if let some (.thmInfo _) := env.find? n then
        theorems := theorems + 1
      let axs ← collectAxioms n
      for a in axs do
        unless allowed.contains a do
          throwError "{n} depends on the axiom {a}"
        unless usedAxioms.contains a do
          usedAxioms := a :: usedAxioms
  unless localHelpers.isEmpty do
    throwError "unsafe recursion helpers declared by this module: {localHelpers}"
  unless importedHelpers.isEmpty do
    throwError "unsafe recursion helpers imported into the namespace: {importedHelpers}"
  IO.println s!"audit ok: {declarations} declarations in EobFfi ({theorems} theorems); axioms used: {usedAxioms}; unsafe recursion helpers in this module: {localHelpers.length}; imported constants in EobFfi: {importedInNs.length}"
  IO.println s!"environment: {localNames.length} constants declared by this module; {importedNames.length} imported constants, of which {(importedNames.filter isHelper).length} are unsafe recursion helpers of the imported libraries"
