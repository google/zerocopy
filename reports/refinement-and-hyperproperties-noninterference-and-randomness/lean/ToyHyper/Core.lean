/-!
# Core Definitions: Systems, Hyperproperties, and Refinement

This module models systems extensionally as sets of execution traces
(`Trace → Prop`), trace properties as predicates on individual traces
(`Trace → Prop`), hyperproperties as predicates on systems
(`System Trace → Prop`), and compiler or specification refinement as
unconditional trace inclusion (`S' ⊑ S`) over a single shared trace type.
Source behaviors excluded by side conditions in a compiler correctness theorem
(such as executions with undefined behavior) must already be represented in the
source trace set `S`, and cross-language trace relations or linking with
adversarial contexts are not modeled here.
-/

namespace Toy.Hyper

universe u

/-- A system is modeled extensionally as the set of execution traces it can
exhibit. -/
abbrev System (Trace : Type u) : Type u := Trace → Prop

/-- A trace property is a set of allowed individual execution traces. -/
abbrev TraceProp (Trace : Type u) : Type u := Trace → Prop

/-- A hyperproperty is a set of systems (equivalently, a predicate on trace
sets), capturing multi-trace possibilistic security and liveness requirements
such as information-flow policies and output-range properties. Probabilistic
unpredictability (such as min-entropy) is not a hyperproperty of a
distribution's support; see `minEntropy_not_a_hyperprop_of_support`. -/
abbrev Hyperprop (Trace : Type u) : Type u := System Trace → Prop

/-- Trace-inclusion refinement: `Refines S' S` (`S' ⊑ S`) captures
whole-program compiler or specification refinement in which every observable
trace of the implementation `S'` is permitted by the specification `S` over a
shared trace type. -/
def Refines {Trace : Type u} (S' S : System Trace) : Prop :=
  ∀ t, S' t → S t

scoped infix:50 " ⊑ " => Refines

/-- A semantic whole-program refining compiler is a transformation on trace
sets that always produces a trace-inclusion refinement of its input system
(including transformations that delete behaviors arbitrarily). -/
def RefiningCompiler {Trace : Type u} (C : System Trace → System Trace) : Prop :=
  ∀ S, Refines (C S) S

/-- A hyperproperty is subset-closed if whenever a system satisfies it, every
sub-system (subset of traces) also satisfies it. -/
def SubsetClosed {Trace : Type u} (H : Hyperprop Trace) : Prop :=
  ∀ S S', (∀ t, S' t → S t) → H S → H S'

/-- A hyperproperty is preserved by all refining compilers if every semantic
refining transformation maps systems satisfying `H` to systems satisfying `H`. -/
def PreservedByAllRefiningCompilers {Trace : Type u} (H : Hyperprop Trace) : Prop :=
  ∀ C : System Trace → System Trace, RefiningCompiler C → ∀ S, H S → H (C S)

/-- Lifting a trace property `P` to a hyperproperty: a system satisfies
`LiftTraceProp P` iff every trace it can produce satisfies `P`. -/
def LiftTraceProp {Trace : Type u} (P : TraceProp Trace) : Hyperprop Trace :=
  fun S => ∀ t, S t → P t

/-- A `k`-ary universal hyperproperty (`∀ t₁ … tₖ ∈ S, Rel t₁ … tₖ`). Over
atomic traces this captures universal `k`-safety-style properties (such as
2-trace observational determinism); over infinite traces, topological
`k`-hypersafety additionally requires violations to be witnessed by finite
prefixes. -/
def UniversalKHyperprop {Trace : Type u} (k : Nat)
    (Rel : (Fin k → Trace) → Prop) : Hyperprop Trace :=
  fun S => ∀ ts : Fin k → Trace, (∀ i : Fin k, S (ts i)) → Rel ts

/-- Trace equivalence: mutual trace inclusion between two systems (extensional
equality of trace sets). -/
def TraceEquiv {Trace : Type u} (S' S : System Trace) : Prop :=
  Refines S' S ∧ Refines S S'

/-! ## Concrete Instances and Definition Examples -/

/-- A concrete Boolean system emitting only `false`. -/
def constFalseBoolSystem : System Bool := fun b => b = false

/-- A concrete Boolean system capable of emitting both `false` and `true`. -/
def fullBoolSystem : System Bool := fun _ => True

/-- Intersecting any system with a fixed target trace set `S₀` yields a
semantic refining compiler (which may delete arbitrary behaviors). -/
def intersectCompiler {Trace : Type u} (S₀ : System Trace) :
    System Trace → System Trace :=
  fun S t => S t ∧ S₀ t

/-- A non-refining transformation that replaces any Boolean system with all
Boolean traces. -/
def constFullBoolCompiler : System Bool → System Bool :=
  fun _ => fullBoolSystem

/-- The hyperproperty requiring a system to exhibit at least one trace
(a simple non-subset-closed hyperliveness property). -/
def NonEmptySystem {Trace : Type u} : Hyperprop Trace :=
  fun S => ∃ t, S t

/-- A hyperproperty over `Nat` requiring all exhibited traces to lie below some
finite bound `N` (used to separate general `SubsetClosed` hyperproperties from
`UniversalKHyperprop k Rel`). -/
def BoundedNatSystem : Hyperprop Nat :=
  fun S => ∃ N : Nat, ∀ n : Nat, S n → n < N

/-- Positive example for `Refines`: `{false}` refines `{false, true}`. -/
theorem refines_pos_example : Refines constFalseBoolSystem fullBoolSystem := by
  intro _ _
  trivial

/-- Negative example for `Refines`: `{false, true}` does not refine `{false}`. -/
theorem refines_neg_example : ¬ Refines fullBoolSystem constFalseBoolSystem := by
  intro h
  have hTrue : constFalseBoolSystem true := h true trivial
  cases hTrue

/-- Positive example for `RefiningCompiler`: `intersectCompiler` always refines. -/
theorem refiningCompiler_pos_example {Trace : Type u} (S₀ : System Trace) :
    RefiningCompiler (intersectCompiler S₀) := by
  intro _ _ h
  exact h.1

/-- Negative example for `RefiningCompiler`: `constFullBoolCompiler` adds traces
to `constFalseBoolSystem`. -/
theorem refiningCompiler_neg_example : ¬ RefiningCompiler constFullBoolCompiler := by
  intro h
  have hTrue : constFalseBoolSystem true := h constFalseBoolSystem true trivial
  cases hTrue

/-- Positive example for `LiftTraceProp`: `{false}` satisfies the lifted
property `b = false`. -/
theorem liftTraceProp_pos_example :
    LiftTraceProp (fun b : Bool => b = false) constFalseBoolSystem := by
  intro _ hb
  exact hb

/-- Negative example for `LiftTraceProp`: `{false, true}` violates the lifted
property `b = false`. -/
theorem liftTraceProp_neg_example :
    ¬ LiftTraceProp (fun b : Bool => b = false) fullBoolSystem := by
  intro h
  have hTrue : true = false := h true trivial
  cases hTrue

/-- Positive example for `UniversalKHyperprop`: `{false}` satisfies the 2-ary
universal property that all pairs of traces are equal. -/
theorem universalKHyperprop_pos_example :
    UniversalKHyperprop 2 (fun ts : Fin 2 → Bool => ts 0 = ts 1) constFalseBoolSystem := by
  intro ts hts
  have h0 : ts 0 = false := hts 0
  have h1 : ts 1 = false := hts 1
  exact h0.trans h1.symm

/-- Negative example for `UniversalKHyperprop`: `{false, true}` violates the
2-ary universal property that all pairs of traces are equal. -/
theorem universalKHyperprop_neg_example :
    ¬ UniversalKHyperprop 2 (fun ts : Fin 2 → Bool => ts 0 = ts 1) fullBoolSystem := by
  intro h
  let ts : Fin 2 → Bool := fun i => if i.val = 0 then false else true
  have hEq : ts 0 = ts 1 := h ts (fun _ => trivial)
  simp [ts] at hEq

/-- Positive example for `SubsetClosed`: lifting `b = false` is subset-closed. -/
theorem subsetClosed_pos_example :
    SubsetClosed (LiftTraceProp (fun b : Bool => b = false)) := by
  intro _ _ hRef hP t ht
  exact hP t (hRef t ht)

/-- Negative example for `SubsetClosed`: `NonEmptySystem` is not subset-closed
on `Bool` (the empty system refines `fullBoolSystem`). -/
theorem subsetClosed_neg_example : ¬ SubsetClosed (@NonEmptySystem Bool) := by
  intro hSC
  have hFull : NonEmptySystem fullBoolSystem := ⟨false, trivial⟩
  have hEmpty : NonEmptySystem (fun _ : Bool => False) :=
    hSC fullBoolSystem (fun _ => False) (fun _ hf => False.elim hf) hFull
  rcases hEmpty with ⟨_, hf⟩
  exact hf

/-- Positive example for `PreservedByAllRefiningCompilers`: lifting `b = false`
is preserved by every refining compiler. -/
theorem preservedByAllRefiningCompilers_pos_example :
    PreservedByAllRefiningCompilers (LiftTraceProp (fun b : Bool => b = false)) := by
  intro C hC S hS t ht
  exact hS t (hC S t ht)

/-- Negative example for `PreservedByAllRefiningCompilers`: `NonEmptySystem` is
not preserved by the refining compiler that discards all traces. -/
theorem preservedByAllRefiningCompilers_neg_example :
    ¬ PreservedByAllRefiningCompilers (@NonEmptySystem Bool) := by
  intro hPres
  let emptyComp : System Bool → System Bool := fun _ _ => False
  have hRef : RefiningCompiler emptyComp := fun _ _ hf => False.elim hf
  have hFull : NonEmptySystem fullBoolSystem := ⟨false, trivial⟩
  have hEmpty : NonEmptySystem (emptyComp fullBoolSystem) :=
    hPres emptyComp hRef fullBoolSystem hFull
  rcases hEmpty with ⟨_, hf⟩
  exact hf

/-- Positive example for `TraceEquiv`: `constFalseBoolSystem` is trace-equivalent
to itself. -/
theorem traceEquiv_pos_example :
    TraceEquiv constFalseBoolSystem constFalseBoolSystem :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- Negative example for `TraceEquiv`: `constFalseBoolSystem` is not
trace-equivalent to `fullBoolSystem`. -/
theorem traceEquiv_neg_example :
    ¬ TraceEquiv constFalseBoolSystem fullBoolSystem := by
  intro h
  exact refines_neg_example h.2

/-! ## Characterizations of Refinement-Preserved Hyperproperties -/

/-- A hyperproperty is subset-closed if and only if it is preserved by every
semantic whole-program refining compiler (including transformations that delete
arbitrary behaviors). -/
theorem subsetClosed_iff_preservedByAllRefiningCompilers
    {Trace : Type u} (H : Hyperprop Trace) :
    SubsetClosed H ↔ PreservedByAllRefiningCompilers H := by
  constructor
  · intro hSC C hC S hS
    exact hSC S (C S) (hC S) hS
  · intro hP S S' hRef hS
    have hEq : intersectCompiler S' S = S' :=
      funext fun t => propext ⟨fun h => h.2, fun h => ⟨hRef t h, h⟩⟩
    have h := hP (intersectCompiler S') (refiningCompiler_pos_example S') S hS
    rw [hEq] at h
    exact h

/-- Non-vacuity witness for `subsetClosed_iff_preservedByAllRefiningCompilers`:
a nontrivial subset-closed hyperproperty on `Bool` that accepts
`constFalseBoolSystem` and rejects `fullBoolSystem`, alongside the
non-subset-closed `NonEmptySystem`. -/
theorem subsetClosed_char_nonvacuity :
    SubsetClosed (LiftTraceProp (fun b : Bool => b = false)) ∧
    LiftTraceProp (fun b : Bool => b = false) constFalseBoolSystem ∧
    ¬ LiftTraceProp (fun b : Bool => b = false) fullBoolSystem ∧
    ¬ SubsetClosed (@NonEmptySystem Bool) :=
  ⟨subsetClosed_pos_example, liftTraceProp_pos_example, liftTraceProp_neg_example,
   subsetClosed_neg_example⟩

/-- Dual characterization: `S'` refines `S` if and only if every subset-closed
hyperproperty satisfied by `S` is also satisfied by `S'` (the context-free
trace-inclusion counterpart of robust subset-closed hyperproperty
preservation). -/
theorem refines_iff_preserves_all_subsetClosed
    {Trace : Type u} (S' S : System Trace) :
    Refines S' S ↔ ∀ H : Hyperprop Trace, SubsetClosed H → H S → H S' := by
  constructor
  · intro hRef H hSC hS
    exact hSC S S' hRef hS
  · intro hAll
    exact hAll (fun X => Refines X S) (fun _ _ hBA hA t ht => hA t (hBA t ht)) (fun _ h => h)

/-- Non-vacuity witness for `refines_iff_preserves_all_subsetClosed`: on `Bool`,
`constFalseBoolSystem ⊑ fullBoolSystem` satisfies both sides, while
`fullBoolSystem` fails both sides against `constFalseBoolSystem`. -/
theorem refines_iff_preserves_all_subsetClosed_nonvacuity :
    (Refines constFalseBoolSystem fullBoolSystem ∧
      ∀ H : Hyperprop Bool, SubsetClosed H → H fullBoolSystem → H constFalseBoolSystem) ∧
    (¬ Refines fullBoolSystem constFalseBoolSystem ∧
      ¬ (∀ H : Hyperprop Bool, SubsetClosed H → H constFalseBoolSystem → H fullBoolSystem)) := by
  refine ⟨⟨refines_pos_example, fun H hSC hS => hSC _ _ refines_pos_example hS⟩,
    ⟨refines_neg_example, ?_⟩⟩
  intro hAll
  exact liftTraceProp_neg_example
    (hAll (LiftTraceProp (fun b : Bool => b = false)) subsetClosed_pos_example
      liftTraceProp_pos_example)

/-- Every trace property lifts to a subset-closed hyperproperty (corollary of
`universalKHyperprop_subsetClosed` at `k = 1` via
`liftTraceProp_iff_universal1Hyperprop`). -/
theorem liftTraceProp_subsetClosed
    {Trace : Type u} (P : TraceProp Trace) :
    SubsetClosed (LiftTraceProp P) := by
  intro _ _ hRef hP t ht
  exact hP t (hRef t ht)

/-- Non-vacuity witness for `liftTraceProp_subsetClosed`: concrete nontrivial
trace property on `Bool`. -/
theorem liftTraceProp_subsetClosed_nonvacuity :
    (LiftTraceProp (fun b : Bool => b = false) constFalseBoolSystem) ∧
    (¬ LiftTraceProp (fun b : Bool => b = false) fullBoolSystem) :=
  ⟨liftTraceProp_pos_example, liftTraceProp_neg_example⟩

/-- Every `k`-ary universal hyperproperty is subset-closed. -/
theorem universalKHyperprop_subsetClosed
    {Trace : Type u} (k : Nat) (Rel : (Fin k → Trace) → Prop) :
    SubsetClosed (UniversalKHyperprop k Rel) := by
  intro _ _ hRef hK ts hts
  exact hK ts (fun i => hRef (ts i) (hts i))

/-- Non-vacuity witness for `universalKHyperprop_subsetClosed`: concrete
nontrivial 2-ary universal hyperproperty on `Bool`. -/
theorem universalKHyperprop_subsetClosed_nonvacuity :
    UniversalKHyperprop 2 (fun ts : Fin 2 → Bool => ts 0 = ts 1) constFalseBoolSystem ∧
    ¬ UniversalKHyperprop 2 (fun ts : Fin 2 → Bool => ts 0 = ts 1) fullBoolSystem :=
  ⟨universalKHyperprop_pos_example, universalKHyperprop_neg_example⟩

/-- Lifting a trace property `P` coincides with the 1-ary universal
hyperproperty checking `P` on the sole trace. -/
theorem liftTraceProp_iff_universal1Hyperprop
    {Trace : Type u} (P : TraceProp Trace) (S : System Trace) :
    LiftTraceProp P S ↔ UniversalKHyperprop 1 (fun ts => P (ts 0)) S := by
  constructor
  · intro hP ts hts
    exact hP (ts 0) (hts 0)
  · intro hU t ht
    exact hU (fun _ => t) (fun _ => ht)

private def maxTupleNat : {k : Nat} → (Fin k → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => Nat.max (f 0) (maxTupleNat (fun i => f i.succ))

private theorem le_maxTupleNat {k : Nat} (f : Fin k → Nat) (i : Fin k) :
    f i ≤ maxTupleNat f := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ ?_ i
    · exact Nat.le_max_left _ _
    · intro j
      exact Nat.le_trans (ih (fun x => f x.succ) j) (Nat.le_max_right _ _)

/-- Boundary theorem for `universalKHyperprop_subsetClosed`: not every
subset-closed hyperproperty has the form `UniversalKHyperprop k Rel`. Over
`Nat`, `BoundedNatSystem` is subset-closed yet coincides with no universal
`k`-trace hyperproperty for any `k`. -/
theorem boundedNatSystem_subsetClosed_not_universalKHyperprop :
    SubsetClosed BoundedNatSystem ∧
    ¬ ∃ (k : Nat) (Rel : (Fin k → Nat) → Prop),
      ∀ S : System Nat, BoundedNatSystem S ↔ UniversalKHyperprop k Rel S := by
  refine ⟨?_, ?_⟩
  · intro S S' hRef ⟨N, hN⟩
    exact ⟨N, fun n hn => hN n (hRef n hn)⟩
  · rintro ⟨k, Rel, hEq⟩
    have hAllRel : ∀ ts : Fin k → Nat, Rel ts := by
      intro ts
      let S_ts : System Nat := fun n => ∃ i : Fin k, n = ts i
      have hBnd : BoundedNatSystem S_ts := by
        refine ⟨maxTupleNat ts + 1, ?_⟩
        rintro n ⟨i, rfl⟩
        have hLe := le_maxTupleNat ts i
        omega
      have hU : UniversalKHyperprop k Rel S_ts := (hEq S_ts).mp hBnd
      exact hU ts (fun i => ⟨i, rfl⟩)
    have hFullU : UniversalKHyperprop k Rel (fun _ : Nat => True) :=
      fun ts _ => hAllRel ts
    have hFullBnd : BoundedNatSystem (fun _ : Nat => True) := (hEq _).mpr hFullU
    rcases hFullBnd with ⟨N, hN⟩
    exact Nat.lt_irrefl N (hN N trivial)

/-- Any hyperproperty is preserved by trace-equivalent systems (which are
extensionally equal trace sets). -/
theorem traceEquiv_preserves_hyperprop
    {Trace : Type u} (H : Hyperprop Trace) {S S' : System Trace}
    (hEq : TraceEquiv S' S) (hS : H S) : H S' := by
  have hFun : S' = S := funext fun t => propext ⟨hEq.1 t, hEq.2 t⟩
  exact hFun ▸ hS

end Toy.Hyper
