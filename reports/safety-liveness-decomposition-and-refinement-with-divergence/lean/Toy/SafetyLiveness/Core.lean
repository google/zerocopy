/-!
# Core definitions for linear-time trace properties, safety, liveness, and stream systems

This module models infinite execution traces as total functions `InfTrace α := Nat → α`,
linear-time properties as predicates on infinite traces, safety and liveness in the
sense of Alpern and Schneider (1985), topological closure over finite prefixes, and
stream-based systems with inclusion refinement.

Following Alpern and Schneider (1985) rather than Lamport (in Alford, Lamport,
and Mullery, 1985) and Abadi and Lamport (1991), properties are unrestricted predicates on `InfTrace α` and are not
required to be invariant under finite stuttering (`stepDiffers_isSafety`).

All core definitions are accompanied by proved positive and negative examples.
-/

namespace Toy.SafetyLiveness

universe u

/-- An infinite execution trace over an observation alphabet `α`, modeled as a
total function from discrete time steps `Nat` to observations `α`. Named
`InfTrace` (rather than `Stream`) so opening `Toy.SafetyLiveness` never shadows
`_root_.Stream`. Captures non-terminating (or infinitely stuttered) linear-time runs. -/
abbrev InfTrace (α : Type u) : Type u := Nat → α

/-- A linear-time trace property over `α`: a predicate on infinite traces `InfTrace α`.
Captures extensional specifications of allowed infinite executions without
requiring stuttering invariance. -/
abbrev TraceProp (α : Type u) : Type u := InfTrace α → Prop

/-- The finite prefix of length `n` of an infinite trace `s`. Captures the finite
observation history available after `n` discrete steps. -/
def takePrefix {α : Type u} (s : InfTrace α) (n : Nat) : List α :=
  List.ofFn (fun i : Fin n => s i.val)

/-- `HasPrefix s u` asserts that the finite trace `u` is an initial prefix of
the infinite trace `s`. Captures the relation "`s` extends the finite history
`u`". -/
def HasPrefix {α : Type u} (s : InfTrace α) (u : List α) : Prop :=
  ∀ (i : Nat) (h : i < u.length), s i = u[i]

/-- `appendPrefix u t` concatenates a finite prefix `u` in front of an infinite
trace `t`. Captures extending a finite execution history `u` with a continuation
trace `t`. -/
def appendPrefix {α : Type u} (u : List α) (t : InfTrace α) : InfTrace α :=
  fun i => if h : i < u.length then u[i] else t (i - u.length)

/-- Pointwise intersection (conjunction) of two trace properties. Named
`PropInter` (rather than `Inter`) so opening `Toy.SafetyLiveness` never shadows
`_root_.Inter`. Captures combining two specifications (for example, a safety
part and a liveness part). -/
def PropInter {α : Type u} (P Q : TraceProp α) : TraceProp α :=
  fun s => P s ∧ Q s

/-- The universal trace property containing every infinite trace over `α`. Captures
the vacuous specification that allows all infinite behaviors. -/
def UnivProp {α : Type u} : TraceProp α :=
  fun _ => True

/-- The empty trace property containing no infinite trace over `α`. Captures an
unsatisfiable specification. -/
def EmptyProp {α : Type u} : TraceProp α :=
  fun _ => False

/-- Alpern–Schneider safety property: every infinite trace outside `P` has a finite
prefix none of whose infinite extensions lies in `P`. Captures "nothing bad
ever happens" (irremediable finite-prefix violation). Unlike Lamport (in Alford,
Lamport, and Mullery, 1985) and Abadi and Lamport (1991), `P` is not required to be closed under stuttering. -/
def IsSafety {α : Type u} (P : TraceProp α) : Prop :=
  ∀ s : InfTrace α, ¬ P s →
    ∃ n : Nat, ∀ s' : InfTrace α, HasPrefix s' (takePrefix s n) → ¬ P s'

/-- Alpern–Schneider liveness property: every finite trace `u : List α` can be
extended to at least one infinite trace satisfying `P`. Captures "something
good can always still happen" (no finite prefix irremediably violates `P`). -/
def IsLiveness {α : Type u} (P : TraceProp α) : Prop :=
  ∀ u : List α, ∃ s : InfTrace α, HasPrefix s u ∧ P s

/-- Topological closure of `P` in the prefix (Cantor) topology on `InfTrace α`:
an infinite trace `s` lies in `Closure P` iff every finite prefix `takePrefix s n`
extends to some infinite trace in `P`. Captures the smallest safety property
containing `P` (see `closure_isSafety`, `subset_closure`, and
`closure_minimal_of_isSafety`). -/
def Closure {α : Type u} (P : TraceProp α) : TraceProp α :=
  fun s => ∀ n : Nat, ∃ s' : InfTrace α, HasPrefix s' (takePrefix s n) ∧ P s'

/-- The canonical Alpern–Schneider liveness component of `P`: infinite traces that
either lie in `P` or lie outside `Closure P` (equivalently `Closure P s → P s`
classically). Together with `Closure P`, it decomposes `P`. -/
def LivenessPart {α : Type u} (P : TraceProp α) : TraceProp α :=
  fun s => P s ∨ ¬ Closure P s

/-- A system modeled denotationally as its set of possible infinite execution
traces. Captures a reactive or transition system's infinite-trace semantics. -/
abbrev StreamSystem (α : Type u) : Type u := InfTrace α → Prop

/-- `Satisfies S P` asserts that every infinite trace produced by system `S`
satisfies trace property `P`. Captures linear-time satisfaction `S ⊆ P`. -/
def Satisfies {α : Type u} (S : StreamSystem α) (P : TraceProp α) : Prop :=
  ∀ s : InfTrace α, S s → P s

/-- `StreamRefines Impl Spec` asserts that every infinite trace of `Impl` is
also permitted by `Spec`. Captures behavioral inclusion `Impl ⊆ Spec`. -/
def StreamRefines {α : Type u} (Impl Spec : StreamSystem α) : Prop :=
  ∀ s : InfTrace α, Impl s → Spec s

/-- `IsNonemptyStream S` asserts that system `S` admits at least one infinite
trace. Separated from `StreamSystem` so theorems state totality/inhabitation
explicitly rather than silently baking it into the type. -/
def IsNonemptyStream {α : Type u} (S : StreamSystem α) : Prop :=
  ∃ s : InfTrace α, S s

/-! ### Elementary prefix and closure lemmas -/

theorem takePrefix_length {α : Type u} (s : InfTrace α) (n : Nat) :
    (takePrefix s n).length = n := by
  simp [takePrefix]

theorem takePrefix_getElem {α : Type u} (s : InfTrace α) (n i : Nat)
    (h : i < (takePrefix s n).length) :
    (takePrefix s n)[i] = s i := by
  simp [takePrefix]

theorem hasPrefix_takePrefix {α : Type u} (s : InfTrace α) (n : Nat) :
    HasPrefix s (takePrefix s n) := by
  intro i h
  simp [takePrefix]

theorem hasPrefix_nil {α : Type u} (s : InfTrace α) :
    HasPrefix s [] := by
  intro i h
  cases h

theorem hasPrefix_appendPrefix {α : Type u} (u : List α) (t : InfTrace α) :
    HasPrefix (appendPrefix u t) u := by
  intro i h
  simp [appendPrefix, h]

theorem hasPrefix_takePrefix_iff {α : Type u} (s s' : InfTrace α) (n : Nat) :
    HasPrefix s' (takePrefix s n) ↔ ∀ i : Nat, i < n → s' i = s i := by
  constructor
  · intro h i hi
    have hlen : i < (takePrefix s n).length := by
      simpa [takePrefix_length] using hi
    simpa [takePrefix] using h i hlen
  · intro h i hi
    have hi' : i < n := by
      simpa [takePrefix_length] using hi
    simpa [takePrefix] using h i hi'

theorem takePrefix_eq_of_hasPrefix {α : Type u} {s : InfTrace α} {u : List α}
    (h : HasPrefix s u) :
    takePrefix s u.length = u := by
  apply List.ext_getElem
  · exact takePrefix_length s u.length
  · intro i hi1 hi2
    rw [takePrefix_getElem]
    exact h i hi2

theorem hasPrefix_iff_takePrefix_eq {α : Type u} (s : InfTrace α) (u : List α) :
    HasPrefix s u ↔ takePrefix s u.length = u := by
  constructor
  · exact takePrefix_eq_of_hasPrefix
  · intro heq i hi
    have h1 : (takePrefix s u.length)[i]'(by simpa [takePrefix_length] using hi) = u[i] := by
      simp [heq]
    simpa [takePrefix] using h1

theorem hasPrefix_of_hasPrefix_takePrefix {α : Type u} {s s' : InfTrace α} {u : List α}
    (hs : HasPrefix s u) (hs' : HasPrefix s' (takePrefix s u.length)) :
    HasPrefix s' u := by
  rw [takePrefix_eq_of_hasPrefix hs] at hs'
  exact hs'

theorem subset_closure {α : Type u} {P : TraceProp α} {s : InfTrace α} (hP : P s) :
    Closure P s := by
  intro n
  exact ⟨s, hasPrefix_takePrefix s n, hP⟩

theorem closure_mono {α : Type u} {P Q : TraceProp α}
    (hPQ : ∀ s : InfTrace α, P s → Q s) :
    ∀ s : InfTrace α, Closure P s → Closure Q s := by
  intro s hs n
  rcases hs n with ⟨s', hpre, hP⟩
  exact ⟨s', hpre, hPQ s' hP⟩

/-! ### Reusable concrete infinite traces and properties on `Bool` -/

/-- The constant-`false` Boolean infinite trace. -/
def constFalse : InfTrace Bool := fun _ => false

/-- The constant-`true` Boolean infinite trace. -/
def constTrue : InfTrace Bool := fun _ => true

/-- Safety property on `Bool`: every step observes `false`. -/
def AlwaysFalse : TraceProp Bool := fun s => ∀ i : Nat, s i = false

/-- Liveness property on `Bool`: `true` is eventually observed. -/
def EventuallyTrue : TraceProp Bool := fun s => ∃ i : Nat, s i = true

/-- Liveness property on `Bool`: `false` is eventually observed. -/
def EventuallyFalse : TraceProp Bool := fun s => ∃ i : Nat, s i = false

/-- Safety property on `Bool`: the initial observation is `true`. -/
def StartsTrue : TraceProp Bool := fun s => s 0 = true

/-- Mixed property on `Bool`: starts with `true` and eventually observes `false`.
Neither a safety property nor a liveness property. -/
def StartsTrueAndEventuallyFalse : TraceProp Bool :=
  fun s => s 0 = true ∧ ∃ i : Nat, s i = false

/-- Safety property on `Bool`: if the initial observation is `false`, all
subsequent observations remain `false`. Used to build a satisfiable
non-machine-closed specification pair with `EventuallyTrue`. -/
def StartsFalseStaysFalse : TraceProp Bool :=
  fun s => s 0 = false → ∀ i : Nat, s i = false

/-! ### Positive and negative examples for core definitions -/

/-- Positive example for `InfTrace`: `constFalse` inhabits `InfTrace Bool`. -/
theorem infTrace_pos_constFalse : Nonempty (InfTrace Bool) :=
  ⟨constFalse⟩

/-- Negative example for `InfTrace`: there is no infinite trace over `Empty`. -/
theorem infTrace_neg_empty : ¬ Nonempty (InfTrace Empty) := by
  rintro ⟨s⟩
  exact Empty.elim (s 0)

/-- Positive example for `TraceProp`: `AlwaysFalse` admits `constFalse`. -/
theorem traceProp_pos_alwaysFalse : AlwaysFalse constFalse := by
  intro i
  rfl

/-- Negative example for `TraceProp`: `AlwaysFalse` rejects `constTrue`. -/
theorem traceProp_neg_alwaysFalse : ¬ AlwaysFalse constTrue := by
  intro h
  have h0 := h 0
  contradiction

/-- Positive example for `takePrefix`: the length-2 prefix of `constFalse` is `[false, false]`. -/
theorem takePrefix_pos_constFalse : takePrefix constFalse 2 = [false, false] := by
  rfl

/-- Negative example for `takePrefix`: the length-1 prefix of `constFalse` is not `[true]`. -/
theorem takePrefix_neg_constFalse : takePrefix constFalse 1 ≠ [true] := by
  decide

/-- Positive example for `HasPrefix`: `constFalse` has prefix `[false, false]`. -/
theorem hasPrefix_pos_constFalse : HasPrefix constFalse [false, false] := by
  intro i h
  match i with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => simp at h; omega

/-- Negative example for `HasPrefix`: `constFalse` does not have prefix `[true]`. -/
theorem hasPrefix_neg_constFalse : ¬ HasPrefix constFalse [true] := by
  intro h
  have h0 := h 0 (by simp)
  simp [constFalse] at h0

/-- Positive example for `appendPrefix`: prepending `[true]` to `constFalse` yields
`true` at step `0` and `false` at step `1`. -/
theorem appendPrefix_pos_true_constFalse :
    appendPrefix [true] constFalse 0 = true ∧ appendPrefix [true] constFalse 1 = false := by
  constructor <;> rfl

/-- Negative example for `appendPrefix`: prepending `[true]` to `constFalse` differs
from `constFalse`. -/
theorem appendPrefix_neg_ne_constFalse :
    appendPrefix [true] constFalse ≠ constFalse := by
  intro h
  have h0 := congrFun h 0
  simp [appendPrefix, constFalse] at h0

/-- Positive example for `PropInter`: `appendPrefix [true] constFalse` satisfies
`PropInter StartsTrue EventuallyFalse`. -/
theorem propInter_pos_startsTrue_eventuallyFalse :
    PropInter StartsTrue EventuallyFalse (appendPrefix [true] constFalse) := by
  refine ⟨rfl, 1, rfl⟩

/-- Negative example for `PropInter`: `constTrue` fails `PropInter StartsTrue EventuallyFalse`. -/
theorem propInter_neg_startsTrue_eventuallyFalse :
    ¬ PropInter StartsTrue EventuallyFalse constTrue := by
  rintro ⟨_, i, hi⟩
  simp [constTrue] at hi

/-- Positive example for `UnivProp`: `constFalse` satisfies `UnivProp`. -/
theorem univProp_pos_constFalse : UnivProp constFalse :=
  trivial

/-- Negative example for `UnivProp`: `UnivProp` on `Bool` is distinct from `EmptyProp`. -/
theorem univProp_neg_ne_emptyProp : (UnivProp : TraceProp Bool) ≠ EmptyProp := by
  intro h
  have h0 := congrFun h constFalse
  have : EmptyProp constFalse := h0 ▸ trivial
  exact this

/-- Positive example for `EmptyProp`: `EmptyProp` implies every property vacuously. -/
theorem emptyProp_pos_implies_all (P : TraceProp Bool) (s : InfTrace Bool) :
    EmptyProp s → P s :=
  False.elim

/-- Negative example for `EmptyProp`: `constFalse` is rejected by `EmptyProp`. -/
theorem emptyProp_neg_constFalse : ¬ EmptyProp constFalse :=
  id

/-- Positive example for `IsSafety`: `AlwaysFalse` is a safety property. -/
theorem alwaysFalse_isSafety : IsSafety AlwaysFalse := by
  intro s hNot
  have hex : ∃ i : Nat, s i ≠ false := by
    apply Classical.byContradiction
    intro hAll
    apply hNot
    intro i
    apply Classical.byContradiction
    intro hne
    exact hAll ⟨i, hne⟩
  rcases hex with ⟨i, hi⟩
  refine ⟨i + 1, fun s' hpre hAll' => ?_⟩
  have heq : s' i = s i := (hasPrefix_takePrefix_iff s s' (i + 1)).mp hpre i (Nat.lt_succ_self i)
  exact hi (heq ▸ hAll' i)

/-- Positive example for `IsSafety`: `StartsTrue` is a safety property. -/
theorem startsTrue_isSafety : IsSafety StartsTrue := by
  intro s hNot
  refine ⟨1, fun s' hpre h0' => ?_⟩
  have heq : s' 0 = s 0 := (hasPrefix_takePrefix_iff s s' 1).mp hpre 0 (by decide)
  exact hNot (heq.symm.trans h0')

/-- Positive example for `IsSafety`: `StartsFalseStaysFalse` is a safety property. -/
theorem startsFalseStaysFalse_isSafety : IsSafety StartsFalseStaysFalse := by
  intro s hNot
  have h0 : s 0 = false := by
    apply Classical.byContradiction
    intro hne
    exact hNot (fun h => absurd h hne)
  have hex : ∃ i : Nat, s i ≠ false := by
    apply Classical.byContradiction
    intro hAll
    apply hNot
    intro _ i
    apply Classical.byContradiction
    intro hne
    exact hAll ⟨i, hne⟩
  rcases hex with ⟨i, hi⟩
  refine ⟨i + 1, fun s' hpre hS' => ?_⟩
  have heq0 : s' 0 = s 0 := (hasPrefix_takePrefix_iff s s' (i + 1)).mp hpre 0 (Nat.zero_lt_succ i)
  have heqi : s' i = s i := (hasPrefix_takePrefix_iff s s' (i + 1)).mp hpre i (Nat.lt_succ_self i)
  have hs'i : s' i = false := hS' (heq0.trans h0) i
  exact hi (heqi.symm.trans hs'i)

/-- Non-stuttering-closed positive example for `IsSafety` (Alpern, Demers, and
Schneider, 1986): `fun s => s 0 ≠ s 1` satisfies `IsSafety` even though
repeating the initial state falsifies it. -/
theorem stepDiffers_isSafety : IsSafety (fun s : InfTrace Bool => s 0 ≠ s 1) := by
  intro s hNot
  refine ⟨2, fun s' hpre hNe => ?_⟩
  have h0 : s' 0 = s 0 := (hasPrefix_takePrefix_iff s s' 2).mp hpre 0 (by decide)
  have h1 : s' 1 = s 1 := (hasPrefix_takePrefix_iff s s' 2).mp hpre 1 (by decide)
  exact hNot (fun hEq => hNe (h0.trans (hEq.trans h1.symm)))

/-- Positive example for `IsSafety`: `UnivProp` is always a safety property. -/
theorem univProp_isSafety {α : Type u} : IsSafety (UnivProp : TraceProp α) := by
  intro s hNot
  exact absurd trivial hNot

/-- Negative example for `IsSafety`: `EventuallyTrue` is not a safety property. -/
theorem eventuallyTrue_not_isSafety : ¬ IsSafety EventuallyTrue := by
  intro hSafe
  have hNot : ¬ EventuallyTrue constFalse := by
    rintro ⟨i, hi⟩
    simp [constFalse] at hi
  rcases hSafe constFalse hNot with ⟨n, hn⟩
  let s' := appendPrefix (takePrefix constFalse n) constTrue
  have hpre : HasPrefix s' (takePrefix constFalse n) :=
    hasPrefix_appendPrefix (takePrefix constFalse n) constTrue
  have hEv : EventuallyTrue s' := by
    refine ⟨n, ?_⟩
    have hlen : (takePrefix constFalse n).length = n := takePrefix_length constFalse n
    simp [s', appendPrefix, hlen, constTrue]
  exact hn s' hpre hEv

/-- Positive example for `IsLiveness`: `EventuallyTrue` is a liveness property. -/
theorem eventuallyTrue_isLiveness : IsLiveness EventuallyTrue := by
  intro u
  refine ⟨appendPrefix u constTrue, hasPrefix_appendPrefix u constTrue, u.length, ?_⟩
  simp [appendPrefix, constTrue]

/-- Positive example for `IsLiveness`: `EventuallyFalse` is a liveness property. -/
theorem eventuallyFalse_isLiveness : IsLiveness EventuallyFalse := by
  intro u
  refine ⟨appendPrefix u constFalse, hasPrefix_appendPrefix u constFalse, u.length, ?_⟩
  simp [appendPrefix, constFalse]

/-- Positive example for `IsLiveness`: `UnivProp` is live over any nonempty alphabet. -/
theorem univProp_isLiveness {α : Type u} (hα : Nonempty α) : IsLiveness (UnivProp : TraceProp α) := by
  rcases hα with ⟨a⟩
  intro u
  exact ⟨appendPrefix u (fun _ => a), hasPrefix_appendPrefix u (fun _ => a), trivial⟩

/-- Negative example for `IsLiveness`: `AlwaysFalse` is not a liveness property. -/
theorem alwaysFalse_not_isLiveness : ¬ IsLiveness AlwaysFalse := by
  intro hLive
  rcases hLive [true] with ⟨s, hpre, hAll⟩
  have h0 : s 0 = true := hpre 0 (by simp)
  have h0' : s 0 = false := hAll 0
  rw [h0] at h0'
  contradiction

/-- Negative example for both `IsSafety` and `IsLiveness`: `StartsTrueAndEventuallyFalse`
is neither a safety property nor a liveness property. -/
theorem startsTrueAndEventuallyFalse_neither_safety_nor_liveness :
    ¬ IsSafety StartsTrueAndEventuallyFalse ∧ ¬ IsLiveness StartsTrueAndEventuallyFalse := by
  constructor
  · intro hSafe
    have hNot : ¬ StartsTrueAndEventuallyFalse constTrue := by
      rintro ⟨_, i, hi⟩
      simp [constTrue] at hi
    rcases hSafe constTrue hNot with ⟨n, hn⟩
    let s' := appendPrefix (takePrefix constTrue (n + 1)) constFalse
    have hpre : HasPrefix s' (takePrefix constTrue n) := by
      rw [hasPrefix_takePrefix_iff]
      intro i hi
      have hlen : i < (takePrefix constTrue (n + 1)).length := by
        rw [takePrefix_length]
        exact Nat.lt_trans hi (Nat.lt_succ_self n)
      have h1 := hasPrefix_appendPrefix (takePrefix constTrue (n + 1)) constFalse i hlen
      rw [takePrefix_getElem] at h1
      exact h1
    have h0 : s' 0 = true := by
      have hlen : 0 < (takePrefix constTrue (n + 1)).length := by
        rw [takePrefix_length]
        exact Nat.zero_lt_succ n
      have h1 := hasPrefix_appendPrefix (takePrefix constTrue (n + 1)) constFalse 0 hlen
      rw [takePrefix_getElem] at h1
      exact h1
    have hEv : ∃ i, s' i = false := by
      refine ⟨n + 1, ?_⟩
      have hlen : (takePrefix constTrue (n + 1)).length = n + 1 :=
        takePrefix_length constTrue (n + 1)
      simp [s', appendPrefix, hlen, constFalse]
    exact hn s' hpre ⟨h0, hEv⟩
  · intro hLive
    rcases hLive [false] with ⟨s, hpre, h0, _⟩
    have hf : s 0 = false := hpre 0 (by simp)
    rw [hf] at h0
    contradiction

/-- Positive example for `Closure`: `constFalse` lies in `Closure EventuallyTrue`
even though it does not lie in `EventuallyTrue`. -/
theorem closure_pos_eventuallyTrue_admits_constFalse :
    Closure EventuallyTrue constFalse := by
  intro n
  exact eventuallyTrue_isLiveness (takePrefix constFalse n)

/-- Negative example for `Closure`: `constTrue` does not lie in `Closure AlwaysFalse`. -/
theorem closure_neg_alwaysFalse_rejects_constTrue :
    ¬ Closure AlwaysFalse constTrue := by
  intro hCl
  rcases hCl 1 with ⟨s', hpre, hAll⟩
  have h0 : s' 0 = true := (hasPrefix_takePrefix_iff constTrue s' 1).mp hpre 0 (by decide)
  have h0' : s' 0 = false := hAll 0
  rw [h0] at h0'
  contradiction

/-- Positive example for `LivenessPart`: `constFalse` lies in
`LivenessPart StartsTrueAndEventuallyFalse` (via being outside its closure). -/
theorem livenessPart_pos_admits_constFalse :
    LivenessPart StartsTrueAndEventuallyFalse constFalse := by
  right
  intro hCl
  rcases hCl 1 with ⟨s', hpre, h0', _⟩
  have hf : s' 0 = false := (hasPrefix_takePrefix_iff constFalse s' 1).mp hpre 0 (by decide)
  rw [hf] at h0'
  contradiction

/-- Negative example for `LivenessPart`: `constTrue` is rejected by
`LivenessPart StartsTrueAndEventuallyFalse` because it lies in the closure
but not in the property itself. -/
theorem livenessPart_neg_rejects_constTrue :
    ¬ LivenessPart StartsTrueAndEventuallyFalse constTrue := by
  rintro (⟨_, i, hi⟩ | hNotCl)
  · simp [constTrue] at hi
  · apply hNotCl
    intro n
    let s' := appendPrefix (takePrefix constTrue (n + 1)) constFalse
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [hasPrefix_takePrefix_iff]
      intro i hi
      have hlen : i < (takePrefix constTrue (n + 1)).length := by
        rw [takePrefix_length]
        exact Nat.lt_trans hi (Nat.lt_succ_self n)
      have h1 := hasPrefix_appendPrefix (takePrefix constTrue (n + 1)) constFalse i hlen
      rw [takePrefix_getElem] at h1
      exact h1
    · have hlen : 0 < (takePrefix constTrue (n + 1)).length := by
        rw [takePrefix_length]
        exact Nat.zero_lt_succ n
      have h1 := hasPrefix_appendPrefix (takePrefix constTrue (n + 1)) constFalse 0 hlen
      rw [takePrefix_getElem] at h1
      exact h1
    · refine ⟨n + 1, ?_⟩
      have hlen : (takePrefix constTrue (n + 1)).length = n + 1 :=
        takePrefix_length constTrue (n + 1)
      simp [s', appendPrefix, hlen, constFalse]

/-- Positive example for `StreamSystem`: the singleton system `{constFalse}` admits `constFalse`. -/
theorem streamSystem_pos_singleton : (fun s : InfTrace Bool => s = constFalse) constFalse :=
  rfl

/-- Negative example for `StreamSystem`: the singleton system `{constFalse}` rejects `constTrue`. -/
theorem streamSystem_neg_singleton : ¬ (fun s : InfTrace Bool => s = constFalse) constTrue := by
  intro h
  have h0 := congrFun h 0
  simp [constFalse, constTrue] at h0

/-- Positive example for `Satisfies`: `{constFalse}` satisfies `AlwaysFalse`. -/
theorem satisfies_pos_constFalse : Satisfies (fun s => s = constFalse) AlwaysFalse := by
  intro s hs
  subst hs
  exact traceProp_pos_alwaysFalse

/-- Negative example for `Satisfies`: `{constTrue}` does not satisfy `AlwaysFalse`. -/
theorem satisfies_neg_constTrue : ¬ Satisfies (fun s => s = constTrue) AlwaysFalse := by
  intro h
  exact traceProp_neg_alwaysFalse (h constTrue rfl)

/-- Positive example for `StreamRefines`: `{constFalse}` refines `AlwaysFalse`. -/
theorem streamRefines_pos_singleton : StreamRefines (fun s => s = constFalse) AlwaysFalse :=
  satisfies_pos_constFalse

/-- Negative example for `StreamRefines`: `{constTrue}` does not refine `AlwaysFalse`. -/
theorem streamRefines_neg_singleton : ¬ StreamRefines (fun s => s = constTrue) AlwaysFalse :=
  satisfies_neg_constTrue

/-- Positive example for `IsNonemptyStream`: `AlwaysFalse` is a nonempty stream system. -/
theorem isNonemptyStream_pos_alwaysFalse : IsNonemptyStream AlwaysFalse :=
  ⟨constFalse, traceProp_pos_alwaysFalse⟩

/-- Negative example for `IsNonemptyStream`: `EmptyProp` is not a nonempty stream system. -/
theorem isNonemptyStream_neg_empty : ¬ IsNonemptyStream (EmptyProp : StreamSystem Bool) := by
  rintro ⟨_, h⟩
  exact h

end Toy.SafetyLiveness
