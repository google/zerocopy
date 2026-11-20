import Toy.SafetyLiveness.Core

/-!
# Stream refinement versus prefix-closed finite-trace refinement

This module contrasts two linear-time refinement relations:
1. **Stream refinement** (`StreamRefines Impl Spec`), which preserves every
   infinite-trace property (safety, liveness, or mixed) by inclusion, and has no
   universal nonempty refiner over alphabets with at least two observations
   (`no_nonempty_streamSystem_refines_all_nonempty`).
2. **Finite-trace refinement** (`FinRefines TImpl TSpec`), where systems are
   prefix-closed nonempty sets of finite traces (as in the CSP traces model of
   Hoare, 1985, and Roscoe, 1997). Here `{[]}` (`doNothingFin`) refines every
   prefix-closed nonempty system, so finite-trace refinement preserves every
   universal linear-time predicate on finite traces (`finRefinesPreserves_linearTime`)
   and every safety property on infinite traces (`finPrefixes_refines_preserves_safety`),
   yet fails every non-safety property (`finPrefixes_refines_fails_of_not_isSafety`),
   every nontrivial liveness property (`finPrefixes_refines_fails_every_nontrivial_liveness`),
   and every finite-trace system property that rejects `{[]}`
   (`finRefines_cannot_preserve_property_rejecting_doNothing`).
-/

namespace Toy.SafetyLiveness

universe u

/-! ### Stream refinement properties and contrast witnesses -/

/-- Stream refinement preserves every linear-time trace property (safety,
liveness, or mixed), directly by transitivity of inclusion. -/
theorem streamRefines_preserves_all_properties
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hRef : StreamRefines Impl Spec) (hSpec : Satisfies Spec P) :
    Satisfies Impl P :=
  fun s hs => hSpec s (hRef s hs)

/-- Stream refinement is transitive, supporting multi-pass refinement chains. -/
theorem streamRefines_trans
    {α : Type u} {S₁ S₂ S₃ : StreamSystem α}
    (h₁₂ : StreamRefines S₁ S₂) (h₂₃ : StreamRefines S₂ S₃) :
    StreamRefines S₁ S₃ :=
  fun s hs => h₂₃ s (h₁₂ s hs)

/-- The empty stream system `EmptyProp` vacuously stream-refines every
specification and vacuously satisfies every property. -/
theorem emptyStreamSystem_refines_all {α : Type u} (Spec : StreamSystem α) :
    StreamRefines EmptyProp Spec :=
  fun _ hs => False.elim hs

/-- Structural contrast between stream inclusion and prefix-closed finite-trace
inclusion: over `Bool`, no nonempty stream system refines every nonempty stream
system (unlike `doNothingFin` in the prefix-closed finite-trace model). -/
theorem no_nonempty_streamSystem_refines_all_nonempty :
    ¬ ∃ Impl : StreamSystem Bool, IsNonemptyStream Impl ∧
        ∀ Spec : StreamSystem Bool, IsNonemptyStream Spec → StreamRefines Impl Spec := by
  rintro ⟨Impl, ⟨s, hs⟩, hAll⟩
  have h := hAll (fun t => t = fun i => !(s i)) ⟨_, rfl⟩ s hs
  have h0 := congrFun h 0
  simp at h0

/-- Over a one-element alphabet (`Unit`), there is only one infinite trace, so
every stream system refines every nonempty stream system. This shows why
`no_nonempty_streamSystem_refines_all_nonempty` requires at least two distinct
observations. -/
theorem unit_streamSystem_refines_all_nonempty (Impl Spec : StreamSystem Unit)
    (hSpec : IsNonemptyStream Spec) : StreamRefines Impl Spec := by
  rcases hSpec with ⟨t, ht⟩
  intro s _
  have hst : s = t := funext fun _ => rfl
  exact hst ▸ ht

/-- Existential possibility predicates are not preserved by stream refinement
even between nonempty systems: `{constFalse}` stream-refines `UnivProp`, which
admits a trace starting with `true`, while `{constFalse}` does not. -/
theorem streamRefines_fails_possibility :
    IsNonemptyStream (fun s : InfTrace Bool => s = constFalse) ∧
      IsNonemptyStream (UnivProp : StreamSystem Bool) ∧
      StreamRefines (fun s : InfTrace Bool => s = constFalse) UnivProp ∧
      (∃ s : InfTrace Bool, (UnivProp : StreamSystem Bool) s ∧ s 0 = true) ∧
      ¬ (∃ s : InfTrace Bool, s = constFalse ∧ s 0 = true) := by
  refine ⟨⟨constFalse, rfl⟩, ⟨constFalse, trivial⟩, fun _ _ => trivial,
    ⟨constTrue, trivial, rfl⟩, ?_⟩
  rintro ⟨s, rfl, h⟩
  cases h

/-- Non-vacuity witness for `streamRefines_preserves_all_properties`: on `Bool`,
`{constTrue}` stream-refines `EventuallyTrue` and `EventuallyTrue` satisfies
itself. -/
theorem streamRefines_preserves_nonvacuity :
    StreamRefines (fun s : InfTrace Bool => s = constTrue) EventuallyTrue ∧
      Satisfies EventuallyTrue EventuallyTrue := by
  refine ⟨fun s hs => ?_, fun _ hs => hs⟩
  subst hs
  exact ⟨0, rfl⟩

/-- Tightness counterexample for `hRef : StreamRefines Impl Spec` in
`streamRefines_preserves_all_properties`: for `Impl = {constFalse}`,
`Spec = EventuallyTrue`, and `P = EventuallyTrue`, `Satisfies Spec P` holds
while `Satisfies Impl P` fails. -/
theorem streamRefines_preserves_tight_refines :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := EventuallyTrue
    Satisfies Spec EventuallyTrue ∧ ¬ Satisfies Impl EventuallyTrue := by
  intro Impl Spec
  refine ⟨fun _ hs => hs, fun hSat => ?_⟩
  rcases hSat constFalse rfl with ⟨i, hi⟩
  simp [constFalse] at hi

/-- Tightness counterexample for `hSpec : Satisfies Spec P` in
`streamRefines_preserves_all_properties`: for `Impl = Spec = {constFalse}` and
`P = EventuallyTrue`, `StreamRefines Impl Spec` holds while `Satisfies Impl P`
fails. -/
theorem streamRefines_preserves_tight_satisfies :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := fun s => s = constFalse
    StreamRefines Impl Spec ∧ ¬ Satisfies Impl EventuallyTrue := by
  intro Impl Spec
  refine ⟨fun _ hs => hs, fun hSat => ?_⟩
  rcases hSat constFalse rfl with ⟨i, hi⟩
  simp [constFalse] at hi

/-! ### Finite-trace semantics definitions -/

/-- `IsPrefix u v` asserts that finite trace `u` is a prefix of finite trace `v`
(`∃ w, u ++ w = v`). Captures extension ordering on finite execution histories. -/
def IsPrefix {α : Type u} (u v : List α) : Prop :=
  ∃ w : List α, u ++ w = v

/-- A system modeled denotationally as a set of finite observable traces
`List α → Prop`. Captures finite-trace semantics (such as the CSP traces model
prior to imposing prefix-closure and nonemptiness). -/
abbrev FinTraceSystem (α : Type u) : Type u := List α → Prop

/-- `IsPrefixClosed T` asserts that whenever `T` admits a finite trace `v`, it
also admits every prefix `u` of `v`. Captures the healthiness condition that
every prefix of an observable finite execution is itself an observable finite
execution. -/
def IsPrefixClosed {α : Type u} (T : FinTraceSystem α) : Prop :=
  ∀ u v : List α, IsPrefix u v → T v → T u

/-- `IsNonemptyFin T` asserts that finite-trace system `T` admits at least one
finite trace. Separated from `IsPrefixClosed` so theorems state nonemptiness
explicitly. -/
def IsNonemptyFin {α : Type u} (T : FinTraceSystem α) : Prop :=
  ∃ u : List α, T u

/-- `FinRefines TImpl TSpec` asserts trace inclusion `TImpl ⊆ TSpec` on finite
traces. Captures CSP traces refinement `TSpec ⊑_T TImpl`. -/
def FinRefines {α : Type u} (TImpl TSpec : FinTraceSystem α) : Prop :=
  ∀ u : List α, TImpl u → TSpec u

/-- The do-nothing finite-trace system `{[]}`, which produces only the empty
trace. Captures CSP `STOP` in the pure traces model (Hoare, 1985; Roscoe, 1997)
as well as immediate halt or operational silent divergence under finite-prefix
projection (`obsFinPrefixes silentDivergeObs = doNothingFin`). Note that in
CSP's failures–divergences model (Brookes and Roscoe, 1985), divergence `⊥` is
instead treated catastrophically with chaotic trace set `Σ*`, opposite to
`STOP`. -/
def doNothingFin {α : Type u} : FinTraceSystem α :=
  fun u => u = []

/-- The set of all finite prefixes of infinite traces produced by a stream
system `S`. Captures projecting an infinite-trace system to its finite-trace
semantics. -/
def finPrefixes {α : Type u} (S : StreamSystem α) : FinTraceSystem α :=
  fun u => ∃ s : InfTrace α, S s ∧ HasPrefix s u

/-- `FinRefinesPreserves Φ` asserts that a predicate `Φ` on finite-trace systems
is preserved downward by `FinRefines` across all prefix-closed nonempty systems.
Captures whether a system-level specification `Φ` survives finite-trace
refinement. -/
def FinRefinesPreserves {α : Type u} (Φ : FinTraceSystem α → Prop) : Prop :=
  ∀ T₁ T₂ : FinTraceSystem α,
    IsPrefixClosed T₁ → IsNonemptyFin T₁ →
    IsPrefixClosed T₂ → IsNonemptyFin T₂ →
    FinRefines T₁ T₂ → Φ T₂ → Φ T₁

/-! ### Elementary finite-trace lemmas -/

theorem isPrefix_nil {α : Type u} (v : List α) : IsPrefix [] v :=
  ⟨v, rfl⟩

theorem isPrefix_refl {α : Type u} (u : List α) : IsPrefix u u :=
  ⟨[], List.append_nil u⟩

theorem isPrefix_trans {α : Type u} {u v w : List α}
    (huv : IsPrefix u v) (hvw : IsPrefix v w) : IsPrefix u w := by
  rcases huv with ⟨x, rfl⟩
  rcases hvw with ⟨y, rfl⟩
  exact ⟨x ++ y, by rw [List.append_assoc]⟩

theorem hasPrefix_of_isPrefix {α : Type u} {s : InfTrace α} {u v : List α}
    (huv : IsPrefix u v) (hsv : HasPrefix s v) : HasPrefix s u := by
  rcases huv with ⟨w, rfl⟩
  intro i hi
  have hi' : i < (u ++ w).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
  have h1 := hsv i hi'
  rw [List.getElem_append_left hi] at h1
  exact h1

theorem doNothingFin_isPrefixClosed {α : Type u} :
    IsPrefixClosed (doNothingFin : FinTraceSystem α) := by
  intro u v huv hv
  rw [doNothingFin] at hv ⊢
  subst hv
  rcases huv with ⟨w, hw⟩
  cases u with
  | nil => rfl
  | cons a t => simp at hw

theorem doNothingFin_isNonemptyFin {α : Type u} :
    IsNonemptyFin (doNothingFin : FinTraceSystem α) :=
  ⟨[], rfl⟩

theorem nil_mem_of_isPrefixClosed_isNonemptyFin {α : Type u} {T : FinTraceSystem α}
    (hClosed : IsPrefixClosed T) (hNonempty : IsNonemptyFin T) :
    T [] := by
  rcases hNonempty with ⟨u, hu⟩
  exact hClosed [] u (isPrefix_nil u) hu

theorem finPrefixes_isPrefixClosed {α : Type u} (S : StreamSystem α) :
    IsPrefixClosed (finPrefixes S) := by
  intro u v huv hv
  rcases hv with ⟨s, hs, hsv⟩
  exact ⟨s, hs, hasPrefix_of_isPrefix huv hsv⟩

theorem finPrefixes_isNonemptyFin_of_isNonemptyStream {α : Type u} {S : StreamSystem α}
    (hNE : IsNonemptyStream S) :
    IsNonemptyFin (finPrefixes S) := by
  rcases hNE with ⟨s, hs⟩
  exact ⟨[], s, hs, hasPrefix_nil s⟩

theorem finPrefixes_eq_univ_of_isLiveness {α : Type u} {P : TraceProp α}
    (hLive : IsLiveness P) (u : List α) :
    finPrefixes P u := by
  rcases hLive u with ⟨s, hpre, hP⟩
  exact ⟨s, hP, hpre⟩

/-! ### Positive and negative examples for finite-trace definitions -/

/-- Positive example for `IsPrefix`: `[false]` is a prefix of `[false, true]`. -/
theorem isPrefix_pos_example : IsPrefix [false] [false, true] :=
  ⟨[true], rfl⟩

/-- Negative example for `IsPrefix`: `[true]` is not a prefix of `[false, true]`. -/
theorem isPrefix_neg_example : ¬ IsPrefix [true] [false, true] := by
  rintro ⟨w, hw⟩
  simp at hw

/-- Positive example for `FinTraceSystem` and `doNothingFin`: `[]` lies in `doNothingFin`. -/
theorem doNothingFin_pos_nil : (doNothingFin : FinTraceSystem Bool) [] :=
  rfl

/-- Negative example for `FinTraceSystem` and `doNothingFin`: `[true]` does not lie in `doNothingFin`. -/
theorem doNothingFin_neg_true : ¬ (doNothingFin : FinTraceSystem Bool) [true] := by
  intro h
  cases h

/-- Positive example for `IsPrefixClosed`: `doNothingFin` is prefix-closed. -/
theorem isPrefixClosed_pos_doNothing : IsPrefixClosed (doNothingFin : FinTraceSystem Bool) :=
  doNothingFin_isPrefixClosed

/-- Negative example for `IsPrefixClosed`: `{[true]}` is not prefix-closed because it omits `[]`. -/
theorem isPrefixClosed_neg_singletonTrue : ¬ IsPrefixClosed (fun u : List Bool => u = [true]) := by
  intro hClosed
  have hnil : ([] : List Bool) = [true] := hClosed [] [true] (isPrefix_nil [true]) rfl
  cases hnil

/-- Positive example for `IsNonemptyFin`: `doNothingFin` is nonempty. -/
theorem isNonemptyFin_pos_doNothing : IsNonemptyFin (doNothingFin : FinTraceSystem Bool) :=
  doNothingFin_isNonemptyFin

/-- Negative example for `IsNonemptyFin`: the empty finite-trace system is not nonempty. -/
theorem isNonemptyFin_neg_empty : ¬ IsNonemptyFin (fun _ : List Bool => False) := by
  rintro ⟨_, h⟩
  exact h

/-- A prefix-closed finite-trace system that can emit `[true]`. -/
def emitTrueFin : FinTraceSystem Bool :=
  fun u => u = [] ∨ u = [true]

theorem emitTrueFin_isPrefixClosed : IsPrefixClosed emitTrueFin := by
  intro u v huv hv
  rcases hv with rfl | rfl
  · rcases huv with ⟨w, hw⟩
    cases u with
    | nil => exact Or.inl rfl
    | cons a t => simp at hw
  · rcases huv with ⟨w, hw⟩
    cases u with
    | nil => exact Or.inl rfl
    | cons a t =>
      cases t with
      | nil =>
        simp at hw
        exact Or.inr (by simp [hw.1])
      | cons b t' =>
        simp at hw

theorem emitTrueFin_isNonemptyFin : IsNonemptyFin emitTrueFin :=
  ⟨[], Or.inl rfl⟩

/-- Positive example for `FinRefines`: `doNothingFin` refines `emitTrueFin`. -/
theorem finRefines_pos_doNothing_emitTrue : FinRefines doNothingFin emitTrueFin := by
  intro u hu
  rw [doNothingFin] at hu
  exact Or.inl hu

/-- Negative example for `FinRefines`: `emitTrueFin` does not refine `doNothingFin`. -/
theorem finRefines_neg_emitTrue_doNothing : ¬ FinRefines emitTrueFin doNothingFin := by
  intro hRef
  have h : ([true] : List Bool) = [] := hRef [true] (Or.inr rfl)
  cases h

/-- Positive example for `finPrefixes`: `[false, false]` is a finite prefix of `AlwaysFalse`. -/
theorem finPrefixes_pos_alwaysFalse : finPrefixes AlwaysFalse [false, false] :=
  ⟨constFalse, traceProp_pos_alwaysFalse, hasPrefix_pos_constFalse⟩

/-- Negative example for `finPrefixes`: `[true]` is not a finite prefix of `AlwaysFalse`. -/
theorem finPrefixes_neg_alwaysFalse : ¬ finPrefixes AlwaysFalse [true] := by
  rintro ⟨s, hAll, hpre⟩
  have h0 : s 0 = true := hpre 0 (by simp)
  have hf : s 0 = false := hAll 0
  rw [h0] at hf
  contradiction

/-- A universal linear-time finite-trace predicate: no trace contains `true`. -/
def FinNeverTrue : FinTraceSystem Bool → Prop :=
  fun T => ∀ u : List Bool, T u → ∀ b ∈ u, b = false

/-- Positive example for `FinRefinesPreserves`: the universal finite-trace
predicate `FinNeverTrue` is preserved by `FinRefines`. -/
theorem finRefinesPreserves_pos_neverTrue : FinRefinesPreserves FinNeverTrue := by
  intro T₁ T₂ _ _ _ _ hRef hT₂ u hu b hb
  exact hT₂ u (hRef u hu) b hb

/-- An existential possibility predicate on finite-trace systems: at least one
nonempty trace is possible. -/
def FinHasNonemptyTrace : FinTraceSystem Bool → Prop :=
  fun T => ∃ u : List Bool, T u ∧ u ≠ []

/-- Negative example for `FinRefinesPreserves`: `FinHasNonemptyTrace` is not
preserved by `FinRefines` (because `doNothingFin` refines `emitTrueFin`). -/
theorem finRefinesPreserves_neg_hasNonemptyTrace : ¬ FinRefinesPreserves FinHasNonemptyTrace := by
  intro hPres
  have hEmit : FinHasNonemptyTrace emitTrueFin := ⟨[true], Or.inr rfl, by decide⟩
  have hDo : FinHasNonemptyTrace doNothingFin :=
    hPres doNothingFin emitTrueFin doNothingFin_isPrefixClosed doNothingFin_isNonemptyFin
      emitTrueFin_isPrefixClosed emitTrueFin_isNonemptyFin finRefines_pos_doNothing_emitTrue hEmit
  rcases hDo with ⟨u, hu, hne⟩
  exact hne hu

/-! ### Finite-trace refinement theorems, characterizations, and impossibilities -/

/-- Exact characterization of `FinRefines doNothingFin Spec`: `{[]}` refines
`Spec` if and only if `Spec` contains the empty trace `[]`. -/
theorem doNothingFin_finRefines_iff_nil_mem {α : Type u} (Spec : FinTraceSystem α) :
    FinRefines doNothingFin Spec ↔ Spec [] :=
  ⟨fun h => h [] rfl, fun h v hv => by
    have hv0 : v = [] := hv
    subst hv0
    exact h⟩

/-- Witness that `IsPrefixClosed Spec` is a traces-model healthiness condition
rather than a necessary condition for `FinRefines doNothingFin Spec`:
`{[], [true, false]}` is nonempty and not prefix-closed, yet `doNothingFin`
still refines it because `[]` belongs to it. -/
theorem doNothingFin_finRefines_without_prefixClosed :
    let Spec : FinTraceSystem Bool := fun v => v = [] ∨ v = [true, false]
    ¬ IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ FinRefines doNothingFin Spec := by
  intro Spec
  refine ⟨?_, ⟨[], Or.inl rfl⟩, (doNothingFin_finRefines_iff_nil_mem Spec).mpr (Or.inl rfl)⟩
  intro hC
  rcases hC [true] [true, false] ⟨[false], rfl⟩ (Or.inr rfl) with h | h <;> cases h

/-- In prefix-closed finite-trace semantics, `doNothingFin` (`{[]}`) refines
every prefix-closed nonempty system `Spec`. -/
theorem doNothingFin_refines_every_prefixClosed_nonempty
    {α : Type u} {Spec : FinTraceSystem α}
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec) :
    FinRefines doNothingFin Spec :=
  (doNothingFin_finRefines_iff_nil_mem Spec).mpr
    (nil_mem_of_isPrefixClosed_isNonemptyFin hClosed hNonempty)

/-- Every universal linear-time finite-trace predicate `T ↦ ∀ v, T v → Q v` is
preserved by `FinRefines`. -/
theorem finRefinesPreserves_linearTime {α : Type u} (Q : List α → Prop) :
    FinRefinesPreserves (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v) :=
  fun _ _ _ _ _ _ hRef h v hv => h v (hRef v hv)

/-- Every universal linear-time finite-trace predicate `T ↦ ∀ v, T v → Q v`
that accepts a prefix-closed nonempty `Spec` also accepts `doNothingFin`
(because `[] ∈ Spec`). -/
theorem linearTime_pred_accepts_doNothing_of_accepts_healthy
    {α : Type u} {Spec : FinTraceSystem α} (Q : List α → Prop)
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec)
    (hSpec : ∀ v : List α, Spec v → Q v) :
    ∀ v : List α, doNothingFin v → Q v := by
  intro v hv
  have hv0 : v = [] := hv
  subst hv0
  exact hSpec [] (nil_mem_of_isPrefixClosed_isNonemptyFin hClosed hNonempty)

/-- Consequently, no universal linear-time predicate `T ↦ ∀ v, T v → Q v` on
finite traces can simultaneously satisfy the four hypotheses of
`finRefines_cannot_preserve_property_rejecting_doNothing`. -/
theorem linearTime_never_meets_impossibility_hyps
    {α : Type u} (Q : List α → Prop) (Spec : FinTraceSystem α) :
    ¬ (IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧
        (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v) Spec ∧
        ¬ (fun T : FinTraceSystem α => ∀ v : List α, T v → Q v) doNothingFin) := by
  rintro ⟨hClosed, hNonempty, hSpec, hReject⟩
  exact hReject (linearTime_pred_accepts_doNothing_of_accepts_healthy Q hClosed hNonempty hSpec)

/-- Finite-trace progress impossibility: no system predicate `Φ` on finite-trace
systems that holds for some prefix-closed nonempty `Spec` and rejects
`doNothingFin` can be preserved by finite-trace refinement across prefix-closed
nonempty systems. -/
theorem finRefines_cannot_preserve_property_rejecting_doNothing
    {α : Type u} {Spec : FinTraceSystem α} {Φ : FinTraceSystem α → Prop}
    (hClosed : IsPrefixClosed Spec) (hNonempty : IsNonemptyFin Spec)
    (hSpec : Φ Spec) (hReject : ¬ Φ doNothingFin) :
    ¬ FinRefinesPreserves Φ := by
  intro hPres
  have hRef : FinRefines doNothingFin Spec :=
    doNothingFin_refines_every_prefixClosed_nonempty hClosed hNonempty
  exact hReject (hPres doNothingFin Spec doNothingFin_isPrefixClosed doNothingFin_isNonemptyFin
    hClosed hNonempty hRef hSpec)

/-- Finite-prefix refinement `FinRefines (finPrefixes Impl) (finPrefixes Spec)`
places `Impl` inside the topological closure `Closure Spec` (not necessarily
inside `Spec` itself). -/
theorem streamRefines_closure_of_finPrefixes_refines
    {α : Type u} {Impl Spec : StreamSystem α}
    (hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec)) :
    StreamRefines Impl (Closure Spec) := by
  intro s hs n
  rcases hRef (takePrefix s n) ⟨s, hs, hasPrefix_takePrefix s n⟩ with ⟨s', hs', hpre'⟩
  exact ⟨s', hpre', hs'⟩

/-- Finite-prefix refinement between stream systems
(`FinRefines (finPrefixes Impl) (finPrefixes Spec)`) preserves every safety
property `P`. -/
theorem finPrefixes_refines_preserves_safety
    {α : Type u} {Impl Spec : StreamSystem α} {P : TraceProp α}
    (hSafe : IsSafety P)
    (hRef : FinRefines (finPrefixes Impl) (finPrefixes Spec))
    (hSpec : Satisfies Spec P) :
    Satisfies Impl P := by
  intro s hs
  apply Classical.byContradiction
  intro hNotP
  rcases hSafe s hNotP with ⟨n, hn⟩
  have hPreImpl : finPrefixes Impl (takePrefix s n) :=
    ⟨s, hs, hasPrefix_takePrefix s n⟩
  rcases hRef (takePrefix s n) hPreImpl with ⟨s', hs', hpre'⟩
  exact hn s' hpre' (hSpec s' hs')

/-- Finite-prefix refinement between nonempty stream systems fails to preserve
every nontrivial liveness property `P`, explicitly witnessed by `Impl := {s₀}`
and `Spec := P` for any infinite trace `s₀` outside `P`. -/
theorem finPrefixes_refines_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P := by
  refine ⟨⟨s₀, rfl⟩, ?_, fun _ h => h, ?_, ?_⟩
  · rcases hLive [] with ⟨s, _, hP⟩
    exact ⟨s, hP⟩
  · intro u _
    exact finPrefixes_eq_univ_of_isLiveness hLive u
  · intro hSat
    exact hNotP (hSat s₀ rfl)

/-- Converse to `finPrefixes_refines_preserves_safety`: finite-prefix refinement
fails to preserve EVERY non-safety property `P` (including mixed safety-plus-liveness
properties), witnessed by some `s₀ ∈ Closure P \ P` against `Spec = P`. Thus
dropping `IsLiveness P` in favor of a mixed non-safety property does not rescue
finite-prefix refinement. -/
theorem finPrefixes_refines_fails_of_not_isSafety
    {α : Type u} {P : TraceProp α} (hNotSafe : ¬ IsSafety P) :
    ∃ s₀ : InfTrace α,
      IsNonemptyStream (fun s => s = s₀) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      FinRefines (finPrefixes (fun s => s = s₀)) (finPrefixes P) ∧
      ¬ Satisfies (fun s => s = s₀) P := by
  have hex : ∃ s₀ : InfTrace α, ¬ P s₀ ∧ Closure P s₀ := by
    apply Classical.byContradiction
    intro hNone
    apply hNotSafe
    intro s hNotP
    apply Classical.byContradiction
    intro hNoBad
    apply hNone
    refine ⟨s, hNotP, fun n => ?_⟩
    apply Classical.byContradiction
    intro hNoExt
    apply hNoBad
    refine ⟨n, fun s' hpre hPs' => hNoExt ⟨s', hpre, hPs'⟩⟩
  rcases hex with ⟨s₀, hNotP₀, hCl₀⟩
  rcases hCl₀ 0 with ⟨s_wit, _, hP_wit⟩
  refine ⟨s₀, ⟨s₀, rfl⟩, ⟨s_wit, hP_wit⟩, fun _ h => h, ?_, ?_⟩
  · intro u hu
    rcases hu with ⟨s, hs, hpre⟩
    subst hs
    rcases hCl₀ u.length with ⟨s', hpre', hPs'⟩
    rw [takePrefix_eq_of_hasPrefix hpre] at hpre'
    exact ⟨s', hPs', hpre'⟩
  · intro hSat
    exact hNotP₀ (hSat s₀ rfl)

/-- Even bidirectional finite-prefix equality (`finPrefixes Impl = finPrefixes Spec`)
fails to preserve every nontrivial liveness property `P`, witnessed by
`Impl := UnivProp` and `Spec := P`. -/
theorem finPrefixes_eq_fails_every_nontrivial_liveness
    {α : Type u} {P : TraceProp α} {s₀ : InfTrace α}
    (hLive : IsLiveness P) (hNotP : ¬ P s₀) :
    IsNonemptyStream (UnivProp : StreamSystem α) ∧
      IsNonemptyStream P ∧
      Satisfies P P ∧
      finPrefixes (UnivProp : StreamSystem α) = finPrefixes P ∧
      ¬ Satisfies (UnivProp : StreamSystem α) P := by
  rcases hLive [] with ⟨s_wit, _, hP_wit⟩
  refine ⟨⟨s₀, trivial⟩, ⟨s_wit, hP_wit⟩, fun _ h => h, ?_, ?_⟩
  · funext u
    apply propext
    constructor
    · intro _
      exact finPrefixes_eq_univ_of_isLiveness hLive u
    · intro _
      exact ⟨appendPrefix u s₀, trivial, hasPrefix_appendPrefix u s₀⟩
  · intro hSat
    exact hNotP (hSat s₀ trivial)

/-! ### Non-vacuity witnesses and tightness counterexamples -/

/-- Non-vacuity witness for `doNothingFin_refines_every_prefixClosed_nonempty`:
`emitTrueFin` on `Bool` is both prefix-closed and nonempty. -/
theorem doNothingFin_refines_nonvacuity :
    IsPrefixClosed emitTrueFin ∧ IsNonemptyFin emitTrueFin :=
  ⟨emitTrueFin_isPrefixClosed, emitTrueFin_isNonemptyFin⟩

/-- Tightness counterexample for `hClosed : IsPrefixClosed Spec` in
`doNothingFin_refines_every_prefixClosed_nonempty`: `{[true]}` is nonempty,
not prefix-closed, and `doNothingFin` does not refine it. -/
theorem singletonTrueTrace_tight_prefixClosed :
    IsNonemptyFin (fun u : List Bool => u = [true]) ∧
      ¬ FinRefines doNothingFin (fun u : List Bool => u = [true]) := by
  refine ⟨⟨[true], rfl⟩, fun hRef => ?_⟩
  have h : ([] : List Bool) = [true] := hRef [] rfl
  cases h

/-- Tightness counterexample for `hNonempty : IsNonemptyFin Spec` in
`doNothingFin_refines_every_prefixClosed_nonempty`: the empty finite-trace
system is prefix-closed, empty, and `doNothingFin` does not refine it. -/
theorem emptyFinSystem_tight_nonempty :
    IsPrefixClosed (fun _ : List Bool => False) ∧
      ¬ FinRefines doNothingFin (fun _ : List Bool => False) := by
  refine ⟨fun _ _ _ h => False.elim h, fun hRef => hRef [] rfl⟩

/-- Non-vacuity witness for `finRefines_cannot_preserve_property_rejecting_doNothing`:
`emitTrueFin` with `FinHasNonemptyTrace`. -/
theorem finRefines_cannot_preserve_nonvacuity :
    IsPrefixClosed emitTrueFin ∧
      IsNonemptyFin emitTrueFin ∧
      FinHasNonemptyTrace emitTrueFin ∧
      ¬ FinHasNonemptyTrace doNothingFin := by
  refine ⟨emitTrueFin_isPrefixClosed, emitTrueFin_isNonemptyFin, ⟨[true], Or.inr rfl, by decide⟩, ?_⟩
  rintro ⟨u, hu, hne⟩
  exact hne hu

/-- Tightness counterexample for `hClosed : IsPrefixClosed Spec` in
`finRefines_cannot_preserve_property_rejecting_doNothing`: for `Spec = {[true]}`
and `Φ T := ∀ u, T u → u ≠ []`, all other hypotheses hold yet `FinRefinesPreserves Φ`
holds vacuously (no prefix-closed nonempty system satisfies `Φ`). -/
theorem finRefines_impossibility_tight_prefixClosed :
    let Spec : FinTraceSystem Bool := fun u => u = [true]
    let Φ : FinTraceSystem Bool → Prop := fun T => ∀ u, T u → u ≠ []
    IsNonemptyFin Spec ∧ Φ Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ := by
  refine ⟨⟨[true], rfl⟩, fun u hu => by subst hu; decide, ?_, ?_⟩
  · intro h
    exact h [] rfl rfl
  · intro T₁ T₂ _ _ hClosed₂ hNE₂ _ hT₂
    exact False.elim (hT₂ [] (nil_mem_of_isPrefixClosed_isNonemptyFin hClosed₂ hNE₂) rfl)

/-- Tightness counterexample for `hNonempty : IsNonemptyFin Spec` in
`finRefines_cannot_preserve_property_rejecting_doNothing`: for `Spec = ∅` and
`Φ T := ¬ T []`, all other hypotheses hold yet `FinRefinesPreserves Φ` holds
vacuously (every prefix-closed nonempty system contains `[]`). -/
theorem finRefines_impossibility_tight_nonempty :
    let Spec : FinTraceSystem Bool := fun _ => False
    let Φ : FinTraceSystem Bool → Prop := fun T => ¬ T []
    IsPrefixClosed Spec ∧ Φ Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ := by
  refine ⟨fun _ _ _ h => False.elim h, id, fun h => h rfl, ?_⟩
  intro T₁ T₂ _ _ hClosed₂ hNE₂ _ hT₂
  exact False.elim (hT₂ (nil_mem_of_isPrefixClosed_isNonemptyFin hClosed₂ hNE₂))

/-- Tightness counterexample for `hSpec : Φ Spec` in
`finRefines_cannot_preserve_property_rejecting_doNothing`: `Φ := fun _ => False`
is preserved vacuously. -/
theorem finRefines_impossibility_tight_spec :
    let Spec : FinTraceSystem Bool := doNothingFin
    let Φ : FinTraceSystem Bool → Prop := fun _ => False
    IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ ¬ Φ doNothingFin ∧ FinRefinesPreserves Φ :=
  ⟨doNothingFin_isPrefixClosed, doNothingFin_isNonemptyFin, id, fun _ _ _ _ _ _ _ h => h⟩

/-- Tightness counterexample for `hReject : ¬ Φ doNothingFin` in
`finRefines_cannot_preserve_property_rejecting_doNothing`: `Φ := fun _ => True`
is trivially preserved. -/
theorem finRefines_impossibility_tight_reject :
    let Spec : FinTraceSystem Bool := doNothingFin
    let Φ : FinTraceSystem Bool → Prop := fun _ => True
    IsPrefixClosed Spec ∧ IsNonemptyFin Spec ∧ Φ Spec ∧ FinRefinesPreserves Φ :=
  ⟨doNothingFin_isPrefixClosed, doNothingFin_isNonemptyFin, trivial, fun _ _ _ _ _ _ _ _ => trivial⟩

/-- Non-vacuity witness for `finPrefixes_refines_preserves_safety`: `{constFalse}`
refines `AlwaysFalse` on finite prefixes, and `AlwaysFalse` is a safety property
satisfying itself. -/
theorem finPrefixes_preserves_safety_nonvacuity :
    IsSafety AlwaysFalse ∧
      FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes AlwaysFalse) ∧
      Satisfies AlwaysFalse AlwaysFalse := by
  refine ⟨alwaysFalse_isSafety, ?_, fun _ h => h⟩
  intro u hu
  rcases hu with ⟨s, hs, hpre⟩
  subst hs
  exact ⟨constFalse, traceProp_pos_alwaysFalse, hpre⟩

/-- Tightness counterexample for `hSafe : IsSafety P` in
`finPrefixes_refines_preserves_safety`: for `Impl = {constFalse}`,
`Spec = EventuallyTrue`, and `P = EventuallyTrue`, `FinRefines` on `finPrefixes`
and `Satisfies Spec P` hold while `Satisfies Impl P` fails. -/
theorem eventuallyTrue_tight_finPrefixes_safety :
    let Impl : StreamSystem Bool := fun s => s = constFalse
    let Spec : StreamSystem Bool := EventuallyTrue
    FinRefines (finPrefixes Impl) (finPrefixes Spec) ∧
      Satisfies Spec EventuallyTrue ∧
      ¬ Satisfies Impl EventuallyTrue := by
  intro Impl Spec
  refine ⟨fun u _ => finPrefixes_eq_univ_of_isLiveness eventuallyTrue_isLiveness u,
    fun _ h => h, ?_⟩
  intro hSat
  rcases hSat constFalse rfl with ⟨i, hi⟩
  simp [constFalse] at hi

/-- Tightness counterexample for `hRef` in `finPrefixes_refines_preserves_safety`:
for `Impl = {constTrue}`, `Spec = AlwaysFalse`, and `P = AlwaysFalse`,
`IsSafety AlwaysFalse` and `Satisfies Spec AlwaysFalse` hold while
`Satisfies Impl AlwaysFalse` fails. -/
theorem finPrefixes_safety_tight_refines :
    let Impl : StreamSystem Bool := fun s => s = constTrue
    let Spec : StreamSystem Bool := AlwaysFalse
    IsSafety AlwaysFalse ∧
      Satisfies Spec AlwaysFalse ∧
      ¬ Satisfies Impl AlwaysFalse :=
  ⟨alwaysFalse_isSafety, fun _ h => h, satisfies_neg_constTrue⟩

/-- Tightness counterexample for `hSpec` in `finPrefixes_refines_preserves_safety`:
for `Impl = Spec = {constTrue}` and `P = AlwaysFalse`, `IsSafety AlwaysFalse`
and `FinRefines (finPrefixes Impl) (finPrefixes Spec)` hold while
`Satisfies Impl AlwaysFalse` fails. -/
theorem finPrefixes_safety_tight_satisfies :
    let Impl : StreamSystem Bool := fun s => s = constTrue
    let Spec : StreamSystem Bool := fun s => s = constTrue
    IsSafety AlwaysFalse ∧
      FinRefines (finPrefixes Impl) (finPrefixes Spec) ∧
      ¬ Satisfies Impl AlwaysFalse :=
  ⟨alwaysFalse_isSafety, fun _ h => h, satisfies_neg_constTrue⟩

/-- Non-vacuity witness for `finPrefixes_refines_fails_every_nontrivial_liveness`:
on `Bool`, `EventuallyTrue` is live and rejects `constFalse`. -/
theorem finPrefixes_fails_liveness_nonvacuity :
    IsLiveness EventuallyTrue ∧ ¬ EventuallyTrue constFalse := by
  refine ⟨eventuallyTrue_isLiveness, ?_⟩
  rintro ⟨i, hi⟩
  simp [constFalse] at hi

/-- Tightness counterexample for `hLive : IsLiveness P` in
`finPrefixes_refines_fails_every_nontrivial_liveness`: for `P = AlwaysFalse` and
`s₀ = constTrue`, `¬ AlwaysFalse constTrue` holds, yet the 5-way failure
conclusion for `Impl = {constTrue}` against `Spec = AlwaysFalse` fails because
`AlwaysFalse` is a safety property (preserved by `finPrefixes_refines_preserves_safety`). -/
theorem alwaysFalse_tight_finPrefixes_liveness :
    ¬ AlwaysFalse constTrue ∧
      ¬ (IsNonemptyStream (fun s => s = constTrue) ∧
         IsNonemptyStream AlwaysFalse ∧
         Satisfies AlwaysFalse AlwaysFalse ∧
         FinRefines (finPrefixes (fun s => s = constTrue)) (finPrefixes AlwaysFalse) ∧
         ¬ Satisfies (fun s => s = constTrue) AlwaysFalse) := by
  refine ⟨traceProp_neg_alwaysFalse, ?_⟩
  rintro ⟨_, _, _, hRef, _⟩
  have hPre : finPrefixes (fun s => s = constTrue) [true] := by
    refine ⟨constTrue, rfl, fun i hi => ?_⟩
    match i with
    | 0 => rfl
    | n + 1 => simp at hi
  exact finPrefixes_neg_alwaysFalse (hRef [true] hPre)

/-- Tightness counterexample for `hNotP : ¬ P s₀` in
`finPrefixes_refines_fails_every_nontrivial_liveness`: for `P = UnivProp` and
`s₀ = constFalse`, `IsLiveness UnivProp` holds, yet the 5-way failure
conclusion fails because `{constFalse}` satisfies `UnivProp`. -/
theorem univ_tight_finPrefixes_liveness :
    IsLiveness (UnivProp : TraceProp Bool) ∧
      ¬ (IsNonemptyStream (fun s => s = constFalse) ∧
         IsNonemptyStream (UnivProp : StreamSystem Bool) ∧
         Satisfies (UnivProp : StreamSystem Bool) UnivProp ∧
         FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes UnivProp) ∧
         ¬ Satisfies (fun s => s = constFalse) UnivProp) := by
  refine ⟨univProp_isLiveness ⟨false⟩, ?_⟩
  rintro ⟨_, _, _, _, hNotSat⟩
  exact hNotSat (fun _ _ => trivial)

end Toy.SafetyLiveness
