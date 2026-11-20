import Toy.SafetyLiveness.Core
import Toy.SafetyLiveness.Refinement

/-!
# Complete observable behaviors with explicit termination and divergence

This module provides the positive control for prefix-closed finite-trace
refinement: modeling each closed-program execution as terminating after a finite
event trace (`terminates u`), silently diverging after a finite event trace
(`diverges u`), or producing an infinite reactive event trace (`reacts s`),
following behavioral inclusion refinement in Leroy (2009, §§2.1 & 3.4),
Leroy and Grall (2009), and the `Terminates / Diverges / Reacts` inductive
behavior split of CompCert's Coq mechanization (`common/Behaviors.v`), omitting
exit codes and undefined-behavior wildcards.

Under complete-behavior inclusion (`ObsRefines`):
- The universal linear-time predicate `ObsSatisfies · EmitsEvent` is preserved
  across nonempty systems while holding for `emitTrueObs` and rejecting both
  `silentDivergeObs` and `immediateHaltObs`
  (`obsRefinesPreserves_emitsEvent_rejects_doNothing`).
- Every nonempty do-nothing implementation (`obsFinPrefixes Impl ⊆ {[]}`) passes
  finite-trace refinement against every nonempty specification satisfying
  `EmitsEvent`, yet fails `ObsRefines`
  (`obsRefines_separates_doNothing_from_finRefines`, factored into
  `finRefines_obsFinPrefixes_of_doNothing` and `not_obsRefines_of_silent_behavior`).
- Whenever `u` is an observable finite prefix of `Spec` (`obsFinPrefixes Spec u`)
  and `Spec` forbids silent divergence at `u` (`¬ Spec (.diverges u)`),
  `Impl := {.diverges u}` passes `FinRefines` on `obsFinPrefixes` while failing
  `ObsRefines` (`obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges`),
  including on the identical complete trace `[true]` against `{.terminates [true]}`
  (`divergeAfterTrue_separates_sameTrace_terminates`).
- Projection `obsFinPrefixes` is monotone from `ObsRefines` to `FinRefines`
  (`obsRefines_implies_finRefines`).
-/

namespace Toy.SafetyLiveness

universe u

/-! ### Complete observable-behavior definitions -/

/-- Complete observable behavior of a closed execution over event alphabet `α`:
either clean termination after a finite event trace `terminates u`, silent
non-termination (divergence/hang with no further observable events) after a
finite event trace `diverges u`, or an infinite reactive event trace
`reacts s`. Mirrors the `Terminates / Diverges / Reacts` split of CompCert's Coq
mechanization (`common/Behaviors.v`; cf. Leroy, 2009, §3.4), simplifying by
omitting integer exit codes/return values on `terminates` and omitting
undefined-behavior wildcards (`Goes_wrong`). -/
inductive ObsBehavior (α : Type u) : Type u where
  | terminates (trace : List α) : ObsBehavior α
  | diverges (trace : List α) : ObsBehavior α
  | reacts (stream : InfTrace α) : ObsBehavior α

/-- A property of complete observable behaviors. Captures specifications that
can constrain termination, divergence-freedom, and infinite reactive liveness. -/
abbrev ObsProp (α : Type u) : Type u := ObsBehavior α → Prop

/-- A system modeled denotationally as its set of possible complete observable
behaviors. -/
abbrev ObsSystem (α : Type u) : Type u := ObsBehavior α → Prop

/-- `ObsSatisfies S Q` asserts that every complete behavior of system `S`
satisfies behavior property `Q`. -/
def ObsSatisfies {α : Type u} (S : ObsSystem α) (Q : ObsProp α) : Prop :=
  ∀ b : ObsBehavior α, S b → Q b

/-- `ObsRefines Impl Spec` asserts behavioral inclusion `Impl ⊆ Spec` over
complete observable behaviors (preserving termination, divergence, and infinite
reactive traces; cf. backward simulation in Leroy, 2009, §2.1, Definition 2). -/
def ObsRefines {α : Type u} (Impl Spec : ObsSystem α) : Prop :=
  ∀ b : ObsBehavior α, Impl b → Spec b

/-- `IsNonemptyObs S` asserts that system `S` has at least one complete
observable behavior. Separated from `ObsSystem` so totality/nonemptiness is an
explicit hypothesis rather than a silent invariant. -/
def IsNonemptyObs {α : Type u} (S : ObsSystem α) : Prop :=
  ∃ b : ObsBehavior α, S b

/-- `ObsRefinesPreserves Φ` asserts that a system-level predicate `Φ` on
complete-behavior systems is preserved downward by `ObsRefines` across all
nonempty behavior systems. Mirrors `FinRefinesPreserves` on `ObsSystem α`. -/
def ObsRefinesPreserves {α : Type u} (Φ : ObsSystem α → Prop) : Prop :=
  ∀ T₁ T₂ : ObsSystem α,
    IsNonemptyObs T₁ → IsNonemptyObs T₂ →
    ObsRefines T₁ T₂ → Φ T₂ → Φ T₁

/-- The finite observable prefixes of a single complete behavior `b`.
Forgets the distinction between termination, silent divergence, and infinite
continuation. -/
def behaviorPrefixes {α : Type u} : ObsBehavior α → FinTraceSystem α
  | .terminates u => fun v => IsPrefix v u
  | .diverges u   => fun v => IsPrefix v u
  | .reacts s     => fun v => HasPrefix s v

/-- Forgetful projection from a complete-behavior system `S` to its
prefix-closed finite-trace semantics. -/
def obsFinPrefixes {α : Type u} (S : ObsSystem α) : FinTraceSystem α :=
  fun v => ∃ b : ObsBehavior α, S b ∧ behaviorPrefixes b v

/-- Initial-event progress property on complete behaviors: the execution emits
at least one observable event (rejecting both immediate empty termination
`.terminates []` and immediate silent divergence `.diverges []`). Note that
because `terminates` omits return values, pure value-returning computations with
no I/O events fail `EmitsEvent`; moreover, `EmitsEvent` accepts post-event
silent divergence `.diverges (a :: u)` (ruling that out requires `NoDivergence`
or `¬ Spec (.diverges u)`). -/
def EmitsEvent {α : Type u} : ObsProp α
  | .terminates u => u ≠ []
  | .diverges u   => u ≠ []
  | .reacts _     => True

/-- Existential possibility analogue of `FinHasNonemptyTrace` on complete-behavior
systems: at least one behavior in `S` emits an observable event. Unlike the
universal predicate `ObsSatisfies · EmitsEvent`, this existential predicate is
NOT preserved by `ObsRefines` (`obsRefines_fails_possibility_canEmit`). -/
def ObsCanEmit {α : Type u} (S : ObsSystem α) : Prop :=
  ∃ b : ObsBehavior α, S b ∧ EmitsEvent b

/-- Divergence-freedom property on complete behaviors: silent divergence
`.diverges u` never occurs after any finite trace `u`. -/
def NoDivergence {α : Type u} : ObsProp α
  | .terminates _ => True
  | .diverges _   => False
  | .reacts _     => True

/-- The silently diverging do-nothing implementation `{.diverges []}` (for
example, an infinite silent loop `while (true) {}`). -/
def silentDivergeObs {α : Type u} : ObsSystem α :=
  fun b => b = .diverges []

/-- The immediately halting empty-trace implementation `{.terminates []}` (an
execution that terminates without emitting any observable event in `α`). -/
def immediateHaltObs {α : Type u} : ObsSystem α :=
  fun b => b = .terminates []

/-- Embedding of a pure infinite-trace system `S` into `ObsSystem α` as
purely reactive behaviors `.reacts s`. -/
def embedStreams {α : Type u} (S : StreamSystem α) : ObsSystem α
  | .reacts s => S s
  | _         => False

/-! ### Elementary observable-behavior and monotonicity lemmas -/

theorem behaviorPrefixes_nil {α : Type u} (b : ObsBehavior α) :
    behaviorPrefixes b [] := by
  cases b with
  | terminates u => exact isPrefix_nil u
  | diverges u   => exact isPrefix_nil u
  | reacts s     => exact hasPrefix_nil s

theorem behaviorPrefixes_isPrefixClosed {α : Type u} (b : ObsBehavior α) :
    IsPrefixClosed (behaviorPrefixes b) := by
  intro u v huv hv
  cases b with
  | terminates w => exact isPrefix_trans huv hv
  | diverges w   => exact isPrefix_trans huv hv
  | reacts s     => exact hasPrefix_of_isPrefix huv hv

theorem obsFinPrefixes_isPrefixClosed {α : Type u} (S : ObsSystem α) :
    IsPrefixClosed (obsFinPrefixes S) := by
  intro u v huv hv
  rcases hv with ⟨b, hb, hpre⟩
  exact ⟨b, hb, behaviorPrefixes_isPrefixClosed b u v huv hpre⟩

theorem obsFinPrefixes_isNonemptyFin_of_isNonemptyObs {α : Type u} {S : ObsSystem α}
    (hNE : IsNonemptyObs S) :
    IsNonemptyFin (obsFinPrefixes S) := by
  rcases hNE with ⟨b, hb⟩
  exact ⟨[], b, hb, behaviorPrefixes_nil b⟩

theorem obsFinPrefixes_silentDivergeObs {α : Type u} :
    obsFinPrefixes (silentDivergeObs : ObsSystem α) = doNothingFin := by
  funext v
  apply propext
  constructor
  · rintro ⟨b, rfl, w, hw⟩
    cases v with
    | nil => rfl
    | cons a t => simp at hw
  · intro hv
    rw [doNothingFin] at hv
    subst hv
    exact ⟨.diverges [], rfl, isPrefix_nil []⟩

theorem obsFinPrefixes_immediateHaltObs {α : Type u} :
    obsFinPrefixes (immediateHaltObs : ObsSystem α) = doNothingFin := by
  funext v
  apply propext
  constructor
  · rintro ⟨b, rfl, w, hw⟩
    cases v with
    | nil => rfl
    | cons a t => simp at hw
  · intro hv
    rw [doNothingFin] at hv
    subst hv
    exact ⟨.terminates [], rfl, isPrefix_nil []⟩

theorem obsRefines_trans {α : Type u} {S₁ S₂ S₃ : ObsSystem α}
    (h₁₂ : ObsRefines S₁ S₂) (h₂₃ : ObsRefines S₂ S₃) :
    ObsRefines S₁ S₃ :=
  fun b hb => h₂₃ b (h₁₂ b hb)

theorem obsRefines_preserves_obsProp {α : Type u} {Impl Spec : ObsSystem α} {Q : ObsProp α}
    (hRef : ObsRefines Impl Spec) (hSpec : ObsSatisfies Spec Q) :
    ObsSatisfies Impl Q :=
  fun b hb => hSpec b (hRef b hb)

theorem obsRefinesPreserves_linearTime {α : Type u} (Q : ObsProp α) :
    ObsRefinesPreserves (fun S : ObsSystem α => ObsSatisfies S Q) :=
  fun _ _ _ _ hRef hSpec b hb => hSpec b (hRef b hb)

/-- Definitional monotonicity of `obsFinPrefixes`: complete-behavior inclusion
`ObsRefines Impl Spec` transports every finite-prefix witness to `FinRefines`
on `obsFinPrefixes`. -/
theorem obsRefines_implies_finRefines
    {α : Type u} {Impl Spec : ObsSystem α}
    (hRef : ObsRefines Impl Spec) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec) :=
  fun _ ⟨b, hb, hp⟩ => ⟨b, hRef b hb, hp⟩

/-- Definitional corollary of `obsRefines_preserves_obsProp`: if `Spec`
satisfies `NoDivergence` and `Impl` admits `.diverges u` for some finite trace
`u`, then `Impl` fails `ObsRefines Impl Spec`. -/
theorem obsRefines_rejects_divergence_of_noDivergence
    {α : Type u} {Impl Spec : ObsSystem α} {u : List α}
    (hDiv : Impl (.diverges u))
    (hNoDiv : ObsSatisfies Spec NoDivergence) :
    ¬ ObsRefines Impl Spec :=
  fun hRef => hNoDiv (.diverges u) (hRef (.diverges u) hDiv)

theorem embedStreams_refines_iff {α : Type u} (S₁ S₂ : StreamSystem α) :
    ObsRefines (embedStreams S₁) (embedStreams S₂) ↔ StreamRefines S₁ S₂ := by
  constructor
  · intro h s hs
    exact h (.reacts s) hs
  · intro h b hb
    cases b with
    | terminates _ => exact False.elim hb
    | diverges _   => exact False.elim hb
    | reacts s     => exact h s hb

/-! ### Reusable concrete observable-behavior systems on `Bool` -/

/-- Specification on `Bool`: must emit `[true]` and terminate cleanly. -/
def emitTrueObs : ObsSystem Bool :=
  fun b => b = .terminates [true]

/-- Specification on `Bool`: must emit `[true, true]` and terminate cleanly. -/
def emitTwoTruesObs : ObsSystem Bool :=
  fun b => b = .terminates [true, true]

/-- Implementation on `Bool` that emits `[true]` and then silently diverges. -/
def divergeAfterTrueObs : ObsSystem Bool :=
  fun b => b = .diverges [true]

/-! ### Positive and negative examples for observable-behavior definitions -/

/-- Positive/negative distinction for `ObsBehavior`: the three behavior kinds
are pairwise distinct even when they share the empty prefix. -/
theorem obsBehavior_constructors_distinct :
    (ObsBehavior.terminates ([] : List Bool) ≠ .diverges []) ∧
      (ObsBehavior.diverges ([] : List Bool) ≠ .reacts constFalse) ∧
      (ObsBehavior.terminates ([] : List Bool) ≠ .reacts constFalse) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- Positive example for `ObsSatisfies` and `EmitsEvent`: `emitTrueObs` satisfies `EmitsEvent`. -/
theorem obsSatisfies_pos_emitTrue_emitsEvent : ObsSatisfies emitTrueObs EmitsEvent := by
  intro b hb
  subst hb
  intro h
  cases h

/-- Negative example for `ObsSatisfies` and `EmitsEvent`: `silentDivergeObs` fails `EmitsEvent`. -/
theorem obsSatisfies_neg_silentDiverge_emitsEvent :
    ¬ ObsSatisfies (silentDivergeObs : ObsSystem Bool) EmitsEvent := by
  intro h
  exact h (.diverges []) rfl rfl

/-- Positive example for `EmitsEvent`: `.terminates [true]` and `.reacts constFalse` satisfy `EmitsEvent`. -/
theorem emitsEvent_pos :
    EmitsEvent (.terminates [true]) ∧ EmitsEvent (.reacts constFalse) := by
  constructor
  · intro h
    cases h
  · trivial

/-- Negative example for `EmitsEvent`: `.diverges []` and `.terminates []` fail `EmitsEvent`. -/
theorem emitsEvent_neg :
    ¬ EmitsEvent (.diverges ([] : List Bool)) ∧ ¬ EmitsEvent (.terminates ([] : List Bool)) :=
  ⟨fun h => h rfl, fun h => h rfl⟩

/-- Positive example for `ObsCanEmit`: `emitTrueObs` can emit an event. -/
theorem obsCanEmit_pos_emitTrue : ObsCanEmit emitTrueObs :=
  ⟨.terminates [true], rfl, fun h => by cases h⟩

/-- Negative example for `ObsCanEmit`: `silentDivergeObs` cannot emit an event. -/
theorem obsCanEmit_neg_silentDiverge : ¬ ObsCanEmit (silentDivergeObs : ObsSystem Bool) := by
  rintro ⟨b, rfl, hE⟩
  exact hE rfl

/-- Positive example for `ObsRefinesPreserves`: `ObsSatisfies · EmitsEvent` is
preserved across nonempty complete-behavior refinements. -/
theorem obsRefinesPreserves_pos_emitsEvent :
    ObsRefinesPreserves (fun S : ObsSystem Bool => ObsSatisfies S EmitsEvent) :=
  obsRefinesPreserves_linearTime EmitsEvent

/-- Witness that `ObsRefines` between nonempty systems does NOT preserve the
existential possibility predicate `ObsCanEmit`: `silentDivergeObs` refines the
nondeterministic system `{.diverges [], .terminates [true]}`, which satisfies
`ObsCanEmit`, while `silentDivergeObs` fails `ObsCanEmit`. -/
theorem obsRefines_fails_possibility_canEmit :
    let Spec : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [true]
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs Spec ∧
      ObsRefines silentDivergeObs Spec ∧
      ObsCanEmit Spec ∧
      ¬ ObsCanEmit (silentDivergeObs : ObsSystem Bool) := by
  intro Spec
  refine ⟨⟨.diverges [], rfl⟩, ⟨.diverges [], Or.inl rfl⟩, fun _ hb => Or.inl hb,
    ⟨.terminates [true], Or.inr rfl, fun h => by cases h⟩, obsCanEmit_neg_silentDiverge⟩

/-- Negative example for `ObsRefinesPreserves`: `ObsCanEmit` is not preserved
across nonempty complete-behavior refinements. -/
theorem obsRefinesPreserves_neg_canEmit :
    ¬ ObsRefinesPreserves (fun S : ObsSystem Bool => ObsCanEmit S) := by
  intro hPres
  rcases obsRefines_fails_possibility_canEmit with ⟨hNE₁, hNE₂, hRef, hSpec, hNotImpl⟩
  exact hNotImpl (hPres silentDivergeObs _ hNE₁ hNE₂ hRef hSpec)

/-- Positive example for `NoDivergence`: terminating and reactive behaviors satisfy `NoDivergence`. -/
theorem noDivergence_pos :
    NoDivergence (.terminates [true]) ∧ NoDivergence (.reacts constFalse) :=
  ⟨trivial, trivial⟩

/-- Negative example for `NoDivergence`: `.diverges []` fails `NoDivergence`. -/
theorem noDivergence_neg : ¬ NoDivergence (.diverges ([] : List Bool)) :=
  id

/-- Positive example for `ObsRefines`: `emitTrueObs` refines itself. -/
theorem obsRefines_pos_refl : ObsRefines emitTrueObs emitTrueObs :=
  fun _ h => h

/-- Negative example for `ObsRefines`: `silentDivergeObs` does not refine `emitTrueObs`. -/
theorem obsRefines_neg_silentDiverge_emitTrue : ¬ ObsRefines silentDivergeObs emitTrueObs := by
  intro hRef
  have h : ObsBehavior.diverges ([] : List Bool) = .terminates [true] := hRef (.diverges []) rfl
  cases h

/-- Positive example for `IsNonemptyObs`: `silentDivergeObs` is nonempty. -/
theorem isNonemptyObs_pos_silentDiverge : IsNonemptyObs (silentDivergeObs : ObsSystem Bool) :=
  ⟨.diverges [], rfl⟩

/-- Negative example for `IsNonemptyObs`: the empty behavior system is not nonempty. -/
theorem isNonemptyObs_neg_empty : ¬ IsNonemptyObs (fun _ : ObsBehavior Bool => False) := by
  rintro ⟨_, h⟩
  exact h

/-- Positive example for `behaviorPrefixes`: `[true]` is a prefix of `.terminates [true]`. -/
theorem behaviorPrefixes_pos_terminates :
    behaviorPrefixes (ObsBehavior.terminates [true]) [true] :=
  isPrefix_refl [true]

/-- Negative example for `behaviorPrefixes`: `[true]` is not a prefix of `.diverges []`. -/
theorem behaviorPrefixes_neg_diverges :
    ¬ behaviorPrefixes (ObsBehavior.diverges ([] : List Bool)) [true] := by
  rintro ⟨w, hw⟩
  simp at hw

/-- Positive example for `obsFinPrefixes`: `[true]` lies in `obsFinPrefixes emitTrueObs`. -/
theorem obsFinPrefixes_pos_emitTrue : obsFinPrefixes emitTrueObs [true] :=
  ⟨.terminates [true], rfl, isPrefix_refl [true]⟩

/-- Negative example for `obsFinPrefixes`: `[true]` does not lie in `obsFinPrefixes silentDivergeObs`. -/
theorem obsFinPrefixes_neg_silentDiverge : ¬ obsFinPrefixes silentDivergeObs [true] := by
  rintro ⟨b, rfl, w, hw⟩
  simp at hw

/-- Positive example for `silentDivergeObs`: contains `.diverges []`. -/
theorem silentDivergeObs_pos : (silentDivergeObs : ObsSystem Bool) (.diverges []) :=
  rfl

/-- Negative example for `silentDivergeObs`: rejects `.terminates []`. -/
theorem silentDivergeObs_neg : ¬ (silentDivergeObs : ObsSystem Bool) (.terminates []) := by
  intro h
  cases h

/-- Positive example for `immediateHaltObs`: contains `.terminates []`. -/
theorem immediateHaltObs_pos : (immediateHaltObs : ObsSystem Bool) (.terminates []) :=
  rfl

/-- Negative example for `immediateHaltObs`: rejects `.diverges []`. -/
theorem immediateHaltObs_neg : ¬ (immediateHaltObs : ObsSystem Bool) (.diverges []) := by
  intro h
  cases h

/-- Positive example for `embedStreams`: `embedStreams AlwaysFalse` contains `.reacts constFalse`. -/
theorem embedStreams_pos : embedStreams AlwaysFalse (.reacts constFalse) :=
  traceProp_pos_alwaysFalse

/-- Negative example for `embedStreams`: `embedStreams AlwaysFalse` rejects `.diverges []`. -/
theorem embedStreams_neg : ¬ embedStreams AlwaysFalse (.diverges []) :=
  id

/-! ### Positive controls and concrete separation witnesses -/

/-- Canonical positive control for `finRefines_cannot_preserve_property_rejecting_doNothing`:
when termination and divergence are observed explicitly (`ObsSystem Bool`), the
universal linear-time predicate `ObsSatisfies · EmitsEvent` is preserved by
`ObsRefines` across all nonempty systems (`ObsRefinesPreserves`), holds for the
nonempty specification `emitTrueObs`, and rejects both do-nothing systems
`silentDivergeObs` and `immediateHaltObs`. -/
theorem obsRefinesPreserves_emitsEvent_rejects_doNothing :
    ObsRefinesPreserves (fun S : ObsSystem Bool => ObsSatisfies S EmitsEvent) ∧
      IsNonemptyObs emitTrueObs ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ ObsSatisfies (silentDivergeObs : ObsSystem Bool) EmitsEvent ∧
      ¬ ObsSatisfies (immediateHaltObs : ObsSystem Bool) EmitsEvent := by
  refine ⟨obsRefinesPreserves_pos_emitsEvent, ⟨.terminates [true], rfl⟩,
    obsSatisfies_pos_emitTrue_emitsEvent, obsSatisfies_neg_silentDiverge_emitsEvent, ?_⟩
  intro h
  exact h (.terminates []) rfl rfl

/-- Concrete separation (silent divergence at `[]`): `silentDivergeObs` passes
finite-trace refinement against `emitTrueObs`, yet fails `ObsRefines`. -/
theorem silentDivergeObs_fails_obsRefines_emitTrue :
    FinRefines (obsFinPrefixes silentDivergeObs) (obsFinPrefixes emitTrueObs) ∧
      ¬ ObsRefines silentDivergeObs emitTrueObs := by
  refine ⟨?_, obsRefines_neg_silentDiverge_emitTrue⟩
  rw [obsFinPrefixes_silentDivergeObs]
  exact doNothingFin_refines_every_prefixClosed_nonempty
    (obsFinPrefixes_isPrefixClosed emitTrueObs)
    (obsFinPrefixes_isNonemptyFin_of_isNonemptyObs ⟨.terminates [true], rfl⟩)

/-- Concrete separation (immediate empty termination): `immediateHaltObs` also
passes finite-trace refinement against `emitTrueObs`, yet fails `ObsRefines`. -/
theorem immediateHaltObs_fails_obsRefines_emitTrue :
    FinRefines (obsFinPrefixes immediateHaltObs) (obsFinPrefixes emitTrueObs) ∧
      ¬ ObsRefines immediateHaltObs emitTrueObs := by
  refine ⟨?_, ?_⟩
  · rw [obsFinPrefixes_immediateHaltObs]
    exact doNothingFin_refines_every_prefixClosed_nonempty
      (obsFinPrefixes_isPrefixClosed emitTrueObs)
      (obsFinPrefixes_isNonemptyFin_of_isNonemptyObs ⟨.terminates [true], rfl⟩)
  · intro hRef
    have h : ObsBehavior.terminates ([] : List Bool) = .terminates [true] :=
      hRef (.terminates []) rfl
    cases h

/-- Positive control for `finPrefixes_refines_fails_every_nontrivial_liveness`:
under finite-prefix refinement `{constFalse}` refines `EventuallyTrue`, whereas
under full `StreamRefines` (equivalently `ObsRefines` on `embedStreams`) it fails. -/
theorem streamRefines_rejects_constFalse_for_eventuallyTrue :
    FinRefines (finPrefixes (fun s => s = constFalse)) (finPrefixes EventuallyTrue) ∧
      ¬ StreamRefines (fun s => s = constFalse) EventuallyTrue ∧
      ¬ ObsRefines (embedStreams (fun s => s = constFalse)) (embedStreams EventuallyTrue) := by
  refine ⟨fun u _ => finPrefixes_eq_univ_of_isLiveness eventuallyTrue_isLiveness u, ?_, ?_⟩
  · intro hRef
    rcases hRef constFalse rfl with ⟨i, hi⟩
    simp [constFalse] at hi
  · intro hRef
    rcases hRef (.reacts constFalse) rfl with ⟨i, hi⟩
    simp [constFalse] at hi

/-- Sharp concrete separation exercising the `.diverges` vs. `.terminates` tag
on the identical complete trace `[true]`: `divergeAfterTrueObs` (`{.diverges [true]}`)
and `emitTrueObs` (`{.terminates [true]}`) induce the exact same finite-prefix
system (`{[], [true]}`), yet neither refines the other under `ObsRefines`. -/
theorem divergeAfterTrue_separates_sameTrace_terminates :
    obsFinPrefixes divergeAfterTrueObs = obsFinPrefixes emitTrueObs ∧
      ¬ ObsRefines divergeAfterTrueObs emitTrueObs ∧
      ¬ ObsRefines emitTrueObs divergeAfterTrueObs := by
  refine ⟨?_, ?_, ?_⟩
  · funext v
    apply propext
    constructor
    · rintro ⟨b, rfl, hpre⟩
      exact ⟨.terminates [true], rfl, hpre⟩
    · rintro ⟨b, rfl, hpre⟩
      exact ⟨.diverges [true], rfl, hpre⟩
  · intro hRef
    have h : ObsBehavior.diverges [true] = .terminates [true] :=
      hRef (.diverges [true]) rfl
    cases h
  · intro hRef
    have h : ObsBehavior.terminates [true] = .diverges [true] :=
      hRef (.terminates [true]) rfl
    cases h

/-- Concrete separation for silent divergence after a strict nonempty prefix:
`divergeAfterTrueObs` (`{.diverges [true]}`) passes finite-trace refinement
against `emitTwoTruesObs` (`{.terminates [true, true]}`), which satisfies
`NoDivergence`, yet fails `ObsRefines`. -/
theorem divergeAfterPrefix_fails_obsRefines_noDivergence :
    ObsSatisfies emitTwoTruesObs NoDivergence ∧
      FinRefines (obsFinPrefixes divergeAfterTrueObs) (obsFinPrefixes emitTwoTruesObs) ∧
      ¬ ObsRefines divergeAfterTrueObs emitTwoTruesObs := by
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    subst hb
    trivial
  · intro v hv
    rcases hv with ⟨b, rfl, hpre⟩
    refine ⟨.terminates [true, true], rfl, isPrefix_trans hpre ⟨[true], rfl⟩⟩
  · intro hRef
    have h : ObsBehavior.diverges [true] = .terminates [true, true] :=
      hRef (.diverges [true]) rfl
    cases h

/-! ### Factored helper lemmas for `obsRefines_separates_doNothing_from_finRefines` -/

/-- First half of `obsRefines_separates_doNothing_from_finRefines`: any
implementation whose finite prefixes lie in `doNothingFin` finite-trace refines
every nonempty complete-behavior specification (needing only `hSpecNE` and
`hDoNothing`). -/
theorem finRefines_obsFinPrefixes_of_doNothing
    {α : Type u} {Impl Spec : ObsSystem α}
    (hSpecNE : IsNonemptyObs Spec)
    (hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec) := by
  intro v hv
  have hv0 : v = [] := hDoNothing v hv
  subst hv0
  rcases hSpecNE with ⟨b, hb⟩
  exact ⟨b, hb, behaviorPrefixes_nil b⟩

/-- Strengthened second half of `obsRefines_separates_doNothing_from_finRefines`:
any implementation admitting at least one silent behavior (`¬ EmitsEvent b`)
fails `ObsRefines` against any specification satisfying `EmitsEvent` (even if
`Impl` also admits event-emitting behaviors and therefore fails `hDoNothing`). -/
theorem not_obsRefines_of_silent_behavior
    {α : Type u} {Impl Spec : ObsSystem α}
    (hSilent : ∃ b : ObsBehavior α, Impl b ∧ ¬ EmitsEvent b)
    (hProgress : ObsSatisfies Spec EmitsEvent) :
    ¬ ObsRefines Impl Spec := by
  intro hRef
  rcases hSilent with ⟨b, hb, hNotE⟩
  exact hNotE (hProgress b (hRef b hb))

/-- Witness that `∃ b, Impl b ∧ ¬ EmitsEvent b` is strictly weaker than
`IsNonemptyObs Impl ∧ FinRefines (obsFinPrefixes Impl) doNothingFin`: the mixed
system `{.diverges [], .terminates [false]}` fails `hDoNothing` yet is still
rejected by `not_obsRefines_of_silent_behavior` against `emitTrueObs`. -/
theorem mixedSilentAndEmit_not_obsRefines_without_doNothing :
    let Impl : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [false]
    (∃ b : ObsBehavior Bool, Impl b ∧ ¬ EmitsEvent b) ∧
      ¬ FinRefines (obsFinPrefixes Impl) doNothingFin ∧
      ¬ ObsRefines Impl emitTrueObs := by
  intro Impl
  have hSilent : ∃ b : ObsBehavior Bool, Impl b ∧ ¬ EmitsEvent b :=
    ⟨.diverges [], Or.inl rfl, fun h => h rfl⟩
  refine ⟨hSilent, ?_,
    not_obsRefines_of_silent_behavior hSilent obsSatisfies_pos_emitTrue_emitsEvent⟩
  intro hDo
  have h := hDo [false] ⟨.terminates [false], Or.inr rfl, isPrefix_refl [false]⟩
  cases h

/-! ### Complete-behavior separation theorems -/

/-- Every nonempty complete-behavior implementation whose finite prefixes lie in
`{[]}` (such as `silentDivergeObs` or `immediateHaltObs`) passes finite-trace
refinement against every nonempty specification satisfying `EmitsEvent`, yet
fails complete-behavior refinement `ObsRefines`. -/
theorem obsRefines_separates_doNothing_from_finRefines
    {α : Type u} {Impl Spec : ObsSystem α}
    (hImplNE : IsNonemptyObs Impl)
    (hSpecNE : IsNonemptyObs Spec)
    (hDoNothing : FinRefines (obsFinPrefixes Impl) doNothingFin)
    (hProgress : ObsSatisfies Spec EmitsEvent) :
    FinRefines (obsFinPrefixes Impl) (obsFinPrefixes Spec) ∧ ¬ ObsRefines Impl Spec := by
  refine ⟨finRefines_obsFinPrefixes_of_doNothing hSpecNE hDoNothing, ?_⟩
  rcases hImplNE with ⟨b, hb⟩
  refine not_obsRefines_of_silent_behavior ⟨b, hb, ?_⟩ hProgress
  cases b with
  | terminates w =>
    intro hne
    exact hne (hDoNothing w ⟨.terminates w, hb, isPrefix_refl w⟩)
  | diverges w =>
    intro hne
    exact hne (hDoNothing w ⟨.diverges w, hb, isPrefix_refl w⟩)
  | reacts s =>
    intro _
    have h1 : HasPrefix s [s 0] := by
      intro i hi
      match i, hi with
      | 0, _ => rfl
    have h := hDoNothing [s 0] ⟨.reacts s, hb, h1⟩
    cases h

/-- Post-prefix and same-trace divergence separation: whenever a finite trace `u`
is an observable prefix of `Spec` (`obsFinPrefixes Spec u`) and `Spec` forbids
silent divergence at `u` (`¬ Spec (.diverges u)`), the diverging implementation
`{.diverges u}` passes finite-trace refinement against `Spec` on `obsFinPrefixes`
while failing `ObsRefines`. In particular, when `Spec = {.terminates u}`, both
systems have the exact same complete trace `u` and only the `.diverges` vs.
`.terminates` tag separates them. -/
theorem obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges
    {α : Type u} {Spec : ObsSystem α} {u : List α}
    (hPrefix : obsFinPrefixes Spec u)
    (hNotDiv : ¬ Spec (.diverges u)) :
    FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
      ¬ ObsRefines (fun b => b = .diverges u) Spec := by
  refine ⟨?_, fun hRef => hNotDiv (hRef _ rfl)⟩
  rintro v ⟨b, rfl, hv⟩
  exact obsFinPrefixes_isPrefixClosed Spec v u hv hPrefix

/-! ### Non-vacuity witnesses and tightness counterexamples -/

/-- Non-vacuity witness for `obsRefines_separates_doNothing_from_finRefines`:
`silentDivergeObs` and `emitTrueObs` on `Bool` satisfy all four hypotheses. -/
theorem obsRefines_separates_doNothing_nonvacuity :
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs emitTrueObs ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ObsSatisfies emitTrueObs EmitsEvent := by
  refine ⟨isNonemptyObs_pos_silentDiverge, ⟨.terminates [true], rfl⟩, ?_,
    obsSatisfies_pos_emitTrue_emitsEvent⟩
  rw [obsFinPrefixes_silentDivergeObs]
  intro u hu
  exact hu

/-- Tightness counterexample for `hImplNE : IsNonemptyObs Impl` in
`obsRefines_separates_doNothing_from_finRefines`: the empty behavior system
`Impl = ∅` satisfies the other three hypotheses against `emitTrueObs`, yet
vacuously refines `emitTrueObs` under `ObsRefines` (falsifying the conclusion). -/
theorem obsEmpty_tight_implNE :
    let Impl : ObsSystem Bool := fun _ => False
    IsNonemptyObs emitTrueObs ∧
      FinRefines (obsFinPrefixes Impl) doNothingFin ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes Impl) (obsFinPrefixes emitTrueObs) ∧
         ¬ ObsRefines Impl emitTrueObs) := by
  refine ⟨⟨.terminates [true], rfl⟩, ?_, obsSatisfies_pos_emitTrue_emitsEvent, ?_⟩
  · rintro v ⟨_, h, _⟩
    exact False.elim h
  · rintro ⟨_, hNotRef⟩
    exact hNotRef (fun _ h => False.elim h)

/-- Tightness counterexample for `hSpecNE : IsNonemptyObs Spec` in
`obsRefines_separates_doNothing_from_finRefines`: for `Impl = silentDivergeObs`
and `Spec = ∅`, the other three hypotheses hold yet finite-trace refinement
fails (falsifying the conclusion). -/
theorem obsSpecEmpty_tight_specNE :
    let Spec : ObsSystem Bool := fun _ => False
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ObsSatisfies Spec EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (silentDivergeObs : ObsSystem Bool) Spec) := by
  refine ⟨isNonemptyObs_pos_silentDiverge, ?_, fun _ h => False.elim h, ?_⟩
  · rw [obsFinPrefixes_silentDivergeObs]
    intro u hu
    exact hu
  · rintro ⟨hRef, _⟩
    have hNil : obsFinPrefixes (silentDivergeObs : ObsSystem Bool) [] :=
      ⟨.diverges [], rfl, isPrefix_nil []⟩
    rcases hRef [] hNil with ⟨_, hFalse, _⟩
    exact hFalse

/-- Tightness counterexample for `hDoNothing` in
`obsRefines_separates_doNothing_from_finRefines`: for `Impl = emitTrueObs` and
`Spec = emitTrueObs`, the other three hypotheses hold yet `ObsRefines` holds
(falsifying the conclusion). -/
theorem obsEmitTrue_tight_doNothing :
    IsNonemptyObs emitTrueObs ∧
      IsNonemptyObs emitTrueObs ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes emitTrueObs) (obsFinPrefixes emitTrueObs) ∧
         ¬ ObsRefines emitTrueObs emitTrueObs) :=
  ⟨⟨.terminates [true], rfl⟩, ⟨.terminates [true], rfl⟩,
    obsSatisfies_pos_emitTrue_emitsEvent, fun h => h.2 obsRefines_pos_refl⟩

/-- Witness showing `hDoNothing` cannot be weakened to `∃ b, Impl b ∧ ¬ EmitsEvent b`
for the combined conjunction of `obsRefines_separates_doNothing_from_finRefines`
(specifically because the `FinRefines` conjunct fails):
`Impl = {.diverges [], .terminates [false]}` has a silent behavior, yet fails
`FinRefines` against `emitTrueObs` because `[false]` is not a prefix of `emitTrueObs`. -/
theorem obsMixed_tight_weakDoNothing :
    let Impl : ObsSystem Bool := fun b => b = .diverges [] ∨ b = .terminates [false]
    IsNonemptyObs Impl ∧
      IsNonemptyObs emitTrueObs ∧
      (∃ b : ObsBehavior Bool, Impl b ∧ ¬ EmitsEvent b) ∧
      ObsSatisfies emitTrueObs EmitsEvent ∧
      ¬ (FinRefines (obsFinPrefixes Impl) (obsFinPrefixes emitTrueObs) ∧
         ¬ ObsRefines Impl emitTrueObs) := by
  refine ⟨⟨.diverges [], Or.inl rfl⟩, ⟨.terminates [true], rfl⟩,
    ⟨.diverges [], Or.inl rfl, fun h => h rfl⟩, obsSatisfies_pos_emitTrue_emitsEvent, ?_⟩
  rintro ⟨hRef, _⟩
  have hFalse : obsFinPrefixes
      (fun b : ObsBehavior Bool => b = .diverges [] ∨ b = .terminates [false]) [false] :=
    ⟨.terminates [false], Or.inr rfl, isPrefix_refl [false]⟩
  rcases hRef [false] hFalse with ⟨b, rfl, w, hw⟩
  simp at hw

/-- Tightness counterexample for `hProgress : ObsSatisfies Spec EmitsEvent` in
`obsRefines_separates_doNothing_from_finRefines`: for `Impl = Spec = silentDivergeObs`,
the other three hypotheses hold yet `ObsRefines` holds (falsifying the conclusion). -/
theorem obsAllowDiverge_tight_progress :
    IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      IsNonemptyObs (silentDivergeObs : ObsSystem Bool) ∧
      FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) doNothingFin ∧
      ¬ (FinRefines (obsFinPrefixes (silentDivergeObs : ObsSystem Bool))
          (obsFinPrefixes (silentDivergeObs : ObsSystem Bool)) ∧
         ¬ ObsRefines (silentDivergeObs : ObsSystem Bool) silentDivergeObs) := by
  refine ⟨isNonemptyObs_pos_silentDiverge, isNonemptyObs_pos_silentDiverge, ?_,
    fun h => h.2 (fun _ hb => hb)⟩
  rw [obsFinPrefixes_silentDivergeObs]
  intro u hu
  exact hu

/-- Non-vacuity witness for
`obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges`: on `Bool`
with `Spec = emitTrueObs` (`{.terminates [true]}`) and `u = [true]`, `[true]`
lies in `obsFinPrefixes emitTrueObs` and `emitTrueObs` rejects `.diverges [true]`. -/
theorem obsSeparatesDiverges_sameTrace_nonvacuity :
    obsFinPrefixes emitTrueObs [true] ∧ ¬ emitTrueObs (.diverges [true]) := by
  refine ⟨obsFinPrefixes_pos_emitTrue, ?_⟩
  intro h
  cases h

/-- Tightness counterexample for `hPrefix : obsFinPrefixes Spec u` in
`obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges`: for
`Spec = immediateHaltObs` (`{.terminates []}`) and `u = [true]`,
`¬ Spec (.diverges [true])` holds yet `FinRefines` on `obsFinPrefixes` fails
(falsifying the conjunction). -/
theorem obsSeparatesDiverges_tight_prefix :
    let Spec : ObsSystem Bool := immediateHaltObs
    let u : List Bool := [true]
    ¬ Spec (.diverges u) ∧
      ¬ (FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (fun b => b = .diverges u) Spec) := by
  intro Spec u
  refine ⟨(fun h => by cases h), ?_⟩
  rintro ⟨hRef, _⟩
  have hTrue : obsFinPrefixes (fun b : ObsBehavior Bool => b = .diverges [true]) [true] :=
    ⟨.diverges [true], rfl, isPrefix_refl [true]⟩
  rcases hRef [true] hTrue with ⟨b, rfl, w, hw⟩
  simp at hw

/-- Tightness counterexample for `hNotDiv : ¬ Spec (.diverges u)` in
`obsRefines_separates_diverges_of_obsFinPrefixes_of_not_diverges`: for
`Spec = divergeAfterTrueObs` (`{.diverges [true]}`) and `u = [true]`,
`obsFinPrefixes Spec [true]` holds yet `ObsRefines` holds (falsifying the
conjunction). -/
theorem obsSeparatesDiverges_tight_notDiv :
    let Spec : ObsSystem Bool := divergeAfterTrueObs
    let u : List Bool := [true]
    obsFinPrefixes Spec u ∧
      ¬ (FinRefines (obsFinPrefixes (fun b => b = .diverges u)) (obsFinPrefixes Spec) ∧
         ¬ ObsRefines (fun b => b = .diverges u) Spec) := by
  intro Spec u
  refine ⟨⟨.diverges [true], rfl, isPrefix_refl [true]⟩, ?_⟩
  rintro ⟨_, hNotRef⟩
  exact hNotRef (fun _ hb => hb)

/-- Tightness counterexample for `hRef` in `obsRefines_implies_finRefines`:
`obsFinPrefixes {.terminates [false]}` does not `FinRefines` `obsFinPrefixes emitTrueObs`. -/
theorem obsRefines_implies_finRefines_tight_ref :
    ¬ FinRefines (obsFinPrefixes (fun b : ObsBehavior Bool => b = .terminates [false]))
        (obsFinPrefixes emitTrueObs) := by
  intro hRef
  have hFalse : obsFinPrefixes (fun b : ObsBehavior Bool => b = .terminates [false]) [false] :=
    ⟨.terminates [false], rfl, isPrefix_refl [false]⟩
  rcases hRef [false] hFalse with ⟨b, rfl, w, hw⟩
  simp at hw

end Toy.SafetyLiveness
