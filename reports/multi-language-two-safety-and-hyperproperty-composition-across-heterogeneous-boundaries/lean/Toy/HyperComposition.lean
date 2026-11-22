/-!
# Multi-Language 2-Safety and Hyperproperty Composition Toy Model

Mathlib-free Lean `v4.34.1` toy mechanization exploring:
1. Vertical compositionality of `LeakageBisim` across heterogeneous observation alphabets
   and its incompatibility with uniform determinizing lowerings (which `UniformRefinement` admits).
2. Horizontal 2-safety breakdown when a non-interfering managed-language module crosses a
   GC-allocation / timing-observing FFI membrane (`membrane_breaks_two_safety`), even while
   1-safety and trace-relating compiler correctness (`CC_R`) hold.
3. Exact Galois connection (`tau` ⊣ `sigma`) between source and target trace properties
   (Abate et al., ESOP 2020 / TOPLAS 2021), its Trinitarian View (`TP_tau ↔ CC_R ↔ TP_sigma`),
   sufficient low-equivalence preservation/reflection conditions for 2-safety composition across
   heterogeneous language chains, and the Galois insertion condition for general hyperproperties.

Model–system relation: none proved. All definitions and theorems characterize this finite
abstract semantic model rather than a concrete compiler or runtime implementation.
-/

namespace Toy.HyperComposition

universe u v w

/-! ## Section 1: Leakage Semantics, `LeakageBisim`, and `UniformRefinement` -/

/-- A relational semantics mapping public input `L` and secret input `H` to a set of
    observable leakage traces in `O`. -/
abbrev Sem (L : Type u) (H : Type v) (O : Type w) : Type (max u v w) :=
  L → H → O → Prop

/-- Deterministic 2-safety (observational determinism): equal public inputs force identical
    observable leakage regardless of secret inputs. -/
def TwoSafety {L : Type u} {H : Type v} {O : Type w} (S : Sem L H O) : Prop :=
  ∀ l h₁ h₂ o₁ o₂, S l h₁ o₁ → S l h₂ o₂ → o₁ = o₂

/-- Set-valued non-interference (possibilistic observational independence): the full set of
    possible leakage observations is invariant under changes to the secret input. -/
def SetNI {L : Type u} {H : Type v} {O : Type w} (S : Sem L H O) : Prop :=
  ∀ l h₁ h₂ o, S l h₁ o → S l h₂ o

/-- Functional determinism of a leakage semantics on fixed `(l, h)`. -/
def Deterministic {L : Type u} {H : Type v} {O : Type w} (S : Sem L H O) : Prop :=
  ∀ l h o₁ o₂, S l h o₁ → S l h o₂ → o₁ = o₂

/-- Exact leakage bisimulation across a (possibly alphabet-changing) public leakage
    transformer `φ : L → O₁ → O₂`: target observations are exactly the `φ`-image of source
    observations at every `(l, h)`. -/
def LeakageBisim {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂) : Prop :=
  ∀ l h o₂, T l h o₂ ↔ ∃ o₁, S l h o₁ ∧ o₂ = φ l o₁

/-- Uniform refinement across a public leakage transformer `φ : L → O₁ → O₂`:
    (1) every target observation is the `φ`-image of a permitted source observation, and
    (2) the resolution of source nondeterminism is uniform across secret inputs
        (if `T` keeps `o₂` under `h₁` and `S` also admits `o₂` via `φ` under `h₂`,
        then `T` keeps `o₂` under `h₂`). -/
def UniformRefinement {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂) : Prop :=
  (∀ l h o₂, T l h o₂ → ∃ o₁, S l h o₁ ∧ o₂ = φ l o₁) ∧
  (∀ l h₁ h₂ o₂, T l h₁ o₂ → (∃ o₁, S l h₂ o₁ ∧ o₂ = φ l o₁) → T l h₂ o₂)

/-- Vertical composition of `LeakageBisim` across heterogeneous alphabets `O₁ → O₂ → O₃`. -/
theorem leakageBisim_compose {L : Type u} {H : Type v} {O₁ O₂ O₃ : Type w}
    (φ₁ : L → O₁ → O₂) (φ₂ : L → O₂ → O₃)
    (S₁ : Sem L H O₁) (S₂ : Sem L H O₂) (S₃ : Sem L H O₃)
    (h₁₂ : LeakageBisim φ₁ S₁ S₂)
    (h₂₃ : LeakageBisim φ₂ S₂ S₃) :
    LeakageBisim (fun l o₁ => φ₂ l (φ₁ l o₁)) S₁ S₃ := by
  intro l h o₃
  constructor
  · intro hs₃
    rcases (h₂₃ l h o₃).mp hs₃ with ⟨o₂, hs₂, rfl⟩
    rcases (h₁₂ l h o₂).mp hs₂ with ⟨o₁, hs₁, rfl⟩
    exact ⟨o₁, hs₁, rfl⟩
  · rintro ⟨o₁, hs₁, rfl⟩
    apply (h₂₃ l h (φ₂ l (φ₁ l o₁))).mpr
    refine ⟨φ₁ l o₁, ?_, rfl⟩
    exact (h₁₂ l h (φ₁ l o₁)).mpr ⟨o₁, hs₁, rfl⟩

/-- Every `LeakageBisim` is a fortiori a `UniformRefinement`. -/
theorem leakageBisim_implies_uniformRefinement {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂)
    (hbisim : LeakageBisim φ S T) :
    UniformRefinement φ S T := by
  constructor
  · intro l h o₂ ht
    exact (hbisim l h o₂).mp ht
  · intro l _ h₂ o₂ _ hsrc
    exact (hbisim l h₂ o₂).mpr hsrc

/-- `UniformRefinement` preserves closed-module `SetNI` across heterogeneous alphabets. -/
theorem uniformRefinement_preserves_setNI {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂)
    (href : UniformRefinement φ S T)
    (hni : SetNI S) :
    SetNI T := by
  intro l h₁ h₂ o₂ ht₁
  rcases href.1 l h₁ o₂ ht₁ with ⟨o₁, hs₁, rfl⟩
  have hs₂ : S l h₂ o₁ := hni l h₁ h₂ o₁ hs₁
  exact href.2 l h₁ h₂ (φ l o₁) ht₁ ⟨o₁, hs₂, rfl⟩

/-- `UniformRefinement` preserves closed-module `TwoSafety` across heterogeneous alphabets. -/
theorem uniformRefinement_preserves_twoSafety {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂)
    (href : UniformRefinement φ S T)
    (h2s : TwoSafety S) :
    TwoSafety T := by
  intro l h₁ h₂ o₁' o₂' ht₁ ht₂
  rcases href.1 l h₁ o₁' ht₁ with ⟨o₁, hs₁, rfl⟩
  rcases href.1 l h₂ o₂' ht₂ with ⟨o₂, hs₂, rfl⟩
  have heq : o₁ = o₂ := h2s l h₁ h₂ o₁ o₂ hs₁ hs₂
  rw [heq]

/-- General incompatibility of `LeakageBisim` with any determinizing lowering: if a source
    admits two observations `o₁, o₂` at `(l, h)` whose `φ`-images are distinct, then no
    deterministic target `T` can stand in `LeakageBisim φ S T`. -/
theorem leakageBisim_incompatible_with_determinizer {L : Type u} {H : Type v} {O₁ O₂ : Type w}
    (φ : L → O₁ → O₂) (S : Sem L H O₁) (T : Sem L H O₂)
    (hdet : Deterministic T)
    (l : L) (h : H) (o₁ o₂ : O₁)
    (hs₁ : S l h o₁) (hs₂ : S l h o₂)
    (hne : φ l o₁ ≠ φ l o₂) :
    ¬ LeakageBisim φ S T := by
  intro hbisim
  have ht₁ : T l h (φ l o₁) := (hbisim l h (φ l o₁)).mpr ⟨o₁, hs₁, rfl⟩
  have ht₂ : T l h (φ l o₂) := (hbisim l h (φ l o₂)).mpr ⟨o₂, hs₂, rfl⟩
  exact hne (hdet l h (φ l o₁) (φ l o₂) ht₁ ht₂)

/-- Concrete witness source: nondeterministic secret-independent alignment choice (`false` or `true`). -/
def nondetAlignSource : Sem Unit Bool Bool := fun _ _ _ => True

/-- Concrete witness honest determinizer: fixes alignment to `false` uniformly for all secrets. -/
def uniformDetTarget : Sem Unit Bool Bool := fun _ _ o => o = false

/-- Concrete witness dishonest determinizer: picks alignment equal to secret `h`. -/
def leakyDetTarget : Sem Unit Bool Bool := fun _ h o => o = h

theorem nondetAlignSource_setNI : SetNI nondetAlignSource := by
  intro _ _ _ _ _; trivial

theorem uniformDetTarget_twoSafety : TwoSafety uniformDetTarget := by
  intro _ _ _ _ _ h₁ h₂
  exact h₁.trans h₂.symm

theorem leakageBisim_rejects_uniformDetTarget :
    ¬ LeakageBisim (fun _ o => o) nondetAlignSource uniformDetTarget := by
  apply leakageBisim_incompatible_with_determinizer (fun _ o => o)
    nondetAlignSource uniformDetTarget
    (by intro _ _ _ _ h₁ h₂; exact h₁.trans h₂.symm)
    () false false true trivial trivial
  decide

theorem uniformRefinement_admits_uniformDetTarget :
    UniformRefinement (fun _ o => o) nondetAlignSource uniformDetTarget := by
  constructor
  · intro _ _ o ho
    exact ⟨o, trivial, rfl⟩
  · intro _ _ _ _ ho _
    exact ho

theorem uniformRefinement_rejects_leakyDetTarget :
    ¬ UniformRefinement (fun _ o => o) nondetAlignSource leakyDetTarget := by
  intro href
  have hbad : leakyDetTarget () false true :=
    href.2 () true false true rfl ⟨true, trivial, rfl⟩
  cases hbad

/-! ## Section 2: Horizontal 2-Safety Breakdown Across a GC / Timing Membrane -/

/-- A managed-language module producing both a logical public result (`Nat`) and a
    managed-heap allocation count (`Nat`) that is invisible in the source language semantics. -/
structure ManagedModule where
  logicalOut : Unit → Bool → Nat
  allocCount : Unit → Bool → Nat

/-- Source semantics of a managed module: exposes only `logicalOut`, erasing heap allocations. -/
def managedSourceSem (M : ManagedModule) : Sem Unit Bool Nat :=
  fun l h o => o = M.logicalOut l h

/-- Target FFI/runtime observation when linked with a native timing/GC-observing context:
    exposes both `logicalOut` and whether a GC compaction pause was triggered (`threshold ≤ allocCount`). -/
structure NativeGCObs where
  logicalOut : Nat
  gcPause : Bool
  deriving DecidableEq

/-- Heterogeneous membrane linking a managed module with a native context that observes GC
    pauses whenever managed allocation reaches `threshold`. -/
def membraneGCSem (threshold : Nat) (M : ManagedModule) : Sem Unit Bool NativeGCObs :=
  fun l h obs => obs = ⟨M.logicalOut l h, decide (threshold ≤ M.allocCount l h)⟩

/-- Concrete managed module: always returns `0` logically (source 2-safe), but allocates
    `1` object when `h = false` and `10` objects when `h = true`. -/
def secretAllocModule : ManagedModule where
  logicalOut := fun _ _ => 0
  allocCount := fun _ h => if h then 10 else 1

/-- In its own source language semantics, `secretAllocModule` is 2-safe (non-interfering). -/
theorem secretAllocModule_source_twoSafety :
    TwoSafety (managedSourceSem secretAllocModule) := by
  intro _ _ _ _ _ h₁ h₂
  exact h₁.trans h₂.symm

/-- Crossing the GC-observing FFI membrane (`threshold = 5`) breaks 2-safety horizontally,
    even though the source module is 2-safe and performs no secret-dependent logical outputs. -/
theorem membrane_breaks_two_safety :
    ¬ TwoSafety (membraneGCSem 5 secretAllocModule) := by
  intro h2s
  have hEq :
      (⟨0, false⟩ : NativeGCObs) = ⟨0, true⟩ :=
    h2s () false true ⟨0, false⟩ ⟨0, true⟩ rfl rfl
  cases hEq

/-- In contrast, 1-safety (`logicalOut = 0`) IS preserved across the exact same GC membrane. -/
theorem membrane_preserves_one_safety :
    ∀ l h obs, membraneGCSem 5 secretAllocModule l h obs → obs.logicalOut = 0 := by
  intro l h obs hobs
  rw [hobs]
  rfl

/-- Observation-enrichment fragility of `UniformRefinement` (conjunction witness without a
    separate linking operator): `managedSourceSem secretAllocModule` satisfies `UniformRefinement`
    with respect to the coarse `SetNI` (non-`TwoSafety`) specification `nondetLogicalSource`, while
    the richer GC-observing semantics `membraneGCSem 5 secretAllocModule` of the same
    `ManagedModule` record violates `TwoSafety`. -/
def nondetLogicalSource : Sem Unit Bool Nat := fun _ _ _ => True

theorem uniformRefinement_breaks_under_richer_context :
    UniformRefinement (fun _ o => o) nondetLogicalSource (managedSourceSem secretAllocModule) ∧
    ¬ TwoSafety (membraneGCSem 5 secretAllocModule) := by
  refine ⟨⟨?_, ?_⟩, membrane_breaks_two_safety⟩
  · intro _ _ o _
    exact ⟨o, trivial, rfl⟩
  · intro _ _ _ _ ho _
    exact ho

/-! ## Section 3: Galois Connections `(tau ⊣ sigma)` and 2-Safety Transfer Across Heterogeneous Alphabets -/

/-- A trace property (or behavior set) over trace space `A`. -/
abbrev PropSet (A : Type u) : Type u := A → Prop

/-- Subset ordering on trace properties. -/
def SubSet {A : Type u} (P Q : PropSet A) : Prop :=
  ∀ x, P x → Q x

/-- A cross-language trace relation `∼ ⊆ S × T`. -/
abbrev TraceRel (S : Type u) (T : Type v) : Type (max u v) := S → T → Prop

/-- Existential (direct) image `τ̃` (lower adjoint `α` of the Galois connection). -/
def tau {S : Type u} {T : Type v} (R : TraceRel S T) (P : PropSet S) : PropSet T :=
  fun t => ∃ s, R s t ∧ P s

/-- Universal image `σ̃` (upper adjoint `γ` of the Galois connection). -/
def sigma {S : Type u} {T : Type v} (R : TraceRel S T) (Q : PropSet T) : PropSet S :=
  fun s => ∀ t, R s t → Q t

/-- Exact Galois connection (adjunction law) `tau R ⊣ sigma R` (Abate et al., ESOP 2020 Def. 2.2 & 2.5). -/
theorem tau_sigma_galois {S : Type u} {T : Type v} (R : TraceRel S T)
    (P : PropSet S) (Q : PropSet T) :
    SubSet (tau R P) Q ↔ SubSet P (sigma R Q) := by
  constructor
  · intro h s hs t hst
    exact h t ⟨s, hst, hs⟩
  · intro h t ⟨s, hst, hs⟩
    exact h s hs t hst

/-- Trace-relating compiler correctness `CC_R` for a pair of behaviors `(BehS, BehT)`:
    every target trace is related via `R` to some source trace (i.e., `BehT ⊆ tau R BehS`). -/
def CCRel {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) : Prop :=
  SubSet BehT (tau R BehS)

/-- Property preservation via existential image `TP_tau`. -/
def TPTau {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) : Prop :=
  ∀ P : PropSet S, SubSet BehS P → SubSet BehT (tau R P)

/-- Property preservation via universal image `TP_sigma`. -/
def TPSigma {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) : Prop :=
  ∀ Q : PropSet T, SubSet BehS (sigma R Q) → SubSet BehT Q

/-- Trinitarian View part 1: `CC_R ↔ TP_tau` (Abate et al., ESOP 2020 Thm. 2.6). -/
theorem ccRel_iff_tpTau {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) :
    CCRel R BehS BehT ↔ TPTau R BehS BehT := by
  constructor
  · intro hcc P hP t ht
    rcases hcc t ht with ⟨s, hst, hs⟩
    exact ⟨s, hst, hP s hs⟩
  · intro htp
    exact htp BehS (fun _ hs => hs)

/-- Trinitarian View part 2: `CC_R ↔ TP_sigma` (Abate et al., ESOP 2020 Thm. 2.6). -/
theorem ccRel_iff_tpSigma {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) :
    CCRel R BehS BehT ↔ TPSigma R BehS BehT := by
  constructor
  · intro hcc Q hQ t ht
    rcases hcc t ht with ⟨s, hst, hs⟩
    exact hQ s hs t hst
  · intro htp
    exact htp (tau R BehS) (fun s hs t hst => ⟨s, hst, hs⟩)

/-- Abstract 2-safety / relational non-interference over an arbitrary trace space `A`,
    parameterized by input low-equivalence `lowIn` and output low-equivalence `lowOut`. -/
def TwoSafetyRel {A : Type u} (lowIn lowOut : A → A → Prop) (Beh : PropSet A) : Prop :=
  ∀ t₁ t₂, Beh t₁ → Beh t₂ → lowIn t₁ t₂ → lowOut t₁ t₂

/-- Input low-equivalence reflection across membrane relation `R`: target traces with
    low-equivalent inputs can only relate to source traces with low-equivalent inputs. -/
def ReflectsLowIn {S : Type u} {T : Type v} (R : TraceRel S T)
    (lowInS : S → S → Prop) (lowInT : T → T → Prop) : Prop :=
  ∀ s₁ s₂ t₁ t₂, R s₁ t₁ → R s₂ t₂ → lowInT t₁ t₂ → lowInS s₁ s₂

/-- Output low-equivalence preservation across membrane relation `R`: low-equivalent source
    outputs can never split into target outputs distinguishable by the target observer. -/
def PreservesLowOut {S : Type u} {T : Type v} (R : TraceRel S T)
    (lowOutS : S → S → Prop) (lowOutT : T → T → Prop) : Prop :=
  ∀ s₁ s₂ t₁ t₂, R s₁ t₁ → R s₂ t₂ → lowOutS s₁ s₂ → lowOutT t₁ t₂

/-- Sufficient condition for transferring 2-safety across an alphabet-changing membrane:
    if the boundary satisfies `CC_R` (`BehT ⊆ tau R BehS`), reflects input low-equivalence,
    and preserves output low-equivalence, then source 2-safety implies target 2-safety. -/
theorem galois_two_safety_composition {S : Type u} {T : Type v}
    (R : TraceRel S T)
    (lowInS lowOutS : S → S → Prop)
    (lowInT lowOutT : T → T → Prop)
    (BehS : PropSet S) (BehT : PropSet T)
    (hcc : CCRel R BehS BehT)
    (hIn : ReflectsLowIn R lowInS lowInT)
    (hOut : PreservesLowOut R lowOutS lowOutT)
    (hSrc : TwoSafetyRel lowInS lowOutS BehS) :
    TwoSafetyRel lowInT lowOutT BehT := by
  intro t₁ t₂ ht₁ ht₂ hlowInT
  rcases hcc t₁ ht₁ with ⟨s₁, hr₁, hs₁⟩
  rcases hcc t₂ ht₂ with ⟨s₂, hr₂, hs₂⟩
  have hlowInS : lowInS s₁ s₂ := hIn s₁ s₂ t₁ t₂ hr₁ hr₂ hlowInT
  have hlowOutS : lowOutS s₁ s₂ := hSrc s₁ s₂ hs₁ hs₂ hlowInS
  exact hOut s₁ s₂ t₁ t₂ hr₁ hr₂ hlowOutS

/-- Relational composition of heterogeneous membrane trace relations `R₁ : S × M` and `R₂ : M × T`. -/
def RelComp {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T) : TraceRel S T :=
  fun s t => ∃ m, R₁ s m ∧ R₂ m t

/-- `tau` distributes functorially over relational composition of trace relations. -/
theorem tau_relComp {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T) (P : PropSet S) (t : T) :
    tau (RelComp R₁ R₂) P t ↔ tau R₂ (tau R₁ P) t := by
  constructor
  · rintro ⟨s, ⟨m, h₁, h₂⟩, hs⟩
    exact ⟨m, h₂, ⟨s, h₁, hs⟩⟩
  · rintro ⟨m, h₂, ⟨s, h₁, hs⟩⟩
    exact ⟨s, ⟨m, h₁, h₂⟩, hs⟩

/-- `sigma` distributes contravariantly over relational composition of trace relations. -/
theorem sigma_relComp {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T) (Q : PropSet T) (s : S) :
    sigma (RelComp R₁ R₂) Q s ↔ sigma R₁ (sigma R₂ Q) s := by
  constructor
  · intro h m h₁ t h₂
    exact h t ⟨m, h₁, h₂⟩
  · intro h t ⟨m, h₁, h₂⟩
    exact h m h₁ t h₂

/-- Vertical composition of `ReflectsLowIn` across heterogeneous membranes `S → M → T`. -/
theorem relComp_reflectsLowIn {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T)
    (lowInS : S → S → Prop) (lowInM : M → M → Prop) (lowInT : T → T → Prop)
    (h₁ : ReflectsLowIn R₁ lowInS lowInM)
    (h₂ : ReflectsLowIn R₂ lowInM lowInT) :
    ReflectsLowIn (RelComp R₁ R₂) lowInS lowInT := by
  rintro s₁ s₂ t₁ t₂ ⟨m₁, hr₁₁, hr₂₁⟩ ⟨m₂, hr₁₂, hr₂₂⟩ hlowInT
  exact h₁ s₁ s₂ m₁ m₂ hr₁₁ hr₁₂ (h₂ m₁ m₂ t₁ t₂ hr₂₁ hr₂₂ hlowInT)

/-- Vertical composition of `PreservesLowOut` across heterogeneous membranes `S → M → T`. -/
theorem relComp_preservesLowOut {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T)
    (lowOutS : S → S → Prop) (lowOutM : M → M → Prop) (lowOutT : T → T → Prop)
    (h₁ : PreservesLowOut R₁ lowOutS lowOutM)
    (h₂ : PreservesLowOut R₂ lowOutM lowOutT) :
    PreservesLowOut (RelComp R₁ R₂) lowOutS lowOutT := by
  rintro s₁ s₂ t₁ t₂ ⟨m₁, hr₁₁, hr₂₁⟩ ⟨m₂, hr₁₂, hr₂₂⟩ hlowOutS
  exact h₂ m₁ m₂ t₁ t₂ hr₂₁ hr₂₂ (h₁ s₁ s₂ m₁ m₂ hr₁₁ hr₁₂ hlowOutS)

/-- End-to-end heterogeneous chain 2-safety composition across two alphabet-changing
    boundaries `S → M → T`. -/
theorem heterogeneous_chain_two_safety {S : Type u} {M : Type v} {T : Type w}
    (R₁ : TraceRel S M) (R₂ : TraceRel M T)
    (lowInS lowOutS : S → S → Prop)
    (lowInM lowOutM : M → M → Prop)
    (lowInT lowOutT : T → T → Prop)
    (BehS : PropSet S) (BehM : PropSet M) (BehT : PropSet T)
    (hcc₁ : CCRel R₁ BehS BehM)
    (hcc₂ : CCRel R₂ BehM BehT)
    (hIn₁ : ReflectsLowIn R₁ lowInS lowInM)
    (hIn₂ : ReflectsLowIn R₂ lowInM lowInT)
    (hOut₁ : PreservesLowOut R₁ lowOutS lowOutM)
    (hOut₂ : PreservesLowOut R₂ lowOutM lowOutT)
    (hSrc : TwoSafetyRel lowInS lowOutS BehS) :
    TwoSafetyRel lowInT lowOutT BehT := by
  have hcc12 : CCRel (RelComp R₁ R₂) BehS BehT := by
    intro t ht
    rcases hcc₂ t ht with ⟨m, hr₂, hm⟩
    rcases hcc₁ m hm with ⟨s, hr₁, hs⟩
    exact ⟨s, ⟨m, hr₁, hr₂⟩, hs⟩
  exact galois_two_safety_composition (RelComp R₁ R₂)
    lowInS lowOutS lowInT lowOutT BehS BehT hcc12
    (relComp_reflectsLowIn R₁ R₂ lowInS lowInM lowInT hIn₁ hIn₂)
    (relComp_preservesLowOut R₁ R₂ lowOutS lowOutM lowOutT hOut₁ hOut₂)
    hSrc

/-! ### Sharpness Check: Linking the GC Membrane to `CC_R`, `ReflectsLowIn`, and `PreservesLowOut` -/

/-- Source trace pairing input `(Unit × Bool)` with logical output `Nat`. -/
abbrev SrcTrace := Unit × Bool × Nat

/-- Target trace pairing input `(Unit × Bool)` with `NativeGCObs`. -/
abbrev TgtGCTrace := Unit × Bool × NativeGCObs

/-- Projection trace relation for the GC membrane: relates a source trace to any target trace
    with the same inputs and the same `logicalOut`, ignoring `gcPause`. -/
def gcTraceRel : TraceRel SrcTrace TgtGCTrace :=
  fun s t => s.1 = t.1 ∧ s.2.1 = t.2.1 ∧ s.2.2 = t.2.2.logicalOut

def srcLowIn : SrcTrace → SrcTrace → Prop := fun s₁ s₂ => s₁.1 = s₂.1
def srcLowOut : SrcTrace → SrcTrace → Prop := fun s₁ s₂ => s₁.2.2 = s₂.2.2
def tgtLowIn : TgtGCTrace → TgtGCTrace → Prop := fun t₁ t₂ => t₁.1 = t₂.1
def tgtLowOut : TgtGCTrace → TgtGCTrace → Prop := fun t₁ t₂ => t₁.2.2 = t₂.2.2

/-- Behavior sets of `secretAllocModule` in source and across `membraneGCSem 5`. -/
def secretAllocSrcBeh : PropSet SrcTrace :=
  fun s => managedSourceSem secretAllocModule s.1 s.2.1 s.2.2

def secretAllocTgtBeh : PropSet TgtGCTrace :=
  fun t => membraneGCSem 5 secretAllocModule t.1 t.2.1 t.2.2

/-- The GC membrane satisfies trace-relating compiler correctness `CC_gcTraceRel`. -/
theorem gc_membrane_satisfies_ccRel :
    CCRel gcTraceRel secretAllocSrcBeh secretAllocTgtBeh := by
  intro t ht
  refine ⟨(t.1, t.2.1, t.2.2.logicalOut), ⟨rfl, rfl, rfl⟩, ?_⟩
  unfold secretAllocSrcBeh managedSourceSem
  unfold secretAllocTgtBeh membraneGCSem at ht
  rw [ht]

/-- The GC membrane reflects input low-equivalence. -/
theorem gc_membrane_reflectsLowIn :
    ReflectsLowIn gcTraceRel srcLowIn tgtLowIn := by
  rintro s₁ s₂ t₁ t₂ ⟨h₁, _, _⟩ ⟨h₂, _, _⟩ hIn
  exact h₁.trans (hIn.trans h₂.symm)

/-- Sharpness: the GC membrane specifically violates `PreservesLowOut`, explaining why
    `galois_two_safety_composition` fails to apply even though `CC_R` and `ReflectsLowIn` hold. -/
theorem gc_membrane_violates_preservesLowOut :
    ¬ PreservesLowOut gcTraceRel srcLowOut tgtLowOut := by
  intro hOut
  have hEq :
      (⟨0, false⟩ : NativeGCObs) = ⟨0, true⟩ :=
    hOut ((), false, 0) ((), true, 0)
         ((), false, ⟨0, false⟩) ((), true, ⟨0, true⟩)
         ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ rfl
  cases hEq

/-! ### Section 4: Galois Insertion and General Hyperproperty Transfer (Abate et al., Thm. 5.3 / B.5) -/

/-- A hyperproperty over trace space `A` (closed under extensional equivalence of behaviors). -/
abbrev Hyperprop (A : Type u) : Type u := PropSet A → Prop

/-- Extensional invariance of a hyperproperty (respecting pointwise iff of trace sets). -/
def ExtInvariant {A : Type u} (H : Hyperprop A) : Prop :=
  ∀ P Q : PropSet A, (∀ x, P x ↔ Q x) → H P → H Q

/-- Galois insertion condition on `tau R ⊣ sigma R`: `tau R (sigma R Q) ⇔ Q` for every
    target property `Q` (no target property information is lost by round-tripping through source). -/
def GaloisInsertion {S : Type u} {T : Type v} (R : TraceRel S T) : Prop :=
  ∀ (Q : PropSet T) (t : T), tau R (sigma R Q) t ↔ Q t

/-- Lifting `sigma R` to map target hyperproperties to source hyperproperty obligations
    (Abate et al., ESOP 2020 Def. 2.10). -/
def liftSigmaHyper {S : Type u} {T : Type v} (R : TraceRel S T) (HT : Hyperprop T) : Hyperprop S :=
  fun BehS => ∃ Q : PropSet T, HT Q ∧ ∀ s, BehS s ↔ sigma R Q s

/-- Exact image condition `HC_R`: `BehT` coincides pointwise with `tau R BehS`. -/
def HCRel {S : Type u} {T : Type v} (R : TraceRel S T)
    (BehS : PropSet S) (BehT : PropSet T) : Prop :=
  ∀ t, BehT t ↔ tau R BehS t

/-- Abate et al. Weak Trinity (ESOP 2020 Thm. 5.3 / B.5): under exact trace image `HC_R`
    and a Galois insertion (`tau R ∘ sigma R = id`), any extensionally invariant target
    hyperproperty `HT` (including non-subset-closed hyperliveness / GNI) transfers from its
    `sigma`-lifted source obligation `liftSigmaHyper R HT`. -/
theorem galois_insertion_transfers_sigma_hyperprop {S : Type u} {T : Type v}
    (R : TraceRel S T)
    (hGI : GaloisInsertion R)
    (BehS : PropSet S) (BehT : PropSet T)
    (hHC : HCRel R BehS BehT)
    (HT : Hyperprop T)
    (hExt : ExtInvariant HT)
    (hSrc : liftSigmaHyper R HT BehS) :
    HT BehT := by
  rcases hSrc with ⟨Q, hQ, hBehS⟩
  apply hExt Q BehT _ hQ
  intro t
  constructor
  · intro hQt
    have hTauSig : tau R (sigma R Q) t := (hGI Q t).mpr hQt
    rcases hTauSig with ⟨s, hst, hs⟩
    exact (hHC t).mpr ⟨s, hst, (hBehS s).mpr hs⟩
  · intro hBt
    rcases (hHC t).mp hBt with ⟨s, hst, hs⟩
    have hSig : sigma R Q s := (hBehS s).mp hs
    exact hSig t hst

/-- A concrete trace relation that is NOT a Galois insertion: the GC projection `gcTraceRel`
    collapses `((), false, ⟨0, false⟩)` and `((), false, ⟨0, true⟩)` onto the same source trace
    `((), false, 0)`, so `tau ∘ sigma` cannot isolate a single `gcPause` value. -/
theorem gcTraceRel_not_galoisInsertion : ¬ GaloisInsertion gcTraceRel := by
  intro hGI
  let Q : PropSet TgtGCTrace := fun t => t.2.2.gcPause = false
  have hmem : Q ((), false, ⟨0, false⟩) := rfl
  have htau : tau gcTraceRel (sigma gcTraceRel Q) ((), false, ⟨0, false⟩) :=
    (hGI Q ((), false, ⟨0, false⟩)).mpr hmem
  rcases htau with ⟨s, ⟨hs1, hs2, hs3⟩, hsig⟩
  have hbad : Q ((), false, ⟨0, true⟩) :=
    hsig ((), false, ⟨0, true⟩) ⟨hs1, hs2, hs3⟩
  cases hbad

end Toy.HyperComposition
