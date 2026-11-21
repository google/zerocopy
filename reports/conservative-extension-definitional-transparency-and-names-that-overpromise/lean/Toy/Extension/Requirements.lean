/-
Requirements and specifications, in two settings.

1. A generic vocabulary extension `ι : SigHom LE L`: domain knowledge `K` and a
   requirement `R` over `LE`, a specification `Spec` over `L`. Consequence-
   conservativity of `K ∪ Spec` over `K` (for `LE`-sentences) leaves the
   specification nothing to contribute to a requirement over `LE`.
2. A split following the reference model of Gunter, Gunter, Jackson and Zave:
   `LW` holds the phenomena visible to the environment (environment-controlled
   `eh`, `ev` and machine-controlled shared `sv`) and is the vocabulary of `K`
   and `R`; `LS` holds the shared phenomena (`ev`, `sv`) and is the vocabulary
   of the specification; `LEv` holds the environment-controlled phenomena
   visible to the machine (`ev`). The specification condition is their
   relative-consistency obligation: every admissible behaviour of `ev` admits a
   specification-conforming response, and every such response is compatible
   with the domain knowledge.
-/
import Toy.Extension.Definitional

namespace Toy.Extension

/-! ## 1. Generic consequence-conservativity criteria -/

section Generic

variable {LE L : Sig}

/-- `K ∪ Spec`: the domain knowledge read in the larger vocabulary, together
with the specification. -/
def combined (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Theory L :=
  (K.map ι).union Spec

/-- The requirement argument `K, Spec ⊨ R`. -/
def Adequate (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) (R : Sentence LE) : Prop :=
  Entails (combined ι K Spec) (R.map ι)

/-- An `LE`-sentence that `K ∪ Spec` entails but the translated `K` alone does
not. Measured against `K.map ι`, so a change of vocabulary alone never counts
(`specConservative_empty`). -/
def SpecAddedConsequence (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L)
    (φ : Sentence LE) : Prop :=
  Entails (combined ι K Spec) (φ.map ι) ∧ ¬ Entails (K.map ι) (φ.map ι)

/-- `K ∪ Spec` adds no `LE`-consequence to the translated `K`. -/
def SpecConservative (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Prop :=
  ∀ φ : Sentence LE, Entails (combined ι K Spec) (φ.map ι) → Entails (K.map ι) (φ.map ι)

/-- Every model of the translated `K` can be changed outside the image of `ι`
(same carrier, same reduct) into a model of `K ∪ Spec`. -/
def SpecExpansionProperty (ι : SigHom LE L) (K : Theory LE) (Spec : Theory L) : Prop :=
  ∀ (β : Type) (M : Str L β), M.ModelsTh (K.map ι) →
    ∃ M' : Str L β, M'.reduct ι = M.reduct ι ∧ M'.ModelsTh (combined ι K Spec)

/-- Duality between the two generic notions (definitional). -/
theorem specConservative_iff_no_added_consequence (ι : SigHom LE L) (K : Theory LE)
    (Spec : Theory L) :
    SpecConservative ι K Spec ↔ ¬ ∃ φ, SpecAddedConsequence ι K Spec φ := by
  constructor
  · rintro h ⟨φ, h1, h2⟩
    exact h2 (h φ h1)
  · intro h φ h1
    exact Classical.byContradiction fun h2 => h ⟨φ, h1, h2⟩

/-- Positive example (`SpecConservative`): the empty specification, for every
morphism `ι` (injective or not) and every `K`. -/
theorem specConservative_empty (ι : SigHom LE L) (K : Theory LE) :
    SpecConservative ι K Theory.empty :=
  fun _ h β S hS => h β S ((modelsTh_union _ _ _).2 ⟨hS, modelsTh_empty _⟩)

/-- Positive example (`SpecExpansionProperty`): the empty specification, for
every morphism `ι` and every `K`. -/
theorem specExpansionProperty_empty (ι : SigHom LE L) (K : Theory LE) :
    SpecExpansionProperty ι K Theory.empty :=
  fun _ M hM => ⟨M, rfl, (modelsTh_union _ _ _).2 ⟨hM, modelsTh_empty _⟩⟩

/-- **Main result.** If `K ∪ Spec` is consequence-conservative over the
translated `K` for `LE`-sentences and the requirement argument `K, Spec ⊨ R`
holds for an `LE`-sentence `R`, then the translated `K` already entails the translated `R`:
the specification contributes nothing to the requirement. -/
theorem adequate_specConservative_implies_translated_domain_entails (ι : SigHom LE L)
    (K : Theory LE) (Spec : Theory L) (R : Sentence LE)
    (hcons : SpecConservative ι K Spec) (hadq : Adequate ι K Spec R) :
    Entails (K.map ι) (R.map ι) :=
  hcons R hadq

/-- The expansion-property criterion collapses in the same way: under it, the
requirement argument holds iff the translated `K` already entails the translated `R`. -/
theorem specExpansionProperty_adequate_iff (ι : SigHom LE L) (K : Theory LE)
    (Spec : Theory L) (R : Sentence LE) (hexp : SpecExpansionProperty ι K Spec) :
    Adequate ι K Spec R ↔ Entails (K.map ι) (R.map ι) := by
  constructor
  · intro hadq β M hM
    obtain ⟨M', hred, hM'⟩ := hexp β M hM
    have h := (models_map ι M' R).1 (hadq β M' hM')
    rw [hred] at h
    exact (models_map ι M R).2 h
  · intro h β M hM
    exact h β M (fun φ hφ => hM φ (Or.inl hφ))

/-- The expansion-property criterion implies the consequence criterion. -/
theorem specExpansionProperty_specConservative (ι : SigHom LE L) (K : Theory LE)
    (Spec : Theory L) (hexp : SpecExpansionProperty ι K Spec) : SpecConservative ι K Spec :=
  fun R hadq => (specExpansionProperty_adequate_iff ι K Spec R hexp).1 hadq

end Generic

/-! ### A generic example: a vocabulary extension by one propositional symbol -/

/-- Two propositional phenomena: a train is in the crossing; a car is in the crossing. -/
inductive EnvRel | train | car
  deriving DecidableEq

/-- The base vocabulary: two 0-ary relation symbols. -/
abbrev LEnv : Sig := ⟨Empty, EnvRel, fun e => e.elim, fun _ => 0⟩

/-- The extended vocabulary: adds one 0-ary symbol `gate` (the new symbol `none`).
No control or visibility distinction is modeled in this section. -/
abbrev LCross : Sig := LEnv.addRel 0

/-- Inclusion of the base vocabulary. -/
def ιCross : SigHom LEnv LCross := SigHom.inclRel LEnv 0

/-- `train`. -/
def trainIn : Sentence LEnv := .rel EnvRel.train (fun i => i.elim0)

/-- `car`. -/
def carIn : Sentence LEnv := .rel EnvRel.car (fun i => i.elim0)

/-- `gate`. -/
def gateDown : Sentence LCross := .rel (none : LCross.Rel) (fun i => i.elim0)

/-- Requirement: `¬ (train ∧ car)`. -/
def noCollision : Sentence LEnv := (Formula.and trainIn carIn).not

/-- The specification `{train → gate, gate → ¬ car}`. -/
def specCross : Theory LCross :=
  Theory.ofList [.imp (trainIn.map ιCross) gateDown, .imp gateDown (carIn.map ιCross).not]

/-- A base structure in which both a train and a car are present. -/
def envBoth : Str LEnv Unit := ⟨fun e => e.elim, fun _ _ => True⟩

/-- A base structure in which nothing is present. -/
def envNone : Str LEnv Unit := ⟨fun e => e.elim, fun _ _ => False⟩

/-- Positive example (`Adequate`): `specCross` meets `¬ (train ∧ car)` with no
domain knowledge. -/
theorem crossing_adequate : Adequate ιCross Theory.empty specCross noCollision := by
  intro β S hS
  have h1 := hS _ (Or.inr (List.Mem.head _))
  have h2 := hS _ (Or.inr (List.Mem.tail _ (List.Mem.head _)))
  exact fun ⟨ht, hc⟩ => h2 (h1 ht) hc

/-- With no domain knowledge, `¬ (train ∧ car)` is not entailed, even in the
extended vocabulary. -/
theorem not_translated_entails_noCollision :
    ¬ Entails ((Theory.empty : Theory LEnv).map ιCross) (noCollision.map ιCross) := by
  intro h
  have hm := h Unit (envBoth.withRel (fun _ => True)) (fun _ ⟨_, hψ, _⟩ => hψ.elim)
  exact (models_map ιCross _ noCollision).1 hm ⟨trivial, trivial⟩

/-- Negative example (`Adequate`): with no specification, the requirement is
not met. -/
theorem empty_spec_not_adequate : ¬ Adequate ιCross Theory.empty Theory.empty noCollision := by
  intro h
  have hS : (envBoth.withRel (fun _ : Fin 0 → Unit => True)).ModelsTh
      (combined ιCross Theory.empty Theory.empty) := by
    rintro ψ (⟨_, hψ, _⟩ | hψ)
    · exact hψ.elim
    · exact hψ.elim
  exact h Unit _ hS ⟨trivial, trivial⟩

/-- Negative example (`SpecConservative`, `SpecExpansionProperty`): `specCross`
over the empty domain knowledge has neither property; the structure with
train and car present cannot be extended by any value of `gate`. -/
theorem specCross_not_specConservative_not_specExpansionProperty :
    ¬ SpecConservative ιCross Theory.empty specCross ∧
    ¬ SpecExpansionProperty ιCross Theory.empty specCross := by
  refine ⟨fun h => not_translated_entails_noCollision (h noCollision crossing_adequate),
    fun h => not_translated_entails_noCollision
      ((specExpansionProperty_adequate_iff _ _ _ _ h).1 crossing_adequate)⟩

/-- `hcons` in `adequate_specConservative_implies_translated_domain_entails` is
tight (witness class: a two-symbol propositional base vocabulary extended by
one symbol): `specCross` is adequate with no domain knowledge, and the
conclusion fails. -/
theorem translated_domain_entails_ce_not_conservative :
    Adequate ιCross Theory.empty specCross noCollision ∧
    ¬ Entails ((Theory.empty : Theory LEnv).map ιCross) (noCollision.map ιCross) :=
  ⟨crossing_adequate, not_translated_entails_noCollision⟩

/-- `hadq` in `adequate_specConservative_implies_translated_domain_entails` is
tight (same witness class): the empty specification is conservative, and the
conclusion fails. -/
theorem translated_domain_entails_ce_not_adequate :
    SpecConservative ιCross (Theory.empty : Theory LEnv) Theory.empty ∧
    ¬ Entails ((Theory.empty : Theory LEnv).map ιCross) (noCollision.map ιCross) :=
  ⟨specConservative_empty _ _, not_translated_entails_noCollision⟩

/-- Non-vacuity for `adequate_specConservative_implies_translated_domain_entails`:
domain knowledge `{¬ (train ∧ car)}` with the empty specification is
conservative and adequate. -/
theorem translated_domain_entails_nonvacuity :
    SpecConservative ιCross (Theory.ofList [noCollision]) Theory.empty ∧
    Adequate ιCross (Theory.ofList [noCollision]) Theory.empty noCollision :=
  ⟨specConservative_empty _ _, fun _ _ hS => hS _ (Or.inl ⟨noCollision, List.Mem.head _, rfl⟩)⟩

/-! ## 2. A split with control and visibility (reference-model style) -/

section Split

variable {LE LEv LS LW : Sig}

/-- Domain knowledge together with the specification, in the domain vocabulary. -/
def withSpec (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS) : Theory LW :=
  K.union (Spec.map ιSW)

/-- Specification adequacy `K, Spec ⊨ R`. -/
def SpecAdequate (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS) (R : Sentence LW) :
    Prop :=
  Entails (withSpec ιSW K Spec) R

/-- First half of relative consistency: for every model `M` of `K`, the
behaviour of the machine-visible environment-controlled phenomena in `M`
(its `LEv`-reduct) has a response on the shared phenomena satisfying `Spec`. -/
def SpecAcceptsEveryEnvInput (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  ∀ (β : Type) (M : Str LW β), M.ModelsTh K →
    ∃ N : Str LS β, N.reduct ιVS = (M.reduct ιSW).reduct ιVS ∧ N.ModelsTh Spec

/-- Second half of relative consistency: every response satisfying `Spec` to
an admissible `LEv`-behaviour extends (by some behaviour of the remaining
environment phenomena) to a model of `K`. -/
def SpecResponsesDomainConsistent (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  ∀ (β : Type) (M : Str LW β), M.ModelsTh K → ∀ N : Str LS β,
    N.reduct ιVS = (M.reduct ιSW).reduct ιVS → N.ModelsTh Spec →
      ∃ M' : Str LW β, M'.reduct ιSW = N ∧ M'.ModelsTh K

/-- Relative consistency of a specification: both halves. -/
def SpecRelConsistent (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW)
    (Spec : Theory LS) : Prop :=
  SpecAcceptsEveryEnvInput ιVS ιSW K Spec ∧ SpecResponsesDomainConsistent ιVS ιSW K Spec

/-- Consequence-conservativity of `K'` over `K` (both over `LW`) for the
sentences of a sub-vocabulary `LE` (for example, the environment-controlled
phenomena). -/
def ConservativeFor (ιEW : SigHom LE LW) (K K' : Theory LW) : Prop :=
  ∀ φ : Sentence LE, Entails K' (φ.map ιEW) → Entails K (φ.map ιEW)

/-- **Main result.** A relatively consistent specification cannot establish a
requirement that mentions only machine-visible environment-controlled
phenomena: if `Spec` is relatively consistent with `K` and `K, Spec ⊨ R` for
an `R` that is the translation of an `LEv`-sentence `ρ`, then `K ⊨ R`. -/
theorem specRelConsistent_adequate_ev_requirement_implies_domain_entails
    (ιVS : SigHom LEv LS) (ιSW : SigHom LS LW) (K : Theory LW) (Spec : Theory LS)
    (ρ : Sentence LEv) (hrc : SpecRelConsistent ιVS ιSW K Spec)
    (hadq : SpecAdequate ιSW K Spec ((ρ.map ιVS).map ιSW)) :
    Entails K ((ρ.map ιVS).map ιSW) := by
  intro β M hM
  obtain ⟨N, hN, hNS⟩ := hrc.1 β M hM
  obtain ⟨M', hM'N, hM'K⟩ := hrc.2 β M hM N hN hNS
  have hM'S : M'.ModelsTh (withSpec ιSW K Spec) :=
    (modelsTh_union _ _ _).2 ⟨hM'K, (modelsTh_map ιSW M' Spec).2 (hM'N ▸ hNS)⟩
  have h1 := (models_map ιVS _ ρ).1 ((models_map ιSW M' _).1 (hadq β M' hM'S))
  rw [hM'N, hN] at h1
  exact (models_map ιSW M _).2 ((models_map ιVS _ ρ).2 h1)

end Split

/-! ### Propositional vocabularies -/

/-- A propositional signature: the elements of `P` as 0-ary relation symbols. -/
abbrev propSig (P : Type) : Sig := ⟨Empty, P, fun e => e.elim, fun _ => 0⟩

/-- The morphism of propositional signatures induced by a map of symbols. -/
def propHom {P Q : Type} (f : P → Q) : SigHom (propSig P) (propSig Q) :=
  ⟨id, f, fun e => e.elim, fun _ => rfl⟩

/-- The propositional structure with truth values `v`. -/
def propStr {P : Type} (β : Type) (v : P → Prop) : Str (propSig P) β :=
  ⟨fun e => e.elim, fun p _ => v p⟩

/-- The atomic sentence `p`. -/
def atom {P : Type} (p : P) : Sentence (propSig P) := .rel p (fun i => i.elim0)

theorem rel_args_irrel {P β : Type} (S : Str (propSig P) β) (p : P)
    (a b : Fin ((propSig P).relArity p) → β) : S.rel p a ↔ S.rel p b := by
  have : a = b := funext (fun i => i.elim0)
  rw [this]

theorem propSig_str_ext {P β : Type} {S T : Str (propSig P) β}
    (h : ∀ p, S.rel p (fun i => i.elim0) ↔ T.rel p (fun i => i.elim0)) : S = T := by
  cases S with
  | mk fS rS =>
    cases T with
    | mk fT rT =>
      have hf : fS = fT := funext (fun e => e.elim)
      have hr : rS = rT := by
        funext p a
        have ha : a = (fun i => i.elim0) := funext (fun i => i.elim0)
        subst ha
        exact propext (h p)
      subst hf
      subst hr
      rfl

/-- Every propositional structure is the structure of its truth values. -/
theorem eq_propStr {P β : Type} (S : Str (propSig P) β) :
    S = propStr β (fun p => S.rel p (fun i => i.elim0)) :=
  propSig_str_ext (fun _ => Iff.rfl)

/-! ### Crossing with the car hidden from the machine: legitimate control -/

/-- `ev`: the environment-controlled phenomenon visible to the machine. -/
inductive CEvA | train
  deriving DecidableEq

/-- Shared phenomena `ev ∪ sv`: `train` and the machine-controlled `gate`. -/
inductive CSA | train | gate
  deriving DecidableEq

/-- Environment-visible phenomena `eh ∪ ev ∪ sv`: `car` is environment-controlled
and hidden from the machine. -/
inductive CWA | train | gate | car
  deriving DecidableEq

/-- Environment-controlled phenomena `eh ∪ ev`. -/
inductive CEnvA | train | car
  deriving DecidableEq

def ιVSA : SigHom (propSig CEvA) (propSig CSA) := propHom (fun | .train => .train)
def ιSWA : SigHom (propSig CSA) (propSig CWA) := propHom (fun | .train => .train | .gate => .gate)
def ιEWA : SigHom (propSig CEnvA) (propSig CWA) := propHom (fun | .train => .train | .car => .car)

/-- Domain knowledge: cars stay out when the gate is down (`gate → ¬ car`). -/
def domainA : Theory (propSig CWA) :=
  Theory.ofList [Formula.imp (atom CWA.gate) (atom CWA.car).not]

/-- Specification over the shared phenomena: `train → gate`. -/
def specA : Theory (propSig CSA) := Theory.ofList [Formula.imp (atom CSA.train) (atom CSA.gate)]

/-- The requirement `¬ (train ∧ car)`, over the environment-controlled phenomena. -/
def noCollisionE : Sentence (propSig CEnvA) :=
  (Formula.and (atom CEnvA.train) (atom CEnvA.car)).not

/-- Truth values on the shared phenomena: `train` as given, `gate` always down. -/
def valSA (t : Prop) : CSA → Prop
  | .train => t
  | .gate => True

/-- Truth values on the environment-visible phenomena: `train` and `gate` as
given, `car` absent. -/
def valWA (t g : Prop) : CWA → Prop
  | .train => t
  | .gate => g
  | .car => False

/-- **Main result (counterexample).** With `train` machine-visible, `car`
hidden, `gate` machine-controlled, domain knowledge `gate → ¬ car` and
specification `train → gate`: the specification meets `¬ (train ∧ car)`, the
domain knowledge alone does not, the specification is relatively consistent,
and yet `K ∪ Spec` is not consequence-conservative over `K` for sentences
about the environment-controlled phenomena. So consequence-conservativity
rejects this legitimate control. -/
theorem crossing_control_spec_relConsistent_not_envConservative :
    SpecAdequate ιSWA domainA specA (noCollisionE.map ιEWA) ∧
    ¬ Entails domainA (noCollisionE.map ιEWA) ∧
    SpecRelConsistent ιVSA ιSWA domainA specA ∧
    ¬ ConservativeFor ιEWA domainA (withSpec ιSWA domainA specA) := by
  have hadq : SpecAdequate ιSWA domainA specA (noCollisionE.map ιEWA) := by
    intro β M hM
    rw [eq_propStr M] at hM ⊢
    have hK := hM _ (Or.inl (List.Mem.head _))
    have hS := hM _ (Or.inr ⟨_, List.Mem.head _, rfl⟩)
    exact fun ⟨ht, hc⟩ => hK (hS ht) hc
  have hnot : ¬ Entails domainA (noCollisionE.map ιEWA) := by
    intro h
    have hK : (propStr Unit (fun | .train => True | .gate => False | .car => True)).ModelsTh
        domainA := by
      intro φ hφ
      cases hφ with
      | head => exact fun h => h.elim
      | tail _ h => cases h
    exact h Unit _ hK ⟨trivial, trivial⟩
  refine ⟨hadq, hnot, ⟨?_, ?_⟩, fun h => hnot (h noCollisionE hadq)⟩
  · intro β M _
    refine ⟨propStr β (valSA (M.rel CWA.train (fun i => i.elim0))), ?_, ?_⟩
    · apply propSig_str_ext
      intro p
      cases p
      exact rel_args_irrel M CWA.train _ _
    · intro φ hφ
      cases hφ with
      | head => exact fun _ => trivial
      | tail _ h => cases h
  · intro β _ _ N _ _
    refine ⟨propStr β (valWA (N.rel CSA.train (fun i => i.elim0))
      (N.rel CSA.gate (fun i => i.elim0))), ?_, ?_⟩
    · apply propSig_str_ext
      intro p
      cases p
      · exact rel_args_irrel N CSA.train _ _
      · exact rel_args_irrel N CSA.gate _ _
    · intro φ hφ
      cases hφ with
      | head => exact fun _ h => h
      | tail _ h => cases h

/-! ### Crossing with the car visible to the machine: a specification that restricts the environment -/

/-- `ev`: `train` and `car`, both environment-controlled and machine-visible. -/
inductive CEvB | train | car
  deriving DecidableEq

/-- Shared phenomena `ev ∪ sv`; here also all environment-visible phenomena. -/
inductive CSB | train | car | gate
  deriving DecidableEq

def ιVSB : SigHom (propSig CEvB) (propSig CSB) := propHom (fun | .train => .train | .car => .car)
def ιSWB : SigHom (propSig CSB) (propSig CSB) := propHom id

/-- The requirement `¬ (train ∧ car)`, over the machine-visible
environment-controlled phenomena. -/
def noCollisionEv : Sentence (propSig CEvB) :=
  (Formula.and (atom CEvB.train) (atom CEvB.car)).not

/-- The specification `{train → gate, gate → ¬ car}` over the shared phenomena. -/
def specB : Theory (propSig CSB) :=
  Theory.ofList [Formula.imp (atom CSB.train) (atom CSB.gate),
    Formula.imp (atom CSB.gate) (atom CSB.car).not]

theorem specB_adequate :
    SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) := by
  intro β M hM
  rw [eq_propStr M] at hM ⊢
  have h1 := hM _ (Or.inr ⟨_, List.Mem.head _, rfl⟩)
  have h2 := hM _ (Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl⟩)
  exact fun ⟨ht, hc⟩ => h2 (h1 ht) hc

theorem not_entails_noCollisionEv :
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) :=
  fun h => h Unit (propStr Unit (fun _ => True)) (modelsTh_empty _) ⟨trivial, trivial⟩

/-- **Main result (counterexample).** With `train` and `car` both
environment-controlled and machine-visible, `gate` machine-controlled and no
domain knowledge: the specification `{train → gate, gate → ¬ car}` meets
`¬ (train ∧ car)`, which the (empty) domain knowledge does not entail, but it
admits no response when a train and a car are both present, so it is not
relatively consistent. Moreover every adequate specification in this setting
fails relative consistency (by
`specRelConsistent_adequate_ev_requirement_implies_domain_entails`). -/
theorem crossing_restricting_spec_violates_env_input_condition :
    SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ SpecAcceptsEveryEnvInput ιVSB ιSWB Theory.empty specB ∧
    ∀ Spec : Theory (propSig CSB),
      SpecAdequate ιSWB Theory.empty Spec ((noCollisionEv.map ιVSB).map ιSWB) →
        ¬ SpecRelConsistent ιVSB ιSWB Theory.empty Spec := by
  refine ⟨specB_adequate, not_entails_noCollisionEv, fun h => ?_, fun Spec hadq hrc =>
    not_entails_noCollisionEv
      (specRelConsistent_adequate_ev_requirement_implies_domain_entails _ _ _ _ _ hrc hadq)⟩
  obtain ⟨N, hN, hNS⟩ := h Unit (propStr Unit (fun _ => True)) (modelsTh_empty _)
  have ht := congrArg (fun S : Str (propSig CEvB) Unit => S.rel CEvB.train (fun i => i.elim0)) hN
  have hc := congrArg (fun S : Str (propSig CEvB) Unit => S.rel CEvB.car (fun i => i.elim0)) hN
  have ht' : N.rel CSB.train (fun i => i.elim0) :=
    (rel_args_irrel N CSB.train _ _).1 (of_eq_true ht)
  have hc' : N.rel CSB.car (fun i => i.elim0) :=
    (rel_args_irrel N CSB.car _ _).1 (of_eq_true hc)
  rw [eq_propStr N] at hNS
  have h1 := hNS _ (List.Mem.head _)
  have h2 := hNS _ (List.Mem.tail _ (List.Mem.head _))
  exact h2 (h1 ht') hc'

/-! ### Tightness counterexamples, positive control and non-vacuity -/

/-- `hrc` in `specRelConsistent_adequate_ev_requirement_implies_domain_entails`
is tight (witness class: a three-symbol propositional split with no hidden
phenomena): `specB` is adequate for a requirement over the machine-visible
environment phenomena and the conclusion fails. -/
theorem ev_requirement_ce_not_relConsistent :
    SpecAdequate ιSWB Theory.empty specB ((noCollisionEv.map ιVSB).map ιSWB) ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) :=
  ⟨specB_adequate, not_entails_noCollisionEv⟩

theorem specRelConsistent_empty_B (K : Theory (propSig CSB))
    (hK : ∀ (β : Type) (M M' : Str (propSig CSB) β), M.ModelsTh K →
      M'.reduct ιVSB = M.reduct ιVSB → M'.ModelsTh K) :
    SpecRelConsistent ιVSB ιSWB K Theory.empty := by
  refine ⟨fun β M _ => ⟨M.reduct ιSWB, rfl, modelsTh_empty _⟩, fun β M hM N hN _ => ?_⟩
  have hNN : N.reduct ιSWB = N := propSig_str_ext (fun p => rel_args_irrel N p _ _)
  have hMM : M.reduct ιSWB = M := propSig_str_ext (fun p => rel_args_irrel M p _ _)
  refine ⟨N, hNN, hK β M N hM ?_⟩
  rw [hN, hMM]

/-- `hadq` in `specRelConsistent_adequate_ev_requirement_implies_domain_entails`
is tight (same witness class): the empty specification is relatively
consistent and the conclusion fails. -/
theorem ev_requirement_ce_not_adequate :
    SpecRelConsistent ιVSB ιSWB Theory.empty Theory.empty ∧
    ¬ Entails (Theory.empty : Theory (propSig CSB)) ((noCollisionEv.map ιVSB).map ιSWB) :=
  ⟨specRelConsistent_empty_B _ (fun _ _ _ _ _ => modelsTh_empty _), not_entails_noCollisionEv⟩

/-- Non-vacuity for `specRelConsistent_adequate_ev_requirement_implies_domain_entails`:
with domain knowledge `{¬ (train ∧ car)}` over the machine-visible phenomena,
the empty specification is relatively consistent and adequate. -/
theorem ev_requirement_nonvacuity :
    SpecRelConsistent ιVSB ιSWB (Theory.ofList [(noCollisionEv.map ιVSB).map ιSWB]) Theory.empty ∧
    SpecAdequate ιSWB (Theory.ofList [(noCollisionEv.map ιVSB).map ιSWB]) Theory.empty
      ((noCollisionEv.map ιVSB).map ιSWB) := by
  refine ⟨specRelConsistent_empty_B _ (fun β M M' hM hred φ hφ => ?_),
    fun _ _ hS => hS _ (Or.inl (List.Mem.head _))⟩
  cases hφ with
  | head =>
    have h := hM _ (List.Mem.head _)
    have h1 := (models_map ιVSB _ noCollisionEv).1 ((models_map ιSWB M _).1 h)
    refine (models_map ιSWB M' _).2 ((models_map ιVSB _ noCollisionEv).2 ?_)
    have hM'r : M'.reduct ιSWB = M' := propSig_str_ext (fun p => rel_args_irrel M' p _ _)
    have hMr : M.reduct ιSWB = M := propSig_str_ext (fun p => rel_args_irrel M p _ _)
    rw [hM'r, hred, ← hMr]
    exact h1
  | tail _ h => cases h

end Toy.Extension
