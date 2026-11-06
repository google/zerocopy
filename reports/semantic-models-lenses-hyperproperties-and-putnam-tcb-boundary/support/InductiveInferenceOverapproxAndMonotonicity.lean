/-
Copyright 2026 The Authors.
Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
https://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
https://opensource.org/licenses/MIT>, at your option.

Standalone Lean 4.34.1 Mechanization:
Inductive Inference Impossibility, Sound Over-Approximation versus Semantic
Completeness, and Crate-Monotonicity Laws in Semantic Verification Models.

This file is completely self-contained, uses zero custom axioms, zero `sorry`,
and zero `unsafe` declarations, and is verified directly by the Lean 4.34.1
kernel (`lean -DElab.async=false -Ddebug.skipKernelTC=false`).
-/

namespace SemanticModelsInductiveInference

/-!
## 0. Core Four-Primitive Semantic Model (`Language`, `Tool`, `BehaviorCodec`, `Spec`)

We formalize the constructive demonic refinement order on partial nondeterministic
behaviors (`Partial`, `Behavior`) and the four primitives of a semantic
verification framework:
1. `Language SemObs`: syntax `Prog`, inputs `Query`, concrete outcomes `Out`,
   observable spine projection `obs : Out → SemObs`, and semantics
   `sem : Prog → Query → Partial (Out → Prop)`.
2. `Spec` (`VerifiedSpineOn`, `FunctionalSpec`, `SpineNonDegenerate`,
   `ViolatesAtQuerySuite`): extrinsic relational and functional contracts.
3. `BehaviorCodec L₁ L₂`: query/outcome simulation morphisms preserving `SemObs`.
4. `Tool L_src L_tgt`: partial compilation or static verification passes
   `L_src.Prog → Partial L_tgt.Prog`.
-/

/-- Preorder typeclass for constructive refinement. -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Demonic partial computation: `defined` guards undefined behavior, and `val`
    yields the outcome predicate when defined. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Total deterministic/nondeterministic computation that is always defined. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _   := b

/-- Nowhere-defined computation (immediate Undefined Behavior / rejection). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val h   := False.elim h

/-- Convert a boolean predicate into a partial identity tool (`true ↦ pure p`,
    `false ↦ ub`). -/
def Bool.toPartial {B : Type u} (cond : Bool) (b : B) : Partial B where
  defined := cond = true
  val _   := b

/-- Outcome predicates refine by subset inclusion (`∀ o, P₁ o → P₂ o`). -/
instance instPreorderPred (Out : Type u) : Preorder (Out → Prop) where
  le P₁ P₂ := ∀ o, P₁ o → P₂ o
  le_refl _ _ h := h
  le_trans h₁₂ h₂₃ o h₁ := h₂₃ o (h₁₂ o h₁)

/-- Demonic refinement on `Partial B`: target is defined whenever source is
    defined, and its value refines the source value. -/
instance instPreorderPartial (B : Type u) [Preorder B] : Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Pointwise refinement on query-indexed behaviors. -/
instance instPreorderArrow (Q : Type u) (B : Type v) [Preorder B] :
    Preorder (Q → B) where
  le f₁ f₂ := ∀ q, f₁ q ≤ f₂ q
  le_refl _ _ := Preorder.le_refl _
  le_trans h₁₂ h₂₃ q := Preorder.le_trans (h₁₂ q) (h₂₃ q)

/-- A semantic behavior maps each query to a partial predicate over outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Primitive 1: `Language SemObs` with observable spine projection `obs`. -/
structure Language (SemObs : Type) where
  Prog     : Type
  Query    : Type
  Out      : Type
  obs      : Out → SemObs
  sem      : Prog → Behavior Query Out
  dom      : Query → Prop := fun _ => True
  abiValid : Query → Out → Prop := fun _ _ => True

/-- Helper constructor for languages where `Out = SemObs` and `obs = id`. -/
abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := id
  sem   := sem

/-- Safety of `prog` at query `q`. -/
abbrev Language.SafeAt {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) : Prop :=
  (L.sem prog q).defined

/-- `prog` safely produces concrete outcome `o` at query `q`. -/
abbrev Language.ProducesOut {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (o : L.Out) : Prop :=
  ∃ h : (L.sem prog q).defined, (L.sem prog q).val h o

/-- `prog` safely produces observable value `v : SemObs` at query `q`. -/
abbrev Language.Produces {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (v : SemObs) : Prop :=
  ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o ∧ L.obs o = v

/-- Non-vacuity of precondition `pre` relative to structural domain `dom`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

/-- Productivity of `prog` on `pre` (excludes empty-outcome miracle programs). -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Observable determinism of `prog` on `pre`. -/
def Language.DeterministicOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  ∀ q : L.Query, pre q →
    ∀ v₁ v₂ : SemObs, L.Produces p q v₁ → L.Produces p q v₂ → v₁ = v₂

/-- Observable query sensitivity of `prog` on `pre`. -/
def Language.QuerySensitiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  (∃ q₁ q₂ : L.Query, pre q₁ ∧ pre q₂ ∧ q₁ ≠ q₂) →
  ∃ (q₁ q₂ : L.Query) (v₁ v₂ : SemObs),
    pre q₁ ∧ pre q₂ ∧ v₁ ≠ v₂ ∧ L.Produces p q₁ v₁ ∧ L.Produces p q₂ v₂

/-- Non-chaotic behavior on `pre`: productive and excludes at least one observation
    at every valid query. -/
def Language.NonChaoticOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  L.ProductiveOn pre p ∧
  ∀ q : L.Query, pre q → ∃ v_excl : SemObs, ¬ L.Produces p q v_excl

/-- Specification behavior induced by `(pre, post)`. -/
def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => {
    defined := pre q
    val     := fun _ o => post q o
  }

/-- Verification of `prog` against `(dom, pre, post)`. -/
def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Spine-level verification of `prog` against `obsPost : L.Query → SemObs → Prop`. -/
def Language.VerifiedSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn dom pre (fun q o => obsPost q (L.obs o)) prog

abbrev Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedSpineOn L.dom pre obsPost prog

/-- Constructive violation of `post` by `badProg` at query `q₀`. -/
def Language.ViolatesAt {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) (q₀ : L.Query) : Prop :=
  pre q₀ ∧
  ∃ h : (L.sem badProg q₀).defined,
    ∃ o : L.Out, (L.sem badProg q₀).val h o ∧ ¬ post q₀ o

/-- Constructive violation of spine specification `obsPost` at some `q₀ ∈ pre`. -/
def Language.ViolatesSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (badProg : L.Prog) : Prop :=
  ∃ q₀ : L.Query, L.ViolatesAt pre (fun q o => obsPost q (L.obs o)) badProg q₀

/-- Undefined-behavior violation on `pre`. -/
def Language.ViolatesSafetyOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (badProg : L.Prog) : Prop :=
  ∃ q₀ : L.Query, pre q₀ ∧ ¬ L.SafeAt badProg q₀

/-- Same-query observable contrast against `goodProg`. -/
def Language.HasSameQueryContrast {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (goodProg : L.Prog) : Prop :=
  ∃ (altProg : L.Prog) (q₀ : L.Query) (v₁ v₂ : SemObs),
    pre q₀ ∧ L.Produces goodProg q₀ v₁ ∧ L.Produces altProg q₀ v₂ ∧ v₁ ≠ v₂

/-- Non-degenerate spine witness (`Candidate 006`–`016`). -/
def Language.SpineNonDegenerate {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg badProg : L.Prog) : Prop :=
  L.ViolatesSpine pre obsPost badProg ∨
  (L.ViolatesSafetyOn pre badProg ∧ L.HasSameQueryContrast pre goodProg)

/-- Conjunction over a list of propositions. -/
def AllHold : List Prop → Prop
  | []      => True
  | P :: Ps => P ∧ AllHold Ps

/-- Pairwise distinctness of a list of identifiers/queries. -/
def NoDupIds {α : Type u} : List α → Prop
  | []      => True
  | x :: xs => AllHold (xs.map (fun y => x ≠ y)) ∧ NoDupIds xs

/-- Functional (single-valued) specification on `pre`. -/
def FunctionalSpec {Query SemObs : Type}
    (pre : Query → Prop) (obsPost : Query → SemObs → Prop) : Prop :=
  ∀ q : Query, pre q →
    ∀ v₁ v₂ : SemObs, obsPost q v₁ → obsPost q v₂ → v₁ = v₂

/-- Point-separating (input-injective) specification on `pre` (`Candidate 008`). -/
def PointSeparatingSpec {Query SemObs : Type}
    (pre : Query → Prop) (obsPost : Query → SemObs → Prop) : Prop :=
  ∀ q₁ q₂ : Query, pre q₁ → pre q₂ → q₁ ≠ q₂ →
    ∀ v : SemObs, ¬ (obsPost q₁ v ∧ obsPost q₂ v)

/-- Pointwise refutability of `obsPost` on `pre` (`Candidate 006`–`016`). -/
def PointwiseRefutable {Query SemObs : Type}
    (pre : Query → Prop) (obsPost : Query → SemObs → Prop) : Prop :=
  ∀ q : Query, pre q → ∃ v_bad : SemObs, ¬ obsPost q v_bad

/-- Suite-indexed $k$-point query separation (`Candidate 008`–`016`). -/
def Language.ViolatesAtQuerySuite {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (suite : List (L.Query × L.Prog)) : Prop :=
  suite ≠ [] ∧
  NoDupIds (suite.map Prod.fst) ∧
  AllHold (suite.map (fun qp =>
    L.ViolatesAt pre (fun q o => obsPost q (L.obs o)) qp.2 qp.1 ∧
    AllHold (suite.map (fun qp' =>
      qp'.1 ≠ qp.1 → ∃ v : SemObs, L.Produces qp.2 qp'.1 v ∧ obsPost qp'.1 v))))

/-- Semantically diverse positive program suite (`Candidate 006`–`016`). -/
def Language.SemanticallyDiverseSuite {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (progs : List L.Prog) : Prop :=
  ∃ (p₁ p₂ : L.Prog),
    p₁ ∈ progs ∧ p₂ ∈ progs ∧
    ∃ (q₀ : L.Query) (v₁ v₂ : SemObs),
      pre q₀ ∧ v₁ ≠ v₂ ∧
      L.Produces p₁ q₀ v₁ ∧ L.Produces p₂ q₀ v₂ ∧
      ¬ L.Produces p₁ q₀ v₂

/-- Primitive 3: `BehaviorCodec` connecting source and target languages. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Identity `BehaviorCodec`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := congrArg L.obs (Option.some.inj h)

/-- Vertical composition of `BehaviorCodec`s. -/
def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂₃.encodeQuery (c₁₂.encodeQuery q₁)
  decodeQuery q₃ := c₁₂.decodeQuery (c₂₃.decodeQuery q₃)
  encodeOut o₁   := c₂₃.encodeOut (c₁₂.encodeOut o₁)
  decodeOut o₃   := Option.bind (c₂₃.decodeOut o₃) c₁₂.decodeOut
  decodeQuery_encodeQuery q₁ := by
    rw [c₂₃.decodeQuery_encodeQuery, c₁₂.decodeQuery_encodeQuery]
  decodeOut_encodeOut o₁ := by
    dsimp [Option.bind]
    rw [c₂₃.decodeOut_encodeOut]
    exact c₁₂.decodeOut_encodeOut o₁
  obs_decodeOut o₃ o₁ h := by
    dsimp [Option.bind] at h
    cases h₂₃ : c₂₃.decodeOut o₃ with
    | none => rw [h₂₃] at h; cases h
    | some o₂ =>
      rw [h₂₃] at h
      exact Eq.trans (c₂₃.obs_decodeOut o₃ o₂ h₂₃) (c₁₂.obs_decodeOut o₂ o₁ h)

/-- Pushforward of a source behavior along a `BehaviorCodec`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b₁ (c.decodeQuery q₂)).defined
    val     := fun h₁ o₂ =>
      ∃ o₁ : L₁.Out, c.decodeOut o₂ = some o₁ ∧ (b₁ (c.decodeQuery q₂)).val h₁ o₁
  }

/-- Demonic target-to-source compilation refinement (`Compiles`). -/
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Miracle-free compilation (`ProductiveCompiles`). -/
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₂ : L_tgt.Query,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined,
      ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

theorem ProductiveCompiles.refl {SemObs : Type} (L : Language SemObs) (p : L.Prog) :
    ProductiveCompiles L L (BehaviorCodec.id L) p p :=
  ⟨fun _ h => ⟨h, fun o ho => ⟨o, rfl, ho⟩⟩, fun _ h => h⟩

theorem ProductiveCompiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : ProductiveCompiles L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : ProductiveCompiles L₂ L₃ c₂₃ p₂ p₃) :
    ProductiveCompiles L₁ L₃ (BehaviorCodec.comp c₁₂ c₂₃) p₁ p₃ := by
  refine ⟨?_, ?_⟩
  · intro q₃ h₁
    have ⟨h₂, hval₂⟩ := h₁₂.1 (c₂₃.decodeQuery q₃) h₁
    have ⟨h₃, hval₃⟩ := h₂₃.1 q₃ h₂
    refine ⟨h₃, fun o₃ ho₃ => ?_⟩
    have ⟨o₂, hdec₂₃, ho₂⟩ := hval₃ o₃ ho₃
    have ⟨o₁, hdec₁₂, ho₁⟩ := hval₂ o₂ ho₂
    refine ⟨o₁, ?_, ho₁⟩
    dsimp [BehaviorCodec.comp, Option.bind]
    rw [hdec₂₃]
    exact hdec₁₂
  · intro q₃ h_prod₁
    exact h₂₃.2 q₃ (h₁₂.2 (c₂₃.decodeQuery q₃) h_prod₁)

/-- Primitive 4: `Tool L_src L_tgt` (partial compiler or verifier). -/
abbrev Tool {SemObs : Type} (L_src L_tgt : Language SemObs) : Type :=
  L_src.Prog → Partial L_tgt.Prog

abbrev Tool.Accepted {SemObs : Type} {L_src L_tgt : Language SemObs}
    (tool : Tool L_src L_tgt) (p : L_src.Prog) : Prop :=
  (tool p).defined

abbrev Tool.Rejected {SemObs : Type} {L_src L_tgt : Language SemObs}
    (tool : Tool L_src L_tgt) (p : L_src.Prog) : Prop :=
  ¬ (tool p).defined

/-- Vertical sequential composition of two tools (`Tool.comp`). -/
def Tool.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (tool₁ : Tool L₁ L₂) (tool₂ : Tool L₂ L₃) : Tool L₁ L₃ :=
  fun p₁ => {
    defined := ∃ h₁ : (tool₁ p₁).defined, (tool₂ ((tool₁ p₁).val h₁)).defined
    val     := fun h =>
      let h₁ : (tool₁ p₁).defined := h.1
      let h₂ : (tool₂ ((tool₁ p₁).val h₁)).defined := h.2
      (tool₂ ((tool₁ p₁).val h₁)).val h₂
  }

/-- Chained acceptance of a positive suite across `Tool.comp`. -/
def Tool.ChainedSuiteAccepted {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    (tool₁ : Tool L₁ L₂) (tool₂ : Tool L₂ L₃)
    (goodProgs : List L₁.Prog) : Prop :=
  AllHold (goodProgs.map (fun p => (Tool.comp tool₁ tool₂ p).defined))

/-!
## 1. The Gold–Angluin Finite-Witness & $k$-Point Evasion Impossibility Theorem
   (`GoldAngluinFiniteWitnessImpossibility`)

We formalize the dual inductive-inference impossibility laws (Gold 1967;
Angluin 1980; Blum & Blum 1975; Weyuker 1983):
1. **Program-Axis Finite-Witness Evasion (`allowlistCompiler`):**
   For *any* finite positive program suite `W_+ : List L_src.Prog` and disjoint
   negative suite `W_- : List L_src.Prog`, the syntactic allowlist restriction
   `allowlistCompiler base W_+` satisfies every positive acceptance clause on
   `W_+`, every negative rejection clause on `W_-`, and universal soundness on
   all accepted programs, while rejecting **every** valid program `p ∉ W_+`.
2. **Query-Axis $k$-Point Specification Evasion (`depthKFunctionalSpec`):**
   For *any* finite query suite `Q_k : List Query`, true specification function
   `f_true : Query → SemObs`, and fallback constant `c_bad : SemObs`, the
   functional specification `depthKFunctionalSpec Q_k f_true c_bad` agrees with
   `f_true` on `Q_k`, satisfies `FunctionalSpec`, `PointwiseRefutable`, and
   $k$-point `ViolatesAtQuerySuite`, and certifies a defective program that
   outputs `c_bad ≠ f_true q` at every uninspected query `q ∉ Q_k`.
-/

/-- Syntactic $N$-entry allowlist compiler restricting `base` to `W_+`. -/
def allowlistCompiler {SemObs : Type} {L_src L_tgt : Language SemObs}
    [DecidableEq L_src.Prog]
    (base : Tool L_src L_tgt) (W_pos : List L_src.Prog) : Tool L_src L_tgt :=
  fun p => {
    defined := p ∈ W_pos ∧ (base p).defined
    val     := fun h => (base p).val h.2
  }

/-- **Theorem 1A (`GoldAngluinFiniteWitnessImpossibility_Prog`):**
    For *any* finite positive program list `W_pos`, disjoint negative canary list
    `W_neg`, and compiler `base` that is defined and sound on `W_pos`:
    1. `allowlistCompiler base W_pos` accepts every `p ∈ W_pos`,
    2. rejects every `b ∈ W_neg`,
    3. satisfies `ProductiveCompiles` on *every* accepted program `p : L_src.Prog`,
    4. yet **rejects every program `p ∉ W_pos`** (even when `p` is semantically
       identical to a member of `W_pos`!). -/
theorem GoldAngluinFiniteWitnessImpossibility_Prog
    {SemObs : Type} {L_src L_tgt : Language SemObs}
    [DecidableEq L_src.Prog]
    (c : BehaviorCodec L_src L_tgt)
    (base : Tool L_src L_tgt)
    (W_pos W_neg : List L_src.Prog)
    (h_pos_defined : ∀ p, p ∈ W_pos → (base p).defined)
    (h_pos_sound : ∀ p, p ∈ W_pos → ∀ h : (base p).defined,
      ProductiveCompiles L_src L_tgt c p ((base p).val h))
    (h_disjoint : ∀ b, b ∈ W_neg → b ∉ W_pos) :
    (∀ p, p ∈ W_pos → Tool.Accepted (allowlistCompiler base W_pos) p) ∧
    (∀ b, b ∈ W_neg → Tool.Rejected (allowlistCompiler base W_pos) b) ∧
    (∀ p : L_src.Prog, ∀ h_acc : (allowlistCompiler base W_pos p).defined,
      ProductiveCompiles L_src L_tgt c p
        ((allowlistCompiler base W_pos p).val h_acc)) ∧
    (∀ p : L_src.Prog, p ∉ W_pos →
      Tool.Rejected (allowlistCompiler base W_pos) p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨hp, h_pos_defined p hp⟩
  · intro b hb h_acc
    exact h_disjoint b hb h_acc.1
  · intro p h_acc
    exact h_pos_sound p h_acc.1 h_acc.2
  · intro p hp_not h_acc
    exact hp_not h_acc.1

/-- Infinite-family source language `L_addK` (`Prog := Nat`, where program `k`
    computes `q + k`) from `PENTEST-R3-2B`. -/
abbrev L_addK : Language Nat :=
  Language.mkSimple Nat Nat Nat (fun k q => Partial.pure (fun o => o = q + k))

/-- Honest compiler on `L_addK` that compiles every `k : Nat` to itself. -/
def honestAddKCompiler : Tool L_addK L_addK :=
  fun k => Partial.pure k

/-- Maximum program index appearing in a finite specification suite `goodSpecs`. -/
def maxSpecProg : List (Nat × (Nat → Nat → Prop)) → Nat
  | []           => 0
  | (p, _) :: xs => Nat.max p (maxSpecProg xs)

theorem le_maxSpecProg {p : Nat} {post : Nat → Nat → Prop}
    { specs : List (Nat × (Nat → Nat → Prop)) }
    (h_mem : (p, post) ∈ specs) : p ≤ maxSpecProg specs := by
  induction specs with
  | nil => cases h_mem
  | cons hd tl ih =>
    cases h_mem with
    | head => exact Nat.le_max_left p (maxSpecProg tl)
    | tail _ h_tl =>
      exact Nat.le_trans (ih h_tl) (Nat.le_max_right hd.1 (maxSpecProg tl))

/-- **Theorem 1B (`FiniteGoodSpecsLocksOutInfiniteFamily` — `PENTEST-R3-2B`):**
    On `L_addK`, for *every* finite list `goodSpecs` of tight specifications
    (where each `(k, post) ∈ goodSpecs` satisfies `post 0 v → v = k`), the valid
    program `p_new = maxSpecProg goodSpecs + 1` is accepted and productively
    compiled by `honestAddKCompiler`, yet satisfies **no** specification in
    `goodSpecs`! -/
theorem FiniteGoodSpecsLocksOutInfiniteFamily
    (goodSpecs : List (Nat × (Nat → Nat → Prop)))
    (h_tight : ∀ sp, sp ∈ goodSpecs → ∀ v, sp.2 0 v → v = sp.1) :
    let p_new := maxSpecProg goodSpecs + 1
    Tool.Accepted honestAddKCompiler p_new ∧
    ProductiveCompiles L_addK L_addK (BehaviorCodec.id L_addK) p_new p_new ∧
    ∀ sp, sp ∈ goodSpecs →
      ¬ L_addK.VerifiedSpine (fun q => q < 100) sp.2 p_new := by
  dsimp only
  refine ⟨trivial, ProductiveCompiles.refl L_addK _, ?_⟩
  intro ⟨k, post⟩ h_mem ⟨_, _, h_ref⟩
  have h0 : (0 : Nat) < 100 := by decide
  have ⟨_, h_val⟩ := h_ref 0 h0
  have h_post : post 0 (maxSpecProg goodSpecs + 1) :=
    h_val (maxSpecProg goodSpecs + 1) (by dsimp [L_addK, Partial.pure]; omega)
  have h_eq : maxSpecProg goodSpecs + 1 = k := h_tight (k, post) h_mem _ h_post
  have h_le : k ≤ maxSpecProg goodSpecs := le_maxSpecProg h_mem
  omega

/-- General $k$-point rubber-stamp functional specification
    (`depthKFunctionalSpec`, generalizing `PENTEST-5`, `PENTEST-R2-5`,
    `PENTEST-R3-5B`, and `PENTEST-R4-9`):
    Agrees with `f_true` on the finite query suite `Q_k`, and maps every
    uninspected query `q ∉ Q_k` to the defective constant `c_bad`. -/
def depthKFunctionalSpec {Query SemObs : Type} [DecidableEq Query]
    (Q_k : List Query) (f_true : Query → SemObs) (c_bad : SemObs)
    (q : Query) (v : SemObs) : Prop :=
  v = if q ∈ Q_k then f_true q else c_bad

/-- Single-program language whose sole program `Unit.unit` agrees with `f_true`
    on `Q_k` and outputs `c_bad` outside `Q_k`. -/
abbrev L_buggyOutsideSuite {Query SemObs : Type} [DecidableEq Query]
    (Q_k : List Query) (f_true : Query → SemObs) (c_bad : SemObs) :
    Language SemObs :=
  Language.mkSimple Unit Query SemObs (fun _ q =>
    Partial.pure (fun o => o = if q ∈ Q_k then f_true q else c_bad))

/-- **Theorem 1C (`GoldAngluinFiniteWitnessImpossibility_Spec`):**
    For *any* finite query suite `Q_k : List Query`, true function `f_true`, and
    defective constant `c_bad`:
    1. `depthKFunctionalSpec Q_k f_true c_bad` is strictly single-valued
       (`FunctionalSpec pre`) across the entire domain,
    2. It agrees pointwise with the true specification `v = f_true q` on every
       tested query `q ∈ Q_k`,
    3. The defective program `Unit.unit` in `L_buggyOutsideSuite Q_k f_true c_bad`
       satisfies `VerifiedSpine pre (depthKFunctionalSpec Q_k f_true c_bad)`
       whenever `pre` is inhabited,
    4. Yet at **every** uninspected query `q ∉ Q_k` where `f_true q ≠ c_bad`,
       the certified program outputs `c_bad` and violates the true specification! -/
theorem GoldAngluinFiniteWitnessImpossibility_Spec
    {Query SemObs : Type} [DecidableEq Query]
    (pre : Query → Prop) (q₀ : Query) (hq₀ : pre q₀)
    (Q_k : List Query) (f_true : Query → SemObs) (c_bad : SemObs) :
    FunctionalSpec pre (depthKFunctionalSpec Q_k f_true c_bad) ∧
    (∀ q, q ∈ Q_k → ∀ v,
      depthKFunctionalSpec Q_k f_true c_bad q v ↔ v = f_true q) ∧
    (L_buggyOutsideSuite Q_k f_true c_bad).VerifiedSpine pre
      (depthKFunctionalSpec Q_k f_true c_bad) () ∧
    (∀ q, pre q → q ∉ Q_k → f_true q ≠ c_bad →
      (L_buggyOutsideSuite Q_k f_true c_bad).Produces () q c_bad ∧
      ¬ (c_bad = f_true q)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q _ v₁ v₂ h₁ h₂
    exact Eq.trans h₁ h₂.symm
  · intro q hq v
    dsimp [depthKFunctionalSpec]
    simp [hq]
  · refine ⟨Or.inl ⟨q₀, hq₀⟩,
      fun q _ => ⟨trivial, if q ∈ Q_k then f_true q else c_bad, rfl⟩,
      fun q _ => ⟨trivial, fun o ho => ho⟩⟩
  · intro q _ h_not_in h_ne
    refine ⟨⟨trivial, c_bad, ?_, rfl⟩, fun h_eq => h_ne h_eq.symm⟩
    dsimp [L_buggyOutsideSuite, Language.mkSimple, Partial.pure]
    simp [h_not_in]

/-- **Theorem 1D (`PointSeparatingSpecLocksOutBooleanAndParitySpecs` — `PENTEST-R3-5A`):**
    Attempting to block `depthKFunctionalSpec` by requiring `PointSeparatingSpec`
    (disjoint output fibers across distinct inputs `q₁ ≠ q₂`) causes a fatal
    Category A2 lockout:
    1. `paritySpec` (`v = q % 2`) is rejected by `PointSeparatingSpec` on `q < 100`.
    2. By the Pigeonhole Principle, on **any** boolean-valued language
       (`SemObs = Bool`) with at least 3 valid queries `q₁, q₂, q₃`, **no**
       specification `obsPost` can simultaneously admit a verified program and
       satisfy `PointSeparatingSpec`! -/
theorem PointSeparatingSpecLocksOutBooleanAndParitySpecs :
    ¬ PointSeparatingSpec (fun q : Nat => q < 100) (fun q v => v = q % 2) ∧
    ∀ (L : Language Bool) (pre : L.Query → Prop)
      (obsPost : L.Query → Bool → Prop) (p : L.Prog)
      (q₁ q₂ q₃ : L.Query),
      pre q₁ → pre q₂ → pre q₃ →
      q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
      L.VerifiedSpine pre obsPost p →
      ¬ PointSeparatingSpec pre obsPost := by
  refine ⟨?_, ?_⟩
  · intro h_sep
    exact h_sep 0 2 (by decide) (by decide) (by decide) 0 ⟨rfl, rfl⟩
  · intro L pre obsPost p q₁ q₂ q₃ hq₁ hq₂ hq₃ h12 h13 h23 ⟨_, h_prod, h_ref⟩ h_sep
    have ⟨hdef₁, o₁, ho₁⟩ := h_prod q₁ hq₁
    have ⟨hdef₂, o₂, ho₂⟩ := h_prod q₂ hq₂
    have ⟨hdef₃, o₃, ho₃⟩ := h_prod q₃ hq₃
    have hpost₁ : obsPost q₁ (L.obs o₁) := (h_ref q₁ hq₁).2 o₁ ho₁
    have hpost₂ : obsPost q₂ (L.obs o₂) := (h_ref q₂ hq₂).2 o₂ ho₂
    have hpost₃ : obsPost q₃ (L.obs o₃) := (h_ref q₃ hq₃).2 o₃ ho₃
    cases hb₁ : L.obs o₁ <;> cases hb₂ : L.obs o₂ <;> cases hb₃ : L.obs o₃
    · rw [hb₁] at hpost₁; rw [hb₂] at hpost₂
      exact h_sep q₁ q₂ hq₁ hq₂ h12 false ⟨hpost₁, hpost₂⟩
    · rw [hb₁] at hpost₁; rw [hb₂] at hpost₂
      exact h_sep q₁ q₂ hq₁ hq₂ h12 false ⟨hpost₁, hpost₂⟩
    · rw [hb₁] at hpost₁; rw [hb₃] at hpost₃
      exact h_sep q₁ q₃ hq₁ hq₃ h13 false ⟨hpost₁, hpost₃⟩
    · rw [hb₂] at hpost₂; rw [hb₃] at hpost₃
      exact h_sep q₂ q₃ hq₂ hq₃ h23 true ⟨hpost₂, hpost₃⟩
    · rw [hb₂] at hpost₂; rw [hb₃] at hpost₃
      exact h_sep q₂ q₃ hq₂ hq₃ h23 false ⟨hpost₂, hpost₃⟩
    · rw [hb₁] at hpost₁; rw [hb₃] at hpost₃
      exact h_sep q₁ q₃ hq₁ hq₃ h13 true ⟨hpost₁, hpost₃⟩
    · rw [hb₁] at hpost₁; rw [hb₂] at hpost₂
      exact h_sep q₁ q₂ hq₁ hq₂ h12 true ⟨hpost₁, hpost₂⟩
    · rw [hb₁] at hpost₁; rw [hb₂] at hpost₂
      exact h_sep q₁ q₂ hq₁ hq₂ h12 true ⟨hpost₁, hpost₂⟩

/-!
## 2. The Rice–Cousot Asymmetry Theorem: Sound Over-Approximation vs. Semantic
   Completeness (`RiceCousotOverapproxImpossibility`)

We formalize the three competing completeness/closure notions from `Candidate 008`
through `Candidate 016`:
- `Tool.SemanticallyClosedOn` (`Candidate 008`): dynamic equivalence forces
  equal tool acceptance.
- `Language.WellBehavedProgOn` & `Language.TotalWellBehavedDomainOn`
  (`Candidate 012`–`016`): intrinsic dynamic well-behavedness + AST-global
  constant initializer heuristics (`CanonicalConstInit`).
-/

/-- Semantic acceptance closure (`Candidate 008` `Tool.SemanticallyClosedOn`). -/
def Tool.SemanticallyClosedOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (pre : L_src.Query → Prop) (tool : Tool L_src L_tgt) : Prop :=
  ∀ p₁ p₂ : L_src.Prog,
    (∀ q : L_src.Query, pre q →
      ∀ v : SemObs, L_src.Produces p₁ q v ↔ L_src.Produces p₂ q v) →
    Tool.Accepted tool p₁ → Tool.Accepted tool p₂

/-- `Candidate 016` magic-number range filter `CanonicalConstInit`. -/
class CanonicalConstInit (SemObs : Type) where
  validMultiShift : (SemObs → Prop) → (SemObs → Prop) → Prop

instance instCanonicalConstInitNat : CanonicalConstInit Nat where
  validMultiShift rangeP' rangeB := ¬ rangeP' 1 ∧ ¬ rangeP' 26 ∧ ¬ rangeB 1

/-- `Candidate 016` intrinsic well-behavedness (`Language.WellBehavedProgOn`). -/
def Language.WellBehavedProgOn {SemObs : Type} [cci : CanonicalConstInit SemObs]
    (L : Language SemObs) (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  L.ProductiveOn pre p ∧
  L.DeterministicOn pre p ∧
  (L.QuerySensitiveOn pre p ∨
   ((∃ b_ub : L.Prog, ∀ q : L.Query, pre q → ¬ (L.sem b_ub q).defined) ∧
    (∀ b : L.Prog, L.ProductiveOn pre b → L.DeterministicOn pre b) ∧
    (∃ (p' : L.Prog) (q₁ q₂ : L.Query) (v₁ v₂ : SemObs),
      L.ProductiveOn pre p' ∧
      pre q₁ ∧ pre q₂ ∧ v₁ ≠ v₂ ∧
      L.Produces p' q₁ v₁ ∧ L.Produces p' q₂ v₂ ∧
      (∀ (b : L.Prog),
        L.ProductiveOn pre b → L.QuerySensitiveOn pre b →
        (∀ (q : L.Query) (v : SemObs),
          pre q → (L.Produces b q v ↔ L.Produces p' q v)) ∨
        ((¬ ∃ q : L.Query, pre q ∧ L.Produces b q v₁) ∧
         L.Produces b q₁ v₂ ∧
         (∀ (q_b q_p : L.Query) (v_ov w : SemObs),
           pre q_b → pre q_p →
           L.Produces b q_b v_ov →
           L.Produces p' q_p v_ov →
           L.Produces b q_p w →
           ¬ ∃ q₃ : L.Query, pre q₃ ∧ L.Produces p' q₃ w) ∧
         (∀ (q : L.Query) (v : SemObs),
           pre q → L.Produces p q v → ¬ L.Produces p' q v) ∧
         (∀ (q : L.Query) (v : SemObs),
           pre q → L.Produces p q v → ¬ L.Produces b q v) ∧
         cci.validMultiShift
           (fun v => ∃ q : L.Query, pre q ∧ L.Produces p' q v)
           (fun v => ∃ q : L.Query, pre q ∧ L.Produces b q v))))))

/-- `Candidate 016` domain-level completeness guard (`TotalWellBehavedDomainOn`). -/
def Language.TotalWellBehavedDomainOn {SemObs : Type}
    [CanonicalConstInit SemObs]
    (L : Language SemObs) (pre : L.Query → Prop) : Prop :=
  (∀ b : L.Prog, L.ProductiveOn pre b ∧ L.DeterministicOn pre b) ∨
  (∀ p₁ p₂ : L.Prog,
    L.WellBehavedProgOn pre p₁ →
    L.WellBehavedProgOn pre p₂ →
    (∀ q : L.Query, pre q →
      ∀ v : SemObs, L.Produces p₁ q v ↔ L.Produces p₂ q v) →
    p₁ = p₂) ∨
  (∃ p₀ : L.Prog, L.WellBehavedProgOn pre p₀ ∧ ¬ L.QuerySensitiveOn pre p₀) ∨
  (∃ p₁ p₂ p₃ : L.Prog,
    L.WellBehavedProgOn pre p₁ ∧
    L.WellBehavedProgOn pre p₂ ∧
    L.WellBehavedProgOn pre p₃ ∧
    (∃ q : L.Query, ∃ v : SemObs,
      pre q ∧ L.Produces p₁ q v ∧ ¬ L.Produces p₂ q v) ∧
    (∃ q : L.Query, ∃ v : SemObs,
      pre q ∧ L.Produces p₁ q v ∧ ¬ L.Produces p₃ q v) ∧
    (∃ q : L.Query, ∃ v : SemObs,
      pre q ∧ L.Produces p₂ q v ∧ ¬ L.Produces p₃ q v))

/-- **Theorem 2A (`DeadBranchSyntacticCheckerLockout` — Rice 1953 / Cousot &
    Cousot 1977 / `PENTEST-R3-2A`):**
    For *any* language `L` and tool `tool : Tool L L_tgt`, if `p_good` and
    `p_deadBranchIllTyped` (`if false then type_error else p_good`) have
    identical dynamic `Produces` semantics on `pre`, then any syntactic static
    analyzer or compiler that accepts `p_good` and rejects `p_deadBranchIllTyped`:
    1. Violates `Tool.SemanticallyClosedOn pre tool`, and
    2. Whenever `L.WellBehavedProgOn pre p_good` holds, also `L.WellBehavedProgOn pre p_deadBranchIllTyped`
       holds, so `tool` violates universal well-behaved completeness
       `∀ p, L.WellBehavedProgOn pre p → Tool.Accepted tool p`! -/
theorem DeadBranchSyntacticCheckerLockout
    {SemObs : Type} [CanonicalConstInit SemObs]
    {L : Language SemObs} {L_tgt : Language SemObs}
    (pre : L.Query → Prop) (tool : Tool L L_tgt)
    (p_good p_deadBranchIllTyped : L.Prog)
    (h_dyn_eq : ∀ q : L.Query, pre q →
      ∀ v : SemObs, L.Produces p_good q v ↔ L.Produces p_deadBranchIllTyped q v)
    (h_prod_dead : L.ProductiveOn pre p_deadBranchIllTyped)
    (h_acc_good : Tool.Accepted tool p_good)
    (h_rej_dead : Tool.Rejected tool p_deadBranchIllTyped) :
    ¬ Tool.SemanticallyClosedOn pre tool ∧
    (L.WellBehavedProgOn pre p_good →
      L.WellBehavedProgOn pre p_deadBranchIllTyped ∧
      ¬ (∀ p : L.Prog, L.WellBehavedProgOn pre p → Tool.Accepted tool p)) := by
  refine ⟨?_, ?_⟩
  · intro h_closed
    exact h_rej_dead (h_closed p_good p_deadBranchIllTyped h_dyn_eq h_acc_good)
  · intro h_wb_good
    have h_wb_dead : L.WellBehavedProgOn pre p_deadBranchIllTyped := by
      refine ⟨h_prod_dead, ?_, ?_⟩
      · intro q hq v₁ v₂ hp₁ hp₂
        exact h_wb_good.2.1 q hq v₁ v₂
          ((h_dyn_eq q hq v₁).mpr hp₁) ((h_dyn_eq q hq v₂).mpr hp₂)
      · cases h_wb_good.2.2 with
        | inl h_qs =>
          refine Or.inl (fun h2 => ?_)
          have ⟨q₁, q₂, v₁, v₂, hq₁, hq₂, hne, hp₁, hp₂⟩ := h_qs h2
          exact ⟨q₁, q₂, v₁, v₂, hq₁, hq₂, hne,
            (h_dyn_eq q₁ hq₁ v₁).mp hp₁, (h_dyn_eq q₂ hq₂ v₂).mp hp₂⟩
        | inr h_init =>
          have ⟨hb_ub, h_all_det, p', q₁, q₂, v₁, v₂, h_prod_p',
            hq₁, hq₂, hne, hp'₁, hp'₂, h_all_b⟩ := h_init
          refine Or.inr ⟨hb_ub, h_all_det, p', q₁, q₂, v₁, v₂, h_prod_p',
            hq₁, hq₂, hne, hp'₁, hp'₂, ?_⟩
          intro b hb_prod hb_qs
          cases h_all_b b hb_prod hb_qs with
          | inl h_eq => exact Or.inl h_eq
          | inr h_sep =>
            refine Or.inr ⟨h_sep.1, h_sep.2.1, h_sep.2.2.1, ?_, ?_, h_sep.2.2.2.2.2⟩
            · intro q v hq hp_dead
              exact h_sep.2.2.2.1 q v hq ((h_dyn_eq q hq v).mpr hp_dead)
            · intro q v hq hp_dead
              exact h_sep.2.2.2.2.1 q v hq ((h_dyn_eq q hq v).mpr hp_dead)
    exact ⟨h_wb_dead, fun h_all => h_rej_dead (h_all p_deadBranchIllTyped h_wb_dead)⟩

/-- Nondeterministic pipeline AST from `PENTEST-R3-10`:
    - `.det1`: deterministically produces `q + 1`.
    - `.det2`: deterministically produces `q + 2`.
    - `.nondet12`: nondeterministically produces `q + 1` or `q + 2`.
    - `.nondet12_alt`: syntactically distinct AST (`(q + 2) ⊔ (q + 1)`) with the
      exact same semantics as `.nondet12`.
    - `.bad0`: produces `0`. -/
inductive NondetPipeProg where
  | det1
  | det2
  | nondet12
  | nondet12_alt
  | bad0
  deriving DecidableEq

abbrev L_nondet_pipe : Language Nat :=
  Language.mkSimple NondetPipeProg Nat Nat (fun p q => match p with
    | .det1         => Partial.pure (fun o => o = q + 1)
    | .det2         => Partial.pure (fun o => o = q + 2)
    | .nondet12     => Partial.pure (fun o => o = q + 1 ∨ o = q + 2)
    | .nondet12_alt => Partial.pure (fun o => o = q + 1 ∨ o = q + 2)
    | .bad0         => Partial.pure (fun o => o = 0))

/-- Stage 1 compiler pass (`stage1SymBreak`): accepts all 4 valid programs and
    refines nondeterminism by lowering `.nondet12 ↦ .det1` and
    `.nondet12_alt ↦ .det2`. -/
def stage1SymBreak : Tool L_nondet_pipe L_nondet_pipe
  | .det1         => Partial.pure .det1
  | .det2         => Partial.pure .det2
  | .nondet12     => Partial.pure .det1
  | .nondet12_alt => Partial.pure .det2
  | .bad0         => Partial.ub

/-- Stage 2 compiler pass (`stage2Filter`): accepts `.det1`, `.nondet12`, and
    `.nondet12_alt` (lowering all three to `.det1`) and rejects `.det2` and
    `.bad0`. -/
def stage2Filter : Tool L_nondet_pipe L_nondet_pipe
  | .det1         => Partial.pure .det1
  | .det2         => Partial.ub
  | .nondet12     => Partial.pure .det1
  | .nondet12_alt => Partial.pure .det1
  | .bad0         => Partial.ub

/-- **Theorem 2B (`SemanticallyClosedNonComposable` — `PENTEST-R3-10`):**
    1. `stage1SymBreak` satisfies `Tool.SemanticallyClosedOn` and
       `ProductiveCompiles` on all accepted programs,
    2. `stage2Filter` satisfies `Tool.SemanticallyClosedOn` and
       `ProductiveCompiles` on all accepted programs,
    3. `Tool.ChainedSuiteAccepted stage1SymBreak stage2Filter [.det1, .nondet12]`
       holds,
    4. Yet their vertical composition `Tool.comp stage1SymBreak stage2Filter`
       **violates `Tool.SemanticallyClosedOn`** (it accepts `.nondet12` and
       rejects the semantically identical `.nondet12_alt`)! -/
theorem SemanticallyClosedNonComposable :
    let pre := fun q : Nat => q < 100
    Tool.SemanticallyClosedOn pre stage1SymBreak ∧
    (∀ p, ∀ h : (stage1SymBreak p).defined,
      ProductiveCompiles L_nondet_pipe L_nondet_pipe
        (BehaviorCodec.id L_nondet_pipe) p ((stage1SymBreak p).val h)) ∧
    Tool.SemanticallyClosedOn pre stage2Filter ∧
    (∀ p, ∀ h : (stage2Filter p).defined,
      ProductiveCompiles L_nondet_pipe L_nondet_pipe
        (BehaviorCodec.id L_nondet_pipe) p ((stage2Filter p).val h)) ∧
    Tool.ChainedSuiteAccepted stage1SymBreak stage2Filter [.det1, .nondet12] ∧
    ¬ Tool.SemanticallyClosedOn pre (Tool.comp stage1SymBreak stage2Filter) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩, ?_⟩
  · intro p₁ p₂ h_eq h_acc₁
    cases p₂ with
    | det1 | det2 | nondet12 | nondet12_alt => exact trivial
    | bad0 =>
      cases p₁ with
      | det1 =>
        have ⟨_, _, ho, hv⟩ := (h_eq 0 (by decide) 1).mp ⟨trivial, 1, rfl, rfl⟩
        have h01 : (0 : Nat) = 1 := Eq.trans ho.symm hv; cases h01
      | det2 =>
        have ⟨_, _, ho, hv⟩ := (h_eq 0 (by decide) 2).mp ⟨trivial, 2, rfl, rfl⟩
        have h02 : (0 : Nat) = 2 := Eq.trans ho.symm hv; cases h02
      | nondet12 | nondet12_alt =>
        have ⟨_, _, ho, hv⟩ :=
          (h_eq 0 (by decide) 1).mp ⟨trivial, 1, Or.inl rfl, rfl⟩
        have h01 : (0 : Nat) = 1 := Eq.trans ho.symm hv; cases h01
      | bad0 => exact False.elim h_acc₁
  · intro p h
    cases p with
    | det1 => exact ProductiveCompiles.refl L_nondet_pipe .det1
    | det2 => exact ProductiveCompiles.refl L_nondet_pipe .det2
    | nondet12 =>
      exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, Or.inl ho⟩⟩,
        fun q _ => ⟨trivial, q + 1, rfl⟩⟩
    | nondet12_alt =>
      exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, Or.inr ho⟩⟩,
        fun q _ => ⟨trivial, q + 2, rfl⟩⟩
    | bad0 => exact False.elim h
  · intro p₁ p₂ h_eq h_acc₁
    cases p₂ with
    | det1 | nondet12 | nondet12_alt => exact trivial
    | det2 =>
      cases p₁ with
      | det1 =>
        have ⟨_, _, ho, hv⟩ := (h_eq 0 (by decide) 1).mp ⟨trivial, 1, rfl, rfl⟩
        have h21 : (2 : Nat) = 1 := Eq.trans ho.symm hv; cases h21
      | det2 => exact False.elim h_acc₁
      | nondet12 | nondet12_alt =>
        have ⟨_, _, ho, hv⟩ :=
          (h_eq 0 (by decide) 1).mp ⟨trivial, 1, Or.inl rfl, rfl⟩
        have h21 : (2 : Nat) = 1 := Eq.trans ho.symm hv; cases h21
      | bad0 => exact False.elim h_acc₁
    | bad0 =>
      cases p₁ with
      | det1 =>
        have ⟨_, _, ho, hv⟩ := (h_eq 0 (by decide) 1).mp ⟨trivial, 1, rfl, rfl⟩
        have h01 : (0 : Nat) = 1 := Eq.trans ho.symm hv; cases h01
      | det2 => exact False.elim h_acc₁
      | nondet12 | nondet12_alt =>
        have ⟨_, _, ho, hv⟩ :=
          (h_eq 0 (by decide) 1).mp ⟨trivial, 1, Or.inl rfl, rfl⟩
        have h01 : (0 : Nat) = 1 := Eq.trans ho.symm hv; cases h01
      | bad0 => exact False.elim h_acc₁
  · intro p h
    cases p with
    | det1 => exact ProductiveCompiles.refl L_nondet_pipe .det1
    | det2 => exact False.elim h
    | nondet12 | nondet12_alt =>
      exact ⟨fun q _ => ⟨trivial, fun o ho => ⟨o, rfl, Or.inl ho⟩⟩,
        fun q _ => ⟨trivial, q + 1, rfl⟩⟩
    | bad0 => exact False.elim h
  · intro h_closed_comp
    have h_eq : ∀ q : Nat, q < 100 → ∀ v : Nat,
        L_nondet_pipe.Produces .nondet12 q v ↔
        L_nondet_pipe.Produces .nondet12_alt q v :=
      fun _ _ _ => Iff.rfl
    have h_acc_alt : Tool.Accepted (Tool.comp stage1SymBreak stage2Filter) .nondet12_alt :=
      h_closed_comp .nondet12 .nondet12_alt h_eq ⟨trivial, trivial⟩
    exact h_acc_alt.2

/-- 4-program spike suite from `PENTEST-R4-7`:
    - `.addOne`: `q + 1`
    - `.addTwo`: `q + 2`
    - `.buggySpike`: `if q = 0 then 1 else 0` (query-sensitive, deterministic,
      total, yet violates `v = q + 1` at every `q ≥ 1`!)
    - `.ubCrash`: `Partial.ub`. -/
inductive SpikeSuiteProg where
  | addOne
  | addTwo
  | buggySpike
  | ubCrash
  deriving DecidableEq

abbrev L_spike_suite : Language Nat :=
  Language.mkSimple SpikeSuiteProg Nat Nat (fun p q => match p with
    | .addOne     => Partial.pure (fun o => o = q + 1)
    | .addTwo     => Partial.pure (fun o => o = q + 2)
    | .buggySpike => Partial.pure (fun o => o = if q = 0 then 1 else 0)
    | .ubCrash    => Partial.ub)

/-- **Theorem 2C (`UnlabeledIntrinsicWellBehavedImpossibility` — `PENTEST-R4-7`):**
    1. Any intrinsic predicate `P_intr` on `Language` that holds whenever a
       program is productive, deterministic, and query-sensitive (`WellBehavedProgOn`)
       **must accept `.buggySpike`** (`if q = 0 then 1 else 0`), even though
       `.buggySpike` violates both `v = q + 1` and `v = q + 2` at every `q ≥ 1`!
    2. On `L_spike_suite`, `TotalWellBehavedDomainOn` holds, so requiring a tool
       to accept all `WellBehavedProgOn` programs forces acceptance of the
       unverified `.buggySpike` and locks out any honest verifier that rejects
       `.buggySpike`! -/
theorem UnlabeledIntrinsicWellBehavedImpossibility :
    let pre := fun q : Nat => q < 100
    L_spike_suite.WellBehavedProgOn pre .buggySpike ∧
    L_spike_suite.TotalWellBehavedDomainOn pre ∧
    L_spike_suite.ViolatesSpine pre (fun q v => v = q + 1) .buggySpike ∧
    L_spike_suite.ViolatesSpine pre (fun q v => v = q + 2) .buggySpike := by
  dsimp only
  have h_wb_1 : L_spike_suite.WellBehavedProgOn (fun q => q < 100) .addOne :=
    ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)⟩
  have h_wb_2 : L_spike_suite.WellBehavedProgOn (fun q => q < 100) .addTwo :=
    ⟨fun q _ => ⟨trivial, q + 2, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 2, 3, by decide, by decide, by decide,
       ⟨trivial, 2, rfl, rfl⟩, ⟨trivial, 3, rfl, rfl⟩⟩)⟩
  have h_wb_spike : L_spike_suite.WellBehavedProgOn (fun q => q < 100) .buggySpike :=
    ⟨fun q _ => ⟨trivial, if q = 0 then 1 else 0, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 0, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 0, rfl, rfl⟩⟩)⟩
  have h_tot : L_spike_suite.TotalWellBehavedDomainOn (fun q => q < 100) := by
    refine Or.inr (Or.inr (Or.inr ⟨.addOne, .addTwo, .buggySpike,
      h_wb_1, h_wb_2, h_wb_spike,
      ⟨0, 1, by decide, ⟨trivial, 1, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h21 : 2 = 1 := Eq.trans ho.symm hv; cases h21⟩,
      ⟨1, 2, by decide, ⟨trivial, 2, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h02 : 0 = 2 := Eq.trans ho.symm hv; cases h02⟩,
      ⟨0, 2, by decide, ⟨trivial, 2, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h12 : 1 = 2 := Eq.trans ho.symm hv; cases h12⟩⟩))
  exact ⟨h_wb_spike, h_tot,
    ⟨1, by decide, trivial, 0, rfl, by decide⟩,
    ⟨0, by decide, trivial, 1, rfl, by decide⟩⟩

/-!
## 3. The Crate-Monotonicity Law (`CrateMonotonicityLaw`) and the Non-Monotonicity
   of AST-Global Quantifiers (`PENTEST-R4-1A/B/C`, `PENTEST-R4-3A/B`)

We define **Crate Extension** (`CrateExtension L L'`) and **Crate Monotonicity
(Local Modularity)** (`CrateMonotonicProgJudgment`). A semantic classification
of a function `p` must depend only on `p`'s own semantics and specification,
never on which other unrelated functions happen to reside in `L.Prog`.

We then prove that `Candidate 016`'s `Language.WellBehavedProgOn` and
`Language.TotalWellBehavedDomainOn` **violate Crate Monotonicity in both
directions**:
1. **Adding an unrelated function promotes a buggy constant function from
   ill-behaved to well-behaved (`PENTEST-R4-1A/B`):**
   - Starting from the 2-program sub-crate `L_sub_bad42` (`{.badConst42, .ubCrash}`),
     `.badConst42` ($q \mapsto 42$) is ill-behaved (`¬ WellBehavedProgOn`).
     Adding the unrelated function `.add1` ($q \mapsto q + 1$) to form
     `L_add1_bad42_ub` flips `.badConst42` to **well-behaved**!
   - Starting from the 2-program sub-crate `L_sub_bad0` (`{.bad0, .ubCrash}`),
     `.bad0` ($q \mapsto 0$) is ill-behaved. Adding `.add27` ($q \mapsto q + 27$)
     and `.add77` ($q \mapsto q + 77$) to form `L_add27_add77_bad0_ub` flips
     `.bad0` to **well-behaved**!
2. **Adding an unrelated honest function demotes an honest constant initializer
   from well-behaved to ill-behaved (`PENTEST-R4-1C`):**
   - In the 3-program honest crate `L_honest_crate_add1` (`{.add1, .initZero, .oobPanic}`),
     `.initZero` ($q \mapsto 0$) is **well-behaved** (`WellBehavedProgOn`).
     Adding the unrelated honest function `.add20` ($q \mapsto q + 20$, which
     produces `26` at `q = 6 < 16`) to form `L_honest_crate_add1_add20` flips
     `.initZero` from **well-behaved to ill-behaved**!
3. **Adding a 3rd well-typed function to a 2-function crate flips a syntactic
   type checker from valid to locked out (`PENTEST-R4-3A`):**
   - In `L_typed2` (2 well-typed functions `.wellTypedAddOne` and
     `.wellTypedAddTwo` plus `.deadBranchIllTyped` and `.liveNullDeref`),
     `TotalWellBehavedDomainOn` is **false**. Adding `.wellTypedAddThree`
     ($q \mapsto q + 3$) to form `L_typed3` makes `TotalWellBehavedDomainOn`
     **true**, forcing every compiler to accept `.deadBranchIllTyped`!
-/

/-- A crate extension `L ≼_crate L'` embeds `L.Prog` injectively into `L'.Prog`
    while preserving `Query`, `Out`, `obs`, `dom`, and per-program semantics `sem`. -/
structure CrateExtension {SemObs : Type} (L L' : Language SemObs) where
  embedProg    : L.Prog → L'.Prog
  embed_inj    : ∀ p₁ p₂, embedProg p₁ = embedProg p₂ → p₁ = p₂
  query_eq     : L.Query = L'.Query
  out_eq       : L.Out = L'.Out
  sem_preserve : ∀ (p : L.Prog) (q : L.Query) (v : SemObs),
    L.Produces p q v ↔ L'.Produces (embedProg p) ( cast query_eq q) v
  safe_preserve : ∀ (p : L.Prog) (q : L.Query),
    L.SafeAt p q ↔ L'.SafeAt (embedProg p) (cast query_eq q)

/-- Same-query/outcome specialization of `CrateExtension` (`L.Query = L'.Query`
    and `L.Out = L'.Out` definitionally). -/
structure SameDomainCrateExtension {SemObs : Type} (L L' : Language SemObs)
    (hQ : L.Query = L'.Query := by rfl)
    (hO : L.Out = L'.Out := by rfl) where
  embedProg : L.Prog → L'.Prog
  embed_inj : ∀ p₁ p₂, embedProg p₁ = embedProg p₂ → p₁ = p₂
  sem_eq    : ∀ p : L.Prog,
    L'.sem (embedProg p) = cast (by rw [hQ, hO]) (L.sem p)

/-- **Definition (`CrateMonotonicProgJudgment`):**
    A program-level semantic classification `J : ∀ (L : Language SemObs),
    (L.Query → Prop) → L.Prog → Prop` is *crate-monotonic* if adding unrelated
    functions to a crate never alters the classification of existing functions. -/
def CrateMonotonicProgJudgment {SemObs : Type}
    (J : ∀ (L : Language SemObs), (L.Query → Prop) → L.Prog → Prop) : Prop :=
  ∀ (L L' : Language SemObs) (pre : L.Query → Prop)
    (hQ : L.Query = L'.Query) (hO : L.Out = L'.Out)
    (ext : SameDomainCrateExtension L L' hQ hO) (p : L.Prog),
    J L pre p ↔ J L' (cast (by rw [hQ]) pre) (ext.embedProg p)

/-- Sub-crate `L_sub_bad42` containing only `.badConst42` (`42`) and `.ubCrash`. -/
inductive SubBad42Prog where
  | badConst42
  | ubCrash
  deriving DecidableEq

abbrev L_sub_bad42 : Language Nat :=
  Language.mkSimple SubBad42Prog Nat Nat (fun p _ => match p with
    | .badConst42 => Partial.pure (fun o => o = 42)
    | .ubCrash    => Partial.ub)

/-- Extended crate `L_add1_bad42_ub` (`PENTEST-R4-1B`) adding `.add1` (`q + 1`). -/
inductive Add1Bad42UbProg where
  | add1
  | badConst42
  | ubCrash
  deriving DecidableEq

abbrev L_add1_bad42_ub : Language Nat :=
  Language.mkSimple Add1Bad42UbProg Nat Nat (fun p q => match p with
    | .add1       => Partial.pure (fun o => o = q + 1)
    | .badConst42 => Partial.pure (fun o => o = 42)
    | .ubCrash    => Partial.ub)

/-- Crate extension embedding `L_sub_bad42` into `L_add1_bad42_ub`. -/
def ext_subBad42_to_add1Bad42 :
    SameDomainCrateExtension L_sub_bad42 L_add1_bad42_ub where
  embedProg
    | .badConst42 => .badConst42
    | .ubCrash    => .ubCrash
  embed_inj p₁ p₂ h := by cases p₁ <;> cases p₂ <;> first | rfl | cases h
  sem_eq p := by cases p <;> rfl

/-- 3-program honest crate `L_honest_crate_add1` (`{.add1, .initZero, .oobPanic}`). -/
inductive HonestCrateAdd1Prog where
  | add1
  | initZero
  | oobPanic
  deriving DecidableEq

abbrev L_honest_crate_add1 : Language Nat :=
  Language.mkSimple HonestCrateAdd1Prog Nat Nat (fun p q => match p with
    | .add1     => Partial.pure (fun o => o = q + 1)
    | .initZero => Partial.pure (fun o => o = 0)
    | .oobPanic => Partial.ub)

/-- Extended 4-program honest crate `L_honest_crate_add1_add20` (`PENTEST-R4-1C`)
    adding `.add20` (`q + 20`). -/
inductive HonestCrateAdd1Add20Prog where
  | add1
  | add20
  | initZero
  | oobPanic
  deriving DecidableEq

abbrev L_honest_crate_add1_add20 : Language Nat :=
  Language.mkSimple HonestCrateAdd1Add20Prog Nat Nat (fun p q => match p with
    | .add1     => Partial.pure (fun o => o = q + 1)
    | .add20    => Partial.pure (fun o => o = q + 20)
    | .initZero => Partial.pure (fun o => o = 0)
    | .oobPanic => Partial.ub)

/-- Crate extension embedding `L_honest_crate_add1` into `L_honest_crate_add1_add20`. -/
def ext_honestAdd1_to_add1Add20 :
    SameDomainCrateExtension L_honest_crate_add1 L_honest_crate_add1_add20 where
  embedProg
    | .add1     => .add1
    | .initZero => .initZero
    | .oobPanic => .oobPanic
  embed_inj p₁ p₂ h := by cases p₁ <;> cases p₂ <;> first | rfl | cases h
  sem_eq p := by cases p <;> rfl

/-- 4-program crate `L_add27_add77_bad0_ub` (`PENTEST-R4-1A`) where `.add27`
    (`q + 27`) and `.add77` (`q + 77`) avoid magic numbers `1` and `26` and
    their overlap escapes `q < 100`. -/
inductive Add27Add77Bad0UbProg where
  | add27
  | add77
  | bad0
  | ubCrash
  deriving DecidableEq

abbrev L_add27_add77_bad0_ub : Language Nat :=
  Language.mkSimple Add27Add77Bad0UbProg Nat Nat (fun p q => match p with
    | .add27   => Partial.pure (fun o => o = q + 27)
    | .add77   => Partial.pure (fun o => o = q + 77)
    | .bad0    => Partial.pure (fun o => o = 0)
    | .ubCrash => Partial.ub)

/-- **Theorem 3A (`WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections` —
    `PENTEST-R4-1A/B/C`):**
    `Language.WellBehavedProgOn` violates `CrateMonotonicProgJudgment` in **both**
    directions:
    1. **False-Positive Promotion (`IllBehaved ↦ WellBehaved`):**
       In `L_sub_bad42`, `.badConst42` is **not** `WellBehavedProgOn`, yet under
       the crate extension `ext_subBad42_to_add1Bad42` (adding `.add1`),
       `.badConst42` **becomes `WellBehavedProgOn`**!
    2. **Shifted-Offset False-Positive (`PENTEST-R4-1A`):**
       In `L_add27_add77_bad0_ub`, the buggy zero-returning function `.bad0`
       satisfies `WellBehavedProgOn (fun q => q < 100)`.
    3. **False-Negative Demotion (`WellBehaved ↦ IllBehaved`, `PENTEST-R4-1C`):**
       In `L_honest_crate_add1`, the legitimate constant initializer `.initZero`
       **is** `WellBehavedProgOn (fun q => q < 16)`, yet under the crate
       extension `ext_honestAdd1_to_add1Add20` (adding the honest function
       `.add20`), `.initZero` **ceases to be `WellBehavedProgOn`**!
    4. Consequently, `¬ CrateMonotonicProgJudgment (fun L pre p => L.WellBehavedProgOn pre p)`. -/
theorem WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections :
    ¬ L_sub_bad42.WellBehavedProgOn (fun q => q < 100) .badConst42 ∧
    L_add1_bad42_ub.WellBehavedProgOn (fun q => q < 100)
      (ext_subBad42_to_add1Bad42.embedProg .badConst42) ∧
    L_add27_add77_bad0_ub.WellBehavedProgOn (fun q => q < 100) .bad0 ∧
    L_honest_crate_add1.WellBehavedProgOn (fun q => q < 16) .initZero ∧
    ¬ L_honest_crate_add1_add20.WellBehavedProgOn (fun q => q < 16)
      (ext_honestAdd1_to_add1Add20.embedProg .initZero) ∧
    ¬ CrateMonotonicProgJudgment (fun (L : Language Nat) pre p =>
        L.WellBehavedProgOn pre p) := by
  have h_not_sub42 :
      ¬ L_sub_bad42.WellBehavedProgOn (fun q => q < 100) .badConst42 := by
    intro ⟨_, _, h_or⟩
    cases h_or with
    | inl h_qs =>
      have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
        h_qs ⟨0, 1, by decide, by decide, by decide⟩
      exact hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂))
    | inr h_init =>
      have ⟨_, _, p', _, _, _, _, h_prod_p', _, _, hne,
        ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩, _⟩ := h_init
      cases p' with
      | badConst42 =>
        exact hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂))
      | ubCrash =>
        exact (h_prod_p' 0 (by decide)).1
  have h_wb_ext42 :
      L_add1_bad42_ub.WellBehavedProgOn (fun q => q < 100) .badConst42 := by
    refine ⟨fun _ _ => ⟨trivial, 42, rfl⟩,
      fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
        Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
      Or.inr ⟨⟨.ubCrash, fun _ _ h => h⟩, ?_,
        .add1, 0, 1, 1, 2,
        fun q _ => ⟨trivial, q + 1, rfl⟩,
        by decide, by decide, by decide,
        ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩, ?_⟩⟩
    · intro b h_prod
      cases b with
      | add1 | badConst42 =>
        exact fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
          Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)
      | ubCrash => exact False.elim (h_prod 0 (by decide)).1
    · intro b h_prod h_qs
      cases b with
      | add1 => exact Or.inl (fun _ _ _ => Iff.rfl)
      | badConst42 =>
        have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
          h_qs ⟨0, 1, by decide, by decide, by decide⟩
        exact False.elim (hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)))
      | ubCrash => exact False.elim (h_prod 0 (by decide)).1
  have h_wb_bad0 :
      L_add27_add77_bad0_ub.WellBehavedProgOn (fun q => q < 100) .bad0 := by
    refine ⟨fun _ _ => ⟨trivial, 0, rfl⟩,
      fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
        Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
      Or.inr ⟨⟨.ubCrash, fun _ _ h => h⟩, ?_,
        .add27, 0, 50, 27, 77,
        fun q _ => ⟨trivial, q + 27, rfl⟩,
        by decide, by decide, by decide,
        ⟨trivial, 27, rfl, rfl⟩, ⟨trivial, 77, rfl, rfl⟩, ?_⟩⟩
    · intro b h_prod
      cases b with
      | add27 | add77 | bad0 =>
        exact fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
          Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)
      | ubCrash => exact False.elim (h_prod 0 (by decide)).1
    · intro b h_prod h_qs
      cases b with
      | add27 => exact Or.inl (fun _ _ _ => Iff.rfl)
      | add77 =>
        refine Or.inr ⟨?_, ⟨trivial, 77, rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro ⟨q, _, _, o, ho, hv⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q o ho hv
          have h_eq : q + 77 = 27 := Eq.trans ho.symm hv
          omega
        · intro (q_b : Nat) (q_p : Nat) (v_ov : Nat) (w : Nat) hqb hqp
            ⟨_, (o_b : Nat), ho_b, hv_b⟩ ⟨_, (o_p : Nat), ho_p, hv_p⟩
            ⟨_, (o_w : Nat), ho_w, hv_w⟩ ⟨(q₃ : Nat), hq₃, _, (o₃ : Nat), ho₃, hv₃⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple, Partial.pure] at *
          omega
        · intro q v _ ⟨_, _, ho₀, hv₀⟩ ⟨_, _, ho₁, hv₁⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q v ho₀ hv₀ ho₁ hv₁
          have h0 : v = 0 := Eq.trans hv₀.symm ho₀
          have h1 : v = q + 27 := Eq.trans hv₁.symm ho₁
          omega
        · intro q v _ ⟨_, _, ho₀, hv₀⟩ ⟨_, _, ho₁, hv₁⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q v ho₀ hv₀ ho₁ hv₁
          have h0 : v = 0 := Eq.trans hv₀.symm ho₀
          have h1 : v = q + 77 := Eq.trans hv₁.symm ho₁
          omega
        · intro ⟨q, _, _, o, ho, hv⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q o ho hv
          have h_eq : q + 27 = 1 := Eq.trans ho.symm hv
          omega
        · intro ⟨q, _, _, o, ho, hv⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q o ho hv
          have h_eq : q + 27 = 26 := Eq.trans ho.symm hv
          omega
        · intro ⟨q, _, _, o, ho, hv⟩
          dsimp [L_add27_add77_bad0_ub, Language.mkSimple] at q o ho hv
          have h_eq : q + 77 = 1 := Eq.trans ho.symm hv
          omega
      | bad0 =>
        have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
          h_qs ⟨0, 1, by decide, by decide, by decide⟩
        exact False.elim (hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)))
      | ubCrash => exact False.elim (h_prod 0 (by decide)).1
  have h_wb_init_small :
      L_honest_crate_add1.WellBehavedProgOn (fun q => q < 16) .initZero := by
    refine ⟨fun _ _ => ⟨trivial, 0, rfl⟩,
      fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
        Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
      Or.inr ⟨⟨.oobPanic, fun _ _ h => h⟩, ?_,
        .add1, 0, 1, 1, 2,
        fun q _ => ⟨trivial, q + 1, rfl⟩,
        by decide, by decide, by decide,
        ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩, ?_⟩⟩
    · intro b h_prod
      cases b with
      | add1 | initZero =>
        exact fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
          Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)
      | oobPanic => exact False.elim (h_prod 0 (by decide)).1
    · intro b h_prod h_qs
      cases b with
      | add1 => exact Or.inl (fun _ _ _ => Iff.rfl)
      | initZero =>
        have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
          h_qs ⟨0, 1, by decide, by decide, by decide⟩
        exact False.elim (hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂)))
      | oobPanic => exact False.elim (h_prod 0 (by decide)).1
  have h_not_init_ext :
      ¬ L_honest_crate_add1_add20.WellBehavedProgOn (fun q => q < 16) .initZero := by
    intro ⟨_, _, h_or⟩
    cases h_or with
    | inl h_qs =>
      have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
        h_qs ⟨0, 1, by decide, by decide, by decide⟩
      exact hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂))
    | inr h_init =>
      have ⟨_, _, p', _, _, _, _, h_prod_p', _, _, hne12,
        ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩, h_all_b⟩ := h_init
      have h_qs_1 : L_honest_crate_add1_add20.QuerySensitiveOn (fun q => q < 16) .add1 :=
        fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
          ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩
      have h_qs_20 : L_honest_crate_add1_add20.QuerySensitiveOn (fun q => q < 16) .add20 :=
        fun _ => ⟨0, 1, 20, 21, by decide, by decide, by decide,
          ⟨trivial, 20, rfl, rfl⟩, ⟨trivial, 21, rfl, rfl⟩⟩
      cases p' with
      | add1 =>
        cases h_all_b .add20 (fun q _ => ⟨trivial, q + 20, rfl⟩) h_qs_20 with
        | inl h_eq =>
          have ⟨_, _, ho, hv⟩ := (h_eq 0 1 (by decide)).mpr ⟨trivial, 1, rfl, rfl⟩
          have h20_1 : (20 : Nat) = 1 := Eq.trans ho.symm hv; cases h20_1
        | inr h_no =>
          exact h_no.2.2.2.2.2.1 ⟨0, by decide, trivial, 1, rfl, rfl⟩
      | add20 =>
        cases h_all_b .add1 (fun q _ => ⟨trivial, q + 1, rfl⟩) h_qs_1 with
        | inl h_eq =>
          have ⟨_, _, ho, hv⟩ := (h_eq 0 20 (by decide)).mpr ⟨trivial, 20, rfl, rfl⟩
          have h1_20 : (1 : Nat) = 20 := Eq.trans ho.symm hv; cases h1_20
        | inr h_no =>
          exact h_no.2.2.2.2.2.2.1 ⟨6, by decide, trivial, 26, rfl, rfl⟩
      | initZero =>
        exact hne12 (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂))
      | oobPanic =>
        exact (h_prod_p' 0 (by decide)).1
  refine ⟨h_not_sub42, h_wb_ext42, h_wb_bad0, h_wb_init_small, h_not_init_ext, ?_⟩
  intro h_mono
  have h_iff := h_mono L_sub_bad42 L_add1_bad42_ub (fun q => q < 100) rfl rfl
    ext_subBad42_to_add1Bad42 .badConst42
  exact h_not_sub42 (h_iff.mpr h_wb_ext42)

/-- 2-function typed language `L_typed2` (where `TotalWellBehavedDomainOn` is
    false, so syntactic type-checking was permitted in `Candidate 016`). -/
inductive Typed2Prog where
  | wellTypedAddOne
  | wellTypedAddTwo
  | deadBranchIllTyped
  | liveNullDeref
  deriving DecidableEq

abbrev L_typed2 : Language Nat :=
  Language.mkSimple Typed2Prog Nat Nat (fun p q => match p with
    | .wellTypedAddOne    => Partial.pure (fun o => o = q + 1)
    | .wellTypedAddTwo    => Partial.pure (fun o => o = q + 2)
    | .deadBranchIllTyped => Partial.pure (fun o => o = q + 1)
    | .liveNullDeref      => Partial.ub)

/-- 3-function typed language `L_typed3` (`PENTEST-R4-3A`, adding `.wellTypedAddThree`). -/
inductive Typed3Prog where
  | wellTypedAddOne
  | wellTypedAddTwo
  | wellTypedAddThree
  | deadBranchIllTyped
  | liveNullDeref
  deriving DecidableEq

abbrev L_typed3 : Language Nat :=
  Language.mkSimple Typed3Prog Nat Nat (fun p q => match p with
    | .wellTypedAddOne    => Partial.pure (fun o => o = q + 1)
    | .wellTypedAddTwo    => Partial.pure (fun o => o = q + 2)
    | .wellTypedAddThree  => Partial.pure (fun o => o = q + 3)
    | .deadBranchIllTyped => Partial.pure (fun o => o = q + 1)
    | .liveNullDeref      => Partial.ub)

/-- Honest syntactic type-checking compiler on `L_typed3`. -/
def honestSyntacticTypeCompiler3 : Tool L_typed3 L_typed3
  | .wellTypedAddOne    => Partial.pure .wellTypedAddOne
  | .wellTypedAddTwo    => Partial.pure .wellTypedAddTwo
  | .wellTypedAddThree  => Partial.pure .wellTypedAddThree
  | .deadBranchIllTyped => Partial.ub
  | .liveNullDeref      => Partial.ub

/-- Crate extension embedding `L_typed2` into `L_typed3`. -/
def ext_typed2_to_typed3 : SameDomainCrateExtension L_typed2 L_typed3 where
  embedProg
    | .wellTypedAddOne    => .wellTypedAddOne
    | .wellTypedAddTwo    => .wellTypedAddTwo
    | .deadBranchIllTyped => .deadBranchIllTyped
    | .liveNullDeref      => .liveNullDeref
  embed_inj p₁ p₂ h := by cases p₁ <;> cases p₂ <;> first | rfl | cases h
  sem_eq p := by cases p <;> rfl

/-- Helper lemma: on `L_typed2`, every `WellBehavedProgOn` program is either
    `.wellTypedAddOne`, `.deadBranchIllTyped` (both `q + 1`), or `.wellTypedAddTwo`
    (`q + 2`), so there are only 2 distinct behaviors and no constant initializer! -/
theorem TotalWellBehavedDomainOn_Typed2_False_Typed3_True :
    ¬ L_typed2.TotalWellBehavedDomainOn (fun q => q < 100) ∧
    L_typed3.TotalWellBehavedDomainOn (fun q => q < 100) ∧
    L_typed3.WellBehavedProgOn (fun q => q < 100) .deadBranchIllTyped ∧
    Tool.Rejected honestSyntacticTypeCompiler3 .deadBranchIllTyped := by
  have h_wb2_1 : L_typed2.WellBehavedProgOn (fun q => q < 100) .wellTypedAddOne :=
    ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)⟩
  have h_wb2_dead : L_typed2.WellBehavedProgOn (fun q => q < 100) .deadBranchIllTyped :=
    ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)⟩
  have h_not_tot2 : ¬ L_typed2.TotalWellBehavedDomainOn (fun q => q < 100) := by
    intro h_tot
    cases h_tot with
    | inl h_all_prod =>
      exact ((h_all_prod .liveNullDeref).1 0 (by decide)).1
    | inr h_rest =>
      cases h_rest with
      | inl h_uniq =>
        have h_eq := h_uniq .wellTypedAddOne .deadBranchIllTyped h_wb2_1 h_wb2_dead
          (fun _ _ _ => Iff.rfl)
        cases h_eq
      | inr h_rest2 =>
        cases h_rest2 with
        | inl h_const =>
          have ⟨p₀, h_wb₀, h_not_qs⟩ := h_const
          cases p₀ with
          | wellTypedAddOne | deadBranchIllTyped =>
            exact h_not_qs (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
              ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)
          | wellTypedAddTwo =>
            exact h_not_qs (fun _ => ⟨0, 1, 2, 3, by decide, by decide, by decide,
              ⟨trivial, 2, rfl, rfl⟩, ⟨trivial, 3, rfl, rfl⟩⟩)
          | liveNullDeref =>
            exact (h_wb₀.1 0 (by decide)).1
        | inr h_three =>
          have ⟨p₁, p₂, p₃, h₁, h₂, h₃,
            ⟨q₁₂, v₁₂, _, hp₁₂, hnot₁₂⟩,
            ⟨q₁₃, v₁₃, _, hp₁₃, hnot₁₃⟩,
            ⟨q₂₃, v₂₃, _, hp₂₃, hnot₂₃⟩⟩ := h_three
          -- Each of p₁, p₂, p₃ cannot be .liveNullDeref, so at least two share
          -- the same semantics (`q + 1` or `q + 2`), contradicting pairwise separation!
          cases p₁ with
          | liveNullDeref => exact (h₁.1 0 (by decide)).1
          | wellTypedAddOne | deadBranchIllTyped =>
            cases p₂ with
            | liveNullDeref => exact (h₂.1 0 (by decide)).1
            | wellTypedAddOne | deadBranchIllTyped =>
              exact hnot₁₂ hp₁₂
            | wellTypedAddTwo =>
              cases p₃ with
              | liveNullDeref => exact (h₃.1 0 (by decide)).1
              | wellTypedAddOne | deadBranchIllTyped => exact hnot₁₃ hp₁₃
              | wellTypedAddTwo => exact hnot₂₃ hp₂₃
          | wellTypedAddTwo =>
            cases p₂ with
            | liveNullDeref => exact (h₂.1 0 (by decide)).1
            | wellTypedAddTwo => exact hnot₁₂ hp₁₂
            | wellTypedAddOne | deadBranchIllTyped =>
              cases p₃ with
              | liveNullDeref => exact (h₃.1 0 (by decide)).1
              | wellTypedAddOne | deadBranchIllTyped => exact hnot₂₃ hp₂₃
              | wellTypedAddTwo => exact hnot₁₃ hp₁₃
  have h_wb3_1 : L_typed3.WellBehavedProgOn (fun q => q < 100) .wellTypedAddOne :=
    ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)⟩
  have h_wb3_2 : L_typed3.WellBehavedProgOn (fun q => q < 100) .wellTypedAddTwo :=
    ⟨fun q _ => ⟨trivial, q + 2, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 2, 3, by decide, by decide, by decide,
       ⟨trivial, 2, rfl, rfl⟩, ⟨trivial, 3, rfl, rfl⟩⟩)⟩
  have h_wb3_3 : L_typed3.WellBehavedProgOn (fun q => q < 100) .wellTypedAddThree :=
    ⟨fun q _ => ⟨trivial, q + 3, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 3, 4, by decide, by decide, by decide,
       ⟨trivial, 3, rfl, rfl⟩, ⟨trivial, 4, rfl, rfl⟩⟩)⟩
  have h_wb3_dead : L_typed3.WellBehavedProgOn (fun q => q < 100) .deadBranchIllTyped :=
    ⟨fun q _ => ⟨trivial, q + 1, rfl⟩,
     fun _ _ _ _ ⟨_, _, ho₁, hv₁⟩ ⟨_, _, ho₂, hv₂⟩ =>
       Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂),
     Or.inl (fun _ => ⟨0, 1, 1, 2, by decide, by decide, by decide,
       ⟨trivial, 1, rfl, rfl⟩, ⟨trivial, 2, rfl, rfl⟩⟩)⟩
  have h_tot3 : L_typed3.TotalWellBehavedDomainOn (fun q => q < 100) :=
    Or.inr (Or.inr (Or.inr ⟨.wellTypedAddOne, .wellTypedAddTwo, .wellTypedAddThree,
      h_wb3_1, h_wb3_2, h_wb3_3,
      ⟨0, 1, by decide, ⟨trivial, 1, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h21 : 2 = 1 := Eq.trans ho.symm hv; cases h21⟩,
      ⟨0, 1, by decide, ⟨trivial, 1, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h31 : 3 = 1 := Eq.trans ho.symm hv; cases h31⟩,
      ⟨0, 2, by decide, ⟨trivial, 2, rfl, rfl⟩, fun ⟨_, _, ho, hv⟩ => by
        have h32 : 3 = 2 := Eq.trans ho.symm hv; cases h32⟩⟩))
  exact ⟨h_not_tot2, h_tot3, h_wb3_dead, fun h => h⟩

/-!
## 4. The Positive Characterization Theorem
   (`ExplicitSubdomainAndIndexedSpecCharacterization`)

We now establish the clean, crate-monotonic, vertically composable resolution
that simultaneously eliminates **both** Category A1 Bypasses and Category A2
Lockouts:
1. **Explicit Syntactic Sub-Domain (`AcceptedDom : L.Prog → Prop`):**
   Static analyzers, type checkers, borrow checkers, and partial compilers
   declare their syntactic domain of accepted programs `AcceptedDom` (e.g.
   `WellTyped`), rather than claiming to accept all dynamically well-behaved
   ASTs (`SemanticallyClosedOn` / `WellBehavedProgOn`).
2. **Extrinsic Indexed Specification Family (`specOf : (p : L.Prog) → AcceptedDom p → Spec`):**
   Whether a function `p` is intended to compute `q + 1`, `q + 20`, or the
   constant initializer `0` (`fn init_zero() -> 0`) is declared by its
   per-function specification `specOf p`, paired with `FunctionalSpec pre (specOf p hp)`
   (or a per-function negative canary `badOf p`), never inferred from magic
   numbers `1`/`26` or AST-global quantifiers over other functions in `L.Prog`.
3. **Crate Monotonicity, Syntactic Type-Checker Admission, Constant-Initializer
   Separation, and Vertical Pipeline Composition (`Theorems 4A–4D`):**
   We prove that this characterization is 100% crate-monotonic, admits
   `honestSyntacticTypeCompiler3` on crates of arbitrary size, certifies
   `.initZero` on `L_honest_crate_add1_add20` while rejecting `.bad0`,
   `.badConst42`, and `.buggySpike`, and composes vertically under `Tool.comp`
   even on the nondeterministic symmetry-breaking pipeline of `PENTEST-R3-10`!
-/

/-- An explicit syntactic sub-domain contract on `L` pairs a syntactic domain
    predicate `AcceptedDom : L.Prog → Prop` with an extrinsic per-program
    specification `specOf`. -/
structure ExplicitDomainContract {SemObs : Type} (L : Language SemObs) where
  AcceptedDom : L.Prog → Prop
  specOf      : (p : L.Prog) → AcceptedDom p → L.Query → SemObs → Prop

/-- Local per-program satisfaction of an `ExplicitDomainContract`:
    `p` belongs to `AcceptedDom`, its specification `specOf p hp` is
    functional on `pre`, and `p` satisfies `L.VerifiedSpineOn dom pre (specOf p hp) p`.
    Notice that this definition mentions **zero** other programs `b : L.Prog`! -/
def Language.SatisfiesExplicitContractOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (C : ExplicitDomainContract L) (p : L.Prog) : Prop :=
  ∃ hp : C.AcceptedDom p,
    FunctionalSpec pre (C.specOf p hp) ∧
    L.VerifiedSpineOn dom pre (C.specOf p hp) p

/-- Soundness and explicit sub-domain completeness of a tool `tool : Tool L_src L_tgt`
    with respect to `C : ExplicitDomainContract L_src`:
    1. **Sound Over-Approximation:** Every accepted program `p` satisfies the
       explicit contract `L_src.SatisfiesExplicitContractOn dom pre C p` and
       compiles productively via `c` (`ProductiveCompiles`).
    2. **Explicit Sub-Domain Completeness:** Every program `p` in the declared
       syntactic sub-domain `C.AcceptedDom p` is accepted by `tool`. -/
def Tool.SoundAndCompleteOnExplicitDomain {SemObs : Type}
    {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt)
    (tool : Tool L_src L_tgt)
    (dom pre : L_src.Query → Prop)
    (C : ExplicitDomainContract L_src) : Prop :=
  (∀ p : L_src.Prog, ∀ h_acc : (tool p).defined,
    L_src.SatisfiesExplicitContractOn dom pre C p ∧
    ProductiveCompiles L_src L_tgt c p ((tool p).val h_acc)) ∧
  (∀ p : L_src.Prog, C.AcceptedDom p → Tool.Accepted tool p)

/-- **Theorem 4A (`ExplicitDomainContract_CrateMonotonic`):**
    Unlike `WellBehavedProgOn` and `TotalWellBehavedDomainOn`,
    `Language.SatisfiesExplicitContractOn` is **100% Crate-Monotonic**: for any
    same-domain crate extension `ext : SameDomainCrateExtension L L' rfl rfl`
    and any contract `C'` on `L'` whose restriction to `L` along `ext.embedProg`
    is `C`, a program `p : L.Prog` satisfies `C` in `L` if and only if
    `ext.embedProg p` satisfies `C'` in `L'`! -/
theorem ExplicitDomainContract_CrateMonotonic
    {SemObs : Type} (L L' : Language SemObs)
    (hQ : L.Query = L'.Query) (hO : L.Out = L'.Out)
    (hObs : ∀ o : L.Out, L'.obs (cast hO o) = L.obs o)
    (ext : SameDomainCrateExtension L L' hQ hO)
    (dom pre : L.Query → Prop)
    (C' : ExplicitDomainContract L')
    (p : L.Prog) :
    let C : ExplicitDomainContract L := {
      AcceptedDom := fun q_p => C'.AcceptedDom (ext.embedProg q_p)
      specOf      := fun q_p hp q v => C'.specOf (ext.embedProg q_p) hp (cast hQ q) v
    }
    L.SatisfiesExplicitContractOn dom pre C p ↔
    L'.SatisfiesExplicitContractOn (cast (by rw [hQ]) dom) (cast (by rw [hQ]) pre)
      C' (ext.embedProg p) := by
  cases L
  cases L'
  cases hQ
  cases hO
  dsimp only [cast_eq] at hObs ⊢
  have h_obs_eq := funext hObs
  subst h_obs_eq
  have h_sem := ext.sem_eq p
  dsimp only [cast_eq] at h_sem
  dsimp [Language.SatisfiesExplicitContractOn, Language.VerifiedSpineOn,
    Language.VerifiedOn, Language.ProductiveOn, Language.SpecOn]
  rw [h_sem]
  exact Iff.rfl

/-- Explicit syntactic well-typedness contract on the 3-function + dead-branch
    crate `L_typed3` (`PENTEST-R4-3A`). -/
def typed3Contract : ExplicitDomainContract L_typed3 where
  AcceptedDom
    | .wellTypedAddOne    => True
    | .wellTypedAddTwo    => True
    | .wellTypedAddThree  => True
    | .deadBranchIllTyped => False
    | .liveNullDeref      => False
  specOf p _ q v := match p with
    | .wellTypedAddOne    => v = q + 1
    | .wellTypedAddTwo    => v = q + 2
    | .wellTypedAddThree  => v = q + 3
    | .deadBranchIllTyped => False
    | .liveNullDeref      => False

/-- **Theorem 4B (`ExplicitDomainContract_Admits_SyntacticTypeCheckers` —
    Resolving `PENTEST-R3-2A` and `PENTEST-R4-3A/B`):**
    On the 3-function crate `L_typed3`, `honestSyntacticTypeCompiler3` satisfies
    `Tool.SoundAndCompleteOnExplicitDomain` with respect to `typed3Contract`:
    it accepts all 3 well-typed functions, verifies each against its exact
    functional specification (`q + 1`, `q + 2`, `q + 3`), and rejects both
    `.deadBranchIllTyped` and `.liveNullDeref` without any Rice/Cousot lockout! -/
theorem ExplicitDomainContract_Admits_SyntacticTypeCheckers :
    Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.id L_typed3)
      honestSyntacticTypeCompiler3
      L_typed3.dom (fun q => q < 100)
      typed3Contract ∧
    Tool.Rejected honestSyntacticTypeCompiler3 .deadBranchIllTyped ∧
    Tool.Rejected honestSyntacticTypeCompiler3 .liveNullDeref := by
  refine ⟨⟨?_, ?_⟩, fun h => h, fun h => h⟩
  · intro p h_acc
    cases p with
    | wellTypedAddOne =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun q _ => ⟨trivial, q + 1, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_typed3 .wellTypedAddOne⟩
    | wellTypedAddTwo =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun q _ => ⟨trivial, q + 2, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_typed3 .wellTypedAddTwo⟩
    | wellTypedAddThree =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun q _ => ⟨trivial, q + 3, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_typed3 .wellTypedAddThree⟩
    | deadBranchIllTyped => exact False.elim h_acc
    | liveNullDeref      => exact False.elim h_acc
  · intro p hp
    cases p with
    | wellTypedAddOne | wellTypedAddTwo | wellTypedAddThree => exact trivial
    | deadBranchIllTyped | liveNullDeref => exact False.elim hp

/-- Unified 7-program crate combining honest query-sensitive functions (`.add1`,
    `.add20`), an honest constant initializer (`.initZero`), and all three Round 4
    buggy bypass programs (`.bad0`, `.badConst42`, `.buggySpike`, `.oobPanic`). -/
inductive UnifiedCrateProg where
  | add1
  | add20
  | initZero
  | bad0
  | badConst42
  | buggySpike
  | oobPanic
  deriving DecidableEq

abbrev L_unified_crate : Language Nat :=
  Language.mkSimple UnifiedCrateProg Nat Nat (fun p q => match p with
    | .add1       => Partial.pure (fun o => o = q + 1)
    | .add20      => Partial.pure (fun o => o = q + 20)
    | .initZero   => Partial.pure (fun o => o = 0)
    | .bad0       => Partial.pure (fun o => o = 0)
    | .badConst42 => Partial.pure (fun o => o = 42)
    | .buggySpike => Partial.pure (fun o => o = if q = 0 then 1 else 0)
    | .oobPanic   => Partial.ub)

/-- Intended per-function specification for every program in `L_unified_crate`:
    - `.initZero` is an intentional constant initializer (`v = 0`),
    - `.add1`, `.bad0`, `.badConst42`, `.buggySpike`, and `.oobPanic` are
      intended to compute `v = q + 1`,
    - `.add20` is intended to compute `v = q + 20`. -/
abbrev intendedUnifiedSpec : UnifiedCrateProg → Nat → Nat → Prop
  | .add1,       q, v => v = q + 1
  | .add20,      q, v => v = q + 20
  | .initZero,   _, v => v = 0
  | .bad0,       q, v => v = q + 1
  | .badConst42, q, v => v = q + 1
  | .buggySpike, q, v => v = q + 1
  | .oobPanic,   q, v => v = q + 1

/-- Honest compiler on `L_unified_crate` that accepts the verified sub-domain
    `{.add1, .add20, .initZero}` and rejects `{.bad0, .badConst42, .buggySpike, .oobPanic}`. -/
def honestUnifiedCrateCompiler : Tool L_unified_crate L_unified_crate
  | .add1       => Partial.pure .add1
  | .add20      => Partial.pure .add20
  | .initZero   => Partial.pure .initZero
  | .bad0       => Partial.ub
  | .badConst42 => Partial.ub
  | .buggySpike => Partial.ub
  | .oobPanic   => Partial.ub

/-- Explicit contract for `L_unified_crate`. -/
def unifiedCrateContract : ExplicitDomainContract L_unified_crate where
  AcceptedDom
    | .add1       => True
    | .add20      => True
    | .initZero   => True
    | .bad0       => False
    | .badConst42 => False
    | .buggySpike => False
    | .oobPanic   => False
  specOf p _ := intendedUnifiedSpec p

/-- **Theorem 4C (`ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike` —
    Resolving `PENTEST-R4-1A/B/C` and `PENTEST-R4-7`):**
    On `L_unified_crate` (even on `q < 16` where `.add1` produces `1` at `q = 0`
    and `.add20` produces `26` at `q = 6`):
    1. `honestUnifiedCrateCompiler` satisfies `Tool.SoundAndCompleteOnExplicitDomain`,
       certifying `.add1`, `.add20`, and the constant initializer `.initZero`!
    2. Each of `.bad0`, `.badConst42`, `.buggySpike`, and `.oobPanic` is
       provably refuted against its intended specification `intendedUnifiedSpec`! -/
theorem ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike :
    let pre := fun q : Nat => q < 16
    Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.id L_unified_crate)
      honestUnifiedCrateCompiler
      L_unified_crate.dom pre
      unifiedCrateContract ∧
    L_unified_crate.ViolatesSpine pre (intendedUnifiedSpec .bad0) .bad0 ∧
    L_unified_crate.ViolatesSpine pre (intendedUnifiedSpec .badConst42) .badConst42 ∧
    L_unified_crate.ViolatesSpine pre (intendedUnifiedSpec .buggySpike) .buggySpike ∧
    L_unified_crate.ViolatesSafetyOn pre .oobPanic := by
  dsimp only
  refine ⟨⟨?_, ?_⟩,
    ⟨0, by decide, trivial, 0, rfl, by decide⟩,
    ⟨0, by decide, trivial, 42, rfl, by decide⟩,
    ⟨1, by decide, trivial, 0, rfl, by decide⟩,
    ⟨0, by decide, fun h => h⟩⟩
  · intro p h_acc
    cases p with
    | add1 =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun q _ => ⟨trivial, q + 1, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_unified_crate .add1⟩
    | add20 =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun q _ => ⟨trivial, q + 20, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_unified_crate .add20⟩
    | initZero =>
      exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
        Or.inl ⟨0, by decide⟩,
        fun _ _ => ⟨trivial, 0, rfl⟩,
        fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
        ProductiveCompiles.refl L_unified_crate .initZero⟩
    | bad0 | badConst42 | buggySpike | oobPanic => exact False.elim h_acc
  · intro p hp
    cases p with
    | add1 | add20 | initZero => exact trivial
    | bad0 | badConst42 | buggySpike | oobPanic => exact False.elim hp

/-- **Theorem 4D (`ExplicitDomainContract_VerticalComposition` — Resolving
    `PENTEST-R3-10`):**
    Unlike `Tool.SemanticallyClosedOn`, `Tool.SoundAndCompleteOnExplicitDomain`
    is **strictly closed under vertical pipeline composition `Tool.comp tool₁ tool₂`**
    for arbitrary (even nondeterministic!) intermediate languages `L₁ → L₂ → L₃`
    whenever `tool₁` maps `C₁.AcceptedDom` into `C₂.AcceptedDom`! -/
theorem ExplicitDomainContract_VerticalComposition
    {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {tool₁ : Tool L₁ L₂} {tool₂ : Tool L₂ L₃}
    {dom₁ pre₁ : L₁.Query → Prop} {dom₂ pre₂ : L₂.Query → Prop}
    {C₁ : ExplicitDomainContract L₁} {C₂ : ExplicitDomainContract L₂}
    (h₁ : Tool.SoundAndCompleteOnExplicitDomain c₁₂ tool₁ dom₁ pre₁ C₁)
    (h₂ : Tool.SoundAndCompleteOnExplicitDomain c₂₃ tool₂ dom₂ pre₂ C₂)
    (h_maps : ∀ p₁ : L₁.Prog, C₁.AcceptedDom p₁ →
      ∀ h_acc₁ : (tool₁ p₁).defined, C₂.AcceptedDom ((tool₁ p₁).val h_acc₁)) :
    Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.comp c₁₂ c₂₃)
      (Tool.comp tool₁ tool₂)
      dom₁ pre₁ C₁ := by
  refine ⟨?_, ?_⟩
  · intro p₁ ⟨h_acc₁, h_acc₂⟩
    have ⟨h_sat₁, h_pcomp₁₂⟩ := h₁.1 p₁ h_acc₁
    have ⟨_, h_pcomp₂₃⟩ := h₂.1 ((tool₁ p₁).val h_acc₁) h_acc₂
    exact ⟨h_sat₁, ProductiveCompiles.comp h_pcomp₁₂ h_pcomp₂₃⟩
  · intro p₁ hp₁
    have h_acc₁ : (tool₁ p₁).defined := h₁.2 p₁ hp₁
    have hp₂ : C₂.AcceptedDom ((tool₁ p₁).val h_acc₁) := h_maps p₁ hp₁ h_acc₁
    have h_acc₂ : (tool₂ ((tool₁ p₁).val h_acc₁)).defined :=
      h₂.2 ((tool₁ p₁).val h_acc₁) hp₂
    exact ⟨h_acc₁, h_acc₂⟩

/-!
## 5. Concrete Pentest Instantiations Across Candidates 001–016
   (`PENTEST-2`, `PENTEST-3A/B`, `PENTEST-5`, `PENTEST-R2-4A/B`, `PENTEST-R2-5`,
    `PENTEST-R3-5B`, `PENTEST-R3-8`, `PENTEST-R3-9B`, `PENTEST-R3-10`,
    `PENTEST-R4-1A`, `PENTEST-R4-3B`, `PENTEST-R4-9`)
-/

/-- Trojan horse compiler on `L_addK` (`PENTEST-2`): compiles witnessed `0`
    faithfully to `0`, but miscompiles every uninspected program `k + 1` to `0`
    while still satisfying witness-only soundness on `W_pos = [0]`! -/
def trojanAddKCompiler : Tool L_addK L_addK :=
  fun _ => Partial.pure 0

/-- **Theorem 5A (`PENTEST_2_3AB_R2_4AB_AllowlistAndTrojanSuite`):**
    1. (`PENTEST-2`): `trojanAddKCompiler` productively compiles the positive
       witness `0`, yet miscompiles `1` (`q + 1`) to `0` (`q + 0`), violating
       `Compiles` on `1`!
    2. (`PENTEST-3A/3B`): The 1-entry allowlist `allowlistCompiler honestAddKCompiler [0]`
       satisfies universal `ProductiveCompiles` on all accepted programs and
       accepts `0`, while rejecting every `k ≥ 1` (which `honestAddKCompiler`
       accepts and productively compiles).
    3. (`PENTEST-R2-4A/B`): The 2-entry allowlist `allowlistCompiler honestAddKCompiler [0, 1]`
       accepts `[0, 1]`, satisfies `Language.SemanticallyDiverseSuite (fun q => q < 100) [0, 1]`,
       and satisfies universal `ProductiveCompiles` on all accepted programs,
       yet rejects `2` (`q + 2`)! -/
theorem PENTEST_2_3AB_R2_4AB_AllowlistAndTrojanSuite :
    (Tool.Accepted trojanAddKCompiler 0 ∧
     ProductiveCompiles L_addK L_addK (BehaviorCodec.id L_addK) 0 0 ∧
     ¬ Compiles L_addK L_addK (BehaviorCodec.id L_addK) 1 0) ∧
    (Tool.Accepted (allowlistCompiler honestAddKCompiler [0]) 0 ∧
     Tool.Rejected (allowlistCompiler honestAddKCompiler [0]) 1 ∧
     Tool.Accepted honestAddKCompiler 1) ∧
    (L_addK.SemanticallyDiverseSuite (fun q => q < 100) [0, 1] ∧
     Tool.Accepted (allowlistCompiler honestAddKCompiler [0, 1]) 0 ∧
     Tool.Accepted (allowlistCompiler honestAddKCompiler [0, 1]) 1 ∧
     Tool.Rejected (allowlistCompiler honestAddKCompiler [0, 1]) 2) := by
  refine ⟨⟨trivial, ProductiveCompiles.refl L_addK 0, ?_⟩,
    ⟨⟨by decide, trivial⟩, fun ⟨h, _⟩ => by revert h; decide, trivial⟩,
    ⟨?_, ⟨by decide, trivial⟩, ⟨by decide, trivial⟩, fun ⟨h, _⟩ => by revert h; decide⟩⟩
  · intro h_comp
    have ⟨_, h_val⟩ := h_comp (0 : Nat) trivial
    have ⟨(o₁ : Nat), h_dec, ho₁⟩ := h_val (0 : Nat) rfl
    dsimp [BehaviorCodec.id, L_addK, Language.mkSimple, Partial.pure] at h_dec ho₁
    have h_o1 : o₁ = 0 := Option.some.inj h_dec.symm
    omega
  · exact ⟨0, 1, by decide, by decide, 0, 0, 1, by decide, by decide,
      ⟨trivial, 0, rfl, rfl⟩, ⟨trivial, 1, rfl, rfl⟩,
      fun ⟨_, _, ho, hv⟩ => by
        dsimp [L_addK, Language.mkSimple, Partial.pure] at ho hv
        omega⟩

/-- 4-program suite for `PENTEST-R3-5B` and `PENTEST-R4-9` (`depth3FunctionalSpec` evasion):
    - `0`: point-mutated canary failing at `q = 0` (`0`) and matching `q + 1` at `q ∈ {1, 2}`.
    - `1`: point-mutated canary failing at `q = 1` (`0`) and matching `q + 1` at `q ∈ {0, 2}`.
    - `2`: point-mutated canary failing at `q = 2` (`0`) and matching `q + 1` at `q ∈ {0, 1}`.
    - `3`: certified program matching `q + 1` on `[0, 1, 2]` and outputting `0` for all `q ≥ 3`! -/
abbrev L_depth3_evasion : Language Nat :=
  Language.mkSimple Nat Nat Nat (fun p q =>
    Partial.pure (fun o =>
      o = if p < 3 ∧ q = p then 0
          else if q ∈ [0, 1, 2] then q + 1
          else 0))

/-- **Theorem 5B (`PENTEST_5_R2_5_R3_5B_R4_9_DepthKSpecSuite`):**
    Concrete $k$-point specification evasion for $k = 1$ (`PENTEST-5`, `Q_1 = [0]`),
    $k = 2$ (`PENTEST-R2-5`, `Q_2 = [0, 1]`), and $k = 3$ (`PENTEST-R3-5B` and
    `PENTEST-R4-9`, `Q_3 = [0, 1, 2]`):
    `depthKFunctionalSpec [0, 1, 2] (fun q => q + 1) 0` satisfies `FunctionalSpec`,
    `PointwiseRefutable`, and 3-query `ViolatesAtQuerySuite` against the diagonal
    canary suite `[(0, 0), (1, 1), (2, 2)]`, yet certifies program `3` in
    `L_depth3_evasion` which outputs `0` at every `q ≥ 3`! -/
theorem PENTEST_5_R2_5_R3_5B_R4_9_DepthKSpecSuite :
    let pre := fun q : Nat => q < 100
    let spec3 := depthKFunctionalSpec [0, 1, 2] (fun q => q + 1) 0
    FunctionalSpec pre spec3 ∧
    PointwiseRefutable pre spec3 ∧
    L_depth3_evasion.ViolatesAtQuerySuite pre spec3 [(0, 0), (1, 1), (2, 2)] ∧
    L_depth3_evasion.VerifiedSpine pre spec3 3 ∧
    L_depth3_evasion.Produces 3 3 0 := by
  dsimp only
  refine ⟨fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
    fun q _ => ⟨(if q ∈ [0, 1, 2] then q + 1 else 0) + 1, by
      dsimp [depthKFunctionalSpec]; omega⟩,
    ⟨by decide,
     ⟨⟨by decide, by decide, trivial⟩, ⟨by decide, trivial⟩, trivial, trivial⟩,
     ⟨⟨by decide, trivial, 0, rfl, by dsimp [depthKFunctionalSpec]; decide⟩,
      ⟨fun h => False.elim (h rfl),
       fun _ => ⟨2, ⟨trivial, 2, rfl, rfl⟩, rfl⟩,
       fun _ => ⟨3, ⟨trivial, 3, rfl, rfl⟩, rfl⟩,
       trivial⟩⟩,
     ⟨⟨by decide, trivial, 0, rfl, by dsimp [depthKFunctionalSpec]; decide⟩,
      ⟨fun _ => ⟨1, ⟨trivial, 1, rfl, rfl⟩, rfl⟩,
       fun h => False.elim (h rfl),
       fun _ => ⟨3, ⟨trivial, 3, rfl, rfl⟩, rfl⟩,
       trivial⟩⟩,
     ⟨⟨by decide, trivial, 0, rfl, by dsimp [depthKFunctionalSpec]; decide⟩,
      ⟨fun _ => ⟨1, ⟨trivial, 1, rfl, rfl⟩, rfl⟩,
       fun _ => ⟨2, ⟨trivial, 2, rfl, rfl⟩, rfl⟩,
       fun h => False.elim (h rfl),
       trivial⟩⟩,
     trivial⟩,
    ⟨Or.inl ⟨0, by decide⟩,
      fun q _ => ⟨trivial, if 3 < 3 ∧ q = 3 then 0 else if q ∈ [0, 1, 2] then q + 1 else 0, rfl⟩,
      fun q _ => ⟨trivial, fun o ho => by
        dsimp [L_depth3_evasion, Language.mkSimple, Partial.pure] at ho
        exact ho⟩⟩,
    ⟨trivial, 0, rfl, rfl⟩⟩

/-- Inverted buggy compiler on `L_spike_suite` (`PENTEST-R3-8` / `PENTEST-R3-9B`):
    accepts ONLY `.buggySpike` while rejecting `.addOne`, `.addTwo`, and `.ubCrash`. -/
def invertedSpikeCompiler : Tool L_spike_suite L_spike_suite
  | .addOne     => Partial.ub
  | .addTwo     => Partial.ub
  | .buggySpike => Partial.pure .buggySpike
  | .ubCrash    => Partial.ub

/-- **Theorem 5C (`PENTEST_R3_8_R3_9B_InvertedBuggyCompiler`):**
    `invertedSpikeCompiler` accepts `.buggySpike`, rejects `.addOne`, `.addTwo`,
    and `.ubCrash`, satisfies `ProductiveCompiles` on all accepted programs, and
    satisfies `Tool.SemanticallyClosedOn`! Thus `SemanticallyClosedOn` +
    `ProductiveCompiles` without an extrinsic specification certifies an inverted
    compiler that accepts only `.buggySpike`! -/
theorem PENTEST_R3_8_R3_9B_InvertedBuggyCompiler :
    let pre := fun q : Nat => q < 100
    Tool.Accepted invertedSpikeCompiler .buggySpike ∧
    Tool.Rejected invertedSpikeCompiler .addOne ∧
    Tool.Rejected invertedSpikeCompiler .addTwo ∧
    Tool.SemanticallyClosedOn pre invertedSpikeCompiler ∧
    (∀ p, ∀ h : (invertedSpikeCompiler p).defined,
      ProductiveCompiles L_spike_suite L_spike_suite
        (BehaviorCodec.id L_spike_suite) p ((invertedSpikeCompiler p).val h)) := by
  dsimp only
  refine ⟨trivial, fun h => h, fun h => h, ?_, ?_⟩
  · intro p₁ p₂ h_eq h_acc₁
    cases p₁ with
    | addOne | addTwo | ubCrash => exact False.elim h_acc₁
    | buggySpike =>
      cases p₂ with
      | buggySpike => exact trivial
      | addOne =>
        have ⟨_, _, ho, hv⟩ := (h_eq 1 (by decide) 0).mp ⟨trivial, 0, rfl, rfl⟩
        have h20 : (2 : Nat) = 0 := Eq.trans ho.symm hv; cases h20
      | addTwo =>
        have ⟨_, _, ho, hv⟩ := (h_eq 0 (by decide) 1).mp ⟨trivial, 1, rfl, rfl⟩
        have h21 : (2 : Nat) = 1 := Eq.trans ho.symm hv; cases h21
      | ubCrash =>
        have ⟨hdef, _⟩ := (h_eq 0 (by decide) 1).mp ⟨trivial, 1, rfl, rfl⟩
        exact False.elim hdef
  · intro p h
    cases p with
    | addOne | addTwo | ubCrash => exact False.elim h
    | buggySpike => exact ProductiveCompiles.refl L_spike_suite .buggySpike

/-- Honest compiler on `L_add27_add77_bad0_ub` that accepts `.add27` and `.add77`
    while rejecting `.bad0` and `.ubCrash` (`PENTEST-R4-1A`, `PENTEST-R4-3B`). -/
def honestAdd27Add77Compiler : Tool L_add27_add77_bad0_ub L_add27_add77_bad0_ub
  | .add27   => Partial.pure .add27
  | .add77   => Partial.pure .add77
  | .bad0    => Partial.ub
  | .ubCrash => Partial.ub

/-- **Theorem 5D (`PENTEST_R4_1A_3B_HonestCompilerLockout`):**
    On `L_add27_add77_bad0_ub`, `TotalWellBehavedDomainOn` holds (because `.bad0`
    is misclassified as a non-query-sensitive `WellBehavedProgOn` program!), so
    requiring universal acceptance of `WellBehavedProgOn` locks out
    `honestAdd27Add77Compiler` for rejecting `.bad0`! -/
theorem PENTEST_R4_1A_3B_HonestCompilerLockout :
    let pre := fun q : Nat => q < 100
    L_add27_add77_bad0_ub.TotalWellBehavedDomainOn pre ∧
    ¬ (∀ p, L_add27_add77_bad0_ub.WellBehavedProgOn pre p →
        Tool.Accepted honestAdd27Add77Compiler p) := by
  dsimp only
  have h_wb_bad0 := WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections.2.2.1
  have h_not_qs_bad0 : ¬ L_add27_add77_bad0_ub.QuerySensitiveOn (fun q => q < 100) .bad0 := by
    intro h_qs
    have ⟨_, _, v₁, v₂, _, _, hne, ⟨_, _, ho₁, hv₁⟩, ⟨_, _, ho₂, hv₂⟩⟩ :=
      h_qs ⟨0, 1, by decide, by decide, by decide⟩
    exact hne (Eq.trans (Eq.trans hv₁.symm ho₁) (Eq.trans ho₂.symm hv₂))
  exact ⟨Or.inr (Or.inr (Or.inl ⟨.bad0, h_wb_bad0, h_not_qs_bad0⟩)),
    fun h_all => h_all .bad0 h_wb_bad0⟩

/-- Explicit contract on `L_nondet_pipe` for the deterministic sub-domain `{.det1}`
    where both `stage1SymBreak` and `stage2Filter` compose cleanly (`PENTEST-R3-10`). -/
def nondetPipeDet1Contract : ExplicitDomainContract L_nondet_pipe where
  AcceptedDom
    | .det1         => True
    | .det2         => False
    | .nondet12     => False
    | .nondet12_alt => False
    | .bad0         => False
  specOf _ _ q v := v = q + 1

/-- **Theorem 5E (`PENTEST_R3_10_ResolvedByExplicitContract`):**
    On `L_nondet_pipe`, restricting `stage1SymBreak` and `stage2Filter` to their
    compatible explicit deterministic contract `nondetPipeDet1Contract` via
    `allowlistCompiler` yields tools whose vertical composition `Tool.comp`
    satisfies `Tool.SoundAndCompleteOnExplicitDomain`! -/
theorem PENTEST_R3_10_ResolvedByExplicitContract :
    let t₁ := allowlistCompiler stage1SymBreak [.det1]
    let t₂ := allowlistCompiler stage2Filter [.det1]
    Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.comp (BehaviorCodec.id L_nondet_pipe) (BehaviorCodec.id L_nondet_pipe))
      (Tool.comp t₁ t₂)
      L_nondet_pipe.dom (fun q => q < 100)
      nondetPipeDet1Contract := by
  dsimp only
  have h₁ : Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.id L_nondet_pipe)
      (allowlistCompiler stage1SymBreak [.det1])
      L_nondet_pipe.dom (fun q => q < 100)
      nondetPipeDet1Contract := by
    refine ⟨?_, ?_⟩
    · intro p ⟨hp_in, h_acc⟩
      cases p with
      | det1 =>
        exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
          Or.inl ⟨0, by decide⟩,
          fun q _ => ⟨trivial, q + 1, rfl⟩,
          fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
          ProductiveCompiles.refl L_nondet_pipe .det1⟩
      | det2 | nondet12 | nondet12_alt | bad0 =>
        exact False.elim (by revert hp_in; decide)
    · intro p hp
      cases p with
      | det1 => exact ⟨by decide, trivial⟩
      | det2 | nondet12 | nondet12_alt | bad0 => exact False.elim hp
  have h₂ : Tool.SoundAndCompleteOnExplicitDomain
      (BehaviorCodec.id L_nondet_pipe)
      (allowlistCompiler stage2Filter [.det1])
      L_nondet_pipe.dom (fun q => q < 100)
      nondetPipeDet1Contract := by
    refine ⟨?_, ?_⟩
    · intro p ⟨hp_in, h_acc⟩
      cases p with
      | det1 =>
        exact ⟨⟨trivial, fun _ _ _ _ h₁ h₂ => Eq.trans h₁ h₂.symm,
          Or.inl ⟨0, by decide⟩,
          fun q _ => ⟨trivial, q + 1, rfl⟩,
          fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
          ProductiveCompiles.refl L_nondet_pipe .det1⟩
      | det2 | nondet12 | nondet12_alt | bad0 =>
        exact False.elim (by revert hp_in; decide)
    · intro p hp
      cases p with
      | det1 => exact ⟨by decide, trivial⟩
      | det2 | nondet12 | nondet12_alt | bad0 => exact False.elim hp
  exact ExplicitDomainContract_VerticalComposition h₁ h₂ (by
    intro p₁ hp₁ _
    cases p₁ with
    | det1 => exact trivial
    | det2 | nondet12 | nondet12_alt | bad0 => exact False.elim hp₁)

end SemanticModelsInductiveInference

#print axioms SemanticModelsInductiveInference.GoldAngluinFiniteWitnessImpossibility_Prog
#print axioms SemanticModelsInductiveInference.FiniteGoodSpecsLocksOutInfiniteFamily
#print axioms SemanticModelsInductiveInference.GoldAngluinFiniteWitnessImpossibility_Spec
#print axioms SemanticModelsInductiveInference.PointSeparatingSpecLocksOutBooleanAndParitySpecs
#print axioms SemanticModelsInductiveInference.DeadBranchSyntacticCheckerLockout
#print axioms SemanticModelsInductiveInference.SemanticallyClosedNonComposable
#print axioms SemanticModelsInductiveInference.UnlabeledIntrinsicWellBehavedImpossibility
#print axioms SemanticModelsInductiveInference.WellBehavedProgOn_Violates_CrateMonotonicity_BothDirections
#print axioms SemanticModelsInductiveInference.TotalWellBehavedDomainOn_Typed2_False_Typed3_True
#print axioms SemanticModelsInductiveInference.ExplicitDomainContract_CrateMonotonic
#print axioms SemanticModelsInductiveInference.ExplicitDomainContract_Admits_SyntacticTypeCheckers
#print axioms SemanticModelsInductiveInference.ExplicitDomainContract_Separates_ConstInit_From_BuggyConst_And_Spike
#print axioms SemanticModelsInductiveInference.ExplicitDomainContract_VerticalComposition
#print axioms SemanticModelsInductiveInference.PENTEST_2_3AB_R2_4AB_AllowlistAndTrojanSuite
#print axioms SemanticModelsInductiveInference.PENTEST_5_R2_5_R3_5B_R4_9_DepthKSpecSuite
#print axioms SemanticModelsInductiveInference.PENTEST_R3_8_R3_9B_InvertedBuggyCompiler
#print axioms SemanticModelsInductiveInference.PENTEST_R4_1A_3B_HonestCompilerLockout
#print axioms SemanticModelsInductiveInference.PENTEST_R3_10_ResolvedByExplicitContract
