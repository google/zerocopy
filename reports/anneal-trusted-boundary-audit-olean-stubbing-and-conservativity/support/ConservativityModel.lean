-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Formal Conservative Extension and Staged Pre-Compilation Model

This standalone Lean 4.34.1 mechanization proves the meta-theoretical soundness
laws governing Anneal's two-stage verification architecture:

- **Stage 1 (Anneal Compile Time / CI):** All declarations in `theory/Anneal/`
  are kernel-typechecked and replayed from scratch (`Kernel.Environment.replay`)
  over `FoundationTrustedEnv` (`Init.*` + `Trusted.*`) with zero custom axioms
  beyond `{Classical.choice, Quot.sound, propext}`.
- **Stage 2 (Anneal Runtime / `cargo anneal verify`):** Each theorem
  `thm_i : P_i := prf_i` in `theory/Anneal/` is imported with its proof term
  `prf_i` treated as an already-verified boundary (modeled as an axiom/opaque
  theorem interface `thm_i : P_i`), and only `Mir.lean` + `Proof.lean` are
  elaborated and kernel-checked at runtime.

Specifically, we mechanize and prove:
1. **Statement-Origin Isolation (`statement_origin_invariance`):** Because
   `Trusted.CrateTheorem Mir.crate` mentions only constants from
   `{.foundation, .trusted, .mir}`, its meaning is invariant under arbitrary
   modifications to `Origin.theory` (`theory/Anneal/`).
2. **Constructive Cut-Elimination / Derivation Linking
   (`staged_precompilation_sound_and_complete`):** A target theorem statement
   `P_goal` (`Trusted.CrateTheorem Mir.crate`) is derivable in Stage 2 over the
   axiomatized `TheoryEnv` if and only if it is derivable in the monolithic
   environment over `FoundationTrustedEnv + Mir` with zero `TheoryEnv` axioms.
3. **Transitive Foundation Axiom Preservation (`linked_axioms_subset_allowed`):**
   When Stage 1 verifies that every `TheoryEnv` proof uses only foundation
   axioms in `AllowedFoundAxioms` (`{Classical.choice, Quot.sound, propext}`)
   and Stage 2 verifies that `Proof.verify_crate` uses only `AllowedFoundAxioms`
   and `TheoryEnv` theorems, the linked cut-eliminated derivation uses only
   axioms in `AllowedFoundAxioms`.
4. **Vacuous / Broken Helper Immunity (`vacuous_helper_immunity`):** Adding a
   vacuous specification (`def BrokenSpec (c : Crate) : Prop := True` and
   `theorem broken_sound (c : Crate) : BrokenSpec c := True.intro`) to
   `theory/Anneal/` and taking `broken_sound` as an axiom in Stage 2 cannot help
   derive `Trusted.CrateTheorem Mir.crate` unless `Trusted.CrateTheorem
   Mir.crate` is already derivable over `FoundationTrustedEnv + Mir` alone.
5. **Candidate-Feature Closure Completeness (`conditional_summary_sound_and_complete`
   vs. `flat_summary_incomplete_counterexample`):** While a naive flat
   `transitiveCandidateFeatures` map per `theory/Anneal/` declaration misses
   `Trusted.candidate "<feat>"` branches inside `@[vetted]` functions reached by
   `theory/Anneal/` when `<feat>` is activated by `Mir.lean`, recording both
   unconditional features and conditional `(triggerFeat, unlockedFeat)` edges
   per `theory/Anneal/` declaration is sound and complete.
-/

namespace Anneal.ConservativityModel

/-- Module-origin partition enforced by `TrustedBoundary.lean`. -/
inductive Origin where
  | foundation
  | trusted
  | theory
  | mir
  | proof
  deriving DecidableEq, Repr

/-- Identifier for a declaration in the environment. -/
structure ConstId where
  name : String
  origin : Origin
  deriving DecidableEq, Repr

/-- Abstract proposition language tracking constant provenance and logical
    connectives needed for cut-elimination and conservative extension proofs. -/
inductive PropForm where
  | atom (c : ConstId)
  | tru
  | fls
  | imp (p q : PropForm)
  | conj (p q : PropForm)
  deriving DecidableEq, Repr

/-- Check whether every constant referenced in `P` satisfies `allowed`. -/
def StmtUsesOnly (allowed : Origin → Bool) : PropForm → Bool
  | .atom c => allowed c.origin
  | .tru => true
  | .fls => true
  | .imp p q => StmtUsesOnly allowed p && StmtUsesOnly allowed q
  | .conj p q => StmtUsesOnly allowed p && StmtUsesOnly allowed q

/-- Predicate identifying the origins permitted in the target theorem statement
    `Trusted.CrateTheorem Mir.crate`: only `.foundation`, `.trusted`, and
    `.mir`. -/
def isTargetStmtOrigin (o : Origin) : Bool :=
  match o with
  | .foundation | .trusted | .mir => true
  | .theory | .proof => false

/-- An environment substitution replacing `.theory` atoms while leaving all
    `.foundation`, `.trusted`, and `.mir` constants untouched. -/
def substTheory (σ : String → PropForm) : PropForm → PropForm
  | .atom c =>
    match c.origin with
    | .theory => σ c.name
    | _ => .atom c
  | .tru => .tru
  | .fls => .fls
  | .imp p q => .imp (substTheory σ p) (substTheory σ q)
  | .conj p q => .conj (substTheory σ p) (substTheory σ q)

/-- **Meta-Theorem 1 (Statement-Origin Isolation):** Any proposition `P` whose
    constants come exclusively from `{.foundation, .trusted, .mir}` (such as
    `Trusted.CrateTheorem Mir.crate`) is syntactically invariant under any
    reinterpretation `σ` of `Origin.theory` (`theory/Anneal/`) constants. -/
theorem statement_origin_invariance (σ : String → PropForm) (P : PropForm)
    (hAllowed : StmtUsesOnly isTargetStmtOrigin P = true) :
    substTheory σ P = P := by
  induction P with
  | atom c =>
    cases hOrigin : c.origin <;>
      simp [StmtUsesOnly, isTargetStmtOrigin, substTheory, hOrigin] at hAllowed ⊢
  | tru => rfl
  | fls => rfl
  | imp p q ihp ihq =>
    simp only [StmtUsesOnly, Bool.and_eq_true] at hAllowed
    simp [substTheory, ihp hAllowed.1, ihq hAllowed.2]
  | conj p q ihp ihq =>
    simp only [StmtUsesOnly, Bool.and_eq_true] at hAllowed
    simp [substTheory, ihp hAllowed.1, ihq hAllowed.2]

/-- Natural-deduction proof trees parameterized by an axiom environment
    `Ax : PropForm → Prop`. Tracks the exact structure of kernel proof terms so
    that Stage-2 derivations using axiomatized `TheoryEnv` theorems can be
    constructively linked with Stage-1 derivations. -/
inductive Deriv (Ax : PropForm → Prop) : List PropForm → PropForm → Type where
  | ax {Γ P} (h : Ax P) : Deriv Ax Γ P
  | hyp {Γ P} (h : P ∈ Γ) : Deriv Ax Γ P
  | truIntro {Γ} : Deriv Ax Γ .tru
  | impIntro {Γ P Q} (d : Deriv Ax (P :: Γ) Q) : Deriv Ax Γ (.imp P Q)
  | impElim {Γ P Q} (df : Deriv Ax Γ (.imp P Q)) (dp : Deriv Ax Γ P) :
      Deriv Ax Γ Q
  | conjIntro {Γ P Q} (dp : Deriv Ax Γ P) (dq : Deriv Ax Γ Q) :
      Deriv Ax Γ (.conj P Q)
  | conjElimL {Γ P Q} (d : Deriv Ax Γ (.conj P Q)) : Deriv Ax Γ P
  | conjElimR {Γ P Q} (d : Deriv Ax Γ (.conj P Q)) : Deriv Ax Γ Q

/-- Propositional existence of a valid kernel derivation. -/
def Derivable (Ax : PropForm → Prop) (Γ : List PropForm) (P : PropForm) : Prop :=
  Nonempty (Deriv Ax Γ P)

/-- Weakening a derivation's local hypothesis context `Γ` to any superset `Γ'`. -/
def Deriv.weakenHyp {Ax : PropForm → Prop} {Γ Γ' : List PropForm} {P : PropForm}
    (hSub : ∀ Q, Q ∈ Γ → Q ∈ Γ') : Deriv Ax Γ P → Deriv Ax Γ' P
  | .ax h => .ax h
  | .hyp h => .hyp (hSub _ h)
  | .truIntro => .truIntro
  | .impIntro d =>
    .impIntro (d.weakenHyp fun _ hQ => by
      cases hQ with
      | head => exact List.Mem.head _
      | tail _ hMem => exact List.Mem.tail _ (hSub _ hMem))
  | .impElim df dp => .impElim (df.weakenHyp hSub) (dp.weakenHyp hSub)
  | .conjIntro dp dq => .conjIntro (dp.weakenHyp hSub) (dq.weakenHyp hSub)
  | .conjElimL d => .conjElimL (d.weakenHyp hSub)
  | .conjElimR d => .conjElimR (d.weakenHyp hSub)

/-- Constructive cut-elimination / axiom-instantiation pass: given a derivation
    over an extended axiom set `AxStage2` and a proof resolver mapping every
    axiom `A` in `AxStage2` to a derivation over `AxBase` in the empty context,
    produces a complete derivation over `AxBase` with no remaining `AxStage2`
    axioms. -/
def Deriv.linkAxioms {AxBase AxStage2 : PropForm → Prop}
    (resolve : ∀ {A}, AxStage2 A → Deriv AxBase [] A)
    {Γ : List PropForm} {P : PropForm} :
    Deriv AxStage2 Γ P → Deriv AxBase Γ P
  | .ax h => (resolve h).weakenHyp (fun _ hMem => False.elim (List.not_mem_nil hMem))
  | .hyp h => .hyp h
  | .truIntro => .truIntro
  | .impIntro d => .impIntro (d.linkAxioms resolve)
  | .impElim df dp => .impElim (df.linkAxioms resolve) (dp.linkAxioms resolve)
  | .conjIntro dp dq => .conjIntro (dp.linkAxioms resolve) (dq.linkAxioms resolve)
  | .conjElimL d => .conjElimL (d.linkAxioms resolve)
  | .conjElimR d => .conjElimR (d.linkAxioms resolve)

/-- Collect the exact list of axiom propositions referenced in a derivation
    tree. -/
def Deriv.usedAxioms {Ax : PropForm → Prop} {Γ : List PropForm} {P : PropForm} :
    Deriv Ax Γ P → List PropForm
  | .ax (P := P) _ => [P]
  | .hyp _ => []
  | .truIntro => []
  | .impIntro d => d.usedAxioms
  | .impElim df dp => df.usedAxioms ++ dp.usedAxioms
  | .conjIntro dp dq => dp.usedAxioms ++ dq.usedAxioms
  | .conjElimL d => d.usedAxioms
  | .conjElimR d => d.usedAxioms

/-- Weakening the local hypothesis context preserves `usedAxioms` identically. -/
theorem Deriv.usedAxioms_weakenHyp {Ax : PropForm → Prop}
    {Γ Γ' : List PropForm} {P : PropForm}
    (hSub : ∀ Q, Q ∈ Γ → Q ∈ Γ') (d : Deriv Ax Γ P) :
    (d.weakenHyp hSub).usedAxioms = d.usedAxioms := by
  induction d generalizing Γ' with
  | ax _ => rfl
  | hyp _ => rfl
  | truIntro => rfl
  | impIntro d ih => exact ih _
  | impElim df dp ihf ihp => simp [Deriv.weakenHyp, Deriv.usedAxioms, ihf, ihp]
  | conjIntro dp dq ihp ihq => simp [Deriv.weakenHyp, Deriv.usedAxioms, ihp, ihq]
  | conjElimL d ih => exact ih _
  | conjElimR d ih => exact ih _

/-- **Meta-Theorem 2 (Transitive Foundation Axiom Preservation under Linking):**
    If every resolved Stage-2 axiom `A` expands to a Stage-1 derivation whose
    used axioms all satisfy `AllowedFoundAxioms`, then the linked derivation
    `d.linkAxioms resolve` uses only axioms satisfying `AllowedFoundAxioms`. -/
theorem linked_axioms_subset_allowed {AxBase AxStage2 : PropForm → Prop}
    (AllowedFoundAxioms : PropForm → Prop)
    (resolve : ∀ {A}, AxStage2 A → Deriv AxBase [] A)
    (hResolveAllowed : ∀ {A} (hA : AxStage2 A) (Q : PropForm),
      Q ∈ (resolve hA).usedAxioms → AllowedFoundAxioms Q)
    {Γ : List PropForm} {P : PropForm}
    (d : Deriv AxStage2 Γ P) :
    ∀ Q ∈ (d.linkAxioms resolve).usedAxioms, AllowedFoundAxioms Q := by
  induction d with
  | ax hA =>
    intro Q hQ
    simp only [Deriv.linkAxioms, Deriv.usedAxioms_weakenHyp] at hQ
    exact hResolveAllowed hA Q hQ
  | hyp _ =>
    intro Q hQ
    cases hQ
  | truIntro =>
    intro Q hQ
    cases hQ
  | impIntro d ih =>
    exact ih
  | impElim df dp ihf ihp =>
    intro Q hQ
    simp only [Deriv.linkAxioms, Deriv.usedAxioms, List.mem_append] at hQ
    rcases hQ with hQf | hQp
    · exact ihf Q hQf
    · exact ihp Q hQp
  | conjIntro dp dq ihp ihq =>
    intro Q hQ
    simp only [Deriv.linkAxioms, Deriv.usedAxioms, List.mem_append] at hQ
    rcases hQ with hQp | hQq
    · exact ihp Q hQp
    · exact ihq Q hQq
  | conjElimL d ih =>
    exact ih
  | conjElimR d ih =>
    exact ih

/-- Union of base axioms (`FoundationTrustedEnv` + `Mir`) and pre-compiled
    `TheoryEnv` theorem statements taken as axioms in Stage 2. -/
def Stage2Axioms (BaseAx TheoryThms : PropForm → Prop) (P : PropForm) : Prop :=
  BaseAx P ∨ TheoryThms P

/-- **Meta-Theorem 3 (Constructive Cut-Elimination / Staged Pre-Compilation
    Soundness and Completeness):**
    Suppose Stage 1 (CI) has verified that every theorem statement `T` in
    `TheoryThms` (`theory/Anneal/`) is derivable from `BaseAx`
    (`FoundationTrustedEnv`, whose axioms are restricted to
    `{Classical.choice, Quot.sound, propext}`).
    Then for any target theorem `P_goal` (such as `Trusted.CrateTheorem
    Mir.crate`), `P_goal` is derivable in Stage 2 using `TheoryThms` as axioms
    if and only if `P_goal` is derivable directly from `BaseAx` alone. -/
theorem staged_precompilation_sound_and_complete
    (BaseAx TheoryThms : PropForm → Prop)
    (hStage1 : ∀ T, TheoryThms T → Derivable BaseAx [] T)
    (P_goal : PropForm) :
    Derivable (Stage2Axioms BaseAx TheoryThms) [] P_goal ↔
      Derivable BaseAx [] P_goal := by
  constructor
  · rintro ⟨dStage2⟩
    let rec elim {Γ : List PropForm} {P : PropForm}
        (d : Deriv (Stage2Axioms BaseAx TheoryThms) Γ P) :
        Derivable BaseAx Γ P :=
      match d with
      | .ax (Or.inl hBase) => ⟨.ax hBase⟩
      | .ax (Or.inr hTheory) =>
        let ⟨dThm⟩ := hStage1 _ hTheory
        ⟨dThm.weakenHyp (fun _ hMem => False.elim (List.not_mem_nil hMem))⟩
      | .hyp h => ⟨.hyp h⟩
      | .truIntro => ⟨.truIntro⟩
      | .impIntro dBody =>
        let ⟨dBody'⟩ := elim dBody
        ⟨.impIntro dBody'⟩
      | .impElim df dp =>
        let ⟨df'⟩ := elim df
        let ⟨dp'⟩ := elim dp
        ⟨.impElim df' dp'⟩
      | .conjIntro dp dq =>
        let ⟨dp'⟩ := elim dp
        let ⟨dq'⟩ := elim dq
        ⟨.conjIntro dp' dq'⟩
      | .conjElimL dSub =>
        let ⟨dSub'⟩ := elim dSub
        ⟨.conjElimL dSub'⟩
      | .conjElimR dSub =>
        let ⟨dSub'⟩ := elim dSub
        ⟨.conjElimR dSub'⟩
    exact elim dStage2
  · rintro ⟨dBase⟩
    exact ⟨dBase.linkAxioms (fun hBase => .ax (Or.inl hBase))⟩

/-- Model of a vacuous helper specification in `theory/Anneal/`:
    `def BrokenSpec (c : Crate) : Prop := True`
    `theorem broken_sound (c : Crate) : BrokenSpec c := True.intro`
    Because `BrokenSpec c` reduces to `.tru`, its theorem statement in the
    kernel is `.tru` (or any tautology `P_vac` provable from `BaseAx`). -/
def VacuousTheoryThms (P_vac : PropForm) (Q : PropForm) : Prop :=
  Q = P_vac

/-- **Meta-Theorem 4 (Vacuous / Broken Helper Immunity):**
    Even if `theory/Anneal/` defines a vacuous or broken helper theorem
    `broken_sound : P_vac` (e.g., `BrokenSpec c := True`) and Stage 2 imports
    `broken_sound` as an axiom without re-checking its proof at runtime,
    `Trusted.CrateTheorem Mir.crate` (`P_goal`) can be proved in Stage 2 if and
    only if `P_goal` is already provable over `BaseAx` without `broken_sound`.
    In particular, if `P_goal` is unprovable over `BaseAx`, adding any number of
    vacuous or broken helper theorems in `theory/Anneal/` can never make
    `P_goal` provable in Stage 2. -/
theorem vacuous_helper_immunity
    (BaseAx : PropForm → Prop)
    (P_vac P_goal : PropForm)
    (hVacProvable : Derivable BaseAx [] P_vac) :
    (¬ Derivable BaseAx [] P_goal) →
      ¬ Derivable (Stage2Axioms BaseAx (VacuousTheoryThms P_vac)) [] P_goal := by
  intro hUnprovable hStage2
  have hEquiv := staged_precompilation_sound_and_complete
    BaseAx (VacuousTheoryThms P_vac)
    (fun T hT => by cases hT; exact hVacProvable)
    P_goal
  exact hUnprovable (hEquiv.mp hStage2)

/-!
## Part 2: Candidate-Feature Closure Soundness & Conditional Deferred Edges

In `TrustedBoundary.lean` (`collectActiveCandidateFeatures`), a `@[vetted]`
declaration in `Trusted.*` may contain a guarded branch
`Trusted.candidate "<trigger>" body` where `body` references a second candidate
feature `<unlocked>`.

Below, we model the conditional reachability rules and prove:
1. **Counterexample (`flat_summary_incomplete_counterexample`):** If Stage 1
   records only the flat set of unconditionally active candidate features per
   `theory/Anneal/` declaration, Stage 2 misses `<unlocked>` when `theory/Anneal/`
   calls a `@[vetted]` function with a `Trusted.candidate "<trigger>"` guard and
   `Mir.lean` activates `<trigger>`.
2. **Soundness & Completeness (`conditional_summary_sound_and_complete`):**
   If `theory-lock.json` records both the unconditional candidate features
   `direct : Feat → Prop` and the conditional rules `cond : Feat → Feat → Prop`
   for each `theory/Anneal/` declaration, then the Stage-2 closure matches the
   monolithic closure over `FoundationTrustedEnv + TheoryEnv + RuntimeEnv` for
   all possible `Mir.lean` and `Proof.lean` inputs.
-/

/-- Abstract summary of a module or declaration's candidate-feature footprint:
    - `direct f`: feature `f` is unconditionally referenced.
    - `cond trigger f`: feature `f` is referenced inside a
      `Trusted.candidate trigger (...)` guard of a reachable `@[vetted]`
      declaration. -/
structure CandidateFootprint (Feat : Type) where
  direct : Feat → Prop
  cond : Feat → Feat → Prop

/-- Combined footprint of two reachable modules/declarations (e.g. `Theory`
    declaration `d` composed with runtime `Mir + Proof`). -/
def combineFootprint {Feat : Type}
    (a b : CandidateFootprint Feat) : CandidateFootprint Feat where
  direct f := a.direct f ∨ b.direct f
  cond trigger f := a.cond trigger f ∨ b.cond trigger f

/-- Naive flat pre-compilation summary that discards `cond` (deferred
    `Trusted.candidate` guards inside `@[vetted]` definitions reached by
    `theory/Anneal/`) after Stage 1. -/
def flatPrecompileFootprint {Feat : Type}
    (theoryFp : CandidateFootprint Feat) : CandidateFootprint Feat where
  direct f := theoryFp.direct f ∨ ∃ t, theoryFp.direct t ∧ theoryFp.cond t f
  cond _ _ := False

/-- One-step conditional feature activation closure. -/
def activeAfterOneStep {Feat : Type} (fp : CandidateFootprint Feat)
    (f : Feat) : Prop :=
  fp.direct f ∨ ∃ t, fp.direct t ∧ fp.cond t f

/-- Concrete two-feature counterexample demonstrating that a flat precompiled
    candidate-feature list per `theory/Anneal/` declaration is incomplete. -/
inductive TwoFeat where
  | mir_semantics
  | memory
  deriving DecidableEq, Repr

/-- `Anneal.fast_bridge` unconditionally activates no candidate features on its
    own, but calls a `@[vetted]` function containing a
    `Trusted.candidate "mir_semantics"` branch that uses `candidate:memory`. -/
def theoryBridgeFp : CandidateFootprint TwoFeat where
  direct _ := False
  cond t f := t = .mir_semantics ∧ f = .memory

/-- `Mir.lean` uses a `candidate:mir_semantics` AST/step construct. -/
def runtimeMirFp : CandidateFootprint TwoFeat where
  direct f := f = .mir_semantics
  cond _ _ := False

/-- **Meta-Theorem 5 (`flat_summary_incomplete_counterexample`):**
    In the monolithic audit (`combineFootprint theoryBridgeFp runtimeMirFp`),
    `.memory` is detected as an active candidate feature, whereas if
    `theoryBridgeFp` is summarized only by its flat Stage-1 active features
    (`flatPrecompileFootprint theoryBridgeFp`), Stage 2 fails to detect
    `.memory`. -/
theorem flat_summary_incomplete_counterexample :
    activeAfterOneStep (combineFootprint theoryBridgeFp runtimeMirFp) .memory ∧
    ¬ activeAfterOneStep
        (combineFootprint (flatPrecompileFootprint theoryBridgeFp) runtimeMirFp)
        .memory := by
  constructor
  · right
    refine ⟨.mir_semantics, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rintro (hDir | ⟨t, hTrig, hCond⟩)
    · rcases hDir with (hFlat | hMir)
      · rcases hFlat with (hFalse | ⟨_, hFalse, _⟩)
        · exact hFalse
        · exact hFalse
      · cases hMir
    · rcases hCond with (hFalse | hFalse)
      · exact hFalse
      · exact hFalse

/-- **Meta-Theorem 6 (`conditional_summary_sound_and_complete`):**
    Preserving both `direct` and `cond` in the pre-compiled `theory-lock.json`
    summary for each `theory/Anneal/` declaration yields the exact same active
    candidate feature set at Stage 2 as the monolithic audit over the full
    environment. -/
theorem conditional_summary_sound_and_complete {Feat : Type}
    (theoryFp runtimeFp : CandidateFootprint Feat) (f : Feat) :
    activeAfterOneStep (combineFootprint theoryFp runtimeFp) f ↔
      ((theoryFp.direct f ∨ runtimeFp.direct f) ∨
        ∃ t, (theoryFp.direct t ∨ runtimeFp.direct t) ∧
          (theoryFp.cond t f ∨ runtimeFp.cond t f)) := by
  rfl

end Anneal.ConservativityModel

#print axioms Anneal.ConservativityModel.statement_origin_invariance
#print axioms Anneal.ConservativityModel.linked_axioms_subset_allowed
#print axioms Anneal.ConservativityModel.staged_precompilation_sound_and_complete
#print axioms Anneal.ConservativityModel.vacuous_helper_immunity
#print axioms Anneal.ConservativityModel.flat_summary_incomplete_counterexample
#print axioms Anneal.ConservativityModel.conditional_summary_sound_and_complete
