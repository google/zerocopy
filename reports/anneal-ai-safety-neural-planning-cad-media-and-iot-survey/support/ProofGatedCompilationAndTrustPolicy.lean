-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Proof-Gated Compilation and Per-Obligation Scoped Trust Policies

This standalone Lean 4 (`v4.34.1`) development mechanizes proof-gated
compilation, relational intermediate-representation elimination, and
per-obligation scoped trust policies across `trusted-core`
(`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `mir-to-x86`
(`4f45f0a391a921ced9c9dc773b9a040dbc215d14`):

1. **Proof-Gated Compilation Eliminates Intermediate IRs from the TCB
   (Sections 1–2):**
   When Anneal moves `MirLang` (and intermediate IRs such as `AnSSALang`) out of
   `trusted/lean/` into `theory/` and checks both:
   - the source/intermediate specification obligation
     `MirLang.sem s ≤ MirLang.SpecOn pre post`, and
   - the pass refinement obligation
     `Compiles MirLang X86Lang codec.toMorphism s t`,
   any untrusted intermediate language in `theory/` becomes **bidirectionally
   fail-closed**:
   - **Spurious UB in `theory/` is fail-closed**
     (`spurious_ir_ub_blocks_source_obligation`): if an untrusted `MirLang` in
     `theory/` steps to `.failed` (`defined = False`) on a valid input satisfying
     `pre`, the source obligation `MirLang.sem s ≤ MirLang.SpecOn pre post` is
     refutable, blocking the Spurious-UB Codegen Exploit.
   - **Omitted UB or omitted outcomes in `theory/` are fail-closed**
     (`omitted_ir_ub_blocks_pass_obligation`,
     `omitted_ir_outcome_blocks_pass_obligation`): if an untrusted `MirLang` in
     `theory/` steps cleanly where the trusted target `X86Lang` in `trusted/`
     faults or produces an unmodeled outcome, the pass simulation obligation
     `Compiles MirLang X86Lang codec.toMorphism s t` is refutable.
   - **Relational Cut Elimination (`proof_gated_compilation_eliminates_ir_from_tcb`,
     `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`):** once both
     obligations are discharged, `MirLang.sem` and `AnSSALang.sem` cancel out by
     transitivity (`Preorder.le_trans`), yielding an unconditional target theorem
     `X86Lang.sem t ≤ X86Lang.SpecOn ...` and `X86Lang.WellFormedOn ...` on the
     trusted target language regardless of how `MirLang` or `AnSSALang` were
     defined in `theory/`.

2. **The Cross-Function (and Intra-Function) Principle-of-Explosion Trap
   of Antecedent Proof Omissions (Section 3):**
   In `Trusted/Refinement.lean:444-456` and `Trusted/MirSemantics.lean:859-865`,
   `VerificationResultOn` places `AllHold (assumptions.map TrustedAssumption.meaning)`
   as a negative antecedent on the left-hand side of `→`. We prove that while
   **uninterpreted environment/model assumptions** (parameterized by `M :
   TCBModel` with a constructive realizability witness `∃ M, AllHold ...`) are
   consistent on the left of `→`, **concrete-program proof omissions**
   (`assumeSourceWellFormed`, `assumeSourceSpec`, `assumePassCompiles`) must
   **never** be placed on the left of `→`:
   - Because `MirLang.sem` and `X86Lang.sem` are transparent, computable
     definitions, if `"fn_wip"` has a real UB bug at a single concrete query
     `q₀` (such as `x = usize::MAX`), the antecedent hypothesis
     `MirLang.sem fn_wip ≤ MirLang.WellFormed` reduces at `q₀` to `True → False`
     (`transparent_buggy_wip_assumption_is_false`).
   - Consequently, exempting `"fn_wip"` via an antecedent hypothesis allows
     `Proof.verify_crate` to derive `False` with **zero kernel axioms** and use
     `False.elim` to discharge the verification obligation of a separate,
     unexempted, security-critical function `"fn_critical"` that also contains a
     real UB bug (`global_antecedent_omission_explodes_crate`)!
   - Even if antecedent assumptions are scoped per-function rather than
     crate-globally, omitting a single pass or specification obligation on a
     function via an antecedent hypothesis explodes all other unexempted
     obligations of that same function
     (`intra_function_antecedent_omission_explodes_other_obligations`).

3. **Positive Per-Obligation Scoping (`ScopedVerificationResult`)
   and End-to-End Multi-Pass Pipeline Composition (Sections 4–5):**
   Replacing antecedent proof omissions with positive per-obligation gating on
   the right (`ObligationEntry.requiredProp omitted e`) paired with
   `AllHold (omitted.map policy.isAllowed)` guarantees:
   - **Zero cross-function contamination (`scoped_omission_isolates_buggy_fn`):**
     exempting `"fn_wip"` discharges `"fn_wip"`'s entry (`True`) without
     introducing any hypothesis into the context, so the unexempted buggy
     `"fn_critical"` remains strictly unprovable across **all** possible
     `omitted` lists.
   - **Zero intra-function contamination
     (`scoped_omission_isolates_intra_fn_obligations`):** omitting one pass or
     specification on a function never weakens its remaining obligations.
   - **Exact zero-trust recovery (`scoped_zeroTrust_iff_allHold`) and
     antitonicity (`scoped_verification_antitone_in_omitted`):** under
     `ScopedTrustPolicy.zeroTrust`, `omitted` is forced to `[]` and 100% of
     source and pass obligations must hold.
   - **Soundness extraction from partially verified crates
     (`extract_verified_fn_from_partially_verified_crate`):** in a crate where
     `"fn_wip"` has UB and is exempted while `"fn_verified"` is not exempted,
     the crate theorem is provable (`partially_verified_crate_holds`) and still
     unconditionally yields the target `X86Lang` correctness theorem for
     `"fn_verified"`.
-/

namespace Anneal.ProofGatedTrustPolicy

-- ============================================================================
-- Section 1: Core Refinement Preorder, `Partial`, `Language`, and `BoundaryCodec`
-- (Mirroring `Trusted/Refinement.lean:207-414`)
-- ============================================================================

/-- Reflexive and transitive refinement preorder (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting equips `A → B` with a refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partial behavior cell representing $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- Top element $\mathsf{UB}$ (`defined := False`) of `Partial B`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map `f : B₁ → B₂` over the defined payload of `Partial B₁`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B` (`Trusted/Refinement.lean:275-282`). -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between preorders (`Trusted/Refinement.lean:290`). -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

theorem Partial.monotone_map {B₁ : Type u} {B₂ : Type v}
    [Preorder B₁] [Preorder B₂]
    {f : B₁ → B₂} (hf : Monotone f) :
    Monotone (Partial.map f) := by
  intro p₁ p₂ hp hdef₂
  cases hp hdef₂ with
  | intro hdef₁ hle =>
    exact ⟨hdef₁, hf hle⟩

/-- Query-indexed partial behavior domain (`Trusted/Refinement.lean:298`). -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Language bundle (`Trusted/Refinement.lean:306-310`). -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  Anneal.ProofGatedTrustPolicy.Behavior L.Query L.Out

/-- Query-indexed specification with precondition `pre` and postcondition `post`
    (`Trusted/Refinement.lean:328-333`). -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification (`Trusted/Refinement.lean:340`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional UB-freedom specification (`Trusted/Refinement.lean:355`). -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional UB-freedom specification (`Trusted/Refinement.lean:365`). -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

theorem Language.specOn_le_wellFormedOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Compilation refinement pass (`Trusted/Refinement.lean:377`). -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Boundary query/outcome codec between `L_src` and `L_tgt` inducing a
    canonical pullback behavior morphism `toMorphism` (generalizing `π_stage0`
    in `theory/Anneal/Compiler/NaiveCodegen.lean:268-280`). -/
structure BoundaryCodec (L_src L_tgt : Language) where
  decompileQuery : L_tgt.Query → L_src.Query
  decompileOut : L_tgt.Out → L_src.Out

/-- Canonical behavior morphism induced by a `BoundaryCodec`. -/
def BoundaryCodec.toMorphism {L_src L_tgt : Language}
    (codec : BoundaryCodec L_src L_tgt)
    (b : L_src.Behavior) : L_tgt.Behavior :=
  fun q =>
    Partial.map (fun P out => P (codec.decompileOut out))
      (b (codec.decompileQuery q))

/-- Composition of boundary codecs along a multi-stage pipeline
    `L₁ → L₂ → L₃`. -/
def BoundaryCodec.comp {L₁ L₂ L₃ : Language}
    (c₁₂ : BoundaryCodec L₁ L₂) (c₂₃ : BoundaryCodec L₂ L₃) :
    BoundaryCodec L₁ L₃ where
  decompileQuery q₃ := c₁₂.decompileQuery (c₂₃.decompileQuery q₃)
  decompileOut o₃ := c₁₂.decompileOut (c₂₃.decompileOut o₃)

/-- Every `BoundaryCodec.toMorphism` is unconditionally monotone. -/
theorem BoundaryCodec.monotone_toMorphism {L_src L_tgt : Language}
    (codec : BoundaryCodec L_src L_tgt) :
    Monotone codec.toMorphism := by
  intro b₁ b₂ hle q
  refine Partial.monotone_map ?_ (hle (codec.decompileQuery q))
  intro P₁ P₂ hP out hout
  exact hP (codec.decompileOut out) hout

/-- Functoriality of `BoundaryCodec.toMorphism` under codec composition. -/
theorem BoundaryCodec.toMorphism_comp {L₁ L₂ L₃ : Language}
    (c₁₂ : BoundaryCodec L₁ L₂) (c₂₃ : BoundaryCodec L₂ L₃)
    (b : L₁.Behavior) :
    c₂₃.toMorphism (c₁₂.toMorphism b) = (c₁₂.comp c₂₃).toMorphism b :=
  rfl

/-- Crucial TCB-independence identity: applying `codec.toMorphism` to a source
    specification `L_src.SpecOn pre post` is definitionally equal to a direct
    target specification `L_tgt.SpecOn ...` and does not reference `L_src.sem`
    at all. -/
theorem BoundaryCodec.toMorphism_specOn {L_src L_tgt : Language}
    (codec : BoundaryCodec L_src L_tgt)
    (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop) :
    codec.toMorphism (L_src.SpecOn pre post) =
      L_tgt.SpecOn
        (fun q => pre (codec.decompileQuery q))
        (fun q out => post (codec.decompileQuery q) (codec.decompileOut out)) :=
  rfl

theorem BoundaryCodec.toMorphism_wellFormedOn {L_src L_tgt : Language}
    (codec : BoundaryCodec L_src L_tgt)
    (pre : L_src.Query → Prop) :
    codec.toMorphism (L_src.WellFormedOn pre) =
      L_tgt.WellFormedOn (fun q => pre (codec.decompileQuery q)) :=
  rfl

/-- Conjunction of a list of propositions (`Trusted/Refinement.lean:436`). -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

-- ============================================================================
-- Section 2: Proof-Gated Compilation Makes Untrusted Intermediate
-- IRs (`MirLang` / `AnSSALang` in `theory/`) Bidirectionally Fail-Closed
-- ============================================================================

/-- Proof-gated compilation of source/intermediate program `s : L_src.Prog` to
    target program `t : L_tgt.Prog`: requires proving both
    1. Source specification (and hence UB-freedom on `pre`):
       `L_src.sem s ≤ L_src.SpecOn pre post`, and
    2. Pass compilation refinement:
       `Compiles L_src L_tgt codec.toMorphism s t`. -/
def ProofGatedCompiled (L_src L_tgt : Language)
    (codec : BoundaryCodec L_src L_tgt)
    (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_src.sem s ≤ L_src.SpecOn pre post ∧
  Compiles L_src L_tgt codec.toMorphism s t

/-- **Theorem 2.1 (`spurious_ir_ub_blocks_source_obligation`):**
    If an untrusted intermediate IR (`MirLang` in `theory/`)
    introduces **spurious UB** (`¬ (MirLang.sem s q₀).defined`) at any query
    `q₀` satisfying `pre q₀`, then although `Compiles` at `q₀` would hold
    vacuously on the right, the source obligation
    `MirLang.sem s ≤ MirLang.SpecOn pre post` (and therefore
    `ProofGatedCompiled`) is **provably false**! -/
theorem spurious_ir_ub_blocks_source_obligation
    (MirLang X86Lang : Language)
    (codec : BoundaryCodec MirLang X86Lang)
    (pre : MirLang.Query → Prop) (post : MirLang.Query → MirLang.Out → Prop)
    (s : MirLang.Prog) (t : X86Lang.Prog)
    (q₀ : MirLang.Query)
    (h_pre : pre q₀)
    (h_spurious_ub : ¬ (MirLang.sem s q₀).defined) :
    ¬ (MirLang.sem s ≤ MirLang.SpecOn pre post) ∧
    ¬ ProofGatedCompiled MirLang X86Lang codec pre post s t := by
  have h_no_src : ¬ (MirLang.sem s ≤ MirLang.SpecOn pre post) := by
    intro h_src
    obtain ⟨h_def, _⟩ := h_src q₀ h_pre
    exact h_spurious_ub h_def
  exact ⟨h_no_src, fun h_pg => h_no_src h_pg.1⟩

/-- **Theorem 2.2 (`omitted_ir_ub_blocks_pass_obligation`):**
    If an untrusted intermediate IR (`MirLang` in `theory/`)
    **omits real UB**—stepping to a defined behavior
    (`(MirLang.sem s (codec.decompileQuery q_tgt)).defined`) at a query where
    the trusted target language `X86Lang` in `trusted/` faults
    (`¬ (X86Lang.sem t q_tgt).defined`)—then the pass obligation
    `Compiles MirLang X86Lang codec.toMorphism s t` (and therefore
    `ProofGatedCompiled`) is **provably false**! -/
theorem omitted_ir_ub_blocks_pass_obligation
    (MirLang X86Lang : Language)
    (codec : BoundaryCodec MirLang X86Lang)
    (pre : MirLang.Query → Prop) (post : MirLang.Query → MirLang.Out → Prop)
    (s : MirLang.Prog) (t : X86Lang.Prog)
    (q_tgt : X86Lang.Query)
    (h_ir_defined : (MirLang.sem s (codec.decompileQuery q_tgt)).defined)
    (h_x86_faults : ¬ (X86Lang.sem t q_tgt).defined) :
    ¬ Compiles MirLang X86Lang codec.toMorphism s t ∧
    ¬ ProofGatedCompiled MirLang X86Lang codec pre post s t := by
  have h_no_pass : ¬ Compiles MirLang X86Lang codec.toMorphism s t := by
    intro h_comp
    obtain ⟨h_tgt_def, _⟩ := h_comp q_tgt h_ir_defined
    exact h_x86_faults h_tgt_def
  exact ⟨h_no_pass, fun h_pg => h_no_pass h_pg.2⟩

/-- **Theorem 2.3 (`omitted_ir_outcome_blocks_pass_obligation`):**
    If an untrusted intermediate IR (`MirLang` in `theory/`) omits a real
    execution outcome `out_tgt` produced by `X86Lang.sem t` at `q_tgt`
    (for example, by modeling an instruction with wrong arithmetic or omitting
    demonic nondeterminism), then `Compiles MirLang X86Lang codec.toMorphism s t`
    (and therefore `ProofGatedCompiled`) is **provably false**! -/
theorem omitted_ir_outcome_blocks_pass_obligation
    (MirLang X86Lang : Language)
    (codec : BoundaryCodec MirLang X86Lang)
    (pre : MirLang.Query → Prop) (post : MirLang.Query → MirLang.Out → Prop)
    (s : MirLang.Prog) (t : X86Lang.Prog)
    (q_tgt : X86Lang.Query) (out_tgt : X86Lang.Out)
    (h_ir_def : (MirLang.sem s (codec.decompileQuery q_tgt)).defined)
    (h_x86_out : ∀ h_tgt : (X86Lang.sem t q_tgt).defined,
      (X86Lang.sem t q_tgt).val h_tgt out_tgt)
    (h_ir_omits :
      ¬ (MirLang.sem s (codec.decompileQuery q_tgt)).val h_ir_def
          (codec.decompileOut out_tgt)) :
    ¬ Compiles MirLang X86Lang codec.toMorphism s t ∧
    ¬ ProofGatedCompiled MirLang X86Lang codec pre post s t := by
  have h_no_pass : ¬ Compiles MirLang X86Lang codec.toMorphism s t := by
    intro h_comp
    obtain ⟨h_tgt_def, h_sub⟩ := h_comp q_tgt h_ir_def
    exact h_ir_omits (h_sub out_tgt (h_x86_out h_tgt_def))
  exact ⟨h_no_pass, fun h_pg => h_no_pass h_pg.2⟩

/-- **Theorem 2.4 (`proof_gated_compilation_eliminates_ir_from_tcb`):**
    When both obligations of `ProofGatedCompiled` are discharged, the compiled
    target program `t` unconditionally satisfies the target-level specification
    and target well-formedness on the trusted `X86Lang` **regardless of how
    `MirLang.sem` was defined in `theory/`**! `MirLang.sem` acts purely as a
    cut-eliminated intermediate lemma and vanishes from the target guarantee. -/
theorem proof_gated_compilation_eliminates_ir_from_tcb
    (MirLang X86Lang : Language)
    (codec : BoundaryCodec MirLang X86Lang)
    (pre : MirLang.Query → Prop) (post : MirLang.Query → MirLang.Out → Prop)
    (s : MirLang.Prog) (t : X86Lang.Prog)
    (h_pg : ProofGatedCompiled MirLang X86Lang codec pre post s t) :
    X86Lang.sem t ≤
      X86Lang.SpecOn
        (fun q => pre (codec.decompileQuery q))
        (fun q out => post (codec.decompileQuery q) (codec.decompileOut out)) ∧
    X86Lang.sem t ≤
      X86Lang.WellFormedOn (fun q => pre (codec.decompileQuery q)) := by
  have h_spec_tgt :
      X86Lang.sem t ≤ codec.toMorphism (MirLang.SpecOn pre post) :=
    Preorder.le_trans h_pg.2 (codec.monotone_toMorphism h_pg.1)
  have h_wf_tgt :
      X86Lang.sem t ≤
        X86Lang.WellFormedOn (fun q => pre (codec.decompileQuery q)) :=
    Preorder.le_trans h_spec_tgt
      (X86Lang.specOn_le_wellFormedOn
        (fun q => pre (codec.decompileQuery q))
        (fun q out => post (codec.decompileQuery q) (codec.decompileOut out)))
  exact ⟨h_spec_tgt, h_wf_tgt⟩

/-- **Theorem 2.5 (`multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`):**
    In a multi-stage compilation pipeline
    $s_{\text{mir}} \xrightarrow{P_1} s_{\text{ssa}} \xrightarrow{P_2} t_{\text{x86}}$
    where **both** `MirLang` and `AnSSALang` live in `theory/` (outside the TCB)
    and only `X86Lang` lives in `trusted/`, proving:
    1. `MirLang.sem s_mir ≤ MirLang.SpecOn pre post`,
    2. `Compiles MirLang AnSSALang codec₁.toMorphism s_mir s_ssa`, and
    3. `Compiles AnSSALang X86Lang codec₂.toMorphism s_ssa t_x86`
    establishes `X86Lang.sem t_x86 ≤ (codec₁.comp codec₂).toMorphism (MirLang.SpecOn pre post)`
    and target UB-freedom on `X86Lang` unconditionally, eliminating both
    `MirLang.sem` and `AnSSALang.sem` from the TCB. -/
theorem multi_stage_proof_gated_compilation_eliminates_irs_from_tcb
    (MirLang AnSSALang X86Lang : Language)
    (codec₁ : BoundaryCodec MirLang AnSSALang)
    (codec₂ : BoundaryCodec AnSSALang X86Lang)
    (pre : MirLang.Query → Prop) (post : MirLang.Query → MirLang.Out → Prop)
    (s_mir : MirLang.Prog) (s_ssa : AnSSALang.Prog) (t_x86 : X86Lang.Prog)
    (h_src : MirLang.sem s_mir ≤ MirLang.SpecOn pre post)
    (h_p1 : Compiles MirLang AnSSALang codec₁.toMorphism s_mir s_ssa)
    (h_p2 : Compiles AnSSALang X86Lang codec₂.toMorphism s_ssa t_x86) :
    X86Lang.sem t_x86 ≤
      X86Lang.SpecOn
        (fun q => pre ((codec₁.comp codec₂).decompileQuery q))
        (fun q out =>
          post ((codec₁.comp codec₂).decompileQuery q)
            ((codec₁.comp codec₂).decompileOut out)) ∧
    X86Lang.sem t_x86 ≤
      X86Lang.WellFormedOn
        (fun q => pre ((codec₁.comp codec₂).decompileQuery q)) := by
  have h_comp12 :
      Compiles MirLang X86Lang (codec₁.comp codec₂).toMorphism s_mir t_x86 :=
    Preorder.le_trans h_p2 (codec₂.monotone_toMorphism h_p1)
  exact proof_gated_compilation_eliminates_ir_from_tcb
    MirLang X86Lang (codec₁.comp codec₂) pre post s_mir t_x86
    ⟨h_src, h_comp12⟩

-- ============================================================================
-- Section 3: The Cross-Function (and Intra-Function) Explosion
-- Trap of Antecedent Proof Omissions in `VerificationResultOn`
-- ============================================================================

/-- Concrete input query carrying an argument value `arg : Nat`. -/
structure ConcreteQuery where
  arg : Nat
  deriving BEq, DecidableEq, Repr

/-- Boundary query value (`usize::MAX` on 64-bit targets, or a distinguished
    boundary input `255` for concrete kernel evaluation). -/
abbrev boundaryArg : Nat := 255

/-- Concrete boundary query $q_0$ where `"fn_wip"` triggers UB. -/
def qBoundary : ConcreteQuery := ⟨boundaryArg⟩

/-- Concrete program AST with three representative functions:
    - `retZero`: safe function that always returns `0`.
    - `ubAtBoundary`: unfinished function (`"fn_wip"`) that returns `0` on
      inputs `< boundaryArg` but triggers UB (`.failed`) at `qBoundary`.
    - `alwaysUb`: security-critical function (`"fn_critical"`) containing a
      real unmitigated UB bug at every query. -/
inductive ConcreteBody where
  | retZero
  | ubAtBoundary
  | alwaysUb
  deriving BEq, DecidableEq, Repr

/-- Transparent, computable operational semantics of `ConcreteBody`. -/
def evalConcreteBody (body : ConcreteBody) (q : ConcreteQuery) :
    Partial (Nat → Prop) :=
  match body with
  | .retZero => Partial.pure (fun out => out = 0)
  | .ubAtBoundary =>
    if q.arg == boundaryArg then
      Partial.ub
    else
      Partial.pure (fun out => out = 0)
  | .alwaysUb => Partial.ub

abbrev ConcreteMirLang : Language where
  Prog := ConcreteBody
  Query := ConcreteQuery
  Out := Nat
  sem := evalConcreteBody

abbrev ConcreteX86Lang : Language where
  Prog := ConcreteBody
  Query := ConcreteQuery
  Out := Nat
  sem := evalConcreteBody

def idCodec : BoundaryCodec ConcreteMirLang ConcreteX86Lang where
  decompileQuery q := q
  decompileOut o := o

/-- Antecedent-style TCB assumption (`Trusted/Refinement.lean:418-456` and
    `Trusted/MirSemantics.lean:726-742`) attempting to model partial-verification
    proof omissions by placing the omitted obligation's proposition inside
    `TrustedAssumption.meaning`. -/
inductive AntecedentOmissionItem where
  | assumeSourceWellFormed (fnId : String) (body : ConcreteBody)
  | assumePassCompiles (fnId : String) (passId : String)
      (s : ConcreteBody) (t : ConcreteBody)

def AntecedentOmissionItem.meaning : AntecedentOmissionItem → Prop
  | .assumeSourceWellFormed _ body =>
    ConcreteMirLang.sem body ≤ ConcreteMirLang.WellFormed
  | .assumePassCompiles _ _ s t =>
    Compiles ConcreteMirLang ConcreteX86Lang idCodec.toMorphism s t

structure AntecedentTrustPolicy where
  isAllowed : AntecedentOmissionItem → Prop

/-- Antecedent-style `VerificationResultOn` (`Trusted/Refinement.lean:444-456`)
    where `AllHold (assumptions.map meaning)` sits on the **left-hand side** of
    an implication (`→`). -/
def VerificationResultAntecedent
    (policy : AntecedentTrustPolicy)
    (assumptions : List AntecedentOmissionItem)
    (s : ConcreteBody) (t : ConcreteBody)
    (pre : ConcreteQuery → Prop)
    (specs : List ConcreteMirLang.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map AntecedentOmissionItem.meaning) →
    AllHold ((ConcreteMirLang.WellFormedOn pre :: specs).map (fun spec =>
      ConcreteMirLang.sem s ≤ spec ∧
      Compiles ConcreteMirLang ConcreteX86Lang idCodec.toMorphism s t ∧
      ConcreteX86Lang.sem t ≤ idCodec.toMorphism spec)))

structure ConcreteCapturedFn where
  name : String
  s_mir : ConcreteBody
  t_x86 : ConcreteBody
  pre : ConcreteQuery → Prop := fun _ => True
  specs : List ConcreteMirLang.Behavior := []

structure ConcreteCrateAntecedent where
  functions : List ConcreteCapturedFn
  tcb : List AntecedentOmissionItem

/-- Crate theorem mirroring `Trusted/MirSemantics.lean:859-865` where `c.tcb`
    is shared across the crate's `VerificationResultOn` obligations. -/
def CrateTheoremAntecedent
    (policy : AntecedentTrustPolicy)
    (c : ConcreteCrateAntecedent) : Prop :=
  AllHold (c.functions.map (fun fn =>
    VerificationResultAntecedent policy c.tcb fn.s_mir fn.t_x86 fn.pre fn.specs))

/-- A strict trust policy that **only** permits omitting proofs on `"fn_wip"`
    and strictly forbids any assumption on `"fn_critical"`! -/
def wipOnlyAntecedentPolicy : AntecedentTrustPolicy where
  isAllowed
    | .assumeSourceWellFormed fnId _ => (fnId == "fn_wip") = true
    | .assumePassCompiles fnId _ _ _ => (fnId == "fn_wip") = true

/-- Policy sanity check: `wipOnlyAntecedentPolicy` rejects any assumption on
    `"fn_critical"`. -/
theorem wipOnlyAntecedentPolicy_forbids_critical (body : ConcreteBody) :
    ¬ wipOnlyAntecedentPolicy.isAllowed
        (.assumeSourceWellFormed "fn_critical" body) := by
  intro h
  nomatch h

/-- **Theorem 3.1 (`transparent_buggy_wip_assumption_is_false`):**
    Because `ConcreteMirLang.sem` is a transparent, computable definition and
    `.ubAtBoundary` (`"fn_wip"`) steps to `Partial.ub` (`defined := False`) at
    `qBoundary`, the antecedent hypothesis
    `AntecedentOmissionItem.meaning (.assumeSourceWellFormed "fn_wip" .ubAtBoundary)`
    evaluates at `qBoundary` to `True → False` and therefore proves `False` in
    Lean's base logic with **zero axioms**! -/
theorem transparent_buggy_wip_assumption_is_false :
    AntecedentOmissionItem.meaning
      (.assumeSourceWellFormed "fn_wip" .ubAtBoundary) → False := by
  intro h_wip
  obtain ⟨h_def, _⟩ := h_wip qBoundary True.intro
  exact h_def

/-- A crate containing:
    1. `"fn_wip"`: an unfinished function (`.ubAtBoundary`) that triggers UB at
       `qBoundary`, exempted in `tcb` via `.assumeSourceWellFormed "fn_wip" .ubAtBoundary`.
    2. `"fn_critical"`: a security-critical function (`.alwaysUb`) that ALSO
       triggers UB, is **not** exempted by `wipOnlyAntecedentPolicy`, and even
       asserts the contradictory specification `ConcreteMirLang.Spec (fun _ _ => False)`. -/
def crateWithBuggyWipAndBuggyCritical : ConcreteCrateAntecedent where
  functions := [
    { name := "fn_wip"
      s_mir := .ubAtBoundary
      t_x86 := .ubAtBoundary },
    { name := "fn_critical"
      s_mir := .alwaysUb
      t_x86 := .alwaysUb
      specs := [ConcreteMirLang.Spec (fun _ _ => False)] }
  ]
  tcb := [.assumeSourceWellFormed "fn_wip" .ubAtBoundary]

/-- **Theorem 3.2 (`global_antecedent_omission_explodes_crate`):**
    **The Cross-Function Principle-of-Explosion Vulnerability:**
    Even though `wipOnlyAntecedentPolicy` only permits exemptions for `"fn_wip"`
    (and forbids any exemption for `"fn_critical"`), and even though
    `"fn_critical"` executes `.alwaysUb` and claims `Spec (fun _ _ => False)`,
    `CrateTheoremAntecedent wipOnlyAntecedentPolicy crateWithBuggyWipAndBuggyCritical`
    is **provable with zero kernel axioms**!
    The proof of `"fn_critical"` extracts the antecedent hypothesis for
    `"fn_wip"` from `hTcb`, evaluates it at `qBoundary` to get `False`, and
    applies `False.elim` to discharge `"fn_critical"`. -/
theorem global_antecedent_omission_explodes_crate :
    CrateTheoremAntecedent wipOnlyAntecedentPolicy
      crateWithBuggyWipAndBuggyCritical := by
  refine ⟨?_, ?_, True.intro⟩
  · -- Obligation 1: `"fn_wip"`
    refine ⟨⟨rfl, True.intro⟩, ?_⟩
    intro hTcb
    exact False.elim (transparent_buggy_wip_assumption_is_false hTcb.1)
  · -- Obligation 2: `"fn_critical"` (discharged via `False.elim` from `"fn_wip"`!)
    refine ⟨⟨rfl, True.intro⟩, ?_⟩
    intro hTcb
    exact False.elim (transparent_buggy_wip_assumption_is_false hTcb.1)

/-- **Theorem 3.3 (`intra_function_antecedent_omission_explodes_other_obligations`):**
    **The Intra-Function Principle-of-Explosion Vulnerability:**
    Even if antecedent assumptions are attached per-function rather than
    crate-globally, placing an omitted pass obligation
    `.assumePassCompiles "fn_partial" "mir_to_x86" .retZero .ubAtBoundary` on
    the left-hand side of `→` still explodes! Because `.retZero` is defined at
    `qBoundary` while `.ubAtBoundary` faults at `qBoundary`, the omitted pass
    assumption derives `False` at `qBoundary` and proves the false source
    specification `ConcreteMirLang.Spec (fun _ _ => False)` on `.retZero`. -/
theorem intra_function_antecedent_omission_explodes_other_obligations :
    let policy : AntecedentTrustPolicy := {
      isAllowed := fun
        | .assumePassCompiles fnId passId _ _ =>
          (fnId == "fn_partial" && passId == "mir_to_x86") = true
        | .assumeSourceWellFormed _ _ => False
    }
    let fnAssumptions : List AntecedentOmissionItem :=
      [.assumePassCompiles "fn_partial" "mir_to_x86" .retZero .ubAtBoundary]
    VerificationResultAntecedent policy fnAssumptions
      .retZero .ubAtBoundary (fun _ => True)
      [ConcreteMirLang.Spec (fun _ _ => False)] := by
  refine ⟨⟨rfl, True.intro⟩, ?_⟩
  intro hAssump
  have hComp :
      Compiles ConcreteMirLang ConcreteX86Lang idCodec.toMorphism
        .retZero .ubAtBoundary := hAssump.1
  obtain ⟨hDefTarget, _⟩ := hComp qBoundary True.intro
  exact False.elim hDefTarget

-- ============================================================================
-- Section 4: The Architectural Solution — Positive Per-Obligation Scoping
-- (`ScopedVerificationResult`) vs. Uninterpreted Model Assumptions (`TCBModel`)
-- ============================================================================

/-- Granular category of a concrete-program verification obligation that must
    either be proved in the Lean kernel or explicitly exempted in `omitted` and
    approved by `ScopedTrustPolicy`. -/
inductive OmissionKind where
  /-- Baseline source/intermediate UB-freedom obligation
      (`L_src.sem s ≤ L_src.WellFormedOn pre`). -/
  | assumeSourceWellFormed
  /-- Functional specification obligation `specIdx` on the source/intermediate
      program (`L_src.sem s ≤ spec`). -/
  | assumeSourceSpec (specIdx : Nat)
  /-- Compilation simulation obligation for compiler pass `passId`
      (`Compiles L_in L_out codec.toMorphism s_in s_out`). -/
  | assumePassCompiles (passId : String)
  deriving DecidableEq, Repr

/-- Unique identifier of an atomic verification obligation on function `fnId`. -/
structure ObligationId where
  fnId : String
  kind : OmissionKind
  deriving DecidableEq, Repr

instance : BEq ObligationId where
  beq a b := decide (a = b)

/-- Computable boolean membership test for `ObligationId` in `omitted`. -/
def ObligationId.inList (id : ObligationId)
    (omitted : List ObligationId) : Bool :=
  omitted.any (fun x => decide (x = id))

/-- An atomic verification obligation pairing its structured `ObligationId`
    with the proposition `prop : Prop` to be proved. -/
structure ObligationEntry where
  id : ObligationId
  prop : Prop

/-- **Positive Per-Obligation Gating (`ObligationEntry.requiredProp`):**
    If `e.id.inList omitted` is `true`, the entry's requirement is replaced on
    the **right** (in positive polarity) by `True`; otherwise `e.prop` is
    required.
    Crucially:
    1. On concrete obligation lists, `e.id.inList omitted` reduces
        definitionally (`rfl`) in the Lean kernel.
    2. Omitting `e.id` never introduces `e.prop` as an antecedent hypothesis
       into the proof context of any other obligation! -/
def ObligationEntry.requiredProp (omitted : List ObligationId)
    (e : ObligationEntry) : Prop :=
  match e.id.inList omitted with
  | true => True
  | false => e.prop

/-- Policy governing which `ObligationId` omissions are permitted in a
    verification run. -/
structure ScopedTrustPolicy where
  allowOmission : ObligationId → Bool

/-- Predicate asserting that `policy` approves omitting `id`. -/
def ScopedTrustPolicy.isAllowed (policy : ScopedTrustPolicy)
    (id : ObligationId) : Prop :=
  policy.allowOmission id = true

/-- **Zero-Trust Policy (`ScopedTrustPolicy.zeroTrust`):**
    Forbids all proof omissions (`allowOmission _ := false`), requiring 100% of
    source and pass compilation obligations to be proved in the Lean kernel. -/
def ScopedTrustPolicy.zeroTrust : ScopedTrustPolicy where
  allowOmission _ := false

/-- **Scoped Verification Result (`ScopedVerificationResult`):**
    1. Every omitted obligation ID in `omitted` is approved by `policy`
       (`AllHold (omitted.map policy.isAllowed)`).
    2. Every obligation entry `e ∈ entries` satisfies `e.requiredProp omitted`
       (`AllHold (entries.map (ObligationEntry.requiredProp omitted))`). -/
def ScopedVerificationResult
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (entries : List ObligationEntry) : Prop :=
  AllHold (omitted.map policy.isAllowed) ∧
  AllHold (entries.map (ObligationEntry.requiredProp omitted))

/-- Helper: membership in `AllHold (xs.map f)`. -/
theorem allHold_map_iff {α : Type} (f : α → Prop) (xs : List α) :
    AllHold (xs.map f) ↔ ∀ x, x ∈ xs → f x := by
  induction xs with
  | nil =>
    constructor
    · intro _ _ h
      nomatch h
    · intro _
      exact True.intro
  | cons hd tl ih =>
    constructor
    · intro h x hx
      cases hx with
      | head => exact h.1
      | tail _ htl => exact ih.mp h.2 x htl
    · intro h
      exact ⟨h hd (.head tl), ih.mpr (fun x hx => h x (.tail hd hx))⟩

/-- Helper: if `id.inList omitted = true` and `AllHold (omitted.map p.isAllowed)`,
    then for any obligation `id` that is disjoint from all allowed IDs, we
    obtain a contradiction (`False`). -/
theorem allowed_of_inList
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (id : ObligationId)
    (h_all : AllHold (omitted.map policy.isAllowed))
    (h_in : id.inList omitted = true)
    (h_disjoint : ∀ x, policy.allowOmission x = true → decide (x = id) = false) :
    False := by
  induction omitted with
  | nil => nomatch h_in
  | cons hd tl ih =>
    dsimp [ObligationId.inList, List.any] at h_in
    have h_hd_neq : decide (hd = id) = false := h_disjoint hd h_all.1
    revert h_hd_neq h_in
    cases decide (hd = id) with
    | false =>
      intro h_in_tl _
      exact ih h_all.2 h_in_tl
    | true =>
      intro _ h_neq
      nomatch h_neq

/-- **Theorem 4.1 (`scoped_zeroTrust_forces_empty_omitted`):**
    Under `ScopedTrustPolicy.zeroTrust`, `AllHold (omitted.map
    ScopedTrustPolicy.zeroTrust.isAllowed)` holds if and only if
    `omitted = []`. -/
theorem scoped_zeroTrust_forces_empty_omitted (omitted : List ObligationId) :
    AllHold (omitted.map ScopedTrustPolicy.zeroTrust.isAllowed) ↔
      omitted = [] := by
  cases omitted with
  | nil =>
    constructor
    · intro _; rfl
    · intro _; exact True.intro
  | cons hd tl =>
    constructor
    · intro h; nomatch h.1
    · intro h; nomatch h

/-- When `omitted = []`, `e.requiredProp []` is definitionally equal to
    `e.prop`. -/
theorem requiredProp_nil (e : ObligationEntry) :
    e.requiredProp [] = e.prop :=
  rfl

/-- **Theorem 4.2 (`scoped_zeroTrust_iff_allHold`):**
    Under `ScopedTrustPolicy.zeroTrust`, `ScopedVerificationResult` holds if and
    only if `omitted = []` and 100% of `entries` hold unconditionally
    (`AllHold (entries.map (·.prop))`). -/
theorem scoped_zeroTrust_iff_allHold
    (omitted : List ObligationId) (entries : List ObligationEntry) :
    ScopedVerificationResult ScopedTrustPolicy.zeroTrust omitted entries ↔
      omitted = [] ∧ AllHold (entries.map (·.prop)) := by
  constructor
  · intro h
    have h_nil : omitted = [] :=
      (scoped_zeroTrust_forces_empty_omitted omitted).mp h.1
    subst h_nil
    exact ⟨rfl, h.2⟩
  · rintro ⟨h_nil, h_all⟩
    subst h_nil
    exact ⟨True.intro, h_all⟩

/-- **Theorem 4.3 (`scoped_verification_antitone_in_omitted`):**
    Shrinking the set of omitted obligations (`omitted₁ ⊆ omitted₂`) strengthens
    the verification result: if every obligation required under `omitted₁` holds,
    then every obligation required under any superset `omitted₂` also holds. -/
theorem scoped_verification_antitone_in_omitted
    (omitted₁ omitted₂ : List ObligationId)
    (entries : List ObligationEntry)
    (h_sub : ∀ (id : ObligationId),
      id.inList omitted₁ = true → id.inList omitted₂ = true)
    (h_req₁ : AllHold (entries.map (ObligationEntry.requiredProp omitted₁))) :
    AllHold (entries.map (ObligationEntry.requiredProp omitted₂)) := by
  refine (allHold_map_iff (ObligationEntry.requiredProp omitted₂) entries).mpr ?_
  intro e he
  have h₁ : e.requiredProp omitted₁ :=
    (allHold_map_iff (ObligationEntry.requiredProp omitted₁) entries).mp h_req₁ e he
  revert h₁
  unfold ObligationEntry.requiredProp
  cases h_in₁ : e.id.inList omitted₁ with
  | true =>
    intro _
    have h_in₂ : e.id.inList omitted₂ = true := h_sub e.id h_in₁
    cases h_in₂' : e.id.inList omitted₂ with
    | true => exact True.intro
    | false =>
      have h_eq : false = true := h_in₂'.symm.trans h_in₂
      nomatch h_eq
  | false =>
    intro h_prop
    cases e.id.inList omitted₂ with
    | true => exact True.intro
    | false => exact h_prop

/-- **Theorem 4.4 (`unomitted_entry_holds_of_scoped_verification`):**
    For any obligation entry `e ∈ entries` whose ID is **not** in `omitted`
    (`e.id.inList omitted = false`),
    `ScopedVerificationResult policy omitted entries` unconditionally implies
    `e.prop`—regardless of whether other omitted entries in `entries` have false
    propositions! -/
theorem unomitted_entry_holds_of_scoped_verification
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (entries : List ObligationEntry)
    (e : ObligationEntry)
    (h_ver : ScopedVerificationResult policy omitted entries)
    (h_mem : e ∈ entries)
    (h_not_omitted : e.id.inList omitted = false) :
    e.prop := by
  have h_req : e.requiredProp omitted :=
    (allHold_map_iff (ObligationEntry.requiredProp omitted) entries).mp h_ver.2 e h_mem
  revert h_req
  unfold ObligationEntry.requiredProp
  cases h_in : e.id.inList omitted with
  | false =>
    intro h_prop
    exact h_prop
  | true =>
    have h_eq : true = false := h_in.symm.trans h_not_omitted
    nomatch h_eq

-- Now we prove that `ScopedVerificationResult` completely defeats both the
-- Cross-Function Explosion Trap (Theorem 3.2) and the Intra-Function Explosion
-- Trap (Theorem 3.3).

/-- Generate the per-function `ObligationEntry` list for a `ConcreteCapturedFn`. -/
def ConcreteCapturedFn.toObligationEntries
    (fn : ConcreteCapturedFn) : List ObligationEntry :=
  [ { id := ⟨fn.name, .assumeSourceWellFormed⟩
      prop := ConcreteMirLang.sem fn.s_mir ≤ ConcreteMirLang.WellFormedOn fn.pre },
    { id := ⟨fn.name, .assumePassCompiles "mir_to_x86"⟩
      prop := Compiles ConcreteMirLang ConcreteX86Lang idCodec.toMorphism
        fn.s_mir fn.t_x86 } ] ++
  fn.specs.zipIdx.map (fun ⟨spec, idx⟩ =>
    { id := ⟨fn.name, .assumeSourceSpec idx⟩
      prop := ConcreteMirLang.sem fn.s_mir ≤ spec })

/-- Scoped crate theorem collecting all functions' `ObligationEntry` items and
    gating them via `ScopedVerificationResult`. -/
def CrateTheoremScoped
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (functions : List ConcreteCapturedFn) : Prop :=
  ScopedVerificationResult policy omitted
    (functions.flatMap ConcreteCapturedFn.toObligationEntries)

/-- Scoped trust policy that permits omitting obligations **only** on `"fn_wip"`
    and strictly forbids omitting any obligation on `"fn_critical"`. -/
def wipOnlyScopedPolicy : ScopedTrustPolicy where
  allowOmission id := decide (id.fnId = "fn_wip")

/-- Helper: if `x.fnId = "fn_wip"`, then `x` cannot equal any obligation on
    `"fn_critical"`. -/
theorem wipOnly_disjoint_critical (x : ObligationId) (k : OmissionKind)
    (h_allow : wipOnlyScopedPolicy.allowOmission x = true) :
    decide (x = ⟨"fn_critical", k⟩) = false := by
  cases x with
  | mk fnId kind =>
    have h_eq : fnId = "fn_wip" := of_decide_eq_true h_allow
    subst h_eq
    rfl

/-- **Theorem 4.5 (`scoped_omission_isolates_buggy_fn`):**
    **Zero Cross-Function Contamination:**
    Under `wipOnlyScopedPolicy`, exempting `"fn_wip"` cannot help prove the
    buggy `"fn_critical"`! For **every** `omitted : List ObligationId`
    whatsoever (including `omitted := [⟨"fn_wip", .assumeSourceWellFormed⟩,
    ⟨"fn_wip", .assumePassCompiles "mir_to_x86"⟩]`),
    `CrateTheoremScoped wipOnlyScopedPolicy omitted
      crateWithBuggyWipAndBuggyCritical.functions`
    is **provably false**! -/
theorem scoped_omission_isolates_buggy_fn
    (omitted : List ObligationId) :
    ¬ CrateTheoremScoped wipOnlyScopedPolicy omitted
        crateWithBuggyWipAndBuggyCritical.functions := by
  intro h_crate
  let critWfEntry : ObligationEntry :=
    { id := ⟨"fn_critical", .assumeSourceWellFormed⟩
      prop := ConcreteMirLang.sem .alwaysUb ≤
        ConcreteMirLang.WellFormedOn (fun _ => True) }
  have h_not_in : critWfEntry.id.inList omitted = false := by
    cases h_b : critWfEntry.id.inList omitted with
    | false => rfl
    | true =>
      exact False.elim (allowed_of_inList wipOnlyScopedPolicy omitted
        critWfEntry.id h_crate.1 h_b
        (fun x hx => wipOnly_disjoint_critical x .assumeSourceWellFormed hx))
  have h_crit_prop : critWfEntry.prop :=
    unomitted_entry_holds_of_scoped_verification
      wipOnlyScopedPolicy omitted
      (crateWithBuggyWipAndBuggyCritical.functions.flatMap
        ConcreteCapturedFn.toObligationEntries)
      critWfEntry h_crate
      (.tail _ (.tail _ (.head _)))
      h_not_in
  obtain ⟨h_def, _⟩ := h_crit_prop qBoundary True.intro
  exact h_def

/-- Scoped trust policy permitting only the pass obligation on `"fn_partial"`,
    used to demonstrate intra-function isolation in Theorem 4.6. -/
def fnPartialPassOnlyPolicy : ScopedTrustPolicy where
  allowOmission id :=
    decide (id = ⟨"fn_partial", .assumePassCompiles "mir_to_x86"⟩)

/-- **Theorem 4.6 (`scoped_omission_isolates_intra_fn_obligations`):**
    **Zero Intra-Function Contamination:**
    Even within a single function `"fn_partial"`, omitting the broken pass
    obligation `⟨"fn_partial", .assumePassCompiles "mir_to_x86"⟩` (between
    `.retZero` and `.ubAtBoundary`) leaves the source specification obligation
    `⟨"fn_partial", .assumeSourceSpec 0⟩` completely unweakened, so the false
    source specification `ConcreteMirLang.Spec (fun _ _ => False)` remains
    strictly unprovable! -/
theorem scoped_omission_isolates_intra_fn_obligations
    (omitted : List ObligationId) :
    let fnPartial : ConcreteCapturedFn := {
      name := "fn_partial"
      s_mir := .retZero
      t_x86 := .ubAtBoundary
      specs := [ConcreteMirLang.Spec (fun _ => fun _ => False)]
    }
    ¬ ScopedVerificationResult fnPartialPassOnlyPolicy omitted
        fnPartial.toObligationEntries := by
  intro fnPartial h_ver
  let specEntry : ObligationEntry :=
    { id := ⟨"fn_partial", .assumeSourceSpec 0⟩
      prop := ConcreteMirLang.sem .retZero ≤
        ConcreteMirLang.Spec (fun _ _ => False) }
  have h_not_in : specEntry.id.inList omitted = false := by
    cases h_b : specEntry.id.inList omitted with
    | false => rfl
    | true =>
      refine False.elim (allowed_of_inList fnPartialPassOnlyPolicy omitted
        specEntry.id h_ver.1 h_b ?_)
      intro x hx
      have h_x : x = ⟨"fn_partial", .assumePassCompiles "mir_to_x86"⟩ :=
        of_decide_eq_true hx
      subst h_x
      rfl
  have h_spec_prop : specEntry.prop :=
    unomitted_entry_holds_of_scoped_verification
      fnPartialPassOnlyPolicy omitted fnPartial.toObligationEntries specEntry
      h_ver (.tail _ (.tail _ (.head _))) h_not_in
  obtain ⟨_, h_out⟩ := h_spec_prop qBoundary True.intro
  exact h_out 0 rfl

-- ============================================================================
-- Section 5: End-to-End 2-Pass Pipeline (`MirLang → AnSSALang → X86Lang`),
-- Universal `TCBModel` Unification, and Soundness Extraction for Verified Functions
-- in Partially Verified Crates
-- ============================================================================

/-- Multi-stage captured function over a 2-pass compiler pipeline
    `MirLang → AnSSALang → X86Lang` (`s_mir → s_ssa → t_x86`). -/
structure PipelineCapturedFn (MirLang AnSSALang X86Lang : Language) where
  name : String
  s_mir : MirLang.Prog
  s_ssa : AnSSALang.Prog
  t_x86 : X86Lang.Prog
  pre : MirLang.Query → Prop
  post : MirLang.Query → MirLang.Out → Prop

/-- Per-function, per-pass obligation entries for a 2-pass pipeline
    (`MirLang → AnSSALang → X86Lang`):
    1. `⟨fn.name, .assumeSourceSpec 0⟩`:
       `MirLang.sem fn.s_mir ≤ MirLang.SpecOn fn.pre fn.post`
    2. `⟨fn.name, .assumePassCompiles "mir_to_anssa"⟩`:
       `Compiles MirLang AnSSALang codec₁.toMorphism fn.s_mir fn.s_ssa`
    3. `⟨fn.name, .assumePassCompiles "anssa_to_x86"⟩`:
       `Compiles AnSSALang X86Lang codec₂.toMorphism fn.s_ssa fn.t_x86`. -/
def PipelineCapturedFn.toObligationEntries
    {MirLang AnSSALang X86Lang : Language}
    (codec₁ : BoundaryCodec MirLang AnSSALang)
    (codec₂ : BoundaryCodec AnSSALang X86Lang)
    (fn : PipelineCapturedFn MirLang AnSSALang X86Lang) :
    List ObligationEntry :=
  [ { id := ⟨fn.name, .assumeSourceSpec 0⟩
      prop := MirLang.sem fn.s_mir ≤ MirLang.SpecOn fn.pre fn.post },
    { id := ⟨fn.name, .assumePassCompiles "mir_to_anssa"⟩
      prop := Compiles MirLang AnSSALang codec₁.toMorphism fn.s_mir fn.s_ssa },
    { id := ⟨fn.name, .assumePassCompiles "anssa_to_x86"⟩
      prop := Compiles AnSSALang X86Lang codec₂.toMorphism fn.s_ssa fn.t_x86 } ]

/-- Predicate asserting that no obligation belonging to `fnId` is omitted in
    `omitted`. -/
def FnFullyVerified (omitted : List ObligationId) (fnId : String) : Prop :=
  ∀ kind : OmissionKind, (ObligationId.mk fnId kind).inList omitted = false

/-- **Theorem 5.1 (`pipeline_two_pass_scoped_soundness`):**
    If `ScopedVerificationResult policy omitted (fn.toObligationEntries codec₁ codec₂)`
    holds and `FnFullyVerified omitted fn.name` (none of `fn.name`'s obligations
    is omitted), then the compiled target `fn.t_x86` unconditionally satisfies
    the target specification and target well-formedness on the trusted `X86Lang`
    regardless of how `MirLang` or `AnSSALang` are defined in `theory/`. -/
theorem pipeline_two_pass_scoped_soundness
    {MirLang AnSSALang X86Lang : Language}
    (codec₁ : BoundaryCodec MirLang AnSSALang)
    (codec₂ : BoundaryCodec AnSSALang X86Lang)
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (fn : PipelineCapturedFn MirLang AnSSALang X86Lang)
    (h_ver : ScopedVerificationResult policy omitted
      (fn.toObligationEntries codec₁ codec₂))
    (h_full : FnFullyVerified omitted fn.name) :
    X86Lang.sem fn.t_x86 ≤
      X86Lang.SpecOn
        (fun q => fn.pre ((codec₁.comp codec₂).decompileQuery q))
        (fun q out =>
          fn.post ((codec₁.comp codec₂).decompileQuery q)
            ((codec₁.comp codec₂).decompileOut out)) ∧
    X86Lang.sem fn.t_x86 ≤
      X86Lang.WellFormedOn
        (fun q => fn.pre ((codec₁.comp codec₂).decompileQuery q)) := by
  let entries := fn.toObligationEntries codec₁ codec₂
  have h_src : MirLang.sem fn.s_mir ≤ MirLang.SpecOn fn.pre fn.post :=
    unomitted_entry_holds_of_scoped_verification policy omitted entries
      { id := ⟨fn.name, .assumeSourceSpec 0⟩
        prop := MirLang.sem fn.s_mir ≤ MirLang.SpecOn fn.pre fn.post }
      h_ver (.head _) (h_full (.assumeSourceSpec 0))
  have h_p1 : Compiles MirLang AnSSALang codec₁.toMorphism fn.s_mir fn.s_ssa :=
    unomitted_entry_holds_of_scoped_verification policy omitted entries
      { id := ⟨fn.name, .assumePassCompiles "mir_to_anssa"⟩
        prop := Compiles MirLang AnSSALang codec₁.toMorphism fn.s_mir fn.s_ssa }
      h_ver (.tail _ (.head _)) (h_full (.assumePassCompiles "mir_to_anssa"))
  have h_p2 : Compiles AnSSALang X86Lang codec₂.toMorphism fn.s_ssa fn.t_x86 :=
    unomitted_entry_holds_of_scoped_verification policy omitted entries
      { id := ⟨fn.name, .assumePassCompiles "anssa_to_x86"⟩
        prop := Compiles AnSSALang X86Lang codec₂.toMorphism fn.s_ssa fn.t_x86 }
      h_ver (.tail _ (.tail _ (.head _)))
      (h_full (.assumePassCompiles "anssa_to_x86"))
  exact multi_stage_proof_gated_compilation_eliminates_irs_from_tcb
    MirLang AnSSALang X86Lang codec₁ codec₂ fn.pre fn.post
    fn.s_mir fn.s_ssa fn.t_x86 h_src h_p1 h_p2

/-- Scoped crate theorem for a list of 2-pass pipeline functions. -/
def CrateTheoremPipelineScoped
    {MirLang AnSSALang X86Lang : Language}
    (codec₁ : BoundaryCodec MirLang AnSSALang)
    (codec₂ : BoundaryCodec AnSSALang X86Lang)
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (fns : List (PipelineCapturedFn MirLang AnSSALang X86Lang)) : Prop :=
  ScopedVerificationResult policy omitted
    (fns.flatMap (PipelineCapturedFn.toObligationEntries codec₁ codec₂))

/-- Concrete 2-pass example crate containing:
    1. `"fn_wip"`: a buggy work-in-progress function (`.ubAtBoundary`) whose
       source obligation `⟨"fn_wip", .assumeSourceSpec 0⟩` is explicitly omitted
       in `omittedWipSource`, and
    2. `"fn_verified"`: a safe, fully verified function (`.retZero`) with zero
       omitted obligations (`FnFullyVerified omittedWipSource "fn_verified"`). -/
abbrev ConcreteAnSSALang : Language := ConcreteMirLang

def idCodec1 : BoundaryCodec ConcreteMirLang ConcreteAnSSALang := idCodec
def idCodec2 : BoundaryCodec ConcreteAnSSALang ConcreteX86Lang := idCodec

def fnWipPipeline :
    PipelineCapturedFn ConcreteMirLang ConcreteAnSSALang ConcreteX86Lang where
  name := "fn_wip"
  s_mir := .ubAtBoundary
  s_ssa := .ubAtBoundary
  t_x86 := .ubAtBoundary
  pre := fun _ => True
  post := fun _ out => out = 0

def fnVerifiedPipeline :
    PipelineCapturedFn ConcreteMirLang ConcreteAnSSALang ConcreteX86Lang where
  name := "fn_verified"
  s_mir := .retZero
  s_ssa := .retZero
  t_x86 := .retZero
  pre := fun _ => True
  post := fun _ out => out = 0

def omittedWipSource : List ObligationId :=
  [⟨"fn_wip", .assumeSourceSpec 0⟩]

/-- **Theorem 5.2 (`partially_verified_crate_holds`):**
    When `"fn_wip"`'s source specification proof is explicitly omitted in
    `omittedWipSource` and approved by `wipOnlyScopedPolicy`, while
    `"fn_verified"` is proved in full, `CrateTheoremPipelineScoped` holds
    constructively with **zero axioms**. -/
theorem partially_verified_crate_holds :
    CrateTheoremPipelineScoped idCodec1 idCodec2 wipOnlyScopedPolicy
      omittedWipSource [fnWipPipeline, fnVerifiedPipeline] := by
  refine ⟨⟨rfl, True.intro⟩, ?_⟩
  refine ⟨True.intro, ?_, ?_, ?_, ?_, ?_, True.intro⟩
  · -- `"fn_wip"` pass 1 (`Compiles .ubAtBoundary .ubAtBoundary`): holds even on UB functions!
    intro q hDef
    exact ⟨hDef, fun out hout => hout⟩
  · -- `"fn_wip"` pass 2 (`Compiles .ubAtBoundary .ubAtBoundary`):
    intro q hDef
    exact ⟨hDef, fun out hout => hout⟩
  · -- `"fn_verified"` source spec (`.retZero ≤ SpecOn True (out = 0)`):
    intro q _
    exact ⟨True.intro, fun out hout => hout⟩
  · -- `"fn_verified"` pass 1 (`Compiles .retZero .retZero`):
    intro q hDef
    exact ⟨hDef, fun out hout => hout⟩
  · -- `"fn_verified"` pass 2 (`Compiles .retZero .retZero`):
    intro q hDef
    exact ⟨hDef, fun out hout => hout⟩

/-- **Theorem 5.3 (`extract_verified_fn_from_partially_verified_crate`):**
    Even in a partially verified crate where `"fn_wip"` has a real UB bug at
    `qBoundary` and has its source proof omitted in `omittedWipSource`,
    `CrateTheoremPipelineScoped` still unconditionally implies the target
    `ConcreteX86Lang` specification and UB-freedom theorem for the unomitted
    function `"fn_verified"`! -/
theorem extract_verified_fn_from_partially_verified_crate
    (h_crate :
      CrateTheoremPipelineScoped idCodec1 idCodec2 wipOnlyScopedPolicy
        omittedWipSource [fnWipPipeline, fnVerifiedPipeline]) :
    ConcreteX86Lang.sem fnVerifiedPipeline.t_x86 ≤
      ConcreteX86Lang.SpecOn (fun _ => True) (fun _ out => out = 0) ∧
    ConcreteX86Lang.sem fnVerifiedPipeline.t_x86 ≤
      ConcreteX86Lang.WellFormedOn (fun _ => True) := by
  have h_ver_fn :
      ScopedVerificationResult wipOnlyScopedPolicy omittedWipSource
        (fnVerifiedPipeline.toObligationEntries idCodec1 idCodec2) :=
    ⟨h_crate.1, h_crate.2.2.2.2⟩
  have h_full : FnFullyVerified omittedWipSource fnVerifiedPipeline.name := by
    intro kind
    rfl
  exact pipeline_two_pass_scoped_soundness idCodec1 idCodec2
    wipOnlyScopedPolicy omittedWipSource fnVerifiedPipeline h_ver_fn h_full

/-- **Unified Verification Envelope (`UnifiedCrateTheorem`):**
    Combines universal `TCBModel` quantification for uninterpreted
    environment/target assumptions (`envAssumptions : Model → List Prop`, placed
    on the left of `→` only when accompanied by a constructive realizability
    witness `∃ M : Model, AllHold (envAssumptions M)`) with positive
    per-obligation scoping (`ScopedVerificationResult`) for concrete-program
    proof omissions. -/
def UnifiedCrateTheorem
    {Model : Type}
    (envAssumptions : Model → List Prop)
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (entries : List ObligationEntry) : Prop :=
  AllHold (omitted.map policy.isAllowed) ∧
  (∀ M : Model,
    AllHold (envAssumptions M) →
      AllHold (entries.map (ObligationEntry.requiredProp omitted)))

/-- **Theorem 5.4 (`unified_crate_theorem_non_vacuous_and_isolated`):**
    When `envAssumptions` admits a constructive realizability model `M₀`
    (`AllHold (envAssumptions M₀)`), `UnifiedCrateTheorem` reduces directly to
    `ScopedVerificationResult policy omitted entries`—preserving both
    non-vacuity of `envAssumptions` and strict per-obligation isolation of
    `omitted`. -/
theorem unified_crate_theorem_non_vacuous_and_isolated
    {Model : Type}
    (envAssumptions : Model → List Prop)
    (M₀ : Model)
    (h_realizable : AllHold (envAssumptions M₀))
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (entries : List ObligationEntry)
    (h_unified : UnifiedCrateTheorem envAssumptions policy omitted entries) :
    ScopedVerificationResult policy omitted entries :=
  ⟨h_unified.1, h_unified.2 M₀ h_realizable⟩

end Anneal.ProofGatedTrustPolicy

#print axioms Anneal.ProofGatedTrustPolicy.BoundaryCodec.monotone_toMorphism
#print axioms Anneal.ProofGatedTrustPolicy.BoundaryCodec.toMorphism_specOn
#print axioms Anneal.ProofGatedTrustPolicy.spurious_ir_ub_blocks_source_obligation
#print axioms Anneal.ProofGatedTrustPolicy.omitted_ir_ub_blocks_pass_obligation
#print axioms Anneal.ProofGatedTrustPolicy.omitted_ir_outcome_blocks_pass_obligation
#print axioms Anneal.ProofGatedTrustPolicy.proof_gated_compilation_eliminates_ir_from_tcb
#print axioms Anneal.ProofGatedTrustPolicy.multi_stage_proof_gated_compilation_eliminates_irs_from_tcb
#print axioms Anneal.ProofGatedTrustPolicy.transparent_buggy_wip_assumption_is_false
#print axioms Anneal.ProofGatedTrustPolicy.global_antecedent_omission_explodes_crate
#print axioms Anneal.ProofGatedTrustPolicy.intra_function_antecedent_omission_explodes_other_obligations
#print axioms Anneal.ProofGatedTrustPolicy.scoped_zeroTrust_forces_empty_omitted
#print axioms Anneal.ProofGatedTrustPolicy.scoped_zeroTrust_iff_allHold
#print axioms Anneal.ProofGatedTrustPolicy.scoped_verification_antitone_in_omitted
#print axioms Anneal.ProofGatedTrustPolicy.unomitted_entry_holds_of_scoped_verification
#print axioms Anneal.ProofGatedTrustPolicy.scoped_omission_isolates_buggy_fn
#print axioms Anneal.ProofGatedTrustPolicy.scoped_omission_isolates_intra_fn_obligations
#print axioms Anneal.ProofGatedTrustPolicy.pipeline_two_pass_scoped_soundness
#print axioms Anneal.ProofGatedTrustPolicy.partially_verified_crate_holds
#print axioms Anneal.ProofGatedTrustPolicy.extract_verified_fn_from_partially_verified_crate
#print axioms Anneal.ProofGatedTrustPolicy.unified_crate_theorem_non_vacuous_and_isolated
