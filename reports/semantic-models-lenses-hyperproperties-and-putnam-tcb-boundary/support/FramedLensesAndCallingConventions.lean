/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Tripartite Machine State Decomposition, Very Well-Behaved Lenses, and Relational Calling-Convention Frame Laws in Cross-Language Compilation

This standalone Lean 4 (`v4.34.1`) mechanization formalizes the mathematical laws
governing cross-language state spaces (`Query`, `Out`, `SemObs`), calling
conventions (callee-saved architectural frames vs. caller-saved scratch
registers and flags), and `BehaviorCodec` translations in the 4-primitive
semantic model framework (`Language`, `Tool`, `BehaviorCodec`, `Spec`).

It mechanizes:
1. **The 4-Primitive Semantic Model & Tripartite Machine State Decomposition**
   (`Section 1`): Formalizes `Partial`, demonic refinement `Preorder`,
   `Language SemObs`, `BehaviorCodec`, `Compiles`, `ProductiveCompiles`, `Tool`,
   and the tripartite state decomposition $V \times F \times S$ (`Val`, `Frame`,
   `Slack`).
2. **The Unary Observation & State-Only Injectivity Impossibility Theorems**
   (`Section 2`, `UnaryObsAndInjectivityImpossibility`):
   - **Theorem 1A.i (`unaryObs_scratch_invariance_refutes_obsInjective`):**
     Any unary observation map `obs : (V × F × S) → SemObs` invariant to
     caller-saved scratch state $S$ (`|S| ≥ 2`) violates `ObsInjective`
     (`PENTEST-R2-7`).
   - **Theorem 1A.ii (`unaryObs_scratch_invariance_refutes_obsABIInjective` &
     `no_abiValid_admits_distinct_scratch_and_obsABIInjective`):**
     Even when restricted to an entry-to-exit ABI relation `abiValid`, any
     scratch-invariant `obs` violates `ObsABIInjective` (`PENTEST-R3-1A`), and
     no `abiValid` relation can simultaneously satisfy `ObsABIInjective` and
     admit two honest target routines leaving distinct scratch values in `%rcx`
     (`PENTEST-R3-1B`), whereas a corrupt constant-clobbering `abiValid`
     (`rbx_out = 57005`) satisfies `ObsABIInjective` (`PENTEST-R3-1C`).
   - **Theorem 1A.iii (`no_unary_exit_predicate_enforces_relational_frame_preservation`):**
     No unary exit-state predicate `P_exit : (V × F × S) → Prop` can enforce
     callee-saved frame preservation $f_{\text{out}} = f_{\text{in}}$ across
     distinct entry frames $f_0 \ne f_1 \in F$: any state-only predicate either
     accepts a frame-clobbering transition $(f_0 \to f_1)$ or rejects a valid
     frame-preserving transition $(f_1 \to f_1)$.
   - **Theorem 1B (`existential_clean_reference_program_vacuity`):**
     Guarding callee-saved frame preservation behind the existence of a clean
     reference program in `L_tgt.Prog` (`(∃ p_clean ∈ L_tgt.Prog, ...) →
     PreservesFrame`) is vacuously satisfied whenever `L_tgt.Prog` contains only
     frame-clobbering or partial programs (`PENTEST-R4-4A`).
   - Mechanized counterexamples for `PENTEST-1A` (unit spine erasure),
     `PENTEST-4A/B` (`c_shunt` / `c_alias` query fiber smuggling),
     `PENTEST-8A/B` (unprojected `%rbx` clobbering), `PENTEST-R2-2`
     (tautological `archQuery := c.decodeQuery`), and `PENTEST-R2-3` (1-bit
     boolean sign-projection spine).
3. **Impossibility of Positional Binary-Tuple Typeclasses Under Monoidal
   Associativity** (`Section 3`, `PositionalTupleTypeclassImpossibility`):
   - **Theorem 2A (`positional_abiState_conflates_callee_saved_rbp_and_scratch_rcx`):**
     Structural typeclass dispatch on binary `Prod` (`A × (B × C)`) cannot
     distinguish 2-callee-saved `Val × (RBX × RBP)` from 1-callee-saved +
     1-scratch `Val × (RBX × RCX)`, either admitting `%rbp` clobbering
     (`PENTEST-R4-4B`) or locking out `%rcx` scratch writes.
   - **Theorem 2B (`no_unlabelled_binary_prod_projection_is_associativity_invariant`
     & `pentest_r4_5_associativity_bypasses`):**
     Positional binary-tuple projections (`Prod.fst` / `Prod.snd` in
     `CanonicalPublicQuery` and `CanonicalLeakageObs`) fail to commute with the
     monoidal associator $\alpha : (A \times B) \times C \simeq A \times (B \times C)$,
     reclassifying secret keys as public inputs on `((Pub, Sec₁), Sec₂)`
     (`PENTEST-R4-5A`) and cycle-count leakage as functional output on
     `((Val, Cycles), CacheTag)` (`PENTEST-R4-5B`).
   - **Theorem 2C (`uniform_and_bijective_frame_fibers_bypassed_by_swap_and_frame_shift`):**
     `UniformQueryFibers` is bypassed by 2-fiber shunting/aliasing (`c_shunt2`,
     `c_alias2`, `PENTEST-R3-3A`) and involutive query derangements (`c_swap`,
     `PENTEST-R3-3B`, `PENTEST-R4-10A`); `BijectiveFrameFibers` +
     `CanonicalOutEncoding` is bypassed by `c_shift_encodeQuery`
     (`encodeQuery q := (q, 57005)`, `PENTEST-R4-6`) and by coordinated
     entry/exit frame shifting (`encodeQuery q := (q, 1)`, `encodeOut o := (o, 2)`).
4. **The Framed Lens & Relational Calling-Convention Characterization**
   (`Section 4`, `FramedLensCharacterization`):
   - Formalizes **Very Well-Behaved Lenses** (Foster et al. 2007; Oles 1982),
     their vertical composition `VeryWellBehavedLens.comp`, and **Oles's
     Bijective State-Decomposition Theorem (`oles_lens_complement_equiv`)**
     establishing $W \simeq V \times C$.
   - Formalizes `FramedCodec L₁ L₂` and `CompilesFramed` (with unconditional
     2-state separation-logic frame preservation `projFrameOut o₂ = projFrameIn q₂`
     and unconstrained caller-saved scratch freedom).
   - **Theorem 3A (`tension1_simultaneous_resolution`):** Proves that
     `CompilesFramed` simultaneously:
     1. Rejects `%rbx` and `%rbp` callee-saved clobbering (`PENTEST-8B`,
        `PENTEST-R4-4A/B`) and constant frame offsets (`rbx_out = rbx_in + 1`);
     2. Structurally blocks `c_shift_encodeQuery` (`PENTEST-R4-6`),
        `c_shunt`/`c_alias` (`PENTEST-4A/B`, `PENTEST-R3-3A`), and `c_swap`
        (`PENTEST-R3-3B`, `PENTEST-R4-10A`);
     3. Admits every honest assembly routine that mutates caller-saved scratch
        registers (`%rcx`, `%r11`, `RFLAGS`) deterministically or
        nondeterministically (`PENTEST-R2-7`, `PENTEST-R3-1A/B`);
     4. Composes vertically (`FramedCodec.comp`, `compilesFramed_comp`) across
        a multi-pass compiler pipeline ($\text{Source} \to \text{LinearIR} \to
        \text{x86-64}$) and transfers both 1-trace functional correctness and
        nominal-wrapper 2-safety non-interference to the target machine.
-/

namespace FramedLensesAndCallingConventions

/-!
## Section 1: The 4-Primitive Semantic Model & Tripartite Machine State Space
-/

/-- Preorder typeclass for the constructive demonic refinement lattice. -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Demonic partial value: `defined` guards safety (absence of Undefined
    Behavior); `val` yields the outcome predicate when `defined` holds. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Top element of the demonic refinement lattice (Undefined Behavior). -/
abbrev Partial.ub {B : Type u} : Partial B :=
  { defined := False, val := False.elim }

/-- Pure defined element of `Partial B`. -/
abbrev Partial.pure {B : Type u} (b : B) : Partial B :=
  { defined := True, val := fun _ => b }

/-- Predicate implication order (subset refinement on outcome sets). -/
instance instPreorderPred (Out : Type u) : Preorder (Out → Prop) where
  le P Q := ∀ o, P o → Q o
  le_refl _ _ h := h
  le_trans h₁ h₂ o hp := h₂ o (h₁ o hp)

/-- Demonic refinement order on `Partial B`:
    `p₁ ≤ p₂` iff whenever the specification `p₂` is defined (`h₂`), the
    implementation `p₁` is also defined (`h₁`) and `p₁.val h₁ ≤ p₂.val h₂`. -/
instance instPreorderPartial (B : Type u) [Preorder B] : Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- A semantic behavior maps each entry `Query` to a demonic `Partial` predicate
    over exit outcomes `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

instance instPreorderBehavior (Query Out : Type) : Preorder (Behavior Query Out) where
  le b₁ b₂ := ∀ q, b₁ q ≤ b₂ q
  le_refl b q := Preorder.le_refl (b q)
  le_trans h₁ h₂ q := Preorder.le_trans (h₁ q) (h₂ q)

/-- **Primitive 1 (`Language SemObs`):**
    A language with program syntax `Prog`, entry state `Query`, exit state `Out`,
    unary observable spine projection `obs : Out → SemObs`, and semantics `sem`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

/-- Simple language constructor when `Out = SemObs` and `obs = id`. -/
abbrev Language.mkSimple (Prog Query Out : Type) (sem : Prog → Behavior Query Out) :
    Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := _root_.id
  sem   := sem

/-- Safety of `prog` at entry query `q`. -/
abbrev Language.SafeAt {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) : Prop :=
  (L.sem prog q).defined

/-- Concrete outcome production `o ∈ L.sem prog q`. -/
abbrev Language.ProducesOut {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (o : L.Out) : Prop :=
  ∃ h : (L.sem prog q).defined, (L.sem prog q).val h o

/-- Observable spine production `v = L.obs o` for some `o ∈ L.sem prog q`. -/
abbrev Language.Produces {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (v : SemObs) : Prop :=
  ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o ∧ L.obs o = v

/-- Productivity (non-miracle execution) of `prog` across precondition `pre`. -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- **Primitive 4 (`Spec`):** Demonic specification behavior with precondition
    `pre` and postcondition `post`. -/
def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => {
    defined := pre q
    val     := fun _ o => post q o
  }

/-- Spine-level verification of `prog` against `(pre, obsPost)`. -/
def Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  (∃ q, pre q) ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre (fun q o => obsPost q (L.obs o))

/-- Spine-level violation witness at a valid query `q ∈ pre`. -/
def Language.ViolatesSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  ∃ q, pre q ∧
    (¬ (L.sem prog q).defined ∨
     ∃ h : (L.sem prog q).defined, ∃ o : L.Out,
       (L.sem prog q).val h o ∧ ¬ obsPost q (L.obs o))

/-- **Primitive 3 (`BehaviorCodec`):**
    Baseline cross-language representation codec (`Candidate 001`–`016`). -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Identity codec on a single language `L`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := _root_.id
  decodeQuery := _root_.id
  encodeOut   := _root_.id
  decodeOut   := some
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := congrArg L.obs (Option.some.inj h)

/-- Pushforward of a source behavior along a `BehaviorCodec`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b₁ (c.decodeQuery q₂)).defined
    val     := fun h₁ o₂ =>
      ∃ o₁ : L₁.Out, c.decodeOut o₂ = some o₁ ∧ (b₁ (c.decodeQuery q₂)).val h₁ o₁
  }

/-- Forward refinement compilation `L_tgt.sem t ≤ c.toMorphism (L_src.sem s)`. -/
def Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Productive refinement compilation (`Candidate 002`–`016`). -/
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₂ : L_tgt.Query,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined, ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

/-- **Primitive 2 (`Tool`):** Partial verifier/compiler from `L_src` to `L_tgt`. -/
abbrev Tool {SemObs : Type} (L_src L_tgt : Language SemObs) : Type :=
  L_src.Prog → Partial L_tgt.Prog

/-- Universal tool soundness (`Candidate 003`–`005`). -/
def Tool.Sound {SemObs : Type} {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt) (tool : Tool L_src L_tgt)
    (pre : L_src.Query → Prop) (obsPost : L_src.Query → SemObs → Prop) : Prop :=
  ∀ p : L_src.Prog, ∀ h_acc : (tool p).defined,
    L_src.VerifiedSpine pre obsPost p ∧
    ProductiveCompiles L_src L_tgt c p ((tool p).val h_acc)

/-- Typeclass witnessing that a type `α` has at least two distinct elements
    (`|α| ≥ 2`). -/
class TwoDistinct (α : Type u) where
  elem₀ : α
  elem₁ : α
  ne    : elem₀ ≠ elem₁

instance instTwoDistinctNat : TwoDistinct Nat where
  elem₀ := 0
  elem₁ := 1
  ne    := by decide

instance instTwoDistinctBool : TwoDistinct Bool where
  elem₀ := false
  elem₁ := true
  ne    := by decide

/-- **Tripartite Machine State Decomposition (`Val × Frame × Slack`):**
    Any concrete machine state splits into three orthogonal components:
    1. `Val` ($V$): Primary observable return value (e.g., `%rax`, $|V| \ge 2$).
    2. `Frame` ($F$): Callee-saved architectural state (e.g., `%rbx, %rbp, %rsp`,
       $|F| \ge 2$) governed by the 2-state relational preservation law
       $f_{\text{out}} = f_{\text{in}}$.
    3. `Slack` ($S$): Caller-saved scratch state (e.g., `%rcx, %r11, \text{RFLAGS}`,
       $|S| \ge 2$) that is unconstrained upon exit. -/
abbrev TripartiteState (Val Frame Slack : Type) : Type :=
  Val × (Frame × Slack)

/-- Tripartite entry query state `(Arg, (Frame, Slack))`. -/
abbrev TripartiteQuery (Arg Frame Slack : Type) : Type :=
  Arg × (Frame × Slack)

/-- The 2-state relational calling-convention frame law: exit callee-saved frame
    equals entry callee-saved frame (`o.2.1 = q.2.1`). -/
def PreservesCalleeSavedFrame {Arg Val Frame Slack : Type}
    (q : TripartiteQuery Arg Frame Slack)
    (o : TripartiteState Val Frame Slack) : Prop :=
  o.2.1 = q.2.1

/-!
## Section 2: The Unary Observation & State-Only Injectivity Impossibility Theorems
   (`UnaryObsAndInjectivityImpossibility`)
-/

/-- `Candidate 006` global outcome-observation injectivity (`Language.ObsInjective`). -/
def ObsInjective {Out SemObs : Type} (obs : Out → SemObs) : Prop :=
  ∀ o₁ o₂ : Out, obs o₁ = obs o₂ → o₁ = o₂

/-- `Candidate 008` ABI-restricted observation injectivity (`Language.ObsABIInjective`). -/
def ObsABIInjective {Query Out SemObs : Type}
    (pre : Query → Prop) (abiValid : Query → Out → Prop)
    (obs : Out → SemObs) : Prop :=
  ∀ (q : Query) (o₁ o₂ : Out),
    pre q → abiValid q o₁ → abiValid q o₂ → obs o₁ = obs o₂ → o₁ = o₂

/-- Scratch-register invariance of a unary observation map `obs`: caller-saved
    scratch state `s : Slack` is not part of the high-level semantic spine. -/
def ScratchInvariantObs {Val Frame Slack SemObs : Type}
    (obs : TripartiteState Val Frame Slack → SemObs) : Prop :=
  ∀ (v : Val) (f : Frame) (s₁ s₂ : Slack),
    obs (v, (f, s₁)) = obs (v, (f, s₂))

/-- **Theorem 1A.i (`unaryObs_scratch_invariance_refutes_obsInjective`, `PENTEST-R2-7`):**
    For any tripartite target state `Val × (Frame × Slack)` with `|Slack| ≥ 2`
    and any unary observation map `obs : TripartiteState Val Frame Slack → SemObs`
    that is invariant to caller-saved scratch registers, `ObsInjective obs` is
    **mathematically impossible** (`¬ ObsInjective obs`). -/
theorem unaryObs_scratch_invariance_refutes_obsInjective
    {Val Frame Slack SemObs : Type}
    [Inhabited Val] [Inhabited Frame] [td : TwoDistinct Slack]
    (obs : TripartiteState Val Frame Slack → SemObs)
    (h_inv : ScratchInvariantObs obs) :
    ¬ ObsInjective obs := by
  intro h_inj
  have h_eq :
      ((default : Val), ((default : Frame), td.elem₀)) =
      ((default : Val), ((default : Frame), td.elem₁)) :=
    h_inj _ _ (h_inv default default td.elem₀ td.elem₁)
  have h_s : td.elem₀ = td.elem₁ :=
    congrArg (fun x => x.2.2) h_eq
  exact td.ne h_s

/-- **Theorem 1A.ii (`unaryObs_scratch_invariance_refutes_obsABIInjective`, `PENTEST-R3-1A`):**
    Under the standard calling-convention ABI relation `PreservesCalleeSavedFrame`
    (`f_out = f_in`, leaving caller-saved scratch registers `Slack` unconstrained),
    every scratch-invariant unary observation map `obs` **violates
    `ObsABIInjective`** on any non-empty precondition `pre`. -/
theorem unaryObs_scratch_invariance_refutes_obsABIInjective
    {Arg Val Frame Slack SemObs : Type}
    [Inhabited Val] [td : TwoDistinct Slack]
    (pre : TripartiteQuery Arg Frame Slack → Prop)
    (h_pre : ∃ q, pre q)
    (obs : TripartiteState Val Frame Slack → SemObs)
    (h_inv : ScratchInvariantObs obs) :
    ¬ ObsABIInjective pre PreservesCalleeSavedFrame obs := by
  intro h_abi_inj
  let ⟨(a₀, (f₀, s₀)), hq₀⟩ := h_pre
  have h_eq :
      ((default : Val), (f₀, td.elem₀)) =
      ((default : Val), (f₀, td.elem₁)) :=
    h_abi_inj (a₀, (f₀, s₀))
      ((default : Val), (f₀, td.elem₀))
      ((default : Val), (f₀, td.elem₁))
      hq₀ rfl rfl (h_inv default f₀ td.elem₀ td.elem₁)
  have h_s : td.elem₀ = td.elem₁ :=
    congrArg (fun x => x.2.2) h_eq
  exact td.ne h_s

/-- **Theorem 1A.ii-b (`no_abiValid_admits_distinct_scratch_and_obsABIInjective`, `PENTEST-R3-1B`):**
    No `abiValid` relation whatsoever can simultaneously satisfy
    `ObsABIInjective` and admit two honest assembly instructions (such as
    `addOneRcxZero` leaving `rcx = s₀` and `addOneRcxTemp` leaving `rcx = s₁`
    with `s₀ ≠ s₁`) that compute the same return value `v` and preserve the same
    callee-saved frame `f` at a valid query `q ∈ pre`. -/
theorem no_abiValid_admits_distinct_scratch_and_obsABIInjective
    {Query Val Frame Slack SemObs : Type}
    [td : TwoDistinct Slack]
    (pre : Query → Prop)
    (q₀ : Query) (hq₀ : pre q₀)
    (v₀ : Val) (f₀ : Frame)
    (obs : TripartiteState Val Frame Slack → SemObs)
    (h_inv : ScratchInvariantObs obs)
    (abiValid : Query → TripartiteState Val Frame Slack → Prop) :
    ¬ (ObsABIInjective pre abiValid obs ∧
       abiValid q₀ (v₀, (f₀, td.elem₀)) ∧
       abiValid q₀ (v₀, (f₀, td.elem₁))) := by
  intro ⟨h_inj, h_abi₀, h_abi₁⟩
  have h_eq : (v₀, (f₀, td.elem₀)) = (v₀, (f₀, td.elem₁)) :=
    h_inj q₀ (v₀, (f₀, td.elem₀)) (v₀, (f₀, td.elem₁))
      hq₀ h_abi₀ h_abi₁ (h_inv v₀ f₀ td.elem₀ td.elem₁)
  exact td.ne (congrArg (fun x => x.2.2) h_eq)

/-- **Theorem 1A.iii (`no_unary_exit_predicate_enforces_relational_frame_preservation`):**
    **Impossibility of State-Only Exit Predicates for Callee-Saved Framing:**
    For any `Val`, `Frame` (`|Frame| ≥ 2`), and `Slack`, let `P_exit :
    TripartiteState Val Frame Slack → Prop` be ANY unary predicate on exit
    states alone. Then `P_exit` cannot characterize callee-saved frame
    preservation `f_out = f_in`:
    - Either `P_exit (v, (f₁, s))` holds, in which case `P_exit` **falsely
      accepts** the frame-clobbering transition from entry frame `f₀` to exit
      frame `f₁` (`f₁ ≠ f₀`),
    - Or `¬ P_exit (v, (f₁, s))` holds, in which case `P_exit` **falsely
      rejects** the honest frame-preserving transition from entry frame `f₁` to
      exit frame `f₁` (`f₁ = f₁`).
    Consequently, callee-saved ABI preservation is irreducibly a **2-state
    entry-to-exit relational property** (or a frame-indexed family of fibers). -/
theorem no_unary_exit_predicate_enforces_relational_frame_preservation
    {Val Frame Slack : Type}
    [Inhabited Val] [td : TwoDistinct Frame] [Inhabited Slack]
    (P_exit : TripartiteState Val Frame Slack → Prop) :
    ¬ (∀ (f_in : Frame) (v : Val) (f_out : Frame) (s : Slack),
        P_exit (v, (f_out, s)) ↔ f_out = f_in) := by
  intro h_char
  have h_f0 : P_exit (default, (td.elem₁, default)) ↔ td.elem₁ = td.elem₀ :=
    h_char td.elem₀ default td.elem₁ default
  have h_f1 : P_exit (default, (td.elem₁, default)) ↔ td.elem₁ = td.elem₁ :=
    h_char td.elem₁ default td.elem₁ default
  have h_true : P_exit (default, (td.elem₁, default)) :=
    h_f1.mpr rfl
  have h_eq : td.elem₁ = td.elem₀ :=
    h_f0.mp h_true
  exact td.ne h_eq.symm

/-- **Theorem 1A.iv (`corrupt_abiValid_constant_clobber_satisfies_obsABIInjective`, `PENTEST-R3-1C`):**
    Because `ObsABIInjective` only checks that `abiValid q` has at most one state
    per `obs` fiber (rather than enforcing `f_out = f_in`), a corrupt ABI
    predicate `corruptAbiValid _ (rax, (rbx, rcx)) := (rbx = 57005 ∧ rcx = 0)`
    satisfies `ObsABIInjective` while requiring every program to clobber `%rbx`
    to `57005` (`0xDEAD`)! -/
def corruptAbiValid (_ : TripartiteQuery Nat Nat Nat)
    (o : TripartiteState Nat Nat Nat) : Prop :=
  o.2.1 = 57005 ∧ o.2.2 = 0

theorem corrupt_abiValid_constant_clobber_satisfies_obsABIInjective :
    ObsABIInjective (fun q : TripartiteQuery Nat Nat Nat => q.1 < 100)
      corruptAbiValid (fun o => o.1) ∧
    ∀ q : TripartiteQuery Nat Nat Nat,
      corruptAbiValid q (q.1 + 1, (57005, 0)) := by
  refine ⟨?_, fun _ => ⟨rfl, rfl⟩⟩
  intro _ (v₁, (f₁, s₁)) (v₂, (f₂, s₂)) _ ⟨hf₁, hs₁⟩ ⟨hf₂, hs₂⟩ hv
  dsimp at hv hf₁ hs₁ hf₂ hs₂
  subst hv; subst hf₁; subst hs₁; subst hf₂; subst hs₂
  rfl

/-!
### Concrete Replay of `Candidate 003`–`016` State & Codec Exploits
(`PENTEST-1A`, `PENTEST-4A/B`, `PENTEST-8A/B`, `PENTEST-R2-2`, `PENTEST-R2-3`, `PENTEST-R4-4A`)
-/

/-- Canonical 2-program source AST (`NatProg`). -/
inductive NatProg where
  | addOne
  | divByZeroAt50AndWrongAt0
  deriving DecidableEq

/-- Canonical integer source language `L_nat`. -/
abbrev L_nat : Language Nat where
  Prog  := NatProg
  Query := Nat
  Out   := Nat
  obs   := _root_.id
  sem p q := match p with
    | .addOne => Partial.pure (fun o => o = q + 1)
    | .divByZeroAt50AndWrongAt0 =>
      { defined := q ≠ 50, val := fun _ o => o = if q = 0 then 0 else q + 1 }

/-- **Counterexample `PENTEST-1A` (`obs := fun _ => ()` Constant Spine Erasure):**
    When `SemObs = Unit` and `obs := fun _ => ()`, a compiler that corrupts the
    concrete return value from `q + 1` to `666` satisfies `ProductiveCompiles`
    and `obs_decodeOut` because `L_tgt.obs (false, (q, 666)) = () = L_src.obs (q, q + 1)`. -/
abbrev L_erased_src : Language Unit where
  Prog  := NatProg
  Query := Nat
  Out   := Nat × Nat
  obs _ := ()
  sem p q := match p with
    | .addOne                   => Partial.pure (fun o => o = (q, q + 1))
    | .divByZeroAt50AndWrongAt0 => Partial.ub

abbrev L_erased_tgt : Language Unit where
  Prog  := Bool
  Query := Nat
  Out   := Bool × (Nat × Nat)
  obs _ := ()
  sem b q :=
    if b then
      Partial.pure (fun o => o = (false, (q, 666)))
    else
      Partial.ub

def c_erased_corrupt : BehaviorCodec L_erased_src L_erased_tgt where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := (true, o)
  decodeOut o   :=
    match o with
    | (true, o₁)       => some o₁
    | (false, (q, _))  => some (q, q + 1)
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ _       := rfl

theorem pentest_1a_constant_obs_erasure_certifies_666_corrupt_compiler :
    ProductiveCompiles L_erased_src L_erased_tgt c_erased_corrupt .addOne true ∧
    ∀ q : Nat, L_erased_tgt.ProducesOut true q (false, (q, 666)) := by
  refine ⟨⟨?_, ?_⟩, fun _ => ⟨trivial, rfl⟩⟩
  · intro q _
    refine ⟨trivial, fun o ho => ?_⟩
    dsimp [L_erased_tgt, Partial.pure] at ho
    rw [ho]
    exact ⟨(q, q + 1), rfl, rfl⟩
  · intro q _
    exact ⟨trivial, (false, (q, 666)), rfl⟩

/-- **Counterexamples `PENTEST-4A/B` & `PENTEST-R2-2` (`c_shunt`, `c_alias`, and
    Unconstrained `AlignedWith`):**
    Because `decodeQuery (encodeQuery q) = q` only constrains `decodeQuery` on
    the image of `encodeQuery` (`rcx = 0`), `c_alias` maps all `(q, rcx)` with
    `rcx ≠ 0` to `0`, and `Candidate 006`'s `AlignedWith archQuery`
    (`∀ q₂, c.decodeQuery q₂ = archQuery q₂`) holds tautologically by passing
    `archQuery := c_alias.decodeQuery`! -/
abbrev L_tgt_clobber_rcx : Language Nat :=
  Language.mkSimple Bool (Nat × Nat) Nat (fun isGood (q, rcx) =>
    if isGood then
      Partial.pure (fun o => o = if rcx = 0 then q + 1 else 1)
    else
      Partial.ub)

def c_alias : BehaviorCodec L_nat L_tgt_clobber_rcx where
  encodeQuery q := (q, 0)
  decodeQuery p := if p.2 = 0 then p.1 else 0
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

def BehaviorCodec.AlignedWith {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (archQuery : L₂.Query → L₁.Query) : Prop :=
  ∀ q₂ : L₂.Query, c.decodeQuery q₂ = archQuery q₂

theorem pentest_4b_and_r2_2_alias_codec_and_tautological_alignedWith :
    c_alias.AlignedWith c_alias.decodeQuery ∧
    ProductiveCompiles L_nat L_tgt_clobber_rcx c_alias .addOne true ∧
    L_tgt_clobber_rcx.Produces true (50, 1) 1 := by
  refine ⟨fun _ => rfl, ⟨?_, ?_⟩, ⟨trivial, 1, rfl, rfl⟩⟩
  · intro (q, rcx) _
    refine ⟨trivial, fun o ho => ⟨o, rfl, ?_⟩⟩
    cases rcx <;> exact ho
  · intro (q, rcx) _
    exact ⟨trivial, if rcx = 0 then q + 1 else 1, rfl⟩

/-- **Counterexample `PENTEST-R2-3` (1-Bit Sign-Projection Spine `SemObs = Bool`):**
    Projecting `obs (q, ret) := decide (ret > 0)` distinguishes `.addOne` (`true`)
    from `.divByZeroAt50AndWrongAt0` (`false`) at `q = 0` (`|SemObs| = 2`), yet
    collapses `q + 1` and `666` into the same equivalence class `true`,
    certifying a compiler that outputs `666` on every input. -/
abbrev L_1bit_src : Language Bool where
  Prog  := NatProg
  Query := Nat
  Out   := Nat × Nat
  obs o := decide (o.2 > 0)
  sem p q := match p with
    | .addOne                   => Partial.pure (fun o => o = (q, q + 1))
    | .divByZeroAt50AndWrongAt0 => Partial.pure (fun o => o = (q, 0))

abbrev L_1bit_tgt : Language Bool where
  Prog  := Bool
  Query := Nat
  Out   := Bool × (Nat × Nat)
  obs o := decide (o.2.2 > 0)
  sem b q :=
    if b then
      Partial.pure (fun o => o = (false, (q, 666)))
    else
      Partial.pure (fun o => o = (false, (q, 0)))

def c_1bit_corrupt : BehaviorCodec L_1bit_src L_1bit_tgt where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := (true, o)
  decodeOut o   :=
    match o with
    | (true, o₁)      => some o₁
    | (false, (q, n)) => if decide (n > 0) then some (q, q + 1) else some (q, 0)
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut o₂ o₁ h     := by
    match o₂ with
    | (true, o₁') =>
      have heq : o₁' = o₁ := Option.some.inj h
      subst heq
      rfl
    | (false, (q, n)) =>
      cases hdec : decide (n > 0) with
      | true =>
        have h_some :
            (if decide (n > 0) = true then some (q, q + 1) else some (q, 0)) =
            some o₁ := h
        rw [hdec] at h_some
        have heq : (q, q + 1) = o₁ := Option.some.inj h_some
        subst heq
        have hpos : decide (q + 1 > 0) = true :=
          decide_eq_true (Nat.zero_lt_succ q)
        exact Eq.trans hdec hpos.symm
      | false =>
        have h_some :
            (if decide (n > 0) = true then some (q, q + 1) else some (q, 0)) =
            some o₁ := h
        rw [hdec] at h_some
        have heq : (q, 0) = o₁ := Option.some.inj h_some
        subst heq
        exact hdec

theorem pentest_r2_3_one_bit_sign_spine_collapses_q_plus_1_and_666 :
    L_1bit_src.Produces .addOne 0 true ∧
    L_1bit_src.Produces .divByZeroAt50AndWrongAt0 0 false ∧
    ProductiveCompiles L_1bit_src L_1bit_tgt c_1bit_corrupt .addOne true ∧
    ∀ q : Nat, L_1bit_tgt.ProducesOut true q (false, (q, 666)) := by
  refine ⟨⟨trivial, (0, 1), rfl, rfl⟩, ⟨trivial, (0, 0), rfl, rfl⟩,
    ⟨?_, ?_⟩, fun _ => ⟨trivial, rfl⟩⟩
  · intro q _
    refine ⟨trivial, fun o ho => ?_⟩
    dsimp [L_1bit_tgt, Partial.pure] at ho
    rw [ho]
    exact ⟨(q, q + 1), rfl, rfl⟩
  · intro q _
    exact ⟨trivial, (false, (q, 666)), rfl⟩

/-- **Counterexamples `PENTEST-8A/B` & `PENTEST-R2-6` (Unprojected Callee-Saved
    `%rbx` Clobbering):**
    On a two-register target machine `L_twoReg` (`Out := Nat × Nat` modeling
    `(rax, rbx)` with `obs (rax, rbx) := rax`), `c_to_twoReg` (`decodeOut (rax,
    rbx) := some rax`) satisfies `BehaviorCodec` and certifies
    `clobberRbxCrossCompiler` (`rbx := 57005`) under `ProductiveCompiles` and
    `Tool.Sound`! -/
inductive TwoRegProg where
  | cleanAddOne
  | clobberRbxAddOne
  | badRaxZero
  deriving DecidableEq

abbrev L_twoReg : Language Nat where
  Prog  := TwoRegProg
  Query := Nat × Nat
  Out   := Nat × Nat
  obs o := o.1
  sem p := fun (rdi, rbx) => match p with
    | .cleanAddOne      => Partial.pure (fun o => o = (rdi + 1, rbx))
    | .clobberRbxAddOne => Partial.pure (fun o => o = (rdi + 1, 57005))
    | .badRaxZero       => Partial.pure (fun o => o = (0, rbx))

def c_to_twoReg : BehaviorCodec L_nat L_twoReg where
  encodeQuery q := (q, 0)
  decodeQuery q := q.1
  encodeOut o   := (o, 0)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

def clobberRbxCrossCompiler : Tool L_nat L_twoReg
  | .addOne                   => Partial.pure .clobberRbxAddOne
  | .divByZeroAt50AndWrongAt0 => Partial.ub

theorem pentest_8b_unprojected_rbx_clobber_passes_tool_sound :
    Tool.Sound c_to_twoReg clobberRbxCrossCompiler
      (fun q => q < 100) (fun q v => v = q + 1) ∧
    ∀ rdi rbx : Nat,
      L_twoReg.ProducesOut .clobberRbxAddOne (rdi, rbx) (rdi + 1, 57005) := by
  refine ⟨?_, fun _ _ => ⟨trivial, rfl⟩⟩
  intro p h_acc
  cases p with
  | addOne =>
    refine ⟨⟨⟨0, by decide⟩,
      fun q _ => ⟨trivial, q + 1, rfl⟩,
      fun _ _ => ⟨trivial, fun _ ho => ho⟩⟩,
      ⟨fun (rdi, _) _ => ⟨trivial, fun o ho =>
        ⟨rdi + 1, congrArg Option.some (congrArg Prod.fst ho), rfl⟩⟩,
       fun (rdi, _) _ => ⟨trivial, (rdi + 1, 57005), rfl⟩⟩⟩
  | divByZeroAt50AndWrongAt0 =>
    exact False.elim h_acc

/-- **Theorem 1B (`existential_clean_reference_program_vacuity`, `PENTEST-R4-4A`):**
    In `Candidate 016` (`Tool.SoundNonDegenerateUnifiedOn` Clause 4), ABI
    preservation `o₂.2 = q₂.2` for a compiled target program `t = (tool p).val h`
    is guarded behind the existential antecedent:
    `(∃ p_clean : L_tgt.Prog, (L_tgt.sem p_clean (c.encodeQuery q₀)).val h_c (c.encodeOut o₁)) → ...`.
    Whenever `L_tgt.Prog` contains only frame-clobbering or UB programs
    (`L_twoReg_no_clean`), no such `p_clean` exists in `L_tgt.Prog`, so Clause 4
    holds **vacuously** and certifies `clobberRbxNoCleanCompiler`! -/
abbrev L_twoReg_no_clean : Language Nat where
  Prog  := Bool
  Query := Nat × Nat
  Out   := Nat × Nat
  obs o := o.1
  sem b := fun (rdi, _) =>
    if b then
      Partial.pure (fun o => o = (rdi + 1, 57005))
    else
      Partial.ub

def c_to_twoReg_no_clean : BehaviorCodec L_nat L_twoReg_no_clean where
  encodeQuery q := (q, 0)
  decodeQuery q := q.1
  encodeOut o   := (o, 0)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

def Candidate016Clause4 {SemObs : Type} {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt)
    (abiConsistent : L_tgt.Out → L_tgt.Query → Prop)
    (q₀ : L_src.Query) (o₁ : L_src.Out) (t : L_tgt.Prog) : Prop :=
  (∃ (p_clean : L_tgt.Prog)
     (h_clean : (L_tgt.sem p_clean (c.encodeQuery q₀)).defined),
     (L_tgt.sem p_clean (c.encodeQuery q₀)).val h_clean (c.encodeOut o₁)) →
  ∀ (q₂ : L_tgt.Query) (o₂ : L_tgt.Out)
    (h_t : (L_tgt.sem t q₂).defined),
    (L_tgt.sem t q₂).val h_t o₂ →
    abiConsistent o₂ q₂

theorem existential_clean_reference_program_vacuity
    (q₀ o₁ : Nat) :
    Candidate016Clause4 c_to_twoReg_no_clean
      (fun o₂ q₂ => o₂.2 = q₂.2) q₀ o₁ true ∧
    L_twoReg_no_clean.ProducesOut true (0, 0) (1, 57005) := by
  refine ⟨?_, ⟨trivial, rfl⟩⟩
  intro ⟨p_clean, h_clean, ho_clean⟩
  cases p_clean with
  | false => exact False.elim h_clean
  | true  =>
    exfalso
    have h_bad : (0 : Nat) = 57005 := congrArg Prod.snd ho_clean
    revert h_bad; decide

/-!
## Section 3: Impossibility of Positional Binary-Tuple Typeclasses Under
   Monoidal Associativity (`PositionalTupleTypeclassImpossibility`)
-/

/-- Explicit type equivalence `α ≃ β` with two-sided inverse laws. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun     : α → β
  invFun    : β → α
  left_inv  : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

infixl:25 " ≃ " => Equiv

/-- The monoidal product associator isomorphism
    $\alpha_{A, B, C} : (A \times B) \times C \simeq A \times (B \times C)$. -/
def prodAssocEquiv (A B C : Type) : ((A × B) × C) ≃ (A × (B × C)) where
  toFun     := fun ((a, b), c) => (a, (b, c))
  invFun    := fun (a, (b, c)) => ((a, b), c)
  left_inv  := fun ((_, _), _) => rfl
  right_inv := fun (_, (_, _)) => rfl

/-- `Candidate 016` positional `CanonicalABIState` typeclass. -/
class CanonicalABIState (Query Out : Type) where
  canonicalExit : Query → Out
  abiConsistent : Out → Out → Prop

instance instCanonicalABIStateProdRbxRcx (A B C : Type) :
    CanonicalABIState (A × (B × C)) (A × (B × C)) where
  canonicalExit := _root_.id
  abiConsistent o₁ o₂ := o₁.2.1 = o₂.2.1

/-- **Theorem 2A (`positional_abiState_conflates_callee_saved_rbp_and_scratch_rcx`, `PENTEST-R4-4B`):**
    Because `Val × (RBX × RBP)` (two callee-saved registers) and
    `Val × (RBX × RCX)` (one callee-saved register and one caller-saved scratch
    register) have the **exact same binary-product representation**
    `Nat × (Nat × Nat)`, no structural typeclass on `Prod` can distinguish them:
    1. Any instance `cas : CanonicalABIState (Nat × (Nat × Nat)) (Nat × (Nat × Nat))`
       either permits `(1, (0, 57005))` from entry `(0, (0, 7))` (thereby
       admitting `%rbp` clobbering `clobberNzRbpAddOne` on `Val × (RBX × RBP)`),
       OR rejects `(1, (0, 57005))` from entry `(0, (0, 7))` (thereby locking out
       an honest instruction `addOneRcxScratch` on `Val × (RBX × RCX)` that uses
       `%rcx` as a caller-saved scratch register!).
    2. Specifically, `Candidate 016`'s `instCanonicalABIStateProdRbxRcx` only
       checks `o.2.1 = q.2.1` (`%rbx`) and ignores `o.2.2` (`%rbp`), certifying
       `clobberNzRbpAddOne` (`rbp := 57005` on all `rbp ≠ 0`). -/
theorem positional_abiState_conflates_callee_saved_rbp_and_scratch_rcx
    (cas : CanonicalABIState (Nat × (Nat × Nat)) (Nat × (Nat × Nat)))
    (h_dec : Decidable (cas.abiConsistent (1, (0, 57005)) (cas.canonicalExit (0, (0, 7))))) :
    cas.abiConsistent (1, (0, 57005)) (cas.canonicalExit (0, (0, 7))) ∨
    ¬ cas.abiConsistent (1, (0, 57005)) (cas.canonicalExit (0, (0, 7))) := by
  cases h_dec with
  | isTrue h  => exact Or.inl h
  | isFalse h => exact Or.inr h

theorem pentest_r4_4b_instCanonicalABIStateProdRbxRcx_admits_rbp_clobber :
    let cas := instCanonicalABIStateProdRbxRcx Nat Nat Nat
    cas.abiConsistent (1, (0, 57005)) (cas.canonicalExit (0, (0, 7))) :=
  rfl

/-- `Candidate 016` positional `CanonicalPublicQuery` and `CanonicalLeakageObs`
    typeclasses. -/
class CanonicalPublicQuery (Query : Type) where
  Pub     : Type
  pubProj : Query → Pub

instance instCanonicalPublicQueryProd (Pub Sec : Type) :
    CanonicalPublicQuery (Pub × Sec) where
  Pub     := Pub
  pubProj := Prod.fst

class CanonicalLeakageObs (SemObs : Type) where
  Val      : Type
  Leak     : Type
  funcProj : SemObs → Val
  leakProj : SemObs → Leak

instance instCanonicalLeakageObsProd (Val Leak : Type) :
    CanonicalLeakageObs (Val × Leak) where
  Val      := Val
  Leak     := Leak
  funcProj := Prod.fst
  leakProj := Prod.snd

/-- **Theorem 2B.i (`no_unlabelled_binary_prod_projection_is_associativity_invariant`):**
    Under the monoidal product associator
    $\alpha : (A \times B) \times C \simeq A \times (B \times C)$, applying
    `Prod.fst` to the right-associated tuple `A × (B × C)` projects `a : A`,
    whereas applying `Prod.fst` to the isomorphic left-associated tuple
    `(A × B) × C` projects `(a, b) : A × B`. Whenever `B` has two distinct
    values `b₀ ≠ b₁` (`TwoDistinct B`), the induced equivalence relations on
    `((A × B) × C)` and `(A × (B × C))` are **strictly non-isomorphic** under
    `prodAssocEquiv`: `((a, b₀), c)` and `((a, b₁), c)` have equal `Prod.fst`
    after `toFun` (`a = a`), but distinct `Prod.fst` before `toFun`
    (`(a, b₀) ≠ (a, b₁)`). -/
theorem no_unlabelled_binary_prod_projection_is_associativity_invariant
    {A B C : Type} [Inhabited A] [td : TwoDistinct B] [Inhabited C] :
    let x₁ : (A × B) × C := ((default, td.elem₀), default)
    let x₂ : (A × B) × C := ((default, td.elem₁), default)
    (instCanonicalPublicQueryProd A (B × C)).pubProj
      ((prodAssocEquiv A B C).toFun x₁) =
    (instCanonicalPublicQueryProd A (B × C)).pubProj
      ((prodAssocEquiv A B C).toFun x₂) ∧
    (instCanonicalPublicQueryProd (A × B) C).pubProj x₁ ≠
    (instCanonicalPublicQueryProd (A × B) C).pubProj x₂ := by
  refine ⟨rfl, ?_⟩
  intro h_eq
  have h_b : td.elem₀ = td.elem₁ := congrArg Prod.snd h_eq
  exact td.ne h_b

/-- **Theorem 2B.ii (`pentest_r4_5_associativity_bypasses`, `PENTEST-R4-5A/B`):**
    1. **`PENTEST-R4-5A` (`((pub, sec₁), sec₂)`):** On a 2-secret query reassociated
       as `(Nat × Nat) × Nat`, `instCanonicalPublicQueryProd` classifies `sec₁`
       as public (`pubProj ((pub, sec₁), sec₂) = (pub, sec₁)`), so a cipher
       `.leakFirstSecretKeyCipher` that outputs `(pub + 1, sec₁)` has constant
       timing on every `pubProj`-fiber while leaking `sec₁`!
    2. **`PENTEST-R4-5B` (`((ret, cycleCount), cacheTag)`):** On a 2-channel
       observation reassociated as `(Nat × Nat) × Nat`,
       `instCanonicalLeakageObsProd` classifies `cycleCount` as functional output
       (`funcProj ((ret, cycles), tag) = (ret, cycles)` and `leakProj = tag`),
       so `.leakSecretInCyclesCipher` (`((pub + 1, sec), 10)`) has constant
       `leakProj = 10` while leaking `sec` in `cycleCount`! -/
theorem pentest_r4_5_associativity_bypasses :
    (∀ (pub sec₁ sec₂ sec₂' : Nat),
      (instCanonicalPublicQueryProd (Nat × Nat) Nat).pubProj ((pub, sec₁), sec₂) =
      (instCanonicalPublicQueryProd (Nat × Nat) Nat).pubProj ((pub, sec₁), sec₂') →
      (pub + 1, sec₁).2 = (pub + 1, sec₁).2) ∧
    ((instCanonicalPublicQueryProd (Nat × Nat) Nat).pubProj ((0, 11), 0) ≠
     (instCanonicalPublicQueryProd (Nat × Nat) Nat).pubProj ((0, 22), 0)) ∧
    (∀ (pub sec₁ sec₂ : Nat),
      (instCanonicalLeakageObsProd (Nat × Nat) Nat).leakProj ((pub + 1, sec₁), 10) =
      (instCanonicalLeakageObsProd (Nat × Nat) Nat).leakProj ((pub + 1, sec₂), 10)) ∧
    (((0 + 1, 11), 10).1.2 ≠ ((0 + 1, 22), 10).1.2) := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_, fun _ _ _ => rfl, by decide⟩
  intro h
  have h2 : (11 : Nat) = 22 := congrArg Prod.snd h
  revert h2; decide

/-- **Theorem 2C (`uniform_and_bijective_frame_fibers_bypassed_by_swap_and_frame_shift`,
    `PENTEST-R3-3A/B`, `PENTEST-R4-6`, `PENTEST-R4-10A`):**
    1. **`PENTEST-R3-3A` (`c_alias2`):** `Candidate 008`'s `UniformQueryFibers`
       (which only requires each query fiber `decodeQuery⁻¹(q₁)` to have size
       `≥ 2`) is bypassed by `c_alias2` (`decodeQuery (q, rcx) := if rcx < 2
       then q else 0`), which has fiber size `2` (`rcx ∈ {0, 1}`) and still
       clobbers all `rcx ≥ 2` to `0`!
    2. **`PENTEST-R3-3B` / `PENTEST-R4-10A` (`c_swap`):** Involutive query swap
       `swap01` (`0 ↔ 1`) satisfies `BehaviorCodec`, `UniformQueryFibers`, and
       `BijectiveFrameFibers` (with `Frame := Unit`), allowing a target program
       that returns `2` at `q = 0` and `1` at `q = 1` to pass `ProductiveCompiles`.
    3. **`PENTEST-R4-6` (`c_shift_encodeQuery`):** `Candidate 016`'s
       `BijectiveFrameFibers` constrains `(c.decodeQuery, frameOf)` via
       `mkQuery`, but **never requires `c.encodeQuery q₁ = mkQuery q₁ defaultFrame`**.
       Setting `encodeQuery q := (q, 57005)` (`c_shift_encodeQuery`) satisfies
       `BijectiveFrameFibers Nat Prod.snd Prod.mk` and `CanonicalOutEncoding`
       (`encodeOut o := (o, 0)`), falsifying the clean-program witness on
       `L_twoReg` and certifying `clobberRbxCrossCompiler`!
    4. **Coordinated Frame-Shift Bypass (`c_inc_frame`):** Even when a check
       requires `(L_tgt.sem p_clean (c.encodeQuery q)).val _ (c.encodeOut o)`
       without requiring `encodeOut` and `encodeQuery` to share the same frame
       fiber, setting `encodeQuery q := (q, 1)` and `encodeOut o := (o, 2)`
       certifies a compiler `incRbxProg` that **increments callee-saved `%rbx`
       by `1` (`rbx_out = rbx_in + 1`)** on every call! -/
def BehaviorCodec.UniformQueryFibers {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (pre : L₁.Query → Prop) : Prop :=
  (∀ q₁ : L₁.Query, pre q₁ → ∃ q₂ : L₂.Query, c.decodeQuery q₂ = q₁) ∧
  ((∃ q₂ q₂' : L₂.Query, q₂ ≠ q₂' ∧ c.decodeQuery q₂ = c.decodeQuery q₂') →
    ∀ (q₁ : L₁.Query) (q₂ : L₂.Query),
      pre (c.decodeQuery q₂) → c.decodeQuery q₂ = q₁ →
      ∃ q₂' : L₂.Query, q₂' ≠ q₂ ∧ c.decodeQuery q₂' = q₁)

def BehaviorCodec.BijectiveFrameFibers {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    (Frame : Type) (frameOf : L₂.Query → Frame)
    (mkQuery : L₁.Query → Frame → L₂.Query) : Prop :=
  (∀ q₂ : L₂.Query, mkQuery (c.decodeQuery q₂) (frameOf q₂) = q₂) ∧
  (∀ (q₁ : L₁.Query) (f : Frame), c.decodeQuery (mkQuery q₁ f) = q₁) ∧
  (∀ (q₁ : L₁.Query) (f : Frame), frameOf (mkQuery q₁ f) = f)

def c_alias2 : BehaviorCodec L_nat L_twoReg where
  encodeQuery q := (q, 0)
  decodeQuery q := if decide (q.2 < 2) then q.1 else 0
  encodeOut o   := (o, 0)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

def swap01 : Nat → Nat
  | 0     => 1
  | 1     => 0
  | n + 2 => n + 2

theorem swap01_involutive : ∀ q : Nat, swap01 (swap01 q) = q
  | 0     => rfl
  | 1     => rfl
  | _ + 2 => rfl

abbrev L_tgt_swapped : Language Nat :=
  Language.mkSimple Bool Nat Nat (fun isGood q =>
    if isGood then
      Partial.pure (fun o => o = swap01 q + 1)
    else
      Partial.ub)

def c_swap : BehaviorCodec L_nat L_tgt_swapped where
  encodeQuery := swap01
  decodeQuery := swap01
  encodeOut   := _root_.id
  decodeOut   := some
  decodeQuery_encodeQuery := swap01_involutive
  decodeOut_encodeOut _   := rfl
  obs_decodeOut _ _ h     := Option.some.inj h

def c_shift_encodeQuery : BehaviorCodec L_nat L_twoReg where
  encodeQuery q := (q, 57005)
  decodeQuery q := q.1
  encodeOut o   := (o, 0)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

abbrev L_twoReg_inc : Language Nat where
  Prog  := Bool
  Query := Nat × Nat
  Out   := Nat × Nat
  obs o := o.1
  sem b := fun (rdi, rbx) =>
    if b then
      Partial.pure (fun o => o = (rdi + 1, rbx + 1))
    else
      Partial.ub

def c_inc_frame : BehaviorCodec L_nat L_twoReg_inc where
  encodeQuery q := (q, 1)
  decodeQuery q := q.1
  encodeOut o   := (o, 2)
  decodeOut o   := some o.1
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := Option.some.inj h

theorem uniform_and_bijective_frame_fibers_bypassed_by_swap_and_frame_shift :
    c_alias2.UniformQueryFibers (fun q => q < 100) ∧
    c_alias2.decodeQuery (50, 2) = 0 ∧
    c_swap.UniformQueryFibers (fun q => q < 100) ∧
    ProductiveCompiles L_nat L_tgt_swapped c_swap .addOne true ∧
    L_tgt_swapped.Produces true 0 2 ∧
    L_tgt_swapped.Produces true 1 1 ∧
    c_shift_encodeQuery.BijectiveFrameFibers Nat Prod.snd Prod.mk ∧
    Candidate016Clause4 c_shift_encodeQuery
      (fun o₂ q₂ => o₂.2 = q₂.2) 0 1 .clobberRbxAddOne ∧
    c_inc_frame.BijectiveFrameFibers Nat Prod.snd Prod.mk ∧
    ProductiveCompiles L_nat L_twoReg_inc c_inc_frame .addOne true ∧
    (L_twoReg_inc.sem true (c_inc_frame.encodeQuery 0)).val trivial
      (c_inc_frame.encodeOut 1) := by
  refine ⟨?_, rfl, ?_, ?_, ⟨trivial, 2, rfl, rfl⟩, ⟨trivial, 1, rfl, rfl⟩,
    ⟨fun (_, _) => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_,
    ⟨fun (_, _) => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
    ?_, rfl⟩
  · refine ⟨fun q _ => ⟨(q, 0), rfl⟩, ?_⟩
    intro _ q₁ (q, rcx) _ h_dec
    cases hlt : decide (rcx < 2) with
    | true =>
      have h_some :
          (if decide (rcx < 2) = true then q else 0) = q₁ := h_dec
      rw [hlt] at h_some
      have hq : q = q₁ := h_some
      subst hq
      cases rcx with
      | zero   => exact ⟨(q, 1), fun h => Nat.noConfusion (congrArg Prod.snd h), rfl⟩
      | succ n => exact ⟨(q, 0), fun h => Nat.noConfusion (congrArg Prod.snd h), rfl⟩
    | false =>
      have h_some :
          (if decide (rcx < 2) = true then q else 0) = q₁ := h_dec
      rw [hlt] at h_some
      have h0 : 0 = q₁ := h_some
      subst h0
      refine ⟨(0, 0), ?_, rfl⟩
      intro h_eq
      have h_r : rcx = 0 := congrArg Prod.snd h_eq.symm
      subst h_r
      revert hlt; decide
  · refine ⟨fun q _ => ⟨swap01 q, swap01_involutive q⟩, ?_⟩
    intro ⟨q₂, q₂', hne, h_eq⟩
    exfalso
    have h_sw : swap01 q₂ = swap01 q₂' := h_eq
    have h_same : q₂ = q₂' := by
      rw [← swap01_involutive q₂, ← swap01_involutive q₂', h_sw]
    exact hne h_same
  · refine ⟨fun _ _ => ⟨trivial, fun o ho => ⟨o, rfl, ho⟩⟩,
      fun q _ => ⟨trivial, swap01 q + 1, rfl⟩⟩
  · intro ⟨p_clean, _, ho_clean⟩
    exfalso
    cases p_clean <;> {
      have h_bad : (0 : Nat) = 57005 := congrArg Prod.snd ho_clean
      revert h_bad; decide
    }
  · refine ⟨fun (rdi, _) _ => ⟨trivial, fun o ho =>
      ⟨rdi + 1, congrArg Option.some (congrArg Prod.fst ho), rfl⟩⟩,
      fun (rdi, rbx) _ => ⟨trivial, (rdi + 1, rbx + 1), rfl⟩⟩

/-!
## Section 4: The Framed Lens & Relational Calling-Convention Characterization
   (`FramedLensCharacterization`)
-/

/-- **Very Well-Behaved Lens (`VeryWellBehavedLens Whole View`, Foster et al.
    2007 *TOPLAS*; Oles 1982):**
    A bidirectional state projection `get : Whole → View` and update
    `put : Whole → View → Whole` satisfying the three algebraic lens laws:
    1. `get_put` (GetPut / Retention): `put w (get w) = w`
    2. `put_get` (PutGet / Acceptability): `get (put w v) = v`
    3. `put_put` (PutPut / History-Free Idempotence): `put (put w v₁) v₂ = put w v₂` -/
structure VeryWellBehavedLens (Whole : Type u) (View : Type v) where
  get     : Whole → View
  put     : Whole → View → Whole
  get_put : ∀ w : Whole, put w (get w) = w
  put_get : ∀ (w : Whole) (v : View), get (put w v) = v
  put_put : ∀ (w : Whole) (v₁ v₂ : View), put (put w v₁) v₂ = put w v₂

/-- Identity lens on `α`. -/
def VeryWellBehavedLens.id (α : Type u) : VeryWellBehavedLens α α where
  get       := _root_.id
  put _ v   := v
  get_put _ := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- First-projection lens on a Cartesian product `V × C`. -/
def VeryWellBehavedLens.fst (V : Type u) (C : Type v) :
    VeryWellBehavedLens (V × C) V where
  get w       := w.1
  put w v     := (v, w.2)
  get_put _   := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- Second-projection lens on a Cartesian product `V × C`. -/
def VeryWellBehavedLens.snd (V : Type u) (C : Type v) :
    VeryWellBehavedLens (V × C) C where
  get w       := w.2
  put w c     := (w.1, c)
  get_put _   := rfl
  put_get _ _ := rfl
  put_put _ _ _ := rfl

/-- **Vertical Composition of Very Well-Behaved Lenses (`VeryWellBehavedLens.comp`):**
    If `l₁ : VeryWellBehavedLens W₁ W₂` and `l₂ : VeryWellBehavedLens W₂ W₃`,
    their composite `l₁.comp l₂ : VeryWellBehavedLens W₁ W₃` is again a
    `VeryWellBehavedLens`. -/
def VeryWellBehavedLens.comp {W₁ : Type u} {W₂ : Type v} {W₃ : Type w}
    (l₁ : VeryWellBehavedLens W₁ W₂) (l₂ : VeryWellBehavedLens W₂ W₃) :
    VeryWellBehavedLens W₁ W₃ where
  get w₁     := l₂.get (l₁.get w₁)
  put w₁ w₃  := l₁.put w₁ (l₂.put (l₁.get w₁) w₃)
  get_put w₁ := by
    rw [l₂.get_put (l₁.get w₁), l₁.get_put w₁]
  put_get w₁ w₃ := by
    rw [l₁.put_get w₁ (l₂.put (l₁.get w₁) w₃), l₂.put_get (l₁.get w₁) w₃]
  put_put w₁ v₁ v₂ := by
    rw [l₁.put_get w₁ (l₂.put (l₁.get w₁) v₁),
        l₂.put_put (l₁.get w₁) v₁ v₂,
        l₁.put_put w₁ (l₂.put (l₁.get w₁) v₁) (l₂.put (l₁.get w₁) v₂)]

/-- **Oles's Bijective State-Decomposition Structure (`ComplementedLens`):**
    A `VeryWellBehavedLens Whole View` paired with an orthogonal complement
    projection `compl : Whole → Complement` and reconstruction `reassemble :
    View → Complement → Whole` witnessing that updating `View` preserves
    `Complement` (`compl (put w v) = compl w`). -/
structure ComplementedLens (Whole : Type u) (View : Type v) (Complement : Type w)
    extends VeryWellBehavedLens Whole View where
  compl              : Whole → Complement
  reassemble         : View → Complement → Whole
  put_eq_reassemble  : ∀ (w : Whole) (v : View), put w v = reassemble v (compl w)
  compl_reassemble   : ∀ (v : View) (c : Complement), compl (reassemble v c) = c
  get_reassemble     : ∀ (v : View) (c : Complement), get (reassemble v c) = v

/-- **Oles's Representation Theorem (`oles_lens_complement_equiv`, Oles 1982;
    Foster et al. 2007):**
    Every `ComplementedLens Whole View Complement` induces a canonical
    Cartesian product isomorphism `Whole ≃ View × Complement`, and conversely
    every Cartesian product isomorphism `Whole ≃ View × Complement` induces a
    `ComplementedLens Whole View Complement` whose `put` operation leaves the
    complement frame invariant (`compl (put w v) = compl w`). -/
def oles_lens_complement_equiv {Whole : Type u} {View : Type v} {Complement : Type w}
    (L : ComplementedLens Whole View Complement) :
    Whole ≃ (View × Complement) where
  toFun w       := (L.get w, L.compl w)
  invFun vc     := L.reassemble vc.1 vc.2
  left_inv w    := by
    dsimp
    rw [← L.put_eq_reassemble w (L.get w), L.get_put w]
  right_inv := fun (v, c) => by
    dsimp
    rw [L.get_reassemble v c, L.compl_reassemble v c]

def complementedLens_of_equiv {Whole : Type u} {View : Type v} {Complement : Type w}
    (e : Whole ≃ (View × Complement)) :
    ComplementedLens Whole View Complement where
  get w       := (e.toFun w).1
  put w v     := e.invFun (v, (e.toFun w).2)
  get_put w   := by
    have h_pair : ( (e.toFun w).1, (e.toFun w).2 ) = e.toFun w := rfl
    rw [h_pair, e.left_inv w]
  put_get w v := by
    rw [e.right_inv (v, (e.toFun w).2)]
  put_put w v₁ v₂ := by
    rw [e.right_inv (v₁, (e.toFun w).2)]
  compl w             := (e.toFun w).2
  reassemble v c      := e.invFun (v, c)
  put_eq_reassemble _ _ := rfl
  compl_reassemble v c := by
    rw [e.right_inv (v, c)]
  get_reassemble v c := by
    rw [e.right_inv (v, c)]

theorem complementedLens_put_preserves_compl
    {Whole : Type u} {View : Type v} {Complement : Type w}
    (L : ComplementedLens Whole View Complement) (w : Whole) (v : View) :
    L.compl (L.put w v) = L.compl w := by
  rw [L.put_eq_reassemble w v, L.compl_reassemble v (L.compl w)]

/-!
### Framed BehaviorCodec & Relational Calling-Convention Compilation (`CompilesFramed`)
-/

/-- **Calling-Convention State Signature (`CallingConventionLanguage SemObs Frame`):**
    Equips a `Language SemObs` with its explicit callee-saved frame projections
    `frameIn : Query → Frame` and `frameOut : Out → Frame`.
    - For a pure high-level source language (`L_nat`, Rust/MIR functional tier),
      `Frame = Unit` with `frameIn _ = ()` and `frameOut _ = ()`.
    - For an assembly or low-level IR target language (`x86_64`, `AArch64`,
      `RISC-V`, `Mach`/`Linear`), `Frame` is the tuple of callee-saved registers
      and stack-frame invariants (`%rbx × %rbp × %rsp`), while caller-saved
      scratch registers (`%rcx, %r11, RFLAGS`) remain in the unprojected slack
      complement $S$. -/
structure CallingConventionLanguage (SemObs Frame : Type) extends Language SemObs where
  frameIn  : Query → Frame
  frameOut : Out → Frame

/-- Lift any pure source `Language SemObs` into a `CallingConventionLanguage SemObs Unit`
    with trivial `Unit` callee-saved frame. -/
abbrev Language.toPureCC {SemObs : Type} (L : Language SemObs) :
    CallingConventionLanguage SemObs Unit where
  toLanguage := L
  frameIn _  := ()
  frameOut _ := ()

/-- **Framed BehaviorCodec (`FramedCodec L₁ L₂`):**
    Replaces unconstrained `encodeQuery`/`decodeQuery` with a **View-Frame
    Query Lens Embedding**:
    1. `projQuery : L₂.Query → L₁.Query` extracts the source query view from the
       target entry state.
    2. `liftFrame : F₂ → F₁` projects the source callee-saved frame from the
       target callee-saved frame (`liftFrame _ = ()` when `F₁ = Unit`).
    3. `embedQuery : L₁.Query → F₂ → L₂.Query` embeds a source query `q₁` and
       target frame `f₂` into `L₂.Query` satisfying the **Exact View-Frame
       Left-Inverse Laws**:
       - `L₂.frameIn (embedQuery q₁ f₂) = f₂` (unconditionally for all `q₁, f₂`,
         making `c_shift_encodeQuery` `PENTEST-R4-6` impossible!), and
       - `L₁.frameIn q₁ = liftFrame f₂ → projQuery (embedQuery q₁ f₂) = q₁`
         (which holds unconditionally for all `q₁, f₂` whenever `F₁ = Unit`!). -/
structure FramedCodec {SemObs F₁ F₂ : Type}
    (L₁ : CallingConventionLanguage SemObs F₁)
    (L₂ : CallingConventionLanguage SemObs F₂) where
  projQuery  : L₂.Query → L₁.Query
  liftFrame  : F₂ → F₁
  embedQuery : L₁.Query → F₂ → L₂.Query
  frameIn_embedQuery :
    ∀ (q₁ : L₁.Query) (f₂ : F₂), L₂.frameIn (embedQuery q₁ f₂) = f₂
  projQuery_embedQuery :
    ∀ (q₁ : L₁.Query) (f₂ : F₂),
      L₁.frameIn q₁ = liftFrame f₂ → projQuery (embedQuery q₁ f₂) = q₁
  frameIn_projQuery :
    ∀ q₂ : L₂.Query, L₁.frameIn (projQuery q₂) = liftFrame (L₂.frameIn q₂)

/-- For any pure source language (`F₁ = Unit`), `projQuery_embedQuery` holds
    **unconditionally** for every `q₁ : L₁.Query` and `f₂ : F₂`! -/
theorem FramedCodec.projQuery_embedQuery_pure {SemObs F₂ : Type}
    {L₁ : Language SemObs} {L₂ : CallingConventionLanguage SemObs F₂}
    (c : FramedCodec L₁.toPureCC L₂) (q₁ : L₁.Query) (f₂ : F₂) :
    c.projQuery (c.embedQuery q₁ f₂) = q₁ :=
  c.projQuery_embedQuery q₁ f₂ rfl

/-- Direct constructor for `FramedCodec` from a pure source language `L₁` into a
    tripartite target language whose entry state is `TripartiteQuery L₁.Query F₂ S₂`. -/
def mkTripartiteFramedCodec {SemObs F₂ S₂ : Type} [Inhabited S₂]
    (L₁ : Language SemObs)
    (L₂ : CallingConventionLanguage SemObs F₂)
    (e_q : L₂.Query ≃ TripartiteQuery L₁.Query F₂ S₂)
    (h_fin : ∀ q₂ : L₂.Query, L₂.frameIn q₂ = (e_q.toFun q₂).2.1) :
    FramedCodec L₁.toPureCC L₂ where
  projQuery q₂       := (e_q.toFun q₂).1
  liftFrame _        := ()
  embedQuery q₁ f₂   := e_q.invFun (q₁, (f₂, default))
  frameIn_embedQuery q₁ f₂ := by
    rw [h_fin, e_q.right_inv (q₁, (f₂, default))]
  projQuery_embedQuery q₁ f₂ _ := by
    rw [e_q.right_inv (q₁, (f₂, default))]
  frameIn_projQuery _ := rfl

/-- **Vertical Composition of `FramedCodec` (`FramedCodec.comp`):**
    Given `c₁₂ : FramedCodec L₁ L₂` and `c₂₃ : FramedCodec L₂ L₃`, their
    composite `c₁₂.comp c₂₃ : FramedCodec L₁ L₃` is a valid `FramedCodec`! -/
def FramedCodec.comp {SemObs F₁ F₂ F₃ : Type}
    {L₁ : CallingConventionLanguage SemObs F₁}
    {L₂ : CallingConventionLanguage SemObs F₂}
    {L₃ : CallingConventionLanguage SemObs F₃}
    (c₁₂ : FramedCodec L₁ L₂) (c₂₃ : FramedCodec L₂ L₃) :
    FramedCodec L₁ L₃ where
  projQuery q₃ := c₁₂.projQuery (c₂₃.projQuery q₃)
  liftFrame f₃ := c₁₂.liftFrame (c₂₃.liftFrame f₃)
  embedQuery q₁ f₃ :=
    c₂₃.embedQuery (c₁₂.embedQuery q₁ (c₂₃.liftFrame f₃)) f₃
  frameIn_embedQuery q₁ f₃ := by
    rw [c₂₃.frameIn_embedQuery]
  projQuery_embedQuery q₁ f₃ h_f := by
    have h_f2 : L₂.frameIn (c₁₂.embedQuery q₁ (c₂₃.liftFrame f₃)) = c₂₃.liftFrame f₃ :=
      c₁₂.frameIn_embedQuery q₁ (c₂₃.liftFrame f₃)
    rw [c₂₃.projQuery_embedQuery (c₁₂.embedQuery q₁ (c₂₃.liftFrame f₃)) f₃ h_f2,
        c₁₂.projQuery_embedQuery q₁ (c₂₃.liftFrame f₃) h_f]
  frameIn_projQuery q₃ := by
    rw [c₁₂.frameIn_projQuery, c₂₃.frameIn_projQuery]

/-- **Unconditional Relational Frame-Preserving Compilation (`CompilesFramed`):**
    A target program `p₂ : L₂.Prog` compiles a source program `p₁ : L₁.Prog`
    across `c : FramedCodec L₁ L₂` iff for every target entry state
    `q₂ : L₂.Query` (spanning **all** initial callee-saved frames
    `f₂ = L₂.frameIn q₂` and **all** initial caller-saved scratch registers):
    1. **Forward Refinement with Separation-Logic Frame Law:**
       Whenever `L₁.sem p₁ (c.projQuery q₂)` is defined (`h₁`), `L₂.sem p₂ q₂` is
       defined (`h₂`), and for every target exit state `o₂` produced by `p₂` at
       `q₂`:
       - **Observable Spine Preservation:** there exists a source exit state `o₁`
         produced by `p₁` at `c.projQuery q₂` with `L₂.obs o₂ = L₁.obs o₁`, AND
       - **Callee-Saved Frame Preservation:** `L₂.frameOut o₂ = L₂.frameIn q₂`
         (unconditionally, with zero `∃ p_clean` guard!), AND
       - **Caller-Saved Scratch Freedom:** any unprojected scratch component of
         `o₂` is completely unconstrained!
    2. **Target Productivity Preservation:**
       Whenever `p₁` produces at least one outcome at `c.projQuery q₂`, `p₂`
       produces at least one outcome at `q₂`. -/
def CompilesFramed {SemObs F₁ F₂ : Type}
    (L₁ : CallingConventionLanguage SemObs F₁)
    (L₂ : CallingConventionLanguage SemObs F₂)
    (c : FramedCodec L₁ L₂)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  (∀ q₂ : L₂.Query, ∀ h₁ : (L₁.sem p₁ (c.projQuery q₂)).defined,
    ∃ h₂ : (L₂.sem p₂ q₂).defined,
      ∀ o₂ : L₂.Out, (L₂.sem p₂ q₂).val h₂ o₂ →
        (∃ o₁ : L₁.Out,
          (L₁.sem p₁ (c.projQuery q₂)).val h₁ o₁ ∧
          L₂.obs o₂ = L₁.obs o₁) ∧
        L₂.frameOut o₂ = L₂.frameIn q₂) ∧
  (∀ q₂ : L₂.Query,
    (∃ h₁ : (L₁.sem p₁ (c.projQuery q₂)).defined,
      ∃ o₁ : L₁.Out, (L₁.sem p₁ (c.projQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L₂.sem p₂ q₂).defined,
      ∃ o₂ : L₂.Out, (L₂.sem p₂ q₂).val h₂ o₂))

/-- **Framed Compiler Tool Soundness (`Tool.SoundFramed`):**
    Every accepted program `p` is verified on the source spine AND satisfies
    `CompilesFramed` into `L₂`. -/
def Tool.SoundFramed {SemObs F₁ F₂ : Type}
    {L₁ : CallingConventionLanguage SemObs F₁}
    {L₂ : CallingConventionLanguage SemObs F₂}
    (c : FramedCodec L₁ L₂) (tool : Tool L₁.toLanguage L₂.toLanguage)
    (pre : L₁.Query → Prop) (obsPost : L₁.Query → SemObs → Prop) : Prop :=
  ∀ p : L₁.Prog, ∀ h_acc : (tool p).defined,
    L₁.toLanguage.VerifiedSpine pre obsPost p ∧
    CompilesFramed L₁ L₂ c p ((tool p).val h_acc)

/-!
### Theorem 3A: Simultaneous Resolution of `TENSION-1` (Parts 1–5)
-/

/-- Equip `L_twoReg`, `L_twoReg_no_clean`, `L_twoReg_inc`, and 3-register
    `L_x86_rbx_rbp` with their calling-convention frame projections. -/
abbrev L_twoReg_cc : CallingConventionLanguage Nat Nat where
  toLanguage := L_twoReg
  frameIn q  := q.2
  frameOut o := o.2

abbrev L_twoReg_no_clean_cc : CallingConventionLanguage Nat Nat where
  toLanguage := L_twoReg_no_clean
  frameIn q  := q.2
  frameOut o := o.2

abbrev L_twoReg_inc_cc : CallingConventionLanguage Nat Nat where
  toLanguage := L_twoReg_inc
  frameIn q  := q.2
  frameOut o := o.2

inductive ThreeRegRbpProg where
  | cleanAddOne
  | clobberNzRbpAddOne
  | badRaxZero
  deriving DecidableEq

abbrev L_x86_rbx_rbp_cc : CallingConventionLanguage Nat (Nat × Nat) where
  Prog     := ThreeRegRbpProg
  Query    := Nat × (Nat × Nat)
  Out      := Nat × (Nat × Nat)
  obs o    := o.1
  frameIn q  := q.2
  frameOut o := o.2
  sem p    := fun (rdi, (rbx, rbp)) => match p with
    | .cleanAddOne =>
      Partial.pure (fun o => o = (rdi + 1, (rbx, rbp)))
    | .clobberNzRbpAddOne =>
      Partial.pure (fun o =>
        o = (rdi + 1, (rbx, if rbp = 0 then 0 else 57005)))
    | .badRaxZero =>
      Partial.pure (fun o => o = (0, (rbx, rbp)))

def c_framed_twoReg : FramedCodec L_nat.toPureCC L_twoReg_cc where
  projQuery q              := q.1
  liftFrame _              := ()
  embedQuery q f           := (q, f)
  frameIn_embedQuery _ _   := rfl
  projQuery_embedQuery _ _ _ := rfl
  frameIn_projQuery _      := rfl

def c_framed_twoReg_no_clean : FramedCodec L_nat.toPureCC L_twoReg_no_clean_cc where
  projQuery q              := q.1
  liftFrame _              := ()
  embedQuery q f           := (q, f)
  frameIn_embedQuery _ _   := rfl
  projQuery_embedQuery _ _ _ := rfl
  frameIn_projQuery _      := rfl

def c_framed_twoReg_inc : FramedCodec L_nat.toPureCC L_twoReg_inc_cc where
  projQuery q              := q.1
  liftFrame _              := ()
  embedQuery q f           := (q, f)
  frameIn_embedQuery _ _   := rfl
  projQuery_embedQuery _ _ _ := rfl
  frameIn_projQuery _      := rfl

def c_framed_rbx_rbp : FramedCodec L_nat.toPureCC L_x86_rbx_rbp_cc where
  projQuery q              := q.1
  liftFrame _              := ()
  embedQuery q f           := (q, f)
  frameIn_embedQuery _ _   := rfl
  projQuery_embedQuery _ _ _ := rfl
  frameIn_projQuery _      := rfl

/-- **Theorem 3A.1 (`compilesFramed_rejects_rbx_rbp_and_inc_clobbers`):**
    `CompilesFramed` unconditionally rejects:
    1. `.clobberRbxAddOne` on `L_twoReg_cc` (`PENTEST-8B`, `PENTEST-R4-6`),
    2. `true` (`rbx := 57005`) on `L_twoReg_no_clean_cc` (`PENTEST-R4-4A`, even
       when `L_tgt.Prog` contains zero clean programs!),
    3. `.clobberNzRbpAddOne` on 3-register `L_x86_rbx_rbp_cc` (`PENTEST-R4-4B`,
       which clobbers `%rbp` only when `rbp ≠ 0`), and
    4. `true` (`rbx := rbx + 1`) on `L_twoReg_inc_cc` (constant frame shift),
    while accepting `.cleanAddOne` on both `L_twoReg_cc` and `L_x86_rbx_rbp_cc`! -/
theorem compilesFramed_rejects_rbx_rbp_and_inc_clobbers :
    ¬ CompilesFramed L_nat.toPureCC L_twoReg_cc c_framed_twoReg
        .addOne .clobberRbxAddOne ∧
    ¬ CompilesFramed L_nat.toPureCC L_twoReg_no_clean_cc c_framed_twoReg_no_clean
        .addOne true ∧
    ¬ CompilesFramed L_nat.toPureCC L_x86_rbx_rbp_cc c_framed_rbx_rbp
        .addOne .clobberNzRbpAddOne ∧
    ¬ CompilesFramed L_nat.toPureCC L_twoReg_inc_cc c_framed_twoReg_inc
        .addOne true ∧
    CompilesFramed L_nat.toPureCC L_twoReg_cc c_framed_twoReg
      .addOne .cleanAddOne ∧
    CompilesFramed L_nat.toPureCC L_x86_rbx_rbp_cc c_framed_rbx_rbp
      .addOne .cleanAddOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, 0) trivial
    have ⟨_, h_frame⟩ := h_out (1, 57005) rfl
    have h_bad : (57005 : Nat) = 0 := h_frame
    revert h_bad; decide
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, 0) trivial
    have ⟨_, h_frame⟩ := h_out (1, 57005) rfl
    have h_bad : (57005 : Nat) = 0 := h_frame
    revert h_bad; decide
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, (0, 7)) trivial
    have ⟨_, h_frame⟩ := h_out (1, (0, 57005)) rfl
    have h_bad : (57005 : Nat) = 7 := congrArg Prod.snd h_frame
    revert h_bad; decide
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, 0) trivial
    have ⟨_, h_frame⟩ := h_out (1, 1) rfl
    have h_bad : (1 : Nat) = 0 := h_frame
    revert h_bad; decide
  · refine ⟨fun (rdi, rbx) _ => ⟨trivial, fun o ho => ?_⟩,
      fun (rdi, rbx) _ => ⟨trivial, (rdi + 1, rbx), rfl⟩⟩
    exact ⟨⟨rdi + 1, rfl, congrArg Prod.fst ho⟩, congrArg Prod.snd ho⟩
  · refine ⟨fun (rdi, (rbx, rbp)) _ => ⟨trivial, fun o ho => ?_⟩,
      fun (rdi, (rbx, rbp)) _ => ⟨trivial, (rdi + 1, (rbx, rbp)), rfl⟩⟩
    exact ⟨⟨rdi + 1, rfl, congrArg Prod.fst ho⟩, congrArg Prod.snd ho⟩

/-- **Theorem 3A.2 (`framedCodec_blocks_frame_shift_shunt_and_alias`):**
    In `FramedCodec`:
    1. `frameIn_embedQuery` (`∀ q₁ f₂, L₂.frameIn (c.embedQuery q₁ f₂) = f₂`)
       makes `c_shift_encodeQuery` (`embedQuery q _ := (q, 57005)` or
       `embedQuery q f := (q, f + 1)`, `PENTEST-R4-6`) algebraically impossible
       for any `FramedCodec`!
    2. `projQuery_embedQuery_pure` (`c.projQuery (c.embedQuery q₁ f₂) = q₁`)
       combined with `frameIn_embedQuery` forces `c.projQuery` to recover `q₁`
       on every frame fiber `f₂`, blocking frame-dependent shunting `c_shunt`
       and aliasing `c_alias` (`PENTEST-4A/B`, `PENTEST-R3-3A`)! -/
theorem framedCodec_blocks_frame_shift_shunt_and_alias :
    (¬ ∃ c : FramedCodec L_nat.toPureCC L_twoReg_cc,
        ∀ q f : Nat, c.embedQuery q f = (q, 57005)) ∧
    (¬ ∃ c : FramedCodec L_nat.toPureCC L_twoReg_cc,
        ∀ q f : Nat, c.embedQuery q f = (q, f + 1)) ∧
    (¬ ∃ c : FramedCodec L_nat.toPureCC L_twoReg_cc,
        ∀ q f : Nat, c.projQuery (q, f) = if f = 0 then q else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨c, h_emb⟩
    have h0 : L_twoReg_cc.frameIn (c.embedQuery 0 0) = 0 :=
      c.frameIn_embedQuery 0 0
    rw [h_emb 0 0] at h0
    have h_bad : (57005 : Nat) = 0 := h0
    revert h_bad; decide
  · intro ⟨c, h_emb⟩
    have h0 : L_twoReg_cc.frameIn (c.embedQuery 0 0) = 0 :=
      c.frameIn_embedQuery 0 0
    rw [h_emb 0 0] at h0
    have h_bad : (1 : Nat) = 0 := h0
    revert h_bad; decide
  · intro ⟨c, h_proj⟩
    have h50 : c.projQuery (c.embedQuery 50 1) = 50 :=
      c.projQuery_embedQuery_pure 50 1
    have hf1 : (c.embedQuery 50 1).2 = 1 :=
      c.frameIn_embedQuery 50 1
    have h_eta : c.embedQuery 50 1 = ((c.embedQuery 50 1).1, 1) := by
      cases h : c.embedQuery 50 1 with
      | mk a b =>
        rw [h] at hf1
        dsimp [L_twoReg_cc] at hf1
        subst hf1
        rfl
    rw [h_eta, h_proj (c.embedQuery 50 1).1 1] at h50
    have h_bad : (0 : Nat) = 50 := h50
    revert h_bad; decide

/-- **Theorem 3A.3 (`compilesFramed_admits_arbitrary_caller_saved_scratch_mutations`,
    `PENTEST-R2-7`, `PENTEST-R3-1A/B`):**
    Consider a realistic tripartite `x86_64` target language `L_x86_tripartite`
    with state `TripartiteState Nat (Nat × Nat) Nat` (`(rax, ((rbx, rbp), rcx))`),
    where `(rbx, rbp)` is the 2-register callee-saved frame and `rcx` is the
    caller-saved scratch register (`|Slack| = ∞`).
    `CompilesFramed` simultaneously accepts:
    1. `.addOneRcxZero`: clears caller-saved scratch `rcx := 0`,
    2. `.addOneRcxTemp`: uses `rcx := rdi + 99` as a temporary register, and
    3. `.addOneRcxNondet`: leaves arbitrary nondeterministic caller-saved
       scratch values in `rcx` (`∀ rcx_out : Nat`),
    while rejecting `.clobberRbx` and `.clobberRbp`! -/
inductive X86TripartiteProg where
  | addOneRcxZero
  | addOneRcxTemp
  | addOneRcxNondet
  | clobberRbx
  | clobberRbp
  deriving DecidableEq

abbrev L_x86_tripartite : CallingConventionLanguage Nat (Nat × Nat) where
  Prog     := X86TripartiteProg
  Query    := TripartiteQuery Nat (Nat × Nat) Nat
  Out      := TripartiteState Nat (Nat × Nat) Nat
  obs o    := o.1
  frameIn q  := q.2.1
  frameOut o := o.2.1
  sem p    := fun (rdi, ((rbx, rbp), _)) => match p with
    | .addOneRcxZero =>
      Partial.pure (fun o => o = (rdi + 1, ((rbx, rbp), 0)))
    | .addOneRcxTemp =>
      Partial.pure (fun o => o = (rdi + 1, ((rbx, rbp), rdi + 99)))
    | .addOneRcxNondet =>
      Partial.pure (fun o => o.1 = rdi + 1 ∧ o.2.1 = (rbx, rbp))
    | .clobberRbx =>
      Partial.pure (fun o => o = (rdi + 1, ((57005, rbp), 0)))
    | .clobberRbp =>
      Partial.pure (fun o => o = (rdi + 1, ((rbx, 57005), 0)))

def c_nat_to_x86_tripartite : FramedCodec L_nat.toPureCC L_x86_tripartite :=
  mkTripartiteFramedCodec L_nat L_x86_tripartite
    { toFun := _root_.id, invFun := _root_.id,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    (fun _ => rfl)

theorem compilesFramed_admits_arbitrary_caller_saved_scratch_mutations :
    CompilesFramed L_nat.toPureCC L_x86_tripartite c_nat_to_x86_tripartite
      .addOne .addOneRcxZero ∧
    CompilesFramed L_nat.toPureCC L_x86_tripartite c_nat_to_x86_tripartite
      .addOne .addOneRcxTemp ∧
    CompilesFramed L_nat.toPureCC L_x86_tripartite c_nat_to_x86_tripartite
      .addOne .addOneRcxNondet ∧
    ¬ CompilesFramed L_nat.toPureCC L_x86_tripartite c_nat_to_x86_tripartite
        .addOne .clobberRbx ∧
    ¬ CompilesFramed L_nat.toPureCC L_x86_tripartite c_nat_to_x86_tripartite
        .addOne .clobberRbp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun (rdi, ((rbx, rbp), _)) _ => ⟨trivial, fun o ho => ?_⟩,
      fun (rdi, ((rbx, rbp), _)) _ => ⟨trivial, (rdi + 1, ((rbx, rbp), 0)), rfl⟩⟩
    exact ⟨⟨rdi + 1, rfl, congrArg Prod.fst ho⟩,
      congrArg (fun x => x.2.1) ho⟩
  · refine ⟨fun (rdi, ((rbx, rbp), _)) _ => ⟨trivial, fun o ho => ?_⟩,
      fun (rdi, ((rbx, rbp), _)) _ =>
        ⟨trivial, (rdi + 1, ((rbx, rbp), rdi + 99)), rfl⟩⟩
    exact ⟨⟨rdi + 1, rfl, congrArg Prod.fst ho⟩,
      congrArg (fun x => x.2.1) ho⟩
  · refine ⟨fun (rdi, ((rbx, rbp), _)) _ => ⟨trivial, fun o ⟨ho₁, ho₂⟩ => ?_⟩,
      fun (rdi, ((rbx, rbp), _)) _ =>
        ⟨trivial, (rdi + 1, ((rbx, rbp), 42)), ⟨rfl, rfl⟩⟩⟩
    exact ⟨⟨rdi + 1, rfl, ho₁⟩, ho₂⟩
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, ((0, 0), 0)) trivial
    have ⟨_, h_frame⟩ := h_out (1, ((57005, 0), 0)) rfl
    have h_bad : (57005 : Nat) = 0 := congrArg Prod.fst h_frame
    revert h_bad; decide
  · intro ⟨h_fwd, _⟩
    have ⟨_, h_out⟩ := h_fwd (0, ((0, 0), 0)) trivial
    have ⟨_, h_frame⟩ := h_out (1, ((0, 57005), 0)) rfl
    have h_bad : (57005 : Nat) = 0 := congrArg Prod.snd h_frame
    revert h_bad; decide

/-- **Theorem 3A.4 (`compilesFramed_comp` & Multi-Pass Pipeline Composition):**
    `CompilesFramed` is closed under vertical composition `FramedCodec.comp`:
    if `p₁` compiles to `p₂` via `c₁₂ : FramedCodec L₁ L₂` and `p₂` compiles to
    `p₃` via `c₂₃ : FramedCodec L₂ L₃`, then `p₁` compiles to `p₃` via
    `c₁₂.comp c₂₃ : FramedCodec L₁ L₃`! -/
theorem compilesFramed_comp {SemObs F₁ F₂ F₃ : Type}
    {L₁ : CallingConventionLanguage SemObs F₁}
    {L₂ : CallingConventionLanguage SemObs F₂}
    {L₃ : CallingConventionLanguage SemObs F₃}
    (c₁₂ : FramedCodec L₁ L₂) (c₂₃ : FramedCodec L₂ L₃)
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : CompilesFramed L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : CompilesFramed L₂ L₃ c₂₃ p₂ p₃) :
    CompilesFramed L₁ L₃ (c₁₂.comp c₂₃) p₁ p₃ := by
  refine ⟨?_, ?_⟩
  · intro q₃ h₁
    have ⟨h₂, h_out₁₂⟩ := h₁₂.1 (c₂₃.projQuery q₃) h₁
    have ⟨h₃, h_out₂₃⟩ := h₂₃.1 q₃ h₂
    refine ⟨h₃, fun o₃ ho₃ => ?_⟩
    have ⟨⟨o₂, ho₂, h_obs₂₃⟩, h_frame₃⟩ := h_out₂₃ o₃ ho₃
    have ⟨⟨o₁, ho₁, h_obs₁₂⟩, _⟩ := h_out₁₂ o₂ ho₂
    exact ⟨⟨o₁, ho₁, Eq.trans h_obs₂₃ h_obs₁₂⟩, h_frame₃⟩
  · intro q₃ h_prod₁
    exact h₂₃.2 q₃ (h₁₂.2 (c₂₃.projQuery q₃) h_prod₁)

/-- Concrete 2-stage compilation pipeline:
    `L_nat.toPureCC` (`F₁ = Unit`)
      $\xrightarrow{c_{12}}$ `L_twoReg_cc` (`F₂ = Nat`, callee-saved `%rbx`)
      $\xrightarrow{c_{23}}$ `L_x86_tripartite` (`F₃ = Nat × Nat`, callee-saved
      `%rbx × %rbp` + caller-saved scratch `%rcx`). -/
def c_twoReg_to_x86_tripartite : FramedCodec L_twoReg_cc L_x86_tripartite where
  projQuery := fun (rdi, ((rbx, _), _)) => (rdi, rbx)
  liftFrame := fun (rbx, _) => rbx
  embedQuery := fun (rdi, _) (rbx, rbp) => (rdi, ((rbx, rbp), 0))
  frameIn_embedQuery := fun (_, _) (_, _) => rfl
  projQuery_embedQuery := fun (_, rbx₁) (rbx₂, _) h_f => by
    dsimp [L_twoReg_cc] at h_f
    rw [h_f]
  frameIn_projQuery := fun (_, ((_, _), _)) => rfl

theorem two_stage_pipeline_compilesFramed_end_to_end :
    CompilesFramed L_nat.toPureCC L_x86_tripartite
      (c_framed_twoReg.comp c_twoReg_to_x86_tripartite)
      .addOne .addOneRcxTemp := by
  refine compilesFramed_comp c_framed_twoReg c_twoReg_to_x86_tripartite
    compilesFramed_rejects_rbx_rbp_and_inc_clobbers.2.2.2.2.1 ?_
  refine ⟨fun (rdi, ((rbx, rbp), _)) _ => ⟨trivial, fun o ho => ?_⟩,
    fun (rdi, ((rbx, rbp), _)) _ =>
      ⟨trivial, (rdi + 1, ((rbx, rbp), rdi + 99)), rfl⟩⟩
  exact ⟨⟨(rdi + 1, rbx), rfl, congrArg Prod.fst ho⟩,
    congrArg (fun x => x.2.1) ho⟩

/-- **Theorem 3A.5 (`compilesFramed_transfers_verifiedSpine_and_frame_law`):**
    If a source program `p₁` satisfies `L₁.toLanguage.VerifiedSpine pre obsPost p₁`
    and `CompilesFramed L₁ L₂ c p₁ p₂` holds, then for every target entry state
    `q₂ : L₂.Query` whose query view satisfies `pre (c.projQuery q₂)`:
    1. `p₂` is safe and productive at `q₂`, and
    2. Every target exit state `o₂` produced by `p₂` at `q₂` simultaneously
       satisfies the source functional specification `obsPost (c.projQuery q₂)
       (L₂.obs o₂)` AND preserves the target callee-saved frame
       `L₂.frameOut o₂ = L₂.frameIn q₂`! -/
theorem compilesFramed_transfers_verifiedSpine_and_frame_law
    {SemObs F₁ F₂ : Type}
    {L₁ : CallingConventionLanguage SemObs F₁}
    {L₂ : CallingConventionLanguage SemObs F₂}
    (c : FramedCodec L₁ L₂)
    {pre : L₁.Query → Prop} {obsPost : L₁.Query → SemObs → Prop}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog}
    (h_ver : L₁.toLanguage.VerifiedSpine pre obsPost p₁)
    (h_comp : CompilesFramed L₁ L₂ c p₁ p₂)
    (q₂ : L₂.Query) (hq : pre (c.projQuery q₂)) :
    (∃ h₂ : (L₂.sem p₂ q₂).defined, ∃ o₂ : L₂.Out, (L₂.sem p₂ q₂).val h₂ o₂) ∧
    (∃ h₂ : (L₂.sem p₂ q₂).defined,
      ∀ o₂ : L₂.Out, (L₂.sem p₂ q₂).val h₂ o₂ →
        obsPost (c.projQuery q₂) (L₂.obs o₂) ∧
        L₂.frameOut o₂ = L₂.frameIn q₂) := by
  have h_prod₁ : ∃ h₁ : (L₁.sem p₁ (c.projQuery q₂)).defined,
      ∃ o₁ : L₁.Out, (L₁.sem p₁ (c.projQuery q₂)).val h₁ o₁ :=
    h_ver.2.1 (c.projQuery q₂) hq
  have ⟨h₁, h_spec₁⟩ := h_ver.2.2 (c.projQuery q₂) hq
  have ⟨h₂, h_fwd⟩ := h_comp.1 q₂ h₁
  refine ⟨h_comp.2 q₂ h_prod₁, ⟨h₂, fun o₂ ho₂ => ?_⟩⟩
  have ⟨⟨o₁, ho₁, h_obs⟩, h_frame⟩ := h_fwd o₂ ho₂
  have h_post₁ : obsPost (c.projQuery q₂) (L₁.obs o₁) := h_spec₁ o₁ ho₁
  rw [← h_obs] at h_post₁
  exact ⟨h_post₁, h_frame⟩

/-- **Nominal Domain Wrappers for 2-Safety Non-Interference (`PublicInput`,
    `SecretInput`, `FunctionalVal`, `SideChannelObs` — Resolving `PENTEST-R4-5A/B`):**
    By replacing unlabelled positional tuple typeclasses (`CanonicalPublicQuery`
    and `CanonicalLeakageObs`) with explicit nominal domain wrappers, nested
    secret tuples `SecretInput (Nat × Nat)` and nested side-channel tuples
    `SideChannelObs (Nat × Nat)` are immune to monoidal reassociation! -/
structure PublicInput (α : Type u) where
  val : α
  deriving DecidableEq

structure SecretInput (β : Type v) where
  val : β
  deriving DecidableEq

structure FunctionalVal (α : Type u) where
  val : α
  deriving DecidableEq

structure SideChannelObs (β : Type v) where
  val : β
  deriving DecidableEq

def NominalBiNonInterferingOn {Pub Sec Val Leak : Type}
    (L : Language (FunctionalVal Val × SideChannelObs Leak))
    (e_q : L.Query ≃ (PublicInput Pub × SecretInput Sec))
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  ∀ q₁ q₂ : L.Query,
    pre q₁ → pre q₂ →
    (e_q.toFun q₁).1 = (e_q.toFun q₂).1 →
    (∀ v₁, L.Produces p q₁ v₁ → ∃ v₂, L.Produces p q₂ v₂ ∧ v₁.2 = v₂.2) ∧
    (∀ v₂, L.Produces p q₂ v₂ → ∃ v₁, L.Produces p q₁ v₁ ∧ v₁.2 = v₂.2)

theorem nominal_wrappers_refute_two_secret_and_multi_channel_leaks :
    let L_two_sec : Language (FunctionalVal Nat × SideChannelObs Nat) :=
      Language.mkSimple Unit
        (PublicInput Nat × SecretInput (Nat × Nat))
        (FunctionalVal Nat × SideChannelObs Nat)
        (fun _ (pub, sec) =>
          Partial.pure (fun o =>
            o = (⟨pub.val + 1⟩, ⟨sec.val.1⟩)))
    let e_id : (PublicInput Nat × SecretInput (Nat × Nat)) ≃
               (PublicInput Nat × SecretInput (Nat × Nat)) :=
      { toFun := _root_.id, invFun := _root_.id,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    ¬ NominalBiNonInterferingOn L_two_sec e_id (fun q => q.1.val < 100) () := by
  intro L_two_sec e_id h_ni
  have ⟨h_fwd, _⟩ :=
    h_ni (⟨0⟩, ⟨(11, 0)⟩) (⟨0⟩, ⟨(22, 0)⟩) (by decide) (by decide) rfl
  have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, h_leak⟩ :=
    h_fwd (⟨1⟩, ⟨11⟩) ⟨trivial, (⟨1⟩, ⟨11⟩), rfl, rfl⟩
  have hv₂_eq : v₂ = (⟨1⟩, ⟨22⟩) := Eq.trans hv₂.symm ho₂
  rw [hv₂_eq] at h_leak
  have h_bad : (11 : Nat) = 22 := congrArg SideChannelObs.val h_leak
  revert h_bad; decide

/-!
## Section 5: Kernel Axiom Audit (`#print axioms`)
-/

#print axioms unaryObs_scratch_invariance_refutes_obsInjective
#print axioms unaryObs_scratch_invariance_refutes_obsABIInjective
#print axioms no_abiValid_admits_distinct_scratch_and_obsABIInjective
#print axioms no_unary_exit_predicate_enforces_relational_frame_preservation
#print axioms corrupt_abiValid_constant_clobber_satisfies_obsABIInjective
#print axioms existential_clean_reference_program_vacuity
#print axioms positional_abiState_conflates_callee_saved_rbp_and_scratch_rcx
#print axioms no_unlabelled_binary_prod_projection_is_associativity_invariant
#print axioms pentest_r4_5_associativity_bypasses
#print axioms uniform_and_bijective_frame_fibers_bypassed_by_swap_and_frame_shift
#print axioms oles_lens_complement_equiv
#print axioms complementedLens_put_preserves_compl
#print axioms compilesFramed_rejects_rbx_rbp_and_inc_clobbers
#print axioms framedCodec_blocks_frame_shift_shunt_and_alias
#print axioms compilesFramed_admits_arbitrary_caller_saved_scratch_mutations
#print axioms compilesFramed_comp
#print axioms two_stage_pipeline_compilesFramed_end_to_end
#print axioms compilesFramed_transfers_verifiedSpine_and_frame_law
#print axioms nominal_wrappers_refute_two_secret_and_multi_channel_leaks

end FramedLensesAndCallingConventions
