-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Hyperproperties, Relational Bisimulation 2-Safety, Bounded Nondeterminism, and McLean's Refinement Paradox in Semantic Verification Models

This standalone Lean 4 (`v4.34.1`) mechanization develops the mathematical laws
governing $k$-safety hyperproperties (non-interference, constant-time execution),
demonic self-composition (`Language.diag`), equivalence relations on public
queries and leakage observations, McLean's refinement paradox across compiler
pipelines, and the nondeterminism refinement lattice (empty vacuity,
specification-bounded nondeterminism, angelic reachability, and bounded/unbounded
uninitialized-memory chaos) in the 4-primitive semantic verification model
(`Language`, `Tool`, `BehaviorCodec`, `Spec`).

## Overview of Mechanized Theorem Families

1. **Section 1 — 1-Trace vs. 2-Safety Expressiveness Separation & Demonic
   Self-Composition (`SelfCompositionVsJitterTheorem`):**
   - **Theorem 1A (`theorem1a_one_trace_blind_to_two_safety`, `PENTEST-7`):**
     For any constant-time cipher $p_{\text{ct}}$ (`o = (q.1 + 1, 10)`) and
     timing-leaking cipher $p_{\text{leak}}$ (`o = (q.1 + 1, q.2)`), if the
     observable spine `obs` projects only the functional output `o.1`, their
     1-trace behaviors are pointwise identical, so **no 1-trace specification
     `Spec` can ever distinguish $p_{\text{ct}}$ from $p_{\text{leak}}$**.
   - **Theorem 1A.2 (`pentest_r2_9a_timing_only_diag_certifies_badCipher`):**
     Conversely, if a 2-safety specification on `L.diag` constrains only timing
     equality (`v.1.2 = v.2.2`) without conjoining 1-trace functional correctness,
     a broken constant-zero cipher `.badCipher` (`o = (0, 0)`) passes 2-safety
     verification while violating functional correctness at every input.
   - **Theorem 1B (`theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic`,
     Barthe-D'Argenio-Rezk 2004 / Terauchi-Aiken 2005 vs. `PENTEST-R2-9B`):**
     A productive program $p$ satisfies the diagonal 2-safety specification
     $S_{\text{diag}}((q_1, q_2), (v_1, v_2)) := \text{lowEq}(q_1, q_2) \to
     \text{leakEq}(v_1, v_2)$ demonically on the self-composed product language
     `L.diag` **if and only if** $p$ is **both** possibilistically
     non-interfering (`NonInterferingOn`) **and** leakage-deterministic on every
     query (`LeakageDeterministicOn`).
   - **Corollary 1B.1 (`pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter`):**
     Demonic self-composition `L.diag` unconditionally rejects every program with
     secret-independent nondeterministic timing jitter (e.g., cache/bus jitter
     $t \in \{10, 11\}$ independent of the secret key), even when its semantic
     behavior is literally constant across all secret keys.

2. **Section 2 — One-Way Simulation Failure vs. Symmetric PER / Bisimulation
   2-Safety (`BisimulationTwoSafetyLaws`):**
   - **Theorem 2A.1 (`pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak`):**
     Under an asymmetric preorder `lowEq` (`pub₁ = pub₂ ∧ sec₁ ≤ sec₂`), one-way
     simulation `NonInterferingOn` certifies `.subsetLeakyCipher` (which produces
     timing $\{10\}$ at $\text{sec} = 0$ and $\{10, 20\}$ at $\text{sec} > 0$),
     even though observing $t = 20$ leaks $\text{sec} > 0$ with 100% certainty.
   - **Theorem 2A.2 (`pentest_r3_6_policy_degeneracies` & `pentest_r4_5_positional_tuple_bypasses`):**
     Even under two-way simulation `BiNonInterferingOn`, policy degeneracies
     (`lowEq := Eq`, punctured master-key exemptions `sec < K`, timing-blind
     `leakEq := True` or `v₁.1 = v₂.1`, and positional binary tuple projections on
     left-associated 3-tuples `((pub, sec₁), sec₂)` or `((ret, cycles), cache)`)
     admit secret-leaking programs.
   - **Theorem 2B (`theorem2b_security_domain_decomposition_characterization`):**
     Parameterizing 2-safety by an explicit Cartesian **Security Domain
     Decomposition** (`SecurityDomain`: `projPub`, `projSec`, `projVal`,
     `projLeak`) induces bona fide equivalence relations `D.lowEq` and
     `D.leakEq`, guarantees non-trivial secret fibers whenever $|\text{Sec}| \ge 2$,
     and proves that two-way `DomainBiNonInterferingOn` holds **if and only if**
     the set of reachable leakage observations is invariant across all secret
     inputs:
     $$\forall \text{pub}\, \text{sec}_1\, \text{sec}_2\, \ell,\ \text{ProducesLeak}(p, (\text{pub}, \text{sec}_1), \ell) \leftrightarrow \text{ProducesLeak}(p, (\text{pub}, \text{sec}_2), \ell).$$

3. **Section 3 — McLean's Refinement Paradox & Bisimulation-Preserving
   Compilation (`McLeanRefinementParadoxAndResolution`):**
   - **Theorem 3A (`theorem3a_mclean_refinement_paradox_counterexample`, McLean 1994):**
     Standard demonic refinement (`ProductiveCompiles`: $\emptyset \subsetneq
     L_2.\text{sem}(p_2, q) \subseteq L_1.\text{sem}(p_1, q)$) **does not
     preserve `BiNonInterferingOn`**! A source program $p_1$ with
     secret-independent timing jitter $\{10, 20\}$ satisfies `BiNonInterferingOn`
     on $L_1$, and productively compiles via `mcleanParadoxCompiler` to a target
     program $p_2$ that refines $\{10, 20\}$ into $\{10\}$ when $\text{sec} = 0$
     and into $\{20\}$ when $\text{sec} > 0$, completely leaking the secret key on
     $L_2$.
   - **Theorem 3B.1 (`theorem3b_resolution1_leakage_deterministic_transfer`):**
     When the source program $p_1$ is leakage-deterministic on `pre`, standard
     `ProductiveCompiles` **does** preserve `BiNonInterferingOn` from $L_1$ to $L_2$.
   - **Theorem 3B.2 (`theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement`):**
     For nondeterministic languages, **Leakage-Bisimulation-Preserving
     Compilation (`LeakageBisimCompiles`)** and **Secret-Uniform Refinement
     (`UniformRefinementCompiles`)** transfer `BiNonInterferingOn` from $L_1$ to
     $L_2$, compose vertically across multi-pass pipelines, and reject
     `mcleanParadoxCompiler` while admitting both jitter-preserving and uniform
     determinizing compilers.

4. **Section 4 — The Nondeterminism Refinement Lattice: Chaos vs. Bounded
   Nondeterminism vs. Angelic Reachability (`NondeterminismRefinementLattice`):**
   - **Theorem 4A (`theorem4a_nondeterminism_pathology_hierarchy`):**
     Mechanizes why demonic-only `Compiles` (`PENTEST-6` / empty-semantics
     vacuity), target-only `SoundTargetOn` (`PENTEST-R2-8A` / `.uninitRead`),
     finite $k$-value exclusion `NonChaoticOn` (`PENTEST-R3-2C` /
     `.uninitByteRead` $0 < o < 2^b$), and angelic verification
     `VerifiedAngelicSpineOn` (`PENTEST-R3-9A` / `.nondetMixed`) each fail.
   - **Theorem 4B (`theorem4b_productive_demonic_spec_refinement_characterization`):**
     Proves that **Productive Demonic Specification Refinement**
     ($\emptyset \subsetneq \text{Obs}(p, q) \subseteq \{v \mid S(q, v)\}$,
     `VerifiedSpineOn`) is the unique verification modality that simultaneously
     rejects empty-semantics miracles, unbounded chaos, bounded bitwidth chaos,
     and angelic may-violate branches while admitting legitimate underspecified
     nondeterminism (e.g., 8-byte aligned allocator choice) and transferring
     soundly across `ProductiveCompiles`.
-/

namespace HyperpropertiesBisimulationAndRefinementParadox

-- ============================================================================
-- Section 0: Foundational 4-Primitive Semantic Model
-- (`Language`, `Spec`, `BehaviorCodec`, `Tool`)
-- ============================================================================

/-- Reflexive and transitive preorder. -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Demonic predicate inclusion preorder on `Out → Prop`:
    `P₁ ≤ P₂` means every outcome permitted by `P₁` is permitted by `P₂`. -/
instance instPreorderPred (Out : Type u) : Preorder (Out → Prop) where
  le P₁ P₂ := ∀ o, P₁ o → P₂ o
  le_refl _ _ h := h
  le_trans h₁₂ h₂₃ o h₁ := h₂₃ o (h₁₂ o h₁)

/-- Partial behavior container (`Partial B`) separating definedness/safety
    (`defined : Prop`, freedom from undefined behavior) from the value
    (`val : defined → B`). -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Pure (always-defined) `Partial` value. -/
def Partial.pure {B : Type u} (b : B) : Partial B :=
  { defined := True, val := fun _ => b }

/-- Undefined behavior (`Partial.ub`, nowhere defined). -/
def Partial.ub {B : Type u} : Partial B :=
  { defined := False, val := fun h => False.elim h }

/-- Demonic refinement ordering on `Partial B`:
    `p₁ ≤ p₂` iff whenever `p₂` is defined (`h₂`), `p₁` is also defined (`h₁`)
    and `p₁.val h₁ ≤ p₂.val h₂`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Pointwise refinement ordering on `Query → B`. -/
instance instPreorderPi (Query : Type u) (B : Type v) [Preorder B] :
    Preorder (Query → B) where
  le f₁ f₂ := ∀ q, f₁ q ≤ f₂ q
  le_refl f q := Preorder.le_refl (f q)
  le_trans h₁₂ h₂₃ q := Preorder.le_trans (h₁₂ q) (h₂₃ q)

/-- Semantic behavior of a program: maps each `Query` to a `Partial` predicate
    over concrete outcomes `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Primitive 1 (`Language SemObs`):
    A language with program AST `Prog`, input `Query`, concrete outcome `Out`,
    observable spine projection `obs : Out → SemObs`, and semantics `sem`. -/
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out
  dom   : Query → Prop := fun _ => True

/-- Constructor for a simple language where `SemObs = Out` and `obs = id`. -/
abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := id
  sem   := sem

/-- Program `prog` is safe (defined / free of UB) at query `q`. -/
abbrev Language.SafeAt {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) : Prop :=
  (L.sem prog q).defined

/-- Program `prog` can produce concrete outcome `o` at query `q`. -/
abbrev Language.ProducesOut {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (o : L.Out) : Prop :=
  ∃ h : (L.sem prog q).defined, (L.sem prog q).val h o

/-- Program `prog` can produce observable outcome `v : SemObs` at query `q`. -/
abbrev Language.Produces {SemObs : Type} (L : Language SemObs)
    (prog : L.Prog) (q : L.Query) (v : SemObs) : Prop :=
  ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o ∧ L.obs o = v

/-- Non-vacuity of a precondition `pre` relative to structural domain `dom`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

/-- Program `prog` is productive (non-empty outcome set) at every query in `pre`. -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Primitive 2 (`Spec` / `Language.SpecOn`):
    1-trace specification behavior requiring `pre q` to imply safety and
    `post q o` for all reachable outcomes `o`. -/
def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => {
    defined := pre q
    val     := fun _ o => post q o
  }

/-- Observable-spine 1-trace specification behavior (`Language.SpineSpecOn`). -/
def Language.SpineSpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) :
    Behavior L.Query L.Out :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

/-- Productive demonic 1-trace verification on concrete outcomes (`VerifiedOn`). -/
def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Productive demonic 1-trace verification on the observable spine (`VerifiedSpineOn`). -/
def Language.VerifiedSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn dom pre (fun q o => obsPost q (L.obs o)) prog

/-- Default-domain specialization of `Language.VerifiedSpineOn`. -/
abbrev Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedSpineOn L.dom pre obsPost prog

/-- Constructive 1-trace violation witness on the observable spine (`ViolatesSpine`). -/
def Language.ViolatesSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (badProg : L.Prog) : Prop :=
  ∃ q : L.Query, pre q ∧
    (∀ h : (L.sem badProg q).defined,
      ∃ o : L.Out, (L.sem badProg q).val h o ∧ ¬ obsPost q (L.obs o))

/-- Any program satisfying `ViolatesSpine` cannot satisfy `VerifiedSpineOn`. -/
theorem Language.violatesSpine_not_verifiedSpineOn {SemObs : Type}
    {L : Language SemObs} {dom pre : L.Query → Prop}
    {obsPost : L.Query → SemObs → Prop} {p : L.Prog}
    (h_viol : L.ViolatesSpine pre obsPost p) :
    ¬ L.VerifiedSpineOn dom pre obsPost p := by
  intro ⟨_, _, h_ref⟩
  have ⟨q, h_pre, h_bad⟩ := h_viol
  have ⟨h_def, h_sub⟩ := h_ref q h_pre
  have ⟨o, ho, h_not⟩ := h_bad h_def
  exact h_not (h_sub o ho)

/-- Primitive 3 (`BehaviorCodec L₁ L₂`):
    Translates queries and outcomes between `L₁` and `L₂` while preserving the
    observable spine `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Identity `BehaviorCodec` on a single language `L`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) : BehaviorCodec L L where
  encodeQuery := _root_.id
  decodeQuery := _root_.id
  encodeOut   := _root_.id
  decodeOut   := Option.some
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := congrArg L.obs (Option.some.inj h)

/-- Vertical composition of `BehaviorCodec`s across three languages. -/
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
    dsimp
    exact c₁₂.decodeOut_encodeOut o₁
  obs_decodeOut o₃ o₁ h := by
    dsimp [Option.bind] at h
    cases h₂ : c₂₃.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      nomatch h
    | some o₂ =>
      rw [h₂] at h
      dsimp at h
      exact Eq.trans (c₂₃.obs_decodeOut o₃ o₂ h₂) (c₁₂.obs_decodeOut o₂ o₁ h)

/-- Action of a `BehaviorCodec` on a source behavior `b₁`. -/
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b₁ : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b₁ (c.decodeQuery q₂)).defined
    val     := fun h₁ o₂ =>
      ∃ o₁ : L₁.Out, c.decodeOut o₂ = some o₁ ∧ (b₁ (c.decodeQuery q₂)).val h₁ o₁
  }

/-- Demonic compilation refinement (`Compiles`):
    `L_tgt.sem t ≤ c.toMorphism (L_src.sem s)`. -/
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Productive demonic compilation refinement (`ProductiveCompiles`):
    Conjoins demonic outcome inclusion (`Compiles`) with target productivity
    whenever the source is productive. -/
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₂ : L_tgt.Query,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined, ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

/-- Reflexivity of `ProductiveCompiles`. -/
theorem ProductiveCompiles.refl {SemObs : Type} (L : Language SemObs)
    (p : L.Prog) : ProductiveCompiles L L (BehaviorCodec.id L) p p := by
  refine ⟨fun q h => ⟨h, fun o ho => ⟨o, rfl, ho⟩⟩, fun q h => h⟩

/-- Vertical transitivity of `ProductiveCompiles` across `BehaviorCodec.comp`. -/
theorem ProductiveCompiles.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
    {c₁₂ : BehaviorCodec L₁ L₂} {c₂₃ : BehaviorCodec L₂ L₃}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : ProductiveCompiles L₁ L₂ c₁₂ p₁ p₂)
    (h₂₃ : ProductiveCompiles L₂ L₃ c₂₃ p₂ p₃) :
    ProductiveCompiles L₁ L₃ (c₁₂.comp c₂₃) p₁ p₃ := by
  refine ⟨?_, ?_⟩
  · intro q₃ h₁
    have ⟨h₂, hsub₂⟩ := h₁₂.1 (c₂₃.decodeQuery q₃) h₁
    have ⟨h₃, hsub₃⟩ := h₂₃.1 q₃ h₂
    refine ⟨h₃, fun o₃ ho₃ => ?_⟩
    have ⟨o₂, hdec₂₃, ho₂⟩ := hsub₃ o₃ ho₃
    have ⟨o₁, hdec₁₂, ho₁⟩ := hsub₂ o₂ ho₂
    refine ⟨o₁, ?_, ho₁⟩
    dsimp [BehaviorCodec.comp, Option.bind]
    rw [hdec₂₃]
    exact hdec₁₂
  · intro q₃ h_prod₁
    exact h₂₃.2 q₃ (h₁₂.2 (c₂₃.decodeQuery q₃) h_prod₁)

/-- Key lemma: `Compiles` maps every target observable outcome `L_tgt.Produces t q₂ v`
    back to the identical source observable outcome `L_src.Produces s (c.decodeQuery q₂) v`. -/
theorem Compiles.produces_imp {SemObs : Type} {L₁ L₂ : Language SemObs}
    {c : BehaviorCodec L₁ L₂} {s : L₁.Prog} {t : L₂.Prog}
    (h_comp : Compiles L₁ L₂ c s t) (q₂ : L₂.Query)
    (h_def₁ : (L₁.sem s (c.decodeQuery q₂)).defined) (v : SemObs)
    (h_prod₂ : L₂.Produces t q₂ v) :
    L₁.Produces s (c.decodeQuery q₂) v := by
  have ⟨_, o₂, ho₂, hobs₂⟩ := h_prod₂
  have ⟨h_def₂, h_sub⟩ := h_comp q₂ h_def₁
  have ⟨o₁, h_dec, ho₁⟩ := h_sub o₂ ho₂
  have h_obs_eq := c.obs_decodeOut o₂ o₁ h_dec
  exact ⟨h_def₁, o₁, ho₁, Eq.trans h_obs_eq.symm hobs₂⟩

/-- Primitive 4 (`Tool L_src L_tgt`):
    Partial compiler or verifier mapping `L_src.Prog` to `Partial L_tgt.Prog`. -/
abbrev Tool {SemObs : Type} (L_src L_tgt : Language SemObs) : Type :=
  L_src.Prog → Partial L_tgt.Prog

/-- Program `p` is accepted by `tool`. -/
abbrev Tool.Accepted {SemObs : Type} {L_src L_tgt : Language SemObs}
    (tool : Tool L_src L_tgt) (p : L_src.Prog) : Prop :=
  (tool p).defined

/-- Program `p` is rejected by `tool`. -/
abbrev Tool.Rejected {SemObs : Type} {L_src L_tgt : Language SemObs}
    (tool : Tool L_src L_tgt) (p : L_src.Prog) : Prop :=
  ¬ (tool p).defined

-- ============================================================================
-- Section 1: The 1-Trace vs. 2-Safety Expressiveness Separation & Demonic
-- Self-Composition Theorem (`SelfCompositionVsJitterTheorem`)
-- ============================================================================

/-!
### 1.1 Theorem 1A: 1-Trace Blindness to 2-Safety Side Channels (`PENTEST-7`)

Per Clarkson & Schneider (2010), a **1-trace property** is a set of individual
execution traces (a predicate on `(Query, SemObs)`), whereas **non-interference**
(Goguen & Meseguer 1982) and **constant-time execution** are **2-safety
hyperproperties** (sets of *sets* of traces constrained across pairs of traces
$(q_1, o_1), (q_2, o_2)$).

We first prove that when `SemObs` projects the functional output `o.1` (or for
any 1-trace functional specification `obsPost` that constrains only the input-to-value
relation), a constant-time cipher `.ctCipher` (`o = (pub + 1, 10)`) and a
secret-leaking cipher `.leakyCipher` (`o = (pub + 1, sec)`) have **identical**
1-trace observable semantics and satisfy the **exact same** 1-trace
specifications `VerifiedSpineOn`.
-/

/-- 3-program cryptographic AST (`PENTEST-7`, `PENTEST-R2-9A`):
    - `.ctCipher`: returns `pub + 1` in constant time `10`,
    - `.leakyCipher`: returns `pub + 1`, but leaks the secret key `sec` in its
      timing channel (`time = sec`),
    - `.badCipher`: returns `0` in constant time `0` (functionally broken,
      constant-time). -/
inductive CryptoProg where
  | ctCipher
  | leakyCipher
  | badCipher
  deriving DecidableEq

/-- 1-trace functional-projection language `L_crypto_1trace : Language Nat`:
    concrete outcomes are `(retVal, cycleCount) : Nat × Nat`, and the observable
    spine `obs o := o.1` projects the functional return value. -/
abbrev L_crypto_1trace : Language Nat where
  Prog  := CryptoProg
  Query := Nat × Nat
  Out   := Nat × Nat
  obs o := o.1
  sem p := fun (pub, sec) => match p with
    | .ctCipher    => Partial.pure (fun o => o = (pub + 1, 10))
    | .leakyCipher => Partial.pure (fun o => o = (pub + 1, sec))
    | .badCipher   => Partial.pure (fun o => o = (0, 0))

/-- Full timing-observable cryptographic language `L_crypto_full : Language (Nat × Nat)`:
    `obs := id` exposes both `(retVal, cycleCount)`. -/
abbrev L_crypto_full : Language (Nat × Nat) :=
  Language.mkSimple CryptoProg (Nat × Nat) (Nat × Nat) (fun p (pub, sec) =>
    match p with
    | .ctCipher    => Partial.pure (fun o => o = (pub + 1, 10))
    | .leakyCipher => Partial.pure (fun o => o = (pub + 1, sec))
    | .badCipher   => Partial.pure (fun o => o = (0, 0)))

/-- **Theorem 1A (1-Trace Blindness to 2-Safety Side Channels, `PENTEST-7`):**
    1. On `L_crypto_1trace` (`obs o := o.1`), `.ctCipher` and `.leakyCipher`
       produce the **exact same** observable outcomes at every query `q`:
       `∀ q v, L_crypto_1trace.Produces .ctCipher q v ↔ L_crypto_1trace.Produces .leakyCipher q v`.
    2. Consequently, for **every** domain `dom`, precondition `pre`, and 1-trace
       specification `obsPost : (Nat × Nat) → Nat → Prop`, `.ctCipher` satisfies
       `VerifiedSpineOn` **if and only if** `.leakyCipher` satisfies
       `VerifiedSpineOn`!
    3. Even on `L_crypto_full` (`obs := id`), `.leakyCipher` satisfies the
       1-trace functional specification `obsPost (pub, _) (ret, _) := (ret = pub + 1)`
       while leaking the secret key across distinct secrets `sec₁ = 11 ≠ 22 = sec₂`! -/
theorem theorem1a_one_trace_blind_to_two_safety :
    (∀ (q : Nat × Nat) (v : Nat),
      L_crypto_1trace.Produces .ctCipher q v ↔
      L_crypto_1trace.Produces .leakyCipher q v) ∧
    (∀ (dom pre : (Nat × Nat) → Prop) (obsPost : (Nat × Nat) → Nat → Prop),
      L_crypto_1trace.VerifiedSpineOn dom pre obsPost .ctCipher ↔
      L_crypto_1trace.VerifiedSpineOn dom pre obsPost .leakyCipher) ∧
    L_crypto_full.VerifiedSpine (fun q => q.1 < 100)
      (fun q v => v.1 = q.1 + 1) .leakyCipher ∧
    (∃ (pub sec₁ sec₂ : Nat) (v₁ v₂ : Nat × Nat),
      L_crypto_full.Produces .leakyCipher (pub, sec₁) v₁ ∧
      L_crypto_full.Produces .leakyCipher (pub, sec₂) v₂ ∧
      v₁.2 ≠ v₂.2) := by
  have h_prod_iff :
      ∀ (q : Nat × Nat) (v : Nat),
        L_crypto_1trace.Produces .ctCipher q v ↔
        L_crypto_1trace.Produces .leakyCipher q v := by
    intro (pub, sec) v
    constructor
    · intro ⟨_, o, ho, hobs⟩
      dsimp [L_crypto_1trace, Partial.pure] at ho hobs
      have hv : pub + 1 = v := Eq.trans (congrArg Prod.fst ho).symm hobs
      exact ⟨trivial, (pub + 1, sec), rfl, hv⟩
    · intro ⟨_, o, ho, hobs⟩
      dsimp [L_crypto_1trace, Partial.pure] at ho hobs
      have hv : pub + 1 = v := Eq.trans (congrArg Prod.fst ho).symm hobs
      exact ⟨trivial, (pub + 1, 10), rfl, hv⟩
  refine ⟨h_prod_iff, ?_, ?_, 0, 11, 22, (1, 11), (1, 22),
    ⟨trivial, (1, 11), rfl, rfl⟩, ⟨trivial, (1, 22), rfl, rfl⟩, by decide⟩
  · intro dom pre obsPost
    constructor
    · intro ⟨h_nv, _, h_ref⟩
      refine ⟨h_nv, fun (pub, sec) _ => ⟨trivial, (pub + 1, sec), rfl⟩, ?_⟩
      intro (pub, sec) h_pre
      refine ⟨trivial, fun o ho => ?_⟩
      dsimp [L_crypto_1trace, Partial.pure] at ho
      have h_sub := (h_ref (pub, sec) h_pre).2 (pub + 1, 10) rfl
      dsimp [Language.SpecOn, L_crypto_1trace] at h_sub ⊢
      rw [ho]
      exact h_sub
    · intro ⟨h_nv, _, h_ref⟩
      refine ⟨h_nv, fun (pub, _) _ => ⟨trivial, (pub + 1, 10), rfl⟩, ?_⟩
      intro (pub, sec) h_pre
      refine ⟨trivial, fun o ho => ?_⟩
      dsimp [L_crypto_1trace, Partial.pure] at ho
      have h_sub := (h_ref (pub, sec) h_pre).2 (pub + 1, sec) rfl
      dsimp [Language.SpecOn, L_crypto_1trace] at h_sub ⊢
      rw [ho]
      exact h_sub
  · refine ⟨Or.inl ⟨(0, 0), by decide⟩,
      fun (pub, sec) _ => ⟨trivial, (pub + 1, sec), rfl⟩,
      fun (pub, sec) _ => ⟨trivial, fun o ho => ?_⟩⟩
    dsimp [L_crypto_full, Language.mkSimple, Partial.pure] at ho
    dsimp [Language.SpecOn, L_crypto_full, Language.mkSimple]
    rw [ho]

/-!
### 1.2 Theorem 1B: Demonic Self-Composition `Language.diag` & The Timing-Jitter Lockout (`PENTEST-R2-9A/B`)

Barthe, D'Argenio & Rezk (2004) and Terauchi & Aiken (2005) showed that for
**deterministic** programs, 2-safety non-interference reduces to a standard
1-trace safety property of the self-composed product program $(p, p)$ running on
`L.diag`.

What happens when we apply demonic self-composition `L.diag` in a semantic
framework that supports nondeterminism? We prove the **Exact Characterization
Theorem for Demonic Self-Composition**:
$$\text{VerifiedSpineOn}_{L.\text{diag}}(\text{DiagPre}(\text{pre}, \text{lowEq}), \text{DiagPost}(\text{leakEq}), p)
  \;\Longleftrightarrow\;
  \text{NonInterferingOn}_L(\text{pre}, \text{lowEq}, \text{leakEq}, p)
  \;\wedge\;
  \text{LeakageDeterministicOn}_L(\text{pre}, \text{leakEq}, p).$$
-/

/-- Synchronized product of two languages `L₁` and `L₂`. -/
abbrev Language.prod {SemObs₁ SemObs₂ : Type}
    (L₁ : Language SemObs₁) (L₂ : Language SemObs₂) :
    Language (SemObs₁ × SemObs₂) where
  Prog  := L₁.Prog × L₂.Prog
  Query := L₁.Query × L₂.Query
  Out   := L₁.Out × L₂.Out
  obs o := (L₁.obs o.1, L₂.obs o.2)
  sem p q := {
    defined := (L₁.sem p.1 q.1).defined ∧ (L₂.sem p.2 q.2).defined
    val     := fun h o =>
      (L₁.sem p.1 q.1).val h.1 o.1 ∧ (L₂.sem p.2 q.2).val h.2 o.2
  }
  dom q := L₁.dom q.1 ∧ L₂.dom q.2

/-- Diagonal 2-safety self-composition of a single language `L` (`Language.diag`):
    `(L.diag).Prog = L.Prog` judgmentally (`rfl`), and `(L.diag).sem p (q₁, q₂)`
    runs two independent copies of `p` on `q₁` and `q₂`. -/
abbrev Language.diag {SemObs : Type} (L : Language SemObs) :
    Language (SemObs × SemObs) where
  Prog  := L.Prog
  Query := L.Query × L.Query
  Out   := L.Out × L.Out
  obs o := (L.obs o.1, L.obs o.2)
  sem p q := (L.prod L).sem (p, p) q
  dom q   := L.dom q.1 ∧ L.dom q.2

/-- 2-safety diagonal precondition on `L.diag`: both queries satisfy `pre` and
    are low-equivalent (`lowEq q.1 q.2`). -/
def DiagPre {Query : Type} (pre : Query → Prop)
    (lowEq : Query → Query → Prop) (q : Query × Query) : Prop :=
  pre q.1 ∧ pre q.2 ∧ lowEq q.1 q.2

/-- 2-safety diagonal postcondition on `L.diag`: the two observable outcomes
    are leakage-equivalent (`leakEq v.1 v.2`). -/
def DiagPost {Query SemObs : Type} (leakEq : SemObs → SemObs → Prop)
    (_ : Query × Query) (v : SemObs × SemObs) : Prop :=
  leakEq v.1 v.2

/-- **PENTEST-R2-9A Theorem (Timing-Only `L.diag` Specification Certifies
    Functionally Broken `.badCipher`):**
    If a 2-safety postcondition on `L_crypto_full.diag` checks only timing
    equality (`v.1.2 = v.2.2`) without conjoining 1-trace functional correctness
    (`v.1.1 = q.1.1 + 1`), then `.badCipher` (which ignores `pub` and always
    returns `(0, 0)`) satisfies `VerifiedSpine` on `L_crypto_full.diag` while
    violating functional correctness at every query! -/
theorem pentest_r2_9a_timing_only_diag_certifies_badCipher :
    L_crypto_full.diag.VerifiedSpine
      (DiagPre (fun q => q.1 < 100) (fun q₁ q₂ => q₁.1 = q₂.1))
      (DiagPost (fun v₁ v₂ => v₁.2 = v₂.2))
      .badCipher ∧
    L_crypto_full.ViolatesSpine (fun q => q.1 < 100)
      (fun q v => v.1 = q.1 + 1) .badCipher := by
  refine ⟨⟨Or.inl ⟨((0, 0), (0, 0)), ⟨by decide, by decide, rfl⟩⟩, ?_, ?_⟩,
    ⟨(0, 0), by decide, fun _ => ⟨(0, 0), rfl, by decide⟩⟩⟩
  · intro ((_, _), (_, _)) _
    exact ⟨⟨trivial, trivial⟩, ((0, 0), (0, 0)), rfl, rfl⟩
  · intro ((_, _), (_, _)) _
    refine ⟨⟨trivial, trivial⟩, fun (o₁, o₂) ⟨ho₁, ho₂⟩ => ?_⟩
    dsimp [L_crypto_full, Language.mkSimple, Partial.pure] at ho₁ ho₂
    dsimp [Language.SpecOn, Language.diag, DiagPost]
    rw [ho₁, ho₂]

/-- One-way possibilistic 2-safety non-interference (`Language.NonInterferingOn`):
    whenever `lowEq q₁ q₂`, every observable outcome `v₁` of `prog` at `q₁` is
    matched up to `leakEq` by some observable outcome `v₂` of `prog` at `q₂`. -/
def Language.NonInterferingOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  ∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → lowEq q₁ q₂ →
    ∀ v₁ : SemObs, L.Produces prog q₁ v₁ →
      ∃ v₂ : SemObs, L.Produces prog q₂ v₂ ∧ leakEq v₁ v₂

/-- Per-query leakage determinism (`Language.LeakageDeterministicOn`):
    at any single valid query `q`, any two outcomes `v₁, v₂` produced by `prog`
    at `q` are leakage-equivalent (`leakEq v₁ v₂`). -/
def Language.LeakageDeterministicOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  ∀ q : L.Query, pre q →
    ∀ v₁ v₂ : SemObs, L.Produces prog q v₁ → L.Produces prog q v₂ →
      leakEq v₁ v₂

/-- All-pairs demonic 2-safety (`Language.AllPairsNonInterferingOn`):
    for any low-equivalent queries `q₁, q₂`, *every* pair of outcomes `v₁` at `q₁`
    and `v₂` at `q₂` satisfies `leakEq v₁ v₂`. -/
def Language.AllPairsNonInterferingOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  ∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → lowEq q₁ q₂ →
    ∀ v₁ v₂ : SemObs, L.Produces prog q₁ v₁ → L.Produces prog q₂ v₂ →
      leakEq v₁ v₂

/-- **Theorem 1B (Exact Characterization of Demonic Self-Composition `L.diag`):**
    Let `lowEq` be reflexive on `pre` and `leakEq` be symmetric and transitive,
    and let `p` be productive on `pre`. Then the following three conditions are
    logically equivalent:
    1. `(L.diag).sem p ≤ (L.diag).SpineSpecOn (DiagPre pre lowEq) (DiagPost leakEq)`
       (demonic self-composition 2-safety on `L.diag`),
    2. `L.AllPairsNonInterferingOn pre lowEq leakEq p`,
    3. `L.NonInterferingOn pre lowEq leakEq p ∧ L.LeakageDeterministicOn pre leakEq p`
       (possibilistic non-interference **plus** per-query leakage determinism)! -/
theorem theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic
    {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (h_low_refl : ∀ q, pre q → lowEq q q)
    (h_leak_symm : ∀ {v₁ v₂}, leakEq v₁ v₂ → leakEq v₂ v₁)
    (h_leak_trans : ∀ {v₁ v₂ v₃}, leakEq v₁ v₂ → leakEq v₂ v₃ → leakEq v₁ v₃)
    (p : L.Prog)
    (h_prod : L.ProductiveOn pre p) :
    ((L.diag).sem p ≤ (L.diag).SpineSpecOn (DiagPre pre lowEq) (DiagPost leakEq) ↔
      L.AllPairsNonInterferingOn pre lowEq leakEq p) ∧
    (L.AllPairsNonInterferingOn pre lowEq leakEq p ↔
      (L.NonInterferingOn pre lowEq leakEq p ∧
       L.LeakageDeterministicOn pre leakEq p)) := by
  have h_diag_iff_all :
      (L.diag).sem p ≤ (L.diag).SpineSpecOn (DiagPre pre lowEq) (DiagPost leakEq) ↔
        L.AllPairsNonInterferingOn pre lowEq leakEq p := by
    constructor
    · intro h_diag q₁ q₂ hq₁ hq₂ hlow v₁ v₂
        ⟨hdef₁, o₁, ho₁, hv₁⟩ ⟨hdef₂, o₂, ho₂, hv₂⟩
      have ⟨_, h_sub⟩ := h_diag (q₁, q₂) ⟨hq₁, hq₂, hlow⟩
      have h_post := h_sub (o₁, o₂) ⟨ho₁, ho₂⟩
      dsimp [Language.SpineSpecOn, Language.SpecOn, Language.diag, DiagPost] at h_post
      rw [← hv₁, ← hv₂]
      exact h_post
    · intro h_all (q₁, q₂) ⟨hq₁, hq₂, hlow⟩
      have ⟨hdef₁, _⟩ := h_prod q₁ hq₁
      have ⟨hdef₂, _⟩ := h_prod q₂ hq₂
      refine ⟨⟨hdef₁, hdef₂⟩, fun (o₁, o₂) ⟨ho₁, ho₂⟩ => ?_⟩
      exact h_all q₁ q₂ hq₁ hq₂ hlow (L.obs o₁) (L.obs o₂)
        ⟨hdef₁, o₁, ho₁, rfl⟩ ⟨hdef₂, o₂, ho₂, rfl⟩
  refine ⟨h_diag_iff_all, ?_⟩
  constructor
  · intro h_all
    refine ⟨?_, ?_⟩
    · intro q₁ q₂ hq₁ hq₂ hlow v₁ hv₁
      have ⟨hdef₂, o₂, ho₂⟩ := h_prod q₂ hq₂
      exact ⟨L.obs o₂, ⟨hdef₂, o₂, ho₂, rfl⟩,
        h_all q₁ q₂ hq₁ hq₂ hlow v₁ (L.obs o₂) hv₁ ⟨hdef₂, o₂, ho₂, rfl⟩⟩
    · intro q hq v₁ v₂ hv₁ hv₂
      exact h_all q q hq hq (h_low_refl q hq) v₁ v₂ hv₁ hv₂
  · intro ⟨h_ni, h_det⟩ q₁ q₂ hq₁ hq₂ hlow v₁ v₂ hv₁ hv₂
    have ⟨v₂', hv₂', h_eq₁₂'⟩ := h_ni q₁ q₂ hq₁ hq₂ hlow v₁ hv₁
    have h_eq₂'₂ := h_det q₂ hq₂ v₂' v₂ hv₂' hv₂
    exact h_leak_trans h_eq₁₂' (h_leak_symm (h_leak_symm h_eq₂'₂))

/-- Cryptographic language `L_crypto_jitter` with secret-independent hardware
    timing jitter (`PENTEST-R2-9B`):
    - Program `true` (`.ctJitterCipher`) computes `pub + 1` and takes either `10`
      or `11` cycles due to secret-independent bus/interrupt jitter
      (`o = (pub + 1, 10) ∨ o = (pub + 1, 11)`).
    - Program `false` (`.leakyCipher`) computes `pub + 1` and takes `sec` cycles. -/
abbrev L_crypto_jitter : Language (Nat × Nat) :=
  Language.mkSimple Bool (Nat × Nat) (Nat × Nat) (fun isCt (pub, sec) =>
    if isCt then
      Partial.pure (fun o => o = (pub + 1, 10) ∨ o = (pub + 1, 11))
    else
      Partial.pure (fun o => o = (pub + 1, sec)))

/-- **Corollary 1B.1 (`PENTEST-R2-9B`: Demonic Self-Composition `L.diag` Locks
    Out Secret-Independent Timing Jitter):**
    On `L_crypto_jitter`, program `true` (`ctJitterCipher`):
    1. Has semantic behavior that is **100% invariant across all secret keys**:
       `∀ pub sec₁ sec₂, L_crypto_jitter.sem true (pub, sec₁) = L_crypto_jitter.sem true (pub, sec₂)`.
    2. Satisfies possibilistic 2-safety `NonInterferingOn` under exact timing
       equality `v₁.2 = v₂.2`.
    3. Yet **violates** demonic self-composition `ViolatesSpine` on
       `L_crypto_jitter.diag` (because run 1 can take `10` cycles while run 2
       takes `11` cycles, `10 ≠ 11`), so `true` is **rejected** by
       `L_crypto_jitter.diag.VerifiedSpine`! -/
theorem pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter :
    (∀ pub sec₁ sec₂ : Nat,
      L_crypto_jitter.sem true (pub, sec₁) =
      L_crypto_jitter.sem true (pub, sec₂)) ∧
    L_crypto_jitter.NonInterferingOn (fun q => q.1 < 100)
      (fun q₁ q₂ => q₁.1 = q₂.1) (fun v₁ v₂ => v₁.2 = v₂.2) true ∧
    L_crypto_jitter.diag.ViolatesSpine
      (DiagPre (fun q => q.1 < 100) (fun q₁ q₂ => q₁.1 = q₂.1))
      (DiagPost (fun v₁ v₂ => v₁.2 = v₂.2))
      true ∧
    ¬ L_crypto_jitter.diag.VerifiedSpine
        (DiagPre (fun q => q.1 < 100) (fun q₁ q₂ => q₁.1 = q₂.1))
        (DiagPost (fun v₁ v₂ => v₁.2 = v₂.2))
        true := by
  have h_viol :
      L_crypto_jitter.diag.ViolatesSpine
        (DiagPre (fun q => q.1 < 100) (fun q₁ q₂ => q₁.1 = q₂.1))
        (DiagPost (fun v₁ v₂ => v₁.2 = v₂.2))
        true :=
    ⟨((0, 0), (0, 0)), ⟨by decide, by decide, rfl⟩,
      fun _ => ⟨((1, 10), (1, 11)), ⟨Or.inl rfl, Or.inr rfl⟩, by
        dsimp [DiagPost, Language.diag, L_crypto_jitter, Language.mkSimple]
        decide⟩⟩
  refine ⟨fun _ _ _ => rfl, ?_, h_viol,
    Language.violatesSpine_not_verifiedSpineOn h_viol⟩
  intro (pub₁, sec₁) (pub₂, sec₂) _ _ _ v₁ ⟨_, o₁, ho₁, hv₁⟩
  dsimp [L_crypto_jitter, Language.mkSimple, Partial.pure] at ho₁ hv₁
  cases ho₁ with
  | inl h10 =>
    have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm h10)
    exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), Or.inl rfl, rfl⟩, hv₁_2⟩
  | inr h11 =>
    have hv₁_2 : v₁.2 = 11 := congrArg Prod.snd (Eq.trans hv₁.symm h11)
    exact ⟨(pub₂ + 1, 11), ⟨trivial, (pub₂ + 1, 11), Or.inr rfl, rfl⟩, hv₁_2⟩

-- ============================================================================
-- Section 2: One-Way Simulation Failure vs. Symmetric PER / Bisimulation
-- 2-Safety (`BisimulationTwoSafetyLaws`)
-- ============================================================================

/-!
### 2.1 Theorem 2A: Asymmetric Preorder & Subset-Timing Bypass of One-Way `NonInterferingOn` (`PENTEST-R3-7`), Policy Degeneracies (`PENTEST-R3-6A/B`), and Positional Tuple Bypasses (`PENTEST-R4-5A/B`)

When `NonInterferingOn` is stated as a one-directional existential simulation:
$$\text{lowEq}(q_1, q_2) \to \forall v_1 \in \text{Produces}(p, q_1),\ \exists v_2 \in \text{Produces}(p, q_2),\ \text{leakEq}(v_1, v_2),$$
any asymmetric preorder `lowEq` (such as `pub₁ = pub₂ ∧ sec₁ ≤ sec₂`) allows the
set of timing observations to grow monotonically with the secret (`{10} ⊂ {10, 20}`).
Observing `20` cycles immediately reveals `sec > 0` with 100% certainty!
-/

/-- 3-program AST for `PENTEST-R3-7` & `PENTEST-R3-6B`:
    - `.subsetLeakyCipher`: produces timing `{10}` when `sec = 0`, and `{10, 20}`
      when `sec > 0` (leaking `sec > 0` whenever `20` cycles is observed!).
    - `.backdoorLeakyCipher`: produces timing `10` when `sec < 2`, and timing
      `sec` when `sec ≥ 2` (leaking all secret keys `sec ≥ 2`!).
    - `.leakyCipher`: produces timing `sec` on all keys. -/
inductive SubsetAndBackdoorCryptoProg where
  | subsetLeakyCipher
  | backdoorLeakyCipher
  | leakyCipher
  deriving DecidableEq

/-- Semantics for `SubsetAndBackdoorCryptoProg`. -/
abbrev L_subset_crypto : Language (Nat × Nat) :=
  Language.mkSimple SubsetAndBackdoorCryptoProg (Nat × Nat) (Nat × Nat)
    (fun p (pub, sec) => match p with
      | .subsetLeakyCipher =>
        Partial.pure (fun o =>
          if sec = 0 then o = (pub + 1, 10)
          else o = (pub + 1, 10) ∨ o = (pub + 1, 20))
      | .backdoorLeakyCipher =>
        Partial.pure (fun o =>
          if sec < 2 then o = (pub + 1, 10)
          else o = (pub + 1, sec))
      | .leakyCipher =>
        Partial.pure (fun o => o = (pub + 1, sec)))

/-- Two-way possibilistic bisimulation 2-safety (`SymmetricBiNonInterferingOn`):
    requires both forward (`q₁ → q₂`) and backward (`q₂ → q₁`) leakage matching. -/
def Language.SymmetricBiNonInterferingOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.NonInterferingOn pre lowEq leakEq prog ∧
  (∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → lowEq q₁ q₂ →
    ∀ v₂ : SemObs, L.Produces prog q₂ v₂ →
      ∃ v₁ : SemObs, L.Produces prog q₁ v₁ ∧ leakEq v₁ v₂)

/-- **Theorem 2A.1 (`PENTEST-R3-7`: Asymmetric Preorder & Subset-Timing Bypass
    of One-Way `NonInterferingOn` vs. Two-Way Bisimulation Refutation):**
    1. Under the asymmetric preorder `lowEq (pub₁, sec₁) (pub₂, sec₂) := (pub₁ = pub₂ ∧ sec₁ ≤ sec₂)`
       and exact timing equality `leakEq v₁ v₂ := (v₁.2 = v₂.2)`,
       `.subsetLeakyCipher` **satisfies one-way `NonInterferingOn`** while
       `.leakyCipher` is refuted (`¬ NonInterferingOn`),
    2. Yet `.subsetLeakyCipher` leaks `sec > 0` whenever timing `20` is observed
       (`Produces .subsetLeakyCipher (0, 1) (1, 20) ∧ ¬ Produces .subsetLeakyCipher (0, 0) (1, 20)`),
    3. And two-way `SymmetricBiNonInterferingOn` **rejects** `.subsetLeakyCipher`
       even under the same asymmetric preorder `sec₁ ≤ sec₂`! -/
theorem pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak :
    L_subset_crypto.NonInterferingOn (fun q => q.1 < 100)
      (fun q₁ q₂ => q₁.1 = q₂.1 ∧ q₁.2 ≤ q₂.2)
      (fun v₁ v₂ => v₁.2 = v₂.2)
      .subsetLeakyCipher ∧
    ¬ L_subset_crypto.NonInterferingOn (fun q => q.1 < 100)
        (fun q₁ q₂ => q₁.1 = q₂.1 ∧ q₁.2 ≤ q₂.2)
        (fun v₁ v₂ => v₁.2 = v₂.2)
        .leakyCipher ∧
    L_subset_crypto.Produces .subsetLeakyCipher (0, 1) (1, 20) ∧
    (∀ v₀ : Nat × Nat,
      L_subset_crypto.Produces .subsetLeakyCipher (0, 0) v₀ → v₀.2 ≠ 20) ∧
    ¬ L_subset_crypto.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
        (fun q₁ q₂ => q₁.1 = q₂.1 ∧ q₁.2 ≤ q₂.2)
        (fun v₁ v₂ => v₁.2 = v₂.2)
        .subsetLeakyCipher := by
  refine ⟨?_, ?_, ⟨trivial, (1, 20), Or.inr rfl, rfl⟩, ?_, ?_⟩
  · intro (pub₁, sec₁) (pub₂, sec₂) _ _ ⟨_, hle⟩ v₁ ⟨_, o₁, ho₁, hv₁⟩
    cases sec₁ with
    | zero =>
      have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
      cases sec₂ with
      | zero =>
        exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), rfl, rfl⟩, hv₁_2⟩
      | succ n₂ =>
        exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), Or.inl rfl, rfl⟩, hv₁_2⟩
    | succ n₁ =>
      cases sec₂ with
      | zero =>
        cases hle
      | succ n₂ =>
        dsimp [L_subset_crypto, Language.mkSimple, Partial.pure] at ho₁
        cases ho₁ with
        | inl h10 =>
          have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm h10)
          exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), Or.inl rfl, rfl⟩, hv₁_2⟩
        | inr h20 =>
          have hv₁_2 : v₁.2 = 20 := congrArg Prod.snd (Eq.trans hv₁.symm h20)
          exact ⟨(pub₂ + 1, 20), ⟨trivial, (pub₂ + 1, 20), Or.inr rfl, rfl⟩, hv₁_2⟩
  · intro h_ni
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, heq⟩ :=
      h_ni (0, 0) (0, 1) (by decide) (by decide) ⟨rfl, by decide⟩
        (1, 0) ⟨trivial, (1, 0), rfl, rfl⟩
    have hv₂_2 : v₂.2 = 1 := congrArg Prod.snd (Eq.trans hv₂.symm ho₂)
    have h01 : (0 : Nat) = 1 := Eq.trans heq hv₂_2
    cases h01
  · intro v₀ ⟨_, o₀, ho₀, hv₀⟩ h20
    have hv₀_2 : v₀.2 = 10 := congrArg Prod.snd (Eq.trans hv₀.symm ho₀)
    have h10_20 : (10 : Nat) = 20 := Eq.trans hv₀_2.symm h20
    cases h10_20
  · intro ⟨_, h_back⟩
    have ⟨v₁, ⟨_, o₁, ho₁, hv₁⟩, heq⟩ :=
      h_back (0, 0) (0, 1) (by decide) (by decide) ⟨rfl, by decide⟩
        (1, 20) ⟨trivial, (1, 20), Or.inr rfl, rfl⟩
    have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
    have h10_20 : (10 : Nat) = 20 := Eq.trans hv₁_2.symm heq
    cases h10_20

/-- **Symmetry Equivalence Lemma (`symmetry_converts_one_way_to_two_way`):**
    Whenever `lowEq` and `leakEq` are symmetric relations, one-way
    `NonInterferingOn` is logically equivalent (`↔`) to two-way
    `SymmetricBiNonInterferingOn`. -/
theorem symmetry_converts_one_way_to_two_way {SemObs : Type}
    (L : Language SemObs) (pre : L.Query → Prop)
    (lowEq : L.Query → L.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (h_low_symm : ∀ {q₁ q₂}, lowEq q₁ q₂ → lowEq q₂ q₁)
    (h_leak_symm : ∀ {v₁ v₂}, leakEq v₁ v₂ → leakEq v₂ v₁)
    (p : L.Prog) :
    L.NonInterferingOn pre lowEq leakEq p ↔
    L.SymmetricBiNonInterferingOn pre lowEq leakEq p := by
  constructor
  · intro h_ni
    refine ⟨h_ni, fun q₁ q₂ hq₁ hq₂ hlow v₂ hv₂ => ?_⟩
    have ⟨v₁, hv₁, hleak⟩ := h_ni q₂ q₁ hq₂ hq₁ (h_low_symm hlow) v₂ hv₂
    exact ⟨v₁, hv₁, h_leak_symm hleak⟩
  · exact And.left

/-- **Theorem 2A.2 (`PENTEST-R2-9` & `PENTEST-R3-6A/B`: Policy-Relation
    Degeneracies Even Under Symmetric Equivalence Relations):**
    Even when `lowEq` and `leakEq` are genuine equivalence relations and
    two-way `SymmetricBiNonInterferingOn` is used:
    1. **Trivial `lowEq := Eq` (`PENTEST-R2-9`):** `.leakyCipher` satisfies
       `SymmetricBiNonInterferingOn` under `lowEq := Eq` and exact timing equality
       `v₁.2 = v₂.2` (because changing the secret key changes `q`).
    2. **Punctured Equivalence Relation `lowEq` (`PENTEST-R3-6B`):** Under the
       equivalence relation `lowEq q₁ q₂ := (q₁.1 = q₂.1 ∧ (q₁.2 = q₂.2 ∨ (q₁.2 < 2 ∧ q₂.2 < 2)))`,
       `.leakyCipher` is refuted at `sec = 0` vs `sec = 1`, yet
       `.backdoorLeakyCipher` (which leaks every master key `sec ≥ 2`) satisfies
       `SymmetricBiNonInterferingOn`!
    3. **Timing-Blind Equivalence Relation `leakEq` (`PENTEST-R3-6A`):** Under the
       equivalence relation `leakEq v₁ v₂ := (v₁.1 = v₂.1)` (ignoring the timing
       component `v.2`), `.leakyCipher` satisfies `SymmetricBiNonInterferingOn`! -/
theorem pentest_r3_6_policy_degeneracies :
    L_subset_crypto.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
      Eq (fun v₁ v₂ => v₁.2 = v₂.2) .leakyCipher ∧
    L_subset_crypto.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
      (fun q₁ q₂ => q₁.1 = q₂.1 ∧ (q₁.2 = q₂.2 ∨ (q₁.2 < 2 ∧ q₂.2 < 2)))
      (fun v₁ v₂ => v₁.2 = v₂.2)
      .backdoorLeakyCipher ∧
    ¬ L_subset_crypto.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
        (fun q₁ q₂ => q₁.1 = q₂.1 ∧ (q₁.2 = q₂.2 ∨ (q₁.2 < 2 ∧ q₂.2 < 2)))
        (fun v₁ v₂ => v₁.2 = v₂.2)
        .leakyCipher ∧
    L_subset_crypto.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
      (fun q₁ q₂ => q₁.1 = q₂.1) (fun v₁ v₂ => v₁.1 = v₂.1) .leakyCipher := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨fun q₁ q₂ _ _ h_eq v₁ hv₁ => by subst h_eq; exact ⟨v₁, hv₁, rfl⟩,
      fun q₁ q₂ _ _ h_eq v₂ hv₂ => by subst h_eq; exact ⟨v₂, hv₂, rfl⟩⟩
  · have h_one_way :
        L_subset_crypto.NonInterferingOn (fun q => q.1 < 100)
          (fun q₁ q₂ => q₁.1 = q₂.1 ∧ (q₁.2 = q₂.2 ∨ (q₁.2 < 2 ∧ q₂.2 < 2)))
          (fun v₁ v₂ => v₁.2 = v₂.2)
          .backdoorLeakyCipher := by
      intro (pub₁, sec₁) (pub₂, sec₂) _ _ ⟨_, h_sec⟩ v₁ ⟨_, o₁, ho₁, hv₁⟩
      dsimp at h_sec
      cases h_sec with
      | inl h_eq =>
        subst h_eq
        dsimp [L_subset_crypto, Language.mkSimple, Partial.pure] at ho₁
        by_cases hlt : sec₁ < 2
        · simp [hlt] at ho₁
          have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
          exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), by simp [Partial.pure, hlt], rfl⟩, hv₁_2⟩
        · simp [hlt] at ho₁
          have hv₁_2 : v₁.2 = sec₁ := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
          exact ⟨(pub₂ + 1, sec₁), ⟨trivial, (pub₂ + 1, sec₁), by simp [Partial.pure, hlt], rfl⟩, hv₁_2⟩
      | inr h_both =>
        dsimp [L_subset_crypto, Language.mkSimple, Partial.pure] at ho₁
        simp [h_both.1] at ho₁
        have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
        exact ⟨(pub₂ + 1, 10),
          ⟨trivial, (pub₂ + 1, 10), by simp [Partial.pure, h_both.2], rfl⟩, hv₁_2⟩
    exact (symmetry_converts_one_way_to_two_way L_subset_crypto (fun q => q.1 < 100)
      _ _ (fun ⟨hp, hs⟩ => ⟨hp.symm, match hs with
        | Or.inl h => Or.inl h.symm
        | Or.inr ⟨h₁, h₂⟩ => Or.inr ⟨h₂, h₁⟩⟩)
      (fun h => h.symm) .backdoorLeakyCipher).mp h_one_way
  · intro ⟨h_ni, _⟩
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, heq⟩ :=
      h_ni (0, 0) (0, 1) (by decide) (by decide) ⟨rfl, Or.inr ⟨by decide, by decide⟩⟩
        (1, 0) ⟨trivial, (1, 0), rfl, rfl⟩
    have hv₂_2 : v₂.2 = 1 := congrArg Prod.snd (Eq.trans hv₂.symm ho₂)
    have h01 : (0 : Nat) = 1 := Eq.trans heq hv₂_2
    cases h01
  · have h_one_way :
        L_subset_crypto.NonInterferingOn (fun q => q.1 < 100)
          (fun q₁ q₂ => q₁.1 = q₂.1) (fun v₁ v₂ => v₁.1 = v₂.1) .leakyCipher := by
      intro (pub₁, sec₁) (pub₂, sec₂) _ _ h_pub v₁ ⟨_, o₁, ho₁, hv₁⟩
      dsimp at h_pub
      subst h_pub
      have hv₁_1 : v₁.1 = pub₁ + 1 := congrArg Prod.fst (Eq.trans hv₁.symm ho₁)
      exact ⟨(pub₁ + 1, sec₂), ⟨trivial, (pub₁ + 1, sec₂), rfl, rfl⟩, hv₁_1⟩
    exact (symmetry_converts_one_way_to_two_way L_subset_crypto (fun q => q.1 < 100)
      _ _ (fun h => h.symm) (fun h => h.symm) .leakyCipher).mp h_one_way

/-- Positional binary product typeclasses (`Candidate 016` `CanonicalPublicQuery`
    and `CanonicalLeakageObs`, `PENTEST-R4-5A/B`). -/
class PositionalPublicQuery (Query : Type) where
  Pub : Type
  pubProj : Query → Pub

instance instPositionalPublicQueryProd (A B : Type) :
    PositionalPublicQuery (A × B) :=
  ⟨A, fun q => q.1⟩

class PositionalLeakageObs (SemObs : Type) where
  Val : Type
  Leak : Type
  funcProj : SemObs → Val
  leakProj : SemObs → Leak

instance instPositionalLeakageObsProd (A B : Type) :
    PositionalLeakageObs (A × B) :=
  ⟨A, B, fun v => v.1, fun v => v.2⟩

/-- Left-associated 3-tuple query language `L_two_secrets` (`Query = (Nat × Nat) × Nat`,
    modeling `((pub, sec₁), sec₂)`, `PENTEST-R4-5A`) where program `true` leaks
    `sec₁` directly in the timing channel `o = (pub + 1, sec₁)`. -/
abbrev L_two_secrets : Language (Nat × Nat) :=
  Language.mkSimple Bool ((Nat × Nat) × Nat) (Nat × Nat)
    (fun leakFirst ((pub, sec₁), sec₂) =>
      if leakFirst then
        Partial.pure (fun o => o = (pub + 1, sec₁))
      else
        Partial.pure (fun o => o = (pub + 1, sec₂)))

/-- Left-associated 3-tuple observation language `L_multi_channel`
    (`SemObs = (Nat × Nat) × Nat`, modeling `((ret, cycles), cacheTag)`,
    `PENTEST-R4-5B`) where program `true` leaks `sec` in `cycles`
    `o = ((pub + 1, sec), 10)`. -/
abbrev L_multi_channel : Language ((Nat × Nat) × Nat) :=
  Language.mkSimple Bool (Nat × Nat) ((Nat × Nat) × Nat)
    (fun leakCycles (pub, sec) =>
      if leakCycles then
        Partial.pure (fun o => o = ((pub + 1, sec), 10))
      else
        Partial.pure (fun o => o = ((pub + 1, 10), sec)))

/-- **Theorem 2A.3 (`PENTEST-R4-5A/B`: Positional Tuple Projection Typeclasses
    Misclassify Multi-Secret Queries and Multi-Channel Observations):**
    1. **`PENTEST-R4-5A`:** On `Query = (Nat × Nat) × Nat` (`((pub, sec₁), sec₂)`),
       `instPositionalPublicQueryProd` projects `pubProj q = (pub, sec₁)`, so
       `L_two_secrets` program `true` (`o = (pub + 1, sec₁)`) satisfies
       `SymmetricBiNonInterferingOn` under `pubProj q₁ = pubProj q₂` while
       leaking `sec₁` (`11 ≠ 22` at `((0, 11), 0)` vs `((0, 22), 0)`).
    2. **`PENTEST-R4-5B`:** On `SemObs = (Nat × Nat) × Nat` (`((ret, cycles), cache)`),
       `instPositionalLeakageObsProd` projects `leakProj v = cache`, so
       `L_multi_channel` program `true` (`o = ((pub + 1, sec), 10)`) satisfies
       `SymmetricBiNonInterferingOn` under `leakProj v₁ = leakProj v₂` while
       leaking `sec` in `cycles` (`11 ≠ 22` at `(0, 11)` vs `(0, 22)`). -/
theorem pentest_r4_5_positional_tuple_bypasses :
    L_two_secrets.SymmetricBiNonInterferingOn (fun q => q.1.1 < 100)
      (fun q₁ q₂ => PositionalPublicQuery.pubProj q₁ = PositionalPublicQuery.pubProj q₂)
      (fun v₁ v₂ => PositionalLeakageObs.leakProj v₁ = PositionalLeakageObs.leakProj v₂)
      true ∧
    (∃ v₁ v₂ : Nat × Nat,
      L_two_secrets.Produces true ((0, 11), 0) v₁ ∧
      L_two_secrets.Produces true ((0, 22), 0) v₂ ∧
      v₁.2 ≠ v₂.2) ∧
    L_multi_channel.SymmetricBiNonInterferingOn (fun q => q.1 < 100)
      (fun q₁ q₂ => PositionalPublicQuery.pubProj q₁ = PositionalPublicQuery.pubProj q₂)
      (fun v₁ v₂ => PositionalLeakageObs.leakProj v₁ = PositionalLeakageObs.leakProj v₂)
      true ∧
    (∃ v₁ v₂ : (Nat × Nat) × Nat,
      L_multi_channel.Produces true (0, 11) v₁ ∧
      L_multi_channel.Produces true (0, 22) v₂ ∧
      v₁.1.2 ≠ v₂.1.2) := by
  refine ⟨?_, ⟨(1, 11), (1, 22), ⟨trivial, (1, 11), rfl, rfl⟩,
    ⟨trivial, (1, 22), rfl, rfl⟩, by decide⟩,
    ?_, ⟨((1, 11), 10), ((1, 22), 10), ⟨trivial, ((1, 11), 10), rfl, rfl⟩,
    ⟨trivial, ((1, 22), 10), rfl, rfl⟩, by decide⟩⟩
  · have h_ni :
        L_two_secrets.NonInterferingOn (fun q => q.1.1 < 100)
          (fun q₁ q₂ => PositionalPublicQuery.pubProj q₁ = PositionalPublicQuery.pubProj q₂)
          (fun v₁ v₂ => PositionalLeakageObs.leakProj v₁ = PositionalLeakageObs.leakProj v₂)
          true := by
      intro ((pub₁, sec₁), _) ((pub₂, sec₁'), _) _ _ h_low v₁ ⟨_, o₁, ho₁, hv₁⟩
      have h_sec : sec₁ = sec₁' := congrArg Prod.snd h_low
      have hv₁_2 : v₁.2 = sec₁' := by
        have h2 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
        exact Eq.trans h2 h_sec
      exact ⟨(pub₂ + 1, sec₁'), ⟨trivial, (pub₂ + 1, sec₁'), rfl, rfl⟩, hv₁_2⟩
    exact (symmetry_converts_one_way_to_two_way L_two_secrets (fun q => q.1.1 < 100)
      _ _ (fun h => h.symm) (fun h => h.symm) true).mp h_ni
  · have h_ni :
        L_multi_channel.NonInterferingOn (fun q => q.1 < 100)
          (fun q₁ q₂ => PositionalPublicQuery.pubProj q₁ = PositionalPublicQuery.pubProj q₂)
          (fun v₁ v₂ => PositionalLeakageObs.leakProj v₁ = PositionalLeakageObs.leakProj v₂)
          true := by
      intro (pub₁, _) (pub₂, sec₂) _ _ _ v₁ ⟨_, o₁, ho₁, hv₁⟩
      have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
      exact ⟨((pub₂ + 1, sec₂), 10),
        ⟨trivial, ((pub₂ + 1, sec₂), 10), rfl, rfl⟩, hv₁_2⟩
    exact (symmetry_converts_one_way_to_two_way L_multi_channel (fun q => q.1 < 100)
      _ _ (fun h => h.symm) (fun h => h.symm) true).mp h_ni

/-!
### 2.2 Theorem 2B: Indexed Security Domain Decomposition Characterization (`SecurityDomain`)

To close all five 2-safety bypasses (`PENTEST-R2-9`, `PENTEST-R3-6A`,
`PENTEST-R3-6B`, `PENTEST-R3-7`, and `PENTEST-R4-5A/B`) simultaneously without
relying on unlabelled positional tuple instances, we parameterize 2-safety by an
explicit Cartesian **Security Domain Decomposition** `SecurityDomain Query SemObs`:
- `Query ≃ Pub × Sec` via `(projPub, projSec, mkQuery)`, and
- `SemObs ≃ Val × Leak` via `(projVal, projLeak, mkObs)`.
-/

/-- Explicit Cartesian Security Domain Decomposition (`SecurityDomain`):
    decomposes `Query` into `Pub × Sec` and `SemObs` into `Val × Leak` with
    verified round-trip laws, inducing canonical equivalence relations `lowEq`
    and `leakEq`. -/
structure SecurityDomain (Query SemObs : Type) where
  Pub      : Type
  Sec      : Type
  Val      : Type
  Leak     : Type
  projPub  : Query → Pub
  projSec  : Query → Sec
  mkQuery  : Pub → Sec → Query
  projVal  : SemObs → Val
  projLeak : SemObs → Leak
  mkObs    : Val → Leak → SemObs
  projPub_mkQuery  : ∀ pub sec, projPub (mkQuery pub sec) = pub
  projSec_mkQuery  : ∀ pub sec, projSec (mkQuery pub sec) = sec
  mkQuery_proj     : ∀ q, mkQuery (projPub q) (projSec q) = q
  projVal_mkObs    : ∀ val leak, projVal (mkObs val leak) = val
  projLeak_mkObs   : ∀ val leak, projLeak (mkObs val leak) = leak
  mkObs_proj       : ∀ v, mkObs (projVal v) (projLeak v) = v

/-- Induced public-input equivalence relation `D.lowEq`. -/
def SecurityDomain.lowEq {Query SemObs : Type} (D : SecurityDomain Query SemObs)
    (q₁ q₂ : Query) : Prop :=
  D.projPub q₁ = D.projPub q₂

/-- Induced leakage-observation equivalence relation `D.leakEq`. -/
def SecurityDomain.leakEq {Query SemObs : Type} (D : SecurityDomain Query SemObs)
    (v₁ v₂ : SemObs) : Prop :=
  D.projLeak v₁ = D.projLeak v₂

/-- Program `prog` can produce leakage observation `ℓ : D.Leak` at query `q`. -/
def Language.ProducesLeak {SemObs : Type} (L : Language SemObs)
    (D : SecurityDomain L.Query SemObs) (prog : L.Prog) (q : L.Query)
    (ℓ : D.Leak) : Prop :=
  ∃ v : SemObs, L.Produces prog q v ∧ D.projLeak v = ℓ

/-- Domain-indexed two-way bisimulation non-interference (`DomainBiNonInterferingOn`). -/
def Language.DomainBiNonInterferingOn {SemObs : Type} (L : Language SemObs)
    (D : SecurityDomain L.Query SemObs) (pre : L.Query → Prop)
    (prog : L.Prog) : Prop :=
  L.SymmetricBiNonInterferingOn pre D.lowEq D.leakEq prog

/-- **Theorem 2B (Indexed Security Domain Characterization of 2-Safety
    Bisimulation Non-Interference):**
    For any `D : SecurityDomain L.Query SemObs`:
    1. **Automatic Equivalence Relations:** `D.lowEq` and `D.leakEq` are
       reflexive, symmetric, and transitive equivalence relations.
    2. **Non-Trivial Secret Fibers (No `lowEq := Eq` or Punctured Master Keys):**
       Whenever `D.Sec` contains two distinct secrets `sec₁ ≠ sec₂`, every
       public input `pub : D.Pub` yields two distinct queries
       `q₁ = D.mkQuery pub sec₁ ≠ D.mkQuery pub sec₂ = q₂` satisfying `D.lowEq q₁ q₂`.
    3. **Soundness & Completeness for Possibilistic Leakage-Set Invariance
       (Sabelfeld & Myers 2003 / Mantel 2000):**
       `L.DomainBiNonInterferingOn D pre prog` holds **if and only if** for all
       `q₁, q₂` with `pre q₁`, `pre q₂`, and `D.lowEq q₁ q₂`, the set of
       reachable leakage observations is identical at `q₁` and `q₂`:
       `∀ ℓ : D.Leak, L.ProducesLeak D prog q₁ ℓ ↔ L.ProducesLeak D prog q₂ ℓ`. -/
theorem theorem2b_security_domain_decomposition_characterization
    {SemObs : Type} (L : Language SemObs)
    (D : SecurityDomain L.Query SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) :
    ((∀ q, D.lowEq q q) ∧
     (∀ {q₁ q₂}, D.lowEq q₁ q₂ → D.lowEq q₂ q₁) ∧
     (∀ {q₁ q₂ q₃}, D.lowEq q₁ q₂ → D.lowEq q₂ q₃ → D.lowEq q₁ q₃)) ∧
    ((∀ v, D.leakEq v v) ∧
     (∀ {v₁ v₂}, D.leakEq v₁ v₂ → D.leakEq v₂ v₁) ∧
     (∀ {v₁ v₂ v₃}, D.leakEq v₁ v₂ → D.leakEq v₂ v₃ → D.leakEq v₁ v₃)) ∧
    (∀ (pub : D.Pub) (sec₁ sec₂ : D.Sec), sec₁ ≠ sec₂ →
      D.mkQuery pub sec₁ ≠ D.mkQuery pub sec₂ ∧
      D.lowEq (D.mkQuery pub sec₁) (D.mkQuery pub sec₂)) ∧
    (L.DomainBiNonInterferingOn D pre prog ↔
      ∀ q₁ q₂ : L.Query, pre q₁ → pre q₂ → D.lowEq q₁ q₂ →
        ∀ ℓ : D.Leak, L.ProducesLeak D prog q₁ ℓ ↔ L.ProducesLeak D prog q₂ ℓ) := by
  refine ⟨⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => Eq.trans h₁ h₂⟩,
    ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => Eq.trans h₁ h₂⟩,
    ?_, ?_⟩
  · intro pub sec₁ sec₂ hne
    refine ⟨?_, ?_⟩
    · intro h_eq
      have h_sec : sec₁ = sec₂ := by
        rw [← D.projSec_mkQuery pub sec₁, ← D.projSec_mkQuery pub sec₂, h_eq]
      exact hne h_sec
    · dsimp [SecurityDomain.lowEq]
      rw [D.projPub_mkQuery, D.projPub_mkQuery]
  · constructor
    · intro ⟨h_fwd, h_bwd⟩ q₁ q₂ hq₁ hq₂ hlow ℓ
      constructor
      · intro ⟨v₁, hv₁, hℓ⟩
        have ⟨v₂, hv₂, hleak⟩ := h_fwd q₁ q₂ hq₁ hq₂ hlow v₁ hv₁
        exact ⟨v₂, hv₂, Eq.trans hleak.symm hℓ⟩
      · intro ⟨v₂, hv₂, hℓ⟩
        have ⟨v₁, hv₁, hleak⟩ := h_bwd q₁ q₂ hq₁ hq₂ hlow v₂ hv₂
        exact ⟨v₁, hv₁, Eq.trans hleak hℓ⟩
    · intro h_iff
      refine ⟨?_, ?_⟩
      · intro q₁ q₂ hq₁ hq₂ hlow v₁ hv₁
        have ⟨v₂, hv₂, hℓ⟩ := (h_iff q₁ q₂ hq₁ hq₂ hlow (D.projLeak v₁)).mp
          ⟨v₁, hv₁, rfl⟩
        exact ⟨v₂, hv₂, hℓ.symm⟩
      · intro q₁ q₂ hq₁ hq₂ hlow v₂ hv₂
        have ⟨v₁, hv₁, hℓ⟩ := (h_iff q₁ q₂ hq₁ hq₂ hlow (D.projLeak v₂)).mpr
          ⟨v₂, hv₂, rfl⟩
        exact ⟨v₁, hv₁, hℓ⟩

/-- Explicit SecurityDomain for `((pub, sec₁), sec₂)` where `Pub := Nat` and
    `Sec := Nat × Nat` (`(sec₁, sec₂)`), closing `PENTEST-R4-5A`, and explicit
    SecurityDomain for `((ret, cycles), cache)` where `Val := Nat` and
    `Leak := Nat × Nat` (`(cycles, cache)`), closing `PENTEST-R4-5B`! -/
def twoSecretDomain : SecurityDomain ((Nat × Nat) × Nat) (Nat × Nat) where
  Pub     := Nat
  Sec     := Nat × Nat
  Val     := Nat
  Leak    := Nat
  projPub q       := q.1.1
  projSec q       := (q.1.2, q.2)
  mkQuery p s     := ((p, s.1), s.2)
  projVal v       := v.1
  projLeak v      := v.2
  mkObs val leak  := (val, leak)
  projPub_mkQuery _ _ := rfl
  projSec_mkQuery _ _ := rfl
  mkQuery_proj _      := rfl
  projVal_mkObs _ _   := rfl
  projLeak_mkObs _ _  := rfl
  mkObs_proj _        := rfl

def multiChannelDomain : SecurityDomain (Nat × Nat) ((Nat × Nat) × Nat) where
  Pub     := Nat
  Sec     := Nat
  Val     := Nat
  Leak    := Nat × Nat
  projPub q       := q.1
  projSec q       := q.2
  mkQuery p s     := (p, s)
  projVal v       := v.1.1
  projLeak v      := (v.1.2, v.2)
  mkObs val leak  := ((val, leak.1), leak.2)
  projPub_mkQuery _ _ := rfl
  projSec_mkQuery _ _ := rfl
  mkQuery_proj _      := rfl
  projVal_mkObs _ _   := rfl
  projLeak_mkObs _ _  := rfl
  mkObs_proj _        := rfl

/-- **Defense Theorem for `PENTEST-R4-5A/B` via `SecurityDomain`:**
    Under `twoSecretDomain` and `multiChannelDomain`, both `.leakFirstSecretKeyCipher`
    (`L_two_secrets` program `true`) and `.leakSecretInCyclesCipher`
    (`L_multi_channel` program `true`) are **unconditionally refuted** by
    `DomainBiNonInterferingOn`! -/
theorem defense_r4_5_explicit_security_domains_refute_both_leaks :
    ¬ L_two_secrets.DomainBiNonInterferingOn twoSecretDomain
        (fun q => q.1.1 < 100) true ∧
    ¬ L_multi_channel.DomainBiNonInterferingOn multiChannelDomain
        (fun q => q.1 < 100) true := by
  refine ⟨?_, ?_⟩
  · intro ⟨h_fwd, _⟩
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, hleak⟩ :=
      h_fwd ((0, 11), 0) ((0, 22), 0) (by decide) (by decide) rfl
        (1, 11) ⟨trivial, (1, 11), rfl, rfl⟩
    have hv₂_2 : v₂.2 = 22 := congrArg Prod.snd (Eq.trans hv₂.symm ho₂)
    have h11_22 : (11 : Nat) = 22 := Eq.trans hleak hv₂_2
    cases h11_22
  · intro ⟨h_fwd, _⟩
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, hleak⟩ :=
      h_fwd (0, 11) (0, 22) (by decide) (by decide) rfl
        ((1, 11), 10) ⟨trivial, ((1, 11), 10), rfl, rfl⟩
    have hv₂_12 : v₂.1.2 = 22 :=
      congrArg Prod.snd (congrArg Prod.fst (Eq.trans hv₂.symm ho₂))
    have h11_22 : (11 : Nat) = 22 :=
      Eq.trans (congrArg Prod.fst hleak) hv₂_12
    cases h11_22

-- ============================================================================
-- Section 3: McLean's Refinement Paradox & Bisimulation-Preserving Compilation
-- (`McLeanRefinementParadoxAndResolution`)
-- ============================================================================

/-!
### 3.1 Theorem 3A: McLean's Refinement Paradox for `ProductiveCompiles` + `BiNonInterferingOn` (McLean 1994)

John McLean (1994, *IEEE Symposium on Security and Privacy*) discovered a
foundational pathology of possibilistic security properties: **non-interference
is not closed under standard demonic subset refinement ($\subseteq$)**.

In our 4-primitive semantic verification model, this means that **verifying
1-trace functional correctness (`VerifiedSpineOn`) AND 2-safety bisimulation
non-interference (`DomainBiNonInterferingOn` / `SymmetricBiNonInterferingOn`) on
the source language $L_{\text{src}}$, together with productive demonic
compilation (`ProductiveCompiles`) from $L_{\text{src}}$ to $L_{\text{tgt}}$,
DOES NOT GUARANTEE 2-safety non-interference of the compiled target program!**

We construct an explicit, kernel-checked counterexample:
- Source program `.jitterSafeCipher` computes `pub + 1` with secret-independent
  nondeterministic timing $t \in \{10, 20\}$ for every `(pub, sec)`.
- Target program `.refinedLeakyCipher` refines $\{10, 20\}$ demonically into
  $\{10\}$ when $\text{sec} = 0$ and into $\{20\}$ when $\text{sec} > 0$.
- Compiler `mcleanParadoxCompiler` lowers `.jitterSafeCipher ↦ .refinedLeakyCipher`.
-/

/-- Standard Cartesian security domain on `(Nat × Nat)` queries `(pub, sec)` and
    `(Nat × Nat)` observations `(ret, time)`. -/
def stdCryptoDomain : SecurityDomain (Nat × Nat) (Nat × Nat) where
  Pub     := Nat
  Sec     := Nat
  Val     := Nat
  Leak    := Nat
  projPub q       := q.1
  projSec q       := q.2
  mkQuery p s     := (p, s)
  projVal v       := v.1
  projLeak v      := v.2
  mkObs val leak  := (val, leak)
  projPub_mkQuery _ _ := rfl
  projSec_mkQuery _ _ := rfl
  mkQuery_proj _      := rfl
  projVal_mkObs _ _   := rfl
  projLeak_mkObs _ _  := rfl
  mkObs_proj _        := rfl

/-- AST for McLean's Refinement Paradox (`Theorem 3A`):
    - `.jitterSafeCipher`: source program with secret-independent timing jitter
      `{10, 20}` (`o = (pub + 1, 10) ∨ o = (pub + 1, 20)`),
    - `.refinedLeakyCipher`: target program that refines `{10, 20}` into `{10}`
      when `sec = 0` and `{20}` when `sec > 0`,
    - `.uniformDet10Cipher`: target program that refines `{10, 20}` uniformly
      into `{10}` for all `(pub, sec)`. -/
inductive McLeanProg where
  | jitterSafeCipher
  | refinedLeakyCipher
  | uniformDet10Cipher
  deriving DecidableEq

/-- Language semantics for `McLeanProg`. -/
abbrev L_mclean : Language (Nat × Nat) :=
  Language.mkSimple McLeanProg (Nat × Nat) (Nat × Nat)
    (fun p (pub, sec) => match p with
      | .jitterSafeCipher =>
        Partial.pure (fun o => o = (pub + 1, 10) ∨ o = (pub + 1, 20))
      | .refinedLeakyCipher =>
        Partial.pure (fun o =>
          if sec = 0 then o = (pub + 1, 10)
          else o = (pub + 1, 20))
      | .uniformDet10Cipher =>
        Partial.pure (fun o => o = (pub + 1, 10)))

/-- Compiler exhibiting McLean's Refinement Paradox: compiles `.jitterSafeCipher`
    into `.refinedLeakyCipher` by resolving timing nondeterminism differently
    depending on `sec = 0` vs `sec > 0`. -/
def mcleanParadoxCompiler : Tool L_mclean L_mclean
  | .jitterSafeCipher   => Partial.pure .refinedLeakyCipher
  | .refinedLeakyCipher => Partial.ub
  | .uniformDet10Cipher => Partial.ub

/-- **Theorem 3A (McLean's Refinement Paradox for `ProductiveCompiles` +
    `DomainBiNonInterferingOn`):**
    1. **Source 1-Trace & 2-Safety Verification:** `.jitterSafeCipher` satisfies
       both 1-trace functional correctness `VerifiedSpine` (`v.1 = q.1 + 1`) and
       two-way 2-safety bisimulation `DomainBiNonInterferingOn stdCryptoDomain`!
    2. **Valid Productive Demonic Compilation:** `mcleanParadoxCompiler` accepts
       `.jitterSafeCipher` and satisfies `ProductiveCompiles` to
       `.refinedLeakyCipher`!
    3. **Target 1-Trace Preservation:** The compiled target program
       `.refinedLeakyCipher` still satisfies 1-trace functional correctness
       `VerifiedSpine` (`v.1 = q.1 + 1`).
    4. **Catastrophic Target 2-Safety Failure:** The compiled target program
       `.refinedLeakyCipher` **violates** both one-way `NonInterferingOn` and
       two-way `DomainBiNonInterferingOn` on `L_mclean`, leaking `sec = 0` vs
       `sec = 1` via deterministic timing `10 ≠ 20`! -/
theorem theorem3a_mclean_refinement_paradox_counterexample :
    L_mclean.VerifiedSpine (fun q => q.1 < 100)
      (fun q v => v.1 = q.1 + 1) .jitterSafeCipher ∧
    L_mclean.DomainBiNonInterferingOn stdCryptoDomain
      (fun q => q.1 < 100) .jitterSafeCipher ∧
    ProductiveCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
      .jitterSafeCipher .refinedLeakyCipher ∧
    L_mclean.VerifiedSpine (fun q => q.1 < 100)
      (fun q v => v.1 = q.1 + 1) .refinedLeakyCipher ∧
    ¬ L_mclean.NonInterferingOn (fun q => q.1 < 100)
        stdCryptoDomain.lowEq stdCryptoDomain.leakEq .refinedLeakyCipher ∧
    ¬ L_mclean.DomainBiNonInterferingOn stdCryptoDomain
        (fun q => q.1 < 100) .refinedLeakyCipher := by
  have h_src_1trace :
      L_mclean.VerifiedSpine (fun q => q.1 < 100)
        (fun q v => v.1 = q.1 + 1) .jitterSafeCipher := by
    refine ⟨Or.inl ⟨(0, 0), by decide⟩,
      fun (pub, _) _ => ⟨trivial, (pub + 1, 10), Or.inl rfl⟩,
      fun (pub, _) _ => ⟨trivial, fun o ho => ?_⟩⟩
    cases ho with
    | inl h10 => exact congrArg Prod.fst h10
    | inr h20 => exact congrArg Prod.fst h20
  have h_src_ni_one :
      L_mclean.NonInterferingOn (fun q => q.1 < 100)
        stdCryptoDomain.lowEq stdCryptoDomain.leakEq .jitterSafeCipher := by
    intro (pub₁, _) (pub₂, _) _ _ _ v₁ ⟨_, o₁, ho₁, hv₁⟩
    cases ho₁ with
    | inl h10 =>
      have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm h10)
      exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), Or.inl rfl, rfl⟩, hv₁_2⟩
    | inr h20 =>
      have hv₁_2 : v₁.2 = 20 := congrArg Prod.snd (Eq.trans hv₁.symm h20)
      exact ⟨(pub₂ + 1, 20), ⟨trivial, (pub₂ + 1, 20), Or.inr rfl, rfl⟩, hv₁_2⟩
  have h_src_bini :
      L_mclean.DomainBiNonInterferingOn stdCryptoDomain
        (fun q => q.1 < 100) .jitterSafeCipher :=
    (symmetry_converts_one_way_to_two_way L_mclean (fun q => q.1 < 100)
      _ _ (fun h => h.symm) (fun h => h.symm) .jitterSafeCipher).mp h_src_ni_one
  have h_pcomp :
      ProductiveCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
        .jitterSafeCipher .refinedLeakyCipher := by
    refine ⟨?_, ?_⟩
    · intro (pub, sec) _
      refine ⟨trivial, fun o ho => ⟨o, rfl, ?_⟩⟩
      cases sec with
      | zero => exact Or.inl ho
      | succ n => exact Or.inr ho
    · intro (pub, sec) _
      cases sec with
      | zero => exact ⟨trivial, (pub + 1, 10), rfl⟩
      | succ n => exact ⟨trivial, (pub + 1, 20), rfl⟩
  have h_tgt_1trace :
      L_mclean.VerifiedSpine (fun q => q.1 < 100)
        (fun q v => v.1 = q.1 + 1) .refinedLeakyCipher := by
    refine ⟨Or.inl ⟨(0, 0), by decide⟩,
      fun (pub, sec) _ => ?_,
      fun (pub, sec) _ => ⟨trivial, fun o ho => ?_⟩⟩
    · cases sec with
      | zero => exact ⟨trivial, (pub + 1, 10), rfl⟩
      | succ n => exact ⟨trivial, (pub + 1, 20), rfl⟩
    · cases sec with
      | zero => exact congrArg Prod.fst ho
      | succ n => exact congrArg Prod.fst ho
  have h_tgt_not_ni :
      ¬ L_mclean.NonInterferingOn (fun q => q.1 < 100)
          stdCryptoDomain.lowEq stdCryptoDomain.leakEq .refinedLeakyCipher := by
    intro h_ni
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, hleak⟩ :=
      h_ni (0, 0) (0, 1) (by decide) (by decide) rfl
        (1, 10) ⟨trivial, (1, 10), rfl, rfl⟩
    have hv₂_2 : v₂.2 = 20 := congrArg Prod.snd (Eq.trans hv₂.symm ho₂)
    have h10_20 : (10 : Nat) = 20 := Eq.trans hleak hv₂_2
    cases h10_20
  exact ⟨h_src_1trace, h_src_bini, h_pcomp, h_tgt_1trace,
    h_tgt_not_ni, fun ⟨h_ni, _⟩ => h_tgt_not_ni h_ni⟩

/-!
### 3.2 Theorem 3B: Two Exact Resolutions of McLean's Refinement Paradox

How can a verified compiler pipeline guarantee that a compiled target program
$p_2$ satisfies 2-safety non-interference? We prove two exact, complementary
resolutions:

1. **Resolution 1 (Leakage-Deterministic Source Transfer,
   `theorem3b_resolution1_leakage_deterministic_transfer`):**
   If the source program $p_1$ is **leakage-deterministic** on `pre₁`
   (`L₁.LeakageDeterministicOn pre₁ leakEq p₁`), then **standard
   `ProductiveCompiles` automatically transfers `SymmetricBiNonInterferingOn`
   from $L_1$ to $L_2$**! Why? Because when $p_1$ has only a single leakage
   equivalence class at each query, any productive subset of $p_1$'s outcomes
   selected by $p_2$ must inhabit that unique leakage equivalence class.

2. **Resolution 2 (Leakage-Bisimulation-Preserving Compilation
   `LeakageBisimCompiles` & Secret-Uniform Refinement
   `UniformRefinementCompiles`,
   `theorem3b_resolution2_leakage_bisim_and_uniform_refinement`):**
   When $p_1$ genuinely exhibits secret-independent nondeterminism (such as
   hardware timing jitter $\{10, 20\}$):
   - **`LeakageBisimCompiles`** conjoins `ProductiveCompiles` with backward
     leakage simulation (every source leakage observation at `c.decodeQuery q₂`
     is still realizable by the target at `q₂`).
   - More generally, **`UniformRefinementCompiles`** conjoins `ProductiveCompiles`
     with **Secret-Independent Refinement Uniformity** (allowing the compiler to
     determinize `{10, 20} → {10}` as in `.uniformDet10Cipher`, provided the
     refinement choice is invariant across `lowEq` target queries!).
   Both transfer `SymmetricBiNonInterferingOn` to the target and compose
   vertically across multi-pass pipelines!
-/

/-- **Theorem 3B.1 (Resolution 1 — Leakage-Deterministic Source Programs
    Transfer 2-Safety Across Standard `ProductiveCompiles`):**
    If `p₁` is productive, satisfies `SymmetricBiNonInterferingOn` on `L₁`, and
    is **leakage-deterministic** (`L₁.LeakageDeterministicOn pre₁ leakEq p₁`),
    then for **every** target program `p₂` satisfying
    `ProductiveCompiles L₁ L₂ c p₁ p₂`, `p₂` automatically satisfies
    `SymmetricBiNonInterferingOn` on `L₂`! -/
theorem theorem3b_resolution1_leakage_deterministic_transfer
    {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    (pre₁ : L₁.Query → Prop)
    (lowEq₁ : L₁.Query → L₁.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (_h_leak_symm : ∀ {v₁ v₂}, leakEq v₁ v₂ → leakEq v₂ v₁)
    (h_leak_trans : ∀ {v₁ v₂ v₃}, leakEq v₁ v₂ → leakEq v₂ v₃ → leakEq v₁ v₃)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog)
    (h_prod₁ : L₁.ProductiveOn pre₁ p₁)
    (h_bini₁ : L₁.SymmetricBiNonInterferingOn pre₁ lowEq₁ leakEq p₁)
    (h_det₁ : L₁.LeakageDeterministicOn pre₁ leakEq p₁)
    (h_pcomp : ProductiveCompiles L₁ L₂ c p₁ p₂) :
    L₂.SymmetricBiNonInterferingOn
      (fun q₂ => pre₁ (c.decodeQuery q₂))
      (fun q₂ q₂' => lowEq₁ (c.decodeQuery q₂) (c.decodeQuery q₂'))
      leakEq p₂ := by
  have h_all₁ : L₁.AllPairsNonInterferingOn pre₁ lowEq₁ leakEq p₁ := by
    intro q₁ q₁' hq₁ hq₁' hlow v₁ v₁' hv₁ hv₁'
    have ⟨v_mid, hv_mid, h_eq₁⟩ := h_bini₁.1 q₁ q₁' hq₁ hq₁' hlow v₁ hv₁
    have h_eq₂ := h_det₁ q₁' hq₁' v_mid v₁' hv_mid hv₁'
    exact h_leak_trans h_eq₁ h_eq₂
  have h_fwd₂ :
      L₂.NonInterferingOn
        (fun q₂ => pre₁ (c.decodeQuery q₂))
        (fun q₂ q₂' => lowEq₁ (c.decodeQuery q₂) (c.decodeQuery q₂'))
        leakEq p₂ := by
    intro q₂ q₂' hq₂ hq₂' hlow v₂ hv₂
    have ⟨hdef₁, o₁, ho₁⟩ := h_prod₁ (c.decodeQuery q₂) hq₂
    have ⟨hdef₁', o₁', ho₁'⟩ := h_prod₁ (c.decodeQuery q₂') hq₂'
    have hv₁ : L₁.Produces p₁ (c.decodeQuery q₂) v₂ :=
      Compiles.produces_imp h_pcomp.1 q₂ hdef₁ v₂ hv₂
    have ⟨hdef₂', o₂', ho₂'⟩ := h_pcomp.2 q₂' ⟨hdef₁', o₁', ho₁'⟩
    have hv₂' : L₂.Produces p₂ q₂' (L₂.obs o₂') := ⟨hdef₂', o₂', ho₂', rfl⟩
    have hv₁' : L₁.Produces p₁ (c.decodeQuery q₂') (L₂.obs o₂') :=
      Compiles.produces_imp h_pcomp.1 q₂' hdef₁' (L₂.obs o₂') hv₂'
    exact ⟨L₂.obs o₂', hv₂',
      h_all₁ (c.decodeQuery q₂) (c.decodeQuery q₂') hq₂ hq₂' hlow
        v₂ (L₂.obs o₂') hv₁ hv₁'⟩
  refine ⟨h_fwd₂, ?_⟩
  intro q₂ q₂' hq₂ hq₂' hlow v₂' hv₂'
  have ⟨hdef₁, o₁, ho₁⟩ := h_prod₁ (c.decodeQuery q₂) hq₂
  have ⟨hdef₁', _⟩ := h_prod₁ (c.decodeQuery q₂') hq₂'
  have hv₁' : L₁.Produces p₁ (c.decodeQuery q₂') v₂' :=
    Compiles.produces_imp h_pcomp.1 q₂' hdef₁' v₂' hv₂'
  have ⟨hdef₂, o₂, ho₂⟩ := h_pcomp.2 q₂ ⟨hdef₁, o₁, ho₁⟩
  have hv₂ : L₂.Produces p₂ q₂ (L₂.obs o₂) := ⟨hdef₂, o₂, ho₂, rfl⟩
  have hv₁ : L₁.Produces p₁ (c.decodeQuery q₂) (L₂.obs o₂) :=
    Compiles.produces_imp h_pcomp.1 q₂ hdef₁ (L₂.obs o₂) hv₂
  exact ⟨L₂.obs o₂, hv₂,
    h_all₁ (c.decodeQuery q₂) (c.decodeQuery q₂') hq₂ hq₂' hlow
      (L₂.obs o₂) v₂' hv₁ hv₁'⟩

/-- **Leakage-Bisimulation-Preserving Compilation (`LeakageBisimCompiles`):**
    Requires both `ProductiveCompiles` (forward demonic inclusion) and backward
    leakage simulation on `pre₁`: every source outcome `v₁` at `c.decodeQuery q₂`
    is matched up to `leakEq` by some target outcome `v₂` at `q₂`. -/
def LeakageBisimCompiles {SemObs : Type} (L₁ L₂ : Language SemObs)
    (c : BehaviorCodec L₁ L₂)
    (pre₁ : L₁.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  ProductiveCompiles L₁ L₂ c p₁ p₂ ∧
  ∀ q₂ : L₂.Query, pre₁ (c.decodeQuery q₂) →
    ∀ v₁ : SemObs, L₁.Produces p₁ (c.decodeQuery q₂) v₁ →
      ∃ v₂ : SemObs, L₂.Produces p₂ q₂ v₂ ∧ leakEq v₁ v₂

/-- **Secret-Uniform Refinement Compilation (`UniformRefinementCompiles`):**
    Requires `ProductiveCompiles` together with target-level 2-safety
    refinement uniformity across `lowEq₁`-equivalent queries (admitting both
    jitter-preserving compilers and uniform determinizing compilers like
    `.jitterSafeCipher ↦ .uniformDet10Cipher`). -/
def UniformRefinementCompiles {SemObs : Type} (L₁ L₂ : Language SemObs)
    (c : BehaviorCodec L₁ L₂)
    (pre₁ : L₁.Query → Prop)
    (lowEq₁ : L₁.Query → L₁.Query → Prop)
    (leakEq : SemObs → SemObs → Prop)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  ProductiveCompiles L₁ L₂ c p₁ p₂ ∧
  L₂.SymmetricBiNonInterferingOn
    (fun q₂ => pre₁ (c.decodeQuery q₂))
    (fun q₂ q₂' => lowEq₁ (c.decodeQuery q₂) (c.decodeQuery q₂'))
    leakEq p₂

/-- **Theorem 3B.2 (Resolution 2 — `LeakageBisimCompiles` Transfers
    `SymmetricBiNonInterferingOn`, Implies `UniformRefinementCompiles`, Composes
    Vertically, and Refutes `mcleanParadoxCompiler`):**
    1. **Transfer Law:** If `p₁` is productive on `pre₁` and satisfies
       `SymmetricBiNonInterferingOn`, then `LeakageBisimCompiles` transfers
       `SymmetricBiNonInterferingOn` to `p₂` on `L₂` (and hence implies
       `UniformRefinementCompiles`)!
    2. **Vertical Pipeline Composition:** `LeakageBisimCompiles` composes
       vertically across multi-stage compiler pipelines `L₁ → L₂ → L₃`!
    3. **Refutation of McLean's Paradox Compiler & Admission of Honest
       Compilers:** `LeakageBisimCompiles` and `UniformRefinementCompiles` both
       **reject** `.jitterSafeCipher ↦ .refinedLeakyCipher` (`mcleanParadoxCompiler`),
       while `LeakageBisimCompiles` **admits** jitter-preserving compilation
       (`.jitterSafeCipher ↦ .jitterSafeCipher`) and `UniformRefinementCompiles`
       **admits** uniform determinizing compilation
       (`.jitterSafeCipher ↦ .uniformDet10Cipher`)! -/
theorem theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement :
    -- 1. Transfer of 2-Safety Bisimulation across `LeakageBisimCompiles`
    (∀ {SemObs : Type} {L₁ L₂ : Language SemObs}
       (c : BehaviorCodec L₁ L₂)
       (pre₁ : L₁.Query → Prop)
       (lowEq₁ : L₁.Query → L₁.Query → Prop)
       (leakEq : SemObs → SemObs → Prop)
       (_ : ∀ {v₁ v₂}, leakEq v₁ v₂ → leakEq v₂ v₁)
       (_ : ∀ {v₁ v₂ v₃}, leakEq v₁ v₂ → leakEq v₂ v₃ → leakEq v₁ v₃)
       (p₁ : L₁.Prog) (p₂ : L₂.Prog),
       L₁.ProductiveOn pre₁ p₁ →
       L₁.SymmetricBiNonInterferingOn pre₁ lowEq₁ leakEq p₁ →
       LeakageBisimCompiles L₁ L₂ c pre₁ leakEq p₁ p₂ →
       UniformRefinementCompiles L₁ L₂ c pre₁ lowEq₁ leakEq p₁ p₂) ∧
    -- 2. Vertical Pipeline Composition of `LeakageBisimCompiles`
    (∀ {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
       (c₁₂ : BehaviorCodec L₁ L₂) (c₂₃ : BehaviorCodec L₂ L₃)
       (pre₁ : L₁.Query → Prop)
       (leakEq : SemObs → SemObs → Prop)
       (_ : ∀ {v₁ v₂ v₃}, leakEq v₁ v₂ → leakEq v₂ v₃ → leakEq v₁ v₃)
       (p₁ : L₁.Prog) (p₂ : L₂.Prog) (p₃ : L₃.Prog),
       LeakageBisimCompiles L₁ L₂ c₁₂ pre₁ leakEq p₁ p₂ →
       LeakageBisimCompiles L₂ L₃ c₂₃ (fun q₂ => pre₁ (c₁₂.decodeQuery q₂)) leakEq p₂ p₃ →
       LeakageBisimCompiles L₁ L₃ (c₁₂.comp c₂₃) pre₁ leakEq p₁ p₃) ∧
    -- 3. Refutation of `mcleanParadoxCompiler` and Admission of Honest Compilers
    ¬ LeakageBisimCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
        (fun q => q.1 < 100) stdCryptoDomain.leakEq
        .jitterSafeCipher .refinedLeakyCipher ∧
    ¬ UniformRefinementCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
        (fun q => q.1 < 100) stdCryptoDomain.lowEq stdCryptoDomain.leakEq
        .jitterSafeCipher .refinedLeakyCipher ∧
    LeakageBisimCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
      (fun q => q.1 < 100) stdCryptoDomain.leakEq
      .jitterSafeCipher .jitterSafeCipher ∧
    UniformRefinementCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
      (fun q => q.1 < 100) stdCryptoDomain.lowEq stdCryptoDomain.leakEq
      .jitterSafeCipher .uniformDet10Cipher := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro SemObs L₁ L₂ c pre₁ lowEq₁ leakEq h_symm h_trans p₁ p₂
      h_prod₁ h_bini₁ ⟨h_pcomp, h_back⟩
    refine ⟨h_pcomp, ?_, ?_⟩
    · intro q₂ q₂' hq₂ hq₂' hlow v₂ hv₂
      have ⟨hdef₁, _⟩ := h_prod₁ (c.decodeQuery q₂) hq₂
      have hv₁ : L₁.Produces p₁ (c.decodeQuery q₂) v₂ :=
        Compiles.produces_imp h_pcomp.1 q₂ hdef₁ v₂ hv₂
      have ⟨v₁', hv₁', hleak₁⟩ :=
        h_bini₁.1 (c.decodeQuery q₂) (c.decodeQuery q₂') hq₂ hq₂' hlow v₂ hv₁
      have ⟨v₂', hv₂', hleak₂⟩ := h_back q₂' hq₂' v₁' hv₁'
      exact ⟨v₂', hv₂', h_trans hleak₁ hleak₂⟩
    · intro q₂ q₂' hq₂ hq₂' hlow v₂' hv₂'
      have ⟨hdef₁', _⟩ := h_prod₁ (c.decodeQuery q₂') hq₂'
      have hv₁' : L₁.Produces p₁ (c.decodeQuery q₂') v₂' :=
        Compiles.produces_imp h_pcomp.1 q₂' hdef₁' v₂' hv₂'
      have ⟨v₁, hv₁, hleak₁⟩ :=
        h_bini₁.2 (c.decodeQuery q₂) (c.decodeQuery q₂') hq₂ hq₂' hlow v₂' hv₁'
      have ⟨v₂, hv₂, hleak₂⟩ := h_back q₂ hq₂ v₁ hv₁
      exact ⟨v₂, hv₂, h_trans (h_symm hleak₂) hleak₁⟩
  · intro SemObs L₁ L₂ L₃ c₁₂ c₂₃ pre₁ leakEq h_trans p₁ p₂ p₃
      ⟨h_pcomp₁₂, h_back₁₂⟩ ⟨h_pcomp₂₃, h_back₂₃⟩
    refine ⟨ProductiveCompiles.comp h_pcomp₁₂ h_pcomp₂₃, ?_⟩
    intro q₃ hq₃ v₁ hv₁
    have ⟨v₂, hv₂, hleak₁₂⟩ := h_back₁₂ (c₂₃.decodeQuery q₃) hq₃ v₁ hv₁
    have ⟨v₃, hv₃, hleak₂₃⟩ := h_back₂₃ q₃ hq₃ v₂ hv₂
    exact ⟨v₃, hv₃, h_trans hleak₁₂ hleak₂₃⟩
  · intro ⟨_, h_back⟩
    have ⟨v₂, ⟨_, o₂, ho₂, hv₂⟩, hleak⟩ :=
      h_back (0, 0) (by decide) (1, 20) ⟨trivial, (1, 20), Or.inr rfl, rfl⟩
    have hv₂_2 : v₂.2 = 10 := congrArg Prod.snd (Eq.trans hv₂.symm ho₂)
    have h20_10 : (20 : Nat) = 10 := Eq.trans hleak hv₂_2
    cases h20_10
  · intro ⟨_, h_bini⟩
    exact theorem3a_mclean_refinement_paradox_counterexample.2.2.2.2.2 h_bini
  · refine ⟨ProductiveCompiles.refl L_mclean .jitterSafeCipher, ?_⟩
    intro q _ v₁ hv₁
    exact ⟨v₁, hv₁, rfl⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro (pub, _) _
      exact ⟨trivial, fun o ho => ⟨o, rfl, Or.inl ho⟩⟩
    · intro (pub, _) _
      exact ⟨trivial, (pub + 1, 10), rfl⟩
    · have h_ni :
          L_mclean.NonInterferingOn (fun q => q.1 < 100)
            stdCryptoDomain.lowEq stdCryptoDomain.leakEq .uniformDet10Cipher := by
        intro (pub₁, _) (pub₂, sec₂) _ _ _ v₁ ⟨_, o₁, ho₁, hv₁⟩
        have hv₁_2 : v₁.2 = 10 := congrArg Prod.snd (Eq.trans hv₁.symm ho₁)
        exact ⟨(pub₂ + 1, 10), ⟨trivial, (pub₂ + 1, 10), rfl, rfl⟩, hv₁_2⟩
      exact (symmetry_converts_one_way_to_two_way L_mclean (fun q => q.1 < 100)
        _ _ (fun h => h.symm) (fun h => h.symm) .uniformDet10Cipher).mp h_ni

-- ============================================================================
-- Section 4: The Nondeterminism Refinement Lattice: Chaos vs. Bounded
-- Nondeterminism vs. Angelic Reachability (`NondeterminismRefinementLattice`)
-- ============================================================================

/-!
### 4.1 Theorem 4A: The Five-Level Nondeterminism Hierarchy & Why Weak Exclusions Fail

In the refinement calculus (Back & von Wright 1998; Søndergaard & Sestoft 1992;
Roscoe 1995), a program's outcome set $\text{Obs}(p, q) \subseteq \text{SemObs}$
at query $q$ sits in a 5-tier lattice relative to a specification
$S(q) = \{v \mid \text{obsPost}(q, v)\}$:

1. **Empty / Miracle ($\bot_{\text{demonic}}$):** $\text{Obs}(p, q) = \emptyset$
   (`PENTEST-6` / `EXPLOIT-1`). Satisfies pure demonic inclusion $\emptyset \subseteq S(q)$
   vacuously, which is why `Compiles` without `ProductiveOn` certifies over-constrained
   or dead-state target miracles.
2. **Deterministic Exact:** $|\text{Obs}(p, q)| = 1$ and $\text{Obs}(p, q) \subseteq S(q)$
   (e.g., `.detAddOne` returning $\{q + 1\}$, or `.alignedAllocLow` returning $\{8(q + 1)\}$).
3. **Specification-Bounded Productive Nondeterminism:**
   $\emptyset \subsetneq \text{Obs}(p, q) \subseteq S(q)$ with $|\text{Obs}(p, q)| \ge 2$
   (e.g., `.alignedAllocChoices` returning $\{8(q + 1), 8(q + 2)\}$ under the
   8-byte alignment contract $v > 0 \wedge v \bmod 8 = 0$).
4. **Angelic / May-Violate Nondeterminism:**
   $\text{Obs}(p, q) \cap S(q) \neq \emptyset$ AND $\text{Obs}(p, q) \not\subseteq S(q)$
   (e.g., `.nondetMixed` returning $\{q + 1, 999\}$, `PENTEST-R3-9A`). Passes
   angelic verification `VerifiedAngelicSpineOn` and 1-value exclusion
   `NonChaoticOn` while violating demonic safety on branch `999`.
5. **Bounded & Unbounded Uninitialized-Read Chaos ($\top_{\text{demonic}}$):**
   - `.uninitByteRead` ($0 < o < 256$, `PENTEST-R3-2C`): excludes $0$ and all
     $v \ge 256$ (passing `NonChaoticOn` and weak inequality specs $v > 0$), yet
     exhibits 255-way uninitialized byte chaos.
   - `.uninitRead` ($\text{Obs}(p, q) = \text{univ}$, `PENTEST-R2-8A`): passes
     target-only `SoundTargetOn` when compiled to a deterministic target stub.
-/

/-- 7-program AST spanning all 5 tiers of the Nondeterminism Refinement Lattice:
    - `.miracleEmpty`: empty outcome set `fun _ => False` (Tier 1: Miracle $\bot$),
    - `.alignedConst8`: deterministically returns `8` (Tier 2a: Constant Deterministic),
    - `.alignedAllocLow`: deterministically returns `8 * (q + 1)` (Tier 2b: Query-Indexed Deterministic),
    - `.alignedAllocChoices`: nondeterministically returns `8 * (q + 1)` or
      `8 * (q + 2)` (Tier 3: Specification-Bounded Nondeterminism),
    - `.nondetMixed`: nondeterministically returns `8 * (q + 1)` or unaligned
      `999` (Tier 4: Angelic / May-Violate Nondeterminism, `PENTEST-R3-9A`),
    - `.uninitByteRead`: nondeterministically returns any `0 < o < 256`
      (Tier 5a: 8-Bit Bounded Uninitialized-Read Chaos, `PENTEST-R3-2C`),
    - `.uninitRead`: nondeterministically returns any `o : Nat`
      (Tier 5b: Unbounded Uninitialized-Read Chaos, `PENTEST-R2-8A`). -/
inductive LatticeProg where
  | miracleEmpty
  | alignedConst8
  | alignedAllocLow
  | alignedAllocChoices
  | nondetMixed
  | uninitByteRead
  | uninitRead
  deriving DecidableEq

/-- Semantics of `L_lattice : Language Nat`. -/
abbrev L_lattice : Language Nat :=
  Language.mkSimple LatticeProg Nat Nat (fun p q => match p with
    | .miracleEmpty        => Partial.pure (fun _ => False)
    | .alignedConst8       => Partial.pure (fun o => o = 8)
    | .alignedAllocLow     => Partial.pure (fun o => o = 8 * (q + 1))
    | .alignedAllocChoices => Partial.pure (fun o => o = 8 * (q + 1) ∨ o = 8 * (q + 2))
    | .nondetMixed         => Partial.pure (fun o => o = 8 * (q + 1) ∨ o = 999)
    | .uninitByteRead      => Partial.pure (fun o => 0 < o ∧ o < 256)
    | .uninitRead          => Partial.pure (fun _ => True))

/-- Candidate 008's 1-value exclusion predicate `Language.NonChaoticOn`
    (`PENTEST-R3-2C`): requires productivity and at least one excluded value. -/
def Language.NonChaoticOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (p : L.Prog) : Prop :=
  L.ProductiveOn pre p ∧
  ∀ q : L.Query, pre q → ∃ v_excl : SemObs, ¬ L.Produces p q v_excl

/-- Candidate 006/008's angelic reachability predicate `Language.VerifiedAngelicSpineOn`
    (`PENTEST-R3-9A`): requires at least one execution branch to satisfy `obsPost`. -/
def Language.VerifiedAngelicSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  ∀ q : L.Query, pre q →
    ∃ v : SemObs, L.Produces prog q v ∧ obsPost q v

/-- Candidate 006's target-only compiler predicate `Tool.SoundTargetOn`
    (`PENTEST-R2-8A`): checks `ProductiveCompiles` and target `SpineSpecOn`,
    omitting source `VerifiedSpineOn`. -/
def Tool.SoundTargetOn {SemObs : Type} {L_src L_tgt : Language SemObs}
    (c : BehaviorCodec L_src L_tgt) (tool : Tool L_src L_tgt)
    (pre : L_src.Query → Prop) (obsPost : L_src.Query → SemObs → Prop) : Prop :=
  ∀ p : L_src.Prog, ∀ h_acc : (tool p).defined,
    L_src.ProductiveOn pre p ∧
    ProductiveCompiles L_src L_tgt c p ((tool p).val h_acc) ∧
    L_tgt.sem ((tool p).val h_acc) ≤
      L_tgt.SpineSpecOn (fun q₂ => pre (c.decodeQuery q₂))
        (fun q₂ v => obsPost (c.decodeQuery q₂) v)

/-- Legitimate underspecified 8-byte aligned allocator specification:
    `v > 0 ∧ v % 8 = 0 ∧ v ≤ 8 * (q + 2)`. -/
def alignedAllocSpec (q v : Nat) : Prop :=
  0 < v ∧ v % 8 = 0 ∧ v ≤ 8 * (q + 2)

/-- Compiler that resolves source nondeterminism by lowering accepted programs
    to `.alignedAllocLow` or `.alignedConst8`. -/
def resolveToAlignedLowCompiler : Tool L_lattice L_lattice
  | .miracleEmpty        => Partial.ub
  | .alignedConst8       => Partial.pure .alignedConst8
  | .alignedAllocLow     => Partial.pure .alignedAllocLow
  | .alignedAllocChoices => Partial.pure .alignedAllocLow
  | .nondetMixed         => Partial.pure .alignedAllocLow
  | .uninitByteRead      => Partial.pure .alignedConst8
  | .uninitRead          => Partial.pure .alignedAllocLow

/-- **Theorem 4A (The Nondeterminism Pathology Hierarchy — Why Demonic-Only
    `Compiles`, `SoundTargetOn`, `NonChaoticOn`, and `VerifiedAngelicSpineOn`
    All Fail):**
    1. **Miracle Vacuity (`PENTEST-6` / `EXPLOIT-1`):** `.miracleEmpty` satisfies
       demonic `Compiles` for `.alignedAllocLow` (`Compiles ... .alignedAllocLow .miracleEmpty`)
       and satisfies demonic inclusion `L_lattice.sem .miracleEmpty ≤ L_lattice.SpineSpecOn ...`,
       despite producing **zero** outcomes (`¬ L_lattice.ProductiveOn (fun q => q < 100) .miracleEmpty`).
    2. **Unbounded Chaos Bypass of `SoundTargetOn` (`PENTEST-R2-8A`):**
       `resolveToAlignedLowCompiler` accepts `.uninitRead` (`fun _ => True`),
       `.uninitByteRead`, and `.nondetMixed`, and satisfies `Tool.SoundTargetOn`
       under `alignedAllocSpec`!
    3. **Bounded Bitwidth Chaos Bypass of `NonChaoticOn` (`PENTEST-R3-2C`):**
       `.uninitByteRead` ($0 < o < 256$) satisfies `L_lattice.NonChaoticOn`
       (since it excludes $0$) and satisfies `VerifiedAngelicSpineOn` under
       `alignedAllocSpec` (since $8 \in (0, 256)$ is 8-byte aligned), yet
       produces unaligned garbage `1` (`1 % 8 ≠ 0`) on every query!
    4. **Angelic May-Violate Bypass (`PENTEST-R3-9A`):**
       `.nondetMixed` satisfies **both** `NonChaoticOn` and
       `VerifiedAngelicSpineOn` under `alignedAllocSpec`, yet can return
       unaligned `999` (`999 % 8 ≠ 0`) on every query! -/
theorem theorem4a_nondeterminism_pathology_hierarchy :
    Compiles L_lattice L_lattice (BehaviorCodec.id L_lattice)
      .alignedAllocLow .miracleEmpty ∧
    ¬ L_lattice.ProductiveOn (fun q => q < 100) .miracleEmpty ∧
    Tool.SoundTargetOn (BehaviorCodec.id L_lattice) resolveToAlignedLowCompiler
      (fun q => q < 100) alignedAllocSpec ∧
    L_lattice.NonChaoticOn (fun q => q < 100) .uninitByteRead ∧
    L_lattice.VerifiedAngelicSpineOn L_lattice.dom (fun q => q < 100)
      alignedAllocSpec .uninitByteRead ∧
    L_lattice.Produces .uninitByteRead 0 1 ∧
    ¬ alignedAllocSpec 0 1 ∧
    L_lattice.NonChaoticOn (fun q => q < 100) .nondetMixed ∧
    L_lattice.VerifiedAngelicSpineOn L_lattice.dom (fun q => q < 100)
      alignedAllocSpec .nondetMixed ∧
    L_lattice.Produces .nondetMixed 0 999 ∧
    ¬ alignedAllocSpec 0 999 := by
  have h_spec_low : ∀ q, alignedAllocSpec q (8 * (q + 1)) := by
    intro q
    refine ⟨Nat.mul_pos (by decide) (Nat.succ_pos q),
      Nat.mul_mod_right 8 (q + 1),
      Nat.mul_le_mul_left 8 (Nat.le_succ (q + 1))⟩
  have h_spec_8 : ∀ q, alignedAllocSpec q 8 := by
    intro q
    refine ⟨by decide, by decide, ?_⟩
    have h1 : 1 ≤ q + 2 := Nat.succ_le_succ (Nat.zero_le (q + 1))
    have h8 : 8 * 1 ≤ 8 * (q + 2) := Nat.mul_le_mul_left 8 h1
    omega
  refine ⟨fun _ _ => ⟨trivial, fun _ h => False.elim h⟩,
    fun h_prod => by
      have ⟨_, _, h_false⟩ := h_prod 0 (by decide)
      exact h_false,
    ?_, ?_, ?_,
    ⟨trivial, 1, ⟨by decide, by decide⟩, rfl⟩,
    fun ⟨_, h_mod, _⟩ => absurd h_mod (by decide),
    ?_, ?_,
    ⟨trivial, 999, Or.inr rfl, rfl⟩,
    fun ⟨_, h_mod, _⟩ => absurd h_mod (by decide)⟩
  · intro p h_acc
    cases p with
    | miracleEmpty => exact False.elim h_acc
    | alignedConst8 =>
      refine ⟨fun _ _ => ⟨trivial, 8, rfl⟩,
        ProductiveCompiles.refl L_lattice .alignedConst8,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_8 q⟩⟩
    | alignedAllocLow =>
      refine ⟨fun q _ => ⟨trivial, 8 * (q + 1), rfl⟩,
        ProductiveCompiles.refl L_lattice .alignedAllocLow,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_low q⟩⟩
    | alignedAllocChoices =>
      refine ⟨fun q _ => ⟨trivial, 8 * (q + 1), Or.inl rfl⟩,
        ⟨fun _ _ => ⟨trivial, fun o ho => ⟨o, rfl, Or.inl ho⟩⟩,
         fun q _ => ⟨trivial, 8 * (q + 1), rfl⟩⟩,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_low q⟩⟩
    | nondetMixed =>
      refine ⟨fun q _ => ⟨trivial, 8 * (q + 1), Or.inl rfl⟩,
        ⟨fun _ _ => ⟨trivial, fun o ho => ⟨o, rfl, Or.inl ho⟩⟩,
         fun q _ => ⟨trivial, 8 * (q + 1), rfl⟩⟩,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_low q⟩⟩
    | uninitByteRead =>
      refine ⟨fun _ _ => ⟨trivial, 8, ⟨by decide, by decide⟩⟩,
        ⟨fun _ _ => ⟨trivial, fun o ho => ⟨o, rfl, by subst ho; exact ⟨by decide, by decide⟩⟩⟩,
         fun _ _ => ⟨trivial, 8, rfl⟩⟩,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_8 q⟩⟩
    | uninitRead =>
      refine ⟨fun _ _ => ⟨trivial, 0, trivial⟩,
        ⟨fun _ _ => ⟨trivial, fun o _ => ⟨o, rfl, trivial⟩⟩,
         fun q _ => ⟨trivial, 8 * (q + 1), rfl⟩⟩,
        fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_low q⟩⟩
  · refine ⟨fun _ _ => ⟨trivial, 1, ⟨by decide, by decide⟩⟩, fun _ _ => ⟨0, ?_⟩⟩
    intro ⟨_, o, ⟨h_pos, _⟩, ho⟩
    subst ho
    exact Nat.lt_irrefl 0 h_pos
  · refine ⟨Or.inl ⟨0, by decide⟩, fun q _ => ⟨8, ?_, h_spec_8 q⟩⟩
    exact ⟨trivial, 8, ⟨by decide, by decide⟩, rfl⟩
  · refine ⟨fun q _ => ⟨trivial, 8 * (q + 1), Or.inl rfl⟩, fun _ _ => ⟨1, ?_⟩⟩
    intro ⟨_, o, ho, h1⟩
    subst h1
    cases ho with
    | inl h_mul => omega
    | inr h_999 => cases h_999
  · refine ⟨Or.inl ⟨0, by decide⟩, fun q _ => ⟨8 * (q + 1), ?_, h_spec_low q⟩⟩
    exact ⟨trivial, 8 * (q + 1), Or.inl rfl, rfl⟩

/-- **Infinitely Many Excluded Values of Bounded-Bitwidth Chaos
    (`bounded_bitwidth_chaos_excludes_infinitely_many_values`):**
    `.uninitByteRead` ($0 < o < 256$) excludes `256 + k` for every `k : Nat`,
    proving that no finite $k$-value exclusion predicate (`NonChaoticOn` with
    any $k \in \mathbb{N}$ excluded witnesses) can rule out bounded-bitwidth
    uninitialized register/memory reads (`PENTEST-R3-2C`). -/
theorem bounded_bitwidth_chaos_excludes_infinitely_many_values (q k : Nat) :
    ¬ L_lattice.Produces .uninitByteRead q (256 + k) := by
  intro ⟨_, o, ⟨_, h_lt⟩, ho⟩
  dsimp [L_lattice, Language.mkSimple] at ho
  omega

/-!
### 4.2 Theorem 4B: Productive Demonic Specification Refinement (`VerifiedSpineOn`)

We now prove that **Productive Demonic Specification Refinement**
(`VerifiedSpineOn`: $\emptyset \subsetneq \text{Obs}(p, q) \subseteq \{v \mid \text{obsPost}(q, v)\}$
with non-vacuous precondition `NonVacuousOn`) is the exact lattice meet of
demonic safety ($\text{Obs}(p, q) \subseteq S(q)$) and operational productivity
($\text{Obs}(p, q) \neq \emptyset$):
- It **rejects** empty miracles (`.miracleEmpty`), unbounded chaos (`.uninitRead`),
  bounded-bitwidth chaos (`.uninitByteRead`), and angelic may-violate
  nondeterminism (`.nondetMixed`);
- It **accepts** both deterministic implementations (`.alignedConst8`,
  `.alignedAllocLow`) and genuinely nondeterministic specification-bounded
  implementations (`.alignedAllocChoices`); and
- It **transfers soundly** from source to target across `ProductiveCompiles`.
-/

/-- **Transfer Law for `VerifiedSpineOn` Across `ProductiveCompiles`
    (`verifiedSpineOn_transfers_across_productiveCompiles`):**
    If `p₁` satisfies `VerifiedSpineOn` on `L₁` and `ProductiveCompiles L₁ L₂ c p₁ p₂`
    holds with non-vacuous pullback precondition on `L₂`, then `p₂` satisfies
    `VerifiedSpineOn` on `L₂`! -/
theorem verifiedSpineOn_transfers_across_productiveCompiles
    {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂)
    (pre₁ : L₁.Query → Prop)
    (obsPost₁ : L₁.Query → SemObs → Prop)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog)
    (h_vspine₁ : L₁.VerifiedSpineOn L₁.dom pre₁ obsPost₁ p₁)
    (h_pcomp : ProductiveCompiles L₁ L₂ c p₁ p₂)
    (h_nonvac₂ : NonVacuousOn L₂.dom (fun q₂ => pre₁ (c.decodeQuery q₂))) :
    L₂.VerifiedSpineOn L₂.dom
      (fun q₂ => pre₁ (c.decodeQuery q₂))
      (fun q₂ v => obsPost₁ (c.decodeQuery q₂) v) p₂ := by
  have ⟨_, h_prod₁, h_spec₁⟩ := h_vspine₁
  refine ⟨h_nonvac₂, ?_, ?_⟩
  · intro q₂ hq₂
    exact h_pcomp.2 q₂ (h_prod₁ (c.decodeQuery q₂) hq₂)
  · intro q₂ hq₂
    have ⟨hdef₁, o₁, ho₁⟩ := h_prod₁ (c.decodeQuery q₂) hq₂
    have ⟨hdef₂, o₂, ho₂⟩ := h_pcomp.2 q₂ ⟨hdef₁, o₁, ho₁⟩
    refine ⟨hdef₂, fun o₂' ho₂' => ?_⟩
    have ⟨o₁', h_dec, ho₁'⟩ := (h_pcomp.1 q₂ hdef₁).2 o₂' ho₂'
    have h_obs_eq := c.obs_decodeOut o₂' o₁' h_dec
    have h_post₁ : obsPost₁ (c.decodeQuery q₂) (L₁.obs o₁') :=
      (h_spec₁ (c.decodeQuery q₂) hq₂).2 o₁' ho₁'
    dsimp [Language.SpecOn]
    rw [h_obs_eq]
    exact h_post₁

/-- **Theorem 4B (Productive Demonic Specification-Bounded Nondeterminism
    Characterization):**
    Under the 8-byte aligned allocator specification `alignedAllocSpec`:
    1. **Rejects Miracle ($\bot$):** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .miracleEmpty`,
    2. **Rejects Unbounded Chaos ($\top$):** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitRead`,
    3. **Rejects 8-Bit Bounded Chaos:** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitByteRead`,
    4. **Rejects Angelic May-Violate Nondeterminism:** `¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .nondetMixed`,
    5. **Certifies Deterministic Implementations:** `L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedConst8`
       and `L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedAllocLow`,
    6. **Certifies Genuine Specification-Bounded Nondeterminism:**
       `L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedAllocChoices`
       while admitting multiple distinct valid outcomes (`8` and `16` at `q = 0`)! -/
theorem theorem4b_productive_demonic_spec_refinement_characterization :
    ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .miracleEmpty ∧
    ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitRead ∧
    ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitByteRead ∧
    ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .nondetMixed ∧
    L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedConst8 ∧
    L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedAllocLow ∧
    L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedAllocChoices ∧
    (L_lattice.Produces .alignedAllocChoices 0 8 ∧
     L_lattice.Produces .alignedAllocChoices 0 16 ∧
     (8 : Nat) ≠ 16) := by
  have h_spec_low : ∀ q, alignedAllocSpec q (8 * (q + 1)) := by
    intro q
    refine ⟨Nat.mul_pos (by decide) (Nat.succ_pos q),
      Nat.mul_mod_right 8 (q + 1),
      Nat.mul_le_mul_left 8 (Nat.le_succ (q + 1))⟩
  have h_spec_high : ∀ q, alignedAllocSpec q (8 * (q + 2)) := by
    intro q
    refine ⟨Nat.mul_pos (by decide) (Nat.succ_pos (q + 1)),
      Nat.mul_mod_right 8 (q + 2),
      Nat.le_refl (8 * (q + 2))⟩
  have h_spec_8 : ∀ q, alignedAllocSpec q 8 := by
    intro q
    refine ⟨by decide, by decide, ?_⟩
    have h1 : 1 ≤ q + 2 := Nat.succ_le_succ (Nat.zero_le (q + 1))
    have h8 : 8 * 1 ≤ 8 * (q + 2) := Nat.mul_le_mul_left 8 h1
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨⟨trivial, 8, Or.inl rfl, rfl⟩, ⟨trivial, 16, Or.inr rfl, rfl⟩, by decide⟩⟩
  · intro ⟨_, h_prod, _⟩
    have ⟨_, _, h_false⟩ := h_prod 0 (by decide)
    exact h_false
  · intro ⟨_, _, h_spec⟩
    have ⟨_, h_sub⟩ := h_spec 0 (show 0 < 100 by decide)
    have ⟨_, h_mod, _⟩ := h_sub 1 trivial
    exact absurd h_mod (by decide)
  · intro ⟨_, _, h_spec⟩
    have ⟨_, h_sub⟩ := h_spec 0 (show 0 < 100 by decide)
    have ⟨_, h_mod, _⟩ := h_sub 1 ⟨by decide, by decide⟩
    exact absurd h_mod (by decide)
  · intro ⟨_, _, h_spec⟩
    have ⟨_, h_sub⟩ := h_spec 0 (show 0 < 100 by decide)
    have ⟨_, h_mod, _⟩ := h_sub 999 (Or.inr rfl)
    exact absurd h_mod (by decide)
  · refine ⟨Or.inl ⟨0, by decide⟩,
      fun _ _ => ⟨trivial, 8, rfl⟩,
      fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_8 q⟩⟩
  · refine ⟨Or.inl ⟨0, by decide⟩,
      fun q _ => ⟨trivial, 8 * (q + 1), rfl⟩,
      fun q _ => ⟨trivial, fun o ho => ho ▸ h_spec_low q⟩⟩
  · refine ⟨Or.inl ⟨0, by decide⟩,
      fun q _ => ⟨trivial, 8 * (q + 1), Or.inl rfl⟩,
      fun q _ => ⟨trivial, fun o ho => ?_⟩⟩
    cases ho with
    | inl h1 => exact h1 ▸ h_spec_low q
    | inr h2 => exact h2 ▸ h_spec_high q

-- ============================================================================
-- Section 5: Master Synthesis & Kernel Axiom Audit
-- ============================================================================

/-- **Master Synthesis Theorem (`hyperproperties_bisimulation_mclean_and_lattice_synthesis`):**
    Combines all four mechanized theorem families in a single kernel-checked
    conjunction:
    1. **1-Trace Blindness vs. Demonic Self-Composition (`Theorem 1A` & `Theorem 1B`):**
       1-trace `VerifiedSpineOn` cannot separate `.ctCipher` from `.leakyCipher`
       when `obs` projects functional outputs, while demonic self-composition on
       `L.diag` is equivalent to `NonInterferingOn ∧ LeakageDeterministicOn`
       and therefore rejects secret-independent timing jitter (`true` on
       `L_crypto_jitter`).
    2. **One-Way Simulation Failure vs. Indexed Security Domain Bisimulation
       (`Theorem 2A` & `Theorem 2B`):**
       One-way `NonInterferingOn` is bypassed under asymmetric preorders
       (`.subsetLeakyCipher`), and positional tuple projections are bypassed by
       left-associated multi-secret/multi-channel types, whereas `SecurityDomain`
       induces genuine equivalence relations with non-trivial secret fibers and
       makes `DomainBiNonInterferingOn` sound and complete for possibilistic
       leakage-set invariance.
    3. **McLean's Refinement Paradox & Resolutions (`Theorem 3A` & `Theorem 3B`):**
       Standard `ProductiveCompiles` fails to preserve `DomainBiNonInterferingOn`
       (`.jitterSafeCipher ↦ .refinedLeakyCipher`), whereas both
       leakage-deterministic source verification (`Resolution 1`) and
       `LeakageBisimCompiles` / `UniformRefinementCompiles` (`Resolution 2`)
       soundly establish target 2-safety.
    4. **Nondeterminism Refinement Lattice (`Theorem 4A` & `Theorem 4B`):**
       `VerifiedSpineOn` rejects miracles, unbounded/bounded uninitialized-read
       chaos, and angelic may-violate nondeterminism while certifying
       specification-bounded nondeterminism and transferring across
       `ProductiveCompiles`. -/
theorem hyperproperties_bisimulation_mclean_and_lattice_synthesis :
    (∀ (dom pre : (Nat × Nat) → Prop) (obsPost : (Nat × Nat) → Nat → Prop),
      L_crypto_1trace.VerifiedSpineOn dom pre obsPost .ctCipher ↔
      L_crypto_1trace.VerifiedSpineOn dom pre obsPost .leakyCipher) ∧
    (L_crypto_jitter.NonInterferingOn (fun q => q.1 < 100)
       (fun q₁ q₂ => q₁.1 = q₂.1) (fun v₁ v₂ => v₁.2 = v₂.2) true ∧
     ¬ L_crypto_jitter.diag.VerifiedSpine
         (DiagPre (fun q => q.1 < 100) (fun q₁ q₂ => q₁.1 = q₂.1))
         (DiagPost (fun v₁ v₂ => v₁.2 = v₂.2))
         true) ∧
    (L_mclean.DomainBiNonInterferingOn stdCryptoDomain
       (fun q => q.1 < 100) .jitterSafeCipher ∧
     ProductiveCompiles L_mclean L_mclean (BehaviorCodec.id L_mclean)
       .jitterSafeCipher .refinedLeakyCipher ∧
     ¬ L_mclean.DomainBiNonInterferingOn stdCryptoDomain
         (fun q => q.1 < 100) .refinedLeakyCipher) ∧
    (L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .alignedAllocChoices ∧
     ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .miracleEmpty ∧
     ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .uninitByteRead ∧
     ¬ L_lattice.VerifiedSpine (fun q => q < 100) alignedAllocSpec .nondetMixed) :=
  ⟨theorem1a_one_trace_blind_to_two_safety.2.1,
   ⟨pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter.2.1,
    pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter.2.2.2⟩,
   ⟨theorem3a_mclean_refinement_paradox_counterexample.2.1,
    theorem3a_mclean_refinement_paradox_counterexample.2.2.1,
    theorem3a_mclean_refinement_paradox_counterexample.2.2.2.2.2⟩,
   ⟨theorem4b_productive_demonic_spec_refinement_characterization.2.2.2.2.2.2.1,
    theorem4b_productive_demonic_spec_refinement_characterization.1,
    theorem4b_productive_demonic_spec_refinement_characterization.2.2.1,
    theorem4b_productive_demonic_spec_refinement_characterization.2.2.2.1⟩⟩

#print axioms theorem1a_one_trace_blind_to_two_safety
#print axioms pentest_r2_9a_timing_only_diag_certifies_badCipher
#print axioms theorem1b_diag_iff_possibilistic_ni_and_leakage_deterministic
#print axioms pentest_r2_9b_demonic_diag_locks_out_secret_independent_jitter
#print axioms pentest_r3_7_asymmetric_one_way_ni_admits_subset_leak
#print axioms pentest_r3_6_policy_degeneracies
#print axioms pentest_r4_5_positional_tuple_bypasses
#print axioms theorem2b_security_domain_decomposition_characterization
#print axioms defense_r4_5_explicit_security_domains_refute_both_leaks
#print axioms theorem3a_mclean_refinement_paradox_counterexample
#print axioms theorem3b_resolution1_leakage_deterministic_transfer
#print axioms theorem3b_resolution2_leakage_bisim_compiles_and_uniform_refinement
#print axioms theorem4a_nondeterminism_pathology_hierarchy
#print axioms bounded_bitwidth_chaos_excludes_infinitely_many_values
#print axioms verifiedSpineOn_transfers_across_productiveCompiles
#print axioms theorem4b_productive_demonic_spec_refinement_characterization
#print axioms hyperproperties_bisimulation_mclean_and_lattice_synthesis

end HyperpropertiesBisimulationAndRefinementParadox

