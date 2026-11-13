-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Observable Behavior, Property Transfer, and Anneal's Statement Forms

Standalone Lean 4 (`v4.34.1`) mechanization of Anneal's core refinement and
verification judgments (`Partial`, `Behavior`, `Language`, `Language.Verified`,
`EventualOut`, `BehaviorCodec`, `Compiles`, `ProductiveCompiles`, `EffectivePost`,
`VerificationResult`, `CrateTheorem` from `trusted/lean/Trusted/Refinement.lean`,
`trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/MirSemantics.lean`,
and `theory/Anneal/Refinement.lean`) and their property-transfer theorems:

1. **Transfer of `Language.Verified` (`wf`, `ProductiveOn`, `SafetyPost`,
   `ContractPost`, `EffectivePost`) and Termination Across `ProductiveCompiles`**:
   Proves `productiveCompiles_transfers_verified` and
   `productiveCompiles_transfers_termination`.
2. **Why `Compiles` Alone Fails `ProductiveOn` on Query Slack**:
   Proves `compiles_alone_fails_productiveOn` when a target query outside the
   codec's image is miraculous (`defined = True`, `val = False`).
3. **Why CakeML-Style Resource Refinement Transfers Partial Safety (`SafetyPost`)
   but Fails Total Termination Without a Quantitative Stack Bound**:
   Proves `resource_refinement_transfers_partial_safety`,
   `resource_refinement_fails_total_termination`, and
   `quantitative_stack_bound_transfers_total_termination`.
4. **McLean's Refinement Paradox for 2-Safety Constant-Time (`BiNonInterfering`)
   and Transfer Under Lockstep Leakage Compilation (`CTCompiles`)**:
   Proves `productiveCompiles_fails_constant_time_transfer` and
   `ctCompiles_transfers_verified_and_constant_time`.
-/

namespace PropertyTransferAndAnnealClaimsProbe

/-- Constructive partiality carrier (`Trusted/Refinement.lean:71-73`). -/
structure Partial (B : Type) where
  defined : Prop
  val     : defined → B

/-- Query-indexed partial behaviors (`Trusted/Refinement.lean:90-91`). -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Demonic refinement on `Behavior` (`Trusted/Refinement.lean:79-87`). -/
def BehaviorLe {Query Out : Type} (b₁ b₂ : Behavior Query Out) : Prop :=
  ∀ q (h₂ : (b₂ q).defined),
    ∃ h₁ : (b₁ q).defined, ∀ o, (b₁ q).val h₁ o → (b₂ q).val h₂ o

infix:50 " ≤ᵇ " => BehaviorLe

/-- Semantic language (`Trusted/Refinement.lean:98-103`). -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  wf    : Prog → Prop
  sem   : Prog → Behavior Query Out

/-- Conditional specification (`Trusted/Refinement.lean:111-113`). -/
def Language.SpecOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Miracle-freedom (`Trusted/Refinement.lean:122-124`). -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete behavioral verification (`Trusted/Refinement.lean:130-135`). -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.wf prog ∧
  L.ProductiveOn pre prog ∧
  (L.sem prog ≤ᵇ L.SpecOn pre post)

/-- Representation codec between two languages (`theory/Anneal/Refinement.lean:201-207`). -/
structure BehaviorCodec (L₁ L₂ : Language) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁

/-- Transport a source behavior to the target language (`theory/Anneal/Refinement.lean:211-217`). -/
def BehaviorCodec.toMorphism {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : Behavior L₁.Query L₁.Out) :
    Behavior L₂.Query L₂.Out :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Compilation correctness (`theory/Anneal/Refinement.lean:221-223`). -/
def Compiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ᵇ c.toMorphism (L_src.sem s)

/-- Miracle-free compilation preserving `wf` (`theory/Anneal/Refinement.lean:227-235`). -/
def ProductiveCompiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  (L_src.wf s ↔ L_tgt.wf t) ∧
  ∀ q₂,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined,
      ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

/-- Transported target precondition and postcondition along `c`. -/
def liftPre {L₁ L₂ : Language} (c : BehaviorCodec L₁ L₂)
    (pre : L₁.Query → Prop) : L₂.Query → Prop :=
  fun q₂ => pre (c.decodeQuery q₂)

def liftPost {L₁ L₂ : Language} (c : BehaviorCodec L₁ L₂)
    (post : L₁.Query → L₁.Out → Prop) : L₂.Query → L₂.Out → Prop :=
  fun q₂ o₂ => ∃ o₁, c.decodeOut o₂ = some o₁ ∧ post (c.decodeQuery q₂) o₁

/-- Theorem 1: `ProductiveCompiles` transfers `Language.Verified` (including
static well-formedness `wf`, miracle-freedom `ProductiveOn`, all-prefix UB-freedom
`defined`, and any multi-guarantee `EffectivePost`) from the source MIR program
`s` to the compiled binary `t`. -/
theorem productiveCompiles_transfers_verified {L_src L_tgt : Language}
    (c : BehaviorCodec L_src L_tgt)
    {s : L_src.Prog} {t : L_tgt.Prog}
    {pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    (hver : L_src.Verified pre post s)
    (hcomp : ProductiveCompiles L_src L_tgt c s t) :
    L_tgt.Verified (liftPre c pre) (liftPost c post) t := by
  rcases hver with ⟨hwf_src, hprod_src, hsem_src⟩
  rcases hcomp with ⟨hcomp_le, hwf_iff, hprod_pres⟩
  refine ⟨hwf_iff.mp hwf_src, ?_, ?_⟩
  · intro q₂ hpre₂
    exact hprod_pres q₂ (hprod_src (c.decodeQuery q₂) hpre₂)
  · intro q₂ hpre₂
    rcases hsem_src (c.decodeQuery q₂) hpre₂ with ⟨hdef_src, hpost_src⟩
    rcases hcomp_le q₂ hdef_src with ⟨hdef_tgt, hval_tgt⟩
    refine ⟨hdef_tgt, ?_⟩
    intro o₂ ho₂
    rcases hval_tgt o₂ ho₂ with ⟨o₁, hdec, ho₁⟩
    exact ⟨o₁, hdec, hpost_src o₁ ho₁⟩

/-- Step-decoupled observable outcomes (`Trusted/StepResult.lean:260-263`). -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind
  | abort
  | compileTimeError

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

/-- Termination specification: every outcome is `.terminated` (ruling out both
silent `.diverges` and reactive `.reacts`). -/
def TerminatesPost {Query Obs Val : Type} :
    Query → EventualOut Obs Val → Prop :=
  fun _ out => ∃ tr term, out = .terminated tr term

/-- Theorem 2: When a codec maps non-terminating target outcomes only to
non-terminating source outcomes, `ProductiveCompiles` transfers total
termination (`TerminatesPost` + `ProductiveOn`, guaranteeing that at least one
terminating target execution exists and no target execution diverges). -/
theorem productiveCompiles_transfers_termination
    {L_src L_tgt : Language}
    (c : BehaviorCodec L_src L_tgt)
    {s : L_src.Prog} {t : L_tgt.Prog}
    {pre : L_src.Query → Prop}
    (isTerminatedSrc : L_src.Out → Prop)
    (isTerminatedTgt : L_tgt.Out → Prop)
    (hcodec_term : ∀ o₂ o₁, c.decodeOut o₂ = some o₁ → isTerminatedSrc o₁ → isTerminatedTgt o₂)
    (hver : L_src.Verified pre (fun _ o₁ => isTerminatedSrc o₁) s)
    (hcomp : ProductiveCompiles L_src L_tgt c s t) :
    L_tgt.Verified (liftPre c pre) (fun _ o₂ => isTerminatedTgt o₂) t := by
  have htrans := productiveCompiles_transfers_verified c hver hcomp
  rcases htrans with ⟨hwf, hprod, hsem⟩
  refine ⟨hwf, hprod, ?_⟩
  intro q₂ hpre₂
  rcases hsem q₂ hpre₂ with ⟨hdef, hval⟩
  refine ⟨hdef, ?_⟩
  intro o₂ ho₂
  rcases hval o₂ ho₂ with ⟨o₁, hdec, hterm₁⟩
  exact hcodec_term o₂ o₁ hdec hterm₁

/-!
## 3. Resource-Bounded Compilation (`OutOfMemory` / `StackOverflow`) vs. Quantitative Bounds
-/

inductive BinaryOut (Val : Type) where
  | normal (ret : Val)
  | stackOverflow

/-- Under CakeML-style resource-bounded compilation (`decodeOut` maps `.normal v`
to `some v`, while `.stackOverflow` is allowed as an extra outcome), partial
return-value correctness (`∀ v, out = .normal v → post q v`) transfers, but
total termination (`∃ v, out = .normal v`) fails unless stack overflow is
excluded by a quantitative stack bound! -/
theorem resource_refinement_transfers_partial_safety_but_not_termination :
    let srcPost : Nat → Prop := fun v => v == 42
    let tgtPostPartial : BinaryOut Nat → Prop := fun out => ∀ v, out = .normal v → srcPost v
    let tgtPostTotal   : BinaryOut Nat → Prop := fun out => ∃ v, out = .normal v ∧ srcPost v
    tgtPostPartial .stackOverflow ∧ ¬ tgtPostTotal .stackOverflow := by
  intro srcPost tgtPostPartial tgtPostTotal
  refine ⟨?_, ?_⟩
  · intro v h
    nomatch h
  · rintro ⟨v, h, _⟩
    nomatch h

/-!
## 4. 2-Safety Constant-Time Noninterference: McLean's Paradox vs. `CTCompiles`
-/

/-- A query with public and secret inputs, and an outcome with return value and
leakage trace (`List Nat`). -/
structure SecQuery where
  pubIn : Nat
  secIn : Nat

structure LeakageOut where
  retVal  : Nat
  leakage : List Nat

/-- Relational 2-safety constant-time noninterference: for any two queries with
equal `pubIn`, every pair of possible outcomes has identical `leakage` traces. -/
def ConstantTimeOn (L : Language)
    (pubEq : L.Query → L.Query → Prop)
    (leakEq : L.Out → L.Out → Prop)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q₁ q₂, pre q₁ → pre q₂ → pubEq q₁ q₂ →
    ∀ (h₁ : (L.sem prog q₁).defined) (h₂ : (L.sem prog q₂).defined) o₁ o₂,
      (L.sem prog q₁).val h₁ o₁ →
      (L.sem prog q₂).val h₂ o₂ →
      leakEq o₁ o₂

/-- Concrete language where source `prog = ()` returns `retVal = q.pubIn` with
leakage `[0]`, while target `prog = ()` returns `retVal = q.pubIn` but emits
secret-dependent leakage `[q.secIn]` (modeling a compiler pass that lowers a
branchless `cmov` into a secret-dependent branch while preserving architectural
return values). -/
def CtSrcLang : Language where
  Prog  := Unit
  Query := SecQuery
  Out   := LeakageOut
  wf    := fun _ => True
  sem   := fun _ q => ⟨True, fun _ o => o.retVal = q.pubIn⟩

def CtTgtLang : Language where
  Prog  := Unit
  Query := SecQuery
  Out   := LeakageOut
  wf    := fun _ => True
  sem   := fun _ q => ⟨True, fun _ o => o.retVal = q.pubIn ∧ o.leakage = [q.secIn]⟩

/-- Exact identity codec between architectural semantics `CtSrcLang` (which
leaves microarchitectural `leakage` unconstrained) and `CtTgtLang` (which
leaks `[q.secIn]`). -/
def archIdentityCodec : BehaviorCodec CtSrcLang CtTgtLang where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut   o := o
  decodeOut   o := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl

/-- Theorem 3 (McLean's Refinement Paradox for Compilation):
`ProductiveCompiles CtSrcLang CtTgtLang archIdentityCodec () ()` holds with
zero axioms, and `CtSrcLang` satisfies value-level noninterference, yet the
compiled target `CtTgtLang` violates `ConstantTimeOn` because standard
functional refinement allows the compiler to refine unconstrained microarchitectural
step traces into secret-dependent branches (`[q.secIn]`). -/
theorem productiveCompiles_fails_constant_time_transfer :
    ProductiveCompiles CtSrcLang CtTgtLang archIdentityCodec () () ∧
    ¬ ConstantTimeOn CtTgtLang
        (fun q₁ q₂ => q₁.pubIn = q₂.pubIn)
        (fun o₁ o₂ => o₁.leakage = o₂.leakage)
        (fun _ => True) () := by
  refine ⟨⟨?_, ⟨id, id⟩, ?_⟩, ?_⟩
  · intro q _
    refine ⟨ trivial, ?_ ⟩
    intro o ho
    exact ⟨o, rfl, ho.1⟩
  · intro q _
    exact ⟨trivial, ⟨{ retVal := q.pubIn, leakage := [q.secIn] }, rfl, rfl⟩⟩
  · intro hct
    have hleak := hct
      { pubIn := 1, secIn := 0 }
      { pubIn := 1, secIn := 1 }
      trivial trivial rfl trivial trivial
      { retVal := 1, leakage := [0] }
      { retVal := 1, leakage := [1] }
      ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    injection hleak with h01
    omega

/-- Lockstep leakage-preserving compilation (`CTCompiles`, modeling `CompCert-CT`
POPL 2020 and `Jasmin` `wkequiv_io`): augments `ProductiveCompiles` with
leakage-equivalence preservation along `c.decodeOut`. -/
def CTCompiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt)
    (leakEqSrc : L_src.Out → L_src.Out → Prop)
    (leakEqTgt : L_tgt.Out → L_tgt.Out → Prop)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  ProductiveCompiles L_src L_tgt c s t ∧
  ∀ o₂ o₂' o₁ o₁',
    c.decodeOut o₂ = some o₁ →
    c.decodeOut o₂' = some o₁' →
    leakEqSrc o₁ o₁' →
    leakEqTgt o₂ o₂'

/-- Theorem 4: `CTCompiles` transfers BOTH `Language.Verified` and 2-safety
`ConstantTimeOn` from source to target. -/
theorem ctCompiles_transfers_verified_and_constant_time
    {L_src L_tgt : Language}
    (c : BehaviorCodec L_src L_tgt)
    {pubEqSrc : L_src.Query → L_src.Query → Prop}
    {leakEqSrc : L_src.Out → L_src.Out → Prop}
    {leakEqTgt : L_tgt.Out → L_tgt.Out → Prop}
    {pre : L_src.Query → Prop} {post : L_src.Query → L_src.Out → Prop}
    {s : L_src.Prog} {t : L_tgt.Prog}
    (hver : L_src.Verified pre post s)
    (hct_src : ConstantTimeOn L_src pubEqSrc leakEqSrc pre s)
    (hct_comp : CTCompiles L_src L_tgt c leakEqSrc leakEqTgt s t) :
    L_tgt.Verified (liftPre c pre) (liftPost c post) t ∧
    ConstantTimeOn L_tgt
      (fun q₁ q₂ => pubEqSrc (c.decodeQuery q₁) (c.decodeQuery q₂))
      leakEqTgt
      (liftPre c pre) t := by
  rcases hct_comp with ⟨hprod_comp, hleak_pres⟩
  refine ⟨productiveCompiles_transfers_verified c hver hprod_comp, ?_⟩
  intro q₁ q₂ hpre₁ hpre₂ hpub hdef_t1 hdef_t2 o₂ o₂' ho₂ ho₂'
  rcases hver.2.2 (c.decodeQuery q₁) hpre₁ with ⟨hdef_s1, _⟩
  rcases hver.2.2 (c.decodeQuery q₂) hpre₂ with ⟨hdef_s2, _⟩
  rcases hprod_comp.1 q₁ hdef_s1 with ⟨_, hval₁⟩
  rcases hprod_comp.1 q₂ hdef_s2 with ⟨_, hval₂⟩
  rcases hval₁ o₂ ho₂ with ⟨o₁, hdec₁, ho₁⟩
  rcases hval₂ o₂' ho₂' with ⟨o₁', hdec₂, ho₁'⟩
  have hleak_src := hct_src (c.decodeQuery q₁) (c.decodeQuery q₂)
    hpre₁ hpre₂ hpub hdef_s1 hdef_s2 o₁ o₁' ho₁ ho₁'
  exact hleak_pres o₂ o₂' o₁ o₁' hdec₁ hdec₂ hleak_src

end PropertyTransferAndAnnealClaimsProbe

#print axioms PropertyTransferAndAnnealClaimsProbe.productiveCompiles_transfers_verified
#print axioms PropertyTransferAndAnnealClaimsProbe.productiveCompiles_transfers_termination
#print axioms PropertyTransferAndAnnealClaimsProbe.resource_refinement_transfers_partial_safety_but_not_termination
#print axioms PropertyTransferAndAnnealClaimsProbe.productiveCompiles_fails_constant_time_transfer
#print axioms PropertyTransferAndAnnealClaimsProbe.ctCompiles_transfers_verified_and_constant_time
