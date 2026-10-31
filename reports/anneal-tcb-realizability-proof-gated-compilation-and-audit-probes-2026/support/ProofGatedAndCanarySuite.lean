-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Proof-Gated Compilation, Fine-Grained `TrustPolicy`, and `BoundaryCanarySuite`

This standalone Lean 4 file mechanizes proof-gated compilation, fine-grained
`TrustPolicy` acknowledgment, and the `BoundaryCanarySuite` typeclass for
trusted language models:

1. **Proof-Gated Compilation & Fine-Grained `TrustPolicy` Acknowledgment**:
   - Proves that requiring *both* `L_src.sem s ≤ L_src.WellFormedOn pre` and
     `Compiles L_src L_tgt codec.toMorphism s t` makes *both* failure modes of
     an untrusted intermediate language (`MirLang` in `theory/`) **fail-closed**:
     - Spurious UB in `MirLang` breaks `L_src.sem s ≤ L_src.WellFormedOn pre`
       (`spurious_ub_breaks_wellFormedOn`),
     - Missing UB or missing nondeterministic outcomes in `MirLang` breaks
       `Compiles L_src L_tgt codec.toMorphism s t` whenever `X86Lang` in
       `trusted/` enforces the hardware trap or outcome (`missing_ub_breaks_compiles`,
       `missing_outcome_breaks_compiles`), and
     - Together they transfer `WellFormedOn` and `SpecOn` to `X86Lang` without
       trusting `MirLang` (`proof_gated_transfers_wellFormedOn`,
       `proof_gated_transfers_specOn`).
   - Mechanizes fine-grained `FineGrainedTCBItem` (`assumeSourceWellFormed`,
     `assumeSourceSpec`, `assumePassCompiles`, `assemblerLowering`) and
     `TrustPolicy` (`strictPolicy` vs. `incrementalDevPolicy`) so intentionally
     omitted proofs during incremental compiler development are explicitly
     declared in `tcb` and gated by `PolicyAdmits`.
2. **Mandatory `BoundaryCanarySuite` Typeclass for Language Models**:
   - Defines `BoundaryCanarySuite (M : X86MachineModel)` bundling positive
     conformance witnesses and negative refutation theorems across 10 critical
     semantic guards (64-bit modular `add`/`sub`, 64-bit shift-count masking,
     `idiv` divide-by-zero trap, `idiv` `INT64_MIN / -1` signed-overflow trap,
     stack-frame `slot < slotCount` bounds trap, 16-byte `rsp` alignment trap at
     `call`, callee-saved register restoration trap at `ret`, `transmute_copy`
     size-mismatch trap, `AdtInv` validity check trap, and CTFE admission
     non-vacuity).
   - Proves that `currentX86Model` (mirroring `Trusted/X86Semantics.lean` at
     `4f45f0a391a921ced9c9dc773b9a040dbc215d14`) **provably fails**
     `BoundaryCanarySuite` (`currentX86Model_fails_BoundaryCanarySuite`), while
     `fixedX86Model` **provably instantiates** `BoundaryCanarySuite`
     (`instBoundaryCanarySuiteFixedX86Model`).
-/

namespace Anneal.ProofGatedAndCanarySuite

/-! ## Section 1: Core Refinement Primitives -/

structure Partial (Out : Type u) where
  defined : Prop
  outcomes : Out → Prop

namespace Partial

def le (a b : Partial Out) : Prop :=
  b.defined → a.defined ∧ ∀ o, a.outcomes o → b.outcomes o

instance : LE (Partial Out) := ⟨Partial.le⟩

theorem le_refl (a : Partial Out) : a ≤ a :=
  fun hd => ⟨hd, fun _ ho => ho⟩

theorem le_trans {a b c : Partial Out} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  intro hc
  obtain ⟨hb, hbc_out⟩ := hbc hc
  obtain ⟨ha, hab_out⟩ := hab hb
  exact ⟨ha, fun o hoa => hbc_out o (hab_out o hoa)⟩

def ub : Partial Out where
  defined := False
  outcomes := fun _ => True

end Partial

def Sem (Q : Type u) (Out : Type v) := Q → Partial Out

namespace Sem

def le (f g : Sem Q Out) : Prop := ∀ q, (f q).le (g q)

instance : LE (Sem Q Out) := ⟨Sem.le⟩

theorem le_refl (f : Sem Q Out) : f ≤ f :=
  fun q => Partial.le_refl (f q)

theorem le_trans {f g h : Sem Q Out} (hfg : f ≤ g) (hgh : g ≤ h) : f ≤ h :=
  fun q => Partial.le_trans (hfg q) (hgh q)

end Sem

structure Language where
  Prog : Type u
  Query : Type v
  Out : Type w
  sem : Prog → Sem Query Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : Sem L.Query L.Out :=
  fun q => {
    defined := pre q
    outcomes := fun o => pre q → post q o
  }

def Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    Sem L.Query L.Out :=
  L.SpecOn pre (fun _ _ => True)

def Compiles (L₁ L₂ : Language)
    (π_c : Sem L₁.Query L₁.Out → Sem L₂.Query L₂.Out)
    (p₁ : L₁.Prog) (p₂ : L₂.Prog) : Prop :=
  L₂.sem p₂ ≤ π_c (L₁.sem p₁)

/-! ## Section 2: `BehaviorCodec` and Proof-Gated Compilation -/

/-- A codec translating target queries and outcomes back to source queries and
outcomes (generalizing `π_stage0` in `theory/Anneal/Compiler/NaiveCodegen.lean:155-158`). -/
structure BehaviorCodec (L_src L_tgt : Language) where
  decompileQ : L_tgt.Query → L_src.Query
  decompileOut : L_tgt.Out → L_src.Out

/-- The induced monotonic behavior morphism `Sem L_src → Sem L_tgt`. -/
def BehaviorCodec.toMorphism {L_src L_tgt : Language}
    (codec : BehaviorCodec L_src L_tgt)
    (srcSem : Sem L_src.Query L_src.Out) : Sem L_tgt.Query L_tgt.Out :=
  fun q_tgt => {
    defined := (srcSem (codec.decompileQ q_tgt)).defined
    outcomes := fun o_tgt =>
      (srcSem (codec.decompileQ q_tgt)).outcomes (codec.decompileOut o_tgt)
  }

/-- **Theorem 1A (`spurious_ub_breaks_wellFormedOn`)**:
If an untrusted intermediate language `L_src` (`MirLang` in `theory/`) introduces
spurious UB (`¬ (L_src.sem s q_src).defined`) at any query `q_src` satisfying
`pre q_src`, then the source well-formedness gate
`L_src.sem s ≤ L_src.WellFormedOn pre` is refutable (fail-closed). -/
theorem spurious_ub_breaks_wellFormedOn
    {L_src : Language} (s : L_src.Prog) (pre : L_src.Query → Prop)
    (q_src : L_src.Query)
    (h_pre : pre q_src)
    (h_spurious_ub : ¬ (L_src.sem s q_src).defined) :
    ¬ (L_src.sem s ≤ L_src.WellFormedOn pre) := by
  intro h_wf
  obtain ⟨h_def, _⟩ := h_wf q_src h_pre
  exact h_spurious_ub h_def

/-- **Theorem 1B (`missing_ub_breaks_compiles`)**:
If an untrusted intermediate language `L_src` (`MirLang` in `theory/`) omits a
real UB/fault condition at `codec.decompileQ q_tgt` (so `(L_src.sem s (codec.decompileQ q_tgt)).defined`
holds), while the trusted target ISA `L_tgt` (`X86Lang` in `trusted/`) traps at
`q_tgt` (`¬ (L_tgt.sem t q_tgt).defined`), then the compilation refinement gate
`Compiles L_src L_tgt codec.toMorphism s t` is refutable (fail-closed). -/
theorem missing_ub_breaks_compiles
    {L_src L_tgt : Language} (codec : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog) (q_tgt : L_tgt.Query)
    (h_src_defined : (L_src.sem s (codec.decompileQ q_tgt)).defined)
    (h_tgt_traps : ¬ (L_tgt.sem t q_tgt).defined) :
    ¬ Compiles L_src L_tgt codec.toMorphism s t := by
  intro h_compiles
  obtain ⟨h_tgt_def, _⟩ := h_compiles q_tgt h_src_defined
  exact h_tgt_traps h_tgt_def

/-- **Theorem 1C (`missing_outcome_breaks_compiles`)**:
If `L_src` under-approximates runtime behavior (e.g., models `0 - 1 = 0` instead
of `2^64 - 1`, or omits a nondeterministic outcome `o_tgt` that `L_tgt` can
produce at `q_tgt`), then `Compiles L_src L_tgt codec.toMorphism s t` is
refutable whenever `(L_src.sem s (codec.decompileQ q_tgt)).defined` holds. -/
theorem missing_outcome_breaks_compiles
    {L_src L_tgt : Language} (codec : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog)
    (q_tgt : L_tgt.Query) (o_tgt : L_tgt.Out)
    (h_src_defined : (L_src.sem s (codec.decompileQ q_tgt)).defined)
    (h_tgt_out : (L_tgt.sem t q_tgt).outcomes o_tgt)
    (h_src_omits : ¬ (L_src.sem s (codec.decompileQ q_tgt)).outcomes (codec.decompileOut o_tgt)) :
    ¬ Compiles L_src L_tgt codec.toMorphism s t := by
  intro h_compiles
  obtain ⟨_, h_out⟩ := h_compiles q_tgt h_src_defined
  exact h_src_omits (h_out o_tgt h_tgt_out)

/-- **Theorem 1D (`proof_gated_transfers_wellFormedOn`)**:
When *both* gates (`L_src.sem s ≤ L_src.WellFormedOn pre` and
`Compiles L_src L_tgt codec.toMorphism s t`) hold, well-formedness transfers
to `L_tgt` on `fun q => pre (codec.decompileQ q)` without trusting `L_src`. -/
theorem proof_gated_transfers_wellFormedOn
    {L_src L_tgt : Language} (codec : BehaviorCodec L_src L_tgt)
    (pre : L_src.Query → Prop) (s : L_src.Prog) (t : L_tgt.Prog)
    (h_src_wf : L_src.sem s ≤ L_src.WellFormedOn pre)
    (h_compiles : Compiles L_src L_tgt codec.toMorphism s t) :
    L_tgt.sem t ≤ L_tgt.WellFormedOn (fun q => pre (codec.decompileQ q)) := by
  intro q h_pre
  obtain ⟨h_src_def, _⟩ := h_src_wf (codec.decompileQ q) h_pre
  obtain ⟨h_tgt_def, _⟩ := h_compiles q h_src_def
  exact ⟨h_tgt_def, fun _ _ _ => trivial⟩

/-- **Theorem 1E (`proof_gated_transfers_specOn`)**:
When *both* `L_src.sem s ≤ L_src.SpecOn pre post` and
`Compiles L_src L_tgt codec.toMorphism s t` hold, the full behavioral
specification transfers to `L_tgt` without trusting `L_src`. -/
theorem proof_gated_transfers_specOn
    {L_src L_tgt : Language} (codec : BehaviorCodec L_src L_tgt)
    (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) (t : L_tgt.Prog)
    (h_src_spec : L_src.sem s ≤ L_src.SpecOn pre post)
    (h_compiles : Compiles L_src L_tgt codec.toMorphism s t) :
    L_tgt.sem t ≤
      L_tgt.SpecOn (fun q => pre (codec.decompileQ q))
        (fun q o => post (codec.decompileQ q) (codec.decompileOut o)) := by
  intro q h_pre
  obtain ⟨h_src_def, h_src_out⟩ := h_src_spec (codec.decompileQ q) h_pre
  obtain ⟨h_tgt_def, h_tgt_out⟩ := h_compiles q h_src_def
  exact ⟨h_tgt_def, fun o ho _ => h_src_out (codec.decompileOut o) (h_tgt_out o ho) h_pre⟩

/-! ## Section 3: Fine-Grained `FineGrainedTCBItem` & `TrustPolicy` for Intentionally Omitted Proofs -/

/-- Fine-grained TCB assumption items that allow intentionally omitted proofs
during incremental development to be tracked explicitly per function and pass. -/
inductive FineGrainedTCBItem (L_src L_tgt : Language)
    (codec : BehaviorCodec L_src L_tgt) where
  | assumeSourceWellFormed
      (fnName : String) (s : L_src.Prog) (pre : L_src.Query → Prop)
  | assumeSourceSpec
      (fnName : String) (s : L_src.Prog)
      (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
  | assumePassCompiles
      (passName fnName : String) (s : L_src.Prog) (t : L_tgt.Prog)
  | assemblerLowering

/-- The exact semantic proposition assumed by each `FineGrainedTCBItem`. -/
def FineGrainedTCBItem.meaning {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    (item : FineGrainedTCBItem L_src L_tgt codec)
    (assemblerSound : Prop) : Prop :=
  match item with
  | .assumeSourceWellFormed _ s pre =>
      L_src.sem s ≤ L_src.WellFormedOn pre
  | .assumeSourceSpec _ s pre post =>
      L_src.sem s ≤ L_src.SpecOn pre post
  | .assumePassCompiles _ _ s t =>
      Compiles L_src L_tgt codec.toMorphism s t
  | .assemblerLowering =>
      assemblerSound

/-- All items in `tcb` hold semantically. -/
def FineGrainedTCBValid {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    (tcb : List (FineGrainedTCBItem L_src L_tgt codec))
    (assemblerSound : Prop) : Prop :=
  ∀ item ∈ tcb, item.meaning assemblerSound

/-- A boolean trust policy deciding which TCB assumptions are permitted. -/
def TrustPolicy (L_src L_tgt : Language) (codec : BehaviorCodec L_src L_tgt) :=
  FineGrainedTCBItem L_src L_tgt codec → Bool

/-- `strictPolicy` permits *only* `.assemblerLowering`; all proof-skipping
assumptions (`assumeSourceWellFormed`, `assumeSourceSpec`, `assumePassCompiles`)
are rejected. -/
def strictPolicy {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt} : TrustPolicy L_src L_tgt codec
  | .assemblerLowering => true
  | .assumeSourceWellFormed _ _ _ => false
  | .assumeSourceSpec _ _ _ _ => false
  | .assumePassCompiles _ _ _ _ => false

/-- `incrementalDevPolicy` permits `.assemblerLowering` plus explicitly
allowlisted function/pass assumptions during staged compiler bring-up. -/
def incrementalDevPolicy {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    (allowedSourceFns : List String)
    (allowedPasses : List (String × String)) : TrustPolicy L_src L_tgt codec
  | .assemblerLowering => true
  | .assumeSourceWellFormed fnName _ _ => allowedSourceFns.contains fnName
  | .assumeSourceSpec fnName _ _ _ => allowedSourceFns.contains fnName
  | .assumePassCompiles passName fnName _ _ =>
      allowedPasses.contains (passName, fnName)

/-- Policy gate: every item in `tcb` must be approved by `policy`. -/
def PolicyAdmits {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    (policy : TrustPolicy L_src L_tgt codec)
    (tcb : List (FineGrainedTCBItem L_src L_tgt codec)) : Prop :=
  ∀ item ∈ tcb, policy item = true

/-- **Theorem 1F (`strictPolicy_forbids_omitted_proofs`)**:
Under `strictPolicy`, neither `.assumeSourceWellFormed`, `.assumeSourceSpec`,
nor `.assumePassCompiles` can appear in any policy-admitted `tcb`. -/
theorem strictPolicy_forbids_omitted_proofs
    {L_src L_tgt : Language} {codec : BehaviorCodec L_src L_tgt}
    (tcb : List (FineGrainedTCBItem L_src L_tgt codec))
    (h_admits : PolicyAdmits strictPolicy tcb) :
    (∀ fn s pre,
      FineGrainedTCBItem.assumeSourceWellFormed fn s pre ∉ tcb) ∧
    (∀ fn s pre post,
      FineGrainedTCBItem.assumeSourceSpec fn s pre post ∉ tcb) ∧
    (∀ pass fn s t,
      FineGrainedTCBItem.assumePassCompiles pass fn s t ∉ tcb) := by
  refine ⟨?_, ?_, ?_⟩
  · intro fn s pre h_in
    have h_eq := h_admits (.assumeSourceWellFormed fn s pre) h_in
    cases h_eq
  · intro fn s pre post h_in
    have h_eq := h_admits (.assumeSourceSpec fn s pre post) h_in
    cases h_eq
  · intro pass fn s t h_in
    have h_eq := h_admits (.assumePassCompiles pass fn s t) h_in
    cases h_eq

/-- Proof-or-acknowledged-assumption witness for a stage obligation. -/
inductive DischargedOrAssumed {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    (tcb : List (FineGrainedTCBItem L_src L_tgt codec))
    (assemblerSound : Prop) (P : Prop) : Prop where
  | proven (h : P)
  | assumed (item : FineGrainedTCBItem L_src L_tgt codec)
      (h_in : item ∈ tcb) (h_eq : item.meaning assemblerSound = P)

theorem DischargedOrAssumed.extract {L_src L_tgt : Language}
    {codec : BehaviorCodec L_src L_tgt}
    {tcb : List (FineGrainedTCBItem L_src L_tgt codec)}
    {assemblerSound P : Prop}
    (h_valid : FineGrainedTCBValid tcb assemblerSound)
    (d : DischargedOrAssumed tcb assemblerSound P) : P := by
  cases d with
  | proven h => exact h
  | assumed item h_in h_eq =>
      exact h_eq ▸ h_valid item h_in

/-- **Theorem 1G (`gated_pipeline_soundness`)**:
Whether the source specification proof and compilation pass proof are discharged
by kernel proofs (`DischargedOrAssumed.proven`) or explicitly declared in `tcb`
and admitted by `policy` (`DischargedOrAssumed.assumed`), `PolicyAdmits` +
`FineGrainedTCBValid` guarantees the target specification on `L_tgt`. -/
theorem gated_pipeline_soundness
    {L_src L_tgt : Language} (codec : BehaviorCodec L_src L_tgt)
    (policy : TrustPolicy L_src L_tgt codec)
    (tcb : List (FineGrainedTCBItem L_src L_tgt codec))
    (assemblerSound : Prop)
    (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) (t : L_tgt.Prog)
    (_h_policy : PolicyAdmits policy tcb)
    (h_tcb : FineGrainedTCBValid tcb assemblerSound)
    (d_src : DischargedOrAssumed tcb assemblerSound
      (L_src.sem s ≤ L_src.SpecOn pre post))
    (d_comp : DischargedOrAssumed tcb assemblerSound
      (Compiles L_src L_tgt codec.toMorphism s t)) :
    L_tgt.sem t ≤
      L_tgt.SpecOn (fun q => pre (codec.decompileQ q))
        (fun q o => post (codec.decompileQ q) (codec.decompileOut o)) :=
  proof_gated_transfers_specOn codec pre post s t
    (d_src.extract h_tcb) (d_comp.extract h_tcb)

/-! ## Section 4: Mandatory `BoundaryCanarySuite` for Language Models -/

/-- Arithmetic status flags in `RFLAGS`. -/
structure RFlags where
  cf : Bool
  zf : Bool
  sf : Bool
  of : Bool
  deriving DecidableEq, Repr

/-- Unified interface for an x86-64 operational semantics model to be tested
against the mandatory `BoundaryCanarySuite`. -/
structure X86MachineModel where
  /-- 64-bit `add` (`addq`) returning `(result_toNat, CF, ZF)`. -/
  evalAdd64 : Nat → Nat → Nat × Bool × Bool
  /-- 64-bit `sub` (`subq`) returning `(result_toNat, CF, SF)`. -/
  evalSub64 : Nat → Nat → Nat × Bool × Bool
  /-- 64-bit `shl` (`shlq`) returning `Partial (result_toNat × RFlags)`. -/
  evalShl64 : Nat → Nat → RFlags → Partial (Nat × RFlags)
  /-- 64-bit `shr` (`shrq`) returning `result_toNat`. -/
  evalShr64 : Nat → Nat → Nat
  /-- 64-bit signed division (`idivq`) returning `Partial (quot_toNat × rem_toNat)`. -/
  evalIdiv64 : BitVec 64 → BitVec 64 → Partial (BitVec 64 × BitVec 64)
  /-- Stack-frame slot write `writeSlot slotCount slotIdx val`. -/
  evalSlotWrite : Nat → Nat → Nat → Partial Nat
  /-- `call` instruction checking System V AMD64 16-byte `rsp` alignment. -/
  evalCallAlign : Nat → Partial Unit
  /-- `ret` instruction checking callee-saved register preservation (`rbp`, `rbx`, `r12`..`r15`). -/
  evalRetCalleeSaved : BitVec 64 → BitVec 64 → Partial Unit
  /-- `transmute_copy` (`rep movsb`) checking `srcByteSize == dstByteSize`. -/
  evalTransmuteCopy : Nat → Nat → Nat → Partial Nat
  /-- Typed scalar/ADT load checking `AdtInv` validity (e.g., `bool` byte `< 2`). -/
  evalLoadBool : Nat → Partial Bool
  /-- CTFE `MonoAdmitted` predicate paired with `ConstNoUnmodeled` non-vacuity guard. -/
  evalCtfeCheck : Bool → Bool → Bool × Bool

/-- **Mandatory `BoundaryCanarySuite` Typeclass**:
Every language model in `trusted/` must instantiate this suite, which pairs
positive conformance witnesses with **negative refutation theorems** that fail
to typecheck if any safety or validity guard in the semantics is weakened. -/
class BoundaryCanarySuite (M : X86MachineModel) : Prop where
  /-- Guard 1A (Positive): `(2^64 - 1) + 1` wraps modulo `2^64` to `0` with `CF = true, ZF = true`. -/
  canary_pos_add64_wrap :
    M.evalAdd64 (2 ^ 64 - 1) 1 = (0, true, true)
  /-- Guard 1B (Negative Refutation): `(2^64 - 1) + 1` must NOT equal unbounded `2^64`. -/
  canary_neg_add64_no_unbounded_nat :
    (M.evalAdd64 (2 ^ 64 - 1) 1).1 ≠ 2 ^ 64
  /-- Guard 2A (Positive): `0 - 1` wraps modulo `2^64` to `2^64 - 1` with `CF = true, SF = true`. -/
  canary_pos_sub64_wrap :
    M.evalSub64 0 1 = (2 ^ 64 - 1, true, true)
  /-- Guard 2B (Negative Refutation): `0 - 1` must NOT truncate to `0` (`Nat` subtraction bug). -/
  canary_neg_sub64_no_zero_truncation :
    (M.evalSub64 0 1).1 ≠ 0
  /-- Guard 3A (Positive): `shlq(1, 64)` masks shift count by `63` (`64 & 63 = 0`)
  and preserves incoming `RFlags`. -/
  canary_pos_shl64_mask_and_flags :
    ∀ f : RFlags,
      (M.evalShl64 1 64 f).defined ∧ (M.evalShl64 1 64 f).outcomes (1, f)
  /-- Guard 3B (Negative Refutation): `shlq(1, 64)` must NOT produce `2^64` and
  `shrq(1, 64)` must NOT produce `0`. -/
  canary_neg_shift64_no_unmasked_count :
    ∀ f : RFlags,
      ¬ (M.evalShl64 1 64 f).outcomes (2 ^ 64, f) ∧ M.evalShr64 1 64 ≠ 0
  /-- Guard 4A (Positive): `idivq(42, 7)` is defined and yields `(6, 0)`. -/
  canary_pos_idiv64_normal :
    (M.evalIdiv64 42#64 7#64).defined ∧
    (M.evalIdiv64 42#64 7#64).outcomes (6#64, 0#64)
  /-- Guard 4B (Negative Refutation — Divide-by-Zero `#DE` Trap):
  `idivq(42, 0)` must be undefined (`¬ defined`). -/
  canary_neg_idiv64_div_zero_traps :
    ¬ (M.evalIdiv64 42#64 0#64).defined
  /-- Guard 5 (Negative Refutation — Signed Overflow `INT64_MIN / -1` `#DE` Trap):
  `idivq(INT64_MIN, -1)` must be undefined (`¬ defined`). -/
  canary_neg_idiv64_intmin_overflow_traps :
    ¬ (M.evalIdiv64 0x8000000000000000#64 0xffffffffffffffff#64).defined
  /-- Guard 6A (Positive): In-bounds stack slot write (`slotIdx < slotCount`) succeeds. -/
  canary_pos_slot_write_in_bounds :
    (M.evalSlotWrite 4 2 99).defined ∧ (M.evalSlotWrite 4 2 99).outcomes 99
  /-- Guard 6B (Negative Refutation — Out-of-Frame Stack Slot Clobber Trap):
  Writing to `slotIdx ≥ slotCount` must be undefined (`¬ defined`). -/
  canary_neg_slot_write_out_of_bounds_traps :
    ¬ (M.evalSlotWrite 4 4 99).defined
  /-- Guard 7A (Positive): `call` with 16-byte aligned `rsp` (`rsp % 16 == 0`) succeeds. -/
  canary_pos_call_rsp_aligned :
    (M.evalCallAlign 0x7fffffffe000).defined
  /-- Guard 7B (Negative Refutation — Misaligned `rsp` at `call` Trap):
  `call` with `rsp % 16 == 8` must be undefined (`¬ defined`). -/
  canary_neg_call_rsp_misaligned_traps :
    ¬ (M.evalCallAlign 0x7fffffffe008).defined
  /-- Guard 8A (Positive): `ret` with preserved callee-saved register state succeeds. -/
  canary_pos_ret_callee_saved_preserved :
    (M.evalRetCalleeSaved 0x1234#64 0x1234#64).defined
  /-- Guard 8B (Negative Refutation — Clobbered Callee-Saved Register Trap):
  `ret` when exit callee-saved register differs from entry must be undefined (`¬ defined`). -/
  canary_neg_ret_callee_saved_clobbered_traps :
    ¬ (M.evalRetCalleeSaved 0x1234#64 0xdead#64).defined
  /-- Guard 9A (Positive): `transmute_copy` with matching `srcSize == dstSize` succeeds. -/
  canary_pos_transmute_copy_same_size :
    (M.evalTransmuteCopy 8 8 0xabcd).defined ∧
    (M.evalTransmuteCopy 8 8 0xabcd).outcomes 0xabcd
  /-- Guard 9B (Negative Refutation — Size-Mismatched `transmute_copy` Trap):
  `transmute_copy` with `srcSize ≠ dstSize` must be undefined (`¬ defined`). -/
  canary_neg_transmute_copy_size_mismatch_traps :
    ¬ (M.evalTransmuteCopy 8 16 0xabcd).defined
  /-- Guard 10A (Positive): Loading a valid `bool` byte (`0` or `1`) succeeds. -/
  canary_pos_load_bool_valid :
    (M.evalLoadBool 1).defined ∧ (M.evalLoadBool 1).outcomes true
  /-- Guard 10B (Negative Refutation — Invalid `AdtInv` Discriminant Trap):
  Loading an invalid `bool` byte (`2`) must be undefined (`¬ defined`). -/
  canary_neg_load_bool_invalid_discriminant_traps :
    ¬ (M.evalLoadBool 2).defined
  /-- Guard 11 (Positive & Negative — CTFE Non-Vacuity & Panic Filtering):
  `evalCtfeCheck isModeled constPassed` returns `(constNoUnmodeled, monoAdmitted)`:
  - When `isModeled = true` and `constPassed = true`, `monoAdmitted = true`.
  - When `isModeled = true` and `constPassed = false`, `monoAdmitted = false`.
  - When `isModeled = false` (unmodeled CTFE instruction), `constNoUnmodeled = false`
    (blocking CTFE vacuous verification!). -/
  canary_ctfe_polarity_guards :
    M.evalCtfeCheck true true = (true, true) ∧
    M.evalCtfeCheck true false = (true, false) ∧
    (M.evalCtfeCheck false true).1 = false

/-! ## Section 5: Current `X86Semantics.lean` (`4f45f0a391a9`) Provably Fails `BoundaryCanarySuite` -/

/-- Model capturing the exact `Nat` ALU and unchecked `writeSlot` behavior of
`mir-to-x86/trusted/lean/Trusted/X86Semantics.lean` at commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`. -/
def currentX86Model : X86MachineModel where
  evalAdd64 := fun a b => (a + b, false, (a + b) == 0)
  evalSub64 := fun a b => (a - b, false, false)
  evalShl64 := fun a b f =>
    { defined := True, outcomes := fun out => out = (a <<< b, f) }
  evalShr64 := fun a b => a >>> b
  evalIdiv64 := fun a b =>
    if b == 0#64 then Partial.ub
    else { defined := True, outcomes := fun out => out = (a.sdiv b, a.srem b) }
  -- In `X86Semantics.lean:105-115`, `writeSlot` never checks `slotIdx < slotCount`!
  evalSlotWrite := fun _slotCount _slotIdx val =>
    { defined := True, outcomes := fun out => out = val }
  evalCallAlign := fun _rsp => { defined := True, outcomes := fun _ => True }
  evalRetCalleeSaved := fun _ _ => { defined := True, outcomes := fun _ => True }
  evalTransmuteCopy := fun srcSz dstSz val =>
    if srcSz == dstSz then { defined := True, outcomes := fun out => out = val }
    else Partial.ub
  evalLoadBool := fun b =>
    if b < 2 then { defined := True, outcomes := fun out => out = (b == 1) }
    else Partial.ub
  -- In `X86Semantics.lean:547-555`, `.failed .unmodeled` is not separated from
  -- `.terminated .unwind`, so `constNoUnmodeled` is missing (`true`).
  evalCtfeCheck := fun isModeled constPassed => (true, isModeled && constPassed)

/-- **Theorem 2A (`currentX86Model_fails_BoundaryCanarySuite`)**:
`currentX86Model` (matching `Trusted/X86Semantics.lean` at `4f45f0a391a9`)
provably violates `BoundaryCanarySuite` (in fact, it fails Guards 1B, 2B, 3B,
5, 6B, 7B, 8B, and 11 simultaneously). -/
theorem currentX86Model_fails_BoundaryCanarySuite :
    ¬ BoundaryCanarySuite currentX86Model := by
  intro h_suite
  have h_no_trunc := h_suite.canary_neg_sub64_no_zero_truncation
  exact h_no_trunc rfl

/-! ## Section 6: Corrected `fixedX86Model` Instantiates `BoundaryCanarySuite` -/

/-- Corrected 64-bit `BitVec 64` + bounds-checked x86-64 semantics model.
Each safety/validity guard is annotated with a `-- MUTATE_GUARD:` marker for
automated guard-mutation testing. -/
def fixedX86Model : X86MachineModel where
  evalAdd64 := fun a b =>
    let va := BitVec.ofNat 64 a
    let vb := BitVec.ofNat 64 b
    let res := (va + vb).toNat -- MUTATE_GUARD: alu_mod64_add
    let cf := a + b >= 2 ^ 64
    (res, cf, res == 0)
  evalSub64 := fun a b =>
    let va := BitVec.ofNat 64 a
    let vb := BitVec.ofNat 64 b
    let res := (va - vb).toNat -- MUTATE_GUARD: alu_mod64_sub
    let cf := a < b
    (res, cf, res >= 2 ^ 63)
  evalShl64 := fun a b f =>
    let va := BitVec.ofNat 64 a
    let c := b % 64 -- MUTATE_GUARD: shift_mask64_check
    if c == 0 then
      { defined := True, outcomes := fun out => out = (va.toNat, f) }
    else
      let res := (va <<< (BitVec.ofNat 64 c)).toNat
      let cf := va.getLsbD (64 - c)
      let zf := res == 0
      let sf := res >= 2 ^ 63
      { defined := True,
        outcomes := fun out =>
          ∃ of_nd : Bool, out = (res, { cf, zf, sf, of := of_nd }) }
  evalShr64 := fun a b =>
    let c := b % 64 -- MUTATE_GUARD: shift_mask64_shr_check
    ((BitVec.ofNat 64 a) >>> (BitVec.ofNat 64 c)).toNat
  evalIdiv64 := fun dividend divisor =>
    let divZero := divisor == 0#64 -- MUTATE_GUARD: div_zero_check
    let sOverflow := dividend == 0x8000000000000000#64 && divisor == 0xffffffffffffffff#64 -- MUTATE_GUARD: idiv_overflow_check
    if divZero || sOverflow then
      Partial.ub
    else
      { defined := True,
        outcomes := fun out => out = (dividend.sdiv divisor, dividend.srem divisor) }
  evalSlotWrite := fun slotCount slotIdx val =>
    let inBounds := slotIdx < slotCount -- MUTATE_GUARD: slot_bounds_check
    if inBounds then
      { defined := True, outcomes := fun out => out = val }
    else
      Partial.ub
  evalCallAlign := fun rsp =>
    let aligned := rsp % 16 == 0 -- MUTATE_GUARD: rsp_align16_check
    if aligned then
      { defined := True, outcomes := fun _ => True }
    else
      Partial.ub
  evalRetCalleeSaved := fun savedEntry savedExit =>
    let preserved := savedEntry == savedExit -- MUTATE_GUARD: callee_saved_check
    if preserved then
      { defined := True, outcomes := fun _ => True }
    else
      Partial.ub
  evalTransmuteCopy := fun srcSz dstSz val =>
    let sizeMatch := srcSz == dstSz -- MUTATE_GUARD: transmute_size_check
    if sizeMatch then
      { defined := True, outcomes := fun out => out = val }
    else
      Partial.ub
  evalLoadBool := fun byteVal =>
    let validBool := byteVal < 2 -- MUTATE_GUARD: adt_inv_check
    if validBool then
      { defined := True, outcomes := fun out => out = (byteVal == 1) }
    else
      Partial.ub
  evalCtfeCheck := fun isModeled constPassed =>
    let noUnmodeled := isModeled -- MUTATE_GUARD: ctfe_no_unmodeled_check
    let monoAdmitted := isModeled && constPassed -- MUTATE_GUARD: ctfe_mono_admitted_check
    (noUnmodeled, monoAdmitted)

/-- **Theorem 2B (`instBoundaryCanarySuiteFixedX86Model`)**:
`fixedX86Model` satisfies all positive and negative canaries in
`BoundaryCanarySuite`. -/
instance instBoundaryCanarySuiteFixedX86Model :
    BoundaryCanarySuite fixedX86Model where
  canary_pos_add64_wrap := by decide
  canary_neg_add64_no_unbounded_nat := by decide
  canary_pos_sub64_wrap := by decide
  canary_neg_sub64_no_zero_truncation := by decide
  canary_pos_shl64_mask_and_flags := fun f => ⟨trivial, rfl⟩
  canary_neg_shift64_no_unmasked_count := by
    intro f
    refine ⟨?_, by decide⟩
    intro h_out
    injection h_out with h_eq _
    revert h_eq
    decide
  canary_pos_idiv64_normal := ⟨trivial, rfl⟩
  canary_neg_idiv64_div_zero_traps := fun h => h
  canary_neg_idiv64_intmin_overflow_traps := fun h => h
  canary_pos_slot_write_in_bounds := ⟨trivial, rfl⟩
  canary_neg_slot_write_out_of_bounds_traps := fun h => h
  canary_pos_call_rsp_aligned := trivial
  canary_neg_call_rsp_misaligned_traps := fun h => h
  canary_pos_ret_callee_saved_preserved := trivial
  canary_neg_ret_callee_saved_clobbered_traps := fun h => h
  canary_pos_transmute_copy_same_size := ⟨trivial, rfl⟩
  canary_neg_transmute_copy_size_mismatch_traps := fun h => h
  canary_pos_load_bool_valid := ⟨trivial, rfl⟩
  canary_neg_load_bool_invalid_discriminant_traps := fun h => h
  canary_ctfe_polarity_guards := by decide

end Anneal.ProofGatedAndCanarySuite

#print axioms Anneal.ProofGatedAndCanarySuite.spurious_ub_breaks_wellFormedOn
#print axioms Anneal.ProofGatedAndCanarySuite.missing_ub_breaks_compiles
#print axioms Anneal.ProofGatedAndCanarySuite.missing_outcome_breaks_compiles
#print axioms Anneal.ProofGatedAndCanarySuite.proof_gated_transfers_wellFormedOn
#print axioms Anneal.ProofGatedAndCanarySuite.proof_gated_transfers_specOn
#print axioms Anneal.ProofGatedAndCanarySuite.strictPolicy_forbids_omitted_proofs
#print axioms Anneal.ProofGatedAndCanarySuite.gated_pipeline_soundness
#print axioms Anneal.ProofGatedAndCanarySuite.currentX86Model_fails_BoundaryCanarySuite
#print axioms Anneal.ProofGatedAndCanarySuite.instBoundaryCanarySuiteFixedX86Model
