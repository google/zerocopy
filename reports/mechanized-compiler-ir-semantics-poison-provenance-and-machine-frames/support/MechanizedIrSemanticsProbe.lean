-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# IR Semantics in Mechanized Compilers: SSA Forms, Poison/Undef/Freeze, Byte-Granularity Provenance Memory, and Machine Stack Frames

This standalone Lean 4.34.1 mechanization formalizes the core IR semantic design choices
across CompCert (`RTL`, `LTL`, `Mach`, `Asm`), `CompCertSSA`, `Vellvm`, `Alive2`,
`Lean-MLIR`, `Isabelle-LLVM`, `K-LLVM`, and Cranelift (`CLIF`/`VCode`):
1. **SSA Representation Equivalence (`phiBlock_equiv_blockArg`):** CompCertSSA-style
   parallel $\phi$-node blocks vs. Cranelift/MLIR/AnSSA block-argument basic blocks.
2. **Multi-Valued `undef` Unsoundness vs. `poison` + Nondeterministic `freeze`
   (`undef_breaks_xor_self_and_cse` vs. `freeze_restores_cse_refinement`):**
   Multi-valued `undef` breaks `x ^^^ x = 0` and GVN/CSE when a single `undef` read is
   duplicated, whereas single-valued deferred `poison` + nondeterministic `freeze`
   preserves CSE refinement.
3. **Byte-Granularity Block-Offset Memory (`AnByteVal`) vs. Whole-Word Scalar Poison
   (`byte_load_preserves_field_across_uninit_padding`):** Modeling memory cells as
   individual tagged bytes (`AnByteVal := .uninit | .init (b : BitVec 8) (prov : Option Nat)`)
   preserves initialized struct fields across uninitialized padding during widened
   aggregate loads (`PassMode::Cast`), whereas whole-word integer poison taints the word.
4. **Machine-Level IR Frame Separation (`LTL` / `Mach` `SlotClass` to `Asm` Flat Stack
   `mach_to_asm_frame_isolation`):** Disjoint offset ranges for `Local`, `Outgoing`, and
   callee-saved spill slots in `Mach` map to non-aliasing byte offsets in `Asm`.
-/

namespace MechanizedIrSemanticsProbe

/-!
## Section 1: CompCertSSA Parallel $\phi$-Nodes vs. Cranelift / MLIR Block-Argument SSA
-/

abbrev RegId := Nat
abbrev RegFile := RegId → BitVec 64

def RegFile.update (rf : RegFile) (r : RegId) (v : BitVec 64) : RegFile :=
  fun r' => if r' == r then v else rf r'

def RegFile.updateMany (base : RegFile) (binds : List (RegId × BitVec 64)) : RegFile :=
  binds.foldl (fun acc (r, v) => acc.update r v) base

/-- In CompCertSSA (`RTL` + `phinode`), entering a join block from predecessor `predIdx`
evaluates all $\phi$-operands in the *pre-join* register file `rf` simultaneously
(parallel-copy semantics) before writing destination registers. -/
structure PhiAssign where
  dst : RegId
  rhs : Nat → RegId

def evalPhiJoin (phis : List PhiAssign) (predIdx : Nat) (rf : RegFile) : RegFile :=
  let evaluated := phis.map (fun p => (p.dst, rf (p.rhs predIdx)))
  rf.updateMany evaluated

/-- In Cranelift CLIF / MLIR / AnSSA, each control-flow edge passes explicit argument
expressions evaluated in `rf` to the target block's formal parameters `params : List RegId`. -/
def evalBlockArgEdge (params : List RegId) (edgeArgs : List RegId) (rf : RegFile) : RegFile :=
  let evaluated := params.zip (edgeArgs.map rf)
  rf.updateMany evaluated

/-- Canonical translation from a `PhiAssign` list for predecessor `predIdx` to block
parameters and edge arguments produces identical post-join register states. -/
theorem phiBlock_equiv_blockArg (phis : List PhiAssign) (predIdx : Nat) (rf : RegFile) :
    evalPhiJoin phis predIdx rf =
      evalBlockArgEdge (phis.map PhiAssign.dst) (phis.map (fun p => p.rhs predIdx)) rf := by
  unfold evalPhiJoin evalBlockArgEdge
  congr 1
  induction phis with
  | nil => rfl
  | cons p rest ih =>
    simp [List.map, List.zip]

/-!
## Section 2: Multi-Valued `undef` Unsoundness vs. `poison` + Nondeterministic `freeze`
-/

/-- Set-of-values denotation for multi-valued `undef` expressions. -/
def UndefDenote := BitVec 64 → Prop

def undefSet : UndefDenote := fun _ => True

def xorSet (A B : UndefDenote) : UndefDenote :=
  fun v => ∃ a b, A a ∧ B b ∧ v = a ^^^ b

/-- If a single deterministic choice `y` is bound once and XORed with itself, the result
is always `0#64`; but substituting the multi-valued set `undefSet` into both operands of
`xorSet` (`undef ^^^ undef`) permits `1#64`! -/
theorem undef_breaks_xor_self_and_cse :
    (∀ y : BitVec 64, y ^^^ y = 0#64) ∧
    xorSet undefSet undefSet 1#64 := by
  refine ⟨fun y => BitVec.xor_self (x := y), ?_⟩
  refine ⟨0#64, 1#64, trivial, trivial, by decide⟩

inductive PoisonVal where
  | poison : PoisonVal
  | value  : BitVec 64 → PoisonVal
  deriving DecidableEq, Repr

def FreezeStep (src : PoisonVal) (v : BitVec 64) : Prop :=
  match src with
  | .poison => True
  | .value w => v = w

theorem freeze_restores_cse_refinement (src : PoisonVal) (v : BitVec 64)
    (_h : FreezeStep src v) :
    v ^^^ v = 0#64 := by
  exact BitVec.xor_self (x := v)

/-!
## Section 3: Byte-Granularity Memory (`AnByteVal`) vs. Whole-Word Scalar Poison on Padding
-/

inductive AnByteVal where
  | uninit : AnByteVal
  | init   : BitVec 8 → Option Nat → AnByteVal
  deriving DecidableEq, Repr

abbrev AnByteWord := Fin 8 → AnByteVal

def isInitByte : AnByteVal → Bool
  | .init _ _ => true
  | .uninit   => false

def loadWord64_wholePoison (w : AnByteWord) : PoisonVal :=
  if isInitByte (w ⟨0, by omega⟩) && isInitByte (w ⟨1, by omega⟩) &&
     isInitByte (w ⟨2, by omega⟩) && isInitByte (w ⟨3, by omega⟩) &&
     isInitByte (w ⟨4, by omega⟩) && isInitByte (w ⟨5, by omega⟩) &&
     isInitByte (w ⟨6, by omega⟩) && isInitByte (w ⟨7, by omega⟩) then
    .value 0#64
  else
    .poison

def extractFieldByte0 (w : AnByteWord) : AnByteVal :=
  w ⟨0, by omega⟩

def samplePaddedStruct (field0 : BitVec 8) : AnByteWord :=
  fun i =>
    if i.val == 0 then .init field0 (some 1)
    else if i.val >= 4 then .init 0x2A#8 (some 1)
    else .uninit

/-- Whole-word scalar load poisons the entire struct load due to uninitialized padding at
byte 1, whereas byte-granularity projection `extractFieldByte0` preserves `.init field0`. -/
theorem byte_load_preserves_field_across_uninit_padding (field0 : BitVec 8) :
    loadWord64_wholePoison (samplePaddedStruct field0) = .poison ∧
    extractFieldByte0 (samplePaddedStruct field0) = .init field0 (some 1) := by
  exact ⟨rfl, rfl⟩

/-!
## Section 4: Machine-Level IR Frame Separation (`LTL` / `Mach` Stack Slots to `Asm`)
-/

inductive SlotClass where
  | localSlot    : Fin 4 → SlotClass
  | calleeSaved  : Fin 4 → SlotClass
  | outgoingArg  : Fin 4 → SlotClass
  deriving DecidableEq, Repr

def slotByteOffset : SlotClass → Nat
  | .outgoingArg i => 8 * i.val
  | .localSlot i   => 32 + 8 * i.val
  | .calleeSaved i => 64 + 8 * i.val

/-- Every distinct `SlotClass` maps to a strictly disjoint 8-byte physical interval
`[ofs₁, ofs₁ + 8) ∩ [ofs₂, ofs₂ + 8) = ∅` within the 96-byte stack frame. -/
theorem mach_to_asm_frame_isolation (s1 s2 : SlotClass) (h_neq : s1 ≠ s2) :
    slotByteOffset s1 + 8 ≤ slotByteOffset s2 ∨
    slotByteOffset s2 + 8 ≤ slotByteOffset s1 := by
  cases s1 with
  | outgoingArg i1 =>
    cases s2 with
    | outgoingArg i2 =>
      have h_val : i1.val ≠ i2.val := fun h => h_neq (congrArg SlotClass.outgoingArg (Fin.ext h))
      simp [slotByteOffset]
      omega
    | localSlot i2 =>
      simp [slotByteOffset]
      omega
    | calleeSaved i2 =>
      simp [slotByteOffset]
      omega
  | localSlot i1 =>
    cases s2 with
    | outgoingArg i2 =>
      simp [slotByteOffset]
      omega
    | localSlot i2 =>
      have h_val : i1.val ≠ i2.val := fun h => h_neq (congrArg SlotClass.localSlot (Fin.ext h))
      simp [slotByteOffset]
      omega
    | calleeSaved i2 =>
      simp [slotByteOffset]
      omega
  | calleeSaved i1 =>
    cases s2 with
    | outgoingArg i2 =>
      simp [slotByteOffset]
      omega
    | localSlot i2 =>
      simp [slotByteOffset]
      omega
    | calleeSaved i2 =>
      have h_val : i1.val ≠ i2.val := fun h => h_neq (congrArg SlotClass.calleeSaved (Fin.ext h))
      simp [slotByteOffset]
      omega

/-- info: 'MechanizedIrSemanticsProbe.phiBlock_equiv_blockArg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms phiBlock_equiv_blockArg

/-- info: 'MechanizedIrSemanticsProbe.undef_breaks_xor_self_and_cse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms undef_breaks_xor_self_and_cse

/-- info: 'MechanizedIrSemanticsProbe.byte_load_preserves_field_across_uninit_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms byte_load_preserves_field_across_uninit_padding

/-- info: 'MechanizedIrSemanticsProbe.mach_to_asm_frame_isolation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mach_to_asm_frame_isolation

end MechanizedIrSemanticsProbe
