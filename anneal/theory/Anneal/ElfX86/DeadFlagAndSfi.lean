-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Anneal.ElfX86.PrefixDecode

public section
namespace Anneal.ElfX86

/-!
# Backward `DeadFlagCollapse` & Explicit `StraightLineLeafAbiCert`
(`Anneal.ElfX86.DeadFlagAndSfi`)

Pure Pass-1 (`0` `._unsafe_rec`, `[]` axioms) flag-liveness collapse and
straight-line ABI/SFI verification over decoded `Anneal.ElfX86` instruction
streams:

1. **Backward `DeadFlagCollapse` (`FlagMask`, `RFlags`, `FlagsAgreeOn`,
   `backwardLiveFlags`):** Tracks architectural defined vs. demonic undefined
   status-flag writes across `XOR`/`AND`/`OR`/`TEST`, `IMUL`, `BSF`, `TZCNT`,
   and exact Intel SDM shift-count masking (`cnt % 64` for 64-bit, `cnt % 32`
   for 16/32-bit; `maskedCnt == 0` preserves all flags; `maskedCnt >= 16` on
   16-bit leaves `CF`/`AF`/`OF` undefined; `maskedCnt == 1` defines `OF`),
   rejects live-out undefined flags fail-closed, and proves
   `backwardLiveFlags_sound`.
2. **Explicit `StraightLineLeafAbiCert` (two-tier store-base discipline):**
   - **Fixed entry-base tier (`checkStraightLineAbiSfiArgStores` /
     `checkStraightLineAbiSfiFixedBases`):** rejects ANY memory store with an
     index register AND rejects the stream if ANY register in
     `allowedStoreBases` is written by any instruction, guaranteeing every
     store targets `[base + disp]` with `base` holding its unmodified entry
     value (`StraightLineLeafAbiFixedBasesCert`).
   - **Base-name-only tier (`checkStraightLineAbiSfiStoreBaseNamesOnly`):**
     syntactic base-register-name check for row-strided kernels that compute
     derived row pointers (e.g., via `lea`) or use scaled indices; full
     address/bounds confinement for derived pointers is a separate semantic
     layer (`StraightLineLeafAbiStoreBaseNamesOnlyCert`).
   Both tiers certify zero callee-saved GPR writes (`rbx, rbp, r12..r15`),
   zero `rsp`/`rbp` stack or frame touches, zero forbidden traps/syscalls/
   branches/`FS:`/`GS:`/`0x67`, and clean `vzeroupper` before a single `ret`.
-/

/-! ## 1. Six-Flag `RFlags`, `FlagMask`, and `FlagsAgreeOn` -/

/-- Six architectural status flags in x86-64 `RFLAGS`. -/
structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false

/-- Per-step demonic choice for architecturally undefined status flags. -/
abbrev UndefFlags := RFlags

/-- Liveness bitmask over `{CF, PF, AF, ZF, SF, OF}`. -/
abbrev FlagMask := RFlags

@[expose] def RFlags.beq (a b : RFlags) : Bool :=
  (a.cf == b.cf) && (a.pf == b.pf) && (a.af == b.af) &&
  (a.zf == b.zf) && (a.sf == b.sf) && (a.of == b.of)

/-- Empty liveness mask (all flags dead, e.g., volatile `RFLAGS` at `ret`). -/
@[expose] def FlagMask.dead : FlagMask :=
  ⟨false, false, false, false, false, false⟩

/-- Full liveness mask (all six status flags live). -/
@[expose] def FlagMask.all : FlagMask :=
  ⟨true, true, true, true, true, true⟩

/-- Bitwise union of two `FlagMask`s. -/
@[expose] def FlagMask.orMask (a b : FlagMask) : FlagMask :=
  ⟨a.cf || b.cf, a.pf || b.pf, a.af || b.af,
   a.zf || b.zf, a.sf || b.sf, a.of || b.of⟩

/-- Bitwise difference `live \ killed`. -/
@[expose] def FlagMask.andNot (live killed : FlagMask) : FlagMask :=
  ⟨live.cf && !killed.cf, live.pf && !killed.pf, live.af && !killed.af,
   live.zf && !killed.zf, live.sf && !killed.sf, live.of && !killed.of⟩

/-- True iff no flag bit is set in both `a` and `b`. -/
@[expose] def flagMaskDisjoint (a b : FlagMask) : Bool :=
  !(a.cf && b.cf) && !(a.pf && b.pf) && !(a.af && b.af) &&
  !(a.zf && b.zf) && !(a.sf && b.sf) && !(a.of && b.of)

/-- Agreement of two `RFlags` records on all bits live in `m`. -/
@[expose] def FlagsAgreeOn (m : FlagMask) (f1 f2 : RFlags) : Prop :=
  (m.cf = true → f1.cf = f2.cf) ∧
  (m.pf = true → f1.pf = f2.pf) ∧
  (m.af = true → f1.af = f2.af) ∧
  (m.zf = true → f1.zf = f2.zf) ∧
  (m.sf = true → f1.sf = f2.sf) ∧
  (m.of = true → f1.of = f2.of)

/-- Every pair of flag states agrees on the empty `FlagMask.dead`. -/
theorem flagsAgreeOn_dead (f1 f2 : RFlags) :
    FlagsAgreeOn FlagMask.dead f1 f2 :=
  ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
   fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
   fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

/-- Reflexivity of `FlagsAgreeOn`. -/
theorem flagsAgreeOn_refl (m : FlagMask) (f : RFlags) :
    FlagsAgreeOn m f f :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl,
   fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Symmetry of `FlagsAgreeOn`. -/
theorem flagsAgreeOn_symm {m : FlagMask} {f1 f2 : RFlags}
    (h : FlagsAgreeOn m f1 f2) : FlagsAgreeOn m f2 f1 :=
  ⟨fun hc => (h.1 hc).symm, fun hc => (h.2.1 hc).symm,
   fun hc => (h.2.2.1 hc).symm, fun hc => (h.2.2.2.1 hc).symm,
   fun hc => (h.2.2.2.2.1 hc).symm, fun hc => (h.2.2.2.2.2 hc).symm⟩

/-- Transitivity of `FlagsAgreeOn`. -/
theorem flagsAgreeOn_trans {m : FlagMask} {f1 f2 f3 : RFlags}
    (h12 : FlagsAgreeOn m f1 f2) (h23 : FlagsAgreeOn m f2 f3) :
    FlagsAgreeOn m f1 f3 :=
  ⟨fun hc => Eq.trans (h12.1 hc) (h23.1 hc),
   fun hc => Eq.trans (h12.2.1 hc) (h23.2.1 hc),
   fun hc => Eq.trans (h12.2.2.1 hc) (h23.2.2.1 hc),
   fun hc => Eq.trans (h12.2.2.2.1 hc) (h23.2.2.2.1 hc),
   fun hc => Eq.trans (h12.2.2.2.2.1 hc) (h23.2.2.2.2.1 hc),
   fun hc => Eq.trans (h12.2.2.2.2.2 hc) (h23.2.2.2.2.2 hc)⟩

/-! ## 2. Per-Instruction Flag Effects & Backward `DeadFlagCollapse` -/

/-- Architectural status-flag read, defined-write, and undefined-write masks
for a single instruction. -/
structure InsnFlagEffect where
  reads : FlagMask
  definedWrites : FlagMask
  undefWrites : FlagMask

@[expose] def aluFlagEffect (op : GpAluOp) : InsnFlagEffect :=
  match op with
  | .add | .sub | .cmp =>
    ⟨FlagMask.dead, FlagMask.all, FlagMask.dead⟩
  | .adc | .sbb =>
    ⟨⟨true, false, false, false, false, false⟩, FlagMask.all, FlagMask.dead⟩
  | .xor | .and | .or | .test =>
    ⟨FlagMask.dead,
     ⟨true, true, false, true, true, true⟩,
     ⟨false, false, true, false, false, false⟩⟩

/-- Exact Intel SDM shift-count masked status-flag effect (`cnt % 64` for
64-bit, `cnt % 32` for 16/32-bit; `0` preserves all flags; 16-bit `≥ 16`
leaves `CF`/`AF`/`OF` undefined; `1` defines `OF`). -/
@[expose] def shiftFlagEffect (sz : OpSize) (cnt : Nat) : InsnFlagEffect :=
  let maskedCnt :=
    if OpSize.beq sz .s64 then Nat.mod cnt 64 else Nat.mod cnt 32
  if Nat.beq maskedCnt 0 then
    ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  else if OpSize.beq sz .s16 && Nat.ble 16 maskedCnt then
    ⟨FlagMask.dead,
     ⟨false, true, false, true, true, false⟩,
     ⟨true, false, true, false, false, true⟩⟩
  else if Nat.beq maskedCnt 1 then
    ⟨FlagMask.dead,
     ⟨true, true, false, true, true, true⟩,
     ⟨false, false, true, false, false, false⟩⟩
  else
    ⟨FlagMask.dead,
     ⟨true, true, false, true, true, false⟩,
     ⟨false, false, true, false, false, true⟩⟩

/-- Architectural status-flag summary for `DecodedInsn`. Matches every
`DecodedInsn` constructor explicitly with NO wildcard fallback so any future
constructor must be classified here (`syscall`/`sysenter`/`intImm`/`int3`/`ud2`
read all 6 status flags via `R11 ← RFLAGS` or interrupt/exception stack frames
and leave all 6 undefined on return; `callRel`/`callInd` leave all 6 undefined
under the System V ABI). -/
@[expose] def insnFlagEffect (ins : DecodedInsn) : InsnFlagEffect :=
  match ins with
  | .vbin _ _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vshift _ _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vload _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vmovhps _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vstore _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vpmovzxwd _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vperm2i128 _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vinserti128 _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vextracti128 _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vpermq _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vpshufd _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vpblendd _ _ _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .vzeroupper => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .lea _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .movsxd _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .movRegRm _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .movRmReg _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .movImm _ _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .aluRmReg _ _ op _ _ => aluFlagEffect op
  | .aluRegRm _ op _ _ => aluFlagEffect op
  | .aluRmImm _ _ op _ _ => aluFlagEffect op
  | .shiftRmImm sz _ _ cnt => shiftFlagEffect sz cnt
  | .imulRegRm _ _ _ =>
    -- Intel SDM: IMUL defines CF and OF; PF, AF, ZF, SF are undefined.
    ⟨FlagMask.dead,
     ⟨true, false, false, false, false, true⟩,
     ⟨false, true, true, true, true, false⟩⟩
  | .bsf _ _ _ =>
    -- Intel SDM: BSF defines ZF; CF, PF, AF, SF, OF are undefined.
    ⟨FlagMask.dead,
     ⟨false, false, false, true, false, false⟩,
     ⟨true, true, true, false, true, true⟩⟩
  | .tzcnt _ _ _ =>
    -- Intel SDM: TZCNT defines CF and ZF; PF, AF, SF, OF are undefined.
    ⟨FlagMask.dead,
     ⟨true, false, false, true, false, false⟩,
     ⟨false, true, true, false, true, true⟩⟩
  | .popcnt _ _ _ =>
    -- Intel SDM: POPCNT defines ZF and zeroes CF, PF, AF, SF, OF.
    ⟨FlagMask.dead, FlagMask.all, FlagMask.dead⟩
  | .lzcnt _ _ _ =>
    -- Intel SDM: LZCNT defines CF and ZF; PF, AF, SF, OF are undefined.
    ⟨FlagMask.dead,
     ⟨true, false, false, true, false, false⟩,
     ⟨false, true, true, false, true, true⟩⟩
  | .div _ _ _ _ =>
    -- Intel SDM: DIV/IDIV read no status flags; all 6 status flags are
    -- undefined.
    ⟨FlagMask.dead, FlagMask.dead, FlagMask.all⟩
  | .xchgAx _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .pushReg _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .popReg _ _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .endbr64 => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .nop => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .ret => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .syscall => ⟨FlagMask.all, FlagMask.dead, FlagMask.all⟩
  | .sysenter => ⟨FlagMask.all, FlagMask.dead, FlagMask.all⟩
  | .intImm _ => ⟨FlagMask.all, FlagMask.dead, FlagMask.all⟩
  | .int3 => ⟨FlagMask.all, FlagMask.dead, FlagMask.all⟩
  | .ud2 => ⟨FlagMask.all, FlagMask.dead, FlagMask.all⟩
  | .jmpRel _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .callRel _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.all⟩
  | .jmpInd _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.dead⟩
  | .callInd _ => ⟨FlagMask.dead, FlagMask.dead, FlagMask.all⟩

/-- Single-bit flag update: undefined takes demonic `nd`, defined takes
`det`, untouched preserves `old`. -/
@[expose] def updFlagBit (defW undefW det old nd : Bool) : Bool :=
  if undefW then nd else if defW then det else old

/-- Demonic one-step status-flag transition. -/
@[expose] def stepFlagEval (eff : InsnFlagEffect) (det old nd : RFlags) :
    RFlags :=
  ⟨updFlagBit eff.definedWrites.cf eff.undefWrites.cf det.cf old.cf nd.cf,
   updFlagBit eff.definedWrites.pf eff.undefWrites.pf det.pf old.pf nd.pf,
   updFlagBit eff.definedWrites.af eff.undefWrites.af det.af old.af nd.af,
   updFlagBit eff.definedWrites.zf eff.undefWrites.zf det.zf old.zf nd.zf,
   updFlagBit eff.definedWrites.sf eff.undefWrites.sf det.sf old.sf nd.sf,
   updFlagBit eff.definedWrites.of eff.undefWrites.of det.of old.of nd.of⟩

/-- Deterministic collapsed one-step transition (substituting `false` for all
undefined flags). -/
@[expose] def stepFlagDet (eff : InsnFlagEffect) (det old : RFlags) :
    RFlags :=
  stepFlagEval eff det old FlagMask.dead

/-- Single-instruction backward flag-liveness step: fails closed (`none`) if
any live-out flag is written as architecturally undefined. -/
@[expose] def backwardLiveFlagsStep (eff : InsnFlagEffect)
    (liveOut : FlagMask) : Option FlagMask :=
  if flagMaskDisjoint liveOut eff.undefWrites then
    let killed := FlagMask.orMask eff.definedWrites eff.undefWrites
    some (FlagMask.orMask eff.reads (FlagMask.andNot liveOut killed))
  else none

/-- Backward flag-liveness pass over an instruction stream from `liveExit`
(implemented via `List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def backwardLiveFlags (liveExit : FlagMask)
    (insns : List DecodedInsn) : Option FlagMask :=
  List.foldr
    (fun ins acc =>
      match acc with
      | none => none
      | some liveOut => backwardLiveFlagsStep (insnFlagEffect ins) liveOut)
    (some liveExit) insns

/-- A single flag-reading execution step: `detFn` computes the instruction's
defined-flag output as a function of the pre-step `RFlags` depending only on
`(insnFlagEffect ins).reads`, and `nd` supplies arbitrary demonic values for
undefined flag writes. -/
structure FlagStep where
  ins : DecodedInsn
  detFn : RFlags → RFlags
  nd : UndefFlags
  respectsReads : ∀ a b,
    FlagsAgreeOn (insnFlagEffect ins).reads a b → detFn a = detFn b

/-- Execute demonic flag-reading transitions over `trace`. -/
@[expose] def evalFlagTraceDemonic (init : RFlags)
    (trace : List FlagStep) : RFlags :=
  List.foldl
    (fun fl step =>
      stepFlagEval (insnFlagEffect step.ins) (step.detFn fl) fl step.nd)
    init trace

/-- Execute deterministic collapsed flag-reading transitions over `trace`
(ignoring every demonic `UndefFlags` input). -/
@[expose] def evalFlagTraceDet (init : RFlags)
    (trace : List FlagStep) : RFlags :=
  List.foldl
    (fun fl step =>
      stepFlagDet (insnFlagEffect step.ins) (step.detFn fl) fl)
    init trace

/-- Every step in `trace` observes identical values on
`(insnFlagEffect step.ins).reads` between demonic execution from `f1` and
deterministic collapsed execution from `f2` (and hence computes identical
`step.detFn` outputs at every step). -/
inductive TraceStepReadsAgree : RFlags → RFlags → List FlagStep → Prop where
  | nil (f1 f2 : RFlags) : TraceStepReadsAgree f1 f2 []
  | cons (f1 f2 : RFlags) (hd : FlagStep) (tl : List FlagStep)
      (hRead : FlagsAgreeOn (insnFlagEffect hd.ins).reads f1 f2)
      (hTl : TraceStepReadsAgree
        (stepFlagEval (insnFlagEffect hd.ins) (hd.detFn f1) f1 hd.nd)
        (stepFlagDet (insnFlagEffect hd.ins) (hd.detFn f2) f2)
        tl) :
      TraceStepReadsAgree f1 f2 (hd :: tl)

private theorem sfiBandLeft {a b : Bool} (h : (a && b) = true) :
    a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

private theorem sfiBandRight {a b : Bool} (h : (a && b) = true) :
    b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

private theorem readBit_agree (readBit restBit f1 f2 : Bool)
    (hAgreeIn : (readBit || restBit) = true → f1 = f2)
    (hRead : readBit = true) : f1 = f2 := by
  subst hRead
  exact hAgreeIn rfl

private theorem updFlagBit_agree
    (liveOut readBit defW undefW det f1 f2 nd : Bool)
    (hDisj : (!(liveOut && undefW)) = true)
    (hAgreeIn : (readBit || (liveOut && !(defW || undefW))) = true → f1 = f2)
    (hLive : liveOut = true) :
    updFlagBit defW undefW det f1 nd =
      updFlagBit defW undefW det f2 false := by
  subst hLive
  cases undefW with
  | true => exact Bool.noConfusion hDisj
  | false =>
    dsimp only [updFlagBit]
    cases defW with
    | true => rfl
    | false =>
      apply hAgreeIn
      cases readBit <;> rfl

/-- Single-step soundness of backward `DeadFlagCollapse` (`[]` axioms): any
accepted step guarantees (1) pre-state agreement on `eff.reads` (hence equal
flag-reading outputs `detFn f1 = detFn f2`), and (2) post-state agreement on
`liveOut` between arbitrary demonic `nd` and deterministic collapsed execution.
-/
theorem stepFlagEval_deadFlagCollapse_sound (eff : InsnFlagEffect)
    (liveOut liveIn : FlagMask) (detFn : RFlags → RFlags)
    (hResp : ∀ a b, FlagsAgreeOn eff.reads a b → detFn a = detFn b)
    (f1 f2 nd : RFlags)
    (hStep : backwardLiveFlagsStep eff liveOut = some liveIn)
    (hIn : FlagsAgreeOn liveIn f1 f2) :
    FlagsAgreeOn eff.reads f1 f2 ∧
    FlagsAgreeOn liveOut (stepFlagEval eff (detFn f1) f1 nd)
      (stepFlagDet eff (detFn f2) f2) := by
  dsimp only [backwardLiveFlagsStep] at hStep
  cases hD : flagMaskDisjoint liveOut eff.undefWrites with
  | false =>
    rw [hD] at hStep
    nomatch hStep
  | true =>
    rw [hD] at hStep
    injection hStep with hEq
    subst hEq
    have hReads : FlagsAgreeOn eff.reads f1 f2 := ⟨
      readBit_agree eff.reads.cf
        (liveOut.cf && !(eff.definedWrites.cf || eff.undefWrites.cf))
        f1.cf f2.cf hIn.1,
      readBit_agree eff.reads.pf
        (liveOut.pf && !(eff.definedWrites.pf || eff.undefWrites.pf))
        f1.pf f2.pf hIn.2.1,
      readBit_agree eff.reads.af
        (liveOut.af && !(eff.definedWrites.af || eff.undefWrites.af))
        f1.af f2.af hIn.2.2.1,
      readBit_agree eff.reads.zf
        (liveOut.zf && !(eff.definedWrites.zf || eff.undefWrites.zf))
        f1.zf f2.zf hIn.2.2.2.1,
      readBit_agree eff.reads.sf
        (liveOut.sf && !(eff.definedWrites.sf || eff.undefWrites.sf))
        f1.sf f2.sf hIn.2.2.2.2.1,
      readBit_agree eff.reads.of
        (liveOut.of && !(eff.definedWrites.of || eff.undefWrites.of))
        f1.of f2.of hIn.2.2.2.2.2⟩
    have hDetEq : detFn f1 = detFn f2 := hResp f1 f2 hReads
    rw [hDetEq]
    dsimp only [flagMaskDisjoint] at hD
    have dOf := sfiBandRight hD
    have d1 := sfiBandLeft hD
    have dSf := sfiBandRight d1
    have d2 := sfiBandLeft d1
    have dZf := sfiBandRight d2
    have d3 := sfiBandLeft d2
    have dAf := sfiBandRight d3
    have d4 := sfiBandLeft d3
    have dPf := sfiBandRight d4
    have dCf := sfiBandLeft d4
    exact ⟨hReads, ⟨
      updFlagBit_agree liveOut.cf eff.reads.cf eff.definedWrites.cf
        eff.undefWrites.cf (detFn f2).cf f1.cf f2.cf nd.cf dCf hIn.1,
      updFlagBit_agree liveOut.pf eff.reads.pf eff.definedWrites.pf
        eff.undefWrites.pf (detFn f2).pf f1.pf f2.pf nd.pf dPf hIn.2.1,
      updFlagBit_agree liveOut.af eff.reads.af eff.definedWrites.af
        eff.undefWrites.af (detFn f2).af f1.af f2.af nd.af dAf hIn.2.2.1,
      updFlagBit_agree liveOut.zf eff.reads.zf eff.definedWrites.zf
        eff.undefWrites.zf (detFn f2).zf f1.zf f2.zf nd.zf dZf hIn.2.2.2.1,
      updFlagBit_agree liveOut.sf eff.reads.sf eff.definedWrites.sf
        eff.undefWrites.sf (detFn f2).sf f1.sf f2.sf nd.sf dSf hIn.2.2.2.2.1,
      updFlagBit_agree liveOut.of eff.reads.of eff.definedWrites.of
        eff.undefWrites.of (detFn f2).of f1.of f2.of nd.of dOf
        hIn.2.2.2.2.2⟩⟩

/-- Multi-step trace soundness of `backwardLiveFlags` (`[]` axioms): if
`backwardLiveFlags liveExit (trace.map FlagStep.ins) = some liveIn`, then
demonic flag-reading execution agrees with deterministic collapsed execution
(1) on every intermediate step's `(insnFlagEffect step.ins).reads`
(`TraceStepReadsAgree`), AND (2) on `liveExit` at trace completion! -/
theorem backwardLiveFlags_sound
    (trace : List FlagStep)
    (liveExit liveIn : FlagMask) (f1 f2 : RFlags)
    (hLive :
      backwardLiveFlags liveExit (trace.map FlagStep.ins) = some liveIn)
    (hIn : FlagsAgreeOn liveIn f1 f2) :
    TraceStepReadsAgree f1 f2 trace ∧
    FlagsAgreeOn liveExit (evalFlagTraceDemonic f1 trace)
      (evalFlagTraceDet f2 trace) := by
  revert liveIn f1 f2
  induction trace with
  | nil =>
    intro liveIn f1 f2 hLive hIn
    dsimp only [List.map, backwardLiveFlags, List.foldr] at hLive
    injection hLive with hEq
    subst hEq
    exact ⟨TraceStepReadsAgree.nil f1 f2, hIn⟩
  | cons hd tl ih =>
    intro liveIn f1 f2 hLive hIn
    dsimp only [List.map, backwardLiveFlags, List.foldr] at hLive
    cases hTail : backwardLiveFlags liveExit (tl.map FlagStep.ins) with
    | none =>
      dsimp only [backwardLiveFlags] at hTail
      rw [hTail] at hLive
      nomatch hLive
    | some liveMid =>
      dsimp only [backwardLiveFlags] at hTail
      rw [hTail] at hLive
      have hStep := stepFlagEval_deadFlagCollapse_sound
        (insnFlagEffect hd.ins) liveMid liveIn hd.detFn hd.respectsReads
        f1 f2 hd.nd hLive hIn
      have hRest := ih liveMid
        (stepFlagEval (insnFlagEffect hd.ins) (hd.detFn f1) f1 hd.nd)
        (stepFlagDet (insnFlagEffect hd.ins) (hd.detFn f2) f2)
        hTail hStep.2
      exact ⟨TraceStepReadsAgree.cons f1 f2 hd tl hStep.1 hRest.1, hRest.2⟩

/-- Non-trivial corollary for System V Class-1 volatile-`RFLAGS` `ret` exit
(`liveExit = FlagMask.dead`): even though exit flags are dead, EVERY
intermediate flag-reading instruction in `trace` (e.g., `adc`/`sbb`) observes
identical read-flag values under arbitrary demonic `UndefFlags` and under
deterministic collapsed execution (`TraceStepReadsAgree`). -/
theorem backwardLiveFlags_volatileRet_reads_agree
    (trace : List FlagStep)
    (liveIn : FlagMask) (f1 f2 : RFlags)
    (hLive :
      backwardLiveFlags FlagMask.dead (trace.map FlagStep.ins) = some liveIn)
    (hIn : FlagsAgreeOn liveIn f1 f2) :
    TraceStepReadsAgree f1 f2 trace :=
  (backwardLiveFlags_sound trace FlagMask.dead liveIn f1 f2 hLive hIn).1

/-! ## 3. Explicit `StraightLineLeafAbiCert` (`checkStraightLineAbiSfi`) -/

/-- True iff `m` uses an `FS:`/`GS:` segment override. -/
@[expose] def memAddrHasSegEscape (m : MemAddr) : Bool :=
  match m with
  | .gpr seg _ _ _ _ => seg.isSome
  | .ripRel seg _ _ _ _ => seg.isSome

/-- True iff `m` references `rsp` or `rbp` as base or index register. -/
@[expose] def memAddrTouchesStackOrFrame (m : MemAddr) : Bool :=
  match m with
  | .gpr _ _ base idx _ =>
    let bTouch := match base with
      | some g => g.isStackOrFramePtr
      | none => false
    let iTouch := match idx with
      | some p => p.1.isStackOrFramePtr
      | none => false
    bTouch || iTouch
  | .ripRel _ _ _ _ _ => false

/-- True iff `m` uses a `0x67` 32-bit address-size override. -/
@[expose] def memAddrHasAddr32 (m : MemAddr) : Bool :=
  match m with
  | .gpr _ a32 _ _ _ => a32
  | .ripRel _ a32 _ _ _ => a32

/-- True iff `g` appears in `gs`. -/
@[expose] def gprInList (g : Gpr) (gs : List Gpr) : Bool :=
  listAny (fun x => Gpr.beq g x) gs

/-- True iff `m` is an un-escaped 64-bit GPR-based address whose base register
name lies in `allowedBases` (syntactic base-name check only; permits index
registers and does not prove address bounds). -/
@[expose] def memAddrBaseNameIn (allowedBases : List Gpr)
    (m : MemAddr) : Bool :=
  match m with
  | .gpr none false (some base) _ _ => gprInList base allowedBases
  | _ => false

/-- True iff `m` is an un-escaped 64-bit GPR-based address with NO index
register whose base register lies in `allowedBases`. -/
@[expose] def memAddrFixedBaseNoIndexIn (allowedBases : List Gpr)
    (m : MemAddr) : Bool :=
  match m with
  | .gpr none false (some base) none _ => gprInList base allowedBases
  | _ => false

/-- True iff `ins` is a forbidden syscall, interrupt, trap, or non-`ret`
control-flow instruction. -/
@[expose] def insnIsForbiddenControlOrTrap (ins : DecodedInsn) : Bool :=
  match ins with
  | .syscall | .sysenter | .intImm _ | .int3 | .ud2
  | .jmpRel _ | .callRel _ | .jmpInd _ | .callInd _ => true
  | _ => false

/-- All GPR destinations written by `ins`, including implicit architectural
writes (`xchgAx` writes `[.rax, dst]`; `syscall` clobbers `[.rcx, .r11]`;
`pushReg`, `callRel`, `callInd`, `ret`, `sysenter`, `intImm`, and `int3`
modify `[.rsp]`; `popReg dst` writes `[dst, .rsp]`; excludes pure
`cmp`/`test`). The wildcard-free `match` itself is the compile-time guard
ensuring any new `DecodedInsn` constructor must be classified here. -/
@[expose] def insnWritesGprs (ins : DecodedInsn) : List Gpr :=
  match ins with
  | .vbin _ _ _ _ _ => []
  | .vshift _ _ _ _ _ => []
  | .vload _ _ _ _ => []
  | .vmovhps _ _ _ => []
  | .vstore _ _ _ _ => []
  | .vpmovzxwd _ _ _ => []
  | .vperm2i128 _ _ _ _ => []
  | .vinserti128 _ _ _ _ => []
  | .vextracti128 _ _ _ => []
  | .vpermq _ _ _ => []
  | .vpshufd _ _ _ _ => []
  | .vpblendd _ _ _ _ _ => []
  | .vzeroupper => []
  | .lea _ dst _ => [dst]
  | .movsxd dst _ => [dst]
  | .movRegRm _ dst _ => [dst]
  | .movRmReg _ dst _ =>
    match dst with
    | .reg g => [g]
    | .mem _ => []
  | .movImm _ dst _ => [dst]
  | .aluRmReg _ _ op dst _ =>
    match op with
    | .cmp => []
    | .test => []
    | .add | .or | .adc | .sbb | .and | .sub | .xor =>
      match dst with
      | .reg g => [g]
      | .mem _ => []
  | .aluRegRm _ op dst _ =>
    match op with
    | .cmp => []
    | .test => []
    | .add | .or | .adc | .sbb | .and | .sub | .xor => [dst]
  | .aluRmImm _ _ op dst _ =>
    match op with
    | .cmp => []
    | .test => []
    | .add | .or | .adc | .sbb | .and | .sub | .xor =>
      match dst with
      | .reg g => [g]
      | .mem _ => []
  | .shiftRmImm _ _ dst _ =>
    match dst with
    | .reg g => [g]
    | .mem _ => []
  | .imulRegRm _ dst _ => [dst]
  | .bsf _ dst _ => [dst]
  | .tzcnt _ dst _ => [dst]
  | .popcnt _ dst _ => [dst]
  | .lzcnt _ dst _ => [dst]
  | .div _ isByte _ _ => if isByte then [.rax] else [.rax, .rdx]
  | .xchgAx _ dst => [.rax, dst]
  | .pushReg _ _ => [.rsp]
  | .popReg _ dst => [dst, .rsp]
  | .endbr64 => []
  | .nop => []
  | .ret => [.rsp]
  | .syscall => [.rcx, .r11]
  | .sysenter => [.rsp]
  | .intImm _ => [.rsp]
  | .int3 => [.rsp]
  | .ud2 => []
  | .jmpRel _ => []
  | .callRel _ => [.rsp]
  | .jmpInd _ => []
  | .callInd _ => [.rsp]

/-- Memory address written by `ins`, if `ins` performs a memory store (excludes
pure loads, `lea`, `cmp`, and `test`). -/
@[expose] def insnStoreAddr? (ins : DecodedInsn) : Option MemAddr :=
  match ins with
  | .vstore _ _ m _ => some m
  | .movRmReg _ (.mem m) _ => some m
  | .aluRmReg _ _ op (.mem m) _ =>
    match op with
    | .cmp | .test => none
    | _ => some m
  | .aluRmImm _ _ op (.mem m) _ =>
    match op with
    | .cmp | .test => none
    | _ => some m
  | .shiftRmImm _ _ (.mem m) _ => some m
  | _ => none

/-- True iff `ins` carries an `FS:`/`GS:` segment override on any memory
operand. -/
@[expose] def insnHasSegEscape (ins : DecodedInsn) : Bool :=
  match insnMemOperandWithSize? ins with
  | some (m, _) => memAddrHasSegEscape m
  | none => false

/-- True iff `ins` uses a `0x67` address-size override on any memory
operand. -/
@[expose] def insnHasAddr32 (ins : DecodedInsn) : Bool :=
  match insnMemOperandWithSize? ins with
  | some (m, _) => memAddrHasAddr32 m
  | none => false

/-- True iff `opnd` references `rsp` or `rbp` either directly or in a memory
address. -/
@[expose] def gpOpndTouchesStackOrFrame (opnd : GpOpnd) : Bool :=
  match opnd with
  | .reg g => g.isStackOrFramePtr
  | .mem m => memAddrTouchesStackOrFrame m

/-- True iff `ins` (other than terminal `ret`) mutates/accesses `rsp` or `rbp`
(`push`/`pop`/`call`/any `rsp` or `rbp` operand, including `[rbp+disp]`). -/
@[expose] def insnTouchesStackOrFrame (ins : DecodedInsn) : Bool :=
  match ins with
  | .pushReg _ _ | .popReg _ _ | .callRel _ | .callInd _ => true
  | .vbin _ _ _ _ (.mem m) | .vload _ _ _ m | .vmovhps _ _ m
  | .vstore _ _ m _ | .vpmovzxwd _ _ (.mem m) | .vperm2i128 _ _ (.mem m) _
  | .vinserti128 _ _ (.mem m) _ | .vpermq _ (.mem m) _
  | .vpshufd _ _ (.mem m) _ | .vpblendd _ _ _ (.mem m) _ =>
    memAddrTouchesStackOrFrame m
  | .lea _ dst m => dst.isStackOrFramePtr || memAddrTouchesStackOrFrame m
  | .movsxd dst src => dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .movRegRm _ dst src =>
    dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .movRmReg _ dst src =>
    gpOpndTouchesStackOrFrame dst || src.isStackOrFramePtr
  | .movImm _ dst _ => dst.isStackOrFramePtr
  | .aluRmReg _ _ _ dst src =>
    gpOpndTouchesStackOrFrame dst || src.isStackOrFramePtr
  | .aluRegRm _ _ dst src =>
    dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .aluRmImm _ _ _ dst _ => gpOpndTouchesStackOrFrame dst
  | .shiftRmImm _ _ dst _ => gpOpndTouchesStackOrFrame dst
  | .imulRegRm _ dst src =>
    dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .bsf _ dst src => dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .tzcnt _ dst src => dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .popcnt _ dst src => dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .lzcnt _ dst src => dst.isStackOrFramePtr || gpOpndTouchesStackOrFrame src
  | .div _ _ _ src => gpOpndTouchesStackOrFrame src
  | .xchgAx _ dst => dst.isStackOrFramePtr
  | .jmpInd target => gpOpndTouchesStackOrFrame target
  | _ => false

/-- True iff `ins` writes no callee-saved GPR. -/
@[expose] def insnPreservesCalleeSaved (ins : DecodedInsn) : Bool :=
  listAll (fun g => !g.isCalleeSaved) (insnWritesGprs ins)

/-- True iff `ins` does not write any register in `protectedBases`. -/
@[expose] def insnPreservesRegs (protectedBases : List Gpr)
    (ins : DecodedInsn) : Bool :=
  listAll (fun g => !gprInList g protectedBases) (insnWritesGprs ins)

/-- Syntactic store-base-name filter: true iff any memory store performed by
`ins` names a base register in `allowedStoreBases` (address/bounds confinement
for derived pointers or indices is a separate layer). -/
@[expose] def insnStoreBaseNameOnly (allowedStoreBases : List Gpr)
    (ins : DecodedInsn) : Bool :=
  match insnStoreAddr? ins with
  | none => true
  | some m => memAddrBaseNameIn allowedStoreBases m

/-- Strict fixed-base store filter: true iff any memory store performed by
`ins` uses NO index register and names a base register in `allowedStoreBases`.
-/
@[expose] def insnStoreFixedBaseNoIndex (allowedStoreBases : List Gpr)
    (ins : DecodedInsn) : Bool :=
  match insnStoreAddr? ins with
  | none => true
  | some m => memAddrFixedBaseNoIndexIn allowedStoreBases m

/-- True iff `m` uses base-less absolute addressing (`.gpr _ _ none _ _`,
e.g. SIB `[disp32]` or `[index*scale + disp32]`). -/
@[expose] def memAddrIsBaseless (m : MemAddr) : Bool :=
  match m with
  | .gpr _ _ none _ _ => true
  | .gpr _ _ (some _) _ _ => false
  | .ripRel _ _ _ _ _ => false

/-- True iff `ins` carries a base-less absolute memory operand. -/
@[expose] def insnHasBaselessMem (ins : DecodedInsn) : Bool :=
  match insnMemOperandWithSize? ins with
  | some (m, _) => memAddrIsBaseless m
  | none => false

/-- Per-instruction ABI & SFI gate (syntactic store-base-name-only tier). -/
@[expose] def insnStraightLineAbiSfiStoreBaseNamesOnlyOk
    (allowedStoreBases : List Gpr) (ins : DecodedInsn) : Bool :=
  !insnIsForbiddenControlOrTrap ins &&
  !insnHasSegEscape ins &&
  !insnHasAddr32 ins &&
  !insnHasBaselessMem ins &&
  !insnTouchesStackOrFrame ins &&
  insnPreservesCalleeSaved ins &&
  insnStoreBaseNameOnly allowedStoreBases ins

/-- Per-instruction ABI & SFI gate (strict fixed entry-base tier: rejects
indexed stores, base-less absolute memory operands, and any write to
`allowedStoreBases`). -/
@[expose] def insnStraightLineAbiSfiFixedBasesOk
    (allowedStoreBases : List Gpr) (ins : DecodedInsn) : Bool :=
  !insnIsForbiddenControlOrTrap ins &&
  !insnHasSegEscape ins &&
  !insnHasAddr32 ins &&
  !insnHasBaselessMem ins &&
  !insnTouchesStackOrFrame ins &&
  insnPreservesCalleeSaved ins &&
  insnPreservesRegs allowedStoreBases ins &&
  insnStoreFixedBaseNoIndex allowedStoreBases ins

/-- Decidable whole-function straight-line ABI & SFI verifier (base-name-only
store tier for row-strided kernels; address bounds are checked separately). -/
@[expose] def checkStraightLineAbiSfiStoreBaseNamesOnly
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn) : Bool :=
  listAll (insnStraightLineAbiSfiStoreBaseNamesOnlyOk allowedStoreBases)
    insns &&
  dirtyYmmClearedBeforeRet insns &&
  hasSingleTerminalRet insns

/-- Decidable whole-function straight-line ABI & SFI verifier (strict fixed
entry-base tier: rejects any store with an index register AND rejects the
stream if any `allowedStoreBases` register is written by any instruction). -/
@[expose] def checkStraightLineAbiSfiFixedBases
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn) : Bool :=
  listAll (insnStraightLineAbiSfiFixedBasesOk allowedStoreBases) insns &&
  dirtyYmmClearedBeforeRet insns &&
  hasSingleTerminalRet insns

/-- Strict System V pointer-arg fixed-base verifier (`[.rdi, .rsi]` never
written anywhere in the stream; zero indexed stores). -/
@[expose] def checkStraightLineAbiSfiArgStores
    (insns : List DecodedInsn) : Bool :=
  checkStraightLineAbiSfiFixedBases [.rdi, .rsi] insns

/-- Explicit kernel-checked straight-line leaf ABI certificate (base-name-only
store tier; full address/bounds confinement is a separate semantic layer). -/
structure StraightLineLeafAbiStoreBaseNamesOnlyCert
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn) : Prop where
  noCalleeSavedWrite : ∀ ins, ins ∈ insns →
    ∀ g, g ∈ insnWritesGprs ins → g.isCalleeSaved = false
  noStackOrFrameTouch : ∀ ins, ins ∈ insns →
    insnTouchesStackOrFrame ins = false
  storeBaseNamesOnly : ∀ ins, ins ∈ insns →
    ∀ m, insnStoreAddr? ins = some m →
      memAddrBaseNameIn allowedStoreBases m = true
  noForbiddenControlOrTrap : ∀ ins, ins ∈ insns →
    insnIsForbiddenControlOrTrap ins = false
  noSegEscape : ∀ ins, ins ∈ insns → insnHasSegEscape ins = false
  noAddr32 : ∀ ins, ins ∈ insns → insnHasAddr32 ins = false
  noBaselessMem : ∀ ins, ins ∈ insns → insnHasBaselessMem ins = false
  ymmCleanBeforeRet : dirtyYmmClearedBeforeRet insns = true
  singleTerminalRet : hasSingleTerminalRet insns = true

/-- Explicit kernel-checked straight-line leaf ABI certificate (strict fixed
entry-base tier: every allowed store base retains its entry value across the
entire stream and every store has `index = none`; signed `disp32` bounds are
proven separately). `storeBasesNeverWritten` relies on `insnWritesGprs`
covering every `DecodedInsn` constructor (including implicit GPR writes); the
wildcard-free `match` in `insnWritesGprs` enforces this at compile time. -/
structure StraightLineLeafAbiFixedBasesCert
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn) : Prop where
  noCalleeSavedWrite : ∀ ins, ins ∈ insns →
    ∀ g, g ∈ insnWritesGprs ins → g.isCalleeSaved = false
  storeBasesNeverWritten : ∀ ins, ins ∈ insns →
    ∀ g, g ∈ insnWritesGprs ins → gprInList g allowedStoreBases = false
  noStackOrFrameTouch : ∀ ins, ins ∈ insns →
    insnTouchesStackOrFrame ins = false
  storesFixedBaseNoIndex : ∀ ins, ins ∈ insns →
    ∀ m, insnStoreAddr? ins = some m →
      memAddrFixedBaseNoIndexIn allowedStoreBases m = true
  noForbiddenControlOrTrap : ∀ ins, ins ∈ insns →
    insnIsForbiddenControlOrTrap ins = false
  noSegEscape : ∀ ins, ins ∈ insns → insnHasSegEscape ins = false
  noAddr32 : ∀ ins, ins ∈ insns → insnHasAddr32 ins = false
  noBaselessMem : ∀ ins, ins ∈ insns → insnHasBaselessMem ins = false
  ymmCleanBeforeRet : dirtyYmmClearedBeforeRet insns = true
  singleTerminalRet : hasSingleTerminalRet insns = true

/-- Compatibility alias for `StraightLineLeafAbiFixedBasesCert`. -/
abbrev StraightLineLeafAbiCert := StraightLineLeafAbiFixedBasesCert

/-- Compatibility alias for `StraightLineLeafAbiFixedBasesCert`. -/
abbrev CalleeSavedAndZeroStackCert := StraightLineLeafAbiFixedBasesCert

private theorem listAll_mem {α : Type} (p : α → Bool) :
    ∀ (xs : List α), listAll p xs = true → ∀ x, x ∈ xs → p x = true := by
  intro xs hAll x hMem
  induction xs with
  | nil => nomatch hMem
  | cons y ys ih =>
    dsimp only [listAll, List.foldr] at hAll
    cases hMem with
    | head _ => exact sfiBandLeft hAll
    | tail _ htl => exact ih (sfiBandRight hAll) htl

private theorem boolFalseOfNotTrue {b : Bool} (h : (!b) = true) :
    b = false := by
  cases b with
  | false => rfl
  | true => exact Bool.noConfusion h

/-- Soundness theorem (`[]` axioms) for the base-name-only store tier. -/
theorem checkStraightLineAbiSfiStoreBaseNamesOnly_sound
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn)
    (h : checkStraightLineAbiSfiStoreBaseNamesOnly allowedStoreBases insns =
      true) :
    StraightLineLeafAbiStoreBaseNamesOnlyCert allowedStoreBases insns := by
  dsimp only [checkStraightLineAbiSfiStoreBaseNamesOnly] at h
  have h1 := sfiBandLeft h
  have hRet := sfiBandRight h
  have hAll := sfiBandLeft h1
  have hYmm := sfiBandRight h1
  have hMemOk := listAll_mem
    (insnStraightLineAbiSfiStoreBaseNamesOnlyOk allowedStoreBases) insns hAll
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hYmm, hRet⟩
  · intro ins hMem g hInWr
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have hCs : insnPreservesCalleeSaved ins = true :=
      sfiBandRight (sfiBandLeft hOk)
    dsimp only [insnPreservesCalleeSaved] at hCs
    exact boolFalseOfNotTrue
      (listAll_mem (fun (r : Gpr) => !r.isCalleeSaved)
        (insnWritesGprs ins) hCs g hInWr)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    exact boolFalseOfNotTrue (sfiBandRight (sfiBandLeft (sfiBandLeft hOk)))
  · intro ins hMem m hSt
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have hConf : insnStoreBaseNameOnly allowedStoreBases ins = true :=
      sfiBandRight hOk
    dsimp only [insnStoreBaseNameOnly] at hConf
    rw [hSt] at hConf
    exact hConf
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have h5 := sfiBandLeft
      (sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk))))
    exact boolFalseOfNotTrue (sfiBandLeft h5)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have h5 := sfiBandLeft
      (sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk))))
    exact boolFalseOfNotTrue (sfiBandRight h5)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have h4 := sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk)))
    exact boolFalseOfNotTrue (sfiBandRight h4)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiStoreBaseNamesOnlyOk] at hOk
    have h3 := sfiBandLeft (sfiBandLeft (sfiBandLeft hOk))
    exact boolFalseOfNotTrue (sfiBandRight h3)

/-- Soundness theorem (`[]` axioms) for the strict fixed entry-base tier:
every allowed store base is never written anywhere in `insns`, and every
memory store uses `[base + disp]` with `index = none` and
`base ∈ allowedStoreBases`. -/
theorem checkStraightLineAbiSfiFixedBases_sound
    (allowedStoreBases : List Gpr) (insns : List DecodedInsn)
    (h : checkStraightLineAbiSfiFixedBases allowedStoreBases insns = true) :
    StraightLineLeafAbiFixedBasesCert allowedStoreBases insns := by
  dsimp only [checkStraightLineAbiSfiFixedBases] at h
  have h1 := sfiBandLeft h
  have hRet := sfiBandRight h
  have hAll := sfiBandLeft h1
  have hYmm := sfiBandRight h1
  have hMemOk := listAll_mem
    (insnStraightLineAbiSfiFixedBasesOk allowedStoreBases) insns hAll
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hYmm, hRet⟩
  · intro ins hMem g hInWr
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hCs : insnPreservesCalleeSaved ins = true :=
      sfiBandRight (sfiBandLeft (sfiBandLeft hOk))
    dsimp only [insnPreservesCalleeSaved] at hCs
    exact boolFalseOfNotTrue
      (listAll_mem (fun (r : Gpr) => !r.isCalleeSaved)
        (insnWritesGprs ins) hCs g hInWr)
  · intro ins hMem g hInWr
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hPr : insnPreservesRegs allowedStoreBases ins = true :=
      sfiBandRight (sfiBandLeft hOk)
    dsimp only [insnPreservesRegs] at hPr
    exact boolFalseOfNotTrue
      (listAll_mem (fun (r : Gpr) => !gprInList r allowedStoreBases)
        (insnWritesGprs ins) hPr g hInWr)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hL3 := sfiBandLeft (sfiBandLeft (sfiBandLeft hOk))
    exact boolFalseOfNotTrue (sfiBandRight hL3)
  · intro ins hMem m hSt
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hConf : insnStoreFixedBaseNoIndex allowedStoreBases ins = true :=
      sfiBandRight hOk
    dsimp only [insnStoreFixedBaseNoIndex] at hConf
    rw [hSt] at hConf
    exact hConf
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hL6 := sfiBandLeft (sfiBandLeft
      (sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk)))))
    exact boolFalseOfNotTrue (sfiBandLeft hL6)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hL6 := sfiBandLeft (sfiBandLeft
      (sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk)))))
    exact boolFalseOfNotTrue (sfiBandRight hL6)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hL5 := sfiBandLeft
      (sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk))))
    exact boolFalseOfNotTrue (sfiBandRight hL5)
  · intro ins hMem
    have hOk := hMemOk ins hMem
    dsimp only [insnStraightLineAbiSfiFixedBasesOk] at hOk
    have hL4 := sfiBandLeft (sfiBandLeft (sfiBandLeft (sfiBandLeft hOk)))
    exact boolFalseOfNotTrue (sfiBandRight hL4)

end Anneal.ElfX86
end
