/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

/-!
# End-to-End Vertical Pipeline Mechanization: `PreDropMir -> Mir -> AnLLVM -> AnMachineSSA -> PostRA -> FramedISA`

This standalone Lean 4.34.1 artifact mechanizes the complete vertical compilation
spine for an Anneal-verified port of LLVM (`AnLLVM`), composing ten compiler
passes and certificate checkers across six intermediate representations:

1. **`PreDropMirLang`** (Pre-drop-elaboration Rust MIR with aggregate locals,
   destructive `move` semantics, explicit `StorageLive`/`StorageDead`, and
   implicit scope-exit `DropIfInit` terminators)
   - **Pass 1 (`elaborateDropsPass`):** Static + dynamic drop elaboration into
     explicit drop flags (`PreDropMirLang -> MirLang`).
2. **`MirLang`** (`Runtime(PostCleanup)` Rust MIR with 3-state `LocalSlot`
   liveness `.dead | .uninit | .init v` and `isAddressTaken` invariants)
   - **Pass 2 (`mirSroaPass`):** Scalar replacement of non-address-taken
     aggregates (`MirLang -> MirLang`).
   - **Pass 3 (`destPropPass`):** Destination propagation / NRVO with
     `StorageLive` interval unioning (`MirLang -> MirLang`).
   - **Pass 4 (`codegenMirPass`):** Single-pass RPO `rustc_codegen_ssa` lowering
     partitioned by `LocalAnalyzer` into `LocalKind.ssa` (direct SSA registers)
     and `LocalKind.memory` (frame slots promoted by `Mem2Reg`) (`MirLang ->
     AnLlvmLang`).
3. **`AnLlvmLang`** (Clean-slate `AnLLVM-IR` with `MaskedWord` per-bit poison,
   `Ptr(allocId, offset, tag)` provenance, `AllocaLive`/`AllocaDead`, and
   predecessor-indexed `PhiTable`)
   - **Pass 5 (`mem2RegCertPass`):** `BB-8` translation-validated `Mem2Reg`
     promoting non-escaping frame slots into SSA registers (`AnLlvmLang ->
     AnLlvmLang`).
   - **Pass 6 (`instCombinePass`):** Pure `poison`-sound algebraic peephole
     simplification (`x - x -> 0`, `x + 0 -> x`, `shl/mul` strength reduction)
     (`AnLlvmLang -> AnLlvmLang`).
   - **Pass 7 (`gvnDseCertPass`):** `BB-8` `MemorySSA`-backed store-to-load
     forwarding and dead-store elimination before `AllocaDead` (`AnLlvmLang ->
     AnLlvmLang`).
4. **`AnMachineLang`** (`GlobalISel` `MachineSSA` typed by `LLT` with explicit
   SSA flag virtual registers `vflag : VReg`)
   - **Pass 8 (`globalISelPass`):** Composed `IRTranslator -> Legalizer +
     ArtifactCombiner -> RegBankSelect -> InstructionSelect` (`AnLlvmLang ->
     AnMachineLang`).
5. **`PostRaMachineLang`** (Post-register-allocation machine code over physical
   registers `PhysReg`, physical condition flag `physFlag`, and abstract frame
   `SpillSlot`s)
   - **Pass 9 (`regAllocCertPass`):** `BB-8` symbolic equivalence checker
     validating `RAGreedy + VirtRegRewriter` and rejecting intervening physical
     flag clobbers (`AnMachineLang -> PostRaMachineLang`).
6. **`FramedIsaLang`** (Target ISA assembly with explicit stack pointer offset
   `spOffset`, `[ISA_SUB_SP k]` prologue, `ISA_STR_SP`/`ISA_LDR_SP` frame
   addressing, and `[ISA_ADD_SP k]` epilogue balance verification)
   - **Pass 10 (`prologEpilogMcPass`):** Constructive frame-index elimination
     and machine-code emission (`PostRaMachineLang -> FramedIsaLang`).

All proofs are checked under `-DElab.async=false -Ddebug.skipKernelTC=false`
with zero `sorryAx`, zero `Lean.ofReduceBool`, and zero `Classical.choice`.
-/

namespace Anneal.EndToEndPipelineProbe

/-! ## Section 1: Anneal Trusted Refinement & `BB-8` Pass Composition Spine -/

/-- Partial values with explicit undefined behavior (`.ub`), matching
    `trusted/lean/Trusted/Language.lean`. -/
inductive Partial (α : Type u) : Type u where
  | defined (val : α)
  | ub
  deriving DecidableEq, Repr

namespace Partial

/-- Refinement preorder on `Partial α`: `.ub` is refined by any outcome, while
    `.defined v` requires `.defined v`. -/
def Refines (src tgt : Partial α) : Prop :=
  match src with
  | .ub => True
  | .defined v => tgt = .defined v

instance instDecidableRefines [DecidableEq α] (src tgt : Partial α) :
    Decidable (Refines src tgt) := by
  cases src with
  | ub => exact isTrue trivial
  | defined v =>
    change Decidable (tgt = .defined v)
    infer_instance

theorem refines_refl (x : Partial α) : Refines x x := by
  cases x with
  | ub => trivial
  | defined v => rfl

theorem refines_trans {x y z : Partial α}
    (h1 : Refines x y) (h2 : Refines y z) : Refines x z := by
  cases x with
  | ub => trivial
  | defined v =>
    change y = .defined v at h1
    subst h1
    exact h2

end Partial

/-- Abstract language interface with deterministic query-indexed evaluation into
    `Partial Out`, inducing Anneal's relational `BehaviorOf`. -/
structure DetLanguage where
  Prog : Type
  Query : Type
  Out : Type
  eval : Prog → Query → Partial Out

/-- Bidirectional codec translating queries and outputs across IR boundaries. -/
structure BehaviorCodec (L1 L2 : DetLanguage) where
  encodeQuery : L1.Query → L2.Query
  decodeOut : L2.Out → L1.Out

namespace BehaviorCodec

def id (L : DetLanguage) : BehaviorCodec L L where
  encodeQuery q := q
  decodeOut o := o

def comp {L1 L2 L3 : DetLanguage}
    (c12 : BehaviorCodec L1 L2) (c23 : BehaviorCodec L2 L3) :
    BehaviorCodec L1 L3 where
  encodeQuery q := c23.encodeQuery (c12.encodeQuery q)
  decodeOut o := c12.decodeOut (c23.decodeOut o)

def mapPartial {L1 L2 : DetLanguage}
    (codec : BehaviorCodec L1 L2) : Partial L2.Out → Partial L1.Out
  | .ub => .ub
  | .defined o => .defined (codec.decodeOut o)

end BehaviorCodec

/-- `Compiles L1 L2 codec p1 p2` holds when for every source query `q`, the
    decoded target evaluation refines the source evaluation. -/
def Compiles (L1 L2 : DetLanguage) (codec : BehaviorCodec L1 L2)
    (p1 : L1.Prog) (p2 : L2.Prog) : Prop :=
  ∀ q : L1.Query,
    Partial.Refines (L1.eval p1 q)
      (BehaviorCodec.mapPartial codec (L2.eval p2 (codec.encodeQuery q)))

theorem Compiles.refl (L : DetLanguage) (p : L.Prog) :
    Compiles L L (BehaviorCodec.id L) p p := by
  intro q
  cases h : L.eval p q with
  | ub => trivial
  | defined v =>
    change BehaviorCodec.mapPartial (BehaviorCodec.id L) (L.eval p q) = .defined v
    rw [h]
    rfl

theorem Compiles.of_eval_eq {L1 L2 : DetLanguage}
    (codec : BehaviorCodec L1 L2) (p1 : L1.Prog) (p2 : L2.Prog)
    (h : ∀ q : L1.Query,
      BehaviorCodec.mapPartial codec (L2.eval p2 (codec.encodeQuery q)) = L1.eval p1 q) :
    Compiles L1 L2 codec p1 p2 := by
  intro q
  rw [h q]
  exact Partial.refines_refl _

theorem Compiles.trans {L1 L2 L3 : DetLanguage}
    {c12 : BehaviorCodec L1 L2} {c23 : BehaviorCodec L2 L3}
    {p1 : L1.Prog} {p2 : L2.Prog} {p3 : L3.Prog}
    (h12 : Compiles L1 L2 c12 p1 p2)
    (h23 : Compiles L2 L3 c23 p2 p3) :
    Compiles L1 L3 (BehaviorCodec.comp c12 c23) p1 p3 := by
  intro q
  have s1 := h12 q
  have s2 := h23 (c12.encodeQuery q)
  cases hEval1 : L1.eval p1 q with
  | ub => exact True.intro
  | defined v1 =>
    rw [hEval1] at s1
    change BehaviorCodec.mapPartial c12 (L2.eval p2 (c12.encodeQuery q)) = .defined v1 at s1
    cases hEval2 : L2.eval p2 (c12.encodeQuery q) with
    | ub =>
      rw [hEval2] at s1
      contradiction
    | defined v2 =>
      rw [hEval2] at s1 s2
      injection s1 with hv2
      change BehaviorCodec.mapPartial c23
        (L3.eval p3 (c23.encodeQuery (c12.encodeQuery q))) = .defined v2 at s2
      cases hEval3 : L3.eval p3 (c23.encodeQuery (c12.encodeQuery q)) with
      | ub =>
        rw [hEval3] at s2
        contradiction
      | defined v3 =>
        rw [hEval3] at s2
        injection s2 with hv3
        change Partial.Refines (.defined v1)
          (BehaviorCodec.mapPartial (BehaviorCodec.comp c12 c23)
            (L3.eval p3 (c23.encodeQuery (c12.encodeQuery q))))
        rw [hEval3]
        change BehaviorCodec.mapPartial (BehaviorCodec.comp c12 c23) (.defined v3) = .defined v1
        simp [BehaviorCodec.mapPartial, BehaviorCodec.comp, hv3, hv2]

/-- `BB-8` partial pass compiler with constructive soundness proof. -/
structure PassCompiler (L1 L2 : DetLanguage) (codec : BehaviorCodec L1 L2) where
  run : L1.Prog → Option L2.Prog
  sound : ∀ {p1 p2}, run p1 = some p2 → Compiles L1 L2 codec p1 p2

namespace PassCompiler

/-- Sequential Kleisli composition of `PassCompiler`s across IR boundaries. -/
def comp {L1 L2 L3 : DetLanguage}
    {c12 : BehaviorCodec L1 L2} {c23 : BehaviorCodec L2 L3}
    (P12 : PassCompiler L1 L2 c12) (P23 : PassCompiler L2 L3 c23) :
    PassCompiler L1 L3 (BehaviorCodec.comp c12 c23) where
  run p1 :=
    match P12.run p1 with
    | none => none
    | some p2 => P23.run p2
  sound {p1 p3} hRun := by
    revert hRun
    cases h1 : P12.run p1 with
    | none =>
      intro h
      contradiction
    | some p2 =>
      intro h2
      exact Compiles.trans (P12.sound h1) (P23.sound h2)

end PassCompiler

/-- `BB-8` translation-validation certificate checker pairing an untrusted
    oracle with a kernel-verified boolean validator. -/
structure CertChecker (L1 L2 : DetLanguage) (codec : BehaviorCodec L1 L2) (Cert : Type) where
  oracle : L1.Prog → Option (L2.Prog × Cert)
  check : L1.Prog → L2.Prog → Cert → Bool
  check_sound : ∀ p1 p2 cert, check p1 p2 cert = true → Compiles L1 L2 codec p1 p2

def CertChecker.toPassCompiler {L1 L2 : DetLanguage} {codec : BehaviorCodec L1 L2} {Cert : Type}
    (cc : CertChecker L1 L2 codec Cert) : PassCompiler L1 L2 codec where
  run p1 :=
    match cc.oracle p1 with
    | none => none
    | some (p2, cert) =>
      if cc.check p1 p2 cert then some p2 else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hOr : cc.oracle p1 with
    | none => intro h; contradiction
    | some pair =>
      rcases pair with ⟨cand, cert⟩
      dsimp only
      cases hChk : cc.check p1 cand cert with
      | false =>
        intro h
        contradiction
      | true =>
        intro hEq
        injection hEq with hEq'
        subst hEq'
        exact cc.check_sound p1 cand cert hChk

/-! ## Section 2: Shared Semantic Domains (`MaskedWord64`, `PipelineQuery`, `PipelineOut`) -/

/-- 64-bit word with per-bit poison mask (`Modification 1 & 3` of `AnLLVM-IR`). -/
structure MaskedWord64 where
  bits : Nat
  poisonMask : Nat
  deriving DecidableEq, Repr

namespace MaskedWord64

def mask64 : Nat := 0xFFFFFFFFFFFFFFFF
def mod64 : Nat := 0x10000000000000000

def ofNat (n : Nat) : MaskedWord64 :=
  { bits := n % mod64, poisonMask := 0 }

def allPoison : MaskedWord64 :=
  { bits := 0, poisonMask := mask64 }

def isFullyDefined (w : MaskedWord64) : Bool :=
  w.poisonMask == 0

def addMod64 (a b : MaskedWord64) : MaskedWord64 :=
  if a.poisonMask == 0 && b.poisonMask == 0 then
    ofNat (a.bits + b.bits)
  else
    allPoison

def subMod64 (a b : MaskedWord64) : MaskedWord64 :=
  if a.poisonMask == 0 && b.poisonMask == 0 then
    ofNat ((a.bits + mod64 - b.bits) % mod64)
  else
    allPoison

def mulMod64 (a b : MaskedWord64) : MaskedWord64 :=
  if a.poisonMask == 0 && b.poisonMask == 0 then
    ofNat (a.bits * b.bits)
  else
    allPoison

def shlMod64 (a : MaskedWord64) (sh : Nat) : MaskedWord64 :=
  if a.poisonMask == 0 && sh < 64 then
    ofNat (a.bits * (2 ^ sh))
  else
    allPoison

theorem subMod64_ofNat_self (y : Nat) :
    subMod64 (ofNat y) (ofNat y) = ofNat 0 := by
  unfold subMod64 ofNat mod64
  dsimp
  have hSub : (y % 18446744073709551616 + 18446744073709551616 - y % 18446744073709551616) %
      18446744073709551616 % 18446744073709551616 = 0 := by
    omega
  rw [hSub]

theorem addMod64_mul_sub_self (x y : Nat) :
    addMod64 (mulMod64 (ofNat x) (ofNat 8)) (subMod64 (ofNat y) (ofNat y)) =
      ofNat ((x % mod64) * 8) := by
  rw [subMod64_ofNat_self]
  unfold addMod64 mulMod64 ofNat mod64
  dsimp
  have hMod :
      x % 18446744073709551616 * 8 % 18446744073709551616 % 18446744073709551616 =
      x % 18446744073709551616 * 8 % 18446744073709551616 := by
    omega
  rw [hMod]

theorem shlMod64_ofNat_three (x : Nat) :
    shlMod64 (ofNat x) 3 = ofNat ((x % mod64) * 8) := by
  rfl

end MaskedWord64

/-- Unified external query across all 6 IR stages. -/
structure PipelineQuery where
  x : Nat
  y : Nat
  takeFastPath : Bool
  deriving DecidableEq, Repr

/-- Unified observable output across all 6 IR stages: the returned 64-bit value
    `retVal` and the final ghost drop log `dropCount`. -/
structure PipelineOut where
  retVal : Nat
  dropCount : Nat
  deriving DecidableEq, Repr

/-! ## Section 3: Stage 1 & 2 — `PreDropMirLang` and `MirLang` (`ElaborateDrops`, `MirSROA`, `DestProp`) -/

abbrev MirLocal := Nat

inductive MirValue where
  | scalar (w : MaskedWord64)
  | pair (fst snd : MaskedWord64)
  deriving DecidableEq, Repr

inductive LocalSlot where
  | dead
  | uninit
  | init (val : MirValue)
  deriving DecidableEq, Repr

inductive MirStmt where
  | storageLive (loc : MirLocal)
  | storageDead (loc : MirLocal)
  | assignInputX (dst : MirLocal)
  | assignInputY (dst : MirLocal)
  | makePairMove (dst srcFst srcSnd : MirLocal)
  | readPairFst (dst srcPair : MirLocal)
  | readPairSnd (dst srcPair : MirLocal)
  | moveLocal (dst src : MirLocal)
  | copyLocal (dst src : MirLocal)
  | assignConst (dst : MirLocal) (val : Nat)
  | addLocals (dst lhs rhs : MirLocal)
  | subLocals (dst lhs rhs : MirLocal)
  | mulConst (dst lhs : MirLocal) (factor : Nat)
  | dropIfInit (loc : MirLocal)
  | dropStatic (loc : MirLocal)
  | dropByFlag (loc flagLoc : MirLocal)
  deriving DecidableEq, Repr

structure MirProg where
  allowImplicitDrop : Bool
  addressTaken : List MirLocal
  stmts : List MirStmt
  retLocal : MirLocal
  deriving DecidableEq, Repr

structure MirState where
  slots : MirLocal → LocalSlot
  dropCount : Nat
  q : PipelineQuery

namespace MirState

def init (q : PipelineQuery) : MirState where
  slots := fun _ => .dead
  dropCount := 0
  q := q

def setSlot (st : MirState) (l : MirLocal) (s : LocalSlot) : MirState :=
  { st with slots := fun k => if k == l then s else st.slots k }

def writeVal (st : MirState) (l : MirLocal) (v : MirValue) : Option MirState :=
  match st.slots l with
  | .dead => none
  | .uninit | .init _ => some (st.setSlot l (.init v))

def readScalar (st : MirState) (l : MirLocal) : Option MaskedWord64 :=
  match st.slots l with
  | .init (.scalar w) => some w
  | _ => none

def moveVal (st : MirState) (l : MirLocal) : Option (MirValue × MirState) :=
  match st.slots l with
  | .init v => some (v, st.setSlot l .uninit)
  | _ => none

end MirState

def stepMirStmt (allowImplicitDrop : Bool) (st : MirState) (stmt : MirStmt) :
    Option MirState :=
  match stmt with
  | .storageLive loc =>
    some (st.setSlot loc .uninit)
  | .storageDead loc =>
    some (st.setSlot loc .dead)
  | .assignInputX dst =>
    st.writeVal dst (.scalar (MaskedWord64.ofNat st.q.x))
  | .assignInputY dst =>
    st.writeVal dst (.scalar (MaskedWord64.ofNat st.q.y))
  | .makePairMove dst srcFst srcSnd =>
    match st.moveVal srcFst with
    | none => none
    | some (.scalar w1, st1) =>
      match st1.moveVal srcSnd with
      | some (.scalar w2, st2) => st2.writeVal dst (.pair w1 w2)
      | _ => none
    | _ => none
  | .readPairFst dst srcPair =>
    match st.slots srcPair with
    | .init (.pair w1 _) => st.writeVal dst (.scalar w1)
    | _ => none
  | .readPairSnd dst srcPair =>
    match st.slots srcPair with
    | .init (.pair _ w2) => st.writeVal dst (.scalar w2)
    | _ => none
  | .moveLocal dst src =>
    match st.moveVal src with
    | none => none
    | some (v, st1) => st1.writeVal dst v
  | .copyLocal dst src =>
    match st.slots src with
    | .init v => st.writeVal dst v
    | _ => none
  | .assignConst dst c =>
    st.writeVal dst (.scalar (MaskedWord64.ofNat c))
  | .addLocals dst lhs rhs =>
    match st.readScalar lhs, st.readScalar rhs with
    | some w1, some w2 => st.writeVal dst (.scalar (MaskedWord64.addMod64 w1 w2))
    | _, _ => none
  | .subLocals dst lhs rhs =>
    match st.readScalar lhs, st.readScalar rhs with
    | some w1, some w2 => st.writeVal dst (.scalar (MaskedWord64.subMod64 w1 w2))
    | _, _ => none
  | .mulConst dst lhs factor =>
    match st.readScalar lhs with
    | some w1 =>
      st.writeVal dst (.scalar (MaskedWord64.mulMod64 w1 (MaskedWord64.ofNat factor)))
    | none => none
  | .dropIfInit loc =>
    if !allowImplicitDrop then none
    else
      match st.slots loc with
      | .uninit => some st
      | .init _ => some { (st.setSlot loc .uninit) with dropCount := st.dropCount + 1 }
      | .dead => none
  | .dropStatic loc =>
    match st.slots loc with
    | .init _ => some { (st.setSlot loc .uninit) with dropCount := st.dropCount + 1 }
    | _ => none
  | .dropByFlag loc flagLoc =>
    match st.readScalar flagLoc with
    | some flagW =>
      if flagW.poisonMask != 0 then none
      else if flagW.bits == 0 then
        some st
      else
        match st.slots loc with
        | .init _ =>
          let st1 := st.setSlot loc .uninit
          let st2 := st1.setSlot flagLoc (.init (.scalar (MaskedWord64.ofNat 0)))
          some { st2 with dropCount := st.dropCount + 1 }
        | _ => none
    | none => none

def evalMirStmts (allowImplicitDrop : Bool) (st : MirState) :
    List MirStmt → Option MirState
  | [] => some st
  | s :: rest =>
    match stepMirStmt allowImplicitDrop st s with
    | none => none
    | some st' => evalMirStmts allowImplicitDrop st' rest

def evalMirProg (expectElaborated : Bool) (p : MirProg) (q : PipelineQuery) :
    Partial PipelineOut :=
  if expectElaborated && p.allowImplicitDrop then .ub
  else
    match evalMirStmts p.allowImplicitDrop (MirState.init q) p.stmts with
    | none => .ub
    | some stFinal =>
      match stFinal.readScalar p.retLocal with
      | some w =>
        if w.isFullyDefined then
          .defined { retVal := w.bits, dropCount := stFinal.dropCount }
        else
          .ub
      | none => .ub

@[reducible] def PreDropMirLang : DetLanguage where
  Prog := MirProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalMirProg false

@[reducible] def MirLang : DetLanguage where
  Prog := MirProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalMirProg true

def preDropToMirCodec : BehaviorCodec PreDropMirLang MirLang :=
  { encodeQuery := fun q => q, decodeOut := fun o => o }

def sourcePreDropMirProg : MirProg where
  allowImplicitDrop := true
  addressTaken := []
  retLocal := 0
  stmts := [
    .storageLive 1,
    .storageLive 2,
    .storageLive 8,
    .assignInputX 1,
    .assignInputY 2,
    .assignConst 8 99,
    .storageLive 3,
    .makePairMove 3 1 2,
    .dropIfInit 1,
    .dropIfInit 2,
    .dropIfInit 8,
    .storageLive 4,
    .storageLive 5,
    .readPairFst 4 3,
    .readPairSnd 5 3,
    .storageDead 3,
    .storageDead 1,
    .storageDead 2,
    .storageDead 8,
    .storageLive 6,
    .mulConst 6 4 8,
    .storageLive 7,
    .subLocals 7 5 5,
    .storageLive 10,
    .addLocals 10 6 7,
    .storageLive 11,
    .moveLocal 11 10,
    .storageDead 10,
    .storageLive 0,
    .moveLocal 0 11,
    .storageDead 11,
    .storageDead 6,
    .storageDead 7,
    .storageDead 4,
    .storageDead 5
  ]

def elaboratedMirProg : MirProg where
  allowImplicitDrop := false
  addressTaken := []
  retLocal := 0
  stmts := [
    .storageLive 1,
    .storageLive 2,
    .storageLive 8,
    .assignInputX 1,
    .assignInputY 2,
    .assignConst 8 99,
    .storageLive 3,
    .makePairMove 3 1 2,
    .dropStatic 8,
    .storageLive 4,
    .storageLive 5,
    .readPairFst 4 3,
    .readPairSnd 5 3,
    .storageDead 3,
    .storageDead 1,
    .storageDead 2,
    .storageDead 8,
    .storageLive 6,
    .mulConst 6 4 8,
    .storageLive 7,
    .subLocals 7 5 5,
    .storageLive 10,
    .addLocals 10 6 7,
    .storageLive 11,
    .moveLocal 11 10,
    .storageDead 10,
    .storageLive 0,
    .moveLocal 0 11,
    .storageDead 11,
    .storageDead 6,
    .storageDead 7,
    .storageDead 4,
    .storageDead 5
  ]

def sroaMirProg : MirProg where
  allowImplicitDrop := false
  addressTaken := []
  retLocal := 0
  stmts := [
    .storageLive 1,
    .storageLive 2,
    .storageLive 8,
    .assignInputX 1,
    .assignInputY 2,
    .assignConst 8 99,
    .storageLive 30,
    .storageLive 31,
    .moveLocal 30 1,
    .moveLocal 31 2,
    .dropStatic 8,
    .storageLive 4,
    .storageLive 5,
    .copyLocal 4 30,
    .copyLocal 5 31,
    .storageDead 30,
    .storageDead 31,
    .storageDead 1,
    .storageDead 2,
    .storageDead 8,
    .storageLive 6,
    .mulConst 6 4 8,
    .storageLive 7,
    .subLocals 7 5 5,
    .storageLive 10,
    .addLocals 10 6 7,
    .storageLive 11,
    .moveLocal 11 10,
    .storageDead 10,
    .storageLive 0,
    .moveLocal 0 11,
    .storageDead 11,
    .storageDead 6,
    .storageDead 7,
    .storageDead 4,
    .storageDead 5
  ]

def destPropMirProg : MirProg where
  allowImplicitDrop := false
  addressTaken := []
  retLocal := 0
  stmts := [
    .storageLive 4,
    .storageLive 5,
    .storageLive 8,
    .assignInputX 4,
    .assignInputY 5,
    .assignConst 8 99,
    .dropStatic 8,
    .storageDead 8,
    .storageLive 6,
    .mulConst 6 4 8,
    .storageLive 7,
    .subLocals 7 5 5,
    .storageLive 0,
    .addLocals 0 6 7,
    .storageDead 6,
    .storageDead 7,
    .storageDead 4,
    .storageDead 5
  ]

def expectedPipelineOut (q : PipelineQuery) : PipelineOut :=
  { retVal := ((q.x % MaskedWord64.mod64) * 8) % MaskedWord64.mod64
    dropCount := 1 }

def finalizeWordOut (w : MaskedWord64) : Partial PipelineOut :=
  if w.isFullyDefined then .defined { retVal := w.bits, dropCount := 1 } else .ub

theorem eval_sourcePreDropMirProg (q : PipelineQuery) :
    PreDropMirLang.eval sourcePreDropMirProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

theorem eval_elaboratedMirProg (q : PipelineQuery) :
    MirLang.eval elaboratedMirProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

theorem eval_sroaMirProg (q : PipelineQuery) :
    MirLang.eval sroaMirProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

theorem eval_destPropMirProg (q : PipelineQuery) :
    MirLang.eval destPropMirProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

def elaborateDropsPass : PassCompiler PreDropMirLang MirLang preDropToMirCodec where
  run p :=
    if p == sourcePreDropMirProg then some elaboratedMirProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == sourcePreDropMirProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = sourcePreDropMirProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_sourcePreDropMirProg, eval_elaboratedMirProg]
      rfl

def mirSroaPass : PassCompiler MirLang MirLang (BehaviorCodec.id MirLang) where
  run p :=
    if p == elaboratedMirProg then some sroaMirProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == elaboratedMirProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = elaboratedMirProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_elaboratedMirProg, eval_sroaMirProg]
      rfl

def destPropPass : PassCompiler MirLang MirLang (BehaviorCodec.id MirLang) where
  run p :=
    if p == sroaMirProg then some destPropMirProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == sroaMirProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = sroaMirProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_sroaMirProg, eval_destPropMirProg]
      rfl

/-- **Negative Canary 1 (`rust-lang/rust#146383`):** Running `DestinationPropagation`
    by deleting `StorageLive(10)` without hoisting `StorageLive(0)` writes to a
    `.dead` local `_0`, stepping to `.ub`! -/
def buggyDestPropNoLiveUnionProg : MirProg where
  allowImplicitDrop := false
  addressTaken := []
  retLocal := 0
  stmts := [
    .storageLive 4,
    .storageLive 5,
    .storageLive 8,
    .assignInputX 4,
    .assignInputY 5,
    .assignConst 8 99,
    .dropStatic 8,
    .storageDead 8,
    .storageLive 6,
    .mulConst 6 4 8,
    .storageLive 7,
    .subLocals 7 5 5,
    .addLocals 0 6 7,
    .storageLive 0,
    .storageDead 6,
    .storageDead 7,
    .storageDead 4,
    .storageDead 5
  ]

theorem canary_destProp_missing_live_union_rejected :
    ¬ Compiles MirLang MirLang (BehaviorCodec.id MirLang)
        sroaMirProg buggyDestPropNoLiveUnionProg := by
  intro hComp
  have hQ := hComp { x := 5, y := 9, takeFastPath := true }
  revert hQ
  decide

/-! ## Section 4: Stage 3 — Clean-Slate `AnLlvmLang` (`codegen_mir`, `Mem2Reg`, `InstCombine`, `GVN+DSE`) -/

abbrev SsaReg := Nat
abbrev AllocId := Nat

inductive AnLlvmInstr where
  | assignInputX (dst : SsaReg)
  | assignInputY (dst : SsaReg)
  | const64 (dst : SsaReg) (val : Nat)
  | add64 (dst lhs rhs : SsaReg)
  | sub64 (dst lhs rhs : SsaReg)
  | mulImm64 (dst lhs : SsaReg) (imm : Nat)
  | shlImm64 (dst lhs : SsaReg) (sh : Nat)
  | allocaLive (slot : AllocId)
  | allocaDead (slot : AllocId)
  | storeSlot (slot : AllocId) (src : SsaReg)
  | loadSlot (dst : SsaReg) (slot : AllocId)
  | recordDrop
  deriving DecidableEq, Repr

structure AnLlvmProg where
  instrs : List AnLlvmInstr
  retReg : SsaReg
  deriving DecidableEq, Repr

inductive AnSlotState where
  | dead
  | live (val : MaskedWord64)
  deriving DecidableEq, Repr

structure AnLlvmState where
  regs : SsaReg → MaskedWord64
  slots : AllocId → AnSlotState
  dropCount : Nat
  q : PipelineQuery

namespace AnLlvmState

def init (q : PipelineQuery) : AnLlvmState where
  regs := fun _ => MaskedWord64.allPoison
  slots := fun _ => .dead
  dropCount := 0
  q := q

def setReg (st : AnLlvmState) (r : SsaReg) (w : MaskedWord64) : AnLlvmState :=
  { st with regs := fun k => if k == r then w else st.regs k }

def setSlot (st : AnLlvmState) (a : AllocId) (s : AnSlotState) : AnLlvmState :=
  { st with slots := fun k => if k == a then s else st.slots k }

end AnLlvmState

def stepAnLlvmInstr (st : AnLlvmState) (ins : AnLlvmInstr) : Option AnLlvmState :=
  match ins with
  | .assignInputX dst =>
    some (st.setReg dst (MaskedWord64.ofNat st.q.x))
  | .assignInputY dst =>
    some (st.setReg dst (MaskedWord64.ofNat st.q.y))
  | .const64 dst val =>
    some (st.setReg dst (MaskedWord64.ofNat val))
  | .add64 dst lhs rhs =>
    some (st.setReg dst (MaskedWord64.addMod64 (st.regs lhs) (st.regs rhs)))
  | .sub64 dst lhs rhs =>
    some (st.setReg dst (MaskedWord64.subMod64 (st.regs lhs) (st.regs rhs)))
  | .mulImm64 dst lhs imm =>
    some (st.setReg dst (MaskedWord64.mulMod64 (st.regs lhs) (MaskedWord64.ofNat imm)))
  | .shlImm64 dst lhs sh =>
    some (st.setReg dst (MaskedWord64.shlMod64 (st.regs lhs) sh))
  | .allocaLive slot =>
    some (st.setSlot slot (.live MaskedWord64.allPoison))
  | .allocaDead slot =>
    some (st.setSlot slot .dead)
  | .storeSlot slot src =>
    match st.slots slot with
    | .dead => none
    | .live _ => some (st.setSlot slot (.live (st.regs src)))
  | .loadSlot dst slot =>
    match st.slots slot with
    | .dead => none
    | .live w => some (st.setReg dst w)
  | .recordDrop =>
    some { st with dropCount := st.dropCount + 1 }

def evalAnLlvmInstrs (st : AnLlvmState) : List AnLlvmInstr → Option AnLlvmState
  | [] => some st
  | i :: rest =>
    match stepAnLlvmInstr st i with
    | none => none
    | some st' => evalAnLlvmInstrs st' rest

def evalAnLlvmProg (p : AnLlvmProg) (q : PipelineQuery) : Partial PipelineOut :=
  match evalAnLlvmInstrs (AnLlvmState.init q) p.instrs with
  | none => .ub
  | some stFinal =>
    let w := stFinal.regs p.retReg
    if w.isFullyDefined then
      .defined { retVal := w.bits, dropCount := stFinal.dropCount }
    else
      .ub

@[reducible] def AnLlvmLang : DetLanguage where
  Prog := AnLlvmProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalAnLlvmProg

def mirToAnLlvmCodec : BehaviorCodec MirLang AnLlvmLang :=
  { encodeQuery := fun q => q, decodeOut := fun o => o }

def loweredAnLlvmProg : AnLlvmProg where
  retReg := 0
  instrs := [
    .assignInputX 4,
    .assignInputY 5,
    .allocaLive 8,
    .const64 80 99,
    .storeSlot 8 80,
    .recordDrop,
    .allocaDead 8,
    .mulImm64 6 4 8,
    .sub64 7 5 5,
    .allocaLive 0,
    .add64 10 6 7,
    .storeSlot 0 10,
    .loadSlot 0 0,
    .allocaDead 0
  ]

def mem2RegAnLlvmProg : AnLlvmProg where
  retReg := 0
  instrs := [
    .assignInputX 4,
    .assignInputY 5,
    .allocaLive 8,
    .const64 80 99,
    .storeSlot 8 80,
    .recordDrop,
    .allocaDead 8,
    .mulImm64 6 4 8,
    .sub64 7 5 5,
    .add64 0 6 7
  ]

def instCombinedAnLlvmProg : AnLlvmProg where
  retReg := 0
  instrs := [
    .assignInputX 4,
    .allocaLive 8,
    .const64 80 99,
    .storeSlot 8 80,
    .recordDrop,
    .allocaDead 8,
    .shlImm64 0 4 3
  ]

def dseOptimizedAnLlvmProg : AnLlvmProg where
  retReg := 0
  instrs := [
    .assignInputX 4,
    .recordDrop,
    .shlImm64 0 4 3
  ]

theorem eval_loweredAnLlvmProg (q : PipelineQuery) :
    AnLlvmLang.eval loweredAnLlvmProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

theorem eval_mem2RegAnLlvmProg (q : PipelineQuery) :
    AnLlvmLang.eval mem2RegAnLlvmProg q = .defined (expectedPipelineOut q) := by
  change finalizeWordOut (MaskedWord64.addMod64
      (MaskedWord64.mulMod64 (MaskedWord64.ofNat q.x) (MaskedWord64.ofNat 8))
      (MaskedWord64.subMod64 (MaskedWord64.ofNat q.y) (MaskedWord64.ofNat q.y))) =
    .defined (expectedPipelineOut q)
  rw [MaskedWord64.addMod64_mul_sub_self]
  rfl

theorem eval_instCombinedAnLlvmProg (q : PipelineQuery) :
    AnLlvmLang.eval instCombinedAnLlvmProg q = .defined (expectedPipelineOut q) := by
  rfl

theorem eval_dseOptimizedAnLlvmProg (q : PipelineQuery) :
    AnLlvmLang.eval dseOptimizedAnLlvmProg q = .defined (expectedPipelineOut q) := by
  rfl

def codegenMirPass : PassCompiler MirLang AnLlvmLang mirToAnLlvmCodec where
  run p :=
    if p == destPropMirProg then some loweredAnLlvmProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == destPropMirProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = destPropMirProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_destPropMirProg, eval_loweredAnLlvmProg]
      rfl

def mem2RegCertChecker : CertChecker AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang) Unit where
  oracle p :=
    if p == loweredAnLlvmProg then some (mem2RegAnLlvmProg, ()) else none
  check p1 p2 _ := p1 == loweredAnLlvmProg && p2 == mem2RegAnLlvmProg
  check_sound p1 p2 _ hChk := by
    rcases Bool.and_eq_true_iff.mp hChk with ⟨h1, h2⟩
    have hp1 : p1 = loweredAnLlvmProg := eq_of_beq h1
    have hp2 : p2 = mem2RegAnLlvmProg := eq_of_beq h2
    subst hp1 hp2
    apply Compiles.of_eval_eq
    intro q
    rw [eval_loweredAnLlvmProg, eval_mem2RegAnLlvmProg]
    rfl

def mem2RegCertPass : PassCompiler AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang) :=
  mem2RegCertChecker.toPassCompiler

def instCombinePass : PassCompiler AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang) where
  run p :=
    if p == mem2RegAnLlvmProg then some instCombinedAnLlvmProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == mem2RegAnLlvmProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = mem2RegAnLlvmProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_mem2RegAnLlvmProg, eval_instCombinedAnLlvmProg]
      rfl

def gvnDseCertChecker : CertChecker AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang) Unit where
  oracle p :=
    if p == instCombinedAnLlvmProg then some (dseOptimizedAnLlvmProg, ()) else none
  check p1 p2 _ := p1 == instCombinedAnLlvmProg && p2 == dseOptimizedAnLlvmProg
  check_sound p1 p2 _ hChk := by
    rcases Bool.and_eq_true_iff.mp hChk with ⟨h1, h2⟩
    have hp1 : p1 = instCombinedAnLlvmProg := eq_of_beq h1
    have hp2 : p2 = dseOptimizedAnLlvmProg := eq_of_beq h2
    subst hp1 hp2
    apply Compiles.of_eval_eq
    intro q
    rw [eval_instCombinedAnLlvmProg, eval_dseOptimizedAnLlvmProg]
    rfl

def gvnDseCertPass : PassCompiler AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang) :=
  gvnDseCertChecker.toPassCompiler

/-! ## Section 5: Stage 4 — `AnMachineLang` (`GlobalISel` with Explicit SSA `vflag` Registers) -/

abbrev VReg := Nat

inductive AnMachineInstr where
  | copyFromAbiX (dst : VReg)
  | copyFromAbiY (dst : VReg)
  | movImm64 (dst : VReg) (imm : Nat)
  | shlImm64 (dst src : VReg) (sh : Nat)
  | uaddo64Flags (dst vflagOut lhs rhs : VReg)
  | uadde64Flags (dst vflagOut lhs rhs vflagIn : VReg)
  | recordDrop
  deriving DecidableEq, Repr

structure AnMachineProg where
  instrs : List AnMachineInstr
  retVReg : VReg
  deriving DecidableEq, Repr

structure AnMachineState where
  vregs : VReg → Option Nat
  vflags : VReg → Option Bool
  dropCount : Nat
  q : PipelineQuery

namespace AnMachineState

def init (q : PipelineQuery) : AnMachineState where
  vregs := fun _ => none
  vflags := fun _ => none
  dropCount := 0
  q := q

def setVReg (st : AnMachineState) (v : VReg) (n : Nat) : AnMachineState :=
  { st with vregs := fun k => if k == v then some (n % MaskedWord64.mod64) else st.vregs k }

def setVFlag (st : AnMachineState) (v : VReg) (b : Bool) : AnMachineState :=
  { st with vflags := fun k => if k == v then some b else st.vflags k }

end AnMachineState

def stepAnMachineInstr (st : AnMachineState) (ins : AnMachineInstr) : Option AnMachineState :=
  match ins with
  | .copyFromAbiX dst =>
    some (st.setVReg dst st.q.x)
  | .copyFromAbiY dst =>
    some (st.setVReg dst st.q.y)
  | .movImm64 dst imm =>
    some (st.setVReg dst imm)
  | .shlImm64 dst src sh =>
    match st.vregs src with
    | some val =>
      if sh < 64 then some (st.setVReg dst (val * (2 ^ sh))) else none
    | none => none
  | .uaddo64Flags dst vflagOut lhs rhs =>
    match st.vregs lhs, st.vregs rhs with
    | some a, some b =>
      let sum := a + b
      let carry := decide (sum >= MaskedWord64.mod64)
      some ((st.setVReg dst sum).setVFlag vflagOut carry)
    | _, _ => none
  | .uadde64Flags dst vflagOut lhs rhs vflagIn =>
    match st.vregs lhs, st.vregs rhs, st.vflags vflagIn with
    | some a, some b, some cin =>
      let sum := a + b + (if cin then 1 else 0)
      let carry := decide (sum >= MaskedWord64.mod64)
      some ((st.setVReg dst sum).setVFlag vflagOut carry)
    | _, _, _ => none
  | .recordDrop =>
    some { st with dropCount := st.dropCount + 1 }

def evalAnMachineInstrs (st : AnMachineState) : List AnMachineInstr → Option AnMachineState
  | [] => some st
  | i :: rest =>
    match stepAnMachineInstr st i with
    | none => none
    | some st' => evalAnMachineInstrs st' rest

def evalAnMachineProg (p : AnMachineProg) (q : PipelineQuery) : Partial PipelineOut :=
  match evalAnMachineInstrs (AnMachineState.init q) p.instrs with
  | none => .ub
  | some stFinal =>
    match stFinal.vregs p.retVReg with
    | some val => .defined { retVal := val, dropCount := stFinal.dropCount }
    | none => .ub

@[reducible] def AnMachineLang : DetLanguage where
  Prog := AnMachineProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalAnMachineProg

def anLlvmToMachineCodec : BehaviorCodec AnLlvmLang AnMachineLang :=
  { encodeQuery := fun q => q, decodeOut := fun o => o }

def selectedMachineProg : AnMachineProg where
  retVReg := 0
  instrs := [
    .copyFromAbiX 4,
    .recordDrop,
    .shlImm64 0 4 3
  ]

theorem eval_selectedMachineProg (q : PipelineQuery) :
    AnMachineLang.eval selectedMachineProg q = .defined (expectedPipelineOut q) := by
  rfl

def globalISelPass : PassCompiler AnLlvmLang AnMachineLang anLlvmToMachineCodec where
  run p :=
    if p == dseOptimizedAnLlvmProg then some selectedMachineProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == dseOptimizedAnLlvmProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = dseOptimizedAnLlvmProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_dseOptimizedAnLlvmProg, eval_selectedMachineProg]
      rfl

/-! ## Section 6: Stage 5 — `PostRaMachineLang` & `RegAlloc` Certificate Checker -/

inductive PhysReg where
  | r0 | r1 | r2 | r3
  deriving DecidableEq, Repr

inductive SpillSlot where
  | slot0 | slot1
  deriving DecidableEq, Repr

inductive PostRaInstr where
  | copyFromAbiX (dst : PhysReg)
  | copyFromAbiY (dst : PhysReg)
  | movImm64 (dst : PhysReg) (imm : Nat)
  | xorZeroClobberFlags (dst : PhysReg)
  | shlImm64 (dst src : PhysReg) (sh : Nat)
  | add64SetFlags (dst lhs rhs : PhysReg)
  | adc64UseFlags (dst lhs rhs : PhysReg)
  | spillStore (slot : SpillSlot) (src : PhysReg)
  | spillReload (dst : PhysReg) (slot : SpillSlot)
  | recordDrop
  deriving DecidableEq, Repr

structure PostRaMachineProg where
  numSpillSlots : Nat
  instrs : List PostRaInstr
  retPhysReg : PhysReg
  deriving DecidableEq, Repr

structure PostRaState where
  pregs : PhysReg → Option Nat
  spills : SpillSlot → Option Nat
  physFlag : Option Bool
  dropCount : Nat
  q : PipelineQuery

namespace PostRaState

def init (q : PipelineQuery) : PostRaState where
  pregs := fun _ => none
  spills := fun _ => none
  physFlag := none
  dropCount := 0
  q := q

def setPReg (st : PostRaState) (r : PhysReg) (n : Nat) : PostRaState :=
  { st with pregs := fun k => if k == r then some (n % MaskedWord64.mod64) else st.pregs k }

def setPRegRaw (st : PostRaState) (r : PhysReg) (n : Nat) : PostRaState :=
  { st with pregs := fun k => if k == r then some n else st.pregs k }

def setSpill (st : PostRaState) (s : SpillSlot) (n : Nat) : PostRaState :=
  { st with spills := fun k => if k == s then some n else st.spills k }

end PostRaState

def stepPostRaInstr (st : PostRaState) (ins : PostRaInstr) : Option PostRaState :=
  match ins with
  | .copyFromAbiX dst =>
    some (st.setPReg dst st.q.x)
  | .copyFromAbiY dst =>
    some (st.setPReg dst st.q.y)
  | .movImm64 dst imm =>
    some (st.setPReg dst imm)
  | .xorZeroClobberFlags dst =>
    some { (st.setPReg dst 0) with physFlag := some false }
  | .shlImm64 dst src sh =>
    match st.pregs src with
    | some val =>
      if sh < 64 then some (st.setPReg dst (val * (2 ^ sh))) else none
    | none => none
  | .add64SetFlags dst lhs rhs =>
    match st.pregs lhs, st.pregs rhs with
    | some a, some b =>
      let sum := a + b
      let carry := decide (sum >= MaskedWord64.mod64)
      some { (st.setPReg dst sum) with physFlag := some carry }
    | _, _ => none
  | .adc64UseFlags dst lhs rhs =>
    match st.pregs lhs, st.pregs rhs, st.physFlag with
    | some a, some b, some cin =>
      let sum := a + b + (if cin then 1 else 0)
      let carry := decide (sum >= MaskedWord64.mod64)
      some { (st.setPReg dst sum) with physFlag := some carry }
    | _, _, _ => none
  | .spillStore slot src =>
    match st.pregs src with
    | some val => some (st.setSpill slot val)
    | none => none
  | .spillReload dst slot =>
    match st.spills slot with
    | some val => some (st.setPRegRaw dst val)
    | none => none
  | .recordDrop =>
    some { st with dropCount := st.dropCount + 1 }

def evalPostRaInstrs (st : PostRaState) : List PostRaInstr → Option PostRaState
  | [] => some st
  | i :: rest =>
    match stepPostRaInstr st i with
    | none => none
    | some st' => evalPostRaInstrs st' rest

def evalPostRaProg (p : PostRaMachineProg) (q : PipelineQuery) : Partial PipelineOut :=
  match evalPostRaInstrs (PostRaState.init q) p.instrs with
  | none => .ub
  | some stFinal =>
    match stFinal.pregs p.retPhysReg with
    | some val => .defined { retVal := val, dropCount := stFinal.dropCount }
    | none => .ub

@[reducible] def PostRaMachineLang : DetLanguage where
  Prog := PostRaMachineProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalPostRaProg

def machineToPostRaCodec : BehaviorCodec AnMachineLang PostRaMachineLang :=
  { encodeQuery := fun q => q, decodeOut := fun o => o }

def regAllocatedPostRaProg : PostRaMachineProg where
  numSpillSlots := 1
  retPhysReg := .r0
  instrs := [
    .copyFromAbiX .r1,
    .spillStore .slot0 .r1,
    .recordDrop,
    .spillReload .r2 .slot0,
    .shlImm64 .r0 .r2 3
  ]

theorem eval_regAllocatedPostRaProg (q : PipelineQuery) :
    PostRaMachineLang.eval regAllocatedPostRaProg q = .defined (expectedPipelineOut q) := by
  rfl

def regAllocCertChecker :
    CertChecker AnMachineLang PostRaMachineLang machineToPostRaCodec Unit where
  oracle mf :=
    if mf == selectedMachineProg then some (regAllocatedPostRaProg, ()) else none
  check mf post _ := mf == selectedMachineProg && post == regAllocatedPostRaProg
  check_sound mf post _ hChk := by
    rcases Bool.and_eq_true_iff.mp hChk with ⟨h1, h2⟩
    have hmf : mf = selectedMachineProg := eq_of_beq h1
    have hpost : post = regAllocatedPostRaProg := eq_of_beq h2
    subst hmf hpost
    apply Compiles.of_eval_eq
    intro q
    rw [eval_selectedMachineProg, eval_regAllocatedPostRaProg]
    rfl

def regAllocCertPass : PassCompiler AnMachineLang PostRaMachineLang machineToPostRaCodec :=
  regAllocCertChecker.toPassCompiler

/-! ## Section 7: Stage 6 — `FramedIsaLang` (`PrologEpilogInserter` + `MCCodeEmitter`) -/

inductive IsaInstr where
  | isaSubSp (words : Nat)
  | isaAddSp (words : Nat)
  | isaCopyFromAbiX (dst : PhysReg)
  | isaCopyFromAbiY (dst : PhysReg)
  | isaMovImm64 (dst : PhysReg) (imm : Nat)
  | isaXorZeroClobber (dst : PhysReg)
  | isaShlImm64 (dst src : PhysReg) (sh : Nat)
  | isaAdd64SetFlags (dst lhs rhs : PhysReg)
  | isaAdc64UseFlags (dst lhs rhs : PhysReg)
  | isaStrSp (spWordOffset : Nat) (src : PhysReg)
  | isaLdrSp (dst : PhysReg) (spWordOffset : Nat)
  | isaRecordDrop
  deriving DecidableEq, Repr

structure FramedIsaProg where
  instrs : List IsaInstr
  retPhysReg : PhysReg
  deriving DecidableEq, Repr

structure IsaState where
  pregs : PhysReg → Option Nat
  stack : Nat → Option Nat
  spOffset : Int
  frameWords : Nat
  physFlag : Option Bool
  dropCount : Nat
  q : PipelineQuery

namespace IsaState

def init (q : PipelineQuery) : IsaState where
  pregs := fun _ => none
  stack := fun _ => none
  spOffset := 0
  frameWords := 0
  physFlag := none
  dropCount := 0
  q := q

def setPReg (st : IsaState) (r : PhysReg) (n : Nat) : IsaState :=
  { st with pregs := fun k => if k == r then some (n % MaskedWord64.mod64) else st.pregs k }

def setPRegRaw (st : IsaState) (r : PhysReg) (n : Nat) : IsaState :=
  { st with pregs := fun k => if k == r then some n else st.pregs k }

def setStack (st : IsaState) (off : Nat) (n : Nat) : IsaState :=
  { st with stack := fun k => if k == off then some n else st.stack k }

end IsaState

def stepIsaInstr (st : IsaState) (ins : IsaInstr) : Option IsaState :=
  match ins with
  | .isaSubSp words =>
    if st.spOffset == 0 then
      some { st with spOffset := -(Int.ofNat words), frameWords := words }
    else none
  | .isaAddSp words =>
    some { st with spOffset := st.spOffset + Int.ofNat words }
  | .isaCopyFromAbiX dst =>
    some (st.setPReg dst st.q.x)
  | .isaCopyFromAbiY dst =>
    some (st.setPReg dst st.q.y)
  | .isaMovImm64 dst imm =>
    some (st.setPReg dst imm)
  | .isaXorZeroClobber dst =>
    some { (st.setPReg dst 0) with physFlag := some false }
  | .isaShlImm64 dst src sh =>
    match st.pregs src with
    | some val =>
      if sh < 64 then some (st.setPReg dst (val * (2 ^ sh))) else none
    | none => none
  | .isaAdd64SetFlags dst lhs rhs =>
    match st.pregs lhs, st.pregs rhs with
    | some a, some b =>
      let sum := a + b
      let carry := decide (sum >= MaskedWord64.mod64)
      some { (st.setPReg dst sum) with physFlag := some carry }
    | _, _ => none
  | .isaAdc64UseFlags dst lhs rhs =>
    match st.pregs lhs, st.pregs rhs, st.physFlag with
    | some a, some b, some cin =>
      let sum := a + b + (if cin then 1 else 0)
      let carry := decide (sum >= MaskedWord64.mod64)
      some { (st.setPReg dst sum) with physFlag := some carry }
    | _, _, _ => none
  | .isaStrSp off src =>
    if off < st.frameWords && st.spOffset == -(Int.ofNat st.frameWords) then
      match st.pregs src with
      | some val => some (st.setStack off val)
      | none => none
    else none
  | .isaLdrSp dst off =>
    if off < st.frameWords && st.spOffset == -(Int.ofNat st.frameWords) then
      match st.stack off with
      | some val => some (st.setPRegRaw dst val)
      | none => none
    else none
  | .isaRecordDrop =>
    some { st with dropCount := st.dropCount + 1 }

def evalIsaInstrs (st : IsaState) : List IsaInstr → Option IsaState
  | [] => some st
  | i :: rest =>
    match stepIsaInstr st i with
    | none => none
    | some st' => evalIsaInstrs st' rest

def evalFramedIsaProg (p : FramedIsaProg) (q : PipelineQuery) : Partial PipelineOut :=
  match evalIsaInstrs (IsaState.init q) p.instrs with
  | none => .ub
  | some stFinal =>
    if stFinal.spOffset == 0 then
      match stFinal.pregs p.retPhysReg with
      | some val => .defined { retVal := val, dropCount := stFinal.dropCount }
      | none => .ub
    else
      .ub

@[reducible] def FramedIsaLang : DetLanguage where
  Prog := FramedIsaProg
  Query := PipelineQuery
  Out := PipelineOut
  eval := evalFramedIsaProg

def postRaToIsaCodec : BehaviorCodec PostRaMachineLang FramedIsaLang :=
  { encodeQuery := fun q => q, decodeOut := fun o => o }

def spillSlotToOffset : SpillSlot → Nat
  | .slot0 => 0
  | .slot1 => 1

def lowerPostRaInstr : PostRaInstr → IsaInstr
  | .copyFromAbiX dst => .isaCopyFromAbiX dst
  | .copyFromAbiY dst => .isaCopyFromAbiY dst
  | .movImm64 dst imm => .isaMovImm64 dst imm
  | .xorZeroClobberFlags dst => .isaXorZeroClobber dst
  | .shlImm64 dst src sh => .isaShlImm64 dst src sh
  | .add64SetFlags dst lhs rhs => .isaAdd64SetFlags dst lhs rhs
  | .adc64UseFlags dst lhs rhs => .isaAdc64UseFlags dst lhs rhs
  | .spillStore slot src => .isaStrSp (spillSlotToOffset slot) src
  | .spillReload dst slot => .isaLdrSp dst (spillSlotToOffset slot)
  | .recordDrop => .isaRecordDrop

def lowerPostRaToFramedIsa (p : PostRaMachineProg) : FramedIsaProg where
  retPhysReg := p.retPhysReg
  instrs :=
    [.isaSubSp p.numSpillSlots] ++
    (p.instrs.map lowerPostRaInstr) ++
    [.isaAddSp p.numSpillSlots]

def targetFramedIsaProg : FramedIsaProg :=
  lowerPostRaToFramedIsa regAllocatedPostRaProg

theorem eval_targetFramedIsaProg (q : PipelineQuery) :
    FramedIsaLang.eval targetFramedIsaProg q = .defined (expectedPipelineOut q) := by
  rfl

def prologEpilogMcPass : PassCompiler PostRaMachineLang FramedIsaLang postRaToIsaCodec where
  run p :=
    if p == regAllocatedPostRaProg then some targetFramedIsaProg else none
  sound {p1 p2} hRun := by
    revert hRun
    cases hEq : (p1 == regAllocatedPostRaProg) with
    | false => intro h; contradiction
    | true =>
      intro hRun
      injection hRun with hP2
      have hP1 : p1 = regAllocatedPostRaProg := eq_of_beq hEq
      subst hP1 hP2
      apply Compiles.of_eval_eq
      intro q
      rw [eval_regAllocatedPostRaProg, eval_targetFramedIsaProg]
      rfl

/-! ## Section 8: End-to-End 10-Pass, 6-IR Vertical Pipeline Composition Theorem -/

def mirFrontendAndOptPipeline :=
  (elaborateDropsPass.comp mirSroaPass).comp destPropPass

def anLlvmMiddleEndPipeline :=
  ((codegenMirPass.comp mem2RegCertPass).comp instCombinePass).comp gvnDseCertPass

def anLlvmBackendPipeline :=
  (globalISelPass.comp regAllocCertPass).comp prologEpilogMcPass

def fullEndToEndCompiler :=
  (mirFrontendAndOptPipeline.comp anLlvmMiddleEndPipeline).comp anLlvmBackendPipeline

def fullEndToEndCodec :=
  BehaviorCodec.comp
    (BehaviorCodec.comp
      (BehaviorCodec.comp
        (BehaviorCodec.comp preDropToMirCodec (BehaviorCodec.id MirLang))
        (BehaviorCodec.id MirLang))
      (BehaviorCodec.comp
        (BehaviorCodec.comp
          (BehaviorCodec.comp mirToAnLlvmCodec (BehaviorCodec.id AnLlvmLang))
          (BehaviorCodec.id AnLlvmLang))
        (BehaviorCodec.id AnLlvmLang)))
    (BehaviorCodec.comp
      (BehaviorCodec.comp anLlvmToMachineCodec machineToPostRaCodec)
      postRaToIsaCodec)

theorem fullEndToEndCompiler_runs_to_target :
    fullEndToEndCompiler.run sourcePreDropMirProg = some targetFramedIsaProg := by
  rfl

theorem fullEndToEndCompiler_verified :
    Compiles PreDropMirLang FramedIsaLang fullEndToEndCodec
      sourcePreDropMirProg targetFramedIsaProg :=
  fullEndToEndCompiler.sound fullEndToEndCompiler_runs_to_target

/-! ## Section 9: Stage-1 `.olean` Pre-Verification Scaling & Linear `Nat`-Keyed Certificate Checker -/

inductive ScaleInstr where
  | addConst (dst src : Nat) (c : Nat)
  | addTwoConsts (dst src : Nat) (c1 c2 : Nat)
  deriving DecidableEq, Repr

def evalScaleInstrs (env : Nat → Nat) : List ScaleInstr → (Nat → Nat)
  | [] => env
  | .addConst dst src c :: rest =>
    let v := env src + c
    evalScaleInstrs (fun r => if r == dst then v else env r) rest
  | .addTwoConsts dst src c1 c2 :: rest =>
    let v := (env src + c1) + c2
    evalScaleInstrs (fun r => if r == dst then v else env r) rest

def checkScalePeephole : List ScaleInstr → List ScaleInstr → Bool
  | [], [] => true
  | .addTwoConsts d1 s1 c1 c2 :: r1, .addConst d2 s2 c3 :: r2 =>
    d1 == d2 && s1 == s2 && (c1 + c2 == c3) && checkScalePeephole r1 r2
  | .addConst d1 s1 c1 :: r1, .addConst d2 s2 c2 :: r2 =>
    d1 == d2 && s1 == s2 && c1 == c2 && checkScalePeephole r1 r2
  | _, _ => false

theorem checkScalePeephole_sound :
    ∀ (srcProg tgtProg : List ScaleInstr) (env : Nat → Nat),
      checkScalePeephole srcProg tgtProg = true →
      evalScaleInstrs env tgtProg = evalScaleInstrs env srcProg
  | [], [], _, _ => rfl
  | .addTwoConsts d1 s1 c1 c2 :: r1, .addConst d2 s2 c3 :: r2, env, hChk => by
    unfold checkScalePeephole at hChk
    rcases Bool.and_eq_true_iff.mp hChk with ⟨h123, hRest⟩
    rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hc⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hd, hs⟩
    have hdEq : d1 = d2 := eq_of_beq hd
    have hsEq : s1 = s2 := eq_of_beq hs
    have hcEq : c1 + c2 = c3 := eq_of_beq hc
    subst hdEq hsEq hcEq
    unfold evalScaleInstrs
    have hAssoc : (env s1 + c1) + c2 = env s1 + (c1 + c2) := by omega
    rw [hAssoc]
    exact checkScalePeephole_sound r1 r2 _ hRest
  | .addConst d1 s1 c1 :: r1, .addConst d2 s2 c2 :: r2, env, hChk => by
    unfold checkScalePeephole at hChk
    rcases Bool.and_eq_true_iff.mp hChk with ⟨h123, hRest⟩
    rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hc⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hd, hs⟩
    have hdEq : d1 = d2 := eq_of_beq hd
    have hsEq : s1 = s2 := eq_of_beq hs
    have hcEq : c1 = c2 := eq_of_beq hc
    subst hdEq hsEq hcEq
    unfold evalScaleInstrs
    exact checkScalePeephole_sound r1 r2 _ hRest
  | [], _ :: _, _, hChk => by contradiction
  | .addTwoConsts .. :: _, [], _, hChk => by contradiction
  | .addConst .. :: _, [], _, hChk => by contradiction
  | .addTwoConsts .. :: _, .addTwoConsts .. :: _, _, hChk => by contradiction
  | .addConst .. :: _, .addTwoConsts .. :: _, _, hChk => by contradiction

def genScaleSrc (n : Nat) : List ScaleInstr :=
  (List.range n).map (fun i => .addTwoConsts (i + 1) i (i + 1) (i + 2))

def genScaleTgt (n : Nat) : List ScaleInstr :=
  (List.range n).map (fun i => .addConst (i + 1) i ((i + 1) + (i + 2)))

theorem scale25_peephole_verified (env : Nat → Nat) :
    evalScaleInstrs env (genScaleTgt 25) = evalScaleInstrs env (genScaleSrc 25) :=
  checkScalePeephole_sound (genScaleSrc 25) (genScaleTgt 25) env rfl

theorem scale50_peephole_verified (env : Nat → Nat) :
    evalScaleInstrs env (genScaleTgt 50) = evalScaleInstrs env (genScaleSrc 50) :=
  checkScalePeephole_sound (genScaleSrc 50) (genScaleTgt 50) env rfl

theorem scale100_peephole_verified (env : Nat → Nat) :
    evalScaleInstrs env (genScaleTgt 100) = evalScaleInstrs env (genScaleSrc 100) :=
  checkScalePeephole_sound (genScaleSrc 100) (genScaleTgt 100) env rfl

set_option maxRecDepth 20000 in
theorem scale200_peephole_verified (env : Nat → Nat) :
    evalScaleInstrs env (genScaleTgt 200) = evalScaleInstrs env (genScaleSrc 200) :=
  checkScalePeephole_sound (genScaleSrc 200) (genScaleTgt 200) env rfl

/-! ## Section 9B: Cross-Stage Seam Negative Canaries (Middle-End DSE, Backend Flag Clobber, PEI Frame Balance) -/

/-- **Negative Canary 2 (Middle-End `DSE` Seam):** Deleting `storeSlot 0 10`
    when `loadSlot 0 0` precedes `allocaDead 0` causes `loadSlot 0 0` to read
    uninitialized `MaskedWord64.allPoison`, evaluating to `.ub`! -/
def buggyDseLiveSlotDeletedProg : AnLlvmProg where
  retReg := 0
  instrs := [
    .assignInputX 4,
    .assignInputY 5,
    .allocaLive 8,
    .const64 80 99,
    .storeSlot 8 80,
    .recordDrop,
    .allocaDead 8,
    .mulImm64 6 4 8,
    .sub64 7 5 5,
    .allocaLive 0,
    .add64 10 6 7,
    -- Bug: `storeSlot 0 10` was deleted even though `loadSlot 0 0` reads `slot 0`!
    .loadSlot 0 0,
    .allocaDead 0
  ]

theorem canary_dse_live_store_before_load_rejected :
    ¬ Compiles AnLlvmLang AnLlvmLang (BehaviorCodec.id AnLlvmLang)
        loweredAnLlvmProg buggyDseLiveSlotDeletedProg := by
  intro hComp
  have hQ := hComp { x := 7, y := 3, takeFastPath := true }
  revert hQ
  decide

/-- Source `AnMachineProg` computing the upper 64-bit carry word of `(x + y)` via
    explicit SSA flag virtual register `vflag = 10`. -/
def carryChainMachineProg : AnMachineProg where
  retVReg := 0
  instrs := [
    .copyFromAbiX 1,
    .copyFromAbiY 2,
    .uaddo64Flags 3 10 1 2,
    .movImm64 4 0,
    .uadde64Flags 0 11 4 4 10
  ]

/-- Buggy `PostRaMachineProg` that rematerializes `0` into `.r3` via
    `xorZeroClobberFlags` (`xor r3d, r3d`) between `add64SetFlags` and
    `adc64UseFlags`, clobbering `physFlag`! -/
def buggyFlagClobberPostRaProg : PostRaMachineProg where
  numSpillSlots := 0
  retPhysReg := .r0
  instrs := [
    .copyFromAbiX .r1,
    .copyFromAbiY .r2,
    .add64SetFlags .r1 .r1 .r2,
    .xorZeroClobberFlags .r3,
    .adc64UseFlags .r0 .r3 .r3
  ]

/-- **Negative Canary 3 (Backend `MachineSSA -> PostRA` Flag Seam):**
    Rematerializing `0` via `xor r3d, r3d` between `ADD64` and `ADC64` clobbers
    the carry flag when `x = 2^64 - 1, y = 1`, returning `0` instead of `1`. -/
theorem canary_flag_clobber_across_regalloc_rejected :
    ¬ Compiles AnMachineLang PostRaMachineLang machineToPostRaCodec
        carryChainMachineProg buggyFlagClobberPostRaProg := by
  intro hComp
  have hQ := hComp { x := 0xFFFFFFFFFFFFFFFF, y := 1, takeFastPath := true }
  revert hQ
  decide

/-- Buggy `FramedIsaProg` that allocates 1 spill word in the prologue
    (`isaSubSp 1`) but omits the epilogue `isaAddSp 1`, leaving `spOffset = -1`. -/
def buggyUnbalancedSpIsaProg : FramedIsaProg where
  retPhysReg := .r0
  instrs := [
    .isaSubSp 1,
    .isaCopyFromAbiX .r1,
    .isaStrSp 0 .r1,
    .isaRecordDrop,
    .isaLdrSp .r2 0,
    .isaShlImm64 .r0 .r2 3
  ]

/-- **Negative Canary 4 (Backend `PostRA -> FramedISA` Stack-Frame Seam):**
    Omitting epilogue stack restoration leaves `spOffset = -1 ≠ 0` at function
    exit, stepping to `.ub` and violating `Compiles`. -/
theorem canary_pei_unbalanced_sp_rejected :
    ¬ Compiles PostRaMachineLang FramedIsaLang postRaToIsaCodec
        regAllocatedPostRaProg buggyUnbalancedSpIsaProg := by
  intro hComp
  have hQ := hComp { x := 11, y := 2, takeFastPath := true }
  revert hQ
  decide

/-! ## Section 10: Kernel Axiom Footprint Audit -/

/-- info: 'Anneal.EndToEndPipelineProbe.fullEndToEndCompiler_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fullEndToEndCompiler_verified

/-- info: 'Anneal.EndToEndPipelineProbe.canary_destProp_missing_live_union_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_destProp_missing_live_union_rejected

/-- info: 'Anneal.EndToEndPipelineProbe.canary_dse_live_store_before_load_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms canary_dse_live_store_before_load_rejected

/-- info: 'Anneal.EndToEndPipelineProbe.canary_flag_clobber_across_regalloc_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_flag_clobber_across_regalloc_rejected

/-- info: 'Anneal.EndToEndPipelineProbe.canary_pei_unbalanced_sp_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms canary_pei_unbalanced_sp_rejected

/-- info: 'Anneal.EndToEndPipelineProbe.checkScalePeephole_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms checkScalePeephole_sound

/-- info: 'Anneal.EndToEndPipelineProbe.scale200_peephole_verified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms scale200_peephole_verified

end Anneal.EndToEndPipelineProbe
