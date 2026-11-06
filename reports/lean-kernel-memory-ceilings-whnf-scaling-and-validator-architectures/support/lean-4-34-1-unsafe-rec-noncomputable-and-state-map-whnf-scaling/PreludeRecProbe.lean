-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.List.Basic

/-!
# Prelude-Only Computable Recursion Probe (`PreludeRecProbe.lean`)

Tests defining computable, kernel-reducible recursive functions over custom
recursive inductives (`MirVal`, `X86Val`) and mutually recursive AST inductives
(`Terminator`, `BasicBlock`, `MirBody`) in `prelude`-only Lean 4.34.1 using only
locked `foundation` imports (`Init.NotationExtra`, `Init.Data.Nat.Basic`,
`Init.Data.List.Basic`) such that:

1. Zero `isUnsafe` or `isPartial` (`._unsafe_rec`) constants are emitted into
   `ModuleData.constants` (`env.checked`).
2. All definitions are computable (`def`, not `noncomputable def`).
3. Closed applications reduce in the Lean 4 kernel via `rfl` and `decide`.
-/

namespace ClusterA1Probe

/-- Index of a MIR local variable (`_0`, `_1`, ...). -/
structure LocalId where
  index : Nat
  deriving DecidableEq

/-- Index of a MIR basic block (`bb0`, `bb1`, ...). -/
structure BlockId where
  index : Nat
  deriving DecidableEq

/-- Index of an x86-64 stack-frame slot (`[rbp - 8 * (slot + 1)]`). -/
structure SlotId where
  index : Nat
  deriving DecidableEq

/-- Index of an x86-64 basic-block label (`.Lbb0`, `.Lbb1`, ...). -/
structure BlockLabel where
  index : Nat
  deriving DecidableEq

/-- MIR type grammar. -/
inductive MirTy where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)
  deriving DecidableEq

/-- x86-64 type grammar. -/
inductive X86Ty where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)
  deriving DecidableEq

/-- Custom recursive inductive representing an initialized MIR runtime value.
    Note: `deriving DecidableEq` on a recursive inductive synthesizes a
    computable recursive `instDecidableEqMirVal.decEq` and emits
    `instDecidableEqMirVal.decEq._unsafe_rec` (`isPartial = true`), so we
    intentionally omit `deriving DecidableEq` here and define fuel-bounded
    boolean equality via `Nat.repeat` below. -/
inductive MirVal where
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (loc : LocalId)

/-- Custom recursive inductive representing an initialized x86-64 value. -/
inductive X86Val where
  | word64 (bits : Nat)
  | boolVal (b : Bool)
  | unit
  | adt (id : Nat) (inner : X86Val)
  | bytes (sz : Nat) (bits : Nat)
  | stackPtr (slot : SlotId)

/-- MIR operand. -/
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

/-- x86-64 operand. -/
inductive X86Operand where
  | stackSlot (slot : SlotId) (deinit : Bool)
  | imm (val : X86Val)

/-- MIR statement. -/
inductive Stmt where
  | assignUse (dst : LocalId) (op : Operand)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | nop

/-- x86-64 instruction. -/
inductive X86Instr where
  | mov (dst : SlotId) (src : X86Operand)
  | allocSlot (slot : SlotId)
  | deallocSlot (slot : SlotId)
  | nop

mutual
  /-- Mutually recursive MIR terminator. -/
  inductive Terminator where
    | return_
    | goto (target : BlockId)
    | unreachable
    | panic
    | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
    | callSizeOf (dst : LocalId) (ty : MirTy) (target : BlockId)
    | call1 (dst : LocalId) (callee : MirBody) (arg : Operand) (target : BlockId)

  /-- MIR basic block. -/
  structure BasicBlock where
    stmts : List Stmt
    terminator : Terminator

  /-- Mutually recursive MIR procedure body. -/
  structure MirBody where
    argTys : List MirTy
    retTy : MirTy
    localCount : Nat
    blocks : List BasicBlock
    requiredConsts : List MirBody := []
end

mutual
  /-- Mutually recursive x86-64 terminator. -/
  inductive X86Term where
    | ret
    | jmp (target : BlockLabel)
    | ud2
    | abortPanic
    | jccBool (cond : X86Operand) (falseTarget : BlockLabel) (trueTarget : BlockLabel)
    | movSizeOfJmp (dst : SlotId) (ty : X86Ty) (target : BlockLabel)
    | call1 (dst : SlotId) (callee : X86Body) (arg : X86Operand) (target : BlockLabel)

  /-- x86-64 basic block. -/
  structure X86Block where
    instrs : List X86Instr
    term : X86Term

  /-- Mutually recursive x86-64 procedure body. -/
  structure X86Body where
    argTys : List X86Ty
    retTy : X86Ty
    slotCount : Nat
    blocks : List X86Block
    requiredConsts : List X86Body := []
end

/-!
## 1. Non-Recursive Helpers
-/

/-- Lower `MirTy` to `X86Ty` (non-recursive computable `def`). -/
def compileTy (ty : MirTy) : X86Ty :=
  match ty with
  | .usize => .usize
  | .bool => .bool
  | .unit => .unit
  | .adt id => .adt id
  | .param idx => .param idx
  | .refParam idx => .refParam idx

/-- Lift `X86Ty` to `MirTy` (non-recursive computable `def`). -/
def decompileTy (ty : X86Ty) : MirTy :=
  match ty with
  | .usize => .usize
  | .bool => .bool
  | .unit => .unit
  | .adt id => .adt id
  | .param idx => .param idx
  | .refParam idx => .refParam idx

/-!
## 2. Technique A1: `Nat.repeat` Combinator (`Init.Data.Nat.Basic`)

Because `compileValStep` and `compileValRepeat` do not reference their own
declaration names, `Lean.Elab.isNonRecursive` returns `true`, routing both
through `addAndCompileNonRec` with zero `._unsafe_rec` constants.
-/

/-- Single open step of `compileVal` parameterized by the recursive continuation
    `recStep`. Uses `MirVal.casesOn` (`isCasesOnLike = true`), which LCNF
    lowers directly to a `.cases` branch. -/
def compileValStep (recStep : MirVal → X86Val) (v : MirVal) : X86Val :=
  match v with
  | .usize bits => .word64 bits
  | .bool b => .boolVal b
  | .unit => .unit
  | .adt id inner => .adt id (recStep inner)
  | .bytes sz bits => .bytes sz bits
  | .ref loc => .stackPtr ⟨loc.index⟩

/-- Computable fuel-bounded `compileVal` via `Nat.repeat` with zero
    `._unsafe_rec` companions. -/
def compileValRepeat (fuel : Nat) (v : MirVal) : X86Val :=
  Nat.repeat compileValStep fuel (fun _ => .unit) v

/-- Single open step of `decompileVal`. -/
def decompileValStep (recStep : X86Val → MirVal) (v : X86Val) : MirVal :=
  match v with
  | .word64 bits => .usize bits
  | .boolVal b => .bool b
  | .unit => .unit
  | .adt id inner => .adt id (recStep inner)
  | .bytes sz bits => .bytes sz bits
  | .stackPtr slot => .ref ⟨slot.index⟩

/-- Computable fuel-bounded `decompileVal` via `Nat.repeat`. -/
def decompileValRepeat (fuel : Nat) (v : X86Val) : MirVal :=
  Nat.repeat decompileValStep fuel (fun _ => .unit) v

/-- Computable `compileOperand` parameterized by `valFuel`. -/
def compileOperandRepeat (valFuel : Nat) (op : Operand) : X86Operand :=
  match op with
  | .copy src => .stackSlot ⟨src.index⟩ false
  | .move src => .stackSlot ⟨src.index⟩ true
  | .constVal val => .imm (compileValRepeat valFuel val)

/-- Computable `compileStmt` parameterized by `valFuel`. -/
def compileStmtRepeat (valFuel : Nat) (stmt : Stmt) : X86Instr :=
  match stmt with
  | .assignUse dst op => .mov ⟨dst.index⟩ (compileOperandRepeat valFuel op)
  | .storageLive loc => .allocSlot ⟨loc.index⟩
  | .storageDead loc => .deallocSlot ⟨loc.index⟩
  | .nop => .nop

/-- Single open step of `compileTerminator` parameterized by `compileBodyRec`. -/
def compileTerminatorStep (valFuel : Nat) (compileBodyRec : MirBody → X86Body)
    (term : Terminator) : X86Term :=
  match term with
  | .return_ => .ret
  | .goto target => .jmp ⟨target.index⟩
  | .unreachable => .ud2
  | .panic => .abortPanic
  | .switchInt discr falseTarget trueTarget =>
    .jccBool (compileOperandRepeat valFuel discr) ⟨falseTarget.index⟩ ⟨trueTarget.index⟩
  | .callSizeOf dst ty target =>
    .movSizeOfJmp ⟨dst.index⟩ (compileTy ty) ⟨target.index⟩
  | .call1 dst callee arg target =>
    .call1 ⟨dst.index⟩ (compileBodyRec callee) (compileOperandRepeat valFuel arg)
      ⟨target.index⟩

/-- Single open step of `compileBlock` using `List.map` from `Init.Prelude`. -/
def compileBlockStep (valFuel : Nat) (compileBodyRec : MirBody → X86Body)
    (bb : BasicBlock) : X86Block :=
  match bb with
  | ⟨stmts, terminator⟩ => {
      instrs := stmts.map (compileStmtRepeat valFuel)
      term := compileTerminatorStep valFuel compileBodyRec terminator
    }

/-- Single open step of `compileStage0` over the mutual `MirBody` /
    `BasicBlock` / `Terminator` group, using `List.map` on `blocks` and
    `requiredConsts`. -/
def compileStage0Step (valFuel : Nat) (compileBodyRec : MirBody → X86Body)
    (body : MirBody) : X86Body :=
  match body with
  | ⟨argTys, retTy, localCount, blocks, requiredConsts⟩ => {
      argTys := argTys.map compileTy
      retTy := compileTy retTy
      slotCount := localCount
      blocks := blocks.map (compileBlockStep valFuel compileBodyRec)
      requiredConsts := requiredConsts.map compileBodyRec
    }

/-- Default fallback `X86Body` when call-depth fuel is exhausted. -/
def emptyX86Body : X86Body :=
  { argTys := [], retTy := .unit, slotCount := 0, blocks := [], requiredConsts := [] }

/-- Computable fuel-bounded `compileStage0` via `Nat.repeat` with zero
    `._unsafe_rec` companions. -/
def compileStage0Repeat (bodyFuel valFuel : Nat) (body : MirBody) : X86Body :=
  Nat.repeat (compileStage0Step valFuel) bodyFuel (fun _ => emptyX86Body) body

/-!
## 3. Technique A2: `Nat.rec` Combinator (`@[csimp] Nat.rec_eq_recCompiled`)

Because `Init.Data.Nat.Basic` registers `@[csimp] theorem Nat.rec_eq_recCompiled :
@Nat.rec = @Nat.recCompiled`, calling `Nat.rec` inside a non-recursive `def`
replaces `Nat.rec` with `Nat.recCompiled` during `ToDecl` / `ToLCNF` and
compiles cleanly with zero `._unsafe_rec` companions in this module.
-/

/-- Computable fuel-bounded `compileVal` defined directly via `Nat.rec`. -/
def compileValNatRec (fuel : Nat) : MirVal → X86Val :=
  Nat.rec
    (fun _ => .unit)
    (fun _ ih v => compileValStep ih v)
    fuel

/-- Computable fuel-bounded `compileStage0` defined directly via `Nat.rec`. -/
def compileStage0NatRec (bodyFuel valFuel : Nat) : MirBody → X86Body :=
  Nat.rec
    (fun _ => emptyX86Body)
    (fun _ ih body => compileStage0Step valFuel ih body)
    bodyFuel

/-!
## 4. Technique A3: `List.foldr` Combinator (`Init.Prelude`)

Calls `List.foldr` from `Init.Prelude` over a list of fuel tokens `List Unit`.
-/

/-- Computable `compileVal` defined via `List.foldr` from `Init.Prelude`. -/
def compileValFoldr (fuelTokens : List Unit) (v : MirVal) : X86Val :=
  fuelTokens.foldr (fun _ acc => compileValStep acc) (fun _ => .unit) v

/-!
## 5. Technique A4: `Prop`-Valued Direct Custom Recursor (`MirVal.rec`)

Because `Lean.Compiler.LCNF.shouldGenerateCode` (`Lean/Compiler/LCNF/Main.lean:31-50`)
returns `false` whenever `Meta.isProp info.type` is `true`, a non-recursive
`Prop`-valued `def` can invoke `MirVal.rec` directly without `noncomputable` and
without emitting any `._unsafe_rec` companion!
-/

/-- Exact structural depth bound predicate on `MirVal` defined via `MirVal.rec`
    as a computable (non-`noncomputable`) `def` with zero `._unsafe_rec`
    companions. -/
def mirValBoundedBy (v : MirVal) : Nat → Prop :=
  MirVal.rec
    (motive := fun _ => Nat → Prop)
    (fun _ d => 0 < d)
    (fun _ d => 0 < d)
    (fun d => 0 < d)
    (fun _ _ ih d => match d with | 0 => False | d' + 1 => ih d')
    (fun _ _ d => 0 < d)
    (fun _ d => 0 < d)
    v

/-!
## 6. Reference `noncomputable def` Structural Definitions
-/

/-- Unbounded structural `compileVal` marked `noncomputable def`. -/
noncomputable def compileValNC (v : MirVal) : X86Val :=
  match v with
  | .usize bits => .word64 bits
  | .bool b => .boolVal b
  | .unit => .unit
  | .adt id inner => .adt id (compileValNC inner)
  | .bytes sz bits => .bytes sz bits
  | .ref loc => .stackPtr ⟨loc.index⟩

/-- Unbounded structural `decompileVal` marked `noncomputable def`. -/
noncomputable def decompileValNC (v : X86Val) : MirVal :=
  match v with
  | .word64 bits => .usize bits
  | .boolVal b => .bool b
  | .unit => .unit
  | .adt id inner => .adt id (decompileValNC inner)
  | .bytes sz bits => .bytes sz bits
  | .stackPtr slot => .ref ⟨slot.index⟩

/-- Unbounded structural depth of a `MirVal` marked `noncomputable def`. -/
noncomputable def mirValDepth : MirVal → Nat
  | .adt _ inner => mirValDepth inner + 1
  | _ => 1

/-- Adequacy theorem: for every `v : MirVal` and `fuel` such that
    `mirValDepth v ≤ fuel`, `compileValRepeat fuel v` is equal to the
    unbounded structural `compileValNC v`. -/
theorem compileValRepeat_eq_compileValNC (v : MirVal) :
    ∀ fuel, mirValDepth v ≤ fuel → compileValRepeat fuel v = compileValNC v := by
  induction v with
  | usize bits =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k => rfl
  | bool b =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k => rfl
  | unit =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k => rfl
  | adt id inner ih =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k =>
      change X86Val.adt id (compileValRepeat k inner) = X86Val.adt id (compileValNC inner)
      have hk : mirValDepth inner ≤ k := Nat.le_of_succ_le_succ hle
      rw [ih k hk]
  | bytes sz bits =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k => rfl
  | ref loc =>
    intro fuel hle
    cases fuel with
    | zero => cases hle
    | succ k => rfl

/-!
## 7. Closed-Term Kernel `rfl` and `decide` Verification
-/

/-- Single open step of boolean equality on `X86Val` for `decide` tests. -/
def beqX86ValStep (recStep : X86Val → X86Val → Bool) (a b : X86Val) : Bool :=
  match a, b with
  | .word64 x, .word64 y => x == y
  | .boolVal x, .boolVal y => x == y
  | .unit, .unit => true
  | .adt id1 v1, .adt id2 v2 => (id1 == id2) && recStep v1 v2
  | .bytes sz1 b1, .bytes sz2 b2 => (sz1 == sz2) && (b1 == b2)
  | .stackPtr s1, .stackPtr s2 => s1 == s2
  | _, _ => false

/-- Computable fuel-bounded boolean equality on `X86Val` via `Nat.repeat` with
    zero `._unsafe_rec` companions. -/
def beqX86ValRepeat (fuel : Nat) (a b : X86Val) : Bool :=
  Nat.repeat beqX86ValStep fuel (fun _ _ => false) a b

/-- Nested ADT value of depth 4 for closed-term reduction tests. -/
def sampleMirVal : MirVal :=
  .adt 1 (.adt 2 (.adt 3 (.usize 42)))

/-- Expected lowered `X86Val` for `sampleMirVal`. -/
def sampleX86Val : X86Val :=
  .adt 1 (.adt 2 (.adt 3 (.word64 42)))

theorem test_compileValRepeat_rfl :
    compileValRepeat 8 sampleMirVal = sampleX86Val :=
  rfl

theorem test_compileValRepeat_decide :
    beqX86ValRepeat 8 (compileValRepeat 8 sampleMirVal) sampleX86Val = true := by
  decide

theorem test_decompile_compile_repeat_rfl :
    decompileValRepeat 8 (compileValRepeat 8 sampleMirVal) = sampleMirVal :=
  rfl

theorem test_compileValNatRec_rfl :
    compileValNatRec 8 sampleMirVal = sampleX86Val :=
  rfl

theorem test_compileValNatRec_decide :
    beqX86ValRepeat 8 (compileValNatRec 8 sampleMirVal) sampleX86Val = true := by
  decide

theorem test_compileValFoldr_rfl :
    compileValFoldr [(), (), (), (), ()] sampleMirVal = sampleX86Val :=
  rfl

theorem test_compileValFoldr_decide :
    beqX86ValRepeat 8 (compileValFoldr [(), (), (), (), ()] sampleMirVal) sampleX86Val = true := by
  decide

theorem test_compileValNC_rfl :
    compileValNC sampleMirVal = sampleX86Val :=
  rfl

theorem test_compileValNC_decide :
    beqX86ValRepeat 8 (compileValNC sampleMirVal) sampleX86Val = true := by
  decide

/-- Sample nested `MirBody` with both a `Terminator.call1` callee and a
    `requiredConsts` entry to test mutual recursion reduction. -/
def sampleCalleeMirBody : MirBody := {
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [{
    stmts := [.assignUse ⟨0⟩ (.copy ⟨1⟩)]
    terminator := .return_
  }]
  requiredConsts := []
}

def sampleOuterMirBody : MirBody := {
  argTys := [.adt 1]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨2⟩, .assignUse ⟨2⟩ (.constVal sampleMirVal)]
      terminator := .call1 ⟨0⟩ sampleCalleeMirBody (.move ⟨2⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := [sampleCalleeMirBody]
}

def sampleCalleeX86Body : X86Body := {
  argTys := [.usize]
  retTy := .usize
  slotCount := 2
  blocks := [{
    instrs := [.mov ⟨0⟩ (.stackSlot ⟨1⟩ false)]
    term := .ret
  }]
  requiredConsts := []
}

def sampleOuterX86Body : X86Body := {
  argTys := [.adt 1]
  retTy := .usize
  slotCount := 3
  blocks := [
    { instrs := [.allocSlot ⟨2⟩, .mov ⟨2⟩ (.imm sampleX86Val)]
      term := .call1 ⟨0⟩ sampleCalleeX86Body (.stackSlot ⟨2⟩ true) ⟨1⟩ },
    { instrs := [.deallocSlot ⟨2⟩]
      term := .ret }
  ]
  requiredConsts := [sampleCalleeX86Body]
}

theorem test_compileStage0Repeat_rfl :
    compileStage0Repeat 4 8 sampleOuterMirBody = sampleOuterX86Body :=
  rfl

theorem test_compileStage0NatRec_rfl :
    compileStage0NatRec 4 8 sampleOuterMirBody = sampleOuterX86Body :=
  rfl

theorem test_mirValBoundedBy_rfl :
    mirValBoundedBy sampleMirVal 5 = (0 < 2) :=
  rfl

end ClusterA1Probe
