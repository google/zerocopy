-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Single-Source Artifact Binding Prototype for `mir-to-x86`

Mechanizes the single-source artifact binding architecture in Lean 4 (`v4.34.1`):
1. `Mir` contains **only** the captured `MirCrate` (`MirBody` ASTs), removing
   the unverified Rust MIR-to-x86 lowering from `trusted/rustc-capture`.
2. `Theory` compiles `MirCrate` to `X86Crate` (`compileStage0`) and applies
   verified in-Lean optimization (`optimizePeephole`).
3. `Trusted.emitX86CrateAsm : X86Crate → String` is the single deterministic
   assembly serializer in the system.
4. `Trusted.CrateTheorem` binds `(mirCrate : MirCrate)`, `(x86Crate : X86Crate)`,
   and `(asmText : String)` via a kernel-checked equality obligation
   `Trusted.emitX86CrateAsm x86Crate = asmText` discharged by `rfl`, while
   `AuditMain.lean` inspects the compiled `.olean` kernel `Environment` and
   verifies that `Prog.asmText` is an `Expr.lit (.strVal s)` matching `Prog.s`
   on disk byte-for-byte.
-/

namespace Trusted

inductive MirBinOp where
  | add
  | sub
  deriving DecidableEq, Repr

inductive MirStmt where
  | assignArg (dstSlot : Nat)
  | assignBinOp (op : MirBinOp) (dstSlot lhsSlot rhsSlot : Nat)
  deriving DecidableEq, Repr

structure MirBody where
  fnName : String
  slotCount : Nat
  stmts : List MirStmt
  retSlot : Nat
  deriving DecidableEq, Repr

structure MirCrate where
  fns : List MirBody
  deriving DecidableEq, Repr

inductive X86Reg where
  | rax
  | rcx
  | rdi
  deriving DecidableEq, Repr

inductive X86Instr where
  | movRegToSlot (dstSlot : Nat) (src : X86Reg)
  | movSlotToReg (dst : X86Reg) (srcSlot : Nat)
  | addRegReg (dst src : X86Reg)
  | subRegReg (dst src : X86Reg)
  deriving DecidableEq, Repr

inductive X86Term where
  | retFromSlot (slot : Nat)
  | abortPanic
  deriving DecidableEq, Repr

structure X86Body where
  fnName : String
  slotCount : Nat
  instrs : List X86Instr
  term : X86Term
  deriving DecidableEq, Repr

structure X86Crate where
  fns : List X86Body
  deriving DecidableEq, Repr

/-- Deterministic slot offset in bytes (`8 * (slot + 1)`). -/
def slotByteOffset (slot : Nat) : Nat :=
  (slot + 1) * 8

/-- Aligns the stack frame size to a 16-byte boundary. -/
def alignedFrameBytes (slotCount : Nat) : Nat :=
  let raw := slotCount * 8
  ((raw + 15) / 16) * 16

def emitReg : X86Reg → String
  | .rax => "rax"
  | .rcx => "rcx"
  | .rdi => "rdi"

def emitInstr : X86Instr → String
  | .movRegToSlot dst src =>
    s!"    mov QWORD PTR [rbp - {slotByteOffset dst}], {emitReg src}\n"
  | .movSlotToReg dst src =>
    s!"    mov {emitReg dst}, QWORD PTR [rbp - {slotByteOffset src}]\n"
  | .addRegReg dst src =>
    s!"    add {emitReg dst}, {emitReg src}\n"
  | .subRegReg dst src =>
    s!"    sub {emitReg dst}, {emitReg src}\n"

def emitTerm (frameBytes : Nat) : X86Term → String
  | .retFromSlot slot =>
    let loadRet := s!"    mov rax, QWORD PTR [rbp - {slotByteOffset slot}]\n"
    let dealloc :=
      if frameBytes == 0 then ""
      else s!"    add rsp, {frameBytes}\n"
    loadRet ++ dealloc ++ "    pop rbp\n    ret\n"
  | .abortPanic =>
    "    call abort\n"

def emitX86BodyAsm (b : X86Body) : String :=
  let frameBytes := alignedFrameBytes b.slotCount
  let header :=
    s!".globl anneal_{b.fnName}\n" ++
    s!".type anneal_{b.fnName}, @function\n" ++
    s!"anneal_{b.fnName}:\n" ++
    "    push rbp\n" ++
    "    mov rbp, rsp\n" ++
    (if frameBytes == 0 then "" else s!"    sub rsp, {frameBytes}\n")
  let body := String.join (b.instrs.map emitInstr)
  let footer := emitTerm frameBytes b.term
  header ++ body ++ footer

/-- Total, deterministic in-Lean x86-64 assembly emitter. -/
def emitX86CrateAsm (c : X86Crate) : String :=
  let prelude := ".intel_syntax noprefix\n.text\n\n"
  let bodies := String.intercalate "\n" (c.fns.map emitX86BodyAsm)
  let noteStack := "\n.section .note.GNU-stack,\"\",@progbits\n"
  prelude ++ bodies ++ noteStack

/-- Big-step 64-bit modular semantics for our prototype subset. -/
def evalMirStmt (arg : UInt64) (env : Nat → UInt64) : MirStmt → (Nat → UInt64)
  | .assignArg dst => fun s => if s == dst then arg else env s
  | .assignBinOp .add dst l r =>
    let v := env l + env r
    fun s => if s == dst then v else env s
  | .assignBinOp .sub dst l r =>
    let v := env l - env r
    fun s => if s == dst then v else env s

def evalMirBody (b : MirBody) (arg : UInt64) : UInt64 :=
  let finalEnv := b.stmts.foldl (evalMirStmt arg) (fun _ => 0)
  finalEnv b.retSlot

structure MachState where
  rax : UInt64 := 0
  rcx : UInt64 := 0
  rdi : UInt64 := 0
  slots : Nat → UInt64 := fun _ => 0

def readReg (st : MachState) : X86Reg → UInt64
  | .rax => st.rax
  | .rcx => st.rcx
  | .rdi => st.rdi

def writeReg (st : MachState) (r : X86Reg) (v : UInt64) : MachState :=
  match r with
  | .rax => { st with rax := v }
  | .rcx => { st with rcx := v }
  | .rdi => { st with rdi := v }

def stepInstr (st : MachState) : X86Instr → MachState
  | .movRegToSlot dst src =>
    let v := readReg st src
    { st with slots := fun s => if s == dst then v else st.slots s }
  | .movSlotToReg dst src =>
    writeReg st dst (st.slots src)
  | .addRegReg dst src =>
    writeReg st dst (readReg st dst + readReg st src)
  | .subRegReg dst src =>
    writeReg st dst (readReg st dst - readReg st src)

def evalX86Body (b : X86Body) (arg : UInt64) : Option UInt64 :=
  let init : MachState := { rdi := arg }
  let final := b.instrs.foldl stepInstr init
  match b.term with
  | .retFromSlot slot => some (final.slots slot)
  | .abortPanic => none

/-- Structural pairwise relational obligation over lists. -/
def Forall2 (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

/-- Single-source crate theorem binding `MirCrate`, `X86Crate`, and `asmText`. -/
structure CrateTheorem
    (mc : MirCrate)
    (xc : X86Crate)
    (asmText : String) : Prop where
  /-- Every compiled function refines its source MIR semantics on all inputs. -/
  refines :
    Forall2
      (fun mb xb =>
        mb.fnName = xb.fnName ∧
        ∀ arg : UInt64, evalX86Body xb arg = some (evalMirBody mb arg))
      mc.fns
      xc.fns
  /-- Kernel-checked commitment that `asmText` is the exact output of
  `emitX86CrateAsm xc`. -/
  asm_eq : emitX86CrateAsm xc = asmText

end Trusted

namespace Theory

open Trusted

def compileStmt : MirStmt → List X86Instr
  | .assignArg dst =>
    [.movRegToSlot dst .rdi, .movSlotToReg .rax dst, .movRegToSlot dst .rax]
  | .assignBinOp .add dst l r =>
    [.movSlotToReg .rax l, .movSlotToReg .rcx r, .addRegReg .rax .rcx, .movRegToSlot dst .rax]
  | .assignBinOp .sub dst l r =>
    [.movSlotToReg .rax l, .movSlotToReg .rcx r, .subRegReg .rax .rcx, .movRegToSlot dst .rax]

def compileStage0 (b : MirBody) : X86Body :=
  { fnName := b.fnName
    slotCount := b.slotCount
    instrs := (b.stmts.map compileStmt).flatten
    term := .retFromSlot b.retSlot }

/-- Peephole optimizer eliminating redundant `mov reg, [slot]; mov [slot], reg`
pairs in `Theory`, written via `List.foldr` (`List.rec`) so that it reduces
definitionally (`rfl`) inside the Lean 4 kernel without triggering
`WellFounded.fix` recursion-depth limits. -/
def peepholeStep (i1 : X86Instr) (acc : List X86Instr) : List X86Instr :=
  match i1, acc with
  | .movSlotToReg r1 s1, .movRegToSlot s2 r2 :: tail =>
    if r1 == r2 && s1 == s2 then
      tail
    else
      i1 :: acc
  | _, _ => i1 :: acc

def peepholeInstrs (instrs : List X86Instr) : List X86Instr :=
  instrs.foldr peepholeStep []

def optimizePeephole (b : X86Body) : X86Body :=
  { b with instrs := peepholeInstrs b.instrs }

def compileAndOptimizeCrate (mc : MirCrate) : X86Crate :=
  { fns := mc.fns.map (fun b => optimizePeephole (compileStage0 b)) }

end Theory

namespace Mir

open Trusted

/-- Captured MIR crate (contains ONLY `MirBody`, no pre-lowered `X86Body`). -/
def double_fn : MirBody :=
  { fnName := "double_u64"
    slotCount := 2
    stmts := [.assignArg 0, .assignBinOp .add 1 0 0]
    retSlot := 1 }

def crate : MirCrate :=
  { fns := [double_fn] }

end Mir

namespace Prog

open Trusted Theory

/-- The compiled + peephole-optimized x86 crate produced inside Lean. -/
def x86Crate : X86Crate :=
  compileAndOptimizeCrate Mir.crate

/-- The exact assembly artifact string literal committed in the `.olean`
environment (`Expr.lit (.strVal s)`). -/
def asmText : String :=
".intel_syntax noprefix
.text

.globl anneal_double_u64
.type anneal_double_u64, @function
anneal_double_u64:
    push rbp
    mov rbp, rsp
    sub rsp, 16
    mov QWORD PTR [rbp - 8], rdi
    mov rax, QWORD PTR [rbp - 8]
    mov rcx, QWORD PTR [rbp - 8]
    add rax, rcx
    mov QWORD PTR [rbp - 16], rax
    mov rax, QWORD PTR [rbp - 16]
    add rsp, 16
    pop rbp
    ret

.section .note.GNU-stack,\"\",@progbits
"

end Prog

namespace Proof

open Trusted

set_option maxRecDepth 20000 in
theorem verify_crate : CrateTheorem Mir.crate Prog.x86Crate Prog.asmText := by
  refine ⟨?_, rfl⟩
  exact ⟨⟨rfl, fun _ => rfl⟩, trivial⟩

end Proof
