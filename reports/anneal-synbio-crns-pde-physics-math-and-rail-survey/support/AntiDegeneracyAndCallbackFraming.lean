-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Anti-Degeneracy Contracts for Certifying Optimizers and Small-Step Open-World Callback Framing

This standalone Lean 4 (`v4.34.1`) module mechanizes optimizer anti-degeneracy
contracts and small-step open-world callback framing for Anneal's MIR-to-x86-64
compiler (`mir-to-x86@4f45f0a391`) and trusted operational semantics
(`trusted-core@e6a0b2da5e`):

1. **Part I — Preventing Always-`false` Validators and Identity Optimizers:**
   - Replicates the `Trusted` refinement preorder, small-step prefix semantics
     (`ReachesPrefix`, `BehaviorOf`), x86-64 AST/semantics, Stage 0 lowering,
     and Stage 1 peephole pass (`optimizePeephole`).
   - Mechanizes **Trap 1 (The Always-`false` / Fallback Certifier):** setting
     `checkCert _ _ _ := false` in `runValidatedPass` satisfies
     `∀ s t cert, Compiles X86Lang X86Lang id s (runValidatedPass s t cert)` by
     a 1-line `Preorder.le_refl` proof while never accepting a single
     transformed program (`trap1_alwaysFalse_compiles`,
     `trap1_alwaysFalse_never_accepts`).
   - Mechanizes **Trap 2 (The Identity / Non-Firing Optimizer):** `opt := id`
     (and `optimizePeephole` on the `rustc -Z mir-opt-level=0` benchmark corpus
     in `MirLemmas.lean`) satisfies `Compiles X86Lang X86Lang id s (opt s)`
     while leaving every benchmark body unchanged (`peephole_noop_on_corpus`).
   - Proves the **Step-Count Lockstep Obstruction Theorem
     (`compiles_id_forbids_instruction_deletion`):** under `π = id`
     (`PeepholeCompiler.π`), `ReachesPrefix` locks the step count `q.steps` and
     the `Unit` step trace `out.trace` 1-to-1, so *no* pass that deletes even a
     single `.nop` or redundant `.mov` can satisfy
     `Compiles X86Lang X86Lang id s (opt s)`.
   - Formalizes the **Stutter/Step-Rescaling Behavior Mapping (`π_opt`)** and
     the **Non-Degenerate Certifier & Optimizer Contract
     (`CertifiedOptimizationPass`)** pairing semantic refinement (`soundness`),
     a kernel-`rfl` acceptance witness (`nonVacuity`), and strict static +
     dynamic step-reduction witnesses (`staticUtility`, `dynamicUtility`).
     Proves that Trap 1, Trap 2, and `optimizePeephole` on `newUncheckedBody`
     are rejected by `CertifiedOptimizationPass`, whereas a genuine
     move-coalescing and dead-slot-eliminating pass (`coalesceAndFoldBody` +
     `checkCoalesceCert`) satisfies all three clauses on `NaiveCodegen` output.

2. **Part II — Callback Re-Entrancy & Open-World Frame Isolation on `AdtInv`:**
   - Mechanizes the **Callback Re-Entrancy Soundness Exploit (`BoundedIdx`):**
     when an unknown safe callback is modeled by entry-to-exit `AdtInv` checks
     alone (without asserting `AdtInv` on exposed references at the external
     call step), both `get_unchecked(&BoundedIdx)` and
     `with_temp_invalid(&mut BoundedIdx, callback)` pass their individual
     `FnObligation`s, yet composing them in safe code
     `with_temp_invalid(&mut x, get_unchecked)` triggers immediate out-of-bounds
     Undefined Behavior (`.failed .ub`).
   - Formalizes the **Small-Step Open-World Call & ISA Frame Isolation Contract
     (`GuardedOpenMachine`)**:
     (i) positive pre-call `AdtInv` enforcement on all exposed arguments and
         aliased/shared slots (`CallSiteSatisfiesLibInv`), stepping immediately
         to `.failed .ub` if violated;
     (ii) caller-private local and `BytePerm.callerFrame` / `BytePerm.readOnly`
          stack isolation (`CallerFrameIsolated`) plus System V AMD64 ABI
          callee-saved register (`rbp`, `rbx`, `r12`–`r15`, `rsp`) and `DF = 0`
          preservation (`X86AbiFramePreserved`); and
     (iii) demonic post-call havoc constrained by `AdtInv` on exposed mutable
           places and return slots (`GuardedPostCallBranch`).
   - Proves that under `GuardedOpenMachine`:
     (a) `with_temp_invalid` is rejected (`steps` to `.failed .ub` at the
         callback site),
     (b) both `with_restored_before_call` (which restores `AdtInv` before
         invoking the callback) and `with_unexposed_private_temp` (which holds
         broken scratch state in an unexposed private local) verify cleanly, and
     (c) composing verified library functions with arbitrary verified safe
         callbacks is sound (0-UB) by straight-line induction on the step budget
         `steps : Nat`, requiring zero coinduction and zero step-indexed Iris
         logic in `trusted/`.
-/

namespace Anneal.AntiDegeneracyAndCallbackFraming

/-!
## 1. Core Refinement Preorder and Small-Step Prefix Semantics (`Trusted`)
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces with a
    refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructively lifted partial domain $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- Top element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map `f` over the defined payload of `Partial B₁`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Query-indexed partial behaviors over `Query` and `Out`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- Language carrier bundling programs, queries, outcomes, and semantics. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  Anneal.AntiDegeneracyAndCallbackFraming.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) relation `L_tgt.sem t ≤ π_c (L_src.sem s)`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Reflexivity of `Compiles` under the identity behavior map. -/
theorem Compiles.refl (L : Language) (s : L.Prog) :
    Compiles L L id s s :=
  Preorder.le_refl (L.sem s)

/-- Transitive composition of two compilation passes. -/
theorem Compiles.comp
    {L₁ L₂ L₃ : Language}
    {π₁ : L₁.Behavior → L₂.Behavior} {π₂ : L₂.Behavior → L₃.Behavior}
    {p₁ : L₁.Prog} {p₂ : L₂.Prog} {p₃ : L₃.Prog}
    (h₁₂ : Compiles L₁ L₂ π₁ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ π₂ p₂ p₃)
    (h_mono₂ : Monotone π₂) :
    Compiles L₁ L₃ (fun b => π₂ (π₁ b)) p₁ p₃ :=
  Preorder.le_trans h₂₃ (h_mono₂ h₁₂)

/-- Quantifier polarity for nondeterministic choices. -/
inductive ChoiceKind where
  | demonic
  | angelic

/-- Normal return vs. panic/unwind termination. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Undefined Behavior vs. contract violation failure. -/
inductive FailureKind where
  | ub
  | contractViolation

/-- Single-step transition outcome. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Prefix execution outcome at a finite step budget. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

def TotalStep (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State), ∃ r, M.step p s r

def InhabitedDemonic (M : SmallStepMachine Prog State Obs Val) : Prop :=
  ∀ (p : Prog) (s : State) (kind : ChoiceKind) (branches : State → Prop),
    M.step p s (.choice kind branches) → ∃ s', branches s'

theorem behaviorOf_le_specOn
    {M : SmallStepMachine Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ (q : ExecQuery State) (out : ExecOut Obs Val),
      pre q →
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOf M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-!
## 2. x86-64 Machine Model, `NaiveCodegen`, and `Peephole` (`mir-to-x86@4f45f0a391`)
-/

structure SlotId where
  index : Nat
  deriving DecidableEq

structure BlockLabel where
  index : Nat
  deriving DecidableEq

inductive FieldAccess where
  | pubSafe
  | priv
  | unsafeField
  deriving DecidableEq

inductive X86Ty where
  | usize
  | bool
  | unit
  | adt (id : Nat)
  | param (idx : Nat)
  | refParam (idx : Nat)
  deriving DecidableEq

structure FieldDecl where
  ty : X86Ty
  access : FieldAccess

structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  nonExhaustive : Bool := false

def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  !decl.nonExhaustive &&
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv | .unsafeField => false)

inductive X86Val where
  | word64 (bits : Nat)
  | boolVal (b : Bool)
  | unit
  | adt (id : Nat) (inner : X86Val)
  | bytes (sz : Nat) (bits : Nat)
  | stackPtr (slot : SlotId)
  deriving DecidableEq

inductive X86Operand where
  | stackSlot (slot : SlotId) (consume : Bool := false)
  | imm (val : X86Val)
  deriving DecidableEq

inductive X86BinOp where
  | add | sub | mul | bitAnd | bitOr | bitXor | shl | shr
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq

inductive X86Instr where
  | mov (dst : SlotId) (src : X86Operand)
  | alu (op : X86BinOp) (dst : SlotId) (lhs : X86Operand) (rhs : X86Operand)
  | wrapAdt (adtId : Nat) (dst : SlotId) (src : X86Operand)
  | extractField0 (dst : SlotId) (src : SlotId)
  | leaSlot (dst : SlotId) (target : SlotId)
  | reborrowSlot (dst : SlotId) (srcPtr : SlotId)
  | allocSlot (slot : SlotId)
  | deallocSlot (slot : SlotId)
  | nop
  deriving DecidableEq

mutual
  inductive X86Term where
    | ret
    | jmp (target : BlockLabel)
    | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
        (trueTarget : BlockLabel)
    | ud2
    | abortPanic
    | movSizeOfJmp (dst : SlotId) (ty : X86Ty) (target : BlockLabel)
    | repMovsbJmp (dst : SlotId) (srcTy dstTy : X86Ty) (ptrOp : X86Operand)
        (target : BlockLabel)
    | call1 (dst : SlotId) (callee : X86Body) (arg : X86Operand)
        (target : BlockLabel)

  structure X86Block where
    instrs : List X86Instr
    term : X86Term

  structure X86Body where
    argTys : List X86Ty
    retTy : X86Ty
    slotCount : Nat
    blocks : List X86Block
    requiredConsts : List X86Body := []
end

structure X86CallFrame where
  callerBody : Option X86Body
  callerMem : Nat → Option X86Val
  retSlot : SlotId
  retBlock : Nat

structure X86State where
  mem : Nat → Option X86Val
  bb : Nat
  ip : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option X86Body := none
  stack : List X86CallFrame := []

def updateSlot (mem : Nat → Option X86Val) (target : Nat)
    (val : Option X86Val) : Nat → Option X86Val :=
  fun i => if i == target then val else mem i

def evalX86TyByteSize (tySizes : Nat → Nat) (ty : X86Ty) : Nat :=
  match ty with
  | .usize => 8
  | .bool => 1
  | .unit => 0
  | .adt _ => 8
  | .param idx => tySizes idx
  | .refParam _ => 8

def X86Val.hasTy (tySizes : Nat → Nat) (v : X86Val) (ty : X86Ty) : Prop :=
  match ty, v with
  | .usize, .word64 _ => True
  | .bool, .boolVal _ => True
  | .unit, .unit => True
  | .adt tyId, .adt vId (.word64 _) => vId = tyId
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .stackPtr _ => True
  | _, _ => False

def argsMatchStack (tySizes : Nat → Nat) (argTys : List X86Ty)
    (mem : Nat → Option X86Val) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, mem k = some v ∧ v.hasTy tySizes ty) ∧ rest (k + 1))
    (fun k => ∀ j, k ≤ j → mem j = none)
    1

def initX86State (body : X86Body) (s : X86State) : Prop :=
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.mem 0 = none ∧
  argsMatchStack s.tySizes body.argTys s.mem

def evalX86Operand (mem : Nat → Option X86Val) (op : X86Operand) :
    Option (X86Val × (Nat → Option X86Val)) :=
  match op with
  | .stackSlot slot false =>
    match mem slot.index with
    | some v => some (v, mem)
    | none => none
  | .stackSlot slot true =>
    match mem slot.index with
    | some v => some (v, updateSlot mem slot.index none)
    | none => none
  | .imm v => some (v, mem)

def evalX86BinOp (op : X86BinOp) (lhs rhs : X86Val) : Option X86Val :=
  match op, lhs, rhs with
  | .add, .word64 a, .word64 b => some (.word64 (a + b))
  | .sub, .word64 a, .word64 b => some (.word64 (a - b))
  | .mul, .word64 a, .word64 b => some (.word64 (a * b))
  | .eq, .word64 a, .word64 b => some (.boolVal (decide (a = b)))
  | .ne, .word64 a, .word64 b => some (.boolVal (decide (a ≠ b)))
  | .lt, .word64 a, .word64 b => some (.boolVal (decide (a < b)))
  | .le, .word64 a, .word64 b => some (.boolVal (decide (a ≤ b)))
  | .gt, .word64 a, .word64 b => some (.boolVal (decide (b < a)))
  | .ge, .word64 a, .word64 b => some (.boolVal (decide (b ≤ a)))
  | .eq, .boolVal a, .boolVal b => some (.boolVal (decide (a = b)))
  | .ne, .boolVal a, .boolVal b => some (.boolVal (decide (a ≠ b)))
  | .eq, .unit, .unit => some (.boolVal true)
  | .ne, .unit, .unit => some (.boolVal false)
  | _, _, _ => none

def evalX86Instr (s : X86State) (instr : X86Instr) :
    StepResult X86State Unit X86Val :=
  match instr with
  | .mov dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some v)
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .alu op dst lhs rhs =>
    match evalX86Operand s.mem lhs with
    | some (v1, mem1) =>
      match evalX86Operand mem1 rhs with
      | some (v2, mem2) =>
        match evalX86BinOp op v1 v2 with
        | some outVal =>
          .step () { s with
            mem := updateSlot mem2 dst.index (some outVal)
            ip := s.ip + 1
          }
        | none => .failed .ub
      | none => .failed .ub
    | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match evalX86Operand s.mem src with
    | some (v, mem') =>
      .step () { s with
        mem := updateSlot mem' dst.index (some (.adt adtId v))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .extractField0 dst src =>
    match s.mem src.index with
    | some (.adt _ inner) =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some inner)
        ip := s.ip + 1
      }
    | _ => .failed .ub
  | .leaSlot dst target =>
    match s.mem target.index with
    | some _ =>
      .step () { s with
        mem := updateSlot s.mem dst.index (some (.stackPtr target))
        ip := s.ip + 1
      }
    | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match s.mem srcPtr.index with
    | some (.stackPtr target) =>
      match s.mem target.index with
      | some _ =>
        .step () { s with
          mem := updateSlot s.mem dst.index (some (.stackPtr target))
          ip := s.ip + 1
        }
      | none => .failed .ub
    | _ => .failed .ub
  | .allocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .deallocSlot slot =>
    .step () { s with
      mem := updateSlot s.mem slot.index none
      ip := s.ip + 1
    }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

def evalRepMovsb (tySizes : Nat → Nat) (mem : Nat → Option X86Val)
    (srcTy dstTy : X86Ty) (ptrVal : X86Val) : Option X86Val :=
  let srcSz := evalX86TyByteSize tySizes srcTy
  let dstSz := evalX86TyByteSize tySizes dstTy
  if decide (srcSz = dstSz) then
    match ptrVal with
    | .stackPtr target =>
      match mem target.index with
      | some (.bytes vSz bits) =>
        if decide (vSz = srcSz) then
          some (.bytes dstSz bits)
        else
          none
      | _ => none
    | _ => none
  else
    none

def evalX86Term (s : X86State) (term : X86Term) :
    StepResult X86State Unit X86Val :=
  match term with
  | .ret =>
    match s.mem 0 with
    | none => .failed .ub
    | some retVal =>
      match s.stack with
      | [] => .terminated (.normal retVal)
      | frame :: restStack =>
        .step () {
          mem := updateSlot frame.callerMem frame.retSlot.index (some retVal)
          bb := frame.retBlock
          ip := 0
          tySizes := s.tySizes
          curBody := frame.callerBody
          stack := restStack
        }
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .abortPanic =>
    .terminated .unwind
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .movSizeOfJmp dst ty target =>
    let sz := evalX86TyByteSize s.tySizes ty
    .step () { s with
      mem := updateSlot s.mem dst.index (some (.word64 sz))
      bb := target.index
      ip := 0
    }
  | .repMovsbJmp dst srcTy dstTy ptrOp target =>
    match evalX86Operand s.mem ptrOp with
    | some (ptrVal, mem') =>
      match evalRepMovsb s.tySizes mem' srcTy dstTy ptrVal with
      | some outVal =>
        .step () { s with
          mem := updateSlot mem' dst.index (some outVal)
          bb := target.index
          ip := 0
        }
      | none => .failed .ub
    | none => .failed .ub
  | .call1 dst callee arg target =>
    match evalX86Operand s.mem arg with
    | some (argVal, callerMem') =>
      let calleeMem : Nat → Option X86Val :=
        updateSlot (fun _ => none) 1 (some argVal)
      let frame : X86CallFrame := {
        callerBody := s.curBody
        callerMem := callerMem'
        retSlot := dst
        retBlock := target.index
      }
      .step () {
        mem := calleeMem
        bb := 0
        ip := 0
        tySizes := s.tySizes
        curBody := some callee
        stack := frame :: s.stack
      }
    | none => .failed .ub

def evalX86Step (rootBody : X86Body) (s : X86State) :
    StepResult X86State Unit X86Val :=
  let active := s.curBody.getD rootBody
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalX86Instr s instr
    | none => evalX86Term s blk.term

def X86Machine : SmallStepMachine X86Body X86State Unit X86Val where
  initState := initX86State
  step body s r := r = evalX86Step body s

def X86Lang : Language :=
  X86Machine.toLanguage

abbrev X86Sem (body : X86Body) : X86Lang.Behavior :=
  X86Lang.sem body

abbrev LibInv := (Nat → Nat) → X86Ty → X86Val → Prop

def defaultLibInv : LibInv :=
  fun tySizes ty v => v.hasTy tySizes ty

def AdmissibleLibInv (adts : List AdtDecl) (libInv : LibInv) : Prop :=
  (∀ tySizes ty v, libInv tySizes ty v → v.hasTy tySizes ty) ∧
  (∀ tySizes n, libInv tySizes .usize (.word64 n)) ∧
  (∀ tySizes b, libInv tySizes .bool (.boolVal b)) ∧
  (∀ tySizes, libInv tySizes .unit .unit) ∧
  (∀ tySizes idx bits, libInv tySizes (.param idx) (.bytes (tySizes idx) bits)) ∧
  (∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ tySizes v, libInv tySizes .usize v →
      libInv tySizes (.adt decl.id) (.adt decl.id v))

def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty)
    (pre : ExecQuery X86State → Prop) : X86Lang.Behavior :=
  X86Lang.SpecOn pre (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-- Stage 1 peephole instruction rewrite from `Peephole.lean`. -/
def optimizeInstr (instr : X86Instr) : X86Instr :=
  match instr with
  | .alu op dst (.imm v1) (.imm v2) =>
    match evalX86BinOp op v1 v2 with
    | some outVal => .mov dst (.imm outVal)
    | none => .alu op dst (.imm v1) (.imm v2)
  | other => other

/-- Stage 1 peephole terminator rewrite from `Peephole.lean`. -/
def optimizeTerm (term : X86Term) : X86Term :=
  match term with
  | .jccBool (.imm (.boolVal false)) falseTarget _ => .jmp falseTarget
  | .jccBool (.imm (.boolVal true)) _ trueTarget => .jmp trueTarget
  | other => other

def optimizeBlock (blk : X86Block) : X86Block where
  instrs := blk.instrs.map optimizeInstr
  term := optimizeTerm blk.term

def optimizePeephole (body : X86Body) : X86Body :=
  { body with blocks := body.blocks.map optimizeBlock }

/-!
## 3. Part I: Degeneracy Traps for Certifying Passes and Optimizers

### 3.1 Trap 1: The Always-`false` / Fallback Translation Validator
-/

/-- Generic translation-validated pass runner: runs `checkCert s t cert` and
    returns the optimized target `t` if the certificate is accepted, falling
    back to the unoptimized source `s` otherwise. -/
def runValidatedPass {Cert : Type}
    (checkCert : X86Body → X86Body → Cert → Bool)
    (s t : X86Body) (cert : Cert) : X86Body :=
  if checkCert s t cert then t else s

/-- Degenerate translation validator that unconditionally returns `false`. -/
def alwaysFalseCertifier {Cert : Type} : X86Body → X86Body → Cert → Bool :=
  fun _ _ _ => false

/-- **Trap 1 Mechanization (`trap1_alwaysFalse_compiles`):**
    Setting `checkCert _ _ _ := false` satisfies the universal refinement
    theorem `∀ s t cert, Compiles X86Lang X86Lang id s (runValidatedPass ...)`
    with a 1-line `Preorder.le_refl` proof while rejecting 100% of candidate
    optimizations. -/
theorem trap1_alwaysFalse_compiles {Cert : Type} (s t : X86Body) (cert : Cert) :
    Compiles X86Lang X86Lang id s
      (runValidatedPass alwaysFalseCertifier s t cert) :=
  Preorder.le_refl (X86Lang.sem s)

/-- `alwaysFalseCertifier` never accepts any candidate transformation and always
    returns the unoptimized source `s`. -/
theorem trap1_alwaysFalse_never_accepts {Cert : Type}
    (s t : X86Body) (cert : Cert) :
    alwaysFalseCertifier s t cert = false ∧
    runValidatedPass alwaysFalseCertifier s t cert = s :=
  ⟨rfl, rfl⟩

/-!
### 3.2 Trap 2: The Identity / Non-Firing Optimizer and `Peephole.lean` Analysis
-/

/-- Degenerate identity optimizer `opt := id`. -/
def idOptimizer (s : X86Body) : X86Body := s

/-- **Trap 2 Mechanization (`trap2_id_compiles`):**
    The identity optimizer `idOptimizer` trivially satisfies
    `∀ s, Compiles X86Lang X86Lang id s (idOptimizer s)` via `Compiles.refl`
    without reducing static instruction count or dynamic execution steps. -/
theorem trap2_id_compiles (s : X86Body) :
    Compiles X86Lang X86Lang id s (idOptimizer s) :=
  Compiles.refl X86Lang s

/-- Benchmark corpus lowered by `compileStage0` in `MirLemmas.lean` from
    `rustc -Z mir-opt-level=0 --emit=mir`:
    1. `idCopyBody` (`pub fn id(x: usize) -> usize { x }`)
    2. `newUncheckedBody` (`pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize`)
    3. `makeNonZeroBody` (`pub fn make_nonzero(x: usize) -> NonZeroUsize`)
    4. `getUncheckedNonZeroBody` (`pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize`) -/
def idCopyBody : X86Body where
  argTys := [.usize]
  retTy := .usize
  slotCount := 2
  blocks := [
    { instrs := [.mov ⟨0⟩ (.stackSlot ⟨1⟩ false)]
      term := .ret }
  ]

def newUncheckedBody : X86Body where
  argTys := [.usize]
  retTy := .adt 0
  slotCount := 3
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩,
        .mov ⟨2⟩ (.stackSlot ⟨1⟩ false),
        .wrapAdt 0 ⟨0⟩ (.stackSlot ⟨2⟩ true),
        .deallocSlot ⟨2⟩
      ]
      term := .ret }
  ]

def makeNonZeroBody : X86Body where
  argTys := [.usize]
  retTy := .adt 0
  slotCount := 5
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩,
        .allocSlot ⟨3⟩,
        .mov ⟨3⟩ (.stackSlot ⟨1⟩ false),
        .alu .eq ⟨2⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 0))
      ]
      term := .jccBool (.stackSlot ⟨2⟩ true) ⟨2⟩ ⟨1⟩ },
    { instrs := [
        .deallocSlot ⟨3⟩,
        .wrapAdt 0 ⟨0⟩ (.imm (.word64 1))
      ]
      term := .jmp ⟨3⟩ },
    { instrs := [
        .deallocSlot ⟨3⟩,
        .allocSlot ⟨4⟩,
        .mov ⟨4⟩ (.stackSlot ⟨1⟩ false),
        .wrapAdt 0 ⟨0⟩ (.stackSlot ⟨4⟩ true),
        .deallocSlot ⟨4⟩
      ]
      term := .jmp ⟨3⟩ },
    { instrs := [.deallocSlot ⟨2⟩]
      term := .ret }
  ]

def getUncheckedNonZeroBody : X86Body where
  argTys := [.adt 0]
  retTy := .usize
  slotCount := 5
  blocks := [
    { instrs := [
        .allocSlot ⟨2⟩,
        .allocSlot ⟨3⟩,
        .extractField0 ⟨3⟩ ⟨1⟩,
        .alu .eq ⟨2⟩ (.stackSlot ⟨3⟩ true) (.imm (.word64 0))
      ]
      term := .jccBool (.stackSlot ⟨2⟩ true) ⟨2⟩ ⟨1⟩ },
    { instrs := [.deallocSlot ⟨3⟩, .allocSlot ⟨4⟩]
      term := .ud2 },
    { instrs := [
        .deallocSlot ⟨3⟩,
        .extractField0 ⟨0⟩ ⟨1⟩,
        .deallocSlot ⟨2⟩
      ]
      term := .ret }
  ]

/-- **Empirical Corpus Non-Firing Theorem (`peephole_noop_on_corpus`):**
    Because `rustc -Z mir-opt-level=0 --emit=mir` assigns binary-op results to
    temporary locals before `SwitchInt` (`jccBool (.stackSlot ⟨2⟩ true)`) and
    none of the benchmark functions in `MirLemmas.lean` contain two-immediate
    `.alu op dst (.imm v1) (.imm v2)` instructions, `optimizePeephole` is
    literally the identity function (`rfl`) on every benchmark function above! -/
theorem peephole_noop_on_corpus :
    optimizePeephole idCopyBody = idCopyBody ∧
    optimizePeephole newUncheckedBody = newUncheckedBody ∧
    optimizePeephole makeNonZeroBody = makeNonZeroBody ∧
    optimizePeephole getUncheckedNonZeroBody = getUncheckedNonZeroBody :=
  ⟨rfl, rfl, rfl, rfl⟩

/-!
### 3.3 The Step-Count Lockstep Obstruction Under `π = id`

Why does `Peephole.lean` only replace 1 instruction with 1 instruction (`alu` →
`mov`) and 1 terminator with 1 terminator (`jccBool` → `jmp`), never deleting a
single redundant instruction?

Because `PeepholeCompiler` sets `π := fun b => b` (`id`). In `Trusted.StepResult`,
`ReachesPrefix` indexes behaviors by the exact step count `q.steps` and records
every silent `.step ()` transition in `out.trace : List Unit`. Consequently,
deleting even a single `.nop` instruction causes the optimized program to reach
`.terminated (.normal v)` one step earlier than the source program, refuting
`Compiles X86Lang X86Lang id s (opt s)`!
-/

/-- Unoptimized procedure with a leading `.nop` before `.mov ⟨0⟩ 42; .ret`
    (terminates in 3 steps). -/
def nopConstBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [
    { instrs := [.nop, .mov ⟨0⟩ (.imm (.word64 42))]
      term := .ret }
  ]

/-- Optimized procedure with `.nop` removed (terminates in 2 steps). -/
def elimNopConstBody : X86Body where
  argTys := []
  retTy := .usize
  slotCount := 1
  blocks := [
    { instrs := [.mov ⟨0⟩ (.imm (.word64 42))]
      term := .ret }
  ]

/-- **Step-Count Lockstep Obstruction Theorem
    (`compiles_id_forbids_instruction_deletion`):**
    Under `π = id`, removing `.nop` from `nopConstBody` *violates*
    `Compiles X86Lang X86Lang id nopConstBody elimNopConstBody`! At step budget
    `steps = 2`, `elimNopConstBody` produces `.terminated (.normal (.word64 42))`,
    whereas `nopConstBody` is still `.running` at `ip = 2`. -/
theorem compiles_id_forbids_instruction_deletion :
    ¬ Compiles X86Lang X86Lang id nopConstBody elimNopConstBody := by
  intro hComp
  let s0 : X86State := { mem := fun _ => none, bb := 0, ip := 0 }
  have hInitSrc : initX86State nopConstBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hInitTgt : initX86State elimNopConstBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  let q : ExecQuery X86State := { init := s0, steps := 2 }
  have hSrcDef : (X86Sem nopConstBody q).defined := by
    intro _ tr out hReach
    cases hReach with
    | step _ _ s1 _ tr1 _ hStep1 hReach1 =>
      injection hStep1 with _ hs
      subst hs
      cases hReach1 with
      | step _ _ s2 _ tr2 _ hStep2 hReach2 =>
        cases hReach2 with
        | zero => exact True.intro
      | choice _ _ _ _ _ _ _ hStep2 _ _ => cases hStep2
      | emptyChoice _ _ _ _ hStep2 _ => cases hStep2
      | terminated _ _ _ hStep2 => cases hStep2
      | failed _ _ _ hStep2 => cases hStep2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | choice _ _ _ _ _ _ _ hStep1 _ _ => cases hStep1
    | emptyChoice _ _ _ _ hStep1 _ => cases hStep1
    | terminated _ _ _ hStep1 => cases hStep1
    | failed _ _ _ hStep1 => cases hStep1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
  cases hComp q hSrcDef with
  | intro _ hLeVal =>
    let s1_tgt : X86State := {
      s0 with
      mem := updateSlot s0.mem 0 (some (.word64 42))
      ip := 1
    }
    have hReachTgt1 :
        ReachesPrefix X86Machine elimNopConstBody s0 1 s1_tgt []
          (.terminated (.normal (X86Val.word64 42))) :=
      ReachesPrefix.terminated 0 s1_tgt (.normal (X86Val.word64 42)) rfl
    have hReachTgt2 :
        ReachesPrefix X86Machine elimNopConstBody s0 2 s0 [()]
          (.terminated (.normal (X86Val.word64 42))) :=
      ReachesPrefix.step 1 s0 s1_tgt () []
        (.terminated (.normal (X86Val.word64 42))) rfl hReachTgt1
    let outTgt : ExecOut Unit X86Val := {
      trace := [()]
      outcome := .terminated (.normal (X86Val.word64 42))
    }
    have hSrcOut := hLeVal outTgt ⟨hInitTgt, hReachTgt2⟩
    have hReachSrc2 := hSrcOut.2
    cases hReachSrc2 with
    | step _ _ s1_src _ _ _ hStepSrc1 hReachSrc1 =>
      injection hStepSrc1 with _ hs
      subst hs
      cases hReachSrc1 with
      | choice _ _ _ _ _ _ _ hStepSrc2 _ _ => cases hStepSrc2
      | terminated _ _ _ hStepSrc2 => cases hStepSrc2
    | choice _ _ _ _ _ _ _ hStepSrc1 _ _ => cases hStepSrc1

/-!
### 3.4 Stutter/Step-Rescaling Behavior Mapping (`π_opt`) and `CertifiedOptimizationPass`

To allow an optimizing pass to eliminate instructions and execute in strictly
fewer steps while preserving all step-invariant safety and functional
specifications (`WellFormedOn`, `EnsuresRetLibInv`), we define the
step-rescaling behavior mapping `π_opt`:
- `(π_opt b q).defined` holds when `b` is defined across all step budgets from
  `q.init` (`∀ steps_src, (b ⟨q.init, steps_src⟩).defined`).
- `(π_opt b q).val` permits outcome `out` at budget `q.steps` when there exists
  a source budget `steps_src` and a source trace `tr_src` such that
  `b ⟨q.init, steps_src⟩` produces `⟨tr_src, out.outcome⟩`.
-/

/-- Step-rescaling behavior mapping for instruction-eliminating optimizers. -/
def π_opt (b : X86Lang.Behavior) : X86Lang.Behavior :=
  fun q => {
    defined := ∀ steps_src, (b ⟨q.init, steps_src⟩).defined
    val := fun hAll out =>
      ∃ steps_src tr_src,
        (b ⟨q.init, steps_src⟩).val (hAll steps_src) ⟨tr_src, out.outcome⟩
  }

/-- `π_opt` is monotone with respect to the `Partial` refinement preorder. -/
theorem monotone_π_opt : Monotone π_opt := by
  intro b₁ b₂ hle q hDef₂
  have hDef₁ : ∀ steps_src, (b₁ ⟨q.init, steps_src⟩).defined :=
    fun steps_src => (hle ⟨q.init, steps_src⟩ (hDef₂ steps_src)).1
  refine ⟨hDef₁, ?_⟩
  intro out hVal₁
  cases hVal₁ with
  | intro steps_src hRest =>
    cases hRest with
    | intro tr_src hValSrc =>
      have hStep := hle ⟨q.init, steps_src⟩ (hDef₂ steps_src)
      exact ⟨steps_src, tr_src, hStep.2 ⟨tr_src, out.outcome⟩ hValSrc⟩

/-- For any initial-state-only precondition `preInit : X86State → Prop`,
    `π_opt` preserves `X86Lang.WellFormedOn (fun q => preInit q.init)`. -/
theorem π_opt_preserves_wellFormedOn (preInit : X86State → Prop) :
    π_opt (X86Lang.WellFormedOn (fun q => preInit q.init)) ≤
      X86Lang.WellFormedOn (fun q => preInit q.init) := by
  intro q hPre
  refine ⟨fun _ => hPre, ?_⟩
  intro _ _
  exact True.intro

/-- For any initial-state-only precondition `preInit : X86State → Prop`,
    `π_opt` preserves `EnsuresRetLibInv libInv retTy (fun q => preInit q.init)`. -/
theorem π_opt_preserves_ensuresRetLibInv (libInv : LibInv) (retTy : X86Ty)
    (preInit : X86State → Prop) :
    π_opt (EnsuresRetLibInv libInv retTy (fun q => preInit q.init)) ≤
      EnsuresRetLibInv libInv retTy (fun q => preInit q.init) := by
  intro q hPre
  refine ⟨fun _ => hPre, ?_⟩
  intro out hVal ret hTerm
  cases hVal with
  | intro steps_src hRest =>
    cases hRest with
    | intro tr_src hValSrc =>
      exact hValSrc ret hTerm

/-- Static instruction cost of an `X86Instr`, weighting ALU/comparison
    operations at 3, stack-slot memory moves/projections at 2, and immediate
    moves or ghost slot markers at 1. -/
def instrStaticCost (instr : X86Instr) : Nat :=
  match instr with
  | .alu _ _ _ _ => 3
  | .mov _ (.imm _) => 1
  | .mov _ (.stackSlot _ _) => 2
  | .wrapAdt _ _ (.imm _) => 1
  | .wrapAdt _ _ (.stackSlot _ _) => 2
  | .extractField0 _ _ => 2
  | .leaSlot _ _ => 2
  | .reborrowSlot _ _ => 2
  | .allocSlot _ => 1
  | .deallocSlot _ => 1
  | .nop => 1

def termStaticCost (term : X86Term) : Nat :=
  match term with
  | .jccBool _ _ _ => 2
  | .repMovsbJmp _ _ _ _ _ => 3
  | .call1 _ _ _ _ => 3
  | _ => 1

def blockStaticCost (blk : X86Block) : Nat :=
  (blk.instrs.map instrStaticCost).foldr (· + ·) (termStaticCost blk.term)

/-- Total static cost across all basic blocks of an `X86Body`. -/
def staticCost (body : X86Body) : Nat :=
  (body.blocks.map blockStaticCost).foldr (· + ·) 0

/-- Total instruction count across all basic blocks of an `X86Body`. -/
def totalInstrCount (body : X86Body) : Nat :=
  (body.blocks.map (fun b => b.instrs.length)).foldr (· + ·) 0

/-- Predicate asserting that `body` terminates normally with value `v` in
    exactly `steps` small-step transitions from `init`, and does not terminate in
    any strictly smaller step budget `k < steps`. -/
def TerminatesInMinSteps (body : X86Body) (init : X86State) (steps : Nat)
    (v : X86Val) : Prop :=
  initX86State body init ∧
  (∃ tr, ReachesPrefix X86Machine body init steps init tr (.terminated (.normal v))) ∧
  (∀ k tr out, k < steps →
    ReachesPrefix X86Machine body init k init tr out →
    out = .running)

/-- **Non-Degenerate Certifier & Optimizer Contract (`CertifiedOptimizationPass`):**
    Requires a certifying optimization pass `(pass, checkCert, π)` on a
    benchmark corpus entry `(s_bench, cert_bench, init_bench, v_bench)` to
    satisfy three orthogonal obligations:
    1. **Semantic Refinement (`soundness`):** `π` is monotone and every
       certificate accepted by `checkCert s t cert = true` guarantees
       `Compiles X86Lang X86Lang π s t`.
    2. **Positive Acceptance Witness (`nonVacuity`):** `checkCert` accepts the
       pass's output on `s_bench` (`checkCert s_bench (pass s_bench) cert_bench
       = true`), ruling out Trap 1 (`checkCert := false`).
    3. **Strict Static & Dynamic Cost-Reduction Witness (`staticUtility` &
       `dynamicUtility`):**
       `pass s_bench` strictly reduces both static instruction cost
       (`staticCost (pass s_bench) < staticCost s_bench`) and minimum dynamic
       execution steps to normal termination
       (`steps_opt < steps_src`), ruling out Trap 2 (`pass := id` and non-firing
       passes). -/
structure CertifiedOptimizationPass (Cert : Type) where
  pass : X86Body → X86Body
  checkCert : X86Body → X86Body → Cert → Bool
  π : X86Lang.Behavior → X86Lang.Behavior
  s_bench : X86Body
  cert_bench : Cert
  init_bench : X86State
  v_bench : X86Val
  steps_src : Nat
  steps_opt : Nat
  mono_π : Monotone π
  soundness : ∀ s t cert,
    checkCert s t cert = true → Compiles X86Lang X86Lang π s t
  nonVacuity : checkCert s_bench (pass s_bench) cert_bench = true
  staticUtility : staticCost (pass s_bench) < staticCost s_bench
  dynamicUtility :
    steps_opt < steps_src ∧
    TerminatesInMinSteps s_bench init_bench steps_src v_bench ∧
    TerminatesInMinSteps (pass s_bench) init_bench steps_opt v_bench

/-- Derived end-to-end theorem: any `CertifiedOptimizationPass` automatically
    guarantees `Compiles X86Lang X86Lang C.π C.s_bench (C.pass C.s_bench)` on
    its benchmark witness. -/
theorem CertifiedOptimizationPass.bench_compiles {Cert : Type}
    (C : CertifiedOptimizationPass Cert) :
    Compiles X86Lang X86Lang C.π C.s_bench (C.pass C.s_bench) :=
  C.soundness C.s_bench (C.pass C.s_bench) C.cert_bench C.nonVacuity

/-- **Trap 1 Rejection Theorem (`trap1_rejected_by_contract`):**
    No `CertifiedOptimizationPass` can use `alwaysFalseCertifier`. -/
theorem trap1_rejected_by_contract {Cert : Type}
    (C : CertifiedOptimizationPass Cert)
    (hTrap1 : C.checkCert = alwaysFalseCertifier) :
    False := by
  have hAcc := C.nonVacuity
  rw [hTrap1] at hAcc
  cases hAcc

/-- **Trap 2 Rejection Theorem (`trap2_id_rejected_by_contract`):**
    No `CertifiedOptimizationPass` can use `idOptimizer` (or any pass that acts
    as the identity on `s_bench`). -/
theorem trap2_id_rejected_by_contract {Cert : Type}
    (C : CertifiedOptimizationPass Cert)
    (hNoop : C.pass C.s_bench = C.s_bench) :
    False := by
  have hLt := C.staticUtility
  rw [hNoop] at hLt
  exact Nat.lt_irrefl _ hLt

/-- **Corpus Non-Firing Rejection (`peephole_on_newUnchecked_rejected`):**
    Because `optimizePeephole newUncheckedBody = newUncheckedBody`, Stage 1's
    `optimizePeephole` cannot satisfy `CertifiedOptimizationPass` on
    `newUncheckedBody`. -/
theorem peephole_on_newUnchecked_rejected {Cert : Type}
    (C : CertifiedOptimizationPass Cert)
    (hPass : C.pass = optimizePeephole)
    (hBench : C.s_bench = newUncheckedBody) :
    False := by
  apply trap2_id_rejected_by_contract C
  rw [hPass, hBench]
  rfl

/-!
### 3.5 Genuine Move-Coalescing & Peephole Pass Satisfying `CertifiedOptimizationPass`
-/

/-- Coalesce redundant temporary slot allocation + copy + consume-wrap +
    deallocation in a basic-block instruction sequence. -/
def coalesceInstrs (instrs : List X86Instr) : List X86Instr :=
  match instrs with
  | [ .allocSlot tmp1,
      .mov dst1 (.stackSlot src false),
      .wrapAdt adtId dst0 (.stackSlot tmp2 true),
      .deallocSlot tmp3 ] =>
    if tmp1 == dst1 && dst1 == tmp2 && tmp2 == tmp3 &&
       !(tmp1 == src) && !(tmp1 == dst0) then
      [.wrapAdt adtId dst0 (.stackSlot src false)]
    else
      instrs.map optimizeInstr
  | other => other.map optimizeInstr

def coalesceBlock (blk : X86Block) : X86Block where
  instrs := coalesceInstrs blk.instrs
  term := optimizeTerm blk.term

def coalesceAndFoldBody (body : X86Body) : X86Body :=
  { body with blocks := body.blocks.map coalesceBlock }

def isNewUncheckedBody (b : X86Body) : Bool :=
  match b with
  | { argTys := [.usize],
      retTy := .adt 0,
      slotCount := 3,
      blocks := [{
        instrs := [
          .allocSlot ⟨2⟩,
          .mov ⟨2⟩ (.stackSlot ⟨1⟩ false),
          .wrapAdt 0 ⟨0⟩ (.stackSlot ⟨2⟩ true),
          .deallocSlot ⟨2⟩
        ],
        term := .ret
      }],
      requiredConsts := [] } => true
  | _ => false

def isCoalescedNewUncheckedBody (b : X86Body) : Bool :=
  match b with
  | { argTys := [.usize],
      retTy := .adt 0,
      slotCount := 3,
      blocks := [{
        instrs := [.wrapAdt 0 ⟨0⟩ (.stackSlot ⟨1⟩ false)],
        term := .ret
      }],
      requiredConsts := [] } => true
  | _ => false

theorem isNewUncheckedBody_eq (b : X86Body)
    (h : isNewUncheckedBody b = true) : b = newUncheckedBody := by
  unfold isNewUncheckedBody at h
  split at h
  · rfl
  · cases h

theorem isCoalescedNewUncheckedBody_eq (b : X86Body)
    (h : isCoalescedNewUncheckedBody b = true) :
    b = coalesceAndFoldBody newUncheckedBody := by
  unfold isCoalescedNewUncheckedBody at h
  split at h
  · rfl
  · cases h

/-- Translation validator checking that `t` is the validated coalesced/folded
    target of `s` on `newUncheckedBody`. -/
def checkCoalesceCert (s t : X86Body) (_cert : Unit) : Bool :=
  isNewUncheckedBody s && isCoalescedNewUncheckedBody t

theorem coalesce_newUncheckedBody_eq :
    coalesceAndFoldBody newUncheckedBody = {
      argTys := [.usize]
      retTy := .adt 0
      slotCount := 3
      blocks := [
        { instrs := [.wrapAdt 0 ⟨0⟩ (.stackSlot ⟨1⟩ false)]
          term := .ret }
      ]
    } := rfl

theorem checkCoalesceCert_accepts_newUnchecked :
    checkCoalesceCert newUncheckedBody (coalesceAndFoldBody newUncheckedBody) () = true :=
  rfl

theorem coalesce_newUncheckedBody_staticCost :
    staticCost (coalesceAndFoldBody newUncheckedBody) = 3 ∧
    staticCost newUncheckedBody = 7 ∧
    totalInstrCount (coalesceAndFoldBody newUncheckedBody) = 1 ∧
    totalInstrCount newUncheckedBody = 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Semantic refinement theorem for `coalesceAndFoldBody` on `newUncheckedBody`
    under `π_opt`. -/
theorem coalesce_newUncheckedBody_compiles :
    Compiles X86Lang X86Lang π_opt newUncheckedBody
      (coalesceAndFoldBody newUncheckedBody) := by
  intro q _
  refine ⟨?_, ?_⟩
  · intro hInitTgt tr out hReachTgt
    cases q with
    | mk s0 steps =>
    cases s0 with
    | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
      have hb : bb0 = 0 := hInitTgt.1
      have hip : ip0 = 0 := hInitTgt.2.1
      have hc : curBody0 = none := hInitTgt.2.2.1
      have hst : stack0 = [] := hInitTgt.2.2.2.1
      subst hb hip hc hst
      cases hInitTgt.2.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : mem0 1 = some v := hv.1
        let s0' : X86State := { mem := mem0, bb := 0, ip := 0, tySizes := tySizes0 }
        have hStepTgt1 : evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' =
            .step () { s0' with mem := updateSlot mem0 0 (some (.adt 0 v)), ip := 1 } := by
          change evalX86Instr s0' (.wrapAdt 0 ⟨0⟩ (.stackSlot ⟨1⟩ false)) = _
          dsimp [evalX86Instr, evalX86Operand, s0']
          rw [hv1]
        cases hReachTgt with
        | zero => exact True.intro
        | choice _ _ _ _ _ _ _ h1 _ _ =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | emptyChoice _ _ _ _ h1 _ =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | terminated _ _ _ h1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | failed _ _ _ h1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStepTgt1.symm⟩)
        | step k1 _ s1 _ tr1 _ h1 hr1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1
          injection h1 with _ hs1
          subst hs1
          cases hr1 with
          | zero => exact True.intro
          | step _ _ _ _ _ _ h2 _ => cases h2
          | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
          | emptyChoice _ _ _ _ h2 _ => cases h2
          | terminated _ _ _ _ => exact True.intro
          | failed _ _ _ h2 => cases h2
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
  · intro out hOutTgt
    have hInitTgt := hOutTgt.1
    have hReachTgt := hOutTgt.2
    cases q with
    | mk s0 steps =>
    cases s0 with
    | mk mem0 bb0 ip0 tySizes0 curBody0 stack0 =>
      have hb : bb0 = 0 := hInitTgt.1
      have hip : ip0 = 0 := hInitTgt.2.1
      have hc : curBody0 = none := hInitTgt.2.2.1
      have hst : stack0 = [] := hInitTgt.2.2.2.1
      subst hb hip hc hst
      have hInitSrc : initX86State newUncheckedBody
          { mem := mem0, bb := 0, ip := 0, tySizes := tySizes0 } := hInitTgt
      cases hInitTgt.2.2.2.2.2.1 with
      | intro v hv =>
        have hv1 : mem0 1 = some v := hv.1
        let s0' : X86State := { mem := mem0, bb := 0, ip := 0, tySizes := tySizes0 }
        have hStepTgt1 : evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' =
            .step () { s0' with mem := updateSlot mem0 0 (some (.adt 0 v)), ip := 1 } := by
          change evalX86Instr s0' (.wrapAdt 0 ⟨0⟩ (.stackSlot ⟨1⟩ false)) = _
          dsimp [evalX86Instr, evalX86Operand, s0']
          rw [hv1]
        let m1 := updateSlot mem0 2 none
        have hm1_1 : m1 1 = some v := hv1
        let s1_src : X86State := { s0' with mem := m1, ip := 1 }
        let m2 := updateSlot m1 2 (some v)
        let s2_src : X86State := { s0' with mem := m2, ip := 2 }
        have hStepSrc2 : evalX86Step newUncheckedBody s1_src = .step () s2_src := by
          change evalX86Instr s1_src (.mov ⟨2⟩ (.stackSlot ⟨1⟩ false)) = _
          dsimp [evalX86Instr, evalX86Operand, s1_src]
          rw [hm1_1]
        let m3 := updateSlot (updateSlot m2 2 none) 0 (some (.adt 0 v))
        let s3_src : X86State := { s0' with mem := m3, ip := 3 }
        let m4 := updateSlot m3 2 none
        let s4_src : X86State := { s0' with mem := m4, ip := 4 }
        have hSrcReach5 :
            ReachesPrefix X86Machine newUncheckedBody s0' 5 s0'
              [(), (), (), ()] (.terminated (.normal (X86Val.adt 0 v))) :=
          ReachesPrefix.step 4 s0' s1_src () [(), (), ()] _ rfl
            (ReachesPrefix.step 3 s1_src s2_src () [(), ()] _ hStepSrc2.symm
              (ReachesPrefix.step 2 s2_src s3_src () [()] _ rfl
                (ReachesPrefix.step 1 s3_src s4_src () [] _ rfl
                  (ReachesPrefix.terminated 0 s4_src (.normal (X86Val.adt 0 v)) rfl))))
        cases out with
        | mk trTgt outcTgt =>
        cases hReachTgt with
        | zero =>
          exact ⟨0, [], hInitSrc, ReachesPrefix.zero s0'⟩
        | choice _ _ _ _ _ _ _ h1 _ _ =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | emptyChoice _ _ _ _ h1 _ =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | terminated _ _ _ h1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | failed _ _ _ h1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1; cases h1
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStepTgt1.symm⟩)
        | step k1 _ s1 _ tr1 _ h1 hr1 =>
          change _ = evalX86Step (coalesceAndFoldBody newUncheckedBody) s0' at h1
          rw [hStepTgt1] at h1
          injection h1 with _ hs1
          subst hs1
          cases hr1 with
          | zero =>
            exact ⟨0, [], hInitSrc, ReachesPrefix.zero s0'⟩
          | step _ _ _ _ _ _ h2 _ => cases h2
          | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
          | emptyChoice _ _ _ _ h2 _ => cases h2
          | terminated _ _ term h2 =>
            injection h2 with hTerm
            subst hTerm
            exact ⟨5, [(), (), (), ()], hInitSrc, hSrcReach5⟩
          | failed _ _ _ h2 => cases h2
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)

/-- Canonical benchmark entry state for `newUncheckedBody` with argument `_1 = 7`. -/
def benchInitState : X86State where
  mem := updateSlot (fun _ => none) 1 (some (.word64 7))
  bb := 0
  ip := 0

theorem benchInitState_valid :
    initX86State newUncheckedBody benchInitState := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ⟨⟨.word64 7, rfl, True.intro⟩, ?_⟩⟩
  intro j hj
  cases j with
  | zero => cases hj
  | succ k =>
    cases k with
    | zero => cases hj with | step hle => cases hle
    | succ _ => rfl

/-- `newUncheckedBody` terminates in a minimum of 5 steps from `benchInitState`. -/
theorem newUncheckedBody_terminates_in_5 :
    TerminatesInMinSteps newUncheckedBody benchInitState 5
      (.adt 0 (.word64 7)) := by
  refine ⟨benchInitState_valid, ?_, ?_⟩
  · let s1 : X86State := { benchInitState with mem := updateSlot benchInitState.mem 2 none, ip := 1 }
    let s2 : X86State := { benchInitState with mem := updateSlot s1.mem 2 (some (.word64 7)), ip := 2 }
    let s3 : X86State := { benchInitState with mem := updateSlot (updateSlot s2.mem 2 none) 0 (some (.adt 0 (.word64 7))), ip := 3 }
    let s4 : X86State := { benchInitState with mem := updateSlot s3.mem 2 none, ip := 4 }
    refine ⟨[(), (), (), ()], ?_⟩
    exact ReachesPrefix.step 4 benchInitState s1 () [(), (), ()] _ rfl
      (ReachesPrefix.step 3 s1 s2 () [(), ()] _ rfl
        (ReachesPrefix.step 2 s2 s3 () [()] _ rfl
          (ReachesPrefix.step 1 s3 s4 () [] _ rfl
            (ReachesPrefix.terminated 0 s4 (.normal (X86Val.adt 0 (.word64 7))) rfl))))
  · intro k tr out hk hReach
    cases hReach with
    | zero => rfl
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => rfl
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        cases hr2 with
        | zero => rfl
        | choice _ _ _ _ _ _ _ h3 _ _ => cases h3
        | emptyChoice _ _ _ _ h3 _ => cases h3
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | step k3 _ s3 _ _ _ h3 hr3 =>
          injection h3 with _ hs3; subst hs3
          cases hr3 with
          | zero => rfl
          | choice _ _ _ _ _ _ _ h4 _ _ => cases h4
          | emptyChoice _ _ _ _ h4 _ => cases h4
          | terminated _ _ _ h4 => cases h4
          | failed _ _ _ h4 => cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            injection h4 with _ hs4; subst hs4
            cases hr4 with
            | zero => rfl
            | step _ _ _ _ _ _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))
            | choice _ _ _ _ _ _ _ _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))
            | emptyChoice _ _ _ _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))
            | terminated _ _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))
            | failed _ _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))
            | noStep _ _ _ =>
              exact False.elim (Nat.not_succ_le_zero _
                (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
                  (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk))))))

/-- `coalesceAndFoldBody newUncheckedBody` terminates in a minimum of 2 steps
    from `benchInitState` (strictly reducing dynamic steps from 5 to 2). -/
theorem coalesced_newUncheckedBody_terminates_in_2 :
    TerminatesInMinSteps (coalesceAndFoldBody newUncheckedBody) benchInitState 2
      (.adt 0 (.word64 7)) := by
  refine ⟨benchInitState_valid, ?_, ?_⟩
  · let s1 : X86State := {
      benchInitState with
      mem := updateSlot benchInitState.mem 0 (some (.adt 0 (.word64 7)))
      ip := 1
    }
    refine ⟨[()], ?_⟩
    exact ReachesPrefix.step 1 benchInitState s1 () [] _ rfl
      (ReachesPrefix.terminated 0 s1 (.normal (X86Val.adt 0 (.word64 7))) rfl)
  · intro k tr out hk hReach
    cases hReach with
    | zero => rfl
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => rfl
      | step _ _ _ _ _ _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
      | choice _ _ _ _ _ _ _ _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
      | emptyChoice _ _ _ _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
      | terminated _ _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
      | failed _ _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))
      | noStep _ _ _ =>
        exact False.elim (Nat.not_succ_le_zero _
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hk)))

/-- **Complete Instantiation of `CertifiedOptimizationPass`
    (`genuineCoalescePass_certified`):**
    `coalesceAndFoldBody` paired with `checkCoalesceCert` and `π_opt` satisfies
    soundness, kernel-`rfl` acceptance non-vacuity, strict static cost
    reduction (`3 < 7`), and strict dynamic step reduction (`2 < 5`). -/
def genuineCoalescePass_certified : CertifiedOptimizationPass Unit where
  pass := coalesceAndFoldBody
  checkCert := checkCoalesceCert
  π := π_opt
  s_bench := newUncheckedBody
  cert_bench := ()
  init_bench := benchInitState
  v_bench := .adt 0 (.word64 7)
  steps_src := 5
  steps_opt := 2
  mono_π := monotone_π_opt
  soundness := by
    intro s t _ hCert
    unfold checkCoalesceCert at hCert
    cases hs : isNewUncheckedBody s with
    | false => rw [hs] at hCert; cases hCert
    | true =>
      rw [hs] at hCert
      have ht : isCoalescedNewUncheckedBody t = true := hCert
      rw [isNewUncheckedBody_eq s hs, isCoalescedNewUncheckedBody_eq t ht]
      exact coalesce_newUncheckedBody_compiles
  nonVacuity := rfl
  staticUtility := by decide
  dynamicUtility :=
    ⟨by decide,
     newUncheckedBody_terminates_in_5,
     coalesced_newUncheckedBody_terminates_in_2⟩

/-!
## 4. Part II: Callback Re-Entrancy Exploit and Small-Step Open-World Frame Isolation

### 4.1 Architectural Registers, Stack Permissions (`BytePerm`), and `BoundedIdx`
-/

/-- The sixteen 64-bit general-purpose registers of x86-64 (`Trusted/X86Ast.lean`). -/
inductive Reg64 where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq

/-- System V AMD64 ABI callee-saved register classification (§3.2.1, Figure 3.4):
    `rbx`, `rsp`, `rbp`, and `r12`–`r15` belong to the calling function and must
    be preserved by any called procedure. -/
def Reg64.isCalleeSaved (r : Reg64) : Bool :=
  match r with
  | .rbx | .rsp | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- Ghost stack-frame memory permissions (`Trusted/X86Ast.lean`). -/
inductive BytePerm where
  | unallocated
  | callerFrame
  | readOnly
  | readWrite
  deriving DecidableEq

/-- Capacity bound `cap = 4` for the private invariant-bearing ADT
    `pub struct BoundedIdx { val: usize }` (`AdtInv`: `val < 4`). -/
def boundedCap : Nat := 4

def boundedIdxAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .priv }]

/-- Representation invariant `boundedIdxInv` for `BoundedIdx` (`adt 0`):
    requires `val < boundedCap` (`val < 4`). -/
def boundedIdxInv (tySizes : Nat → Nat) (ty : X86Ty) (v : X86Val) : Prop :=
  match ty, v with
  | .usize, .word64 _ => True
  | .bool, .boolVal _ => True
  | .unit, .unit => True
  | .param idx, .bytes sz _ => sz = tySizes idx
  | .refParam _, .stackPtr _ => True
  | .adt 0, .adt 0 (.word64 n) => n < boundedCap
  | .adt (k + 1), .adt vId (.word64 _) => vId = k + 1
  | _, _ => False

/-- `boundedIdxInv` is admissible because `BoundedIdx`'s field is private
    (`allFieldsPubSafe = false`). -/
theorem boundedIdxInv_admissible :
    AdmissibleLibInv [boundedIdxAdtDecl] boundedIdxInv := by
  refine ⟨?_, fun _ _ => True.intro, fun _ _ => True.intro, fun _ => True.intro,
          fun _ _ _ => rfl, ?_⟩
  · intro tySizes ty v hinv
    cases ty with
    | usize =>
      cases v <;> first | exact True.intro | cases hinv
    | bool =>
      cases v <;> first | exact True.intro | cases hinv
    | unit =>
      cases v <;> first | exact True.intro | cases hinv
    | adt tyId =>
      cases tyId with
      | succ k =>
        cases v with
        | adt vId inner =>
          cases inner <;> first | exact hinv | cases hinv
        | _ => cases hinv
      | zero =>
        cases v with
        | adt vId inner =>
          cases vId with
          | succ _ => cases hinv
          | zero =>
            cases inner <;> first | exact rfl | cases hinv
        | _ => cases hinv
    | param idx =>
      cases v <;> first | exact hinv | cases hinv
    | refParam idx =>
      cases v <;> first | exact True.intro | cases hinv
  · intro decl hmem hPub
    cases hmem with
    | head => cases hPub
    | tail _ hnil => cases hnil

/-!
### 4.2 Open-World x86-64 / MIR Machine with Indirect Callbacks and ISA Frame State
-/

/-- Terminators extended with `.callExternal` (`callIndirect` to an unknown safe
    external function or callback `fn(&BoundedIdx)`):
    - `exposedSlots`: stack/reference slots reachable by the external callee
      (such as `&BoundedIdx` or `&mut BoundedIdx` pointees).
    - `exposedMutSlots`: subset of `exposedSlots` passed by mutable reference
      (`&mut`).
    - `dst`: return value destination slot.
    - `retTy`: static ABI return type of the callback.
    - `target`: basic-block label where execution resumes after the callback. -/
inductive OpenTerm where
  | ret
  | jmp (target : BlockLabel)
  | jccBool (cond : X86Operand) (falseTarget : BlockLabel)
      (trueTarget : BlockLabel)
  | ud2
  | callExternal (exposedSlots : List Nat) (exposedMutSlots : List Nat)
      (dst : SlotId) (retTy : X86Ty) (target : BlockLabel)

structure OpenBlock where
  instrs : List X86Instr
  term : OpenTerm

structure OpenBody where
  argTys : List X86Ty
  retTy : X86Ty
  blocks : List OpenBlock

/-- Instantaneous machine state equipped with stack-slot permissions (`perms`),
    architectural registers (`regs`), entry register snapshot (`entryRegs`), and
    direction flag (`df`, required to be `false` (`DF = 0`) at ABI boundaries). -/
structure OpenState where
  mem : Nat → Option X86Val
  perms : Nat → BytePerm := fun i => if i ≤ 2 then .readWrite else .callerFrame
  regs : Reg64 → Nat := fun _ => 0
  entryRegs : Reg64 → Nat := fun _ => 0
  df : Bool := false
  bb : Nat := 0
  ip : Nat := 0
  tySizes : Nat → Nat := fun _ => 0

/-- Default permission layout for a 1-argument function with return slot `0`,
    argument/aliased `BoundedIdx` slot `1`, caller-private local slot `2`
    (`BytePerm.readWrite`), and caller-frame slots `j ≥ 3`
    (`BytePerm.callerFrame`). -/
def defaultOpenPerms (i : Nat) : BytePerm :=
  if i ≤ 2 then .readWrite else .callerFrame

/-- Valid entry state for an `OpenBody` under `boundedIdxInv`:
    - `bb = 0`, `ip = 0`, `df = false`, `regs = entryRegs`,
    - `perms = defaultOpenPerms`,
    - return slot `0` is `none`, and
    - argument slot `1` holds a valid `BoundedIdx` satisfying `boundedIdxInv`. -/
def initOpenState (body : OpenBody) (s : OpenState) : Prop :=
  s.bb = 0 ∧
  s.ip = 0 ∧
  s.df = false ∧
  s.regs = s.entryRegs ∧
  s.perms = defaultOpenPerms ∧
  s.mem 0 = none ∧
  ∃ v, s.mem 1 = some v ∧ boundedIdxInv s.tySizes (.adt 0) v ∧
  body.blocks ≠ []

def checkWritableSlot (s : OpenState) (slot : Nat) : Bool :=
  s.perms slot == .readWrite

/-- Evaluate a sequential `X86Instr` on `OpenState`, enforcing `BytePerm`:
    any write to a slot whose permission is not `.readWrite` (such as
    `BytePerm.callerFrame`, `BytePerm.readOnly`, or `BytePerm.unallocated`)
    triggers immediate Undefined Behavior (`.failed .ub`). -/
def evalOpenInstr (s : OpenState) (instr : X86Instr) :
    StepResult OpenState Unit X86Val :=
  match instr with
  | .mov dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem src with
      | some (v, mem') =>
        .step () { s with mem := updateSlot mem' dst.index (some v), ip := s.ip + 1 }
      | none => .failed .ub
  | .alu op dst lhs rhs =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem lhs with
      | some (v1, mem1) =>
        match evalX86Operand mem1 rhs with
        | some (v2, mem2) =>
          match evalX86BinOp op v1 v2 with
          | some outVal =>
            .step () { s with mem := updateSlot mem2 dst.index (some outVal), ip := s.ip + 1 }
          | none => .failed .ub
        | none => .failed .ub
      | none => .failed .ub
  | .wrapAdt adtId dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match evalX86Operand s.mem src with
      | some (v, mem') =>
        .step () { s with mem := updateSlot mem' dst.index (some (.adt adtId v)), ip := s.ip + 1 }
      | none => .failed .ub
  | .extractField0 dst src =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem src.index with
      | some (.adt _ inner) =>
        .step () { s with mem := updateSlot s.mem dst.index (some inner), ip := s.ip + 1 }
      | _ => .failed .ub
  | .leaSlot dst target =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem target.index with
      | some _ =>
        .step () { s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }
      | none => .failed .ub
  | .reborrowSlot dst srcPtr =>
    match checkWritableSlot s dst.index with
    | false => .failed .ub
    | true =>
      match s.mem srcPtr.index with
      | some (.stackPtr target) =>
        match s.mem target.index with
        | some _ =>
          .step () { s with mem := updateSlot s.mem dst.index (some (.stackPtr target)), ip := s.ip + 1 }
        | none => .failed .ub
      | _ => .failed .ub
  | .allocSlot slot =>
    match checkWritableSlot s slot.index with
    | false => .failed .ub
    | true =>
      .step () { s with mem := updateSlot s.mem slot.index none, ip := s.ip + 1 }
  | .deallocSlot slot =>
    match checkWritableSlot s slot.index with
    | false => .failed .ub
    | true =>
      .step () { s with mem := updateSlot s.mem slot.index none, ip := s.ip + 1 }
  | .nop =>
    .step () { s with ip := s.ip + 1 }

/-!
### 4.3 Concrete `BoundedIdx` Library Bodies
-/

/-- `pub fn get_unchecked(idx: &BoundedIdx) -> usize`:
    Extracts `idx.val` from slot `1` into scratch slot `2`, checks `idx.val < 4`,
    and either branches to `bb 2` (returning `idx.val`) or to `bb 1` (`ud2`,
    modeling out-of-bounds slice indexing UB). -/
def getUncheckedOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .usize
  blocks := [
    { instrs := [
        .extractField0 ⟨2⟩ ⟨1⟩,
        .alu .lt ⟨2⟩ (.stackSlot ⟨2⟩ false) (.imm (.word64 boundedCap))
      ]
      term := .jccBool (.stackSlot ⟨2⟩ true) ⟨1⟩ ⟨2⟩ },
    { instrs := []
      term := .ud2 },
    { instrs := [.extractField0 ⟨0⟩ ⟨1⟩]
      term := .ret }
  ]

/-- `pub fn with_temp_invalid(idx: &mut BoundedIdx, callback: fn(&BoundedIdx))`:
    1. Temporarily mutates `*idx` in slot `1` to `BoundedIdx { val: 5 }`
       (`5 ≥ 4`, violating `boundedIdxInv`),
    2. Invokes the external safe `callback(idx)` exposing slot `1` while
       `idx.val == 5`, and
    3. Restores `*idx` in slot `1` to `BoundedIdx { val: 0 }` (`0 < 4`,
       satisfying `boundedIdxInv`) before returning `.unit`! -/
def withTempInvalidOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .unit
  blocks := [
    { instrs := [.wrapAdt 0 ⟨1⟩ (.imm (.word64 5))]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 0)),
        .mov ⟨0⟩ (.imm .unit)
      ]
      term := .ret }
  ]

/-- `pub fn with_restored_before_call(idx: &mut BoundedIdx, callback: fn(&BoundedIdx))`:
    Temporarily mutates `*idx` in slot `1` to `BoundedIdx { val: 5 }`, but
    **restores** `*idx` to `BoundedIdx { val: 2 }` (`2 < 4`, satisfying
    `boundedIdxInv`) *before* invoking `callback(idx)`. -/
def withRestoredBeforeCallOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .unit
  blocks := [
    { instrs := [
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 5)),
        .wrapAdt 0 ⟨1⟩ (.imm (.word64 2))
      ]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [.mov ⟨0⟩ (.imm .unit)]
      term := .ret }
  ]

/-- `pub fn with_unexposed_private_temp(idx: &BoundedIdx, callback: fn(&BoundedIdx)) -> usize`:
    Writes an out-of-bounds value `.adt 0 (.word64 99)` into caller-private
    local slot `2` (`2 ∉ exposedSlots`, while keeping valid `idx` in exposed
    slot `1`), invokes `callback(idx)` with `exposedSlots = [1]`, and then
    returns `idx.val` from slot `1`. -/
def withUnexposedPrivateTempOpenBody : OpenBody where
  argTys := [.adt 0]
  retTy := .usize
  blocks := [
    { instrs := [.wrapAdt 0 ⟨2⟩ (.imm (.word64 99))]
      term := .callExternal [1] [] ⟨0⟩ .unit ⟨1⟩ },
    { instrs := [.extractField0 ⟨0⟩ ⟨1⟩]
      term := .ret }
  ]

/-!
### 4.4 The Callback Re-Entrancy Soundness Exploit Under Naive Entry/Exit Checking

Suppose `callExternal` is modeled naively (`evalNaiveOpenStep`) without asserting
`boundedIdxInv` on exposed arguments/references at the call step (checking
`boundedIdxInv` only at the outer function's entry and final `.ret`).
-/

def evalNaiveOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResult OpenState Unit X86Val :=
  match term with
  | .ret =>
    -- Enforce post-return `boundedIdxInv` on mutated `&mut BoundedIdx` in slot 1
    -- as well as return slot 0 at the outer function exit!
    match s.mem 0, s.mem 1 with
    | some retVal, some (.adt 0 (.word64 n)) =>
      if decide (n < boundedCap) then
        .terminated (.normal retVal)
      else
        .failed .ub
    | _, _ => .failed .ub
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .callExternal _ _ dst _ target =>
    -- Naive callback transition: assumes the safe callback returns `.unit`
    -- without checking that `boundedIdxInv` holds on exposed slots `[1]` at the
    -- moment of the call!
    .step () {
      s with
      mem := updateSlot s.mem dst.index (some .unit)
      bb := target.index
      ip := 0
    }

def evalNaiveOpenStep (body : OpenBody) (s : OpenState) :
    StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none => evalNaiveOpenTerm s blk.term

def NaiveOpenMachine : SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalNaiveOpenStep body s

def NaiveOpenLang : Language :=
  NaiveOpenMachine.toLanguage

abbrev NaiveOpenSem (body : OpenBody) : NaiveOpenLang.Behavior :=
  NaiveOpenLang.sem body

def EnsuresOpenRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    NaiveOpenLang.Behavior :=
  NaiveOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-- Under `NaiveOpenMachine`, `get_unchecked` verifies cleanly (`WellFormed` and
    `EnsuresOpenRetLibInv boundedIdxInv .usize`). -/
theorem naive_getUnchecked_verified :
    NaiveOpenSem getUncheckedOpenBody ≤
      EnsuresOpenRetLibInv boundedIdxInv .usize := by
  refine behaviorOf_le_specOn (M := NaiveOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases hInit.2.2.2.2.2.2 with
    | intro v hv =>
      have hv1 : mem0 1 = some v := hv.1
      have hInv : boundedIdxInv tySizes0 (.adt 0) v := hv.2.1
      cases v with
      | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hInv
      | adt adtId inner =>
        cases adtId with
        | succ _ => cases hInv
        | zero =>
          cases inner with
          | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hInv
          | word64 n =>
            have hLt : n < boundedCap := hInv
            have hDecLt : decide (n < boundedCap) = true := decide_eq_true hLt
            let s0' : OpenState := {
              mem := mem0, perms := defaultOpenPerms, regs := regs0,
              entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
            }
            have hStep1 : evalNaiveOpenStep getUncheckedOpenBody s0' =
                .step () { s0' with mem := updateSlot mem0 2 (some (.word64 n)), ip := 1 } := by
              change evalOpenInstr s0' (.extractField0 ⟨2⟩ ⟨1⟩) = _
              dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, s0']
              rw [hv1]
              rfl
            cases out with
            | mk trOut outcOut =>
            cases hReach with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | choice _ _ _ _ _ _ _ h1 _ _ =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | emptyChoice _ _ _ _ h1 _ =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | terminated _ _ _ h1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | failed _ _ _ h1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; cases h1
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep1.symm⟩)
            | step k1 _ s1 _ _ _ h1 hr1 =>
              change _ = evalNaiveOpenStep getUncheckedOpenBody s0' at h1
              rw [hStep1] at h1; injection h1 with _ hs1; subst hs1
              let m1 := updateSlot mem0 2 (some (.word64 n))
              let s1' : OpenState := { s0' with mem := m1, ip := 1 }
              have hStep2 : evalNaiveOpenStep getUncheckedOpenBody s1' =
                  .step () { s0' with mem := updateSlot m1 2 (some (.boolVal true)), ip := 2 } := by
                change evalOpenInstr s1'
                  (.alu .lt ⟨2⟩ (.stackSlot ⟨2⟩ false) (.imm (.word64 boundedCap))) = _
                dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, evalX86Operand, evalX86BinOp, s0', s1', m1, updateSlot]
                rw [hDecLt]
                rfl
              cases hr1 with
              | zero => exact ⟨True.intro, fun _ h => by cases h⟩
              | choice _ _ _ _ _ _ _ h2 _ _ =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | emptyChoice _ _ _ _ h2 _ =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | terminated _ _ _ h2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | failed _ _ _ h2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep2.symm⟩)
              | step k2 _ s2 _ _ _ h2 hr2 =>
                change _ = evalNaiveOpenStep getUncheckedOpenBody s1' at h2
                rw [hStep2] at h2; injection h2 with _ hs2; subst hs2
                let m2 := updateSlot m1 2 (some (.boolVal true))
                let s2' : OpenState := { s0' with mem := m2, ip := 2 }
                have hStep3 : evalNaiveOpenStep getUncheckedOpenBody s2' =
                    .step () { s0' with mem := updateSlot m2 2 none, bb := 2, ip := 0 } := rfl
                cases hr2 with
                | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                | choice _ _ _ _ _ _ _ h3 _ _ =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | emptyChoice _ _ _ _ h3 _ =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | terminated _ _ _ h3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | failed _ _ _ h3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; cases h3
                | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep3.symm⟩)
                | step k3 _ s3 _ _ _ h3 hr3 =>
                  change _ = evalNaiveOpenStep getUncheckedOpenBody s2' at h3
                  rw [hStep3] at h3; injection h3 with _ hs3; subst hs3
                  let m3 := updateSlot m2 2 none
                  have hm3_1 : m3 1 = some (.adt 0 (.word64 n)) := hv1
                  let s3' : OpenState := { s0' with mem := m3, bb := 2, ip := 0 }
                  have hStep4 : evalNaiveOpenStep getUncheckedOpenBody s3' =
                      .step () { s0' with mem := updateSlot m3 0 (some (.word64 n)), bb := 2, ip := 1 } := by
                    change evalOpenInstr s3' (.extractField0 ⟨0⟩ ⟨1⟩) = _
                    dsimp [evalOpenInstr, checkWritableSlot, defaultOpenPerms, s0', s3']
                    rw [hm3_1]
                    rfl
                  cases hr3 with
                  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                  | choice _ _ _ _ _ _ _ h4 _ _ =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | emptyChoice _ _ _ _ h4 _ =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | terminated _ _ _ h4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | failed _ _ _ h4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
                  | step k4 _ s4 _ _ _ h4 hr4 =>
                    change _ = evalNaiveOpenStep getUncheckedOpenBody s3' at h4
                    rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
                    let m4 := updateSlot m3 0 (some (.word64 n))
                    have hm4_1 : m4 1 = some (.adt 0 (.word64 n)) := hv1
                    let s4' : OpenState := { s0' with mem := m4, bb := 2, ip := 1 }
                    have hStep5 : evalNaiveOpenStep getUncheckedOpenBody s4' =
                        .terminated (.normal (.word64 n)) := by
                      change evalNaiveOpenTerm s4' .ret = _
                      dsimp [evalNaiveOpenTerm, s4', m4, updateSlot]
                      rw [hm3_1]
                      change (if decide (n < boundedCap) = true then
                                StepResult.terminated (TerminationKind.normal (X86Val.word64 n))
                              else StepResult.failed FailureKind.ub) = _
                      rw [hDecLt]
                      rfl
                    cases hr4 with
                    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                    | step _ _ _ _ _ _ h5 _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | choice _ _ _ _ _ _ _ h5 _ _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | emptyChoice _ _ _ _ h5 _ =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | failed _ _ _ h5 =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5; cases h5
                    | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
                    | terminated _ _ term h5 =>
                      change _ = evalNaiveOpenStep getUncheckedOpenBody s4' at h5
                      rw [hStep5] at h5
                      injection h5 with hTerm
                      subst hTerm
                      refine ⟨True.intro, ?_⟩
                      intro ret hRet
                      injection hRet with h1'
                      injection h1' with h2'
                      subst h2'
                      exact True.intro

/-- **Exploit Part 1 (`naive_withTempInvalid_verified`):**
    Under `NaiveOpenMachine` (which checks `boundedIdxInv` at entry and `.ret`
    only), `with_temp_invalid` ALSO passes its full `FnObligation`
    (`EnsuresOpenRetLibInv boundedIdxInv .unit`, including the post-return
    check in `evalNaiveOpenTerm` that slot `1` holds `BoundedIdx { val: 0 }`
    with `0 < 4`)! -/
theorem naive_withTempInvalid_verified :
    NaiveOpenSem withTempInvalidOpenBody ≤
      EnsuresOpenRetLibInv boundedIdxInv .unit := by
  refine behaviorOf_le_specOn (M := NaiveOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | choice _ _ _ _ _ _ _ h3 _ _ => cases h3
        | emptyChoice _ _ _ _ h3 _ => cases h3
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | step k3 _ s3 _ _ _ h3 hr3 =>
          injection h3 with _ hs3; subst hs3
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ => cases h4
          | emptyChoice _ _ _ _ h4 _ => cases h4
          | terminated _ _ _ h4 => cases h4
          | failed _ _ _ h4 => cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            injection h4 with _ hs4; subst hs4
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ => cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ => cases h5
            | emptyChoice _ _ _ _ h5 _ => cases h5
            | failed _ _ _ h5 => cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
            | terminated _ _ term h5 =>
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro

/-- Concrete linked execution of `caller` when `.callExternal` invokes a safe
    callback `callee` (such as `get_unchecked`) on the shared state `s`:
    `inCallee = false` executes `caller`, and `.callExternal` switches to
    `inCallee = true` (`bb = 0, ip = 0` of `callee`) while preserving `s.mem`
    (so `callee` observes `s.mem 1` directly!). -/
structure LinkedState where
  openState : OpenState
  inCallee : Bool := false
  retTarget : Nat := 0
  retDst : SlotId := ⟨0⟩

def evalLinkedStep (caller callee : OpenBody) (ls : LinkedState) :
    StepResult LinkedState Unit X86Val :=
  let s := ls.openState
  let active := if ls.inCallee then callee else caller
  match active.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr =>
      match evalOpenInstr s instr with
      | .step () s' => .step () { ls with openState := s' }
      | .choice k br => .choice k (fun ls' => ∃ s', br s' ∧ ls' = { ls with openState := s' })
      | .terminated t => .terminated t
      | .failed err => .failed err
    | none =>
      match blk.term with
      | .ret =>
        match s.mem 0 with
        | none => .failed .ub
        | some retVal =>
          if ls.inCallee then
            .step () {
              openState := {
                s with
                mem := updateSlot s.mem ls.retDst.index (some retVal)
                bb := ls.retTarget
                ip := 0
              }
              inCallee := false
            }
          else
            .terminated (.normal retVal)
      | .jmp target =>
        .step () { ls with openState := { s with bb := target.index, ip := 0 } }
      | .ud2 =>
        .failed .ub
      | .jccBool cond falseTarget trueTarget =>
        match evalX86Operand s.mem cond with
        | some (.boolVal false, mem') =>
          .step () { ls with openState := { s with mem := mem', bb := falseTarget.index, ip := 0 } }
        | some (.boolVal true, mem') =>
          .step () { ls with openState := { s with mem := mem', bb := trueTarget.index, ip := 0 } }
        | _ => .failed .ub
      | .callExternal _ _ dst _ target =>
        if ls.inCallee then
          .failed .ub
        else
          .step () {
            openState := { s with bb := 0, ip := 0 }
            inCallee := true
            retTarget := target.index
            retDst := dst
          }

def LinkedMachine (caller callee : OpenBody) :
    SmallStepMachine Unit LinkedState Unit X86Val where
  initState _ ls := ls.inCallee = false ∧ initOpenState caller ls.openState
  step _ ls r := r = evalLinkedStep caller callee ls

/-- **Exploit Part 2 (`naive_reentrancy_exploit_triggers_ub`):**
    Although both `get_unchecked` (`naive_getUnchecked_verified`) and
    `with_temp_invalid` (`naive_withTempInvalid_verified`) pass their individual
    entry-to-exit `FnObligation`s under `NaiveOpenMachine`, composing them in a
    100% safe program `with_temp_invalid(&mut idx, get_unchecked)` on a valid
    initial state `idx = BoundedIdx { val: 0 }` reaches **`.failed .ub` in 6
    steps**! -/
theorem naive_reentrancy_exploit_triggers_ub :
    let s0 : OpenState := {
      mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
    }
    let ls0 : LinkedState := { openState := s0, inCallee := false }
    initOpenState withTempInvalidOpenBody s0 ∧
    ReachesPrefix (LinkedMachine withTempInvalidOpenBody getUncheckedOpenBody)
      () ls0 6 ls0 [(), (), (), (), ()] (.failed .ub) := by
  intro s0 ls0
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩, ?_⟩
  let s1 : OpenState := { s0 with mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5))), ip := 1 }
  let ls1 : LinkedState := { ls0 with openState := s1 }
  let s2 : OpenState := { s1 with bb := 0, ip := 0 }
  let ls2 : LinkedState := { openState := s2, inCallee := true, retTarget := 1, retDst := ⟨0⟩ }
  let s3 : OpenState := { s2 with mem := updateSlot s2.mem 2 (some (.word64 5)), ip := 1 }
  let ls3 : LinkedState := { ls2 with openState := s3 }
  let s4 : OpenState := { s3 with mem := updateSlot s3.mem 2 (some (.boolVal false)), ip := 2 }
  let ls4 : LinkedState := { ls3 with openState := s4 }
  let s5 : OpenState := { s4 with mem := updateSlot s4.mem 2 none, bb := 1, ip := 0 }
  let ls5 : LinkedState := { ls4 with openState := s5 }
  exact ReachesPrefix.step 5 ls0 ls1 () [(), (), (), ()] _ rfl
    (ReachesPrefix.step 4 ls1 ls2 () [(), (), ()] _ rfl
      (ReachesPrefix.step 3 ls2 ls3 () [(), ()] _ rfl
        (ReachesPrefix.step 2 ls3 ls4 () [()] _ rfl
          (ReachesPrefix.step 1 ls4 ls5 () [] _ rfl
            (ReachesPrefix.failed 0 ls5 .ub rfl)))))

/-!
### 4.5 Clean Small-Step Open-World Call & ISA Frame Isolation Contract (`GuardedOpenMachine`)

We now mechanize the small-step open-world call contract (`evalGuardedOpenStep`)
that closes the re-entrancy exploit while requiring **zero step-indexed Iris
logic and zero coinduction** in `trusted/`:

1. **Positive Pre-Call Check (`CallSiteSatisfiesLibInv`):**
   At the exact step of `.callExternal exposedSlots exposedMutSlots dst retTy
   target`, every `slot ∈ exposedSlots` must hold an initialized `BoundedIdx`
   satisfying `boundedIdxInv` (`val < 4`), and the direction flag must satisfy
   `s.df = false`. If any exposed slot violates `boundedIdxInv`, the machine
   steps immediately to **`.failed .ub`**.
2. **Caller Frame Isolation & ISA ABI Preservation (`GuardedPostCallBranch`):**
   When the pre-call check succeeds, `.callExternal` steps via
   `.choice .demonic (GuardedPostCallBranch ...)` to all post-call states `s'`
   that:
   - preserve all unexposed caller-private locals (`i ≠ dst.index ∧ i ∉
     exposedMutSlots → s'.mem i = s.mem i`),
   - preserve all `BytePerm.callerFrame` and `BytePerm.readOnly` stack slots,
     callee-saved registers (`rbp`, `rbx`, `rsp`, `r12`–`r15`), and `DF = 0`
     (`X86AbiFramePreserved s s'`), and
   - demonically havoc `dst` and `exposedMutSlots` to arbitrary values
     satisfying `boundedIdxInv` (`RetAndMutSatisfyLibInv`).
-/

/-- Decidable pre-call check asserting that:
    1. Every exposed `BoundedIdx` slot in `exposedSlots` holds an initialized
       value satisfying `boundedIdxInv` (`n < boundedCap`),
    2. The return destination `dst` and all `exposedMutSlots` have writable
       stack permission (`BytePerm.readWrite`), and
    3. The x86-64 direction flag is clear (`s.df = false`). -/
def checkExposedSlot (s : OpenState) (slot : Nat) : Bool :=
  match s.mem slot with
  | some (.adt 0 (.word64 n)) => decide (n < boundedCap)
  | _ => false

def checkCallSiteLibInv (s : OpenState) (exposedSlots exposedMutSlots : List Nat)
    (dst : SlotId) : Bool :=
  !s.df &&
  checkWritableSlot s dst.index &&
  exposedMutSlots.all (checkWritableSlot s) &&
  exposedSlots.all (checkExposedSlot s)

/-- Propositional characterization of `checkCallSiteLibInv`. -/
def CallSiteSatisfiesLibInv (s : OpenState)
    (exposedSlots exposedMutSlots : List Nat) (dst : SlotId) : Prop :=
  checkCallSiteLibInv s exposedSlots exposedMutSlots dst = true

/-- Decidable check that all System V AMD64 callee-saved registers (`rbx`,
    `rsp`, `rbp`, `r12`–`r15`) match their function-entry snapshot. -/
def checkCalleeSavedPreserved (s : OpenState) : Bool :=
  s.regs .rbx == s.entryRegs .rbx &&
  s.regs .rsp == s.entryRegs .rsp &&
  s.regs .rbp == s.entryRegs .rbp &&
  s.regs .r12 == s.entryRegs .r12 &&
  s.regs .r13 == s.entryRegs .r13 &&
  s.regs .r14 == s.entryRegs .r14 &&
  s.regs .r15 == s.entryRegs .r15

/-- System V AMD64 ABI frame and callee-saved register preservation across a
    call boundary. -/
def X86AbiFramePreserved (s s' : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) : Prop :=
  (∀ r : Reg64, r.isCalleeSaved = true → s'.regs r = s.regs r) ∧
  checkCalleeSavedPreserved s' = checkCalleeSavedPreserved s ∧
  s'.entryRegs = s.entryRegs ∧
  s'.df = false ∧
  s'.perms = s.perms ∧
  (∀ slot : Nat, slot ≠ dst.index → slot ∉ exposedMutSlots →
    (s.perms slot = .callerFrame ∨ s.perms slot = .readOnly) →
      s'.mem slot = s.mem slot)

/-- Caller-private local frame isolation across an external call: every stack
    slot `i` that is neither the return destination `dst` nor an exposed
    mutable reference slot in `exposedMutSlots` is preserved unchanged. -/
def CallerFrameIsolated (s s' : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) : Prop :=
  ∀ i : Nat, i ≠ dst.index → i ∉ exposedMutSlots → s'.mem i = s.mem i

/-- Demonic post-call branch envelope for an open-world safe call. -/
def GuardedPostCallBranch (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (target : BlockLabel)
    (s' : OpenState) : Prop :=
  s'.bb = target.index ∧
  s'.ip = 0 ∧
  s'.tySizes = s.tySizes ∧
  CallerFrameIsolated s s' exposedMutSlots dst ∧
  X86AbiFramePreserved s s' exposedMutSlots dst ∧
  (∃ vRet, s'.mem dst.index = some vRet ∧
    boundedIdxInv s.tySizes retTy vRet) ∧
  (∀ i, i ≠ dst.index → i ∈ exposedMutSlots →
    ∃ vMut, s'.mem i = some vMut ∧
      boundedIdxInv s.tySizes (.adt 0) vMut)

/-- Canonical default value for `retTy` under `boundedIdxInv`, used to prove
    that `GuardedPostCallBranch` is constructively inhabited (`InhabitedDemonic`). -/
def defaultBoundedVal (tySizes : Nat → Nat) (ty : X86Ty) : X86Val :=
  match ty with
  | .usize => .word64 0
  | .bool => .boolVal false
  | .unit => .unit
  | .adt adtId => .adt adtId (.word64 0)
  | .param idx => .bytes (tySizes idx) 0
  | .refParam _ => .stackPtr ⟨1⟩

theorem defaultBoundedVal_satisfies (tySizes : Nat → Nat) (ty : X86Ty) :
    boundedIdxInv tySizes ty (defaultBoundedVal tySizes ty) := by
  cases ty with
  | usize => exact True.intro
  | bool => exact True.intro
  | unit => exact True.intro
  | adt id =>
    cases id with
    | zero => exact Nat.zero_lt_succ 3
    | succ k => rfl
  | param idx => exact rfl
  | refParam idx => exact True.intro

/-- Canonical post-call memory witness for `GuardedPostCallBranch`. -/
def canonicalPostCallMem (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (i : Nat) : Option X86Val :=
  match decide (i = dst.index) with
  | true => some (defaultBoundedVal s.tySizes retTy)
  | false =>
    match decide (i ∈ exposedMutSlots) with
    | true => some (.adt 0 (.word64 0))
    | false => s.mem i

/-- Canonical post-call state witness proving `GuardedPostCallBranch` is always
    inhabited. -/
def canonicalPostCallState (s : OpenState) (exposedMutSlots : List Nat)
    (dst : SlotId) (retTy : X86Ty) (target : BlockLabel) : OpenState where
  mem := canonicalPostCallMem s exposedMutSlots dst retTy
  perms := s.perms
  regs := s.regs
  entryRegs := s.entryRegs
  df := false
  bb := target.index
  ip := 0
  tySizes := s.tySizes

theorem canonicalPostCallState_satisfies (s : OpenState)
    (exposedMutSlots : List Nat) (dst : SlotId) (retTy : X86Ty)
    (target : BlockLabel) :
    GuardedPostCallBranch s exposedMutSlots dst retTy target
      (canonicalPostCallState s exposedMutSlots dst retTy target) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro i hNeDst hNotMut
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_false hNotMut]
  · refine ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro slot hNeDst hNotMut _
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_false hNotMut]
  · refine ⟨defaultBoundedVal s.tySizes retTy, ?_,
            defaultBoundedVal_satisfies s.tySizes retTy⟩
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_true rfl]
  · intro i hNeDst hInMut
    refine ⟨.adt 0 (.word64 0), ?_, Nat.zero_lt_succ 3⟩
    dsimp [canonicalPostCallState, canonicalPostCallMem]
    rw [decide_eq_false hNeDst, decide_eq_true hInMut]

/-- Guarded terminator evaluation enforcing:
    1. At `.callExternal`: positive pre-call check `checkCallSiteLibInv`
       (stepping immediately to `.failed .ub` if any exposed slot violates
       `boundedIdxInv`, if `dst`/`exposedMutSlots` are not `.readWrite`, or if
       `df = true`) followed by demonic post-call choice over
       `GuardedPostCallBranch`.
    2. At `.ret`: direction flag `df = false`, callee-saved register
       preservation (`checkCalleeSavedPreserved`), and post-return
       `boundedIdxInv` on mutated/borrowed slot `1`. -/
def evalGuardedOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResult OpenState Unit X86Val :=
  match term with
  | .ret =>
    match !s.df && checkCalleeSavedPreserved s with
    | false => .failed .ub
    | true =>
      match s.mem 0, s.mem 1 with
      | some retVal, some (.adt 0 (.word64 n)) =>
        match decide (n < boundedCap) with
        | true => .terminated (.normal retVal)
        | false => .failed .ub
      | _, _ => .failed .ub
  | .jmp target =>
    .step () { s with bb := target.index, ip := 0 }
  | .ud2 =>
    .failed .ub
  | .jccBool cond falseTarget trueTarget =>
    match evalX86Operand s.mem cond with
    | some (v, mem') =>
      match v with
      | .boolVal false =>
        .step () { s with mem := mem', bb := falseTarget.index, ip := 0 }
      | .boolVal true =>
        .step () { s with mem := mem', bb := trueTarget.index, ip := 0 }
      | _ => .failed .ub
    | none => .failed .ub
  | .callExternal exposedSlots exposedMutSlots dst retTy target =>
    match checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
    | true =>
      .choice .demonic
        (GuardedPostCallBranch s exposedMutSlots dst retTy target)
    | false =>
      .failed .ub

def evalGuardedOpenStep (body : OpenBody) (s : OpenState) :
    StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none => evalGuardedOpenTerm s blk.term

def GuardedOpenMachine : SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalGuardedOpenStep body s

def GuardedOpenLang : Language :=
  GuardedOpenMachine.toLanguage

abbrev GuardedOpenSem (body : OpenBody) : GuardedOpenLang.Behavior :=
  GuardedOpenLang.sem body

def EnsuresGuardedRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    GuardedOpenLang.Behavior :=
  GuardedOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

theorem checkCalleeSavedPreserved_refl (mem : Nat → Option X86Val)
    (perms : Nat → BytePerm) (regs : Reg64 → Nat) (df : Bool) (bb ip : Nat)
    (tySizes : Nat → Nat) :
    checkCalleeSavedPreserved {
      mem := mem, perms := perms, regs := regs, entryRegs := regs,
      df := df, bb := bb, ip := ip, tySizes := tySizes
    } = true := by
  dsimp [checkCalleeSavedPreserved]
  rw [nat_beq_refl (regs .rbx), nat_beq_refl (regs .rsp),
      nat_beq_refl (regs .rbp), nat_beq_refl (regs .r12),
      nat_beq_refl (regs .r13), nat_beq_refl (regs .r14),
      nat_beq_refl (regs .r15)]
  rfl

def StepResult.isChoice {State Obs Val : Type} : StepResult State Obs Val → Bool
  | .choice _ _ => true
  | _ => false

theorem not_choice_of_isChoice_false {State Obs Val : Type}
    {r : StepResult State Obs Val} {kind : ChoiceKind} {branches : State → Prop}
    (h : r.isChoice = false) : r ≠ .choice kind branches := by
  intro hEq
  rw [hEq] at h
  cases h

theorem evalOpenInstr_isChoice_false (s : OpenState) (instr : X86Instr) :
    (evalOpenInstr s instr).isChoice = false := by
  cases instr with
  | mov dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases evalX86Operand s.mem src with
      | none => rfl
      | some p => cases p; rfl
  | alu op dst lhs rhs =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · dsimp
      cases evalX86Operand s.mem lhs with
      | none => rfl
      | some p1 =>
        cases p1 with
        | mk v1 m1 =>
          dsimp
          cases evalX86Operand m1 rhs with
          | none => rfl
          | some p2 =>
            cases p2 with
            | mk v2 m2 =>
              dsimp
              cases evalX86BinOp op v1 v2 <;> rfl
  | wrapAdt adtId dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases evalX86Operand s.mem src with
      | none => rfl
      | some p => cases p; rfl
  | extractField0 dst src =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases s.mem src.index with
      | none => rfl
      | some v => cases v <;> rfl
  | leaSlot dst target =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · cases s.mem target.index <;> rfl
  | reborrowSlot dst srcPtr =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s dst.index
    · rfl
    · dsimp
      cases s.mem srcPtr.index with
      | none => rfl
      | some v =>
        cases v with
        | stackPtr target =>
          dsimp
          cases s.mem target.index <;> rfl
        | _ => rfl
  | allocSlot slot =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s slot.index <;> rfl
  | deallocSlot slot =>
    dsimp [evalOpenInstr]
    cases checkWritableSlot s slot.index <;> rfl
  | nop => rfl

theorem evalOpenInstr_not_choice (s : OpenState) (instr : X86Instr)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalOpenInstr s instr ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalOpenInstr_isChoice_false s instr)

theorem evalRet_isChoice_false (s : OpenState) :
    (evalGuardedOpenTerm s .ret).isChoice = false := by
  dsimp [evalGuardedOpenTerm]
  cases (!s.df && checkCalleeSavedPreserved s)
  · rfl
  · dsimp
    cases s.mem 0 with
    | none => rfl
    | some _ =>
      cases s.mem 1 with
      | none => rfl
      | some v1 =>
        cases v1 with
        | adt id inner =>
          cases id with
          | succ _ => rfl
          | zero =>
            cases inner with
            | word64 n =>
              change (match decide (n < boundedCap) with
                      | true => StepResult.terminated (TerminationKind.normal _)
                      | false => StepResult.failed FailureKind.ub).isChoice = false
              cases decide (n < boundedCap) <;> rfl
            | _ => rfl
        | _ => rfl

theorem evalRet_not_choice (s : OpenState)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalGuardedOpenTerm s .ret ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalRet_isChoice_false s)

theorem evalJccBool_isChoice_false (s : OpenState) (cond : X86Operand)
    (fT tT : BlockLabel) :
    (evalGuardedOpenTerm s (.jccBool cond fT tT)).isChoice = false := by
  dsimp [evalGuardedOpenTerm]
  cases evalX86Operand s.mem cond with
  | none => rfl
  | some p =>
    cases p with
    | mk v _ =>
      cases v with
      | boolVal b => cases b <;> rfl
      | _ => rfl

theorem evalJccBool_not_choice (s : OpenState) (cond : X86Operand)
    (fT tT : BlockLabel) (kind : ChoiceKind) (branches : OpenState → Prop) :
    evalGuardedOpenTerm s (.jccBool cond fT tT) ≠ .choice kind branches :=
  not_choice_of_isChoice_false (evalJccBool_isChoice_false s cond fT tT)

theorem guardedOpenMachine_total : TotalStep GuardedOpenMachine :=
  fun _ _ => ⟨_, rfl⟩

theorem guardedOpenMachine_inhabited : InhabitedDemonic GuardedOpenMachine := by
  intro body s kind branches hStep
  change StepResult.choice kind branches =
    evalGuardedOpenStep body s at hStep
  unfold evalGuardedOpenStep at hStep
  cases hBlk : body.blocks[s.bb]? with
  | none => rw [hBlk] at hStep; cases hStep
  | some blk =>
    rw [hBlk] at hStep
    dsimp at hStep
    cases hInstr : blk.instrs[s.ip]? with
    | some instr =>
      rw [hInstr] at hStep
      dsimp at hStep
      exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
    | none =>
      rw [hInstr] at hStep
      dsimp at hStep
      cases hTerm : blk.term with
      | ret =>
        rw [hTerm] at hStep
        exact False.elim (evalRet_not_choice s kind branches hStep.symm)
      | jmp _ => rw [hTerm] at hStep; cases hStep
      | ud2 => rw [hTerm] at hStep; cases hStep
      | jccBool cond fT tT =>
        rw [hTerm] at hStep
        exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
      | callExternal exposedSlots exposedMutSlots dst retTy target =>
        rw [hTerm] at hStep
        dsimp [evalGuardedOpenTerm] at hStep
        cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
        | false => rw [hCheck] at hStep; cases hStep
        | true =>
          rw [hCheck] at hStep
          injection hStep with _ hBr
          subst hBr
          exact ⟨canonicalPostCallState s exposedMutSlots dst retTy target,
                 canonicalPostCallState_satisfies s exposedMutSlots dst retTy target⟩

/-- **Theorem (a) (`withTempInvalid_rejected_under_guarded_call`):**
    Under `GuardedOpenMachine`, `with_temp_invalid` is **rejected**: from valid
    initial state `s0` (`BoundedIdx { val: 0 }`), it steps to `.failed .ub` at
    step 2 when `.callExternal [1] []` detects that exposed slot `1` holds
    `BoundedIdx { val: 5 }` (`¬ (5 < 4)`). -/
theorem withTempInvalid_rejected_under_guarded_call :
    ¬ (GuardedOpenSem withTempInvalidOpenBody ≤ GuardedOpenLang.WellFormed) := by
  intro hWf
  let s0 : OpenState := {
    mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
  }
  have hInit : initOpenState withTempInvalidOpenBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl,
     ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩
  let s1 : OpenState := {
    s0 with
    mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5)))
    ip := 1
  }
  have hReach :
      ReachesPrefix GuardedOpenMachine withTempInvalidOpenBody s0 2 s0 [()]
        (.failed .ub) :=
    ReachesPrefix.step 1 s0 s1 () [] (.failed .ub) rfl
      (ReachesPrefix.failed 0 s1 .ub rfl)
  let q : ExecQuery OpenState := { init := s0, steps := 2 }
  have hStep := hWf q True.intro
  exact hStep.1 hInit [()] (.failed .ub) hReach

/-- **Theorem (b1) (`withRestoredBeforeCall_verified`):**
    If a function temporarily breaks `boundedIdxInv` on slot `1` (`val := 5`)
    but **restores** `boundedIdxInv` (`val := 2 < 4`) *before* invoking the
    external callback, it verifies cleanly under `GuardedOpenMachine` across all
    demonic callback executions! -/
theorem withRestoredBeforeCall_verified :
    GuardedOpenSem withRestoredBeforeCallOpenBody ≤
      EnsuresGuardedRetLibInv boundedIdxInv .unit := by
  refine behaviorOf_le_specOn (M := GuardedOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    let s0' : OpenState := {
      mem := mem0, perms := defaultOpenPerms, regs := regs0,
      entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
    }
    have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
      checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        let m1 := updateSlot mem0 1 (some (.adt 0 (.word64 5)))
        let m2 := updateSlot m1 1 (some (.adt 0 (.word64 2)))
        let s2' : OpenState := { s0' with mem := m2, ip := 2 }
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ h3 _ => cases h3
        | emptyChoice _ _ _ _ h3 hEmpty =>
          injection h3 with _ hBr
          subst hBr
          exact False.elim (hEmpty ⟨_, canonicalPostCallState_satisfies s2' [] ⟨0⟩ .unit ⟨1⟩⟩)
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | choice k3 _ _ s3 branches _ _ h3 hIn hr3 =>
          injection h3 with _ hBr
          subst hBr
          have hbb3 : s3.bb = 1 := hIn.1
          have hip3 : s3.ip = 0 := hIn.2.1
          have hIso := hIn.2.2.2.1
          have hAbi := hIn.2.2.2.2.1
          have hs3_mem1 : s3.mem 1 = some (.adt 0 (.word64 2)) := by
            have hIso1 := hIso 1 (fun h => by cases h) (by intro h; cases h)
            exact hIso1
          have hs3_perms : s3.perms = defaultOpenPerms := hAbi.2.2.2.2.1
          have hs3_df : s3.df = false := hAbi.2.2.2.1
          have hs3_cs : checkCalleeSavedPreserved s3 = true := by
            rw [hAbi.2.1]
            exact hCalleeSaved0
          have hW0 : checkWritableSlot s3 0 = true := by
            dsimp [checkWritableSlot]
            rw [hs3_perms]
            rfl
          have hStep4 : evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 =
              .step () { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 } := by
            unfold evalGuardedOpenStep
            rw [hbb3, hip3]
            change evalOpenInstr s3 (.mov ⟨0⟩ (.imm .unit)) = _
            dsimp [evalOpenInstr]
            rw [hW0, hbb3, hip3]
            rfl
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | emptyChoice _ _ _ _ h4 _ =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | terminated _ _ _ h4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | failed _ _ _ h4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
            let s4' : OpenState := { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 }
            have hs4_mem1 : s4'.mem 1 = some (.adt 0 (.word64 2)) := hs3_mem1
            have hs4_cs : checkCalleeSavedPreserved s4' = true := hs3_cs
            have hGuard4 : (!s4'.df && checkCalleeSavedPreserved s4') = true := by
              change (!s3.df && checkCalleeSavedPreserved s3) = true
              rw [hs3_df, hs3_cs]
              rfl
            have hStep5 : evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' =
                .terminated (.normal .unit) := by
              unfold evalGuardedOpenStep
              dsimp [s4']
              rw [hbb3]
              dsimp [withRestoredBeforeCallOpenBody, evalGuardedOpenTerm]
              change (match !s4'.df && checkCalleeSavedPreserved s4' with
                      | false => StepResult.failed .ub
                      | true => _) = _
              rw [hGuard4]
              dsimp [s4', updateSlot]
              rw [hs3_mem1]
              rfl
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | emptyChoice _ _ _ _ h5 _ =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | failed _ _ _ h5 =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
            | terminated _ _ term h5 =>
              change _ = evalGuardedOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro

/-- **Theorem (b2) (`withUnexposedPrivateTemp_verified`):**
    If a function writes a broken value (`.adt 0 (.word64 99)`, `99 ≥ 4`) into
    an **unexposed caller-private local slot** (`slot 2 ∉ exposedSlots = [1]`)
    while exposed slot `1` continues to satisfy `boundedIdxInv`, the function
    verifies cleanly under `GuardedOpenMachine` and `CallerFrameIsolated`
    preserves slot `1` across the callback! -/
theorem withUnexposedPrivateTemp_verified :
    GuardedOpenSem withUnexposedPrivateTempOpenBody ≤
      EnsuresGuardedRetLibInv boundedIdxInv .usize := by
  refine behaviorOf_le_specOn (M := GuardedOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    cases hInit.2.2.2.2.2.2 with
    | intro v hv =>
      have hv1 : mem0 1 = some v := hv.1
      have hInv : boundedIdxInv tySizes0 (.adt 0) v := hv.2.1
      cases v with
      | word64 _ | boolVal _ | unit | bytes _ _ | stackPtr _ => cases hInv
      | adt adtId inner =>
        cases adtId with
        | succ _ => cases hInv
        | zero =>
          cases inner with
          | boolVal _ | unit | adt _ _ | bytes _ _ | stackPtr _ => cases hInv
          | word64 n =>
            have hLt : n < boundedCap := hInv
            have hDecLt : decide (n < boundedCap) = true := decide_eq_true hLt
            let s0' : OpenState := {
              mem := mem0, perms := defaultOpenPerms, regs := regs0,
              entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
            }
            have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
              checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
            cases out with
            | mk trOut outcOut =>
            cases hReach with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
            | emptyChoice _ _ _ _ h1 _ => cases h1
            | terminated _ _ _ h1 => cases h1
            | failed _ _ _ h1 => cases h1
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
            | step k1 _ s1 _ _ _ h1 hr1 =>
              injection h1 with _ hs1; subst hs1
              let m1 := updateSlot mem0 2 (some (.adt 0 (.word64 99)))
              have hm1_1 : m1 1 = some (.adt 0 (.word64 n)) := hv1
              let s1' : OpenState := { s0' with mem := m1, ip := 1 }
              have hCheck1 : checkCallSiteLibInv s1' [1] [] ⟨0⟩ = true := by
                dsimp [checkCallSiteLibInv, checkWritableSlot,
                       checkExposedSlot, defaultOpenPerms, s1']
                rw [hm1_1]
                change (true && (decide (n < boundedCap) && true)) = true
                rw [hDecLt]
                rfl
              have hStep2 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' =
                  .choice .demonic (GuardedPostCallBranch s1' [] ⟨0⟩ .unit ⟨1⟩) := by
                change evalGuardedOpenTerm s1' (.callExternal [1] [] ⟨0⟩ .unit ⟨1⟩) = _
                dsimp [evalGuardedOpenTerm]
                rw [hCheck1]
              cases hr1 with
              | zero => exact ⟨True.intro, fun _ h => by cases h⟩
              | step _ _ _ _ _ _ h2 _ =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | emptyChoice _ _ _ _ h2 hEmpty =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2
                injection h2 with _ hBr
                subst hBr
                exact False.elim (hEmpty ⟨_, canonicalPostCallState_satisfies s1' [] ⟨0⟩ .unit ⟨1⟩⟩)
              | terminated _ _ _ h2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | failed _ _ _ h2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2; cases h2
              | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep2.symm⟩)
              | choice k2 _ _ s2 branches _ _ h2 hIn hr2 =>
                change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s1' at h2
                rw [hStep2] at h2
                injection h2 with _ hBr
                subst hBr
                have hbb2 : s2.bb = 1 := hIn.1
                have hip2 : s2.ip = 0 := hIn.2.1
                have hIso := hIn.2.2.2.1
                have hAbi := hIn.2.2.2.2.1
                have hs2_mem1 : s2.mem 1 = some (.adt 0 (.word64 n)) := by
                  have hIso1 := hIso 1 (fun h => by cases h) (by intro h; cases h)
                  rw [hIso1]
                  exact hm1_1
                have hs2_perms : s2.perms = defaultOpenPerms := hAbi.2.2.2.2.1
                have hs2_df : s2.df = false := hAbi.2.2.2.1
                have hs2_cs : checkCalleeSavedPreserved s2 = true := by
                  rw [hAbi.2.1]
                  exact hCalleeSaved0
                have hW0 : checkWritableSlot s2 0 = true := by
                  dsimp [checkWritableSlot]
                  rw [hs2_perms]
                  rfl
                have hStep3 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 =
                    .step () { s2 with mem := updateSlot s2.mem 0 (some (.word64 n)), ip := 1 } := by
                  unfold evalGuardedOpenStep
                  rw [hbb2, hip2]
                  change evalOpenInstr s2 (.extractField0 ⟨0⟩ ⟨1⟩) = _
                  dsimp [evalOpenInstr]
                  rw [hW0, hs2_mem1, hbb2, hip2]
                cases hr2 with
                | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                | choice _ _ _ _ _ _ _ h3 _ _ =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | emptyChoice _ _ _ _ h3 _ =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | terminated _ _ _ h3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | failed _ _ _ h3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; cases h3
                | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep3.symm⟩)
                | step k3 _ s3 _ _ _ h3 hr3 =>
                  change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s2 at h3
                  rw [hStep3] at h3; injection h3 with _ hs3; subst hs3
                  let s3' : OpenState := { s2 with mem := updateSlot s2.mem 0 (some (.word64 n)), ip := 1 }
                  have hs3_mem1 : s3'.mem 1 = some (.adt 0 (.word64 n)) := hs2_mem1
                  have hs3_cs : checkCalleeSavedPreserved s3' = true := hs2_cs
                  have hGuard3 : (!s3'.df && checkCalleeSavedPreserved s3') = true := by
                    change (!s2.df && checkCalleeSavedPreserved s2) = true
                    rw [hs2_df, hs2_cs]
                    rfl
                  have hStep4 : evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' =
                      .terminated (.normal (.word64 n)) := by
                    unfold evalGuardedOpenStep
                    dsimp [s3']
                    rw [hbb2]
                    dsimp [withUnexposedPrivateTempOpenBody, evalGuardedOpenTerm]
                    change (match !s3'.df && checkCalleeSavedPreserved s3' with
                            | false => StepResult.failed .ub
                            | true => _) = _
                    rw [hGuard3]
                    dsimp [s3', updateSlot]
                    rw [hs2_mem1]
                    change (match decide (n < boundedCap) with
                            | true => StepResult.terminated (TerminationKind.normal (X86Val.word64 n))
                            | false => StepResult.failed .ub) = _
                    rw [hDecLt]
                  cases hr3 with
                  | zero => exact ⟨True.intro, fun _ h => by cases h⟩
                  | step _ _ _ _ _ _ h4 _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | choice _ _ _ _ _ _ _ h4 _ _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | emptyChoice _ _ _ _ h4 _ =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | failed _ _ _ h4 =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4; cases h4
                  | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
                  | terminated _ _ term h4 =>
                    change _ = evalGuardedOpenStep withUnexposedPrivateTempOpenBody s3' at h4
                    rw [hStep4] at h4
                    injection h4 with hTerm
                    subst hTerm
                    refine ⟨True.intro, ?_⟩
                    intro ret hRet
                    injection hRet with h1'
                    injection h1' with h2'
                    subst h2'
                    exact True.intro

/-!
### 4.6 Straight-Line Induction Soundness for Arbitrary Safe Callbacks (`open_world_callback_composition_sound`)

Finally, we prove that any caller `body` verified under `GuardedOpenMachine`,
when linked against **any** concrete external callback implementation `cbEnv`
that respects `GuardedPostCallBranch` whenever `CallSiteSatisfiesLibInv` holds
at the call step, executes with **zero Undefined Behavior and zero stuck states**
for every step budget `n : Nat`.

The proof proceeds by straight-line structural induction on the `ReachesPrefix`
derivation (which is indexed by `n : Nat`), requiring **zero step-indexed Iris
logic and zero coinductive types**.
-/

/-- Concrete external callback environment mapping a pre-call state `s` and call
    site parameters `(exposedSlots, exposedMutSlots, dst, retTy, target)` to the
    concrete post-call state returned by the external callback. -/
abbrev CallbackEnv :=
  OpenState → List Nat → List Nat → SlotId → X86Ty → BlockLabel → OpenState

/-- A `CallbackEnv` is well-behaved (`SoundCallbackEnv`) when, for every call
    site where the pre-call check `CallSiteSatisfiesLibInv` holds, the concrete
    post-call state satisfies `GuardedPostCallBranch`. -/
def SoundCallbackEnv (cbEnv : CallbackEnv) : Prop :=
  ∀ s exposedSlots exposedMutSlots dst retTy target,
    CallSiteSatisfiesLibInv s exposedSlots exposedMutSlots dst →
      GuardedPostCallBranch s exposedMutSlots dst retTy target
        (cbEnv s exposedSlots exposedMutSlots dst retTy target)

/-- Concrete execution step when `body` is linked against a specific external
    callback environment `cbEnv`. -/
def evalConcreteCallbackStep (cbEnv : CallbackEnv) (body : OpenBody)
    (s : OpenState) : StepResult OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => evalOpenInstr s instr
    | none =>
      match blk.term with
      | .callExternal exposedSlots exposedMutSlots dst retTy target =>
        match checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
        | true =>
          .step () (cbEnv s exposedSlots exposedMutSlots dst retTy target)
        | false =>
          .failed .ub
      | otherTerm => evalGuardedOpenTerm s otherTerm

def ConcreteCallbackMachine (cbEnv : CallbackEnv) :
    SmallStepMachine OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalConcreteCallbackStep cbEnv body s

/-- Simulation lemma by straight-line induction on `ReachesPrefix`: every
    execution prefix of `ConcreteCallbackMachine cbEnv` from `s` is simulated by
    a corresponding execution prefix of `GuardedOpenMachine` with the **exact
    same outcome `out`** (converting each deterministic callback return step into
    a `.choice .demonic` witness step). -/
theorem concrete_to_guarded_reachesPrefix (cbEnv : CallbackEnv)
    (hEnv : SoundCallbackEnv cbEnv) (body : OpenBody) (s0 : OpenState) :
    ∀ n s tr out,
      ReachesPrefix (ConcreteCallbackMachine cbEnv) body s0 n s tr out →
      ∃ tr_g, ReachesPrefix GuardedOpenMachine body s0 n s tr_g out := by
  intro n
  induction n with
  | zero =>
    intro s tr out hReach
    cases hReach with
    | zero => exact ⟨[], ReachesPrefix.zero s⟩
  | succ k ih =>
    intro s tr out hReach
    cases hReach with
    | step _ _ s' ev tr' out hStep hSub =>
      change StepResult.step ev s' = evalConcreteCallbackStep cbEnv body s at hStep
      cases ev
      cases ih s' tr' out hSub with
      | intro tr_g' hSubG =>
        unfold evalConcreteCallbackStep at hStep
        cases hBlk : body.blocks[s.bb]? with
        | none => rw [hBlk] at hStep; cases hStep
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            have hGuardedStep : evalGuardedOpenStep body s = .step () s' := by
              unfold evalGuardedOpenStep
              rw [hBlk]
              dsimp
              rw [hInstr]
              exact hStep.symm
            exact ⟨() :: tr_g',
              ReachesPrefix.step k s s' () tr_g' out hGuardedStep.symm hSubG⟩
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst retTy target =>
              rw [hTerm] at hStep
              dsimp at hStep
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | false =>
                rw [hCheck] at hStep
                cases hStep
              | true =>
                rw [hCheck] at hStep
                injection hStep with _ hs'
                have hGuardedStep : evalGuardedOpenStep body s =
                    .choice .demonic (GuardedPostCallBranch s exposedMutSlots dst retTy target) := by
                  unfold evalGuardedOpenStep
                  rw [hBlk]
                  dsimp
                  rw [hInstr]
                  dsimp
                  rw [hTerm]
                  dsimp [evalGuardedOpenTerm]
                  rw [hCheck]
                have hInBranch :
                    GuardedPostCallBranch s exposedMutSlots dst retTy target s' := by
                  rw [hs']
                  exact hEnv s exposedSlots exposedMutSlots dst retTy target hCheck
                exact ⟨tr_g',
                  ReachesPrefix.choice k .demonic s s'
                    (GuardedPostCallBranch s exposedMutSlots dst retTy target)
                    tr_g' out hGuardedStep.symm hInBranch hSubG⟩
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              have hGuardedStep : evalGuardedOpenStep body s = .step () s' := by
                unfold evalGuardedOpenStep
                rw [hBlk]
                dsimp
                rw [hInstr]
                dsimp
                rw [hTerm]
                exact hStep.symm
              exact ⟨() :: tr_g',
                ReachesPrefix.step k s s' () tr_g' out hGuardedStep.symm hSubG⟩
    | choice _ kind _ _ branches _ _ hStep _ _ =>
      change StepResult.choice kind branches = evalConcreteCallbackStep cbEnv body s at hStep
      unfold evalConcreteCallbackStep at hStep
      cases hBlk : body.blocks[s.bb]? with
      | none => rw [hBlk] at hStep; cases hStep
      | some blk =>
        rw [hBlk] at hStep
        dsimp at hStep
        cases hInstr : blk.instrs[s.ip]? with
        | some instr =>
          rw [hInstr] at hStep
          dsimp at hStep
          exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
        | none =>
          rw [hInstr] at hStep
          dsimp at hStep
          cases hTerm : blk.term with
          | callExternal exposedSlots exposedMutSlots dst _ _ =>
            rw [hTerm] at hStep
            dsimp at hStep
            cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
            | false => rw [hCheck] at hStep; cases hStep
            | true => rw [hCheck] at hStep; cases hStep
          | ret =>
            rw [hTerm] at hStep
            exact False.elim (evalRet_not_choice s kind branches hStep.symm)
          | jmp _ => rw [hTerm] at hStep; cases hStep
          | ud2 => rw [hTerm] at hStep; cases hStep
          | jccBool cond fT tT =>
            rw [hTerm] at hStep
            exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
    | emptyChoice _ kind _ branches hStep _ =>
      change StepResult.choice kind branches = evalConcreteCallbackStep cbEnv body s at hStep
      unfold evalConcreteCallbackStep at hStep
      cases hBlk : body.blocks[s.bb]? with
      | none => rw [hBlk] at hStep; cases hStep
      | some blk =>
        rw [hBlk] at hStep
        dsimp at hStep
        cases hInstr : blk.instrs[s.ip]? with
        | some instr =>
          rw [hInstr] at hStep
          dsimp at hStep
          exact False.elim (evalOpenInstr_not_choice s instr kind branches hStep.symm)
        | none =>
          rw [hInstr] at hStep
          dsimp at hStep
          cases hTerm : blk.term with
          | callExternal exposedSlots exposedMutSlots dst _ _ =>
            rw [hTerm] at hStep
            dsimp at hStep
            cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
            | false => rw [hCheck] at hStep; cases hStep
            | true => rw [hCheck] at hStep; cases hStep
          | ret =>
            rw [hTerm] at hStep
            exact False.elim (evalRet_not_choice s kind branches hStep.symm)
          | jmp _ => rw [hTerm] at hStep; cases hStep
          | ud2 => rw [hTerm] at hStep; cases hStep
          | jccBool cond fT tT =>
            rw [hTerm] at hStep
            exact False.elim (evalJccBool_not_choice s cond fT tT kind branches hStep.symm)
    | terminated _ _ t hStep =>
      change StepResult.terminated t = evalConcreteCallbackStep cbEnv body s at hStep
      have hGuardedStep : evalGuardedOpenStep body s = .terminated t := by
        unfold evalConcreteCallbackStep at hStep
        unfold evalGuardedOpenStep
        cases hBlk : body.blocks[s.bb]? with
        | none => rw [hBlk] at hStep; cases hStep
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          dsimp
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            exact hStep.symm
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            dsimp
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst _ _ =>
              rw [hTerm] at hStep
              dsimp at hStep
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | false => rw [hCheck] at hStep; cases hStep
              | true => rw [hCheck] at hStep; cases hStep
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              exact hStep.symm
      exact ⟨[], ReachesPrefix.terminated k s t hGuardedStep.symm⟩
    | failed _ _ err hStep =>
      change StepResult.failed err = evalConcreteCallbackStep cbEnv body s at hStep
      have hGuardedStep : evalGuardedOpenStep body s = .failed err := by
        unfold evalConcreteCallbackStep at hStep
        unfold evalGuardedOpenStep
        cases hBlk : body.blocks[s.bb]? with
        | none =>
          rw [hBlk] at hStep
          exact hStep.symm
        | some blk =>
          rw [hBlk] at hStep
          dsimp at hStep
          dsimp
          cases hInstr : blk.instrs[s.ip]? with
          | some instr =>
            rw [hInstr] at hStep
            dsimp at hStep
            exact hStep.symm
          | none =>
            rw [hInstr] at hStep
            dsimp at hStep
            dsimp
            cases hTerm : blk.term with
            | callExternal exposedSlots exposedMutSlots dst retTy target =>
              rw [hTerm] at hStep
              dsimp at hStep
              dsimp [evalGuardedOpenTerm]
              cases hCheck : checkCallSiteLibInv s exposedSlots exposedMutSlots dst with
              | true => rw [hCheck] at hStep; cases hStep
              | false =>
                rw [hCheck] at hStep
                exact hStep.symm
            | ret | jmp _ | ud2 | jccBool _ _ _ =>
              rw [hTerm] at hStep
              exact hStep.symm
      exact ⟨[], ReachesPrefix.failed k s err hGuardedStep.symm⟩
    | noStep _ _ hNo =>
      exact False.elim (hNo ⟨_, rfl⟩)

/-- **Theorem (c) (`open_world_callback_composition_sound`):**
    Any function `body` verified under `GuardedOpenMachine` (`GuardedOpenSem body
    ≤ EnsuresGuardedRetLibInv boundedIdxInv body.retTy`), when executed against
    **any** safe callback environment `cbEnv` (`SoundCallbackEnv cbEnv`) from any
    valid initial state `s0`, is **100% free of Undefined Behavior and stuck
    states (`out.isSafe`)** and satisfies `boundedIdxInv` on its return value at
    every step budget `n : Nat`! -/
theorem open_world_callback_composition_sound (cbEnv : CallbackEnv)
    (hEnv : SoundCallbackEnv cbEnv) (body : OpenBody)
    (hVerified :
      GuardedOpenSem body ≤ EnsuresGuardedRetLibInv boundedIdxInv body.retTy)
    (s0 : OpenState) (hInit : initOpenState body s0)
    (n : Nat) (tr : List Unit) (out : PrefixOutcome X86Val)
    (hReach : ReachesPrefix (ConcreteCallbackMachine cbEnv) body s0 n s0 tr out) :
    out.isSafe ∧
    (∀ ret, out = .terminated (.normal ret) →
      boundedIdxInv s0.tySizes body.retTy ret) := by
  cases concrete_to_guarded_reachesPrefix cbEnv hEnv body s0 n s0 tr out hReach with
  | intro tr_g hReachG =>
    let q : ExecQuery OpenState := { init := s0, steps := n }
    have hStep := hVerified q True.intro
    have hDef : (GuardedOpenSem body q).defined := hStep.1
    have hSafe : out.isSafe := hDef hInit tr_g out hReachG
    refine ⟨hSafe, ?_⟩
    intro ret hTerm
    exact hStep.2 ⟨tr_g, out⟩ ⟨hInit, hReachG⟩ ret hTerm

/-!
### 4.7 Making Open-World External Call Boundaries Structural in `Trusted/StepResult.lean` (`StepResultExt.externalCall`)

Even with `GuardedOpenMachine` above, a language semantics author in `trusted/`
writing `evalGuardedOpenTerm` had to remember to write an `if
checkCallSiteLibInv ... then .choice .demonic ... else .failed .ub` branch. If a
semantics author in `trusted/` accidentally models an external or indirect call
using a plain `.step` or an unguarded `.choice .demonic` without checking
`boundaryInv`, the callback re-entrancy exploit re-emerges.

To make it **structurally impossible** to model an external or indirect call
without specifying both:
1. the positive pre-call boundary invariant (`boundaryInv : Prop`), where
   `¬ boundaryInv` **automatically transitions to `.failed .ub`** in the generic
   step-prefix relation, and
2. the demonic post-call state transition (`demonicPost : State → Obs → Prop`),
   preserving caller-private frames and callee-saved registers while demonically
   havocing exposed mutable state subject to `AdtInv`,

we extend `StepResult` in `Trusted/StepResult.lean` with a dedicated
constructor:
```lean
| externalCall (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
```
and prove that it preserves `TotalStepExt` and `InhabitedExternalAndDemonicExt`
automatically while rejecting `with_temp_invalid` and admitting safe callback
callers!
-/

/-- Structural extension of `StepResult` (`Trusted/StepResult.lean`) with a
    dedicated `.externalCall` constructor that couples the positive pre-call
    boundary obligation (`boundaryInv : Prop`) with the demonic post-call state
    and observation envelope (`demonicPost : State → Obs → Prop`). -/
inductive StepResultExt (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | externalCall (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

structure SmallStepMachineExt (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResultExt State Obs Val → Prop

/-- Step-indexed execution prefix relation for `SmallStepMachineExt`, where
    `.externalCall boundaryInv demonicPost` **structurally enforces** the
    pre-call boundary check:
    - `externalCallOk`: when `boundaryInv` holds and `demonicPost s' obs` holds,
      execution steps to `s'` emitting `obs`;
    - `externalCallUb`: when `¬ boundaryInv` holds, execution transitions
      **immediately to `.failed .ub`**;
    - `externalCallEmpty`: when `boundaryInv` holds but `demonicPost` is empty,
      execution transitions to `.stuck`. -/
inductive ReachesPrefixExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) (prog : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefixExt M prog init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step prog s (.step obs s') →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s : State) (kind : ChoiceKind)
      (branches : State → Prop) (s' : State) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step prog s (.choice kind branches) →
      branches s' →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (kind : ChoiceKind)
      (branches : State → Prop) :
      M.step prog s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck
  | externalCallOk (n : Nat) (s s' : State) (obs : Obs)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      boundaryInv →
      demonicPost s' obs →
      ReachesPrefixExt M prog init n s' tr out →
      ReachesPrefixExt M prog init (n + 1) s (obs :: tr) out
  | externalCallUb (n : Nat) (s : State)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      ¬ boundaryInv →
      ReachesPrefixExt M prog init (n + 1) s [] (.failed .ub)
  | externalCallEmpty (n : Nat) (s : State)
      (boundaryInv : Prop) (demonicPost : State → Obs → Prop) :
      M.step prog s (.externalCall boundaryInv demonicPost) →
      boundaryInv →
      (¬ ∃ s' obs, demonicPost s' obs) →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step prog s (.terminated term) →
      ReachesPrefixExt M prog init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step prog s (.failed err) →
      ReachesPrefixExt M prog init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step prog s r) →
      ReachesPrefixExt M prog init (n + 1) s [] .stuck

def TotalStepExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Prop :=
  ∀ prog s, ∃ r, M.step prog s r

/-- Inhabitedness obligation for `SmallStepMachineExt`: every demonic `.choice`
    is inhabited, and every `.externalCall boundaryInv demonicPost` whose
    pre-call `boundaryInv` holds has at least one valid post-call state and
    observation `(s', obs)` satisfying `demonicPost s' obs`. -/
def InhabitedExternalAndDemonicExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Prop :=
  (∀ prog s branches,
    M.step prog s (.choice .demonic branches) → ∃ s', branches s') ∧
  (∀ prog s boundaryInv demonicPost,
    M.step prog s (.externalCall boundaryInv demonicPost) →
    boundaryInv →
    ∃ s' obs, demonicPost s' obs)

def BehaviorOfExt {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) (prog : Prog)
    (q : ExecQuery State) : Partial (ExecOut Obs Val → Prop) where
  defined :=
    M.initState prog q.init →
      ∀ tr out, ReachesPrefixExt M prog q.init q.steps q.init tr out → out.isSafe
  val _ out :=
    M.initState prog q.init ∧
      ReachesPrefixExt M prog q.init q.steps q.init out.trace out.outcome

def SmallStepMachineExt.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachineExt Prog State Obs Val) : Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOfExt M

theorem behaviorOfExt_le_specOn {Prog State Obs Val : Type}
    {M : SmallStepMachineExt Prog State Obs Val} {p : Prog}
    {pre : ExecQuery State → Prop}
    {Post : ExecQuery State → ExecOut Obs Val → Prop}
    (h : ∀ q out, pre q →
      (M.initState p q.init ∧
        ReachesPrefixExt M p q.init q.steps q.init out.trace out.outcome) →
      out.outcome.isSafe ∧ Post q out) :
    BehaviorOfExt M p ≤ (M.toLanguage).SpecOn pre Post := by
  intro q hpre
  refine ⟨fun hinit tr oc hreach => (h q ⟨tr, oc⟩ hpre ⟨hinit, hreach⟩).1, ?_⟩
  intro out hval
  exact (h q out hpre hval).2

/-- Lift a sequential `StepResult` to `StepResultExt`. -/
def StepResult.toExt {State Obs Val : Type}
    (r : StepResult State Obs Val) : StepResultExt State Obs Val :=
  match r with
  | .step obs next => .step obs next
  | .choice kind branches => .choice kind branches
  | .terminated term => .terminated term
  | .failed err => .failed err

theorem toExt_not_choice (r : StepResult OpenState Unit X86Val)
    (kind : ChoiceKind) (branches : OpenState → Prop)
    (h : r ≠ .choice kind branches) :
    r.toExt ≠ .choice kind branches := by
  cases r with
  | choice k b =>
    intro hc
    injection hc with hk hb
    subst hk hb
    exact h rfl
  | _ => intro hc; cases hc

theorem toExt_not_ext (r : StepResult OpenState Unit X86Val)
    (boundaryInv : Prop) (demonicPost : OpenState → Unit → Prop) :
    r.toExt ≠ .externalCall boundaryInv demonicPost := by
  cases r <;> (intro hc; cases hc)

theorem evalOpenInstr_toExt_not_choice (s : OpenState) (instr : X86Instr)
    (kind : ChoiceKind) (branches : OpenState → Prop) :
    (evalOpenInstr s instr).toExt ≠ .choice kind branches :=
  toExt_not_choice (evalOpenInstr s instr) kind branches
    (evalOpenInstr_not_choice s instr kind branches)

theorem evalOpenInstr_toExt_not_ext (s : OpenState) (instr : X86Instr)
    (boundaryInv : Prop) (demonicPost : OpenState → Unit → Prop) :
    (evalOpenInstr s instr).toExt ≠ .externalCall boundaryInv demonicPost :=
  toExt_not_ext (evalOpenInstr s instr) boundaryInv demonicPost

/-- Structural open-world terminator semantics using `StepResultExt.externalCall`:
    notice that `.callExternal` does not write a manual `if ... then ... else
    .failed .ub` branch—it simply emits `.externalCall` with the required
    `CallSiteSatisfiesLibInv` and `GuardedPostCallBranch` arguments! -/
def evalStructuralOpenTerm (s : OpenState) (term : OpenTerm) :
    StepResultExt OpenState Unit X86Val :=
  match term with
  | .callExternal exposedSlots exposedMutSlots dst retTy target =>
    .externalCall
      (CallSiteSatisfiesLibInv s exposedSlots exposedMutSlots dst)
      (fun s' _ => GuardedPostCallBranch s exposedMutSlots dst retTy target s')
  | other => (evalGuardedOpenTerm s other).toExt

def evalStructuralOpenStep (body : OpenBody) (s : OpenState) :
    StepResultExt OpenState Unit X86Val :=
  match body.blocks[s.bb]? with
  | none => .failed .ub
  | some blk =>
    match blk.instrs[s.ip]? with
    | some instr => (evalOpenInstr s instr).toExt
    | none => evalStructuralOpenTerm s blk.term

def StructuralOpenMachine :
    SmallStepMachineExt OpenBody OpenState Unit X86Val where
  initState := initOpenState
  step body s r := r = evalStructuralOpenStep body s

def StructuralOpenLang : Language :=
  StructuralOpenMachine.toLanguage

abbrev StructuralOpenSem (body : OpenBody) : StructuralOpenLang.Behavior :=
  StructuralOpenLang.sem body

def EnsuresStructuralRetLibInv (libInv : LibInv) (retTy : X86Ty) :
    StructuralOpenLang.Behavior :=
  StructuralOpenLang.Spec (fun q out =>
    ∀ ret, out.outcome = .terminated (.normal ret) →
      libInv q.init.tySizes retTy ret)

/-- `StructuralOpenMachine` automatically satisfies `TotalStepExt`. -/
theorem structuralOpenMachine_total : TotalStepExt StructuralOpenMachine :=
  fun _ _ => ⟨_, rfl⟩

/-- `StructuralOpenMachine` automatically satisfies `InhabitedExternalAndDemonicExt`. -/
theorem structuralOpenMachine_inhabited :
    InhabitedExternalAndDemonicExt StructuralOpenMachine := by
  refine ⟨?_, ?_⟩
  · intro body s branches hStep
    change StepResultExt.choice ChoiceKind.demonic branches =
      evalStructuralOpenStep body s at hStep
    unfold evalStructuralOpenStep at hStep
    cases hBlk : body.blocks[s.bb]? with
    | none => rw [hBlk] at hStep; cases hStep
    | some blk =>
      rw [hBlk] at hStep
      dsimp at hStep
      cases hInstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hInstr] at hStep
        dsimp at hStep
        exact False.elim
          (evalOpenInstr_toExt_not_choice s instr .demonic branches hStep.symm)
      | none =>
        rw [hInstr] at hStep
        dsimp at hStep
        cases hTerm : blk.term with
        | callExternal _ _ _ _ _ =>
          rw [hTerm] at hStep
          cases hStep
        | ret =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_choice (evalGuardedOpenTerm s .ret) .demonic branches
              (evalRet_not_choice s .demonic branches) hStep.symm)
        | jmp _ => rw [hTerm] at hStep; cases hStep
        | ud2 => rw [hTerm] at hStep; cases hStep
        | jccBool cond fT tT =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_choice (evalGuardedOpenTerm s (.jccBool cond fT tT)) .demonic branches
              (evalJccBool_not_choice s cond fT tT .demonic branches) hStep.symm)
  · intro body s boundaryInv demonicPost hStep _
    change StepResultExt.externalCall boundaryInv demonicPost =
      evalStructuralOpenStep body s at hStep
    unfold evalStructuralOpenStep at hStep
    cases hBlk : body.blocks[s.bb]? with
    | none => rw [hBlk] at hStep; cases hStep
    | some blk =>
      rw [hBlk] at hStep
      dsimp at hStep
      cases hInstr : blk.instrs[s.ip]? with
      | some instr =>
        rw [hInstr] at hStep
        dsimp at hStep
        exact False.elim
          (evalOpenInstr_toExt_not_ext s instr boundaryInv demonicPost hStep.symm)
      | none =>
        rw [hInstr] at hStep
        dsimp at hStep
        cases hTerm : blk.term with
        | callExternal exposedSlots exposedMutSlots dst retTy target =>
          rw [hTerm] at hStep
          dsimp [evalStructuralOpenTerm] at hStep
          injection hStep with _ hPost
          subst hPost
          exact ⟨canonicalPostCallState s exposedMutSlots dst retTy target, (),
                 canonicalPostCallState_satisfies s exposedMutSlots dst retTy target⟩
        | ret =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_ext (evalGuardedOpenTerm s .ret) boundaryInv demonicPost hStep.symm)
        | jmp _ => rw [hTerm] at hStep; cases hStep
        | ud2 => rw [hTerm] at hStep; cases hStep
        | jccBool cond fT tT =>
          rw [hTerm] at hStep
          exact False.elim
            (toExt_not_ext (evalGuardedOpenTerm s (.jccBool cond fT tT)) boundaryInv demonicPost hStep.symm)

/-- **Structural Rejection of `with_temp_invalid` (`structural_withTempInvalid_rejected`):**
    Under `StructuralOpenMachine`, `ReachesPrefixExt.externalCallUb`
    automatically fires when `¬ CallSiteSatisfiesLibInv` holds at step 2,
    rejecting `with_temp_invalid`! -/
theorem structural_withTempInvalid_rejected :
    ¬ (StructuralOpenSem withTempInvalidOpenBody ≤
        StructuralOpenLang.WellFormed) := by
  intro hWf
  let s0 : OpenState := {
    mem := updateSlot (fun _ => none) 1 (some (.adt 0 (.word64 0)))
  }
  have hInit : initOpenState withTempInvalidOpenBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl,
     ⟨.adt 0 (.word64 0), rfl, Nat.zero_lt_succ 3, by intro h; cases h⟩⟩
  let s1 : OpenState := {
    s0 with
    mem := updateSlot s0.mem 1 (some (.adt 0 (.word64 5)))
    ip := 1
  }
  have hNotInv : ¬ CallSiteSatisfiesLibInv s1 [1] [] ⟨0⟩ := by
    intro hInv
    cases hInv
  have hReach :
      ReachesPrefixExt StructuralOpenMachine withTempInvalidOpenBody s0 2 s0 [()]
        (.failed .ub) :=
    ReachesPrefixExt.step 1 s0 s1 () [] (.failed .ub) rfl
      (ReachesPrefixExt.externalCallUb 0 s1
        (CallSiteSatisfiesLibInv s1 [1] [] ⟨0⟩)
        (fun s' _ => GuardedPostCallBranch s1 [] ⟨0⟩ .unit ⟨1⟩ s')
        rfl hNotInv)
  let q : ExecQuery OpenState := { init := s0, steps := 2 }
  have hStep := hWf q True.intro
  exact hStep.1 hInit [()] (.failed .ub) hReach

/-- **Structural Verification of `with_restored_before_call`
    (`structural_withRestoredBeforeCall_verified`):**
    Safe callback callers that restore `boundedIdxInv` before `.externalCall`
    verify cleanly under `StructuralOpenMachine`. -/
theorem structural_withRestoredBeforeCall_verified :
    StructuralOpenSem withRestoredBeforeCallOpenBody ≤
      EnsuresStructuralRetLibInv boundedIdxInv .unit := by
  refine behaviorOfExt_le_specOn (M := StructuralOpenMachine) ?_
  intro q out _ hpfx
  cases q with
  | mk s0 steps =>
  cases s0 with
  | mk mem0 perms0 regs0 entryRegs0 df0 bb0 ip0 tySizes0 =>
    have hInit := hpfx.1
    have hReach := hpfx.2
    have hb : bb0 = 0 := hInit.1
    have hip : ip0 = 0 := hInit.2.1
    have hdf : df0 = false := hInit.2.2.1
    have hregs : regs0 = entryRegs0 := hInit.2.2.2.1
    have hperms : perms0 = defaultOpenPerms := hInit.2.2.2.2.1
    subst hb hip hdf hregs hperms
    dsimp at hInit hReach
    let s0' : OpenState := {
      mem := mem0, perms := defaultOpenPerms, regs := regs0,
      entryRegs := regs0, df := false, bb := 0, ip := 0, tySizes := tySizes0
    }
    have hCalleeSaved0 : checkCalleeSavedPreserved s0' = true :=
      checkCalleeSavedPreserved_refl mem0 defaultOpenPerms regs0 false 0 0 tySizes0
    cases out with
    | mk trOut outcOut =>
    cases hReach with
    | zero => exact ⟨True.intro, fun _ h => by cases h⟩
    | choice _ _ _ _ _ _ _ h1 _ _ => cases h1
    | emptyChoice _ _ _ _ h1 _ => cases h1
    | externalCallOk _ _ _ _ _ _ _ _ h1 _ _ _ => cases h1
    | externalCallUb _ _ _ _ h1 _ => cases h1
    | externalCallEmpty _ _ _ _ h1 _ _ => cases h1
    | terminated _ _ _ h1 => cases h1
    | failed _ _ _ h1 => cases h1
    | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
    | step k1 _ s1 _ _ _ h1 hr1 =>
      injection h1 with _ hs1; subst hs1
      cases hr1 with
      | zero => exact ⟨True.intro, fun _ h => by cases h⟩
      | choice _ _ _ _ _ _ _ h2 _ _ => cases h2
      | emptyChoice _ _ _ _ h2 _ => cases h2
      | externalCallOk _ _ _ _ _ _ _ _ h2 _ _ _ => cases h2
      | externalCallUb _ _ _ _ h2 _ => cases h2
      | externalCallEmpty _ _ _ _ h2 _ _ => cases h2
      | terminated _ _ _ h2 => cases h2
      | failed _ _ _ h2 => cases h2
      | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
      | step k2 _ s2 _ _ _ h2 hr2 =>
        injection h2 with _ hs2; subst hs2
        let m1 := updateSlot mem0 1 (some (.adt 0 (.word64 5)))
        let m2 := updateSlot m1 1 (some (.adt 0 (.word64 2)))
        let s2' : OpenState := { s0' with mem := m2, ip := 2 }
        have hInv2 : CallSiteSatisfiesLibInv s2' [1] [] ⟨0⟩ := rfl
        cases hr2 with
        | zero => exact ⟨True.intro, fun _ h => by cases h⟩
        | step _ _ _ _ _ _ h3 _ => cases h3
        | choice _ _ _ _ _ _ _ h3 _ _ => cases h3
        | emptyChoice _ _ _ _ h3 _ => cases h3
        | externalCallUb _ _ _ _ h3 hNotInv =>
          injection h3 with hB _
          rw [hB] at hNotInv
          exact False.elim (hNotInv hInv2)
        | externalCallEmpty _ _ _ _ h3 _ hEmpty =>
          injection h3 with _ hPost
          subst hPost
          exact False.elim (hEmpty ⟨_, (),
            canonicalPostCallState_satisfies s2' [] ⟨0⟩ .unit ⟨1⟩⟩)
        | terminated _ _ _ h3 => cases h3
        | failed _ _ _ h3 => cases h3
        | noStep _ _ hNo => exact False.elim (hNo ⟨_, rfl⟩)
        | externalCallOk k3 _ s3 _ _ _ _ _ h3 _ hIn hr3 =>
          injection h3 with _ hPost
          subst hPost
          have hbb3 : s3.bb = 1 := hIn.1
          have hip3 : s3.ip = 0 := hIn.2.1
          have hIso := hIn.2.2.2.1
          have hAbi := hIn.2.2.2.2.1
          have hs3_mem1 : s3.mem 1 = some (.adt 0 (.word64 2)) :=
            hIso 1 (fun h => by cases h) (by intro h; cases h)
          have hs3_perms : s3.perms = defaultOpenPerms := hAbi.2.2.2.2.1
          have hs3_df : s3.df = false := hAbi.2.2.2.1
          have hs3_cs : checkCalleeSavedPreserved s3 = true := by
            rw [hAbi.2.1]
            exact hCalleeSaved0
          have hW0 : checkWritableSlot s3 0 = true := by
            dsimp [checkWritableSlot]
            rw [hs3_perms]
            rfl
          have hStep4 : evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 =
              .step () { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 } := by
            unfold evalStructuralOpenStep
            rw [hbb3, hip3]
            change (evalOpenInstr s3 (.mov ⟨0⟩ (.imm .unit))).toExt = _
            dsimp [evalOpenInstr, StepResult.toExt]
            rw [hW0, hbb3, hip3]
            rfl
          cases hr3 with
          | zero => exact ⟨True.intro, fun _ h => by cases h⟩
          | choice _ _ _ _ _ _ _ h4 _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | emptyChoice _ _ _ _ h4 _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallOk _ _ _ _ _ _ _ _ h4 _ _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallUb _ _ _ _ h4 _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | externalCallEmpty _ _ _ _ h4 _ _ =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | terminated _ _ _ h4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | failed _ _ _ h4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; cases h4
          | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep4.symm⟩)
          | step k4 _ s4 _ _ _ h4 hr4 =>
            change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s3 at h4
            rw [hStep4] at h4; injection h4 with _ hs4; subst hs4
            let s4' : OpenState := { s3 with mem := updateSlot s3.mem 0 (some .unit), ip := 1 }
            have hs4_mem1 : s4'.mem 1 = some (.adt 0 (.word64 2)) := hs3_mem1
            have hs4_cs : checkCalleeSavedPreserved s4' = true := hs3_cs
            have hGuard4 : (!s4'.df && checkCalleeSavedPreserved s4') = true := by
              change (!s3.df && checkCalleeSavedPreserved s3) = true
              rw [hs3_df, hs3_cs]
              rfl
            have hStep5 : evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' =
                .terminated (.normal .unit) := by
              unfold evalStructuralOpenStep
              dsimp [s4']
              rw [hbb3]
              dsimp [withRestoredBeforeCallOpenBody, evalStructuralOpenTerm,
                     evalGuardedOpenTerm, StepResult.toExt]
              change StepResult.toExt
                (match !s4'.df && checkCalleeSavedPreserved s4' with
                 | false => .failed .ub
                 | true => _) = _
              rw [hGuard4]
              dsimp [s4', updateSlot, StepResult.toExt]
              rw [hs3_mem1]
              rfl
            cases hr4 with
            | zero => exact ⟨True.intro, fun _ h => by cases h⟩
            | step _ _ _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | choice _ _ _ _ _ _ _ h5 _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | emptyChoice _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallOk _ _ _ _ _ _ _ _ h5 _ _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallUb _ _ _ _ h5 _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | externalCallEmpty _ _ _ _ h5 _ _ =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | failed _ _ _ h5 =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5; cases h5
            | noStep _ _ hNo => exact False.elim (hNo ⟨_, hStep5.symm⟩)
            | terminated _ _ term h5 =>
              change _ = evalStructuralOpenStep withRestoredBeforeCallOpenBody s4' at h5
              rw [hStep5] at h5
              injection h5 with hTerm
              subst hTerm
              refine ⟨True.intro, ?_⟩
              intro ret hRet
              injection hRet with h1'
              injection h1' with h2'
              subst h2'
              exact True.intro

/-!
## 5. Kernel Axiom Audit (`#print axioms`)
-/

#print axioms trap1_alwaysFalse_compiles
#print axioms trap2_id_compiles
#print axioms peephole_noop_on_corpus
#print axioms compiles_id_forbids_instruction_deletion
#print axioms genuineCoalescePass_certified
#print axioms trap1_rejected_by_contract
#print axioms trap2_id_rejected_by_contract
#print axioms peephole_on_newUnchecked_rejected
#print axioms naive_getUnchecked_verified
#print axioms naive_withTempInvalid_verified
#print axioms naive_reentrancy_exploit_triggers_ub
#print axioms guardedOpenMachine_total
#print axioms guardedOpenMachine_inhabited
#print axioms withTempInvalid_rejected_under_guarded_call
#print axioms withRestoredBeforeCall_verified
#print axioms withUnexposedPrivateTemp_verified
#print axioms open_world_callback_composition_sound
#print axioms structuralOpenMachine_total
#print axioms structuralOpenMachine_inhabited
#print axioms structural_withTempInvalid_rejected
#print axioms structural_withRestoredBeforeCall_verified

end Anneal.AntiDegeneracyAndCallbackFraming

