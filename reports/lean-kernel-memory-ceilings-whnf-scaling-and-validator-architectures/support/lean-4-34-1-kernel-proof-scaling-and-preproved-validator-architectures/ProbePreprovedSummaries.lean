-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Pre-Proved Stdlib & Intrinsic Summaries (`ProbePreprovedSummaries.lean`)

This self-contained Lean 4.34.1 probe models `Trusted/MirSemantics.lean`'s
interprocedural call-stack machine (`FnTable`, `LayoutEnv`, `AdtInv`,
`CallFrame`, `Terminator.call1`, `Terminator.return_`) and benchmarks:

1. **Universal Stack-Frame Lifting (`call1_summary_sound`)**:
   Proving once in `theory/Anneal/` that any callee satisfying a stack-neutral
   `CalleeSummary` contract can be invoked from an arbitrary caller frame and
   call stack `s.stack` in a single compositional transition, without unfolding
   the callee's `MirBody`.
2. **Pre-Proved Polymorphic Stdlib & Intrinsic Summary Table**:
   10 polymorphic `core` operations (`Option::unwrap_or`, `Option::is_some`,
   `NonZeroUsize::new`, `checked_add`, `wrapping_add`, `size_of`, `align_of`,
   `transmute_copy`, `slice::len`, `slice::get`) parameterized over arbitrary
   types `T : Ty`, `layout : LayoutEnv`, and `adtInv : AdtInv`.
3. **Quantitative Comparison (Naive Unnormalized Inlining vs. Normalized Inline
   Callee Re-Verification vs. Pre-Proved Summary Instantiation)** across callers
   invoking $K \in \{2, 5, 10\}$ stdlib helpers.
-/

open Lean

namespace ProbePreprovedSummaries

/-!
## 1. Types, Values, Layout Environment, and ADT Invariants
-/

inductive Ty where
  | usize
  | bool
  | option (inner : Ty)
  | nonZeroUsize
  | sliceRef (elem : Ty)
  | customAdt (id : Nat)
  deriving Repr, DecidableEq

inductive Val where
  | usize (n : Nat)
  | bool (b : Bool)
  | noneVal
  | someVal (v : Val)
  | sliceFatPtr (base : Nat) (len : Nat)
  deriving Repr, DecidableEq

/-- Symbolic layout environment mapping each `Ty` to its `(size, align)` in
    bytes, mirroring `LayoutEnv` / `tySizes` in `Trusted/MirSemantics.lean`. -/
structure LayoutEnv where
  sizeOf : Ty → Nat
  alignOf : Ty → Nat

/-- Symbolic ADT validity invariant mapping `(Ty, Val)` to `Bool`, mirroring
    `AdtInv` in `Trusted/MirSemantics.lean`. -/
abbrev AdtInv := Ty → Val → Bool

def defaultAdtInv : AdtInv
  | .nonZeroUsize, .usize n => !(n == 0)
  | _, _ => true

/-!
## 2. Pure Mathematical Specifications of the 10 `core` Operations
-/

def specUnwrapOr (v1 v2 : Val) : Val :=
  match v1 with
  | .someVal v => v
  | _ => v2

def specIsSome (v1 : Val) : Val :=
  match v1 with
  | .someVal _ => .bool true
  | _ => .bool false

def specNonZeroNew (adtInv : AdtInv) (v1 : Val) : Val :=
  match v1 with
  | .usize n => if adtInv .nonZeroUsize (.usize n) then .someVal (.usize n) else .noneVal
  | _ => .noneVal

def specCheckedAdd (maxUsize : Nat) (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .usize a, .usize b =>
    if decide (a + b ≤ maxUsize) then .someVal (.usize (a + b)) else .noneVal
  | _, _ => .noneVal

def specWrappingAdd (modulus : Nat) (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .usize a, .usize b => .usize ((a + b) % modulus)
  | _, _ => .usize 0

def specSizeOf (layout : LayoutEnv) (ty : Ty) : Val :=
  .usize (layout.sizeOf ty)

def specAlignOf (layout : LayoutEnv) (ty : Ty) : Val :=
  .usize (layout.alignOf ty)

def specTransmuteCopy (layout : LayoutEnv) (adtInv : AdtInv) (srcTy dstTy : Ty) (v1 : Val) : Val :=
  if layout.sizeOf srcTy == layout.sizeOf dstTy && adtInv dstTy v1 then
    .someVal v1
  else
    .noneVal

def specSliceLen (v1 : Val) : Val :=
  match v1 with
  | .sliceFatPtr _ len => .usize len
  | _ => .usize 0

def specSliceGet (v1 v2 : Val) : Val :=
  match v1, v2 with
  | .sliceFatPtr base len, .usize idx =>
    if decide (idx < len) then .someVal (.usize (base + idx)) else .noneVal
  | _, _ => .noneVal

/-!
## 3. Interprocedural Call-Stack MIR Semantics (Mirroring `MirSemantics.lean`)
-/

inductive Stmt where
  | assignConst (dst : Nat) (v : Val)
  | assignCopy (dst : Nat) (src : Nat)
  | unwrapOrStep (dst : Nat) (optSrc : Nat) (defSrc : Nat)
  | isSomeStep (dst : Nat) (optSrc : Nat)
  | nonZeroNewStep (dst : Nat) (src : Nat)
  | checkedAddStep (dst : Nat) (lhs : Nat) (rhs : Nat) (maxUsize : Nat)
  | wrappingAddStep (dst : Nat) (lhs : Nat) (rhs : Nat) (modulus : Nat)
  | sizeOfStep (dst : Nat) (ty : Ty)
  | alignOfStep (dst : Nat) (ty : Ty)
  | transmuteCopyStep (dst : Nat) (src : Nat) (srcTy dstTy : Ty)
  | sliceLenStep (dst : Nat) (sliceSrc : Nat)
  | sliceGetStep (dst : Nat) (sliceSrc : Nat) (idxSrc : Nat)
  deriving Repr, DecidableEq

inductive Terminator where
  | goto (target : Nat)
  | call1 (dest : Nat) (callee : Nat) (arg1 : Nat) (arg2 : Nat) (target : Nat)
  | return_
  deriving Repr, DecidableEq

structure BasicBlock where
  stmts : List Stmt
  term : Terminator
  deriving Repr, DecidableEq

structure MirBody where
  blocks : List BasicBlock
  deriving Repr, DecidableEq

/-- Saved caller activation record on the call stack, mirroring `CallFrame` in
    `Trusted/MirSemantics.lean:160-169`. -/
structure CallFrame where
  returnBody : MirBody
  locals : Nat → Option Val
  returnBlock : Nat
  destLocal : Nat

/-- Operational machine state with an explicit interprocedural `stack`. -/
structure MirState where
  curBody : MirBody
  locals : Nat → Option Val
  block : Nat
  stmtIdx : Nat
  stack : List CallFrame

def updateLocal (locals : Nat → Option Val) (idx : Nat) (v : Option Val) :
    Nat → Option Val :=
  fun i => if i == idx then v else locals i

def initCalleeLocals (arg1Val arg2Val : Val) : Nat → Option Val :=
  fun i =>
    if i == 1 then some arg1Val
    else if i == 2 then some arg2Val
    else none

/-- Execute one statement in `MirState` under `(layout, adtInv)`. -/
def evalStmt (layout : LayoutEnv) (adtInv : AdtInv) (s : MirState) (st : Stmt) :
    Option MirState :=
  match st with
  | .assignConst dst v =>
    some { s with locals := updateLocal s.locals dst (some v), stmtIdx := s.stmtIdx + 1 }
  | .assignCopy dst src =>
    match s.locals src with
    | some v =>
      some { s with locals := updateLocal s.locals dst (some v), stmtIdx := s.stmtIdx + 1 }
    | none => none
  | .unwrapOrStep dst optSrc defSrc =>
    match s.locals optSrc, s.locals defSrc with
    | some v1, some v2 =>
      some { s with locals := updateLocal s.locals dst (some (specUnwrapOr v1 v2)),
                    stmtIdx := s.stmtIdx + 1 }
    | _, _ => none
  | .isSomeStep dst optSrc =>
    match s.locals optSrc with
    | some v1 =>
      some { s with locals := updateLocal s.locals dst (some (specIsSome v1)),
                    stmtIdx := s.stmtIdx + 1 }
    | none => none
  | .nonZeroNewStep dst src =>
    match s.locals src with
    | some v1 =>
      some { s with locals := updateLocal s.locals dst (some (specNonZeroNew adtInv v1)),
                    stmtIdx := s.stmtIdx + 1 }
    | none => none
  | .checkedAddStep dst lhs rhs maxUsize =>
    match s.locals lhs, s.locals rhs with
    | some v1, some v2 =>
      some { s with locals := updateLocal s.locals dst (some (specCheckedAdd maxUsize v1 v2)),
                    stmtIdx := s.stmtIdx + 1 }
    | _, _ => none
  | .wrappingAddStep dst lhs rhs modulus =>
    match s.locals lhs, s.locals rhs with
    | some v1, some v2 =>
      some { s with locals := updateLocal s.locals dst (some (specWrappingAdd modulus v1 v2)),
                    stmtIdx := s.stmtIdx + 1 }
    | _, _ => none
  | .sizeOfStep dst ty =>
    some { s with locals := updateLocal s.locals dst (some (specSizeOf layout ty)),
                  stmtIdx := s.stmtIdx + 1 }
  | .alignOfStep dst ty =>
    some { s with locals := updateLocal s.locals dst (some (specAlignOf layout ty)),
                  stmtIdx := s.stmtIdx + 1 }
  | .transmuteCopyStep dst src srcTy dstTy =>
    match s.locals src with
    | some v1 =>
      some { s with locals := updateLocal s.locals dst
                      (some (specTransmuteCopy layout adtInv srcTy dstTy v1)),
                    stmtIdx := s.stmtIdx + 1 }
    | none => none
  | .sliceLenStep dst sliceSrc =>
    match s.locals sliceSrc with
    | some v1 =>
      some { s with locals := updateLocal s.locals dst (some (specSliceLen v1)),
                    stmtIdx := s.stmtIdx + 1 }
    | none => none
  | .sliceGetStep dst sliceSrc idxSrc =>
    match s.locals sliceSrc, s.locals idxSrc with
    | some v1, some v2 =>
      some { s with locals := updateLocal s.locals dst (some (specSliceGet v1 v2)),
                    stmtIdx := s.stmtIdx + 1 }
    | _, _ => none

inductive StepOut where
  | step (next : MirState)
  | returned (retVal : Val)
  | stuck

abbrev FnTable := Nat → Option MirBody

/-- Small-step operational semantics with call stack (`call1` pushes a
    `CallFrame`; `return_` pops the top `CallFrame` or finishes when `stack = []`). -/
def evalMirStep (fnTable : FnTable) (layout : LayoutEnv) (adtInv : AdtInv)
    (s : MirState) : StepOut :=
  match s.curBody.blocks[s.block]? with
  | none => .stuck
  | some bb =>
    match bb.stmts[s.stmtIdx]? with
    | some st =>
      match evalStmt layout adtInv s st with
      | some s' => .step s'
      | none => .stuck
    | none =>
      match bb.term with
      | .goto target =>
        .step { s with block := target, stmtIdx := 0 }
      | .call1 dest calleeId arg1 arg2 target =>
        match fnTable calleeId, s.locals arg1, s.locals arg2 with
        | some calleeBody, some v1, some v2 =>
          let frame : CallFrame := {
            returnBody := s.curBody
            locals := s.locals
            returnBlock := target
            destLocal := dest
          }
          .step {
            curBody := calleeBody
            locals := initCalleeLocals v1 v2
            block := 0
            stmtIdx := 0
            stack := frame :: s.stack
          }
        | _, _, _ => .stuck
      | .return_ =>
        match s.locals 0, s.stack with
        | some retVal, [] => .returned retVal
        | some retVal, frame :: restStack =>
          .step {
            curBody := frame.returnBody
            locals := updateLocal frame.locals frame.destLocal (some retVal)
            block := frame.returnBlock
            stmtIdx := 0
            stack := restStack
          }
        | none, _ => .stuck

inductive SafeReaches (fnTable : FnTable) (layout : LayoutEnv) (adtInv : AdtInv) :
    MirState → Val → Prop where
  | of_ret {s : MirState} {v : Val}
      (h : evalMirStep fnTable layout adtInv s = .returned v) :
      SafeReaches fnTable layout adtInv s v
  | of_step {s s' : MirState} {v : Val}
      (h : evalMirStep fnTable layout adtInv s = .step s')
      (hnext : SafeReaches fnTable layout adtInv s' v) :
      SafeReaches fnTable layout adtInv s v

/-!
## 4. Universal Stack-Frame Lifting Theorem (`call1_summary_sound`)
-/

/-- Pre-proved summary contract for a 2-argument stdlib/intrinsic callee `calleeId`:
    From any stack `frame :: restStack`, starting `calleeBody` at
    `(block = 0, stmtIdx = 0)` with arguments `(v1, v2)` steps deterministically
    through `calleeBody` to `.return_` with `locals 0 = some (specFn layout adtInv v1 v2)`
    and pops `frame`. -/
def CalleeSummary (fnTable : FnTable) (layout : LayoutEnv) (adtInv : AdtInv)
    (calleeId : Nat) (specFn : LayoutEnv → AdtInv → Val → Val → Val) : Prop :=
  ∃ calleeBody,
    fnTable calleeId = some calleeBody ∧
    ∀ (frame : CallFrame) (restStack : List CallFrame) (v1 v2 : Val) (finalRet : Val),
      SafeReaches fnTable layout adtInv {
        curBody := frame.returnBody
        locals := updateLocal frame.locals frame.destLocal (some (specFn layout adtInv v1 v2))
        block := frame.returnBlock
        stmtIdx := 0
        stack := restStack
      } finalRet →
      SafeReaches fnTable layout adtInv {
        curBody := calleeBody
        locals := initCalleeLocals v1 v2
        block := 0
        stmtIdx := 0
        stack := frame :: restStack
      } finalRet

/-- **Universal Call-Site Frame-Lifting Theorem (`call1_summary_sound`)**:
    Proved once in `theory/Anneal/`. Discharges any `.call1` terminator in a
    single step using the callee's pre-proved `CalleeSummary`, normalizing the
    output value `vOut` via `hOut : specFn layout adtInv v1 v2 = vOut` so
    subsequent calls do not accumulate unreduced `specFn` closures. -/
theorem call1_summary_sound
    {fnTable : FnTable} {layout : LayoutEnv} {adtInv : AdtInv}
    {s : MirState} {bb : BasicBlock}
    {dest calleeId arg1 arg2 target : Nat}
    {v1 v2 vOut : Val}
    {specFn : LayoutEnv → AdtInv → Val → Val → Val}
    {finalRet : Val}
    (hSummary : CalleeSummary fnTable layout adtInv calleeId specFn)
    (hbb : s.curBody.blocks[s.block]? = some bb)
    (hstmt : bb.stmts[s.stmtIdx]? = none)
    (hterm : bb.term = .call1 dest calleeId arg1 arg2 target)
    (harg1 : s.locals arg1 = some v1)
    (harg2 : s.locals arg2 = some v2)
    (hOut : specFn layout adtInv v1 v2 = vOut)
    (hAfter : SafeReaches fnTable layout adtInv {
      s with
      locals := updateLocal s.locals dest (some vOut)
      block := target
      stmtIdx := 0
    } finalRet) :
    SafeReaches fnTable layout adtInv s finalRet := by
  have ⟨calleeBody, hFn, hCallee⟩ := hSummary
  let frame : CallFrame := {
    returnBody := s.curBody
    locals := s.locals
    returnBlock := target
    destLocal := dest
  }
  have hStepCall : evalMirStep fnTable layout adtInv s = .step {
      curBody := calleeBody
      locals := initCalleeLocals v1 v2
      block := 0
      stmtIdx := 0
      stack := frame :: s.stack
    } := by
    unfold evalMirStep
    rw [hbb]; dsimp; rw [hstmt]; dsimp; rw [hterm]; dsimp
    rw [hFn, harg1, harg2]
  rw [← hOut] at hAfter
  exact SafeReaches.of_step hStepCall (hCallee frame s.stack v1 v2 finalRet hAfter)

/-- **Flat-Projection Call-Site Frame-Lifting Theorem (`call1_summary_flat_sound`)**:
    Avoids `{ s with locals := updateLocal s.locals ... }` record-update
    desugaring (which mentions `s` three times per step: `s.curBody`,
    `s.locals`, `s.stack`, causing $O(3^K)$ unshared tree growth across $K$
    chained calls) by operating directly on `⟨curBody, locals, blk, 0, stk⟩`. -/
theorem call1_summary_flat_sound
    {fnTable : FnTable} {layout : LayoutEnv} {adtInv : AdtInv}
    {curBody : MirBody} {locals : Nat → Option Val} {blk : Nat} {stk : List CallFrame}
    {bb : BasicBlock}
    {dest calleeId arg1 arg2 target : Nat}
    {v1 v2 vOut : Val}
    {specFn : LayoutEnv → AdtInv → Val → Val → Val}
    {finalRet : Val}
    (hSummary : CalleeSummary fnTable layout adtInv calleeId specFn)
    (hbb : curBody.blocks[blk]? = some bb)
    (hstmt : bb.stmts[0]? = none)
    (hterm : bb.term = .call1 dest calleeId arg1 arg2 target)
    (harg1 : locals arg1 = some v1)
    (harg2 : locals arg2 = some v2)
    (hOut : specFn layout adtInv v1 v2 = vOut)
    (hAfter : SafeReaches fnTable layout adtInv
      ⟨curBody, updateLocal locals dest (some vOut), target, 0, stk⟩ finalRet) :
    SafeReaches fnTable layout adtInv ⟨curBody, locals, blk, 0, stk⟩ finalRet :=
  call1_summary_sound hSummary hbb hstmt hterm harg1 harg2 hOut hAfter

/-!
## 5. Pre-Proved Summary Table for 10 Polymorphic `core` Intrinsics & Helpers
-/

def mkStdlibCalleeBody (opStmt : Stmt) : MirBody := {
  blocks := [
    -- bb0: copy _1 -> _3; copy _2 -> _4; goto bb1
    { stmts := [.assignCopy 3 1, .assignCopy 4 2]
      term := .goto 1 },
    -- bb1: opStmt (writes _5 from _3, _4); copy _5 -> _0; goto bb2
    { stmts := [opStmt, .assignCopy 0 5]
      term := .goto 2 },
    -- bb2: return
    { stmts := []
      term := .return_ }
  ]
}

def bodyUnwrapOr : MirBody := mkStdlibCalleeBody (.unwrapOrStep 5 3 4)
def bodyIsSome : MirBody := mkStdlibCalleeBody (.isSomeStep 5 3)
def bodyNonZeroNew : MirBody := mkStdlibCalleeBody (.nonZeroNewStep 5 3)
def bodyCheckedAdd : MirBody := mkStdlibCalleeBody (.checkedAddStep 5 3 4 65535)
def bodyWrappingAdd : MirBody := mkStdlibCalleeBody (.wrappingAddStep 5 3 4 65536)
def bodySizeOf (ty : Ty) : MirBody := mkStdlibCalleeBody (.sizeOfStep 5 ty)
def bodyAlignOf (ty : Ty) : MirBody := mkStdlibCalleeBody (.alignOfStep 5 ty)
def bodyTransmuteCopy (srcTy dstTy : Ty) : MirBody :=
  mkStdlibCalleeBody (.transmuteCopyStep 5 3 srcTy dstTy)
def bodySliceLen : MirBody := mkStdlibCalleeBody (.sliceLenStep 5 3)
def bodySliceGet : MirBody := mkStdlibCalleeBody (.sliceGetStep 5 3 4)

def stdlibFnTable (ty : Ty) : FnTable
  | 101 => some bodyUnwrapOr
  | 102 => some bodyIsSome
  | 103 => some bodyNonZeroNew
  | 104 => some bodyCheckedAdd
  | 105 => some bodyWrappingAdd
  | 106 => some (bodySizeOf ty)
  | 107 => some (bodyAlignOf ty)
  | 108 => some (bodyTransmuteCopy ty ty)
  | 109 => some bodySliceLen
  | 110 => some bodySliceGet
  | _ => none

/-- Generic 7-step soundness schema for any `mkStdlibCalleeBody opStmt` whose
    `opStmt` evaluates to `some vOut` on `_3 = v1, _4 = v2`. -/
theorem mkStdlibCalleeBody_sound
    {fnTable : FnTable} {layout : LayoutEnv} {adtInv : AdtInv}
    {opStmt : Stmt} {frame : CallFrame} {restStack : List CallFrame}
    {v1 v2 vOut finalRet : Val}
    (hOp : evalStmt layout adtInv {
      curBody := mkStdlibCalleeBody opStmt
      locals := updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)
      block := 1
      stmtIdx := 0
      stack := frame :: restStack
    } opStmt = some {
      curBody := mkStdlibCalleeBody opStmt
      locals := updateLocal
        (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2))
        5 (some vOut)
      block := 1
      stmtIdx := 1
      stack := frame :: restStack
    })
    (hAfter : SafeReaches fnTable layout adtInv {
      curBody := frame.returnBody
      locals := updateLocal frame.locals frame.destLocal (some vOut)
      block := frame.returnBlock
      stmtIdx := 0
      stack := restStack
    } finalRet) :
    SafeReaches fnTable layout adtInv {
      curBody := mkStdlibCalleeBody opStmt
      locals := initCalleeLocals v1 v2
      block := 0
      stmtIdx := 0
      stack := frame :: restStack
    } finalRet := by
  let loc0 := initCalleeLocals v1 v2
  let loc1 := updateLocal loc0 3 (some v1)
  let loc2 := updateLocal loc1 4 (some v2)
  let loc3 := updateLocal loc2 5 (some vOut)
  let loc4 := updateLocal loc3 0 (some vOut)
  have s1 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc0, 0, 0, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc1, 0, 1, frame :: restStack⟩ := rfl
  have s2 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc1, 0, 1, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc2, 0, 2, frame :: restStack⟩ := rfl
  have s3 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc2, 0, 2, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc2, 1, 0, frame :: restStack⟩ := rfl
  have s4 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc2, 1, 0, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc3, 1, 1, frame :: restStack⟩ := by
    change (match evalStmt layout adtInv ⟨mkStdlibCalleeBody opStmt, loc2, 1, 0, frame :: restStack⟩ opStmt with
      | some s' => StepOut.step s'
      | none => StepOut.stuck) = _
    rw [hOp]
  have s5 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc3, 1, 1, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc4, 1, 2, frame :: restStack⟩ := rfl
  have s6 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc4, 1, 2, frame :: restStack⟩ =
      .step ⟨mkStdlibCalleeBody opStmt, loc4, 2, 0, frame :: restStack⟩ := rfl
  have s7 : evalMirStep fnTable layout adtInv
      ⟨mkStdlibCalleeBody opStmt, loc4, 2, 0, frame :: restStack⟩ =
      .step ⟨frame.returnBody, updateLocal frame.locals frame.destLocal (some vOut),
             frame.returnBlock, 0, restStack⟩ := rfl
  exact SafeReaches.of_step s1
    (SafeReaches.of_step s2
      (SafeReaches.of_step s3
        (SafeReaches.of_step s4
          (SafeReaches.of_step s5
            (SafeReaches.of_step s6
              (SafeReaches.of_step s7 hAfter))))))

-- Pre-Proved Summary 1: `core::option::Option::<T>::unwrap_or`
theorem summary_unwrapOr (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 101
      (fun _ _ v1 v2 => specUnwrapOr v1 v2) :=
  ⟨bodyUnwrapOr, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 2: `core::option::Option::<T>::is_some`
theorem summary_isSome (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 102
      (fun _ _ v1 _ => specIsSome v1) :=
  ⟨bodyIsSome, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 3: `core::num::NonZeroUsize::new`
theorem summary_nonZeroNew (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 103
      (fun _ inv v1 _ => specNonZeroNew inv v1) :=
  ⟨bodyNonZeroNew, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 4: `core::num::usize::checked_add`
theorem summary_checkedAdd (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 104
      (fun _ _ v1 v2 => specCheckedAdd 65535 v1 v2) :=
  ⟨bodyCheckedAdd, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 5: `core::num::usize::wrapping_add`
theorem summary_wrappingAdd (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 105
      (fun _ _ v1 v2 => specWrappingAdd 65536 v1 v2) :=
  ⟨bodyWrappingAdd, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 6: `core::mem::size_of::<T>`
theorem summary_sizeOf (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 106
      (fun l _ _ _ => specSizeOf l ty) :=
  ⟨bodySizeOf ty, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 7: `core::mem::align_of::<T>`
theorem summary_alignOf (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 107
      (fun l _ _ _ => specAlignOf l ty) :=
  ⟨bodyAlignOf ty, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 8: `core::mem::transmute_copy::<T, T>`
theorem summary_transmuteCopy (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 108
      (fun l inv v1 _ => specTransmuteCopy l inv ty ty v1) :=
  ⟨bodyTransmuteCopy ty ty, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 9: `core::slice::<impl [T]>::len`
theorem summary_sliceLen (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 109
      (fun _ _ v1 _ => specSliceLen v1) :=
  ⟨bodySliceLen, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

-- Pre-Proved Summary 10: `core::slice::<impl [T]>::get`
theorem summary_sliceGet (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) :
    CalleeSummary (stdlibFnTable ty) layout adtInv 110
      (fun _ _ v1 v2 => specSliceGet v1 v2) :=
  ⟨bodySliceGet, rfl, fun _ _ _ _ _ hAfter => mkStdlibCalleeBody_sound rfl hAfter⟩

/-!
## 6. Callers Invoking $K \in \{2, 5, 10\}$ Stdlib Helpers: Inline vs. Summary
-/

/-- Caller invoking 2 stdlib helpers (`size_of::<T>`, `wrapping_add`). -/
def caller2Body : MirBody := {
  blocks := [
    { stmts := [], term := .call1 3 106 1 2 1 },
    { stmts := [], term := .call1 0 105 3 1 2 },
    { stmts := [], term := .return_ }
  ]
}

/-- Caller invoking 5 stdlib helpers (`size_of::<T>`, `align_of::<T>`,
    `wrapping_add`, `checked_add`, `Option::unwrap_or`). -/
def caller5Body : MirBody := {
  blocks := [
    { stmts := [], term := .call1 3 106 1 2 1 },
    { stmts := [], term := .call1 4 107 1 2 2 },
    { stmts := [], term := .call1 5 105 3 4 3 },
    { stmts := [], term := .call1 6 104 5 1 4 },
    { stmts := [], term := .call1 0 101 6 2 5 },
    { stmts := [], term := .return_ }
  ]
}

/-- Caller invoking all 10 stdlib helpers in sequence. -/
def caller10Body : MirBody := {
  blocks := [
    { stmts := [], term := .call1 3 106 1 2 1 },
    { stmts := [], term := .call1 4 107 1 2 2 },
    { stmts := [], term := .call1 5 105 3 4 3 },
    { stmts := [], term := .call1 6 104 5 1 4 },
    { stmts := [], term := .call1 7 101 6 1 5 },
    { stmts := [], term := .call1 8 103 7 1 6 },
    { stmts := [], term := .call1 9 102 8 1 7 },
    { stmts := [], term := .call1 10 109 2 1 8 },
    { stmts := [], term := .call1 11 110 2 1 9 },
    { stmts := [], term := .call1 0 108 11 1 10 },
    { stmts := [], term := .return_ }
  ]
}

def testLayout : LayoutEnv where
  sizeOf _ := 8
  alignOf _ := 8

def initCallerLocals : Nat → Option Val :=
  initCalleeLocals (.usize 2) (.sliceFatPtr 1000 16)

/-- Helper that steps through all 8 concrete transitions of an inlined stdlib
    call (`1 call push` + `7 callee steps/pop`) with explicitly named
    intermediate states (mirroring `MirLemmas.lean:814-1158`). -/
theorem inlineStepCall8
    {fnTable : FnTable} {layout : LayoutEnv} {adtInv : AdtInv}
    {callerBody calleeBody : MirBody} {locals : Nat → Option Val}
    {blk dest target : Nat} {stk : List CallFrame}
    (v1 v2 vOut : Val) {finalRet : Val}
    (hs1 : evalMirStep fnTable layout adtInv ⟨callerBody, locals, blk, 0, stk⟩ =
      .step ⟨calleeBody, initCalleeLocals v1 v2, 0, 0, ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs2 : evalMirStep fnTable layout adtInv
      ⟨calleeBody, initCalleeLocals v1 v2, 0, 0, ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody, updateLocal (initCalleeLocals v1 v2) 3 (some v1), 0, 1,
             ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs3 : evalMirStep fnTable layout adtInv
      ⟨calleeBody, updateLocal (initCalleeLocals v1 v2) 3 (some v1), 0, 1,
       ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody, updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2), 0, 2,
             ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs4 : evalMirStep fnTable layout adtInv
      ⟨calleeBody, updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2), 0, 2,
       ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody, updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2), 1, 0,
             ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs5 : evalMirStep fnTable layout adtInv
      ⟨calleeBody, updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2), 1, 0,
       ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody,
             updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut),
             1, 1, ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs6 : evalMirStep fnTable layout adtInv
      ⟨calleeBody,
       updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut),
       1, 1, ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody,
             updateLocal (updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut)) 0 (some vOut),
             1, 2, ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs7 : evalMirStep fnTable layout adtInv
      ⟨calleeBody,
       updateLocal (updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut)) 0 (some vOut),
       1, 2, ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨calleeBody,
             updateLocal (updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut)) 0 (some vOut),
             2, 0, ⟨callerBody, locals, target, dest⟩ :: stk⟩)
    (hs8 : evalMirStep fnTable layout adtInv
      ⟨calleeBody,
       updateLocal (updateLocal (updateLocal (updateLocal (initCalleeLocals v1 v2) 3 (some v1)) 4 (some v2)) 5 (some vOut)) 0 (some vOut),
       2, 0, ⟨callerBody, locals, target, dest⟩ :: stk⟩ =
      .step ⟨callerBody, updateLocal locals dest (some vOut), target, 0, stk⟩)
    (hAfter : SafeReaches fnTable layout adtInv
      ⟨callerBody, updateLocal locals dest (some vOut), target, 0, stk⟩ finalRet) :
    SafeReaches fnTable layout adtInv ⟨callerBody, locals, blk, 0, stk⟩ finalRet :=
  SafeReaches.of_step hs1
    (SafeReaches.of_step hs2
      (SafeReaches.of_step hs3
        (SafeReaches.of_step hs4
          (SafeReaches.of_step hs5
            (SafeReaches.of_step hs6
              (SafeReaches.of_step hs7
                (SafeReaches.of_step hs8 hAfter)))))))

-- Way A0 (Naive Unnormalized Inlining on K = 2, showing exponential closure duplication)
theorem naive_inline_caller2 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller2Body, initCallerLocals, 0, 0, []⟩ (.usize 10) := by
  refine SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl
    (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl ?_)))))))
  refine SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl
    (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl (SafeReaches.of_step rfl ?_)))))))
  exact SafeReaches.of_ret rfl

-- Way A (Normalized Inline Callee Re-Verification, as in `MirLemmas.lean:814-1158`): K = 2, 5, 10
theorem inline_caller2 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller2Body, initCallerLocals, 0, 0, []⟩ (.usize 10) := by
  refine inlineStepCall8 (.usize 2) (.sliceFatPtr 1000 16) (.usize 8)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 8) (.usize 2) (.usize 10)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  exact SafeReaches.of_ret rfl

theorem inline_caller5 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller5Body, initCallerLocals, 0, 0, []⟩ (.usize 18) := by
  refine inlineStepCall8 (.usize 2) (.sliceFatPtr 1000 16) (.usize 8)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 2) (.sliceFatPtr 1000 16) (.usize 8)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 8) (.usize 8) (.usize 16)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 16) (.usize 2) (.someVal (.usize 18))
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.someVal (.usize 18)) (.sliceFatPtr 1000 16) (.usize 18)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  exact SafeReaches.of_ret rfl

theorem inline_caller10 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller10Body, initCallerLocals, 0, 0, []⟩ (.someVal (.someVal (.usize 1002))) := by
  refine inlineStepCall8 (.usize 2) (.sliceFatPtr 1000 16) (.usize 8)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 2) (.sliceFatPtr 1000 16) (.usize 8)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 8) (.usize 8) (.usize 16)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 16) (.usize 2) (.someVal (.usize 18))
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.someVal (.usize 18)) (.usize 2) (.usize 18)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.usize 18) (.usize 2) (.someVal (.usize 18))
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.someVal (.usize 18)) (.usize 2) (.bool true)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.sliceFatPtr 1000 16) (.usize 2) (.usize 16)
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.sliceFatPtr 1000 16) (.usize 2) (.someVal (.usize 1002))
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  refine inlineStepCall8 (.someVal (.usize 1002)) (.usize 2) (.someVal (.someVal (.usize 1002)))
    rfl rfl rfl rfl rfl rfl rfl rfl ?_
  exact SafeReaches.of_ret rfl

-- Way B (Pre-Proved Summary Instantiation via `call1_summary_sound`): K = 2, 5, 10
theorem summary_caller2 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller2Body, initCallerLocals, 0, 0, []⟩ (.usize 10) := by
  refine call1_summary_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 10) rfl ?_
  exact SafeReaches.of_ret rfl

theorem summary_caller5 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller5Body, initCallerLocals, 0, 0, []⟩ (.usize 18) := by
  refine call1_summary_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_sound (summary_alignOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_sound (summary_checkedAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_sound (summary_unwrapOr .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 18) rfl ?_
  exact SafeReaches.of_ret rfl

theorem summary_caller10 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller10Body, initCallerLocals, 0, 0, []⟩ (.someVal (.someVal (.usize 1002))) := by
  refine call1_summary_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_sound (summary_alignOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_sound (summary_checkedAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_sound (summary_unwrapOr .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 18) rfl ?_
  refine call1_summary_sound (summary_nonZeroNew .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_sound (summary_isSome .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .bool true) rfl ?_
  refine call1_summary_sound (summary_sliceLen .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_sound (summary_sliceGet .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 1002)) rfl ?_
  refine call1_summary_sound (summary_transmuteCopy .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.someVal (.usize 1002))) rfl ?_
  exact SafeReaches.of_ret rfl

-- Way C (Flat-Projection Summary Instantiation via `call1_summary_flat_sound`): K = 2, 5, 10
theorem summary_flat_caller2 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller2Body, initCallerLocals, 0, 0, []⟩ (.usize 10) := by
  refine call1_summary_flat_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_flat_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 10) rfl ?_
  exact SafeReaches.of_ret rfl

theorem summary_flat_caller5 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller5Body, initCallerLocals, 0, 0, []⟩ (.usize 18) := by
  refine call1_summary_flat_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_flat_sound (summary_alignOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_flat_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_flat_sound (summary_checkedAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_flat_sound (summary_unwrapOr .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 18) rfl ?_
  exact SafeReaches.of_ret rfl

theorem summary_flat_caller10 :
    SafeReaches (stdlibFnTable .usize) testLayout defaultAdtInv
      ⟨caller10Body, initCallerLocals, 0, 0, []⟩ (.someVal (.someVal (.usize 1002))) := by
  refine call1_summary_flat_sound (summary_sizeOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_flat_sound (summary_alignOf .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 8) rfl ?_
  refine call1_summary_flat_sound (summary_wrappingAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_flat_sound (summary_checkedAdd .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_flat_sound (summary_unwrapOr .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 18) rfl ?_
  refine call1_summary_flat_sound (summary_nonZeroNew .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 18)) rfl ?_
  refine call1_summary_flat_sound (summary_isSome .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .bool true) rfl ?_
  refine call1_summary_flat_sound (summary_sliceLen .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .usize 16) rfl ?_
  refine call1_summary_flat_sound (summary_sliceGet .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.usize 1002)) rfl ?_
  refine call1_summary_flat_sound (summary_transmuteCopy .usize testLayout defaultAdtInv)
    rfl rfl rfl rfl rfl (vOut := .someVal (.someVal (.usize 1002))) rfl ?_
  exact SafeReaches.of_ret rfl

/-- Polymorphic caller verification over symbolic `ty : Ty`, `layout : LayoutEnv`,
    and `adtInv : AdtInv`, demonstrating that `call1_summary_sound` works even
    when layout and type parameters are universally quantified! -/
theorem summary_caller2_polymorphic (ty : Ty) (layout : LayoutEnv) (adtInv : AdtInv) (x : Nat) :
    SafeReaches (stdlibFnTable ty) layout adtInv
      ⟨caller2Body, initCalleeLocals (.usize x) (.usize 0), 0, 0, []⟩
      (.usize ((layout.sizeOf ty + x) % 65536)) := by
  refine call1_summary_sound (summary_sizeOf ty layout adtInv)
    rfl rfl rfl rfl rfl (vOut := .usize (layout.sizeOf ty)) rfl ?_
  refine call1_summary_sound (summary_wrappingAdd ty layout adtInv)
    rfl rfl rfl rfl rfl (vOut := .usize ((layout.sizeOf ty + x) % 65536)) rfl ?_
  exact SafeReaches.of_ret rfl

/-!
## 7. In-Kernel Replay & Proof-Term Size Measurement Harness
-/

def measureTheorem (env : Environment) (declName : Name) (iters : Nat) : IO String := do
  let some ci := env.find? declName
    | return s!"missing {declName}"
  let some val := ci.value? (allowOpaque := true)
    | return s!"no value for {declName}"
  let objs ← val.numObjs
  let bytes := val.sizeWithoutSharing
  let mut totalNs : Nat := 0
  for i in [0:iters] do
    let aliasName := declName.num i
    let aliasCi := ConstantInfo.thmInfo {
      name := aliasName
      levelParams := ci.levelParams
      type := ci.type
      value := val
      all := [aliasName]
    }
    let mut map : Std.HashMap Name ConstantInfo := {}
    map := map.insert aliasName aliasCi
    let t0 ← IO.monoNanosNow
    let _ ← env.toKernelEnv.replay map
    let t1 ← IO.monoNanosNow
    totalNs := totalNs + (t1 - t0)
  let avgUs := totalNs / (iters * 1000)
  return s!"{declName} | DAG nodes: {objs} | Tree size: {bytes} | Kernel check avg: {avgUs} us ({iters} runs)"

#eval show MetaM Unit from do
  let env ← getEnv
  IO.println "=== Pre-Proved Stdlib Summaries vs. Inline Callee Re-Verification ==="
  let names := [
    ``naive_inline_caller2,
    ``inline_caller2,
    ``summary_caller2,
    ``summary_flat_caller2,
    ``inline_caller5,
    ``summary_caller5,
    ``summary_flat_caller5,
    ``inline_caller10,
    ``summary_caller10,
    ``summary_flat_caller10,
    ``summary_caller2_polymorphic
  ]
  for n in names do
    let line ← measureTheorem env n 10
    IO.println line

end ProbePreprovedSummaries
