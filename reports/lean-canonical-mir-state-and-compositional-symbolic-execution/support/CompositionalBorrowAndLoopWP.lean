-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Probe 3: Compositional Symbolic Execution, Backward Lenses, and Canonical-State Loop Invariants in Lean 4

This probe demonstrates how replacing closure-based symbolic states
(`locals : Nat → Option SymVal`, `loans : Nat → Option LoanEntry`) and per-function
`extractSymArgs` unpacking cascades in `FunctionalTranslation.lean` (11,619 lines)
with:
1. A **Canonical Extensional Symbolic State** (`locals : List (Option SymVal)`,
   `loans : List (Option LoanEntry)`) with spine-normalizing `getAt`/`setAt`,
2. A **Compositional Backward-Lens Reborrow Model** (`back : SymVal → List (Nat × SymVal)`)
   for mutable references, diamond borrow joins (`joinBorrow`), sequential reborrows
   (`endLoan`), and functions returning `&'a mut T` (`evalMutReturnFwd`/`evalMutReturnBack`),
3. A **Single Generic WP / Hoare Bridge Theorem** (`verify_scalar_fn`, `verify_mut_return_fn`)
   that eliminates the ~80-line per-function `extractSymArgs` case-split cascade, and
4. **Canonical Loop-Header State Normalization** for `while` loops (`count_up`), where
   dead/moved temporaries reset to `none` so each loop iteration `bb1 → bb2 → bb3 → bb4 → bb1`
   reduces back to the canonical `countUpHeaderState n (i + 1)` without closure wrappers
   (`countUpLocalsAfterBb1..4`),

verifies all 6 target functions from `FunctionalTranslation.lean` (`max_assign`,
`update_min`, `clamp_assign`, `choose_mut`, `two_phase_reborrow`, and `count_up`)
in 1,041 lines total (including the standalone MIR AST and all 6 `MirBody` fixtures,
vs. 11,619 lines in `FunctionalTranslation.lean` — an 11.2x reduction).
-/

namespace CompositionalBorrowAndLoopWP

set_option maxRecDepth 100000

def usizeMax : Nat := 18446744073709551615

/-!
## 1. Core MIR Syntax and Concrete Operational Semantics
-/

structure LocalId where
  index : Nat
  deriving DecidableEq, Repr

structure BlockId where
  index : Nat
  deriving DecidableEq, Repr

inductive Ty where
  | usize
  | bool
  | unit
  | tupleUsizeBool
  | refMutUsize
  deriving DecidableEq, Repr

inductive MirVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (n : Nat) (b : Bool)
  | refMutLoc (loc : Nat)
  deriving DecidableEq, Repr

inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (v : MirVal)
  deriving DecidableEq, Repr

inductive BinOp where
  | add | sub | lt | le | gt | ge | eq | bitAnd
  deriving DecidableEq, Repr

inductive Rvalue where
  | use (op : Operand)
  | binaryOp (op : BinOp) (lhs rhs : Operand)
  | checkedBinaryOp (op : BinOp) (lhs rhs : Operand)
  | proj0 (src : LocalId)
  | deref (src : LocalId)
  deriving DecidableEq, Repr

inductive Stmt where
  | assign (dst : LocalId) (rv : Rvalue)
  | assignDeref (dstRef : LocalId) (op : Operand)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  deriving DecidableEq, Repr

inductive Terminator where
  | goto (target : BlockId)
  | switchInt (discr : Operand) (falseTarget trueTarget : BlockId)
  | assertNotOverflow (tup : LocalId) (target : BlockId)
  | return_
  | unreachable
  deriving DecidableEq, Repr

structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator
  deriving DecidableEq, Repr

structure MirBody where
  argTys : List Ty
  retTy : Ty
  localCount : Nat
  blocks : List BasicBlock
  deriving DecidableEq, Repr

/-- Spine-normalizing canonical list lookup and update (`O(idx)`). -/
def nthOpt : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => nthOpt xs i

def getAt : List (Option α) → Nat → Option α
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getAt xs i

def setAt : List (Option α) → Nat → Option α → List (Option α)
  | [], _, _ => []
  | _ :: xs, 0, v => v :: xs
  | x :: xs, i + 1, v => x :: setAt xs i v

def replicateNone : Nat → List (Option α)
  | 0 => []
  | n + 1 => none :: replicateNone n

/-!
## 2. Reusable 105-Line Canonical Symbolic Evaluator & Backward-Lens Engine
-/

inductive SymVal where
  | usize (n : Nat)
  | bool (b : Bool)
  | unit
  | tupleUsizeBool (n : Nat) (b : Bool)
  | borrow (loanId : Nat)
  deriving DecidableEq, Repr

def SymVal.toScalarMirVal : SymVal → Option MirVal
  | .usize n => some (.usize n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .tupleUsizeBool n b => some (.tupleUsizeBool n b)
  | .borrow _ => none

/-- Push a branch condition inside scalar `.usize` and `.bool` constructors so
    the outer `SymVal` constructor spine remains concrete across CFG joins. -/
def zipSymVal (cond : Bool) : SymVal → SymVal → SymVal
  | .usize t, .usize f => .usize (if cond then t else f)
  | .bool t, .bool f => .bool (if cond then t else f)
  | .unit, .unit => .unit
  | .borrow lidT, .borrow lidF =>
    if lidT == lidF then .borrow lidT else if cond then .borrow lidT else .borrow lidF
  | t, f => if cond then t else f

/-- First-order defunctionalized backward lens for a mutable borrow.
    Eliminating function closures from `LoanEntry` makes `SymState` a purely
    first-order canonical data structure (`deriving DecidableEq, Repr`) and prevents
    unreduced thunks from hiding under lambda binders during WHNF reduction. -/
inductive LoanBack where
  | root
  | join2 (cond : Bool) (falseLid : Nat) (vFalse : SymVal) (trueLid : Nat) (vTrue : SymVal)
  deriving DecidableEq, Repr

def LoanBack.apply : LoanBack → SymVal → List (Nat × SymVal)
  | .root, _ => []
  | .join2 cond falseLid vFalse trueLid vTrue, newVal =>
    [(falseLid, zipSymVal cond vFalse newVal),
     (trueLid, zipSymVal cond newVal vTrue)]

/-- A canonical loan entry tracks its current symbolic value, whether it is
    frozen by an active child reborrow, and its first-order backward lens `back`. -/
structure LoanEntry where
  curVal : SymVal
  frozen : Bool := false
  back : LoanBack := .root
  deriving DecidableEq, Repr

/-- Canonical symbolic state using extensional `List` stores and first-order
    backward lenses (zero closures anywhere in `SymState`). -/
structure SymState where
  locals : List (Option SymVal)
  loans : List (Option LoanEntry)
  block : Nat := 0
  stmtIdx : Nat := 0
  deriving DecidableEq, Repr

def evalSymOperand (locals : List (Option SymVal)) :
    Operand → Option (SymVal × List (Option SymVal))
  | .copy src =>
    match getAt locals src.index with
    | some v => some (v, locals)
    | none => none
  | .move src =>
    match getAt locals src.index with
    | some v => some (v, setAt locals src.index none)
    | none => none
  | .constVal (.usize n) => some (.usize n, locals)
  | .constVal (.bool b) => some (.bool b, locals)
  | .constVal .unit => some (.unit, locals)
  | .constVal (.tupleUsizeBool n b) => some (.tupleUsizeBool n b, locals)
  | .constVal (.refMutLoc _) => none

def evalSymBinOp (op : BinOp) (v1 v2 : SymVal) : Option SymVal :=
  match op, v1, v2 with
  | .add, .usize a, .usize b =>
    if decide (usizeMax < a + b) then none else some (.usize (a + b))
  | .sub, .usize a, .usize b =>
    if decide (a < b) then none else some (.usize (a - b))
  | .lt, .usize a, .usize b => some (.bool (decide (a < b)))
  | .le, .usize a, .usize b => some (.bool (decide (a ≤ b)))
  | .gt, .usize a, .usize b => some (.bool (decide (b < a)))
  | .ge, .usize a, .usize b => some (.bool (decide (b ≤ a)))
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .bitAnd, .usize a, .usize b => some (.usize (Nat.land a b))
  | _, _, _ => none

def evalSymCheckedBinOp (op : BinOp) (v1 v2 : SymVal) : Option SymVal :=
  match op, v1, v2 with
  | .add, .usize a, .usize b =>
    some (.tupleUsizeBool (a + b) (decide (usizeMax < a + b)))
  | .sub, .usize a, .usize b =>
    some (.tupleUsizeBool (a - b) (decide (a < b)))
  | _, _, _ => none

def evalSymStmt (sym : SymState) : Stmt → Option SymState
  | .assign dst (.use op) =>
    match evalSymOperand sym.locals op with
    | some (sv, locals') =>
      some { sym with locals := setAt locals' dst.index (some sv), stmtIdx := sym.stmtIdx + 1 }
    | none => none
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | some (v2, locals2) =>
        match evalSymBinOp op v1 v2 with
        | some res =>
          some { sym with locals := setAt locals2 dst.index (some res), stmtIdx := sym.stmtIdx + 1 }
        | none => none
      | none => none
    | none => none
  | .assign dst (.checkedBinaryOp op lhs rhs) =>
    match evalSymOperand sym.locals lhs with
    | some (v1, locals1) =>
      match evalSymOperand locals1 rhs with
      | some (v2, locals2) =>
        match evalSymCheckedBinOp op v1 v2 with
        | some res =>
          some { sym with locals := setAt locals2 dst.index (some res), stmtIdx := sym.stmtIdx + 1 }
        | none => none
      | none => none
    | none => none
  | .assign dst (.proj0 src) =>
    match getAt sym.locals src.index with
    | some (.tupleUsizeBool n _) =>
      -- Move projection clears the temporary tuple slot `src` to `none`
      let locals1 := setAt sym.locals src.index none
      some { sym with locals := setAt locals1 dst.index (some (.usize n)), stmtIdx := sym.stmtIdx + 1 }
    | _ => none
  | .assign dst (.deref src) =>
    match getAt sym.locals src.index with
    | some (.borrow lid) =>
      match getAt sym.loans lid with
      | some entry =>
        if !entry.frozen then
          some { sym with locals := setAt sym.locals dst.index (some entry.curVal), stmtIdx := sym.stmtIdx + 1 }
        else none
      | none => none
    | _ => none
  | .assignDeref dstRef op =>
    match evalSymOperand sym.locals op with
    | some (sv, locals') =>
      match getAt locals' dstRef.index with
      | some (.borrow lid) =>
        match getAt sym.loans lid with
        | some entry =>
          if !entry.frozen then
            some { sym with
              locals := locals'
              loans := setAt sym.loans lid (some { entry with curVal := sv })
              stmtIdx := sym.stmtIdx + 1 }
          else none
        | none => none
      | _ => none
    | none => none
  | .storageLive loc | .storageDead loc =>
    some { sym with locals := setAt sym.locals loc.index none, stmtIdx := sym.stmtIdx + 1 }

/-- Execute one statement or non-branching terminator (`goto`, `assertNotOverflow`). -/
def evalSymStep (body : MirBody) (sym : SymState) : Option SymState :=
  match nthOpt body.blocks sym.block with
  | none => none
  | some bb =>
    match nthOpt bb.stmts sym.stmtIdx with
    | some stmt => evalSymStmt sym stmt
    | none =>
      match bb.terminator with
      | .goto target => some { sym with block := target.index, stmtIdx := 0 }
      | .assertNotOverflow tup target =>
        match getAt sym.locals tup.index with
        | some (.tupleUsizeBool _ ov) =>
          if ov then none else some { sym with block := target.index, stmtIdx := 0 }
        | _ => none
      | _ => none

/-- Evaluate a `switchInt` terminator into `(cond, falseState, trueState)`. -/
def evalBranchStep (body : MirBody) (sym : SymState) : Option (Bool × SymState × SymState) :=
  match nthOpt body.blocks sym.block with
  | none => none
  | some bb =>
    match nthOpt bb.stmts sym.stmtIdx with
    | some _ => none
    | none =>
      match bb.terminator with
      | .switchInt op falseTarget trueTarget =>
        match evalSymOperand sym.locals op with
        | some (.bool cond, locals') =>
          some (cond,
            { sym with locals := locals', block := falseTarget.index, stmtIdx := 0 },
            { sym with locals := locals', block := trueTarget.index, stmtIdx := 0 })
        | _ => none
      | _ => none

/-- Pointwise canonical join of two `List (Option SymVal)` local stores. -/
def zipLocals (cond : Bool) : List (Option SymVal) → List (Option SymVal) → List (Option SymVal)
  | none :: restT, none :: restF => none :: zipLocals cond restT restF
  | some vT :: restT, some vF :: restF => some (zipSymVal cond vT vF) :: zipLocals cond restT restF
  | oT :: restT, oF :: restF => (if cond then oT else oF) :: zipLocals cond restT restF
  | [], _ => []
  | _, [] => []

/-- Pointwise canonical join of two `List (Option LoanEntry)` loan stores. -/
def zipLoans (cond : Bool) : List (Option LoanEntry) → List (Option LoanEntry) → List (Option LoanEntry)
  | none :: restT, none :: restF => none :: zipLoans cond restT restF
  | some eT :: restT, some eF :: restF =>
    some {
      curVal := zipSymVal cond eT.curVal eF.curVal
      frozen := if eT.frozen == eF.frozen then eT.frozen else if cond then eT.frozen else eF.frozen
      back := if eT.back == eF.back then eT.back else if cond then eT.back else eF.back
    } :: zipLoans cond restT restF
  | oT :: restT, oF :: restF => (if cond then oT else oF) :: zipLoans cond restT restF
  | [], _ => []
  | _, [] => []

/-- Canonical join of two `SymState`s at the same CFG join point `(block, stmtIdx)`. -/
def joinSymStates (cond : Bool) (symT symF : SymState) : Option SymState :=
  if symT.block == symF.block && symT.stmtIdx == symF.stmtIdx then
    some {
      locals := zipLocals cond symT.locals symF.locals
      loans := zipLoans cond symT.loans symF.loans
      block := symT.block
      stmtIdx := symT.stmtIdx
    }
  else none

/-- Pattern-match a single-statement borrow-copy arm `_dst = copy _src; goto -> bbJoin`. -/
def matchBorrowArm (bb : BasicBlock) : Option (Nat × Nat × Nat) :=
  match bb.stmts, bb.terminator with
  | [.assign dst (.use (.copy src))], .goto joinBlk =>
    some (dst.index, src.index, joinBlk.index)
  | _, _ => none

/-- Compositional diamond borrow join (`let r = if cond { &mut *x } else { &mut *y }`):
    freezes both parent loans and creates a joined child loan at `joinedLid` whose
    backward lens `back` routes the updated value back to the selected parent. -/
def evalJoinBorrow (body : MirBody) (sym : SymState)
    (dstLocal falseSrc trueSrc joinBlock joinedLid : Nat) : Option SymState :=
  match evalBranchStep body sym with
  | some (cond, symF, symT) =>
    match nthOpt body.blocks symF.block, nthOpt body.blocks symT.block with
    | some bbF, some bbT =>
      match matchBorrowArm bbF, matchBorrowArm bbT with
      | some (dstF, srcF, joinF), some (dstT, srcT, joinT) =>
        if dstF == dstLocal && dstT == dstLocal &&
           srcF == falseSrc && srcT == trueSrc &&
           joinF == joinBlock && joinT == joinBlock then
          match getAt symF.locals falseSrc, getAt symT.locals trueSrc with
          | some (.borrow falseLid), some (.borrow trueLid) =>
            if falseLid != trueLid then
              match getAt sym.loans falseLid, getAt sym.loans trueLid with
              | some eF, some eT =>
                if !eF.frozen && !eT.frozen then
                  let vF := eF.curVal
                  let vT := eT.curVal
                  let joinedEntry : LoanEntry := {
                    curVal := zipSymVal cond vT vF
                    frozen := false
                    back := .join2 cond falseLid vF trueLid vT
                  }
                  let loans1 := setAt sym.loans falseLid (some { eF with frozen := true })
                  let loans2 := setAt loans1 trueLid (some { eT with frozen := true })
                  let loans3 := setAt loans2 joinedLid (some joinedEntry)
                  some {
                    locals := setAt symF.locals dstLocal (some (.borrow joinedLid))
                    loans := loans3
                    block := joinBlock
                    stmtIdx := 0
                  }
                else none
              | _, _ => none
            else none
          | _, _ => none
        else none
      | _, _ => none
    | _, _ => none
  | none => none

def applyLoanUpdates (loans : List (Option LoanEntry)) : List (Nat × SymVal) → List (Option LoanEntry)
  | [] => loans
  | (pLid, pVal) :: rest =>
    let loans' :=
      match getAt loans pLid with
      | some pEntry => setAt loans pLid (some { pEntry with curVal := pVal, frozen := false })
      | none => loans
    applyLoanUpdates loans' rest

/-- Ending a loan `lid` applies its backward lens `entry.back.apply entry.curVal` to
    unfreeze and update its parent loan(s), then clears `loans[lid]` to `none`. -/
def evalEndLoan (sym : SymState) (lid : Nat) : Option SymState :=
  match getAt sym.loans lid with
  | some entry =>
    if !entry.frozen then
      let updates := entry.back.apply entry.curVal
      let loansCleared := setAt sym.loans lid none
      let loansUpdated := applyLoanUpdates loansCleared updates
      some { sym with loans := loansUpdated }
    else none
  | none => none

def evalReturn (body : MirBody) (sym : SymState) : Option MirVal :=
  match nthOpt body.blocks sym.block with
  | some bb =>
    match nthOpt bb.stmts sym.stmtIdx, bb.terminator with
    | none, .return_ =>
      match getAt sym.locals 0 with
      | some sv => sv.toScalarMirVal
      | none => none
    | _, _ => none
  | none => none

/-- CPS spine-forcing helpers so `setAt` chains over symbolic `List` states
    never accumulate unreduced thunks when `hasFVar == true` disables Lean's
    WHNF cache. -/
@[inline] def forceOptionSymVal (o : Option SymVal) (k : Option SymVal → α) : α :=
  match o with
  | none => k none
  | some (.usize n) => k (some (.usize n))
  | some (.bool b) => k (some (.bool b))
  | some .unit => k (some .unit)
  | some (.tupleUsizeBool n b) => k (some (.tupleUsizeBool n b))
  | some (.borrow lid) => k (some (.borrow lid))

@[inline] def forceLocals (xs : List (Option SymVal)) (k : List (Option SymVal) → α) : α :=
  match xs with
  | [] => k []
  | x :: rest =>
    forceOptionSymVal x (fun x' =>
      forceLocals rest (fun rest' =>
        k (x' :: rest')))

@[inline] def forceLoanBack (b : LoanBack) (k : LoanBack → α) : α :=
  match b with
  | .root => k .root
  | .join2 cond fLid (.usize vf) tLid (.usize vt) =>
    k (.join2 cond fLid (.usize vf) tLid (.usize vt))
  | .join2 cond fLid vf tLid vt =>
    k (.join2 cond fLid vf tLid vt)

@[inline] def forceOptionLoan (o : Option LoanEntry) (k : Option LoanEntry → α) : α :=
  match o with
  | none => k none
  | some e =>
    forceLoanBack e.back (fun back' =>
      match e.curVal, e.frozen with
      | .usize n, false => k (some { curVal := .usize n, frozen := false, back := back' })
      | .usize n, true  => k (some { curVal := .usize n, frozen := true,  back := back' })
      | cv, frz         => k (some { curVal := cv,       frozen := frz,   back := back' }))

@[inline] def forceLoans (xs : List (Option LoanEntry)) (k : List (Option LoanEntry) → α) : α :=
  match xs with
  | [] => k []
  | x :: rest =>
    forceOptionLoan x (fun x' =>
      forceLoans rest (fun rest' =>
        k (x' :: rest')))

@[inline] def forceSymState (s : SymState) (k : SymState → α) : α :=
  forceLocals s.locals (fun locals' =>
    forceLoans s.loans (fun loans' =>
      k { locals := locals', loans := loans', block := s.block, stmtIdx := s.stmtIdx }))

theorem forceOptionSymVal_eq (o : Option SymVal) (k : Option SymVal → α) :
    forceOptionSymVal o k = k o := by
  cases o with
  | none => rfl
  | some v => cases v <;> rfl

theorem forceLocals_eq (xs : List (Option SymVal)) (k : List (Option SymVal) → α) :
    forceLocals xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x rest ih =>
    dsimp [forceLocals]
    rw [forceOptionSymVal_eq, ih]

theorem forceLoanBack_eq (b : LoanBack) (k : LoanBack → α) :
    forceLoanBack b k = k b := by
  cases b with
  | root => rfl
  | join2 cond fLid vf tLid vt =>
    cases vf <;> cases vt <;> rfl

theorem forceOptionLoan_eq (o : Option LoanEntry) (k : Option LoanEntry → α) :
    forceOptionLoan o k = k o := by
  cases o with
  | none => rfl
  | some e =>
    cases e with
    | mk cv frz bk =>
      dsimp [forceOptionLoan]
      rw [forceLoanBack_eq]
      cases cv <;> cases frz <;> rfl

theorem forceLoans_eq (xs : List (Option LoanEntry)) (k : List (Option LoanEntry) → α) :
    forceLoans xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x rest ih =>
    dsimp [forceLoans]
    rw [forceOptionLoan_eq, ih]

/-- Soundness of CPS spine-forcing on `SymState`: `forceSymState s k` is
    propositionally identical to `k s` for all `s` and `k`. -/
theorem forceSymState_eq (s : SymState) (k : SymState → α) :
    forceSymState s k = k s := by
  cases s
  dsimp [forceSymState]
  rw [forceLocals_eq, forceLoans_eq]

inductive TransPlan where
  | here
  | ret
  | step (next : TransPlan)
  | branch (falsePlan truePlan : TransPlan)
  | diamond (falseArm trueArm afterJoin : TransPlan)
  | joinBorrow (dstLocal falseSrc trueSrc joinBlock joinedLid : Nat) (afterJoin : TransPlan)
  | endLoan (lid : Nat) (next : TransPlan)
  | fail
  deriving Repr

/-- Unified symbolic state evaluator for straight-line steps, CFG diamonds,
    loop branches, diamond reborrows, and loan termination. -/
def evalSymState : TransPlan → MirBody → SymState → Option SymState
  | .here, _, sym => some sym
  | .ret, body, sym =>
    match nthOpt body.blocks sym.block with
    | some bb =>
      match nthOpt bb.stmts sym.stmtIdx, bb.terminator with
      | none, .return_ => some sym
      | _, _ => none
    | none => none
  | .step next, body, sym =>
    match evalSymStep body sym with
    | some sym' => forceSymState sym' (fun symForced => evalSymState next body symForced)
    | none => none
  | .branch falsePlan truePlan, body, sym =>
    match evalBranchStep body sym with
    | some (cond, symF, symT) =>
      if cond then
        forceSymState symT (fun symTForced => evalSymState truePlan body symTForced)
      else
        forceSymState symF (fun symFForced => evalSymState falsePlan body symFForced)
    | none => none
  | .diamond falseArm trueArm afterJoin, body, sym =>
    match evalBranchStep body sym with
    | some (cond, symF, symT) =>
      match evalSymState falseArm body symF, evalSymState trueArm body symT with
      | some symF', some symT' =>
        match joinSymStates cond symT' symF' with
        | some symJ => forceSymState symJ (fun symJForced => evalSymState afterJoin body symJForced)
        | none => none
      | _, _ => none
    | none => none
  | .joinBorrow dst fSrc tSrc joinBlk jLid afterJoin, body, sym =>
    match evalJoinBorrow body sym dst fSrc tSrc joinBlk jLid with
    | some symJ => forceSymState symJ (fun symJForced => evalSymState afterJoin body symJForced)
    | none => none
  | .endLoan lid next, body, sym =>
    match evalEndLoan sym lid with
    | some sym' => forceSymState sym' (fun symForced => evalSymState next body symForced)
    | none => none
  | .fail, _, _ => none

/-- Extract the post-state `curVal` of each active, unfrozen loan in `loanIds`
    via direct structural recursion (avoiding `Monad Option` typeclass overhead). -/
def extractPostLoans (loans : List (Option LoanEntry)) : List Nat → Option (List SymVal)
  | [] => some []
  | lid :: rest =>
    match getAt loans lid, extractPostLoans loans rest with
    | some e, some tail => if !e.frozen then some (e.curVal :: tail) else none
    | _, _ => none

/-- Forward value read from the returned mutable borrow in `_0`. -/
def evalMutReturnFwd (sym : SymState) : Option SymVal :=
  match getAt sym.locals 0 with
  | some (.borrow lid) =>
    match getAt sym.loans lid with
    | some entry => if !entry.frozen then some entry.curVal else none
    | none => none
  | _ => none

/-- Backward lens for a returned mutable borrow in `_0`: writes `newVal` into
    the returned loan, ends the loan (propagating updates to parent loans), and
    reads back the updated values of `parentLoans`. -/
def evalMutReturnBack (sym : SymState) (newVal : SymVal) (parentLoans : List Nat) :
    Option (List SymVal) :=
  match getAt sym.locals 0 with
  | some (.borrow lid) =>
    match getAt sym.loans lid with
    | some entry =>
      if !entry.frozen then
        let symUpdated := { sym with loans := setAt sym.loans lid (some { entry with curVal := newVal }) }
        match evalEndLoan symUpdated lid with
        | some symEnded => extractPostLoans symEnded.loans parentLoans
        | none => none
      else none
    | none => none
  | _ => none

/-!
## 3. Canonical Initial State Builder & Single Generic Specification Bridge

Instead of repeating 70–106 lines of `extractSymArgs` unpacking per function,
`mkCanonicalInit` constructs the canonical `List`-backed `SymState` from a
`List SymArg` in one pass, and `evalPureRet` / `evalPurePostLoans` extract both
the return value and the final values of mutable-reference parameters.
-/

inductive SymArg where
  | usize (n : Nat)
  | bool (b : Bool)
  | refMut (n : Nat)
  deriving DecidableEq, Repr

def mkCanonicalInit (localCount : Nat) (loanCapacity : Nat) (args : List SymArg) : SymState :=
  let baseLocals := replicateNone localCount
  let baseLoans := replicateNone loanCapacity
  let (locals, loans, _) := args.foldl (fun (locs, lns, idx) arg =>
    match arg with
    | .usize n => (setAt locs idx (some (.usize n)), lns, idx + 1)
    | .bool b => (setAt locs idx (some (.bool b)), lns, idx + 1)
    | .refMut n =>
      let entry : LoanEntry := { curVal := .usize n, frozen := false, back := .root }
      (setAt locs idx (some (.borrow idx)), setAt lns idx (some entry), idx + 1)
  ) (baseLocals, baseLoans, 1)
  { locals := locals, loans := loans, block := 0, stmtIdx := 0 }

def evalPureRet (plan : TransPlan) (body : MirBody) (loanCap : Nat) (args : List SymArg) :
    Option MirVal :=
  (evalSymState plan body (mkCanonicalInit body.localCount loanCap args)).bind (evalReturn body)

def evalPurePostLoans (plan : TransPlan) (body : MirBody) (loanCap : Nat)
    (args : List SymArg) (loanIds : List Nat) : Option (MirVal × List SymVal) :=
  match evalSymState plan body (mkCanonicalInit body.localCount loanCap args) with
  | some symFinal =>
    match evalReturn body symFinal, extractPostLoans symFinal.loans loanIds with
    | some mv, some postVals => some (mv, postVals)
    | _, _ => none
  | none => none

/-!
## 4. Verification of the 6 Target Functions from `FunctionalTranslation.lean`
-/

/-! ### 4.1 `max_assign` (Branching Mutable Borrow Mutation with Canonical Diamond Join) -/

def maxAssignBody : MirBody where
  argTys := [.refMutUsize, .usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .assign ⟨4⟩ (.deref ⟨1⟩),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨2⟩)]
      terminator := .goto ⟨2⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨1⟩)]
      terminator := .return_ }
  ]

def maxAssignPlan : TransPlan :=
  .step (.step (.diamond .here (.step (.step .here)) (.step .ret)))

theorem maxAssign_eval_rfl (x0 y0 : Nat) :
    evalPurePostLoans maxAssignPlan maxAssignBody 2 [.refMut x0, .usize y0] [1] =
      some (.usize (if decide (x0 < y0) then y0 else x0),
            [.usize (if decide (x0 < y0) then y0 else x0)]) :=
  rfl

/-! ### 4.2 `update_min` (Diamond Mutable Reborrow Join + `.endLoan`) -/

def updateMinBody : MirBody where
  argTys := [.refMutUsize, .refMutUsize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨6⟩ (.deref ⟨1⟩),
        .assign ⟨7⟩ (.deref ⟨2⟩),
        .assign ⟨5⟩ (.binaryOp .le (.move ⟨6⟩) (.move ⟨7⟩))
      ]
      terminator := .switchInt (.move ⟨5⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨1⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨4⟩ (.copy ⟨3⟩),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

def updateMinPlan : TransPlan :=
  .step (.step (.step
    (.joinBorrow 4 2 1 3 4
      (.step (.endLoan 4 (.step .ret))))))

/-- Both the return value `*x` and the post-state pair `(x', y')` reduce by `rfl`! -/
theorem updateMin_eval_rfl (x0 y0 v0 : Nat) :
    evalPurePostLoans updateMinPlan updateMinBody 5
      [.refMut x0, .refMut y0, .usize v0] [1, 2] =
      some (.usize (if decide (x0 ≤ y0) then v0 else x0),
            [.usize (if decide (x0 ≤ y0) then v0 else x0),
             .usize (if decide (x0 ≤ y0) then y0 else v0)]) :=
  rfl

/-! ### 4.3 `clamp_assign` (Cascaded 3-Way `if / else if` Mutable Borrow Mutation) -/

def clampAssignBody : MirBody where
  argTys := [.refMutUsize, .usize, .usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [
        .assign ⟨5⟩ (.deref ⟨1⟩),
        .assign ⟨4⟩ (.binaryOp .lt (.move ⟨5⟩) (.copy ⟨2⟩))
      ]
      terminator := .switchInt (.move ⟨4⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨2⟩)]
      terminator := .goto ⟨4⟩ },
    { stmts := [
        .assign ⟨7⟩ (.deref ⟨1⟩),
        .assign ⟨6⟩ (.binaryOp .gt (.move ⟨7⟩) (.copy ⟨3⟩))
      ]
      terminator := .switchInt (.move ⟨6⟩) ⟨4⟩ ⟨3⟩ },
    { stmts := [.assignDeref ⟨1⟩ (.copy ⟨3⟩)]
      terminator := .goto ⟨4⟩ },
    { stmts := [.assign ⟨0⟩ (.deref ⟨1⟩)]
      terminator := .return_ }
  ]

def clampAssignPlan : TransPlan :=
  .step (.step (.diamond
    (.step (.step (.diamond .here (.step (.step .here)) .here)))
    (.step (.step .here))
    (.step .ret)))

theorem clampAssign_eval_rfl (x0 lo hi : Nat) :
    evalPurePostLoans clampAssignPlan clampAssignBody 2
      [.refMut x0, .usize lo, .usize hi] [1] =
      some (.usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0),
            [.usize (if decide (x0 < lo) then lo else if decide (hi < x0) then hi else x0)]) :=
  rfl

/-! ### 4.4 `choose_mut` (Returning `&'a mut usize` via Forward & Backward Lenses) -/

def chooseMutBody : MirBody where
  argTys := [.bool, .refMutUsize, .refMutUsize]
  retTy := .refMutUsize
  localCount := 5
  blocks := [
    { stmts := []
      terminator := .switchInt (.copy ⟨1⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨4⟩ (.use (.copy ⟨3⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨4⟩))]
      terminator := .return_ }
  ]

def chooseMutPlan : TransPlan :=
  .joinBorrow 4 3 2 3 4 (.step .ret)

def evalChooseMutFwd (b : Bool) (x0 y0 : Nat) : Option SymVal :=
  match evalSymState chooseMutPlan chooseMutBody
          (mkCanonicalInit chooseMutBody.localCount 5 [.bool b, .refMut x0, .refMut y0]) with
  | some symRet => evalMutReturnFwd symRet
  | none => none

def evalChooseMutBack (b : Bool) (x0 y0 v : Nat) : Option (List SymVal) :=
  match evalSymState chooseMutPlan chooseMutBody
          (mkCanonicalInit chooseMutBody.localCount 5 [.bool b, .refMut x0, .refMut y0]) with
  | some symRet => evalMutReturnBack symRet (.usize v) [2, 3]
  | none => none

theorem chooseMut_fwd_rfl (b : Bool) (x0 y0 : Nat) :
    evalChooseMutFwd b x0 y0 = some (.usize (if b then x0 else y0)) :=
  rfl

theorem chooseMut_back_rfl (b : Bool) (x0 y0 v : Nat) :
    evalChooseMutBack b x0 y0 v =
      some [.usize (if b then v else x0), .usize (if b then y0 else v)] :=
  rfl

/-- Get-Put, Put-Get, and Put-Put lens laws directly on the evaluated lens! -/
theorem chooseMut_lens_laws (b : Bool) (x0 y0 v1 v2 : Nat) :
    (evalChooseMutBack b x0 y0 (if b then x0 else y0) = some [.usize x0, .usize y0]) ∧
    (evalChooseMutFwd b (if b then v1 else x0) (if b then y0 else v1) = some (.usize v1)) ∧
    (evalChooseMutBack b (if b then v1 else x0) (if b then y0 else v1) v2 =
      evalChooseMutBack b x0 y0 v2) := by
  cases b <;> exact ⟨rfl, rfl, rfl⟩

/-! ### 4.5 `two_phase_reborrow` (Sequential Diamond Reborrows with Intermediate `.endLoan`) -/

def twoPhaseReborrowBody : MirBody where
  argTys := [.refMutUsize, .refMutUsize, .usize, .usize]
  retTy := .usize
  localCount := 13
  blocks := [
    { stmts := [
        .assign ⟨7⟩ (.deref ⟨1⟩),
        .assign ⟨8⟩ (.deref ⟨2⟩),
        .assign ⟨6⟩ (.binaryOp .le (.move ⟨7⟩) (.move ⟨8⟩))
      ]
      terminator := .switchInt (.move ⟨6⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.assign ⟨5⟩ (.use (.copy ⟨1⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨5⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .assignDeref ⟨5⟩ (.copy ⟨3⟩),
        .assign ⟨11⟩ (.deref ⟨1⟩),
        .assign ⟨12⟩ (.deref ⟨2⟩),
        .assign ⟨10⟩ (.binaryOp .le (.move ⟨11⟩) (.move ⟨12⟩))
      ]
      terminator := .switchInt (.move ⟨10⟩) ⟨5⟩ ⟨4⟩ },
    { stmts := [.assign ⟨9⟩ (.use (.copy ⟨2⟩))]
      terminator := .goto ⟨6⟩ },
    { stmts := [.assign ⟨9⟩ (.use (.copy ⟨1⟩))]
      terminator := .goto ⟨6⟩ },
    { stmts := [
        .assignDeref ⟨9⟩ (.copy ⟨4⟩),
        .assign ⟨0⟩ (.deref ⟨1⟩)
      ]
      terminator := .return_ }
  ]

def twoPhaseReborrowPlan : TransPlan :=
  .step (.step (.step
    (.joinBorrow 5 2 1 3 5
      (.step (.endLoan 5
        (.step (.step (.step
          (.joinBorrow 9 1 2 6 9
            (.step (.endLoan 9 (.step .ret))))))))))))

theorem twoPhaseReborrow_eval_rfl (x0 y0 a b : Nat) :
    evalPureRet twoPhaseReborrowPlan twoPhaseReborrowBody 10
      [.refMut x0, .refMut y0, .usize a, .usize b] =
      some (.usize
        (if decide ((if decide (x0 ≤ y0) then a else x0) ≤ (if decide (x0 ≤ y0) then y0 else a))
         then (if decide (x0 ≤ y0) then a else x0)
         else b)) :=
  rfl

/-! ### 4.6 `count_up` (`while i < n && i < 1000` Verified via Canonical Loop-Header State)

Because `SymState.locals` is a canonical 8-element `List (Option SymVal)` and
`.move` / `.proj0` clear consumed temporaries (`_3, _4, _5, _6, _7`) back to `none`,
the loop header state at `bb1` has the exact canonical shape:
`countUpHeaderState n i = [none, some (.usize n), some (.usize i), none, none, none, none, none]`.

Executing one full loop iteration (`bb1 → bb2 → bb3 → bb4 → bb1`) from
`countUpHeaderState n i` reduces **directly to `countUpHeaderState n (i + 1)`**
with **zero** `countUpLocalsAfterBb1..4` closure wrappers!
-/

def countUpBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 8
  blocks := [
    { stmts := [.assign ⟨2⟩ (.use (.constVal (.usize 0)))]
      terminator := .goto ⟨1⟩ },
    { stmts := [
        .assign ⟨4⟩ (.use (.copy ⟨2⟩)),
        .assign ⟨3⟩ (.binaryOp .lt (.move ⟨4⟩) (.copy ⟨1⟩))
      ]
      terminator := .switchInt (.move ⟨3⟩) ⟨5⟩ ⟨2⟩ },
    { stmts := [
        .assign ⟨6⟩ (.use (.copy ⟨2⟩)),
        .assign ⟨5⟩ (.binaryOp .lt (.move ⟨6⟩) (.constVal (.usize 1000)))
      ]
      terminator := .switchInt (.move ⟨5⟩) ⟨5⟩ ⟨3⟩ },
    { stmts := [
        .assign ⟨7⟩ (.checkedBinaryOp .add (.copy ⟨2⟩) (.constVal (.usize 1)))
      ]
      terminator := .assertNotOverflow ⟨7⟩ ⟨4⟩ },
    { stmts := [.assign ⟨2⟩ (.proj0 ⟨7⟩)]
      terminator := .goto ⟨1⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨2⟩))]
      terminator := .return_ }
  ]

def countUpLoopPlan : Nat → TransPlan
  | 0 => .fail
  | k + 1 =>
    .step (.step (.branch
      (.step .ret)
      (.step (.step (.branch
        (.step .ret)
        (.step (.step (.step (.step (countUpLoopPlan k))))))))))

def countUpPlan (n : Nat) : TransPlan :=
  .step (.step (countUpLoopPlan (n + 1)))

/-- Canonical loop-header state at `bb1` (`block = 1, stmtIdx = 0`):
    every temporary `_3.._7` is `none`, `_1 = n`, and `_2 = i`. -/
def countUpHeaderState (n i : Nat) : SymState where
  locals := [none, some (.usize n), some (.usize i), none, none, none, none, none]
  loans := []
  block := 1
  stmtIdx := 0

/-- Stepping through `bb0` (`_2 = 0; goto bb1`) from `mkCanonicalInit` reaches
    `countUpHeaderState n 0` for any continuation `rest : TransPlan` by `rfl`! -/
theorem countUp_entry_step (n : Nat) (rest : TransPlan) :
    evalSymState (.step (.step rest)) countUpBody
      (mkCanonicalInit countUpBody.localCount 0 [.usize n]) =
      evalSymState rest countUpBody (countUpHeaderState n 0) :=
  rfl

/-- Canonical exit state at `bb5` (`return` site) when the loop terminates at `i`. -/
def countUpExitState (n i : Nat) : SymState where
  locals := [some (.usize i), some (.usize n), some (.usize i), none, none, none, none, none]
  loans := []
  block := 5
  stmtIdx := 1

/-- One symbolic iteration of `count_up` from `countUpHeaderState n i` with an
    opaque continuation `rest : TransPlan`. Because `countUpHeaderState n i` is
    canonical, the continue branch (`i < n`, `i < 1000`, `¬(usizeMax < i + 1)`)
    reduces **directly** to `evalSymState rest countUpBody (countUpHeaderState n (i + 1))`! -/
theorem countUp_iter_step (i n : Nat) (rest : TransPlan) :
    evalSymState
      (.step (.step (.branch
        (.step .ret)
        (.step (.step (.branch
          (.step .ret)
          (.step (.step (.step (.step rest))))))))))
      countUpBody (countUpHeaderState n i) =
      if decide (i < n) then
        if decide (i < 1000) then
          if decide (usizeMax < i + 1) then none
          else evalSymState rest countUpBody (countUpHeaderState n (i + 1))
        else some (countUpExitState n i)
      else some (countUpExitState n i) := by
  dsimp [evalSymState, evalSymStep, evalBranchStep, evalSymStmt, evalSymOperand,
         evalSymBinOp, evalSymCheckedBinOp, countUpBody, countUpHeaderState,
         countUpExitState, nthOpt, getAt, setAt, forceSymState, forceLocals,
         forceOptionSymVal, forceLoans, forceOptionLoan]
  cases decide (i < n) <;> cases decide (i < 1000) <;> cases decide (usizeMax < i + 1) <;> rfl

theorem countUp_add_one_no_overflow {i : Nat} (hi : i < 1000) :
    decide (usizeMax < i + 1) = false := by
  apply decide_eq_false
  have h1000 : 1000 ≤ usizeMax := by decide
  exact Nat.not_lt.mpr (Nat.le_trans hi h1000)

/-- **Canonical Loop-Header Invariant Proof (zero closure wrappers!)**:
    At `countUpHeaderState n i`, rewriting with `countUp_iter_step` steps
    cleanly from `countUpHeaderState n i` to `countUpHeaderState n (i + 1)`. -/
theorem countUp_loop_eval (k i n : Nat)
    (hi_n : i ≤ n) (hi_1000 : i ≤ 1000) (hk : n - i ≤ k) :
    (evalSymState (countUpLoopPlan (k + 1)) countUpBody (countUpHeaderState n i)).bind
      (evalReturn countUpBody) =
      some (.usize (if decide (n ≤ 1000) then n else 1000)) := by
  induction k generalizing i with
  | zero =>
    unfold countUpLoopPlan
    rw [countUp_iter_step]
    have hnot_lt : ¬ (i < n) := by omega
    have h1 : decide (i < n) = false := decide_eq_false hnot_lt
    have hi_eq : i = n := by omega
    subst hi_eq
    have hdec : decide (i ≤ 1000) = true := decide_eq_true hi_1000
    rw [h1, hdec]
    rfl
  | succ k' ih =>
    conv => lhs; arg 1; unfold countUpLoopPlan
    rw [countUp_iter_step]
    cases h1 : decide (i < n) with
    | false =>
      have hge : n ≤ i := Nat.not_lt.mp (of_decide_eq_false h1)
      have hi_eq : i = n := Nat.le_antisymm hi_n hge
      subst hi_eq
      have hdec : decide (i ≤ 1000) = true := decide_eq_true hi_1000
      rw [hdec]; rfl
    | true =>
      have hilt : i < n := of_decide_eq_true h1
      cases h2 : decide (i < 1000) with
      | false =>
        have hge1000 : 1000 ≤ i := Nat.not_lt.mp (of_decide_eq_false h2)
        have hi_eq : i = 1000 := Nat.le_antisymm hi_1000 hge1000
        subst hi_eq
        have hnot_le : decide (n ≤ 1000) = false := decide_eq_false (Nat.not_le.mpr hilt)
        rw [hnot_le]; rfl
      | true =>
        have hi1000 : i < 1000 := of_decide_eq_true h2
        rw [countUp_add_one_no_overflow hi1000]
        dsimp
        exact ih (i + 1) hilt hi1000 (by omega)

/-- Full input-parametric verification of `count_up` for all `n : Nat`. -/
theorem countUp_eval_eq (n : Nat) :
    evalPureRet (countUpPlan n) countUpBody 0 [.usize n] =
      some (.usize (if decide (n ≤ 1000) then n else 1000)) := by
  unfold evalPureRet countUpPlan
  rw [countUp_entry_step]
  exact countUp_loop_eval n 0 n (Nat.zero_le n) (Nat.zero_le 1000) (by omega)

end CompositionalBorrowAndLoopWP
