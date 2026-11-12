-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import InitialCache

namespace ProductionSteps
open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

set_option maxRecDepth 8192

def initLocals (flag width value : Word) : List Slot := [
  .uninit, .value flag, .value width, .value value, .dead,
  .uninit, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .dead, .dead, .dead, .dead,
  .dead, .uninit, .dead, .dead, .dead
]

theorem initial_sourceBody (flag width value : Word) :
    initial sourceBody [flag, width, value] = ⟨0, 0, initLocals flag width value⟩ := by rfl

def setLocalSpine : List Slot → Nat → Slot → Option (List Slot)
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
      match setLocalSpine xs n v with
      | some xs' => some (x :: xs')
      | none => none
  | [], _, _ => some []

theorem setLocalSpine_eq : ∀ (xs : List Slot) (i : Nat) (v : Slot),
    setLocalSpine xs i v = some (xs.set i v)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: xs, n + 1, v => by
      rw [setLocalSpine, setLocalSpine_eq xs n v, List.set]

def setLocal : List Slot → Nat → Slot → Option (List Slot)
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
      match setLocal xs n v with
      | some xs' => some (x :: xs')
      | none => none
  | [], _, _ => none

theorem setLocal_eq : ∀ (xs : List Slot) (i : Nat) (v : Slot),
    setLocal xs i v = if decide (i < xs.length) then some (xs.set i v) else none
  | [], i, _ => by
      have h : decide (i < ([] : List Slot).length) = false := by
        cases i <;> rfl
      rw [setLocal, h]
      rfl
  | x :: xs, 0, v => rfl
  | x :: xs, n + 1, v => by
      have hlen : decide (n + 1 < (x :: xs).length) = decide (n < xs.length) := by
        simp only [List.length_cons, Nat.add_lt_add_iff_right]
      rw [setLocal, setLocal_eq xs n v, hlen, List.set]
      cases decide (n < xs.length) <;> rfl

def evalOperandFast (body : Body) (locals : List Slot) : Operand →
    Except Fault (Ty × Word × List Slot)
  | .copy index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals)
      | .error reason => .error reason
  | .move index =>
      match readLocal body locals index with
      | .ok (ty, value) =>
          match setLocalSpine locals index .uninit with
          | some locals' => .ok (ty, value, locals')
          | none => .error .badLocal
      | .error reason => .error reason
  | .constant ty bits =>
      if rawValid ty bits then .ok (ty, BitVec.ofNat 64 bits, locals)
      else .error .invalidValue

theorem evalOperandFast_eq (body : Body) (locals : List Slot) (op : Operand) :
    evalOperandFast body locals op = evalOperand body locals op := by
  cases op with
  | copy index => rfl
  | move index =>
      dsimp only [evalOperandFast, evalOperand]
      rw [setLocalSpine_eq]
      rfl
  | constant ty bits => rfl

def evalRvalueFast (body : Body) (locals : List Slot) : Rvalue →
    Except Fault (Ty × Word × List Slot)
  | .unit => .ok (.unit, 0, locals)
  | .use operand _ => evalOperandFast body locals operand
  | .binary op left right =>
      match evalOperandFast body locals left with
      | .error reason => .error reason
      | .ok (lt, lv, locals') =>
          match evalOperandFast body locals' right with
          | .error reason => .error reason
          | .ok (rt, rv, locals'') =>
              match evalBinary op lt lv rt rv with
              | .ok (ty, value) => .ok (ty, value, locals'')
              | .error reason => .error reason
  | .discriminant index =>
      match readLocal body locals index with
      | .error reason => .error reason
      | .ok (.enum _ ds, value) =>
          match ds[value.toNat]? with
          | some disc => .ok (.int 64 true, BitVec.ofNat 64 disc, locals)
          | none => .error .invalidValue
      | .ok _ => .error .typeMismatch

theorem evalRvalueFast_eq (body : Body) (locals : List Slot) (rv : Rvalue) :
    evalRvalueFast body locals rv = evalRvalue body locals rv := by
  cases rv with
  | unit => rfl
  | use operand _ => exact evalOperandFast_eq body locals operand
  | binary op left right =>
      dsimp only [evalRvalueFast, evalRvalue]
      rw [evalOperandFast_eq]
      cases evalOperand body locals left with
      | error reason => rfl
      | ok res =>
          rcases res with ⟨lt, lv, locals'⟩
          dsimp only
          rw [evalOperandFast_eq]
          rfl
  | discriminant index => rfl

def writeLocalFast (body : Body) (locals : List Slot) (index : Nat)
    (ty : Ty) (value : Word) : Except Fault (List Slot) :=
  match body.localTys[index]?, locals[index]? with
  | some targetTy, some slot =>
      if targetTy != ty then .error .typeMismatch
      else if !(validValue targetTy value) then .error .invalidValue
      else match slot with
        | .dead => .error .deadLocal
        | _ =>
            match setLocalSpine locals index (.value value) with
            | some locals' => .ok locals'
            | none => .error .badLocal
  | _, _ => .error .badLocal

theorem writeLocalFast_eq (body : Body) (locals : List Slot) (index : Nat)
    (ty : Ty) (value : Word) :
    writeLocalFast body locals index ty value = writeLocal body locals index ty value := by
  dsimp only [writeLocalFast, writeLocal]
  rw [setLocalSpine_eq]
  rfl

def execStatementFast (body : Body) (numLocals : Nat) (locals : List Slot) : Statement →
    Except Fault (List Slot)
  | .assign index rhs =>
      match evalRvalueFast body locals rhs with
      | .error reason => .error reason
      | .ok (ty, value, locals') => writeLocalFast body locals' index ty value
  | .storageLive index =>
      if decide (index < numLocals) = true then
        (match setLocal locals index .uninit with
         | some locals' => .ok locals'
         | none => .error .badLocal)
      else .error .badLocal
  | .storageDead index =>
      if decide (index < numLocals) = true then
        (match setLocal locals index .dead with
         | some locals' => .ok locals'
         | none => .error .badLocal)
      else .error .badLocal
  | .nop => .ok locals

theorem execStatementFast_eq (body : Body) (locals : List Slot) (stmt : Statement) :
    execStatementFast body body.localTys.length locals stmt = execStatement body locals stmt := by
  cases stmt with
  | assign index rhs =>
      dsimp only [execStatementFast, execStatement]
      rw [evalRvalueFast_eq]
      cases evalRvalue body locals rhs with
      | error reason => rfl
      | ok res =>
          rcases res with ⟨ty, value, locals'⟩
          exact writeLocalFast_eq body locals' index ty value
  | storageLive index =>
      dsimp only [execStatementFast, execStatement]
      rw [setLocal_eq]
      cases decide (index < body.localTys.length) <;>
        cases decide (index < locals.length) <;> rfl
  | storageDead index =>
      dsimp only [execStatementFast, execStatement]
      rw [setLocal_eq]
      cases decide (index < body.localTys.length) <;>
        cases decide (index < locals.length) <;> rfl
  | nop => rfl

def execTerminatorFast (body : Body) (locals : List Slot) : Terminator → StepResult
  | .goto block => .next ⟨block, 0, locals⟩
  | .switchInt operand targets otherwise =>
      match evalOperandFast body locals operand with
      | .error reason => .fault reason
      | .ok (ty, value, locals') =>
          if switchTy ty then
            .next ⟨switchTarget value.toNat targets otherwise, 0, locals'⟩
          else .fault .typeMismatch
  | .ret =>
      match readLocal body locals 0 with
      | .ok (_, value) => .ret value
      | .error reason => .fault reason
  | .unreachable => .fault .unreachable

theorem execTerminatorFast_eq (body : Body) (state : State) (term : Terminator) :
    execTerminatorFast body state.locals term = execTerminator body state term := by
  cases term with
  | goto block => rfl
  | switchInt operand targets otherwise =>
      dsimp only [execTerminatorFast, execTerminator]
      rw [evalOperandFast_eq]
      rfl
  | ret => rfl
  | unreachable => rfl

def stepFast (body : Body) (numLocals : Nat) : State → StepResult
  | ⟨blockIdx, stmtIdx, locals⟩ =>
      match body.blocks[blockIdx]? with
      | none => .fault .badBlock
      | some block =>
          match block.statements[stmtIdx]? with
          | some statement =>
              match execStatementFast body numLocals locals statement with
              | .ok locals' => .next ⟨blockIdx, stmtIdx + 1, locals'⟩
              | .error reason => .fault reason
          | none =>
              if stmtIdx == block.statements.length then
                execTerminatorFast body locals block.terminator
              else .fault .badPosition

theorem stepFast_eq (body : Body) (state : State) :
    stepFast body body.localTys.length state = step body state := by
  cases state with
  | mk blockIdx stmtIdx locals =>
      dsimp only [stepFast, step]
      cases body.blocks[blockIdx]? with
      | none => rfl
      | some block =>
          dsimp only
          cases block.statements[stmtIdx]? with
          | some statement =>
              dsimp only
              rw [execStatementFast_eq]
              rfl
          | none =>
              dsimp only
              rw [execTerminatorFast_eq body ⟨blockIdx, stmtIdx, locals⟩ block.terminator]

def runFastAux (body : Body) (numLocals : Nat) : Nat → State → Option Word
  | 0, _ => none
  | fuel + 1, state =>
      match stepFast body numLocals state with
      | .next nextState => runFastAux body numLocals fuel nextState
      | .ret value => some value
      | .fault _ => none

theorem runFastAux_eq_run (body : Body) : ∀ (fuel : Nat) (state : State),
    runFastAux body body.localTys.length fuel state = run body fuel state
  | 0, _ => rfl
  | fuel + 1, state => by
      change (match stepFast body body.localTys.length state with
        | .next nextState => runFastAux body body.localTys.length fuel nextState
        | .ret value => some value
        | .fault _ => none) =
        (match step body state with
        | .next nextState => run body fuel nextState
        | .ret value => some value
        | .fault _ => none)
      rw [stepFast_eq]
      cases step body state with
      | next nextState => exact runFastAux_eq_run body fuel nextState
      | ret value => rfl
      | fault reason => rfl

theorem sourceBody_numLocals : sourceBody.localTys.length = 65 := rfl

theorem path_success {flag width value result : Word} {fuel : Nat}
    (h : runFastAux sourceBody 65 fuel ⟨0, 0, initLocals flag width value⟩ = some result) :
    Safe sourceBody [flag, width, value] ∧
      Returns sourceBody [flag, width, value] result := by
  unfold Safe Returns
  rw [initial_sourceBody flag width value]
  have h' : runFastAux sourceBody sourceBody.localTys.length fuel ⟨0, 0, initLocals flag width value⟩ = some result := by
    rw [sourceBody_numLocals]
    exact h
  exact run_success (runFastAux_eq_run sourceBody fuel _ ▸ h')

theorem le8 (value : Word) :
    Safe sourceBody [0, 0, value] ∧
      Returns sourceBody [0, 0, value] (value &&& 255) := by
  have h : runFastAux sourceBody 65 12 ⟨0, 0, initLocals 0 0 value⟩ = some (value &&& 255) := by rfl
  exact path_success h

theorem le16 (value : Word) :
    Safe sourceBody [0, 1, value] ∧
      Returns sourceBody [0, 1, value] (value &&& 65535) := by
  have h : runFastAux sourceBody 65 12 ⟨0, 0, initLocals 0 1 value⟩ = some (value &&& 65535) := by rfl
  exact path_success h

theorem le32 (value : Word) :
    Safe sourceBody [0, 2, value] ∧
      Returns sourceBody [0, 2, value] (value &&& 4294967295) := by
  have h : runFastAux sourceBody 65 12 ⟨0, 0, initLocals 0 2 value⟩ = some (value &&& 4294967295) := by rfl
  exact path_success h

theorem le64 (value : Word) :
    Safe sourceBody [0, 3, value] ∧
      Returns sourceBody [0, 3, value] value := by
  have h : runFastAux sourceBody 65 9 ⟨0, 0, initLocals 0 3 value⟩ = some value := by rfl
  exact path_success h

theorem be8 (value : Word) :
    Safe sourceBody [1, 0, value] ∧
      Returns sourceBody [1, 0, value] (swap8 value) := by
  have h : runFastAux sourceBody 65 12 ⟨0, 0, initLocals 1 0 value⟩ = some (swap8 value) := by rfl
  exact path_success h

theorem be16 (value : Word) :
    Safe sourceBody [1, 1, value] ∧
      Returns sourceBody [1, 1, value] (swap16 value) := by
  have h : runFastAux sourceBody 65 33 ⟨0, 0, initLocals 1 1 value⟩ = some (swap16 value) := by rfl
  exact path_success h

theorem be32 (value : Word) :
    Safe sourceBody [1, 2, value] ∧
      Returns sourceBody [1, 2, value] (swap32 value) := by
  have h : runFastAux sourceBody 65 57 ⟨0, 0, initLocals 1 2 value⟩ = some (swap32 value) := by rfl
  exact path_success h

theorem be64 (value : Word) :
    Safe sourceBody [1, 3, value] ∧
      Returns sourceBody [1, 3, value] (swap64 value) := by
  have h : runFastAux sourceBody 65 99 ⟨0, 0, initLocals 1 3 value⟩ = some (swap64 value) := by rfl
  exact path_success h

end ProductionSteps
