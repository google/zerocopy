import InitialCache

namespace TestRunStmtsFast
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

def setLocal : List Slot → Nat → Slot → Option (List Slot)
  | _ :: xs, 0, v => some (v :: xs)
  | x :: xs, n + 1, v =>
      match setLocal xs n v with
      | some xs' => some (x :: xs')
      | none => none
  | [], _, _ => none

def evalOperandFast (body : Body) (locals : List Slot) : Operand →
    Except Fault (Ty × Word × List Slot)
  | .copy index =>
      match readLocal body locals index with
      | .ok (ty, value) => .ok (ty, value, locals)
      | .error reason => .error reason
  | .move index =>
      match readLocal body locals index with
      | .ok (ty, value) =>
          match setLocal locals index .uninit with
          | some locals' => .ok (ty, value, locals')
          | none => .error .badLocal
      | .error reason => .error reason
  | .constant ty bits =>
      if rawValid ty bits then .ok (ty, BitVec.ofNat 64 bits, locals)
      else .error .invalidValue

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

def writeLocalFast (body : Body) (locals : List Slot) (index : Nat)
    (ty : Ty) (value : Word) : Except Fault (List Slot) :=
  match body.localTys[index]?, locals[index]? with
  | some targetTy, some slot =>
      if targetTy != ty then .error .typeMismatch
      else if !(validValue targetTy value) then .error .invalidValue
      else match slot with
        | .dead => .error .deadLocal
        | _ =>
            match setLocal locals index (.value value) with
            | some locals' => .ok locals'
            | none => .error .badLocal
  | _, _ => .error .badLocal

def execStatementFast (body : Body) (numLocals : Nat) (locals : List Slot) : Statement →
    Except Fault (List Slot)
  | .assign index rhs =>
      match evalRvalueFast body locals rhs with
      | .error reason => .error reason
      | .ok (ty, value, locals') => writeLocalFast body locals' index ty value
  | .storageLive index =>
      if index < numLocals then
        match setLocal locals index .uninit with
        | some locals' => .ok locals'
        | none => .error .badLocal
      else .error .badLocal
  | .storageDead index =>
      if index < numLocals then
        match setLocal locals index .dead with
        | some locals' => .ok locals'
        | none => .error .badLocal
      else .error .badLocal
  | .nop => .ok locals

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

def runBlocksFast (body : Body) (numLocals : Nat) : Nat → Nat → List Statement → Terminator → List Slot → Option Word
  | 0, _, _, _, _ => none
  | fuel + 1, blockIdx, stmt :: rest, term, locals =>
      match execStatementFast body numLocals locals stmt with
      | .ok locals' => runBlocksFast body numLocals fuel blockIdx rest term locals'
      | .error _ => none
  | fuel + 1, _, [], term, locals =>
      match execTerminatorFast body locals term with
      | .next ⟨nextBlock, 0, locals'⟩ =>
          match body.blocks[nextBlock]? with
          | some b => runBlocksFast body numLocals fuel nextBlock b.statements b.terminator locals'
          | none => none
      | .next _ => none
      | .ret value => some value
      | .fault _ => none

def startBlocksFast (body : Body) (fuel : Nat) (locals : List Slot) : Option Word :=
  match body.blocks[0]? with
  | some b => runBlocksFast body body.localTys.length fuel 0 b.statements b.terminator locals
  | none => none

theorem le8_fast (value : Word) :
    startBlocksFast sourceBody 12 (initLocals 0 0 value) = some (value &&& 255) := by rfl

theorem le16_fast (value : Word) :
    startBlocksFast sourceBody 12 (initLocals 0 1 value) = some (value &&& 65535) := by rfl

theorem le32_fast (value : Word) :
    startBlocksFast sourceBody 12 (initLocals 0 2 value) = some (value &&& 4294967295) := by rfl

theorem le64_fast (value : Word) :
    startBlocksFast sourceBody 9 (initLocals 0 3 value) = some value := by rfl

theorem be8_fast (value : Word) :
    startBlocksFast sourceBody 12 (initLocals 1 0 value) = some (swap8 value) := by rfl

theorem be16_fast (value : Word) :
    startBlocksFast sourceBody 33 (initLocals 1 1 value) = some (swap16 value) := by rfl

theorem be32_fast (value : Word) :
    startBlocksFast sourceBody 57 (initLocals 1 2 value) = some (swap32 value) := by rfl

theorem be64_fast (value : Word) :
    startBlocksFast sourceBody 99 (initLocals 1 3 value) = some (swap64 value) := by rfl

end TestRunStmtsFast
