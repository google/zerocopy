/- Source-derived semantic controls; not compiled by author.
   Compile the unchanged Proof.lean first as module Proof, then this file.
   These prove witnesses. They do not equate tactic failure with rejection. -/
import Proof

open Sail.ArchSem LeanRV64D

namespace AnnealSail.Controls

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

/-- Actual top-level SUB has the same three effects, with subtraction. -/
theorem execute_sub_effects :
    Functions.execute
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.SUB)) =
    (FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x1 none))) fun (a : BitVec 64) =>
      FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x2 none))) fun (b : BitVec 64) =>
        FreeM.impure (.inl (.ok (@InstructionEffect.regWrite (inferInstance : Arch) Register.x3 none (a - b)))) fun _ =>
          FreeM.pure (ExecutionResult.Retire_Success ())) := by
  rfl

theorem execute_sub_full_state
    (a b : BitVec 64) (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b) :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.SUB)))).run s =
    .ok (ExecutionResult.Retire_Success ())
      {s with regs := s.regs.insert Register.x3 (a - b)} := by
  rw [execute_sub_effects]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, getThe, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, h1, h2]

/-- Wrong-destination control still invokes the actual generated executor. -/
theorem execute_rd4_effects :
    Functions.execute
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 4, rop.ADD)) =
    (FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x1 none))) fun (a : BitVec 64) =>
      FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x2 none))) fun (b : BitVec 64) =>
        FreeM.impure (.inl (.ok (@InstructionEffect.regWrite (inferInstance : Arch) Register.x4 none (a + b)))) fun _ =>
          FreeM.pure (ExecutionResult.Retire_Success ())) := by
  rfl

theorem execute_rd4_full_state
    (a b : BitVec 64) (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b) :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 4, rop.ADD)))).run s =
    .ok (ExecutionResult.Retire_Success ())
      {s with regs := s.regs.insert Register.x4 (a + b)} := by
  rw [execute_rd4_effects]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, getThe, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, h1, h2]

theorem add_missing_x1
    (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = none) :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run s =
    .error .Unreachable s := by
  rw [AnnealSail.execute_add_effects]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, getThe, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, h1]

theorem add_missing_x2
    (a : BitVec 64) (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = none) :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run s =
    .error .Unreachable s := by
  rw [AnnealSail.execute_add_effects]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, getThe, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw, h1, h2]

/-- Full real dependent-map state; unmentioned registers and all memory absent. -/
def emptyState : SequentialState RegisterType :=
  { regs := {}, mem := {}, tags := (), cycleCount := 0, sailOutput := #[] }

def fixture12 : SequentialState RegisterType :=
  { emptyState with regs := (((emptyState.regs.insert Register.x1 1).insert Register.x2 2).insert Register.x3 0).insert Register.x4 0 }

def fixtureWrap : SequentialState RegisterType :=
  { emptyState with regs := (emptyState.regs.insert Register.x1 18446744073709551615).insert Register.x2 1 }

def fixtureMissing1 : SequentialState RegisterType :=
  { emptyState with regs := emptyState.regs.insert Register.x2 2 }

def fixtureMissing2 : SequentialState RegisterType :=
  { emptyState with regs := emptyState.regs.insert Register.x1 1 }

theorem add_wraps :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run fixtureWrap =
    .ok (ExecutionResult.Retire_Success ())
      {fixtureWrap with regs := fixtureWrap.regs.insert Register.x3 0} := by
  have h1 : fixtureWrap.regs.get? Register.x1 = some (18446744073709551615 : BitVec 64) := by
    simp [fixtureWrap, emptyState, Std.ExtDHashMap.get?_insert]
  have h2 : fixtureWrap.regs.get? Register.x2 = some (1 : BitVec 64) := by
    simp [fixtureWrap, emptyState, Std.ExtDHashMap.get?_insert]
  have hw : (18446744073709551615 : BitVec 64) + 1 = 0 := by decide
  simpa only [hw] using
    AnnealSail.execute_add_full_state 18446744073709551615 1 fixtureWrap h1 h2

theorem sub_fixture :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.SUB)))).run fixture12 =
    .ok (ExecutionResult.Retire_Success ())
      {fixture12 with regs := fixture12.regs.insert Register.x3 (18446744073709551615 : BitVec 64)} := by
  have h1 : fixture12.regs.get? Register.x1 = some (1 : BitVec 64) := by
    simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]
  have h2 : fixture12.regs.get? Register.x2 = some (2 : BitVec 64) := by
    simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]
  have hw : (1 : BitVec 64) - 2 = 18446744073709551615 := by decide
  simpa only [hw] using execute_sub_full_state 1 2 fixture12 h1 h2

/-- Constructive wrong-op witness: actual SUB x3 is all ones, not ADD's3. -/
theorem sub_differs_from_add :
    (match (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.SUB)))).run fixture12 with
      | .ok _ s' => s'.regs.get? Register.x3
      | .error _ _ => none) ≠ some (3 : BitVec 64) := by
  rw [sub_fixture]
  simp only [Std.ExtDHashMap.get?_insert_self]
  change (some (18446744073709551615 : BitVec 64) : Option (BitVec 64)) ≠ some (3 : BitVec 64)
  decide

theorem rd4_fixture :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 4, rop.ADD)))).run fixture12 =
    .ok (ExecutionResult.Retire_Success ())
      {fixture12 with regs := fixture12.regs.insert Register.x4 3} := by
  have h1 : fixture12.regs.get? Register.x1 = some (1 : BitVec 64) := by
    simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]
  have h2 : fixture12.regs.get? Register.x2 = some (2 : BitVec 64) := by
    simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]
  have hw : (1 : BitVec 64) + 2 = 3 := by decide
  simpa only [hw] using execute_rd4_full_state 1 2 fixture12 h1 h2

/-- Actual wrong-rd result keeps x3=0 and writes x4=3. -/
theorem rd4_observation :
    (match (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 4, rop.ADD)))).run fixture12 with
      | .ok _ s' => (s'.regs.get? Register.x3, s'.regs.get? Register.x4)
      | .error _ _ => (none, none)) = (some (0 : BitVec 64), some (3 : BitVec 64)) := by
  rw [rd4_fixture]
  simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]

theorem missing1_fixture :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run fixtureMissing1 =
    .error .Unreachable fixtureMissing1 := by
  apply add_missing_x1
  simp [fixtureMissing1, emptyState, Std.ExtDHashMap.get?_insert]

theorem missing2_fixture :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run fixtureMissing2 =
    .error .Unreachable fixtureMissing2 := by
  apply add_missing_x2 1
  · simp [fixtureMissing2, emptyState, Std.ExtDHashMap.get?_insert]
  · simp [fixtureMissing2, emptyState, Std.ExtDHashMap.get?_insert]

#print axioms add_wraps
#print axioms sub_fixture
#print axioms sub_differs_from_add
#print axioms rd4_fixture
#print axioms rd4_observation
#print axioms missing1_fixture
#print axioms missing2_fixture

end AnnealSail.Controls
