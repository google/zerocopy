/- Source-derived draft against the complete generated official RV64D project.
   Not compiled by the author. No model or support definitions are replaced.
   Parent must check this file with actual generated/support import artifacts. -/
import LeanRV64D
import Sail.ArchSemSequential
import Std.Data.ExtDHashMap.Lemmas

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

open Sail.ArchSem
open LeanRV64D

namespace AnnealSail

/-- Exact effect tree of the real top-level execute on the selected ADD.
    In particular, there are exactly two reads and one write, with no
    memory, ignored system event, choice, or error hidden by the interpreter. -/
theorem execute_add_effects :
    Functions.execute
      (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)) =
    (FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x1 none))) fun (a : BitVec 64) =>
      FreeM.impure (.inl (.ok (@InstructionEffect.regRead (inferInstance : Arch) Register.x2 none))) fun (b : BitVec 64) =>
        FreeM.impure (.inl (.ok (@InstructionEffect.regWrite (inferInstance : Arch) Register.x3 none (a + b)))) fun _ =>
          FreeM.pure (ExecutionResult.Retire_Success ())) := by
  rfl

/-- Universal modulo-2^64 ADD, success, and equality of the entire actual
    sequential machine state. Only x1 and x2 need to be present initially. -/
theorem execute_add_full_state
    (a b : BitVec 64)
    (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b) :
    (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run s =
    EStateM.Result.ok (ExecutionResult.Retire_Success ())
      {s with regs := s.regs.insert Register.x3 (a + b)} := by
  rw [execute_add_effects]
  simp [interpretSailEffects, FreeM.liftM, interpretInstructionEffect,
    EStateM.run, EStateM.bind, EStateM.pure, EStateM.get,
    EStateM.set, EStateM.modifyGet, EStateM.map, EStateM.seqRight,
    Bind.bind, Pure.pure, Functor.map, get, modifyGet,
    MonadStateOf.get, MonadStateOf.modifyGet, modify, h1, h2]

/-- Every generated register except x3, including PC and nextPC, is framed.
    Missing unrelated registers remain missing. -/
theorem execute_add_register_frame
    (a b : BitVec 64)
    (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b)
    (r : Register) (hr : r ≠ Register.x3) :
    (match (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run s with
      | .ok _ s' => s'.regs.get? r
      | .error _ _ => none) = s.regs.get? r := by
  rw [execute_add_full_state a b s h1 h2]
  simp [Std.ExtDHashMap.get?_insert, hr, Ne.symm hr]

/-- AST execution preserves PC; this is not a fetch/step PC+4 claim. -/
theorem execute_add_pc_frame
    (a b : BitVec 64)
    (s : SequentialState RegisterType)
    (h1 : s.regs.get? Register.x1 = some a)
    (h2 : s.regs.get? Register.x2 = some b) :
    (match (interpretSailEffects
      (Functions.execute
        (instruction.RTYPE
          (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run s with
      | .ok _ s' => s'.regs.get? Register.PC
      | .error _ _ => none) = s.regs.get? Register.PC := by
  exact execute_add_register_frame a b s h1 h2 Register.PC (by decide)

#print execute_add_effects
#print axioms execute_add_effects
#print execute_add_full_state
#print axioms execute_add_full_state
#print axioms execute_add_register_frame
#print axioms execute_add_pc_frame

end AnnealSail
