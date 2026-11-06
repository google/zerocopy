import Controls
open Sail.ArchSem LeanRV64D
open AnnealSail AnnealSail.Controls
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
namespace IndependentControls

def actualX3 (op : rop) (rd : regidx) (s : SequentialState RegisterType) : Option (BitVec 64) :=
  match (interpretSailEffects
    (Functions.execute (instruction.RTYPE (regidx.Regidx 2, regidx.Regidx 1, rd, op)))).run s with
  | .ok _ s' => s'.regs.get? Register.x3
  | .error _ _ => none

theorem false_missing_input_success :
    (interpretSailEffects
      (Functions.execute (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run fixtureMissing1 =
    EStateM.Result.ok (ExecutionResult.Retire_Success ())
      {fixtureMissing1 with regs := fixtureMissing1.regs.insert Register.x3 (2 : BitVec 64)} := by
  rw [missing1_fixture]
  rfl

end IndependentControls
