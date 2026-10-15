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

theorem false_rd4_as_rd3 :
    actualX3 rop.ADD (regidx.Regidx 4) fixture12 = some (3 : BitVec 64) := by
  have hx : actualX3 rop.ADD (regidx.Regidx 4) fixture12 = some (0 : BitVec 64) := by
    unfold actualX3
    rw [rd4_fixture]
    simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]
  rw [hx]
  decide

end IndependentControls
