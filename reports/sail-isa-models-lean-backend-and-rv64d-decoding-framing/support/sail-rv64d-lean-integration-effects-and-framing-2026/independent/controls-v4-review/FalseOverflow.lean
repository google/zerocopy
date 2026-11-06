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

theorem false_unbounded_nat_sum :
    (actualX3 rop.ADD (regidx.Regidx 3) fixtureWrap).map (fun (x : BitVec 64) => x.toNat) =
      some (18446744073709551616 : Nat) := by
  unfold actualX3
  rw [add_wraps]
  simp only [Std.ExtDHashMap.get?_insert_self, Option.map_some]
  change (some (0 : Nat) : Option Nat) = some (18446744073709551616 : Nat)
  decide

end IndependentControls
