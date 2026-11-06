import Controls
open Sail.ArchSem LeanRV64D
open AnnealSail AnnealSail.Controls
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
namespace IndependentControls

noncomputable def actualX3 (op : rop) (rd : regidx) (s : SequentialState RegisterType) : Option (BitVec 64) :=
  match (interpretSailEffects
    (Functions.execute (instruction.RTYPE (regidx.Regidx 2, regidx.Regidx 1, rd, op)))).run s with
  | .ok _ s' => s'.regs.get? Register.x3
  | .error _ _ => none

theorem rejects_sub_as_add :
    actualX3 rop.SUB (regidx.Regidx 3) fixture12 ≠ some (3 : BitVec 64) := by
  exact sub_differs_from_add

theorem rd4_leaves_x3_zero :
    actualX3 rop.ADD (regidx.Regidx 4) fixture12 = some (0 : BitVec 64) := by
  unfold actualX3
  rw [rd4_fixture]
  simp [fixture12, emptyState, Std.ExtDHashMap.get?_insert]

theorem rejects_rd4_as_rd3 :
    actualX3 rop.ADD (regidx.Regidx 4) fixture12 ≠ some (3 : BitVec 64) := by
  rw [rd4_leaves_x3_zero]
  decide

theorem rejects_missing_input_success :
    (interpretSailEffects
      (Functions.execute (instruction.RTYPE
        (regidx.Regidx 2, regidx.Regidx 1, regidx.Regidx 3, rop.ADD)))).run fixtureMissing1 ≠
    EStateM.Result.ok (ExecutionResult.Retire_Success ())
      {fixtureMissing1 with regs := fixtureMissing1.regs.insert Register.x3 (2 : BitVec 64)} := by
  intro h
  rw [missing1_fixture] at h
  cases h

theorem rejects_unbounded_nat_sum :
    (actualX3 rop.ADD (regidx.Regidx 3) fixtureWrap).map (fun (x : BitVec 64) => x.toNat) ≠
      some (18446744073709551616 : Nat) := by
  unfold actualX3
  rw [add_wraps]
  simp only [Std.ExtDHashMap.get?_insert_self, Option.map_some]
  change (some (0 : Nat) : Option Nat) ≠ some (18446744073709551616 : Nat)
  decide

#print AnnealSail.Controls.execute_sub_effects
#print axioms AnnealSail.Controls.execute_sub_effects
#print AnnealSail.Controls.execute_sub_full_state
#print axioms AnnealSail.Controls.execute_sub_full_state
#print AnnealSail.Controls.execute_rd4_effects
#print axioms AnnealSail.Controls.execute_rd4_effects
#print AnnealSail.Controls.execute_rd4_full_state
#print axioms AnnealSail.Controls.execute_rd4_full_state
#print AnnealSail.Controls.add_missing_x1
#print axioms AnnealSail.Controls.add_missing_x1
#print AnnealSail.Controls.add_missing_x2
#print axioms AnnealSail.Controls.add_missing_x2
#print AnnealSail.Controls.add_wraps
#print axioms AnnealSail.Controls.add_wraps
#print AnnealSail.Controls.sub_fixture
#print axioms AnnealSail.Controls.sub_fixture
#print AnnealSail.Controls.sub_differs_from_add
#print axioms AnnealSail.Controls.sub_differs_from_add
#print AnnealSail.Controls.rd4_fixture
#print axioms AnnealSail.Controls.rd4_fixture
#print AnnealSail.Controls.rd4_observation
#print axioms AnnealSail.Controls.rd4_observation
#print AnnealSail.Controls.missing1_fixture
#print axioms AnnealSail.Controls.missing1_fixture
#print AnnealSail.Controls.missing2_fixture
#print axioms AnnealSail.Controls.missing2_fixture
#print rejects_sub_as_add
#print axioms rejects_sub_as_add
#print rd4_leaves_x3_zero
#print axioms rd4_leaves_x3_zero
#print rejects_rd4_as_rd3
#print axioms rejects_rd4_as_rd3
#print rejects_missing_input_success
#print axioms rejects_missing_input_success
#print rejects_unbounded_nat_sum
#print axioms rejects_unbounded_nat_sum

end IndependentControls
