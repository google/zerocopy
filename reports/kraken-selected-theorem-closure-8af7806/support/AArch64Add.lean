module
import all Kraken.AArch64.Examples.Examples
open Kraken.AArch64
open Kraken.AArch64.Parser
def addPilot : Program := parseAArch64("add x0, x1, #42")
theorem addPilot_correct [layout : Layout] (d : MachineData) :
    straightlineStep (layout addPilot) ⟨d, layout.start⟩
      (fun s' => s'.data.regs.X0 = d.regs.X1 + 42) := by
  kprologue addPilot with d
  sym => kstep; tactic =>
  simp (config := { zetaDelta := true })
#print axioms addPilot_correct
