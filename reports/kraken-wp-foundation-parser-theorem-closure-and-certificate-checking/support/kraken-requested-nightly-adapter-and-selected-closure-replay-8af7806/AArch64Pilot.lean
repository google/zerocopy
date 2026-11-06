import Kraken.AArch64.Examples.Examples

open Kraken.AArch64 Kraken.AArch64.Parser

def addBody : Program := parseAArch64("add x0, x0, x1")

theorem addBody_correct [layout : Layout] (d : MachineData) :
    straightlineStep (layout addBody) ⟨d, layout.start⟩
      (fun s' => s'.1.regs.X0 = d.regs.X0 + d.regs.X1 ∧
                  s'.1.dmem = d.dmem ∧ s'.1.regs.SP = d.regs.SP ∧
                  s'.1.status = d.status) := by
  kprologue addBody with d
  sym => kstep; tactic =>
  simp (config := { zetaDelta := true })

def addReturn : Program := parseAArch64("add x0, x0, x1\nret")

theorem addReturn_correct [layout : Layout] (d : MachineData) :
    straightlineStep (layout addReturn) ⟨d, layout.start⟩
      (fun s' => s'.1 = { d with regs := { d.regs with X0 := d.regs.X0 + d.regs.X1 } } ∧
                  s'.2.toBitVec = d.regs.X30.toBitVec) := by
  kprologue addReturn with d
  sym => kstep; tactic =>
  simp (config := { zetaDelta := true })

#print axioms addBody_correct
#print axioms addReturn_correct
