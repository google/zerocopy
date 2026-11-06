module
import Kraken.X64.OmniSemantics
meta import Kraken.X64.Semantics
meta import Kraken.X64.Syntax

def base : MachineState := ⟨{}, 0⟩
theorem read_request_ignored (addr : BitVec 64) (w : Width) :
    (Effects.require_read_access addr w (fun _ => .done base)).All (fun _ => True) := by
  trivial
theorem write_request_ignored (addr : BitVec 64) (w : Width) :
    (Effects.require_write_access addr w (fun _ => .done base)).All (fun _ => True) := by
  trivial
theorem exec_request_ignored (p : Std.Rco Int64) :
    (Effects.require_exec_access p (fun _ => .done base)).All (fun _ => True) := by
  trivial
theorem undefined_must_cover_both :
    ¬ (Effects.undefined (fun b : Bool => .done ⟨{regs := {rax := if b then 1 else 0}}, 0⟩)).All
      (fun s => s.data.regs.rax = 0) := by
  intro h
  have hf := h true
  simp [Effects.All] at hf
theorem unsupported_rejected : ¬ (Effects.unimplemented "unsupported").All (fun _ => True) := by
  intro h
  exact h

def requestWidth (e : Effects) : Nat :=
  match e with
  | .require_read_access _ w _ => w.bytes
  | .require_write_access _ w _ => w.bytes
  | _ => 0
#eval requestWidth (MachineData.loadAvx {} 0 .W256 (fun _ _ => .done base))
#eval requestWidth (MachineData.storeAvx {} 0 (w := .W512) 0 (fun _ => .done base))
#eval AvxWidth.W256.bytes
#eval AvxWidth.W512.bytes
#print axioms read_request_ignored
#print axioms undefined_must_cover_both
