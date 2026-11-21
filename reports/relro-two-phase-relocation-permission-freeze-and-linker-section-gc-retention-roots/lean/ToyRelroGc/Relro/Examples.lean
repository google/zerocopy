import ToyRelroGc.Relro.Model

/-!
Concrete instances and definition examples for the RELRO model.
-/
namespace Toy.RelroGc

/-- Symbol table used by the examples: symbol `s` is at address `100 + s`. -/
def sa0 : SymTab := fun s => 100 + s

/-- Address-only relocation writing the address of symbol `t` into `x`. -/
def symReloc (x : Nat) (t : Sym) : Reloc := ⟨x, fun sa _ => sa t⟩

/-- Instance: byte 0 is RELRO holding a relocated pointer, byte 1 is mutable; `protect`
covers exactly byte 0. -/
def goodCfg : Cfg where
  kinds := [.relro, .mutable]
  init := fun _ => 0
  relocs := [symReloc 0 0]
  prot := rangeMask 0 1
  lazy := []
  stub := 0

example : LoadOk (trace goodCfg sa0 (twoPhase goodCfg [])) := by decide

example : (trace goodCfg sa0 (twoPhase goodCfg [.write 0 5, .write 1 5])).opOuts = [.fault, .ok] := by
  decide

example : (trace goodCfg sa0 (twoPhase goodCfg [])).memAtProtect =
    some (applyAll sa0 goodCfg.relocs goodCfg.init) := rfl

end Toy.RelroGc
