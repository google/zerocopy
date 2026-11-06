module
import Kraken.AArch64.OmniSemantics
import all Kraken.Mem

-- One explicit environment response, not general device/interrupt semantics.
def readyMemory : DataMem := (∅ : DataMem).insert (256#64) 42

def deviceEffect : Effects :=
  .nonmem_load {} 61440 .W8 (fun value memory =>
    .done ⟨{ regs := { X0 := UInt64.ofNat value.toNat }, dmem := memory }, 4⟩)

def readyPost (s : MachineState) : Prop :=
  s.data.regs.X0 = 7 ∧ s.data.dmem = readyMemory ∧ s.pc = 4

theorem default_rejects_device : ¬ deviceEffect.All readyPost := by
  simp [deviceEffect, Effects.All]

-- Checking this response does not prove a physical device obeys it.
def chosenDeviceContract : Prop :=
  readyPost ⟨{regs := {X0 := 7}, dmem := readyMemory}, 4⟩

theorem response_satisfies_contract : chosenDeviceContract := by
  simp [chosenDeviceContract, readyPost]

theorem omitted_memory_effect_rejected :
    ¬ readyPost ⟨{regs := {X0 := 7}, dmem := {}}, 4⟩ := by
  intro h
  have values := congrArg (fun m : DataMem => m[256#64]?) h.2.1
  simp [readyMemory] at values

#print axioms default_rejects_device
#print axioms response_satisfies_contract
#print axioms omitted_memory_effect_rejected
