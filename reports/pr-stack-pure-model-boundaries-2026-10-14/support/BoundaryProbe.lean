import Rust

open Rust.Storage

-- This proof-carrying layout satisfies numerical laws without a Rust type index.
def numericalLayout : Rust.Layout :=
  ⟨1, 1, Rust.alignment_one, by decide⟩

example : numericalLayout.size = 1 := rfl

-- Geometry deliberately contains no live allocation or pointer-permission fact.
def emptyAllocation : Rust.Allocation :=
  ⟨100, 0, fun _ => False, by simp⟩
def emptyReferent : Rust.Referent :=
  ⟨100, 0, fun _ => False, by simp⟩
example : Rust.FitsInAllocation emptyReferent emptyAllocation := by
  simp [Rust.FitsInAllocation, emptyReferent, emptyAllocation]

-- Width and initialization are distinct; the domain can also be vacuous.
def noInputs : BitDecoder Unit where
  byteSize := 1
  decode _ := none
theorem noInputs_initialized : noInputs.Initialized := by
  intro bytes raw h
  simp [BitDecoder.run, noInputs] at h

def allInputs : BitDecoder Unit where
  byteSize := 1
  decode _ := some ()
example : allInputs.run [AMByte.uninit] = some () := by decide
theorem allInputs_not_initialized : ¬ allInputs.Initialized := by
  intro h
  have impossible := h [AMByte.uninit] () (by decide)
  simp [Initialized] at impossible

example : (arrayDecoder boolDecoder 2).run [AMByte.init 0, AMByte.uninit] = none := by decide
example : (arrayDecoder unitDecoder 3).run [] = some ⟨[(), (), ()], rfl⟩ := by decide
example : Rust.Bytes.decodeLE [1, 0] = 1 := by decide
example : Rust.Bytes.decodeBE [1, 0] = 256 := by decide
example : Rust.roundUpToAlign 9 0 = 0 := by decide

#print axioms noInputs_initialized
#print axioms allInputs_not_initialized
#print axioms Rust.Storage.arrayDecoder_initialized
