import Miri.Interpreter.ExecutionChoices
import Miri.Interpreter.RawMemoryMachine

/-! Pinned helpers.rs::gen_random. Source host getrandom failure is unsupported;
isolated random bytes are nondeterministic semantic inputs, never a fixed seed. -/
namespace Miri.Interpreter.RandomMemory
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S : Type) where
  communicate : Bool
  hostUsizeBits : Nat
  /-- Host getrandom::fill result; retains its actual state/error effects. -/
  hostFill : Nat → M S (Except String ByteArray)
  isolatedFill : Nat → M S ByteArray
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit

def generate (h : Hooks S) (pointer : Pointer (Option Provenance)) (length : UInt64) : M S Unit := do
  if length == 0 then return
  if length.toNat >= 2^h.hostUsizeBits then throw (.invalidProgram "random length host usize conversion")
  let bytes ← if h.communicate then do
      match ← h.hostFill length.toNat with
      | .ok bytes => pure bytes
      | .error reason => throw (.unsupported s!"host getrandom failed: {reason}")
    else h.isolatedFill length.toNat
  unless bytes.size == length.toNat do throw (.invalidProgram "random fill violated fixed buffer length")
  h.writeBytes pointer bytes

def bind [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (tape : ExecutionChoices.Access (MachineHooks.State K U))
    (base : Hooks (MachineHooks.State K U)) : Hooks (MachineHooks.State K U) :=
  {base with
    isolatedFill := ExecutionChoices.bytes tape .osRandom
    writeBytes := RawMemoryMachine.writeBytes access ⟨access.runtime.pointerSize⟩}

/-- Construct helpers.rs::gen_random directly from genuine host effects and
the current machine's source-choice tape and physical byte writer. This form
does not require placeholder random or memory callbacks in a baseline record. -/
def machine [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (tape : ExecutionChoices.Access (MachineHooks.State K U))
    (communicate : Bool) (hostUsizeBits : Nat)
    (hostFill : Nat → M (MachineHooks.State K U) (Except String ByteArray)) :
    Hooks (MachineHooks.State K U) := {
  communicate
  hostUsizeBits
  hostFill
  isolatedFill := ExecutionChoices.bytes tape .osRandom
  writeBytes := RawMemoryMachine.writeBytes access ⟨access.runtime.pointerSize⟩
}
end Miri.Interpreter.RandomMemory
