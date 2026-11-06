import Std
namespace Packet
abbrev Byte := Fin 256

def writePayload (payload destination : List Byte) : Option (List Byte) :=
  if payload.length ≤ destination.length then some (payload ++ destination.drop payload.length) else none

theorem write_success (payload destination : List Byte) (capacity : payload.length ≤ destination.length) :
    writePayload payload destination = some (payload ++ destination.drop payload.length) := by
  simp [writePayload,capacity]
theorem write_short (payload destination : List Byte) (capacity : ¬ payload.length ≤ destination.length) :
    writePayload payload destination = none := by simp [writePayload,capacity]
theorem write_frame (payload destination : List Byte) :
    (payload ++ destination.drop payload.length).drop payload.length = destination.drop payload.length := by simp

def validFlags (flags : List Byte) : Bool := flags.length == 4 && flags.all (fun b => b.val < 2)
def process (flags payload destination : List Byte) (available : Bool) : Option (List Byte) :=
  if validFlags flags && available then writePayload payload destination else none

theorem invalid_flags_no_write (flags payload destination : List Byte) (invalid : validFlags flags = false) :
    process flags payload destination available = none := by simp [process,invalid]
theorem missing_payload_no_write (flags payload destination : List Byte) :
    process flags payload destination false = none := by simp [process]
theorem pipeline_success (flags payload destination : List Byte) (valid : validFlags flags = true)
    (capacity : payload.length ≤ destination.length) :
    process flags payload destination true = some (payload ++ destination.drop payload.length) := by
  simp [process, valid, writePayload, capacity]

def expectedLayout (wordBytes : Nat) : List Nat := [wordBytes,4,1,2,1]
#print axioms write_success
#print axioms write_short
#print axioms write_frame
#print axioms invalid_flags_no_write
#print axioms missing_payload_no_write
#print axioms pipeline_success
end Packet
