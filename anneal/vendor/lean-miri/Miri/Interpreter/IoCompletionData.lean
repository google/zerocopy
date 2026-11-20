import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.Step

/-! Data environments of source IO finish callbacks. A Finish value is a
transient call parameter; only its data capture may enter HostRuntime storage.
Function coercions retain fixture compatibility without decoding functions. -/
namespace Miri.Interpreter.IoCompletionData
open Miri.Memory
abbrev Dest := MPlaceTy Provenance
abbrev Buffer := Pointer (Option Provenance) × UInt64
inductive Capture where
  | unixScalar (count : Nat) (dest : Dest)
  | unixVectored (write : Bool) (temporary : Pointer (Option Provenance))
      (buffers : Array Buffer) (dest : Dest)
  | windowsNt (count : UInt32) (status information dest : Dest)
structure Finish (S Error : Type) where
  body : Except Error Nat → EStateM StepError S Unit
  capture : Option Capture := none
instance : Coe (Except Error Nat → EStateM StepError S Unit) (Finish S Error) :=
  ⟨fun body => ⟨body,none⟩⟩
instance : CoeFun (Finish S Error) (fun _ => Except Error Nat → EStateM StepError S Unit) :=
  ⟨Finish.body⟩
def Finish.source (capture : Capture) (body : Except Error Nat → EStateM StepError S Unit) : Finish S Error :=
  ⟨body,some capture⟩
end Miri.Interpreter.IoCompletionData
