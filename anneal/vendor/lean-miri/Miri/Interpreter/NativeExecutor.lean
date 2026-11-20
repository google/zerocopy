import Miri.Interpreter.NativeMachine

/-! Native mod.rs::call_native_raw direct orchestration. Source lines96–126
publish the actual InterpCx interchange pointer, run Supervisor::do_ffi, clear
that pointer, then return its result (including an interpreter error). Actual
libffi invocation and stable host storage remain explicit external effects. -/
namespace Miri.Interpreter.NativeExecutor
open Miri.ABI Miri.Memory Miri.MIR
abbrev State := NativeMachine.State
abbrev M := NativeMachine.M

structure Hooks (K U C Code : Type) where
  supervisor : Native.Trace.ChildHooks (State K U) C
  /-- Build source Cif descriptors, consume each once, allocate a zeroed return
  buffer of precisely `size`, perform the actual FFI call, and report changed
  backings via publish on every returning outcome. Arbitrary native code may
  diverge; this is not a termination or safety contract. -/
  ffi : (AllocId → Array UInt8 → M K U Unit) → C → Code → Array Native.OwnedArg →
    Native.FfiType → Size → M K U (Array UInt8)

/-- Source supervisor locking/tracing/protection order is executed by the
ported driver, rather than supplied as a replacement whole rawCall callback. -/
def execute (h : Hooks K U C Code) (publish : AllocId → Array UInt8 → M K U Unit)
    (choice : C) (code : Code) (arguments : Array Native.OwnedArg)
    (resultType : Native.FfiType) (size : Size) :
    M K U (Array UInt8 × Option (Array Native.AccessEvent)) := do
  let address ← h.supervisor.currentContextAddress choice
  h.supervisor.setInterchange choice address
  let outcome ← try
    let result ← Native.Trace.doFfi h.supervisor choice
      (h.ffi publish choice code arguments resultType size)
    pure (.ok result : Except StepError (Array UInt8 × Option (Array Native.AccessEvent)))
    catch error => pure (.error error)
  h.supervisor.setInterchange choice 0
  match outcome with
  | .ok result =>
    unless result.1.size == size.bytes.toNat do
      throw (.invalidProgram "native libffi returned a buffer with incorrect source size")
    pure result
  | .error error => throw error
end Miri.Interpreter.NativeExecutor
