import Miri.Input.CompilerNamedShimAbi
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalWorld
import Miri.Input.EvalUnixSourceConstruction
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.SourceOther
import Miri.Interpreter.Unwind

/-! Source Unix `dlsym` and `_Unwind_RaiseException` construction. Function
symbols go through the canonical FunctionPointers registry, data symbols read
the live ExternStatic root, C strings use actual guest memory, and unwind
payloads use the source thread/runtime store. -/
namespace Miri.Input.EvalUnixDynamicConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.State Os R P H D Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Error

private def lift (value : Except StepError A) : EStateM StepError S A :=
  match value with
  | .ok result => pure result
  | .error error => throw error

/-- Source `read_c_str`: scan one byte at a time through the terminator, then
perform the source's second full byte read. Every access goes through the
canonical guest allocation/access hooks and preserves partial state. -/
private def readCString [DecidableEq MiriMemoryKind]
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control
        (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
          (EvalSyncMachine.Host Poll Instant System H D (Other Raw Listener TcpStream Error)
            Native Profiler))) C P)
    (budget : Nat) (pointer : Pointer (Option Provenance)) :
    EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      ByteArray := do
  let rec scan : Nat → Nat → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Nat
    | 0,_ => throw (.resourceExhaustion "dlsym C string scan budget")
    | fuel+1,length => do
      if length >= 2^64 then throw (.invalidProgram "dlsym C string length overflow")
      let current ← lift (RawMemoryMachine.offset memory.pointers.arithmetic pointer (UInt64.ofNat length))
      if (← RawMemoryMachine.readByte memory.access memory.pointers.arithmetic current) == 0 then
        pure length
      else scan fuel (length+1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes memory.access memory.pointers.arithmetic pointer
    (UInt64.ofNat length)
  unless bytes.size == length do
    throw (.invalidProgram "dlsym C string byte-read length mismatch")
  pure bytes

/-- Build the target-aware optional Unix dynamic-symbol handler from canonical
source owners. `core` supplies only common source ABI/argument/result
operations; this constructor owns the dynamic policy, guest C string, actual
function registry, extern-static root, and start-unwind action. -/
def handlerFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control
        (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
          (EvalSyncMachine.Host Poll Instant System H D (Other Raw Listener TcpStream Error)
            Native Profiler))) C P)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Other Raw Listener TcpStream Error))
    (choice : C)
    (unwind : Unwind.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C (Other Raw Listener TcpStream Error))
    (core : ForeignItems.Core Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) : Except StepError
      (UnixForeign.OptionalHandler
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram "Unix dynamic-symbol constructor on a non-Unix target")
  let primitive : ShimSignatures.PrimitiveHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := {
    family := core.family
    os := core.os
    checkAbi := ForeignItems.Core.checkAbi core
    checkSymbolClash := core.checkSymbolClash
    transmute := core.transmute }
  let hook : UnixDynamic.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (MPlaceTy Provenance) LoadedBody CallInstance := {
    signatures := primitive
    signature := CompilerNamedShimAbi.query p.namedAbi
    targetEnv := target.env
    readUsize := core.readUsize
    readPointer := core.readPointer
    readCString := readCString memory memory.stringScanBudget
    functionPointer := fun symbol => do
      let pointer ← FunctionPointers.functionPointer functions
        (.Other (SourceOther.unixSymbol symbol))
      pure pointer.withOptionalProvenance
    externStatic := fun name => do
      let entries := EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter (← get).machine.user)
        |>.symbols.filter (·.1 == name)
      if entries.size > 1 then throw (.invalidProgram "duplicate canonical extern static")
      pure (entries[0]?.map fun (_,pointer) => pointer.withOptionalProvenance)
    writePointer := core.writePointer
    writeNull := core.writeNull
    startUnwind := Unwind.handleStartUnwind unwind choice }
  pure fun name abi args destination => UnixDynamic.emulate hook name abi args destination

end Miri.Input.EvalUnixDynamicConstruction
