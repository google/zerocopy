import Miri.Input.EvalUnixMemoryConstruction
import Miri.Input.CompilerFacts
import Miri.Input.CompilerShimSignatures
import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.UnixForeign
import Miri.Interpreter.ShimSignatures

/-! The source Unix memory family can be attached before the wider FD/
LinuxForeign bundle exists. Common Unix memory calls use the canonical
`UnixMemory.emulate` implementation; Linux `mremap` remains a separate later
arm with its own compiler-backed variadic signature check. -/
namespace Miri.Input.EvalUnixLinuxMemoryDispatchConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev RuntimeState (U : Type) := EvalHostRuntimeConstruction.RuntimeState U

structure Components (S : Type) where
  memory : LinuxMemory.Hooks S Miri.MIR.Place LoadedBody CallInstance
  unixMemory : UnixForeign.OptionalHandler S
  linuxPlatform : UnixForeign.OptionalHandler S

def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (environment : UnixEnvironmentDispatch.Hooks (RuntimeState U) Os E EnvVars.Kind)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory U C Payload)
    (extras : MemoryExtras.Hooks MiriMemoryKind (PointerMachine.User U) Payload)
    (spans : AllocationDriver.SpanHooks)
    (place : PlaceHooks Provenance (RuntimeState U) C MachineHooks.FrameExtra)
    (choice : C) (pageSize : UInt64) (hostUsizeBits : Nat)
    (core : ForeignItems.Core Provenance (RuntimeState U) Miri.MIR.Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance) :
    Except StepError (Components (RuntimeState U)) := do
  let compilerFacts := p.lifecycle.calls.symbols.facts.context
  let foreign : ForeignItems.Hooks Provenance (RuntimeState U) Miri.MIR.Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance := {
    toCore := core
    math := fun name _ _ _ => throw (.unsupported s!"isolated Unix memory source context reached math shim `{name}`")
    unix := fun name _ _ _ => throw (.unsupported s!"isolated Unix memory source context reached Unix shim `{name}`")
    windows := fun name _ _ _ => throw (.unsupported s!"isolated Unix memory source context reached Windows shim `{name}`")
    otherPortable := fun name _ _ _ => throw (.unsupported s!"isolated Unix memory source context reached portable shim `{name}`") }
  let signatures : ShimSignatures.Hooks Provenance (RuntimeState U) Miri.MIR.Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance :=
    CompilerShimSignatures.hooks compilerFacts {
      foreign
      types := CompilerFacts.compatibilityQueries compilerFacts
      isCVoid := fun ty => match CompilerFacts.boolean compilerFacts ty "is_c_void" with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler c_void query: {reason}")
      readScalar := fun operand => do
        let immediate ← PlaceMachine.readImmediate access operand
        match immediate.imm.toScalar with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.immediateError error)
      hostUsizeBits }
  let linuxMemory ← EvalUnixMemoryConstruction.fromSource p userRelevantCrates environment
    signatures memory extras spans place choice pageSize
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  let signature := CompilerNamedShimAbi.query p.namedAbi
  let unixMemory : UnixForeign.OptionalHandler (RuntimeState U) := fun name abi args dest => do
    if !target.families.contains "unix" then return none
    UnixMemory.emulate linuxMemory.memory name abi args dest
  let linuxPlatform : UnixForeign.OptionalHandler (RuntimeState U) := fun name abi args dest => do
    if target.os != "linux" then return none
    if name == "mmap64" then
      signatures.foreign.checkSymbolClash name
      if abi.conv != .C then throw (.undefinedBehavior "Linux legacy calling convention mismatch")
      if abi.cVariadic then throw (.undefinedBehavior "Linux legacy variadic signature")
      unless args.size == 6 do throw (.undefinedBehavior "Linux legacy argument count mismatch")
      let offsetOperand ← match args[5]? with
        | some value => pure value
        | none => throw (.invalidProgram "checked mmap64 operand missing")
      let offset ← match (← signatures.readScalar offsetOperand).toInt64 with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      UnixMemory.mmap linuxMemory.memory args offset.toInt dest
      return some .NeedsReturn
    if name == "mremap" then
      let (args,_) ← ShimSignatures.variadic signatures name (signature name) 4 abi args
      let arg : Nat → EStateM StepError (RuntimeState U) (OpTy Provenance) := fun index =>
        match args[index]? with
        | some value => pure value
        | none => throw (.invalidProgram "checked mremap operand missing")
      LinuxMemory.remap linuxMemory (← arg 0) (← arg 1) (← arg 2) (← arg 3) dest
      return some .NeedsReturn
    return none
  return ⟨linuxMemory,unixMemory,linuxPlatform⟩

end Miri.Input.EvalUnixLinuxMemoryDispatchConstruction
