import Miri.Input.EvalStartupWindows
import Miri.Input.EvalPreparation
import Miri.Input.EvalEntrySymbols
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.CompilerForeignSymbols

/-! Compiler-backed assembly of the canonical startup runner. This closes
the startup facts, argv allocation, platform constant lookup, Main/TLS policy,
late-init hooks, and fixed-config run loop around one prepared compiler input.
Host environment and extern-static effects remain explicit source capabilities.
-/
namespace Miri.Input.EvalStartupAssembly
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev W := EvalEntryMachine.W
abbrev User Os R P H D O Aff B Host := EvalExecutable.U Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalRuntimeConstruction.EntryState Os R P H D O Aff B Host
abbrev InnerState Os R P H D O Aff B Host :=
  MachineHooks.State MiriMemoryKind (EvalEntryMachine.InnerUser Os R P H D O Aff B Host)
abbrev InnerControl Os R P H D O Aff B Host :=
  ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))

/-- The inner pointer-machine lens for the single environment root in
EvalWorld. Reads go through the registered canonical root view; writes update
that same runtime field and preserve every surrounding world field. -/
def environmentLens : EvalHostRuntimeConstruction.EnvironmentLens
    (InnerControl Os R P H D O Aff B Host) Os := {
  get := fun user => EvalWorld.roots.environment (ExecutionStateTransport.toOuter user)
  set := fun user value =>
    {user with payload := {user.payload with payload :=
      {user.payload.payload with user :=
        {user.payload.payload.user with runtime :=
          {user.payload.payload.user.runtime with environment := value}}}}} }

/-- The ExternStatic registry is another field of the same machine runtime,
and must be updated through that field so GC and symbol resolution observe
the exact state changed by late initialization. -/
def externStaticLens : EvalHostRuntimeConstruction.ExternStaticLens
    (InnerControl Os R P H D O Aff B Host) := {
  get := fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user)
  set := fun user value =>
    {user with payload := {user.payload with payload :=
      {user.payload.payload with user :=
        {user.payload.payload.user with runtime :=
          {user.payload.payload.user.runtime with externStatics := value}}}}} }

@[simp] theorem environmentLens_get_set
    (user : PointerMachine.User (InnerControl Os R P H D O Aff B Host))
    (value : EnvVars.State (Option Provenance) Os) :
    environmentLens.get (environmentLens.set user value) = value := by rfl

@[simp] theorem environmentLens_set_get
    (user : PointerMachine.User (InnerControl Os R P H D O Aff B Host)) :
    environmentLens.set user (environmentLens.get user) = user := by rfl

/-- Carry host-environment operations built on the inner canonical pointer
machine into late-init's outer thread-storage view. This is only the lossless
state reassociation; all memory, roots and environment updates remain in the
same machine. -/
def outerEnvironmentHooks
    (hooks : EnvVars.Hooks (Option Provenance) Os
      (InnerState Os R P H D O Aff B Host)) :
    EnvVars.Hooks (Option Provenance) Os (State Os R P H D O Aff B Host) := {
  family := hooks.family
  get := ExecutionStateTransport.action hooks.get
  put := fun value => ExecutionStateTransport.action (hooks.put value)
  encodeUnix := fun value => ExecutionStateTransport.action (hooks.encodeUnix value)
  decodeUnix := fun value => ExecutionStateTransport.action (hooks.decodeUnix value)
  emptyOs := hooks.emptyOs
  concatOs := hooks.concatOs
  asciiOs := hooks.asciiOs
  isEmpty := hooks.isEmpty
  containsEquals := hooks.containsEquals
  nullPointer := hooks.nullPointer
  isNull := fun pointer => ExecutionStateTransport.action (hooks.isNull pointer)
  readCString := fun pointer => ExecutionStateTransport.action (hooks.readCString pointer)
  allocCString := fun bytes kind => ExecutionStateTransport.action (hooks.allocCString bytes kind)
  allocPointerCell := fun kind => ExecutionStateTransport.action (hooks.allocPointerCell kind)
  allocPointerArray := fun count kind => ExecutionStateTransport.action (hooks.allocPointerArray count kind)
  projectPointerElement := fun pointer count index =>
    ExecutionStateTransport.action (hooks.projectPointerElement pointer count index)
  readPointer := fun pointer => ExecutionStateTransport.action (hooks.readPointer pointer)
  writePointer := fun pointer value =>
    ExecutionStateTransport.action (hooks.writePointer pointer value)
  offset := fun pointer amount => ExecutionStateTransport.action (hooks.offset pointer amount)
  deallocate := fun pointer kind => ExecutionStateTransport.action (hooks.deallocate pointer kind)
  invalidArgument := ExecutionStateTransport.action hooks.invalidArgument
  readWideString := fun pointer => ExecutionStateTransport.action (hooks.readWideString pointer)
  writeWideString := fun value pointer capacity =>
    ExecutionStateTransport.action (hooks.writeWideString value pointer capacity)
  allocWideString := fun value kind => ExecutionStateTransport.action (hooks.allocWideString value kind)
  envVarNotFound := ExecutionStateTransport.action hooks.envVarNotFound }

/-- Close the host constructor's source-shaped environment effects over the
actual World environment root, then transport those effects losslessly into
late-init's outer state. Only host OsStr conversions and OS error effects are
provided by the embedding. -/
def environmentFromSource [DecidableEq MiriMemoryKind]
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (InnerControl Os R P H D O Aff B Host))
    (family : ForeignItems.Family)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D O Aff B Host) C P) :
    EnvVars.Hooks (Option Provenance) Os (State Os R P H D O Aff B Host) :=
  outerEnvironmentHooks (EvalHostRuntimeConstruction.envVarsFromSource
    host hostEffects environmentLens family memory)

private def environmentFamilyFromCompiler
    (facts : CompilerExternStatic.TargetFacts) : ForeignItems.Family :=
  if facts.os == "windows" || facts.families.contains "windows" then .windows
  else if facts.families.contains "unix" then .unix
  else .other

private def outerExternStaticHooks
    (hooks : ExternStatic.InitHooks
      (InnerState Os R P H D O Aff B Host)) :
    ExternStatic.InitHooks (State Os R P H D O Aff B Host) := {
  get := ExecutionStateTransport.action hooks.get
  put := fun value => ExecutionStateTransport.action (hooks.put value)
  unix := hooks.unix
  os := hooks.os
  gnu := hooks.gnu
  environ := ExecutionStateTransport.action hooks.environ
  allocateValue := fun kind => ExecutionStateTransport.action (hooks.allocateValue kind)
  allocatePointerCell := fun value => ExecutionStateTransport.action (hooks.allocatePointerCell value)
  isDynSym := fun name => ExecutionStateTransport.action (hooks.isDynSym name)
  functionPointer := fun name => ExecutionStateTransport.action (hooks.functionPointer name) }

/-- Build extern-static initialization from the canonical runtime memory,
environment root and function-pointer registry. `target` and `dynamicValue`
are the exact target/platform and `Other`-symbol encoding selected by the
embedding; all allocation, scalar writes, symbol checks and pointer lookup
come from source machines. -/
def externStaticsFromSource [DecidableEq MiriMemoryKind]
    (target : EvalHostRuntimeConstruction.ExternStaticTarget)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D O Aff B Host) C P)
    (functions : FunctionPointers.Hooks MiriMemoryKind
      (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) O)
    (dynamicValue : String → O)
    (u8Layout usizeLayout : LocalLayout) :
    ExternStatic.InitHooks (State Os R P H D O Aff B Host) :=
  outerExternStaticHooks (EvalHostRuntimeConstruction.externStaticsFromSource
    target environmentLens externStaticLens memory functions dynamicValue u8Layout usizeLayout)

/-- Exact source target adapters. TLS uses the compiler OS enum and cfg target
family set; constructors use rustc's `Target.binary_format`. The actual source
factory never accepts these policy values from an embedding. -/
private def tlsPlatformFromCompiler (facts : CompilerExternStatic.TargetFacts) : TlsPlatform :=
  { unix := facts.families.contains "unix"
    os := match facts.os with
      | "linux" => .linux
      | "macos" => .macos
      | "windows" => .windows
      | os => .other os }

private def constructorFormatFromCompiler
    (facts : CompilerExternStatic.TargetFacts) : ConstructorBinaryFormat :=
  match facts.binaryFormat with
  | "coff" => .coff
  | "mach-o" => .machO
  | "elf" => .elf
  | "wasm" => .wasm
  | format => .other format

private def outerFunctions
    (hooks : FunctionPointers.Hooks MiriMemoryKind
      (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) O) :
    FunctionPointers.Hooks MiriMemoryKind
      (EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B Host) O := {
  registry := fun user => hooks.registry (ExecutionStateTransport.toInner user)
  putRegistry := fun user value => ExecutionStateTransport.toOuter
    (hooks.putRegistry (ExecutionStateTransport.toInner user) value)
  crossCrateInlineAlways := hooks.crossCrateInlineAlways
  inlineNever := fun callee => ExecutionStateTransport.action (hooks.inlineNever callee)
  chooseSalt := ExecutionStateTransport.action hooks.chooseSalt
  ptrGetAlloc := fun pointer => ExecutionStateTransport.action (hooks.ptrGetAlloc pointer)
  adjustRootPointer := fun id tag => ExecutionStateTransport.action (hooks.adjustRootPointer id tag)
  importedFunction := fun id => ExecutionStateTransport.action (hooks.importedFunction id) }

/-- Reassociate the vtable adapter from the fixed execution view to the outer
late-init view. Registries and memory queries still address the same canonical
world and allocation memory. -/
def vtableRuntimeFromExecution
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost) :
    VTableMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (User Os R P H D O Aff B Host)) O := Id.run do
  let inner := EvalCompilerMachine.vtables prepared.compiler prepared.image execution.functions
  return {
    functions := outerFunctions inner.functions
    registry := fun user => inner.registry (ExecutionStateTransport.toInner user)
    putRegistry := fun user value => ExecutionStateTransport.toOuter
      (inner.putRegistry (ExecutionStateTransport.toInner user) value)
    target := inner.target
    importedVTable := fun id => ExecutionStateTransport.action (inner.importedVTable id) }

/-- Run source late-init and a finite scheduler prefix using compiler-derived
startup facts, argument layouts, and exact Windows constants. `configs choice`
is the same fixed execution configuration used by Main/TLS construction and
argv allocation; scheduled choices continue through the supplied config
function and the fixed `EvalExecutable.loop` core step. -/
def startFromCompilerExecutionPrefix [DecidableEq Os]
    (prepared : EvalPreparation.Prepared)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (deallocationError : MemoryLifecycleError → StepError)
    (deallocate : Pointer (Option Provenance) → Option (Size × Align) →
      MemoryKind MiriMemoryKind → MachineHooks.M MiriMemoryKind
        (EvalEntryMachine.InnerUser Os R P H D O Aff B Host) Unit)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (platform : TlsPlatform) (format : ConstructorBinaryFormat)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind
      (EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B Host)
      (Pointer Provenance))
    (environment : EnvVars.Hooks (Option Provenance) Os (State Os R P H D O Aff B Host))
    (externStatics : ExternStatic.InitHooks (State Os R P H D O Aff B Host))
    (configuration : EvalBootstrap.Configuration Os)
    (base : RunLoopHooks (State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (User Os R P H D O Aff B Host))
    (stop : State Os R P H D O Aff B Host → Bool)
    (choices : List C) (initial : State Os R P H D O Aff B Host) :
    StepResult (State Os R P H D O Aff B Host) Unit := Id.run do
  let configuration ← match CompilerMain.sourceCompilerEntry prepared.compiler.main with
    | .ok (some (entry,entryType)) => pure {configuration with entry,entryType}
    | .ok none => pure configuration
    | .error reason => return (initial,.error (.unsupported s!"compiler main entry metadata: {reason}"))
  let execution := configs choice
  let compiler := prepared.compiler
  match EvalStartupRuntimeConstruction.prepare compiler with
  | .error reason => return (initial,.error (.unsupported reason))
  | .ok startupFacts =>
    match EvalStartupRuntimeConstruction.argumentsFromExecution compiler execution startupFacts with
      | .error reason => return (initial,.error (.unsupported reason))
      | .ok arguments =>
        return EvalRuntimeConstruction.startFromExecutionPrefix compiler execution configs limits
          deallocationError deallocate choice prepared.layouts spans platform format externStatic
          (EvalStartupWindows.evalWindows compiler) arguments environment externStatics
          EvalEntrySymbols.access prepared.image (vtableRuntimeFromExecution prepared execution)
          configuration base scheduler stop choices initial

/-- Fully source-wired startup entrypoint. The execution Config selected by
`configs choice` supplies the function-pointer registry to extern-static
initialization; the same choice/config closure drives Main/TLS and every MIR
step. Environment and weak-symbol storage operate on the canonical runtime
roots through the source host constructor. -/
def startFromSourceExecutionPrefix [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (InnerControl Os R P H D O Aff B Host))
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D O Aff B Host) C P)
    (dynamicValue : String → O)
    (u8Layout usizeLayout : LocalLayout)
    (configuration : EvalBootstrap.Configuration Os)
    (base : RunLoopHooks (State Os R P H D O Aff B Host) C MainMachine.Callback)
    (scheduler : C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (User Os R P H D O Aff B Host))
    (stop : State Os R P H D O Aff B Host → Bool)
    (choices : List C) (initial : State Os R P H D O Aff B Host) :
    StepResult (State Os R P H D O Aff B Host) Unit := Id.run do
  let execution := configs choice
  let externStatic : DefId → MachineHooks.M MiriMemoryKind
      (EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B Host) (Pointer Provenance) :=
    fun definition => ExecutionStateTransport.action do
      let symbols ← match prepared.compiler.foreignSymbols with
        | .ok symbols => pure symbols
        | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
      let checkSymbolClash := fun symbol => do
        match CompilerForeignSymbols.checkSymbolClash symbols symbol with
        | .ok () => pure ()
        | .error error => throw error
      CompilerExternStatic.resolve prepared.compiler.externStatics prepared.image
        checkSymbolClash execution.functions
        (fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user)) definition
  let targetFacts := prepared.compiler.externStatics.targetFacts
  let target ← match targetFacts with
    | .ok facts => pure (EvalHostRuntimeConstruction.ExternStaticTarget.fromCompiler facts)
    | .error reason => return (initial,.error (.unsupported s!"compiler target facts unavailable: {reason}"))
  let .ok exactTargetFacts := targetFacts
    | return (initial,.error (.unsupported "compiler target facts unavailable"))
  let family := environmentFamilyFromCompiler exactTargetFacts
  let environment := environmentFromSource host hostEffects family memory
  let platform := tlsPlatformFromCompiler exactTargetFacts
  let format := constructorFormatFromCompiler exactTargetFacts
  let externStatics := externStaticsFromSource target memory execution.functions
    dynamicValue u8Layout usizeLayout
  return startFromCompilerExecutionPrefix prepared configs limits
    AllocationMachine.deallocationError memory.deallocate
    choice spans platform format externStatic environment externStatics configuration
    base scheduler stop choices initial

end Miri.Input.EvalStartupAssembly
