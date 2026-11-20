import Lean.Util.Profile
import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalRunConstruction
import Miri.Input.EvalBootstrap
import Miri.Input.EvalStartupRuntimeConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.InitialMachine
import Miri.Input.EvalConfigurationCore
import Miri.Input.EvalChronoTimeSource
import Miri.Input.EvalMiriConnectedSourceConstruction
import Miri.Input.EvalSyncPayload
import Miri.Interpreter.ExecutionStateTransport
import Miri.Input.MachineConstruction
import Miri.Interpreter.CpuAffinity

/-! Source-owned process entry construction.  This module is kept
separate from EvalStartupAssembly because the source Core imports the Unix
foreign chain that itself depends on the legacy assembly module. -/
namespace Miri.Input.EvalSourceRunConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- Evidence that every choice requested by the run loop is the same choice
used to assemble its initial source package. This is an opt-in optimization:
generic runners without this evidence continue to construct per-choice source
packages. -/
structure StableChoice {C : Type} (choice : C) : Type where
  same : ∀ selected : C, selected = choice

abbrev W := EvalEntryMachine.W
abbrev State Os R P H D O Aff B Host := EvalRuntimeConstruction.EntryState Os R P H D O Aff B Host
abbrev SourceHost Poll Instant System H D O Native Profiler :=
  HostRuntime.Storage Poll Instant System H D O Native Profiler
abbrev SourceState Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalRuntimeConstruction.EntryState Os R P H D O Aff B
    (SourceHost Poll Instant System H D O Native Profiler)

/-- Create the canonical initial EvalWorld for the source runner from
the selected initialization configuration, imported memory, runtime type
arrays, choice tape and actual host storage. The caller supplies the exact
source configuration; this constructor applies it once, rather than requiring
an arbitrary preassembled machine State. -/
def initialStateFromSourceConfiguration
    {Os R P H D O Aff B Poll Instant System Native Profiler : Type}
    (configuration : InitialMachine.Configuration Aff B)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (types : RuntimeArrayTypes.World)
    (choices : ExecutionChoices.Tape)
    (host : SourceHost Poll Instant System H D O Native Profiler) :
    Except StepError
      (SourceState Os R P H D O Aff B Poll Instant System Native Profiler) :=
  InitialMachine.create configuration memory types choices host

/-- Compute argv hooks from the same fixed source execution config that will
run Main and the MIR body. Compiler facts remain demand-local errors. -/
def sourceArguments {Os R P H D O Aff B Host C ClockHost : Type}
    (compiler : CompilerProviders.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (facts : EvalStartupRuntimeConstruction.StartupFacts) :
    Except StepError (ULift.{1} (EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))) P C)) := do
  match EvalStartupRuntimeConstruction.argumentsFromExecution compiler execution facts with
  | .error reason => throw (.unsupported reason)
  | .ok hooks => pure ⟨hooks⟩

private def sourceTlsPlatform (facts : CompilerExternStatic.TargetFacts) : TlsPlatform :=
  { unix := facts.families.contains "unix"
    os := match facts.os with
      | "linux" => .linux
      | "macos" => .macos
      | "windows" => .windows
      | os => .other os }

private def sourceConstructorFormat
    (facts : CompilerExternStatic.TargetFacts) : ConstructorBinaryFormat :=
  match facts.binaryFormat with
  | "coff" => .coff
  | "mach-o" => .machO
  | "elf" => .elf
  | "wasm" => .wasm
  | format => .other format

private def sourceForeignSymbols (compiler : CompilerProviders.Prepared) :
    Except StepError CompilerForeignSymbols.Prepared :=
  (compiler.foreignSymbols).mapError
    (fun reason => .unsupported s!"compiler foreign-symbol query: {reason}")

private def sourceTargetFacts (compiler : CompilerProviders.Prepared) :
    Except StepError (ULift.{1} CompilerExternStatic.TargetFacts) :=
  match compiler.externStatics.targetFacts with
  | .ok facts => .ok ⟨facts⟩
  | .error reason => .error (.unsupported s!"compiler target facts unavailable: {reason}")

private def sourceLayouts (compiler : CompilerProviders.Prepared) :
    Except StepError (ULift.{1} EvalEntryMachine.Layouts) :=
  match EvalEntryMachine.layouts compiler with
  | .ok layouts => .ok ⟨layouts⟩
  | .error reason => .error (.unsupported reason)

private def sourceStartupFacts (compiler : CompilerProviders.Prepared) :
    Except StepError (ULift.{1} EvalStartupRuntimeConstruction.StartupFacts) :=
  match EvalStartupRuntimeConstruction.prepare compiler with
  | .ok facts => .ok ⟨facts⟩
  | .error reason => .error (.unsupported reason)

private def startupPrimitiveLayout
    (compiler : CompilerProviders.Prepared) (name : String) :
    Except StepError (ULift.{1} LocalLayout) := do
  match compiler.primitiveLayout name with
  | .ok layout => pure ⟨layout⟩
  | .error reason => throw (.unsupported s!"compiler {name} layout for startup: {reason}")

private def sourceMainConfiguration {Os : Type}
    (compiler : CompilerProviders.Prepared)
    (configuration : EvalBootstrap.Configuration Os) :
    Except StepError (ULift.{1} (EvalBootstrap.Configuration Os)) := do
  match CompilerMain.sourceCompilerEntry compiler.main with
  | .ok (some (entry,entryType)) =>
      pure ⟨{configuration with entry,entryType}⟩
  | .ok none => throw (.unsupported "compiler has no selected Rust main entry")
  | .error reason => throw (.unsupported s!"compiler main entry metadata: {reason}")

def sourceClockToOuter
    {Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error : Type}
    (clock : Clock.HostHooks Instant System
      (EvalUnixSourceConstruction.State Os R P H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error)) :
    Clock.HostHooks Instant System
      (EvalRuntimeConstruction.EntryState Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (SourceHost Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) := {
  monotonicNow := ExecutionStateTransport.action clock.monotonicNow
  systemNow := ExecutionStateTransport.action clock.systemNow
  unixEpoch := clock.unixEpoch
  checkedAddMonotonic := fun instant duration =>
    ExecutionStateTransport.action (clock.checkedAddMonotonic instant duration)
  checkedAddSystem := fun instant duration =>
    ExecutionStateTransport.action (clock.checkedAddSystem instant duration)
  durationSince := fun later earlier =>
    ExecutionStateTransport.action (clock.durationSince later earlier)
  sleep := fun duration => ExecutionStateTransport.action (clock.sleep duration) }

def sourceDurationSinceToOuter
    {Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error : Type}
    (operation : System → System →
      Clock.M (EvalUnixSourceConstruction.State Os R EvalSyncPayload.Payload H D Aff B
        Poll Instant System Native Profiler Raw Listener TcpStream Error) (Option Clock.Duration)) :
    System → System → Clock.M (EvalRuntimeConstruction.EntryState Os R EvalSyncPayload.Payload H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (SourceHost Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler))
      (Option Clock.Duration) := fun later earlier =>
  ExecutionStateTransport.action
    (K := Miri.Memory.MiriMemoryKind)
    (U := EvalSocketStorage.World Os R EvalSyncPayload.Payload H D Aff B Poll Instant System
      Native Profiler Raw Listener TcpStream Error)
    (operation later earlier)

def sourceChoiceAccess
    {Os R H D O Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error : Type} :
    ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (EvalCallbackMachine.ThreadUser Os R EvalSyncPayload.Payload H D O Aff B
          Poll Instant System Native Profiler)) := {
  get := fun state => EvalCoreMachine.tape.get (ExecutionStateTransport.inward state)
  put := fun state tape => ExecutionStateTransport.outward
    (EvalCoreMachine.tape.put (ExecutionStateTransport.inward state) tape) }

/-- Construct Main/TLS from the exact source Core and compiler target facts.
Extern-static lookup is closed over the same function registry and runtime
root used by that Core; no complete Main hook record is accepted. -/
def sourceMainFromExecution [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C ClockHost : Type}
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B Host) C P)
    (initial : EvalRuntimeConstruction.EntryState Os R P H D O Aff B Host) :
    Except StepError (MainMachine.Hooks (EvalExecutable.U Os R P H D O Aff B Host)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P) := do
  let targetFacts ← sourceTargetFacts prepared.compiler
  let targetFacts := targetFacts.down
  let externStatic : DefId → MachineHooks.M MiriMemoryKind
      (EvalRuntimeConstruction.EntryOuter Os R P H D O Aff B Host) (Pointer Provenance) :=
    fun definition => ExecutionStateTransport.action do
      let symbols ← match sourceForeignSymbols prepared.compiler with
        | .ok symbols => pure symbols
        | .error error => throw error
      let checkSymbolClash := fun symbol => do
        match CompilerForeignSymbols.checkSymbolClash symbols symbol with
        | .ok () => pure ()
        | .error error => throw error
      CompilerExternStatic.resolve prepared.compiler.externStatics prepared.image
        checkSymbolClash execution.functions
        (fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user))
        definition
  let layout ← sourceLayouts prepared.compiler
  let layout := layout.down
  EvalEntryMachine.mainFromExecution prepared.compiler execution limits
    AllocationMachine.deallocationError memory.deallocate choice layout spans
    (sourceTlsPlatform targetFacts) (sourceConstructorFormat targetFacts) externStatic
    (EvalStartupWindows.evalWindows prepared.compiler) initial

/-- Assemble the exact late-init hooks from already source-constructed argv
and Main components plus canonical environment/static/vtable adapters. The
argv capability is unlifted only at this typed boundary; no hooks dictionary
is accepted as a whole. -/
def assembleBootstrapHooks
    {Os R P H D O Aff B Host C ClockHost : Type}
    (arguments : ULift.{1} (EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))) P C))
    (main : MainMachine.Hooks (EvalExecutable.U Os R P H D O Aff B Host)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (environment : EnvVars.Hooks (Option Provenance) Os
      (MainMachine.State (EvalExecutable.U Os R P H D O Aff B Host)))
    (externStatics : ExternStatic.InitHooks
      (MainMachine.State (EvalExecutable.U Os R P H D O Aff B Host)))
    (compiler : CompilerProviders.Prepared)
    (image : AllocationImage.Imported)
    (vtableRuntime : VTableMachine.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host)) O)
    (configuration : EvalBootstrap.Configuration Os) :
    EvalBootstrap.Configuration Os × EvalBootstrap.Hooks
      (EvalExecutable.U Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff P
      (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))) Os :=
  let hooks := EvalRuntimeConstruction.bootstrapHooks arguments.down main environment
    externStatics compiler
    (EvalEntrySymbols.access (Os := Os) (R := R) (P := P) (H := H)
      (D := D) (O := O) (Aff := Aff) (B := B) (Host := Host)) image vtableRuntime
  (configuration,hooks)

/-- Build source startup hooks from one final execution config. This is the
Rust entry path: the selected compiler Main is mandatory; argv,
extern-static initialization, environment roots, Main/TLS, and vtable metadata
all derive from the same prepared compiler and execution. -/
private def bootstrapFromSourceExecutionWithEncoding [DecidableEq MiriMemoryKind]
    {Os R P H D O Aff B Host C ClockHost : Type}
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B Host))
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B Host) C P)
    (dynamicValue : String → O)
    (u8Layout usizeLayout : LocalLayout)
    (configuration : EvalBootstrap.Configuration Os)
    (initial : EvalRuntimeConstruction.EntryState Os R P H D O Aff B Host) :
    Except StepError
      (ULift.{1} (EvalBootstrap.Configuration Os × EvalBootstrap.Hooks
        (EvalExecutable.U Os R P H D O Aff B Host) C O ABI.ExternAbi
        (FnAbi TyId) (ArgAbi TyId) Aff P
        (ValidityMachine.Control (ThreadStacks.Storage (W Os R P H D O Aff B Host))) Os)) := do
  let targetFactLift ← sourceTargetFacts prepared.compiler
  let targetFacts := targetFactLift.down
  let configurationLift ← sourceMainConfiguration prepared.compiler configuration
  let configuration := configurationLift.down
  let factsLift ← sourceStartupFacts prepared.compiler
  let argumentsLift ← sourceArguments prepared.compiler execution factsLift.down
  let main ← sourceMainFromExecution prepared execution limits choice spans memory initial
  let family := if targetFacts.os == "windows" || targetFacts.families.contains "windows" then .windows
    else if targetFacts.families.contains "unix" then .unix else .other
  let environment := EvalStartupAssembly.environmentFromSource host hostEffects family memory
  let target := EvalHostRuntimeConstruction.ExternStaticTarget.fromCompiler targetFacts
  let externStatics := EvalStartupAssembly.externStaticsFromSource target memory
    execution.functions dynamicValue u8Layout usizeLayout
  let bootstrap := assembleBootstrapHooks (ClockHost := ClockHost)
    argumentsLift main environment externStatics
    prepared.compiler prepared.image (EvalStartupAssembly.vtableRuntimeFromExecution prepared execution)
    configuration
  pure ⟨bootstrap⟩

/-- Canonical Unix bootstrap. Dynamic symbols use the source `Other` dynamic
symbol constructor, and the scalar layouts come from the same compiler runtime
facts as the execution Core. No caller-provided encoding or target-sized
layout can diverge from the selected export. -/
def bootstrapFromSourceExecution [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error : Type}
    {Os R P H D Aff B Poll Instant System Native Profiler C : Type}
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
      (SourceHost Poll Instant System H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)
      C Instant)
    (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalStartupAssembly.InnerControl Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (SourceHost Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)))
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
        (SourceHost Poll Instant System H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) C P)
    (configuration : EvalBootstrap.Configuration Os)
    (initial : EvalRuntimeConstruction.EntryState Os R P H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
      (SourceHost Poll Instant System H D
        (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)) :
    Except StepError
      (ULift.{1} (EvalBootstrap.Configuration Os × EvalBootstrap.Hooks
        (EvalExecutable.U Os R P H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
          (SourceHost Poll Instant System H D
            (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler))
        C (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
        ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P
        (ValidityMachine.Control (ThreadStacks.Storage
          (W Os R P H D
            (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Aff B
            (SourceHost Poll Instant System H D
              (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)))) Os)) := do
  let u8LayoutLift ← startupPrimitiveLayout prepared.compiler "u8"
  let usizeLayoutLift ← startupPrimitiveLayout prepared.compiler "usize"
  let u8Layout := u8LayoutLift.down
  let usizeLayout := usizeLayoutLift.down
  bootstrapFromSourceExecutionWithEncoding (Os := Os) (R := R) (P := P) (H := H)
    (D := D) (O := EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
    (Aff := Aff) (B := B)
    (Host := SourceHost Poll Instant System H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)
    (C := C) (ClockHost := Instant)
    prepared execution limits choice spans host hostEffects memory
    (fun name => SourceOther.Value.dynamicSymbol name) u8Layout usizeLayout configuration initial

/-- Internal composition seam for the final source constructor. It performs
late initialization on the supplied final Core's bootstrap hooks, then runs
the source local scheduler with fallible choice-specific Core construction.
The callback dictionary is intentionally an internal input here; the public
source constructor must obtain it from the typed callback factory rather than
expose a caller-selected `EvalCallbackMachine.Hooks`. -/
private def initializeAndRunSource
    {Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter
      Raw Listener TcpStream Host AddrIter : Type}
    [DecidableEq Os]
    (runtimeConfiguration : HostRuntime.Configuration)
    (bootstrap : EvalBootstrap.Configuration Os × EvalBootstrap.Hooks
      (EvalExecutable.U Os R P H D O Aff B (SourceHost Poll Instant System H D O Native Profiler))
      C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff P
      (ValidityMachine.Control (ThreadStacks.Storage
        (W Os R P H D O Aff B (SourceHost Poll Instant System H D O Native Profiler)))) Os)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B
      Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B
      (SourceHost Poll Instant System H D O Native Profiler) C Instant))
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (EvalCallbackMachine.ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (EvalRunConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System →
      EvalRunConstruction.M Os R P H D O Aff B Poll Instant System Native Profiler
        (Option Clock.Duration))
    (process : EvalRunConstruction.ProcessEffects
      (EvalRunConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (initialChoice : C) (iterationFuel : Nat) (choices : List C)
    (initial : SourceState Os R P H D O Aff B Poll Instant System Native Profiler) :
    Except
      (SourceState Os R P H D O Aff B Poll Instant System Native Profiler × StepError)
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R P H D O Aff B Poll Instant System Native Profiler)) := Id.run do
  if runtimeConfiguration.communicate != bootstrap.1.communicate then
    return .error (initial,.invalidProgram
      "startup and HostRuntime communication settings differ")
  let loop := EvalRunConstruction.hooksFromSource runtimeConfiguration callbacks
    bootstrap.2.main configs limits choiceAccess clock systemDurationSince process
  let (state,result) := MachineHooks.run
    (EvalBootstrap.createContextWithBytes bootstrap.2 bootstrap.1 initialChoice) initial
  match result with
  | .error error => return .error (state,error)
  | .ok _ => return .ok (EvalRunConstruction.runUntilTerminal loop
      iterationFuel choices state)

/-- Internal end-to-end entry over one already selected source Core.
The upcoming source factory supplies that Core and its canonical startup
memory/callback inputs together; this wrapper does not create a provisional
configuration or substitute a caller-built RunLoop. -/
private def startAndRunSourceExecution
    {Os R P H D O Aff B Poll Instant System Native Profiler C : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    (prepared : EvalPreparation.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B
      (SourceHost Poll Instant System H D O Native Profiler) C Instant)
    (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B
        (SourceHost Poll Instant System H D O Native Profiler)))
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (EvalStartupAssembly.InnerControl Os R P H D O Aff B
        (SourceHost Poll Instant System H D O Native Profiler)) C P)
    (dynamicValue : String → O)
    (u8Layout usizeLayout : LocalLayout)
    (configuration : EvalBootstrap.Configuration Os)
    (initial : SourceState Os R P H D O Aff B Poll Instant System Native Profiler)
    (runtimeConfiguration : HostRuntime.Configuration)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B
      Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B
      (SourceHost Poll Instant System H D O Native Profiler) C Instant))
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (EvalCallbackMachine.ThreadUser Os R P H D O Aff B
          Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (EvalRunConstruction.State Os R P H D O Aff B
        Poll Instant System Native Profiler))
    (systemDurationSince : System → System →
      EvalRunConstruction.M Os R P H D O Aff B
        Poll Instant System Native Profiler (Option Clock.Duration))
    (process : EvalRunConstruction.ProcessEffects
      (EvalRunConstruction.State Os R P H D O Aff B
        Poll Instant System Native Profiler))
    (iterationFuel : Nat) (choices : List C) :
    Except
      (SourceState Os R P H D O Aff B Poll Instant System Native Profiler × StepError)
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R P H D O Aff B
          Poll Instant System Native Profiler)) :=
  match bootstrapFromSourceExecutionWithEncoding (Os := Os) (R := R) (P := P) (H := H) (D := D)
      (O := O) (Aff := Aff) (B := B)
      (Host := SourceHost Poll Instant System H D O Native Profiler) (C := C)
      (ClockHost := Instant) prepared execution limits choice spans host
      hostEffects memory dynamicValue u8Layout usizeLayout configuration initial with
  | .error error => .error (initial,error)
  | .ok bootstrap => initializeAndRunSource runtimeConfiguration bootstrap.down callbacks configs
      limits choiceAccess clock systemDurationSince process choice iterationFuel choices initial

/-! Continue from the exact machine state produced by the source constructor.
No host, descriptor or ownership store is rebuilt here. -/
def runFromInitialProfiled
    {Os R H D B Poll Instant System Native Profiler C : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (profile : Lean.Options)
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
      Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Miri.MIR.Place C
      Instant EvalSyncObjectAccess.Payload AddrIter)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C)
    (initial : EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      Poll Instant System Native Profiler)
    (stableChoice : Option (StableChoice choice) := none) :
    Except StepError
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          Poll Instant System Native Profiler)) := Id.run do
  let compiler := prepared.compiler
  if initialConfiguration.geometry.pageSize != sourceLeaves.foreignSource.geometry.pageSize ||
      initialConfiguration.geometry.stackAddress != sourceLeaves.foreignSource.geometry.stackAddress ||
      initialConfiguration.geometry.stackSize != sourceLeaves.foreignSource.geometry.stackSize ||
      initialConfiguration.alignment != sourceLeaves.foreignSource.alignment ||
      initialConfiguration.validation != options.place.validation then
    return .ok (EvalRunConstruction.classifyError initial
      (.invalidProgram "initial machine geometry/alignment/validation differs from source Core inputs"))
  let packaged := EvalConfigurationCore.makeFromSourcePackage compiler image bytes options sourceLeaves choice capacity
  match packaged with
  | .error error => return .ok (EvalRunConstruction.classifyError initial error)
  | .ok package => do
    let execution := package.execution
    let context := package.context
    let some buildAssembly := context.sourceAssembly |
      return .ok (EvalRunConstruction.classifyError initial
        (.unsupported "source Core did not provide its same-world startup assembly"))
    let (afterAssembly,assemblyResult) := MachineHooks.run
      (ExecutionStateTransport.action (buildAssembly ())) initial
    let assembly ← match assemblyResult with
      | .ok assembly => pure assembly
      | .error error => return .ok (EvalRunConstruction.classifyError afterAssembly error)
    let some _ := assembly.environment |
      return .ok (EvalRunConstruction.classifyError afterAssembly
        (.unsupported "source Core startup assembly lacks canonical environment hooks"))
    let some memory := assembly.memory |
      return .ok (EvalRunConstruction.classifyError afterAssembly
        (.unsupported "source Core startup assembly lacks canonical environment memory"))
    if sourceLeaves.hostConfiguration.communicate != bootstrapConfiguration.communicate then
      return .ok (EvalRunConstruction.classifyError afterAssembly
        (.invalidProgram "startup and HostRuntime communication settings differ"))
    match bootstrapFromSourceExecution
        (Os := Os) (R := R) (P := EvalSyncObjectAccess.Payload) (H := H) (D := D)
        (Aff := CpuAffinity.Mask) (B := B) (Poll := Poll) (Instant := Instant) (System := System)
        (Native := Native) (Profiler := Profiler) (C := C)
        prepared execution limits choice
        sourceLeaves.spans sourceLeaves.foreignSource.host.os
        sourceLeaves.foreignSource.host.environment memory bootstrapConfiguration afterAssembly with
    | .error error => return .ok (EvalRunConstruction.classifyError afterAssembly error)
    | .ok liftedBootstrap => do
        let bootstrap := liftedBootstrap.down
        let hostProcess := sourceLeaves.foreignSource.host.process
        let process : EvalRunConstruction.ProcessEffects
            (EvalRunConstruction.State Os R EvalSyncObjectAccess.Payload H D
              (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
              Poll Instant System Native Profiler) := {
          interrupted := fun state => hostProcess.interrupted (ExecutionStateTransport.inward state)
          handleAbnormalTermination := fun state => ExecutionStateTransport.outward
            (hostProcess.handleAbnormalTermination (ExecutionStateTransport.inward state)) }
        let clock := sourceClockToOuter sourceLeaves.foreignSource.host.clock
        let durationSince := sourceDurationSinceToOuter
          sourceLeaves.foreignSource.host.systemDurationSince
        let (afterInit,initResult) := MachineHooks.run
          (EvalBootstrap.createContextWithBytesProfiled (Os := Os) profile bootstrap.2 bootstrap.1 choice) afterAssembly
        match initResult with
        | .error error => return .ok (EvalRunConstruction.classifyError afterInit error)
        | .ok _ =>
            let choiceAccess := sourceChoiceAccess (Os := Os) (R := R) (H := H) (D := D)
              (O := EvalUnixSourceConstruction.Other Raw Listener TcpStream Error)
              (Aff := CpuAffinity.Mask) (B := B) (Poll := Poll) (Instant := Instant) (System := System)
              (Native := Native) (Profiler := Profiler)
              (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream) (Error := Error)
            match package.callbackBuilder assembly execution bootstrap.2.main afterInit with
            | .error (error,afterCallbacks) =>
                return .ok (EvalRunConstruction.classifyError afterCallbacks error)
            | .ok (callbackProduct,afterCallbacks) =>
                let callbacks := callbackProduct.hooks
                let bindPackage := fun (selected : C) selectedPackage => do
                    let rebound := selectedPackage.rebindCallbacks callbackProduct selectedPackage.execution
                    let some foreign := rebound.calls.dispatch.foreign |
                      throw (.unsupported "selected source Core lacks callback-rebound foreign hooks")
                    let connectedForeign := do
                      let foreignHooks ← foreign
                      let miriOptions := {options with panicUnwinds := selectedPackage.panicUnwinds}
                      match EvalMiriConnectedSourceConstruction.bind compiler image miriOptions
                          sourceLeaves selectedPackage.context
                          callbackProduct.main.termination.tls.thread foreignHooks with
                      | .ok connected => pure connected
                      | .error error => throw error
                    let dispatch := {rebound.calls.dispatch with foreign := some connectedForeign}
                    let calls := {rebound.calls with dispatch}
                    pure {rebound with calls}
                let configs : C → Except StepError (EvalExecutable.Core Os R EvalSyncObjectAccess.Payload H D
                    (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
                    (SourceHost Poll Instant System H D
                      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler) C Instant) :=
                  match stableChoice with
                  | some proof =>
                      let cachedConfig := bindPackage choice package
                      fun selected => do
                        let _sameChoice : selected = choice := proof.same selected
                        cachedConfig
                  | none => fun selected => do
                      let selectedPackage ← EvalConfigurationCore.makeFromSourcePackage compiler image
                        bytes options sourceLeaves selected capacity
                      bindPackage selected selectedPackage
                let loop := EvalRunConstruction.hooksFromSource
                  sourceLeaves.hostConfiguration callbacks bootstrap.2.main configs limits
                  choiceAccess clock durationSince process
                let loopReady := Lean.profileit "startup.bootstrap_ready" profile
                  (fun _ => afterCallbacks)
                return .ok (EvalRunConstruction.runUntilTerminalProfiled profile loop
                  iterationFuel outerChoices loopReady)

/-- Compatibility entry with the original positional API. Runtime profiling is
opt-in through `runFromInitialProfiled`; ordinary callers retain this exact
signature and delegate with profiler options disabled. -/
def runFromInitial
    {Os R H D B Poll Instant System Native Profiler C : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
      Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Miri.MIR.Place C
      Instant EvalSyncObjectAccess.Payload AddrIter)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C)
    (initial : EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
      Poll Instant System Native Profiler)
    (stableChoice : Option (StableChoice choice) := none) :
    Except StepError
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          Poll Instant System Native Profiler)) :=
  runFromInitialProfiled {} prepared image bytes options sourceLeaves choice initialConfiguration
    bootstrapConfiguration limits capacity iterationFuel outerChoices initial stableChoice

/-! Explicit lower entry for callers that already own a HostRuntime payload.
This keeps that contract available for existing embeddings while the normal
production entry below performs the pinned machine construction itself. -/
def runFromPreinitializedHost
    {Os R H D B Poll Instant System Native Profiler C : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
      Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Miri.MIR.Place C
      Instant EvalSyncObjectAccess.Payload AddrIter)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (runtimeTypes : RuntimeArrayTypes.World)
    (choiceTape : ExecutionChoices.Tape)
    (host : SourceHost Poll Instant System H D
      (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) Native Profiler)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C) :
    Except StepError
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          Poll Instant System Native Profiler)) := do
  let initial ← InitialMachine.create initialConfiguration initialMemory runtimeTypes choiceTape host
  runFromInitial prepared image bytes options sourceLeaves choice initialConfiguration
    bootstrapConfiguration limits capacity iterationFuel outerChoices initial

/-! Canonical normal process entry. Raw host lifecycle hooks and their exact
external state are threaded through MachineConstruction.create. The returned
guest state is the same state whose descriptor/ownership tables were created
there; startup and execution continue without reinitializing either table.
The result retains HostRuntime storage, including for resumable Pending states.
It does not implicitly dispose host resources after a terminal guest outcome;
embeddings may explicitly call HostRuntime.dispose once the retained state is
no longer needed. Constructor rollback still uses MachineConstruction's
protect path. -/
def runFromSourceProfiled
    {Os R H D B Poll Instant System Native Profiler C External : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (profile : Lean.Options)
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
      Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Miri.MIR.Place C
      Instant EvalSyncObjectAccess.Payload AddrIter)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (runtimeTypes : RuntimeArrayTypes.World)
    (choiceTape : ExecutionChoices.Tape)
    (hostRuntime : HostRuntime.Hooks External Poll Instant System Native Profiler)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C)
    (useBuiltinChronoTz : Bool := true)
    (stableChoice : Option (StableChoice choice) := none) :
    EStateM StepError External
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          Poll Instant System Native Profiler)) := do
  /- The production Unix source entry installs the pure pinned Chrono-TZ
  provider when the host seed has no explicit time provider. Passing false
  preserves the Core's demand-local no-Chrono fallback; an explicitly supplied
  provider always takes precedence. -/
  let sourceLeaves :=
    if useBuiltinChronoTz && sourceLeaves.foreignSource.host.time.isNone then
      {sourceLeaves with foreignSource :=
        EvalChronoTimeSource.installSourceInput sourceLeaves.foreignSource}
    else sourceLeaves
  let targetFacts ← match sourceTargetFacts prepared.compiler with
    | .ok facts => pure facts.down
    | .error error => throw error
  let startupFacts ← match sourceStartupFacts prepared.compiler with
    | .ok facts => pure facts.down
    | .error error => throw error
  let noCore ← match startupFacts.noCore with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler no_core query: {reason}")
  let cULong ← match CompilerPrimitiveFacts.cULongLayout prepared.compiler.runtime with
    | .ok layout => pure layout
    | .error reason => throw (.unsupported s!"compiler c_ulong layout: {reason}")
  let machineTarget : MachineConstruction.Target := {
    os := targetFacts.os
    noCore
    cpuCount := sourceLeaves.foreignSource.host.unixConfig.numCpus
    cUlongBytes := cULong.layout.size.bytes.toNat
    endian := prepared.compiler.runtime.target.base.endian }
  let initial ← MachineConstruction.create hostRuntime sourceLeaves.hostConfiguration machineTarget
    initialConfiguration initialMemory runtimeTypes choiceTape
  match runFromInitialProfiled profile prepared image bytes options sourceLeaves choice initialConfiguration
      bootstrapConfiguration limits capacity iterationFuel outerChoices initial
      stableChoice with
  | .ok result => pure result
  | .error error => throw error

/-- Compatibility entry with the original positional API. Profiling callers
use `runFromSourceProfiled`; ordinary callers delegate with profiling disabled. -/
def runFromSource
    {Os R H D B Poll Instant System Native Profiler C External : Type}
    [DecidableEq Os] [DecidableEq MiriMemoryKind]
    {Raw Listener TcpStream Error ErrorHost Meta Path AddrIter : Type}
    (prepared : EvalPreparation.Prepared)
    (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared)
    (options : EvalConfigurationCore.Options)
    (sourceLeaves : EvalConfigurationCore.SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
      Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost Meta Path Miri.MIR.Place C
      Instant EvalSyncObjectAccess.Payload AddrIter)
    (choice : C)
    (initialConfiguration : InitialMachine.Configuration CpuAffinity.Mask B)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (runtimeTypes : RuntimeArrayTypes.World)
    (choiceTape : ExecutionChoices.Tape)
    (hostRuntime : HostRuntime.Hooks External Poll Instant System Native Profiler)
    (bootstrapConfiguration : EvalBootstrap.Configuration Os)
    (limits : ExecutionMachine.Limits)
    (capacity iterationFuel : Nat)
    (outerChoices : List C)
    (useBuiltinChronoTz : Bool := true)
    (stableChoice : Option (StableChoice choice) := none) :
    EStateM StepError External
      (EvalRunConstruction.RunResult
        (EvalRunConstruction.State Os R EvalSyncPayload.Payload H D
          (EvalUnixSourceConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
          Poll Instant System Native Profiler)) :=
  runFromSourceProfiled {} prepared image bytes options sourceLeaves choice initialConfiguration
    initialMemory runtimeTypes choiceTape hostRuntime bootstrapConfiguration limits capacity
    iterationFuel outerChoices useBuiltinChronoTz stableChoice

end Miri.Input.EvalSourceRunConstruction
