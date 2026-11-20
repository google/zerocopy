import Miri.Interpreter.RaceMode
import Miri.Input.EvalWorld
import Miri.Concurrency.GlobalState

/-! Portable machine.rs::new initialization on canonical shared storage.
Compiler-imported memory, and runtime type identities
are supplied explicitly; host poll/native/profiler/clock initialization is not
silently replaced by this pure constructor. -/
namespace Miri.Input.InitialMachine
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter Miri.Concurrency

structure Geometry where
  pageSize : UInt64
  stackAddress : UInt64
  stackSize : UInt64

def geometry (pointerBits : Nat) (arch : String) (darwin : Bool) (overridePage : Option UInt64) :
    Except StepError Geometry := do
  let page := overridePage.getD (if arch == "wasm32" || arch == "wasm64" then 65536
    else if arch == "aarch64" && darwin then 16384 else 4096)
  let address := page.toNat * (if pointerBits < 32 then 1 else 32)
  let size := page.toNat * (if pointerBits < 32 then 4 else 16)
  if address >= 2^64 || size >= 2^64 then throw (.invalidProgram "initial stack geometry overflow")
  return ⟨page,UInt64.ofNat address,UInt64.ofNat size⟩

structure Configuration (Aff B : Type) where
  geometry : Geometry
  /-- Canonical compiler DUMMY_SP identity; table index zero is not reserved. -/
  dummySpan : Miri.MIR.SpanRef
  provenance : ProvenanceMode
  addressMode : AddressSpaceMode
  addressStop : UInt64
  addressReuse : AddressReuseConfig
  fixedScheduling : Bool
  trackOutdatedLoads : Bool
  weakMemory : Bool
  backend : RaceMode.Selection B
  trackedTags : Option (Array BorTag)
  /-- Explicit allocation identities selected for source tracking diagnostics.
  Runtime allocation identities must already have been resolved by the caller. -/
  trackedAllocations : Array AllocId := #[]
  validation : ValidityMachine.ValidationMode
  alignment : ValidityMachine.AlignmentCheck
  affinity : Option Aff
  muteOutput : Bool
  hostUsizeBits : Nat

/-- Source-owned empty caches/arenas are constructed here, not supplied as
arbitrary MIR operation hooks. Imported memory is retained exactly, and caller
must install imported function/vtable salt-zero reservations before execution. -/
def create (config : Configuration Aff B)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (types : RuntimeArrayTypes.World) (choices : ExecutionChoices.Tape) (host : Host) :
    Except StepError (EvalWorld.State Os R P H D O Aff B Host) := do
  let addresses ← (GlobalAddressState.new config.provenance config.addressMode
    config.geometry.stackAddress config.addressStop config.addressReuse).mapError
      (fun error => .invalidProgram s!"initial addresses: {reprStr error}")
  let descriptors ← Files.Table.init config.muteOutput config.hostUsizeBits
  let mut ownership : FileOwnership.Registry (Files.Description H D O) := {}
  for (_,reference) in descriptors.fds do ownership ← FileOwnership.register ownership reference
  let clocks ← match config.backend with
    | .none => pure none
    | .vclocks => pure (some (GlobalState.initial config.trackOutdatedLoads config.weakMemory))
  let borrow := config.trackedTags.map fun tags =>
    MachineHooks.BorrowState.mk (Miri.TreeBorrows.GlobalState.new tags) .Default
  let runtime : MachineGCRoots.Storage Os R P H D O Aff := {
    threads := { affinity := config.affinity.map (fun value => #[(ThreadId.MAIN_THREAD,value)]) }
    tls := ⟨ThreadTlsData.initial,#[],#[]⟩
    errnoPlaces := #[], unwindPayloads := .empty, extras := {allocations := #[]}
    environment := .uninit, directories := {}, descriptors := descriptors, ownership := ownership
    entry := ⟨none,none,none,none⟩, externStatics := {} }
  let world : EvalWorld.World Os R P H D O Aff B Host :=
    {runtime, main := none, types, functions := ⟨#[],#[]⟩, vtables := ⟨#[]⟩
     symbols := .empty, choices, trackedAllocations := config.trackedAllocations
     backend := config.backend, host}
  let user : EvalWorld.User Os R P H D O Aff B Host := {
    registry := ⟨ThreadId.MAIN_THREAD,#[]⟩
    identitySupply := ⟨0⟩
    user := ⟨addresses,⟨world,config.validation,config.alignment,false,#[]⟩,#[]⟩ }
  let threads := ThreadManager.initial config.fixedScheduling
  let threads := {threads with threads := threads.threads.map fun thread =>
    {thread with originSpanToken := config.dummySpan.id}}
  return ⟨⟨#[]⟩,⟨memory,borrow,clocks,threads,#[],#[],user⟩⟩
end Miri.Input.InitialMachine
