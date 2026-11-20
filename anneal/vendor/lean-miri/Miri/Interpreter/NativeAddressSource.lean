import Miri.Interpreter.NativePreparedGlobals
import Miri.Interpreter.NativeAbi
import Miri.Interpreter.MachineAddress

/-! Pinned alloc_addresses/mod.rs:110–198,225–233. Native external-address
selection runs on the actual machine, reading canonical allocation kinds and
owners. Only compiler signature queries and actual libffi closure construction
remain supplied; there is no whole-allocation-address oracle or invented frame. -/
namespace Miri.Interpreter.NativeAddressSource
open Miri.ABI Miri.Memory Miri.MIR Miri.Memory.AllocAddresses
abbrev State := MachineAddress.State
abbrev M := MachineAddress.M

structure Compiler (K U C : Type) where
  queries : NativeAbi.Queries (State K U) C
  /-- Actual instantiate_bound_regions_with_erased(fn_sig(instance)) query on
  this compiler GlobalAlloc::Function. Missing evidence is an error; it must
  not choose the non-instance dummy-allocation branch. -/
  functionSignature : C → AllocId → M K U (Array TyId × TyId)

structure Effects (K U C : Type) where
  backing : NativeAllocationLifecycle.Backing (State K U)
  compiler : Compiler K U C
  closure : NativeAbi.ClosureHost (State K U) C Nat
  /-- Source cfg(all(feature="native-lib", unix)), not guest target guessing. -/
  closuresEnabled : Bool
  queryBudget : Nat

private def checkedAddress (address : Nat) : M K U UInt64 := do
  if address == 0 then throw (.invalidProgram "native host address is null")
  unless address < 2^64 do throw (.invalidProgram "native host address does not fit source u64")
  pure (UInt64.ofNat address)

/-- Actual source native branch. The surrounding MachineAddress engine owns
TypeId zero, first-use caching and post-effect address state. -/
def externalAddress (effects : Effects K U C) (choice : C) (id : AllocId)
    (_sourceInfo : AllocationAddressInfo) : M K U UInt64 := do
  let machine ← get
  unless machine.user.addresses.addressMode == .nativeLib do
    throw (.invalidProgram "native address provider selected outside native-lib address mode")
  let info ← match machine.memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.invalidProgram s!"native allocation metadata: {reprStr error}")
  match info.kind with
  | .dead => throw (.invalidProgram "native address requested for dead allocation")
  | .typeId => throw (.invalidProgram "native address provider received source TypeId zero branch")
  | .liveData =>
    -- Compiler data/statics enter with Global memory kind. Dynamic allocation
    -- of the machine Global kind is forbidden by MemoryLifecycle; an ordinary
    -- local allocation is already in the live map with its retained owner.
    if let some global := machine.memory.findGlobal? id then
      unless global.kind == .memory || global.kind == .static do
        throw (.invalidProgram "native live-data global has non-data compiler identity")
      checkedAddress (← NativePreparedGlobals.reserve NativePreparedGlobals.machineAccess
        effects.backing id info.size info.align)
    else
      let some (_,entry) := machine.memory.live.find? (·.1 == id)
        | throw (.invalidProgram "native non-global data backing is not live")
      let address ← match NativeAllocationLifecycle.address entry.allocation with
        | .ok address => pure address
        | .error reason => throw (.invalidProgram reason)
      checkedAddress address
  | .function =>
    if effects.closuresEnabled then
      if let some global := machine.memory.findGlobal? id then
        unless global.kind == .function do
          throw (.invalidProgram "native function has non-function compiler identity")
        match global.payload with
        | some .function =>
          let (inputs,output) ← effects.compiler.functionSignature choice id
          let address ← NativeAbi.buildClosure effects.compiler.queries effects.closure
            choice effects.queryBudget inputs output
          return ← checkedAddress address
        | _ => throw (.unsupported "native compiler function instance evidence unavailable")
    checkedAddress (← NativePreparedGlobals.dummyAddress effects.backing)
  | .vtable | .vaList =>
    checkedAddress (← NativePreparedGlobals.dummyAddress effects.backing)

/-- Construct the native machine address dictionary from genuine leaves. -/
def hooks (runtime : RuntimeTargetDataLayout) (classify : AddressStateError → StepError)
    (effects : Effects K U C) (choice : C) : MachineAddress.Hooks K U where
  arithmetic := ⟨runtime.pointerSize⟩
  externalAddress := externalAddress effects choice
  classifyAddressError := classify
/-- Source get_global_alloc_bytes shares both the actual address engine and
its prepared-owner store; self-references observe the cached address before
compiler pointer relocation begins. -/
def globalBytes (choices : ExecutionChoices.Access (State K U))
    (h : MachineAddress.Hooks K U) (effects : Effects K U C) :
    GlobalAllocationMachine.Bytes K (PointerMachine.User U) :=
  NativePreparedGlobals.bytes NativePreparedGlobals.machineAccess effects.backing
    (fun id => do return (← MachineAddress.addrFromAllocId choices h id (some .other)).toNat)
end Miri.Interpreter.NativeAddressSource
