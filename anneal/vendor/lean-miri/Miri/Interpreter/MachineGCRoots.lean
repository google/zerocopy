import Miri.Interpreter.MiriShims
import Miri.Interpreter.GCRoots
import Miri.Interpreter.ThreadTlsMachine
import Miri.Interpreter.UnixDirectories
import Miri.Interpreter.FileOwnership
import Miri.Interpreter.FunctionPointers

/-! Source whole-machine provenance visitor composition. Views project actual
runtime records, not caller-chosen root lists. No machine read, retag, callback,
host operation or descriptor drop is executed while collecting roots. -/
namespace Miri.Interpreter.MachineGCRoots
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
open ProvenanceGC (Roots)

/-- Exact machine.rs saved pointer fields. Their absent state is represented by
None only when the corresponding source machine field is absent. -/
structure EntryPointers where
  mainReturn : Option (MPlaceTy Provenance)
  argc : Option (Pointer Provenance)
  argv : Option (Pointer Provenance)
  commandLine : Option (Pointer Provenance)

/-- Required actual storage projections. There is intentionally no generic
"remaining roots" callback or empty default for unported runtime fields. FDs
are included to make their source-empty visitor an explicit operation. -/
structure Views (User Os ReadDir Payload Handle Directory Other : Type) where
  stacks : User → ThreadStacks.Registry
  tls : User → ThreadTlsMachine.Data
  errnoPlaces : User → Array (AllocId × MPlaceTy Provenance)
  unwindPayloads : User → Unwind.PayloadStore
  extras : User → MemoryExtras.Registry Payload
  environment : User → EnvVars.State (Option Provenance) Os
  directories : User → UnixDirectories.Table ReadDir
  descriptors : User → Files.Table (Files.Description Handle Directory Other)
  ownership : User → FileOwnership.Registry (Files.Description Handle Directory Other)
  entry : User → EntryPointers
  externStatics : User → ExternStatic.State

/-- files.rs:101–105,584–588 explicitly assumes all source FileDescription
instances carry no provenance. Numeric FD identities and host/peer handles do
not become allocation roots. This does not license arbitrary new extensions
with provenance-bearing description fields to omit their own source visitor. -/
def visitFiles (roots : Roots) (_table : Files.Table (Files.Description H D O))
    (_ownership : FileOwnership.Registry (Files.Description H D O)) : Roots := roots

/-- unix/fs.rs:228–236 visits stream.entry only, not the host ReadDir, FD
number/identity, next-id counter, or special-entry strings. -/
def visitDirectories (roots : Roots) (table : UnixDirectories.Table R) : Roots :=
  table.streams.foldl (fun roots (_,stream) => match stream.entry with
    | none => roots | some (pointer,_) => roots.pointer pointer) roots

/-- Thread.visit visits last_error even for terminated retained records. Unused
side-table entries are not source-owned errno places and are not roots. -/
def visitErrno (roots : Roots) (manager : ThreadManager)
    (storage : Array (AllocId × MPlaceTy Provenance)) : Except StepError Roots := do
  let mut roots := roots
  for thread in manager.threads do
    if let some token := thread.lastErrorLocation then
      let entries := storage.filter (fun entry => entry.1.value.toNat == token)
      let some (_,place) := entries[0]? | throw (.invalidProgram "GC errno token has no typed place")
      if entries.size != 1 then throw (.invalidProgram "GC errno token ambiguous")
      roots ← roots.memPlace place.mplace
  return roots

/-- Full user portion of machine.rs:1093–1110, plus actual inactive-thread
stacks and allocation-local weak-buffer visitors. The active stack and live
allocation bytes/tree tags are visited by ProvenanceGC.run itself. -/
def visit (views : Views User Os R Payload H D O)
    (state : MachineHooks.State K User) (initial : Roots) : Except StepError Roots := do
  let user := state.machine.user
  let manager := state.machine.threads
  let mut roots ← ProvenanceGC.Roots.unwindPayloads initial manager (views.unwindPayloads user)
  roots ← visitErrno roots manager (views.errnoPlaces user)
  roots ← roots.inactiveStacks manager (views.stacks user)
  let tls := views.tls user
  roots ← roots.threadLocalAllocations manager tls.statics
  roots ← roots.threadTls tls.values
  roots := roots.envVars (views.environment user)
  roots := visitDirectories roots (views.directories user)
  roots := visitFiles roots (views.descriptors user) (views.ownership user)
  -- Source AllocExtra::visit belongs to actual live allocations, not leftover
  -- registry slots from an already removed allocation's failing deallocation.
  let registry := views.extras user
  let registry := {registry with allocations := registry.allocations.filter fun entry =>
    state.machine.memory.live.any (fun live => live.1 == entry.1)}
  roots ← roots.weakMemory registry
  let entry := views.entry user
  if let some place := entry.mainReturn then roots ← roots.memPlace place.mplace
  for pointer in #[entry.argc,entry.argv,entry.commandLine] do
    if let some pointer := pointer then roots := roots.strictPointer pointer
  roots := roots.externStatics (views.externStatics user)
  -- Source intentionally ignores static_roots (leak reporting), blocked/TLS
  -- callbacks, sync objects, readiness closures, caches and host-only fields.
  return roots

/-- The lawful address lens points at the SAME canonical address and symbolic
alignment maps used by function pointers, casts and alignment checks. GC never
creates a parallel cache or reconstructs addresses from allocation identity. -/
def hooks (views : Views User Os R Payload H D O)
    (addresses : FunctionPointers.AddressLens User AddressPayload) : ProvenanceGC.Hooks K User where
  visitUser := visit views
  addresses := fun user => (addresses.get user).addresses
  setAddresses := fun value user => addresses.put user {addresses.get user with addresses := value}
  symbolicAlignment := fun user => (addresses.get user).symbolicAlignment
  setSymbolicAlignment := fun value user => addresses.put user {addresses.get user with symbolicAlignment := value}

/-- Actual source collection and TB/dead/address metadata pruning in one
machine action. Root extraction has no memory-access hooks or initialization
checks, and source error prefixes are retained by ProvenanceGC.run. -/
def run [DecidableEq K] (views : Views User Os R Payload H D O)
    (addresses : FunctionPointers.AddressLens User AddressPayload) : MachineHooks.M K User Unit :=
  ProvenanceGC.run (hooks views addresses)

/-- Bind the actual miri_provenance_gc foreign arm to this whole-machine walk. -/
def bindMiri (views : Views User Os R Payload H D O)
    (addresses : FunctionPointers.AddressLens User AddressPayload)
    (base : MiriShims.Hooks Provenance (MachineHooks.State K User) Dest MD B I HostPath) [DecidableEq K] :
    MiriShims.Hooks Provenance (MachineHooks.State K User) Dest MD B I HostPath :=
  {base with provenanceGc := run views addresses}
/-- Concrete root-bearing source storage. Runtime state adapters can directly
use these fields rather than maintaining GC-only shadow copies. Callbacks are
real thread-runtime state, deliberately excluded by the pinned thread visitor. -/
structure Storage (Os R Payload H D O Aff : Type) where
  threads : ThreadMachine.Runtime Aff
  tls : ThreadTlsMachine.Data
  errnoPlaces : Array (AllocId × MPlaceTy Provenance)
  unwindPayloads : Unwind.PayloadStore
  extras : MemoryExtras.Registry Payload
  environment : EnvVars.State (Option Provenance) Os
  directories : UnixDirectories.Table R
  descriptors : Files.Table (Files.Description H D O)
  ownership : FileOwnership.Registry (Files.Description H D O)
  entry : EntryPointers
  externStatics : ExternStatic.State

abbrev StoredUser (Os R Payload H D O Aff : Type) :=
  ThreadStacks.Storage (PointerMachine.User (Storage Os R Payload H D O Aff))

/-- The active stack is StepState.stack and inactive stacks are the actual
ThreadStacks registry. Address state exists once, in the nested PointerMachine
user. All other projections read the source runtime fields above directly. -/
def storedViews : Views (StoredUser Os R Payload H D O Aff) Os R Payload H D O where
  stacks := fun user => user.registry
  tls := fun user => user.user.payload.tls
  errnoPlaces := fun user => user.user.payload.errnoPlaces
  unwindPayloads := fun user => user.user.payload.unwindPayloads
  extras := fun user => user.user.payload.extras
  environment := fun user => user.user.payload.environment
  directories := fun user => user.user.payload.directories
  descriptors := fun user => user.user.payload.descriptors
  ownership := fun user => user.user.payload.ownership
  entry := fun user => user.user.payload.entry
  externStatics := fun user => user.user.payload.externStatics

def storedAddresses : FunctionPointers.AddressLens (StoredUser Os R Payload H D O Aff)
    (Storage Os R Payload H D O Aff) where
  get := fun user => user.user
  put := fun user value => {user with user := value}
  getPut := by intros; rfl
  putGet := by intro user; cases user; rfl
  putPut := by intros; rfl

/-- Entire source GC operation for this concrete runtime composition. -/
def runStored [DecidableEq K] : MachineHooks.M K (StoredUser Os R Payload H D O Aff) Unit :=
  run storedViews storedAddresses

def bindStoredMiri [DecidableEq K]
    (base : MiriShims.Hooks Provenance (MachineHooks.State K (StoredUser Os R Payload H D O Aff))
      Dest MD B I HostPath) :
    MiriShims.Hooks Provenance (MachineHooks.State K (StoredUser Os R Payload H D O Aff))
      Dest MD B I HostPath :=
  {base with provenanceGc := runStored}

end Miri.Interpreter.MachineGCRoots
