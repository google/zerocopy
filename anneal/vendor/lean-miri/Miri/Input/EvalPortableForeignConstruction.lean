import Miri.Input.EvalForeignConstruction
import Miri.Interpreter.MiriShimMachine
import Miri.Interpreter.BacktraceMachine
import Miri.Interpreter.ThreadMachine

/-! Source construction for the portable Miri and backtrace extern families.
The physical operations are projected from canonical machine state; the
remaining fields are explicit host/compiler effects, never complete shim
operation records supplied as opaque fallbacks. -/
namespace Miri.Input.EvalPortableForeignConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.Concurrency
open EvalForeignConstruction

abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev World Os R P H D O Aff B Host := EvalWorld.World Os R P H D O Aff B Host
abbrev Stored Os R P H D O Aff B Host := EvalCoreMachine.Stored Os R P H D O Aff B Host
abbrev Control Os R P H D O Aff B Host := ValidityMachine.Control (Stored Os R P H D O Aff B Host)
abbrev EntryUser Os R P H D O Aff B Host := ValidityMachine.UserState (World Os R P H D O Aff B Host)
abbrev M Os R P H D O Aff B Host A := MachineHooks.M MiriMemoryKind
  (User Os R P H D O Aff B Host) A

/-- Host/source effects which have no canonical physical implementation in
MiriShimMachine. stdout/stderr failures are interpreted by the caller using
Miri's ignored-I/O-error policy; absence of a host implementation is an error. -/
structure MiriEffects (Os R P H D O Aff B Host HostPath : Type) where
  /-- Optional authoritative `AllocId.0.get()` evidence from the source
  compiler identity domain. This must not be reconstructed from the importer's
  dense runtime allocation IDs. When absent, `miri_get_alloc_id` remains an
  explicit Unsupported obligation after its source pointer checks. -/
  sourceAllocIdNumber : Option (AllocId → M Os R P H D O Aff B Host UInt64) := none
  namePointer : Pointer (Option Provenance) → UInt8 → ByteArray →
    M Os R P H D O Aff B Host Unit
  printBorrowState : UInt64 → Bool → M Os R P H D O Aff B Host Unit
  checkNoIsolation : String → M Os R P H D O Aff B Host Unit
  readHostPath : Pointer (Option Provenance) → M Os R P H D O Aff B Host HostPath
  writeTargetPath : HostPath → Pointer (Option Provenance) → UInt64 →
    M Os R P H D O Aff B Host (Bool × UInt64)
  writeHost : Bool → ByteArray → M Os R P H D O Aff B Host Unit

private def unavailable (message : String) : M Os R P H D O Aff B Host A :=
  throw (.unsupported message)

/-- Build the Miri-only operation record from canonical memory/provenance/GC
and thread machines. The caller supplies only the true host, diagnostic, and
selected-backend effects. Allocation, scalar access, byte slices, unwind,
bookkeeping, yielding, and symbolic promises come from MiriShimMachine.core. -/
def miriCore [DecidableEq MiriMemoryKind]
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host) C MachineHooks.FrameExtra Other)
    (choice : C)
    (thread : ThreadMachine.Hooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host) C O
      ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff)
    (unitLayout : M Os R P H D O Aff B Host LocalLayout)
    (reuseClock : Option Concurrency.VectorIdx)
    (effects : MiriEffects Os R P H D O Aff B Host HostPath)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :=
  let source : MiriShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance HostPath := {
    foreign
    readU64 := fun _ => unavailable "Miri physical u64 reader was not installed"
    readU8 := fun _ => unavailable "Miri physical u8 reader was not installed"
    readBool := fun _ => unavailable "Miri physical bool reader was not installed"
    readImmediate := fun _ => unavailable "Miri physical immediate reader was not installed"
    readByteSlice := fun _ => unavailable "Miri physical byte reader was not installed"
    writeU64 := fun _ _ => unavailable "Miri physical u64 writer was not installed"
    writeUsize := fun _ _ => unavailable "Miri physical usize writer was not installed"
    writeBool := fun _ _ => unavailable "Miri physical bool writer was not installed"
    allocation := fun _ => unavailable "Miri allocation projection was not installed"
    sourceAllocIdNumber := fun id =>
      match effects.sourceAllocIdNumber with
      | some query => query id
      | none => unavailable "authoritative source rustc AllocId number is unavailable"
    allocationInfo := fun _ => unavailable "Miri allocation metadata projection was not installed"
    localCAllocation := fun _ => unavailable "Miri allocation-kind projection was not installed"
    trackAllocation := fun _ => unavailable "Miri tracking projection was not installed"
    staticRoot := fun _ => unavailable "Miri static-root projection was not installed"
    startUnwind := fun _ => unavailable "Miri unwind projection was not installed"
    provenanceGc := unavailable "Miri provenance-GC projection was not installed"
    namePointer := effects.namePointer
    printBorrowState := effects.printBorrowState
    checkNoIsolation := effects.checkNoIsolation
    readHostPath := effects.readHostPath
    writeTargetPath := effects.writeTargetPath
    writeHost := effects.writeHost
    -- These fields are replaced by MiriShimMachine.core below. Reaching one
    -- would indicate a mismatch in the canonical machine projection.
    threadFromUsize := fun _ => unavailable "Miri thread lookup projection was not installed"
    yieldThread := unavailable "Miri yield projection was not installed"
    symbolicPromise := fun _ _ => unavailable "Miri symbolic-alignment projection was not installed"
    spawnThread := fun dest routine argument => do
      let dest ← foreign.forceAllocation dest
      let .memory memory := dest.ref
        | throw (.invalidProgram "miri_thread_spawn destination was not materialized")
      let mplace : MPlaceTy Provenance := ⟨memory,dest.layout⟩
      let unitLayout ← unitLayout
      ExecutionStateTransport.reverseAction do
        let _ ← ThreadMachine.startRegularThread thread choice (some mplace) routine
          thread.functions.call.rustAbi argument unitLayout reuseClock
        pure ()
    joinExclusive := fun joined success dest => do
      let dest ← foreign.forceAllocation dest
      let .memory memory := dest.ref
        | throw (.invalidProgram "miri_thread_join destination was not materialized")
      let mplace : MPlaceTy Provenance := ⟨memory,dest.layout⟩
      ExecutionStateTransport.reverseAction
        (ThreadMachine.joinExclusive thread choice joined (Scalar.fromBool success) mplace) }
  MiriShimMachine.core machine choice source

/-- Construct the connected backtrace family with real machine stack and
memory operations, exact compiler-exported hygiene/source-map queries, and
canonical function allocation/global lookup capabilities. -/
def backtraceCore [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D O Aff B Host))
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (choice : C)
    (prepared : CompilerBacktraceSource.Prepared)
    (hostUsizeMax : Nat)
    (unitPointerLayout : M Os R P H D O Aff B Host LocalLayout)
    (misaligned : Pointer (Option Provenance) → Align →
      M Os R P H D O Aff B Host (Option Misalignment))
    (functionPointer : CallInstance → M Os R P H D O Aff B Host (Pointer (Option Provenance)))
    (allocation : Pointer (Option Provenance) → M Os R P H D O Aff B Host (AllocId × Size))
    (globalFunction : AllocId → M Os R P H D O Aff B Host (Option CallInstance))
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    Backtrace.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance
      MachineHooks.FrameExtra CompilerBacktraceSource.Position :=
  BacktraceMachine.core access arithmetic projection choice
    (CompilerBacktraceSource.source prepared hostUsizeMax unitPointerLayout
      misaligned functionPointer allocation globalFunction) foreign

/-- Full portable order uses the source Miri family, then backtrace, then
memory/string. This constructor cannot accept whole Miri or backtrace Hooks;
their physical portions are built from the canonical source machines above. -/
def portableOther
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (miri : MiriShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance HostPath)
    (backtrace : Backtrace.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance
      MachineHooks.FrameExtra CompilerBacktraceSource.Position)
    (adtReprC : TyId → M Os R P H D O Aff B Host (Option Bool))
    (memory : MemoryShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance)
    (stringBudget : Nat) :
    String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host (Option ForeignItems.EmulateItemResult) :=
  EvalForeignConstruction.portableOther foreign memory stringBudget miri backtrace adtReprC

/-- Complete portable-family constructor: no complete Miri or backtrace Hooks
record crosses this boundary. Their operations are derived here from canonical
machine configurations and exact compiler source tables. -/
def portableOtherFromSource [DecidableEq MiriMemoryKind]
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (machine : MiriShimMachine.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host) C MachineHooks.FrameExtra Other)
    (choice : C)
    (thread : ThreadMachine.Hooks MiriMemoryKind
      (EntryUser Os R P H D O Aff B Host) C O
      ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff)
    (unitLayout : LocalLayout) (reuseClock : Option Concurrency.VectorIdx)
    (effects : MiriEffects Os R P H D O Aff B Host HostPath)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (EvalCoreMachine.User Os R P H D O Aff B Host))
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (prepared : CompilerBacktraceSource.Prepared)
    (hostUsizeMax : Nat)
    (unitPointerLayout : M Os R P H D O Aff B Host LocalLayout)
    (misaligned : Pointer (Option Provenance) → Align →
      M Os R P H D O Aff B Host (Option Misalignment))
    (functionPointer : CallInstance → M Os R P H D O Aff B Host (Pointer (Option Provenance)))
    (allocation : Pointer (Option Provenance) → M Os R P H D O Aff B Host (AllocId × Size))
    (globalFunction : AllocId → M Os R P H D O Aff B Host (Option CallInstance))
    (adtReprC : TyId → M Os R P H D O Aff B Host (Option Bool))
    (memory : MemoryShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance)
    (stringBudget : Nat) :
    String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host (Option ForeignItems.EmulateItemResult) := by
  let miri := miriCore machine choice thread (pure unitLayout) reuseClock effects foreign
  let backtrace := backtraceCore access arithmetic projection choice prepared
    hostUsizeMax unitPointerLayout misaligned functionPointer allocation globalFunction foreign
  exact EvalForeignConstruction.portableOther foreign memory stringBudget miri backtrace adtReprC

end Miri.Input.EvalPortableForeignConstruction
