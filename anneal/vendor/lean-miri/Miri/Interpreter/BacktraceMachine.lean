import Miri.Interpreter.Backtrace
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.MiriShims

/-! Canonical actual-memory binding for backtrace.rs. Raw string copying owns
bounds/init/provenance/race/TB transitions through RawMemoryMachine; typed
pointer and field writes use PlaceMachine's source place writer. -/
namespace Miri.Interpreter.BacktraceMachine
open Miri.ABI Miri.Memory Miri.MIR

private def lift (result : Except StepError A) : MachineHooks.M K User A :=
  match result with | .ok value => pure value | .error error => throw error

/-- Machine source/span rendering and compiler signature leaves stay required.
This binding supplies actual active frames (including body IDs), actual typed
scalar reads, local projections and all raw/typed destination writes. -/
def hooks [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (choice : C)
    (base : Backtrace.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      B I MachineHooks.FrameExtra Loc) :
    Backtrace.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      B I MachineHooks.FrameExtra Loc :=
  let readScalar := fun operand => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let readPointer := fun operand => do
    let scalar ← readScalar operand
    lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let writePointer := fun pointer dest => do
    let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer |>.mapError ScalarOps.scalarError)
    writePlaceImmediate projection.place choice (.scalar scalar) dest
  { base with
    foreign := { base.foreign with readPointer, writePointer }
    target := access.runtime.base
    arithmetic
    stack := do return (← get).stack
    readU64 := fun operand => do lift ((← readScalar operand).toUInt64.mapError ScalarOps.scalarError)
    memoryOffset := projection.place.memoryOffset choice
    memoryPlace := fun place => ⟨.memory place.mplace,place.layout⟩
    layout := RuntimePlace.layout
    projectField := PlaceDynamic.field projection choice
    writeScalar := fun scalar dest => writePlaceImmediate projection.place choice (.scalar scalar) dest
    writeBytes := RawMemoryMachine.writeBytes access arithmetic }

/-- Exact compiler/global source capabilities. Physical frame reads, pointer
and field writes are built below and cannot be replaced by this record. -/
structure Sources (S Loc : Type) where
  hostUsizeMax : Nat
  unitPointerLayout : EStateM StepError S LocalLayout
  misaligned : Pointer (Option Provenance) → Align → EStateM StepError S (Option Misalignment)
  functionPointer : CallInstance → EStateM StepError S (Pointer (Option Provenance))
  collapsedSpanLo : BodyIdentity → SpanRef → EStateM StepError S UInt32
  allocation : Pointer (Option Provenance) → EStateM StepError S (AllocId × Size)
  globalFunction : AllocId → EStateM StepError S (Option CallInstance)
  lookupCharPos : UInt32 → EStateM StepError S Loc
  line : Loc → Nat
  column : Loc → Nat
  renderInstance : CallInstance → EStateM StepError S String
  remappedFilename : Loc → EStateM StepError S String

/-- Nonrecursive source construction: no baseline portable/foreign dispatcher. -/
def core [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (choice : C) (source : Sources (MachineHooks.State K User) Loc)
    (foreign : ForeignItems.Core Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      (Pointer (Option Provenance)) B I) :
    Backtrace.CoreHooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      B I MachineHooks.FrameExtra Loc :=
  let readScalar := fun operand => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  { foreign
    target := access.runtime.base
    arithmetic
    hostUsizeMax := source.hostUsizeMax
    stack := do return (← get).stack
    readU64 := fun operand => do lift ((← readScalar operand).toUInt64.mapError ScalarOps.scalarError)
    unitPointerLayout := source.unitPointerLayout
    misaligned := source.misaligned
    memoryOffset := projection.place.memoryOffset choice
    memoryPlace := fun place => ⟨.memory place.mplace,place.layout⟩
    layout := RuntimePlace.layout
    projectField := PlaceDynamic.field projection choice
    writeScalar := fun scalar dest => writePlaceImmediate projection.place choice (.scalar scalar) dest
    writeBytes := RawMemoryMachine.writeBytes access arithmetic
    functionPointer := source.functionPointer
    collapsedSpanLo := source.collapsedSpanLo
    allocation := source.allocation
    globalFunction := source.globalFunction
    lookupCharPos := source.lookupCharPos
    line := source.line
    column := source.column
    renderInstance := source.renderInstance
    remappedFilename := source.remappedFilename }

def bind [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (choice : C)
    (base : Backtrace.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      B I MachineHooks.FrameExtra Loc)
    (adtReprC : TyId → MachineHooks.M K User (Option Bool)) :
    ForeignItems.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      (Pointer (Option Provenance)) B I :=
  Backtrace.bind (hooks access arithmetic projection choice base) adtReprC

/-- Connect the four source APIs to the Miri-only portable dispatch chain.
Other portable/foreign operations retain the already bound source dictionary. -/
def bindMiriShims [DecidableEq K] (access : PlaceMachine.AccessConfig K User)
    (arithmetic : PointerArithmetic)
    (projection : PlaceProjectionHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (choice : C)
    (backtrace : Backtrace.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      B I MachineHooks.FrameExtra Loc)
    (miri : MiriShims.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance) B I HostPath)
    (adtReprC : TyId → MachineHooks.M K User (Option Bool)) :
    ForeignItems.Hooks Provenance (MachineHooks.State K User) D (RuntimePlace Provenance)
      (Pointer (Option Provenance)) B I :=
  bind access arithmetic projection choice { backtrace with foreign := MiriShims.bind miri } adtReprC

end Miri.Interpreter.BacktraceMachine
