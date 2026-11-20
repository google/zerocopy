import Miri.Input.EvalPortableForeignConstruction
import Miri.Input.AllocationImage
import Miri.Input.EvalUnixIoConstruction
import Miri.Interpreter.OsStrings

/-! Raw source residual bindings for the portable Miri-specific externs.
This module derives host path conversion, output and isolation from source-level capabilities. Unsupported diagnostics and
compiler identity evidence remain demand-local. -/
namespace Miri.Input.EvalMiriHostEffectsConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev User Os R P H D O Aff B Host := EvalCoreMachine.User Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host := EvalCoreMachine.State Os R P H D O Aff B Host
abbrev M Os R P H D O Aff B Host A :=
  MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A

set_option autoImplicit false in
structure RawLeaves
    (Os R P H D O Aff B Host Error Meta Kind : Type) where
  strings : OsStrings.Hooks Provenance
    (State Os R P H D O Aff B Host) Os Kind
  hostFiles : EvalUnixIoConstruction.HostFileEffects
    (State Os R P H D O Aff B Host) H D O Error Meta
  /-- Bound the source `write_all` retry loop so repeated Interrupted or
  adversarial short writes remain an explicit resource-exhaustion outcome. -/
  writeRetryBudget : Nat
  communicate : Bool
  /-- Exact rustc allocation-number identity mapping, when the source compiler
  retains it. Dense imported memory IDs are deliberately not accepted here. -/
  sourceAllocIdNumber : Option
    (AllocId → M Os R P H D O Aff B Host UInt64) := none

  namePointer : Option
    (Pointer (Option Provenance) → UInt8 → ByteArray → M Os R P H D O Aff B Host Unit) := none
  printBorrowState : Option
    (UInt64 → Bool → M Os R P H D O Aff B Host Unit) := none
  -- Host OsString representation is the source host-path carrier.

private def unsupported (message : String) : M Os R P H D O Aff B Host A :=
  throw (.unsupported message)

/-- The source `Write::write_all` loop over a host writer. Host I/O errors are
returned to this boundary and ignored by its caller; capability and interpreter
errors remain thrown. A finite budget prevents endless Interrupted responses. -/
def writeAllHost {S E : Type}
    (write : ByteArray → EStateM StepError S (Except (IoError.HostError E) Nat))
    (budget : Nat) (bytes : ByteArray) : EStateM StepError S Unit := do
  let rec loop : Nat → Nat → EStateM StepError S Unit
    | 0, offset =>
      if offset >= bytes.size then pure ()
      else throw (.resourceExhaustion "miri_write_to_stdout/stderr write_all budget")
    | fuel + 1, offset => do
      if offset >= bytes.size then return
      let remaining := bytes.extract offset bytes.size
      match ← write remaining with
      | .error error =>
        if error.kind == .Interrupted then loop fuel offset
        else pure ()
      | .ok 0 => pure ()
      | .ok count =>
        if count > remaining.size then
          throw (.invalidProgram "host write returned a count larger than its input")
        loop fuel (offset + count)
  loop budget 0

/-- Bind actual source OS-string routines and host stdout/stderr effects to
the Miri shim residual record. `HostFileEffects.hostWrite` errors are ignored
because pinned `foreign_items.rs` ignores `write_all` errors; absent
capabilities represented by `StepError` still propagate. -/
def fromSource
    (leaves : RawLeaves Os R P H D O Aff B Host Error Meta Kind) :
    EvalPortableForeignConstruction.MiriEffects Os R P H D O Aff B Host Os := {
  sourceAllocIdNumber := leaves.sourceAllocIdNumber
  namePointer := leaves.namePointer.getD
    (fun _ _ _ => unsupported "miri_pointer_name source Tree Borrows diagnostic")
  printBorrowState := leaves.printBorrowState.getD
    (fun _ _ => unsupported "miri_print_borrow_state source Tree Borrows diagnostic")
  checkNoIsolation := fun name => do
    unless leaves.communicate do throw (.termination (.unsupportedInIsolation name))
  readHostPath := fun pointer => OsStrings.readOsString leaves.strings pointer
  writeTargetPath := fun path pointer capacity =>
    OsStrings.writePath leaves.strings path pointer capacity
  writeHost := fun stderr bytes => do
    let description : Files.Description H D O := if stderr then .stderr else .stdout
    writeAllHost (leaves.hostFiles.hostWrite description) leaves.writeRetryBudget bytes
  }

/-- Source-context convenience constructor. OS encodings, target conversion,
and target-memory C-string operations are generated from the same canonical
environment memory and host `OsStr` implementation used by other shims. -/
def fromCoreSource [DecidableEq MiriMemoryKind]
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)) C P)
    (hostFiles : EvalUnixIoConstruction.HostFileEffects
      (State Os R P H D O Aff B Host) H D O Error Meta)
    (communicate : Bool)
    (writeRetryBudget : Nat)
    (sourceAllocIdNumber : Option
      (AllocId → M Os R P H D O Aff B Host UInt64) := none)
    (namePointer : Option
      (Pointer (Option Provenance) → UInt8 → ByteArray → M Os R P H D O Aff B Host Unit) := none)
    (printBorrowState : Option
      (UInt64 → Bool → M Os R P H D O Aff B Host Unit) := none) :
    EvalPortableForeignConstruction.MiriEffects Os R P H D O Aff B Host Os :=
  fromSource {
    strings := EvalHostRuntimeConstruction.osStringsFromMemory host memory
    hostFiles
    communicate
    writeRetryBudget
    sourceAllocIdNumber
    namePointer
    printBorrowState
  }

/-- Recover rustc's allocation number only through the exact exporter-node to
runtime-global crosswalk. Fresh runtime allocations and legacy exports have no
witness and remain Unsupported; the runtime's own dense ID is never returned. -/
def sourceAllocIdNumberFromImage
    (image : AllocationImage.Imported) :
    AllocId → M Os R P H D O Aff B Host UInt64 := fun id => do
  let state ← get
  if state.machine.memory.sourceAllocIdWorldActive then
    match state.machine.memory.sourceAllocIdForRuntime? id with
    | some sourceId => return sourceId
    | none => throw (.unsupported "miri_get_alloc_id source raw identity is absent from the installed prepared AllocId world")
  let node ← match image.sourceNode state.machine.memory id with
    | .ok node => pure node
    | .error reason => throw (.unsupported s!"miri_get_alloc_id source identity: {reason}")
  match node.sourceAllocId with
  | some number =>
    if image.source.any (fun candidate =>
        candidate.id != node.id && candidate.sourceAllocId == some number) then
      throw (.invalidProgram "multiple compiler allocation nodes share one rustc AllocId witness")
    pure number
  | none => throw (.unsupported "miri_get_alloc_id source rustc AllocId witness is absent")

/-- Inverse source-number lookup for `miri_print_borrow_state`. Zero and a raw ID
with no global return none. Opaque globals remain Unsupported: source memory
and statics can be live data even before their payload is imported. Export-node
witnesses and the runtime imported-global table must identify one unique
allocation before it can be inspected. -/
def sourceAllocIdFromImage
    (image : AllocationImage.Imported) :
    UInt64 → M Os R P H D O Aff B Host (Option AllocId) := fun sourceNumber => do
  if sourceNumber == 0 then return none
  let state ← get
  if state.machine.memory.sourceAllocIdWorldActive then
    if state.machine.memory.opaqueSourceGlobalIds.contains sourceNumber then
      throw (.unsupported "miri_print_borrow_state source global payload is opaque in the prepared AllocId world")
    return state.machine.memory.runtimeForSourceAllocId? sourceNumber
  let foundNodes := image.source.filter (fun node => node.sourceAllocId == some sourceNumber)
  if foundNodes.size > 1 then
    throw (.invalidProgram "multiple compiler allocation nodes share one rustc AllocId witness")
  let some node := foundNodes[0]? |
    throw (.unsupported "miri_print_borrow_state rustc AllocId witness is unavailable")
  match state.machine.memory.runtimeIdForExport? node.id with
  | some runtimeId => return some runtimeId
  | none => throw (.unsupported "miri_print_borrow_state source allocation has no imported runtime identity")

end Miri.Input.EvalMiriHostEffectsConstruction
