import Lean.Util.Profile
import Miri.Interpreter.ExecutionCallLeaves
import Miri.Interpreter.FunctionPointerConsumers
import Miri.Input.CompilerVTableQueries
import Miri.Input.CompilerCallPipeline
import Miri.Interpreter.VTableMachine

/-! Imported/dynamic symbolic vtables share canonical type/predicate identities
and the same actual allocation/address engine. Compiler query leaves stay typed. -/
namespace Miri.Input.CompilerVTableMachine
open Lean Miri.ABI Miri.Memory Miri.Interpreter
structure Prepared where
  calls : CompilerCallPipeline.Prepared
  queries : CompilerVTableQueries.Prepared

def prepare (calls : CompilerCallPipeline.Prepared) : Except String Prepared := do
  return ⟨calls,← CompilerVTableQueries.prepare calls.symbols.facts⟩

private def lift (result : Except String A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler vtable machine: {error}")

def hooks (p : Prepared) (image : AllocationImage.Imported)
    (base : VTableMachine.Hooks K User Other) : VTableMachine.Hooks K User Other :=
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.calls.symbols
  {base with importedVTable := fun id => do
    lift (CompilerVTableRuntime.globalVTableUsing p.calls.symbols lookup image (← get).machine.memory id)}

private abbrev VTableKeyIndex := Std.HashMap (Nat × Nat × Nat) (Array Nat)
private abbrev AllocIdIndex := Std.HashMap UInt64 Bool

private def addVTableKey (index : VTableKeyIndex) (ty dynamicType salt position : Nat) : VTableKeyIndex :=
  let key := (ty,dynamicType,salt)
  index.insert key ((index[key]?).getD #[] |>.push position)

private def vtableKeyIndex (entries : Array VTableMachine.Entry) : VTableKeyIndex := Id.run do
  let mut index : VTableKeyIndex := {}
  for (entry, position) in entries.toList.zipIdx do
    index := addVTableKey index entry.typeId entry.dynamicType entry.salt.val position
  return index

private def vtableAllocIndex (entries : Array VTableMachine.Entry) : AllocIdIndex := Id.run do
  let mut index : AllocIdIndex := {}
  for entry in entries do index := index.insert entry.allocation.value true
  return index

private def findVTableKey (entries : Array VTableMachine.Entry) (index : VTableKeyIndex)
    (ty dynamicType salt : Nat) : Option VTableMachine.Entry := Id.run do
  for position in (index[(ty,dynamicType,salt)]?).getD #[] do
    if let some entry := entries[position]? then
      if entry.typeId == ty && entry.dynamicType == dynamicType && entry.salt.val == salt then
        return some entry
  return none

private def seedImportedImpl (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : VTableMachine.Registry) : Except String VTableMachine.Registry := do
  let mut registry := initial
  let mut keys := vtableKeyIndex registry.entries
  let mut allocated := vtableAllocIndex registry.entries
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.calls.symbols
  let input := p.calls.calls.program.input
  let world? := input.compilerAllocIdWorld
  if let some world := world? then
    unless memory.sourceAllocIdWorldActive do
      throw "prepared vtable catalog requires the active source AllocId world"
    unless image.source == input.allocations.filter (·.status == .supported) do
      throw "prepared vtable catalog allocation image differs from its owning program"
    Miri.Input.validateCompilerAllocIdWorldRaw input.raw input.allocations (some world)
      |>.mapError fun error => s!"prepared AllocId world: {error}"
  else
    for (_,id) in memory.importedGlobalIds do
      if let some (ty,dynType) ← CompilerVTableRuntime.globalVTableUsing p.calls.symbols lookup image memory id then
        if let some old := findVTableKey registry.entries keys ty dynType 0 then
          unless old.allocation == id do throw "conflicting imported CTFE salt-zero vtable identities"
        else
          unless !(allocated.contains id.value) do throw "vtable allocation identity already assigned"
          keys := addVTableKey keys ty dynType 0 registry.entries.size
          allocated := allocated.insert id.value true
          registry := {registry with entries := registry.entries.push ⟨ty,dynType,⟨0,by decide⟩,id⟩}
  if let some world := world? then
    for row in world.dedupCatalog do
      if row.keyKind == .vtable then
        let keyRuntime ← AllocationImage.runtimeId memory row.keyAllocationId
        let some key ← CompilerVTableRuntime.globalVTableUsing p.calls.symbols lookup image memory keyRuntime
          | throw "prepared vtable key witness is not a symbolic vtable"
        for result in row.salts do
          if saltBound : result.salt < 32 then
            let resultRuntime ← AllocationImage.runtimeId memory result.allocationId
            unless memory.sourceAllocIdForRuntime? resultRuntime == some result.sourceAllocId do
              throw "prepared vtable result raw AllocId does not match the active memory world"
            let some resultKey ← CompilerVTableRuntime.globalVTableUsing p.calls.symbols lookup image memory resultRuntime
              | throw "prepared vtable salt result is not a symbolic vtable"
            unless resultKey == key do
              throw "prepared vtable salt result does not match its exact type/predicate key"
            let salt : Fin 32 := ⟨result.salt, saltBound⟩
            if let some old := findVTableKey registry.entries keys key.1 key.2 result.salt then
              unless old.allocation == resultRuntime do throw "conflicting prepared vtable allocation for key/salt"
            else
              unless !(allocated.contains resultRuntime.value) do
                throw "prepared vtable allocation identity is already assigned"
              keys := addVTableKey keys key.1 key.2 result.salt registry.entries.size
              allocated := allocated.insert resultRuntime.value true
              registry := {registry with entries := registry.entries.push ⟨key.1,key.2,salt,resultRuntime⟩}
          else throw "prepared vtable salt is outside the source key domain"
  return registry

def seedImportedProfiled (profile : Lean.Options) (p : Prepared)
    (image : AllocationImage.Imported) (memory : MemoryState P E K)
    (initial : VTableMachine.Registry) : Except String VTableMachine.Registry :=
  profileit "startup.vtable_registry" profile fun _ => seedImportedImpl p image memory initial

def seedImported (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : VTableMachine.Registry) :
    Except String VTableMachine.Registry :=
  seedImportedProfiled {} p image memory initial

theorem seedImported_profile_identity (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : VTableMachine.Registry) :
    seedImported p image memory initial = seedImportedProfiled {} p image memory initial := rfl

def attachProfiled (profile : Lean.Options) (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other) : MachineHooks.M K User Unit := do
  let state ← get
  let registry ← lift (seedImportedProfiled profile p image state.machine.memory
    (h.registry state.machine.user))
  modify fun state => {state with machine := {state.machine with user := h.putRegistry state.machine.user registry}}

def attach (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other) : MachineHooks.M K User Unit :=
  attachProfiled {} p image h

theorem attach_profile_identity (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other) :
    attach p image h = attachProfiled {} p image h := rfl

/-- Runtime symbolic maps must wrap the imported queries: reversing this order
would lose freshly reserved function/vtable identities after successful casts. -/
def vtableHooks (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other)
    (base : VTableHooks Provenance (MachineHooks.State K User) C CallInstance (FnAbi MIR.TyId)) :
    VTableHooks Provenance (MachineHooks.State K User) C CallInstance (FnAbi MIR.TyId) :=
  VTableMachine.hooks (hooks p image h)
    (CompilerVTableQueries.hooks p.queries
      (CompilerCallPipeline.vtableHooks p.calls image (fun (state : MachineHooks.State K User) => state.machine.memory) base))

def virtualHooks (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other)
    (base : VirtualCalls.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra) :
    VirtualCalls.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra :=
  {base with compiler := CompilerCallPipeline.compilerHooks p.calls base.compiler, vtable := vtableHooks p image h base.vtable}

/-- Production compiler/vtable leaves require no runtime-operation scaffold. -/
def virtualLeaves (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other) (base : ExecutionCallLeaves.Virtual K User C) :
    ExecutionCallLeaves.Virtual K User C :=
  {base with compiler := CompilerCallPipeline.compilerHooks p.calls base.compiler, vtable := vtableHooks p image h base.vtable}

/-- Close virtual receiver/type selection, dynamic drop, caller location and
actual function-pointer resolution on the canonical call state. -/
def callHooks (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other)
    (virtual : VirtualCalls.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra)
    (budget : Nat)
    (base : CallHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId)) :
    CallHooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      Other Extern (FnAbi MIR.TyId) (ArgAbi MIR.TyId) :=
  FunctionPointers.callHooks h.functions (VirtualCalls.bind (virtualHooks p image h virtual) budget base)
/-- Unsize/upcast casts create and inspect actual symbolic vtables and actual
function pointers; compiler layout/type queries remain the source provider. -/
def castHooks (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other)
    (vtableBase : VTableHooks Provenance (MachineHooks.State K User) C CallInstance (FnAbi MIR.TyId))
    (base : CastHooks Provenance (MachineHooks.State K User) C D) :
    CastHooks Provenance (MachineHooks.State K User) C D :=
  let table := vtableHooks p image h vtableBase
  {FunctionPointerConsumers.cast h.functions base with
    vtableType := VTable.getPtrVTableType table
    vtablePointer := VTable.getPointer table
    vtableEntries := table.entries}

/-- Validity preserves FnVal.Other for source get_ptr_fn checks while compiler
virtual method entries retain full Instance identities. -/
def validityHooks (p : Prepared) (image : AllocationImage.Imported)
    (h : VTableMachine.Hooks K User Other)
    (vtableBase : VTableHooks Provenance (MachineHooks.State K User) C CallInstance (FnAbi MIR.TyId))
    (base : ValidityVisitor.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      (FnVal Other) (FnAbi MIR.TyId) Pad) :
    ValidityVisitor.Hooks Provenance (MachineHooks.State K User) C MachineHooks.FrameExtra
      (FnVal Other) (FnAbi MIR.TyId) Pad :=
  {base with vtable := FunctionPointerConsumers.vtable h.functions (vtableHooks p image h vtableBase)}
end Miri.Input.CompilerVTableMachine
