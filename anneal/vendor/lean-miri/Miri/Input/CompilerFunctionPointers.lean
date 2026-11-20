import Lean.Util.Profile
import Miri.Input.CompilerLifecyclePipeline
import Miri.Interpreter.FunctionPointers

/-! Actual compiler inlining attributes and imported GlobalAlloc::Function
identity bridge. Exported compiler function reservations use CTFE_ALLOC_SALT=0. -/
namespace Miri.Input.CompilerFunctionPointers
open Lean Miri.Memory Miri.Interpreter
structure Prepared where
  calls : CompilerCallPipeline.Prepared
  inlineAttributes : Array (CallInstance × Bool)

private abbrev FunctionKeyIndex := Std.HashMap (Nat × Nat) (Array Nat)
private abbrev AllocIdIndex := Std.HashMap UInt64 Bool
abbrev InlineIndex := Std.HashMap Nat (Array (CallInstance × Bool))

private def addFunctionKey (index : FunctionKeyIndex) (callee : CallInstance)
    (salt : Nat) (position : Nat) : FunctionKeyIndex :=
  let key := (callee.defId, salt)
  index.insert key ((index[key]?).getD #[] |>.push position)

private def functionKeyIndex (functions : Array FunctionPointers.FunctionEntry) : FunctionKeyIndex := Id.run do
  let mut index : FunctionKeyIndex := {}
  for (entry, position) in functions.toList.zipIdx do
    index := addFunctionKey index entry.callee entry.salt.val position
  return index

private def functionAllocIndex (registry : FunctionPointers.Registry Other) : AllocIdIndex := Id.run do
  let mut index : AllocIdIndex := {}
  for entry in registry.functions do index := index.insert entry.allocation.value true
  for (allocation, _) in registry.extras do index := index.insert allocation.value true
  return index

private def findFunctionKey (functions : Array FunctionPointers.FunctionEntry) (index : FunctionKeyIndex)
    (callee : CallInstance) (salt : Nat) : Option FunctionPointers.FunctionEntry := Id.run do
  let key := (callee.defId, salt)
  for position in (index[key]?).getD #[] do
    if let some entry := functions[position]? then
      if entry.callee == callee && entry.salt.val == salt then return some entry
  return none

structure InlineLookup (prepared : Prepared) where
  private mk ::
  private rows : Array (CallInstance × Bool)
  private index : InlineIndex
  private exactRows : rows = prepared.inlineAttributes

def InlineLookup.prepare (prepared : Prepared) : InlineLookup prepared := Id.run do
  let rows := prepared.inlineAttributes
  let mut index : InlineIndex := {}
  for entry in rows do
    let key := entry.1.defId
    index := index.insert key ((index[key]?).getD #[] |>.push entry)
  return ⟨rows,index,rfl⟩

def inlineNeverUsing (lookup : InlineLookup prepared) (callee : CallInstance) :
    Option Bool := Id.run do
  for (candidate, value) in (lookup.index[callee.defId]?).getD #[] do
    if candidate == callee then return some value
  return none

def prepare (calls : CompilerCallPipeline.Prepared) : Except String Prepared := do
  let raw ← (← (← calls.calls.program.input.raw.getObjVal? "compiler_runtime_queries").getObjVal? "instances").getArr?
  let ctx := LowerContext.ofDocument calls.calls.program.input
  let tables := calls.calls.program.compilerTables
  let mut entries := #[]
  let mut indexed : InlineIndex := {}
  for record in raw do
    let (callee,next) ← CompilerInstance.decode ctx tables record
    unless next.definitions == tables.definitions && next.typeConstants == tables.typeConstants do
      throw "function inline query requires unprepared shared compiler identities"
    let never ← (← record.getObjVal? "inline_never").getBool?
    let key := callee.defId
    let bucket := (indexed[key]?).getD #[]
    if let some (_,old) := bucket.find? (fun e : CallInstance × Bool => e.1 == callee) then
      unless old == never do throw "conflicting exact full-instance inline attribute"
    else
      entries := entries.push (callee,never)
      indexed := indexed.insert key (bucket.push (callee,never))
  return ⟨calls,entries⟩

private def lift (result : Except String A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler function pointers: {error}")

def hooks (p : Prepared) (image : AllocationImage.Imported)
    (base : FunctionPointers.Hooks K User Other) : FunctionPointers.Hooks K User Other :=
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.calls.symbols
  let inlineLookup := InlineLookup.prepare p
  {base with
    inlineNever := fun callee => lift do
      let some never := inlineNeverUsing inlineLookup callee
        | throw "exact full-instance inline attribute absent"
      pure never
    importedFunction := fun id => do
      lift (CompilerVTableRuntime.globalFunctionUsing p.calls.symbols lookup image (← get).machine.memory id)}

/-- Seed actual compiler-image function reservations before execution. Reject
conflicting salt-zero identities rather than pick an arbitrary matching body. -/
private def seedImportedImpl (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : FunctionPointers.Registry Other) :
    Except String (FunctionPointers.Registry Other) := do
  let mut registry := initial
  let mut keys := functionKeyIndex registry.functions
  let mut allocated := functionAllocIndex registry
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.calls.symbols
  let input := p.calls.calls.program.input
  let world? := input.compilerAllocIdWorld
  if let some world := world? then
    unless memory.sourceAllocIdWorldActive do
      throw "prepared function catalog requires the active source AllocId world"
    unless image.source == input.allocations.filter (·.status == .supported) do
      throw "prepared function catalog allocation image differs from its owning program"
    Miri.Input.validateCompilerAllocIdWorldRaw input.raw input.allocations (some world)
      |>.mapError fun error => s!"prepared AllocId world: {error}"
  else
    for (_,id) in memory.importedGlobalIds do
      if let some callee ← CompilerVTableRuntime.globalFunctionUsing p.calls.symbols lookup image memory id then
        if let some old := findFunctionKey registry.functions keys callee 0 then
          unless old.allocation == id do throw "conflicting imported salt-zero function allocations"
        else
          unless !(allocated.contains id.value) do
            throw "imported function allocation identity already assigned"
          keys := addFunctionKey keys callee 0 registry.functions.size
          allocated := allocated.insert id.value true
          registry := {registry with functions := registry.functions.push ⟨callee,⟨0,by decide⟩,id⟩}
  if let some world := world? then
    for row in world.dedupCatalog do
      if row.keyKind == .function then
        let keyRuntime ← AllocationImage.runtimeId memory row.keyAllocationId
        let some keyCallee ← CompilerVTableRuntime.globalFunctionUsing p.calls.symbols lookup image memory keyRuntime
          | throw "prepared function key witness is not a symbolic function"
        for result in row.salts do
          if saltBound : result.salt < 32 then
            let resultRuntime ← AllocationImage.runtimeId memory result.allocationId
            unless memory.sourceAllocIdForRuntime? resultRuntime == some result.sourceAllocId do
              throw "prepared function result raw AllocId does not match the active memory world"
            let some resultCallee ← CompilerVTableRuntime.globalFunctionUsing p.calls.symbols lookup image memory resultRuntime
              | throw "prepared function salt result is not a symbolic function"
            unless resultCallee == keyCallee do
              throw "prepared function salt result does not match its exact compiler Instance key"
            let salt : Fin 32 := ⟨result.salt, saltBound⟩
            if let some old := findFunctionKey registry.functions keys keyCallee result.salt then
              unless old.allocation == resultRuntime do throw "conflicting prepared function allocation for key/salt"
            else
              unless !(allocated.contains resultRuntime.value) do
                throw "prepared function allocation identity is already assigned"
              keys := addFunctionKey keys keyCallee result.salt registry.functions.size
              allocated := allocated.insert resultRuntime.value true
              registry := {registry with functions := registry.functions.push ⟨keyCallee,salt,resultRuntime⟩}
          else throw "prepared function salt is outside the source key domain"
  return registry

def seedImportedProfiled (profile : Lean.Options) (p : Prepared)
    (image : AllocationImage.Imported) (memory : MemoryState P E K)
    (initial : FunctionPointers.Registry Other) : Except String (FunctionPointers.Registry Other) :=
  profileit "startup.function_registry" profile fun _ =>
    seedImportedImpl p image memory initial

def seedImported (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : FunctionPointers.Registry Other) :
    Except String (FunctionPointers.Registry Other) :=
  seedImportedProfiled {} p image memory initial

theorem seedImported_profile_identity (p : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : FunctionPointers.Registry Other) :
    seedImported p image memory initial = seedImportedProfiled {} p image memory initial := rfl
/-- Attach the already imported compiler image before executing guest code.
This installs source dedup identities, never allocation addresses or fake bytes. -/
def attachProfiled (profile : Lean.Options) (p : Prepared) (image : AllocationImage.Imported)
    (h : FunctionPointers.Hooks K User Other) : MachineHooks.M K User Unit := do
  let state ← get
  let registry ← lift (seedImportedProfiled profile p image state.machine.memory
    (h.registry state.machine.user))
  modify fun state => {state with machine := {state.machine with
    user := h.putRegistry state.machine.user registry}}

def attach (p : Prepared) (image : AllocationImage.Imported)
    (h : FunctionPointers.Hooks K User Other) : MachineHooks.M K User Unit :=
  attachProfiled {} p image h

theorem attach_profile_identity (p : Prepared) (image : AllocationImage.Imported)
    (h : FunctionPointers.Hooks K User Other) :
    attach p image h = attachProfiled {} p image h := rfl

/-- Fully bind actual address operations and compiler function metadata under
one lawful concrete user-state embedding. Choices are explicit semantic inputs. -/
def runtimeHooks (p : Prepared) (image : AllocationImage.Imported)
    (lens : FunctionPointers.AddressLens User Payload)
    (pointer : PointerMachine.Hooks K Payload)
    (choices : AllocId → AllocAddresses.AddressRandomChoices)
    (base : FunctionPointers.Hooks K User Other) : FunctionPointers.Hooks K User Other :=
  FunctionPointers.pointerMachineVia lens pointer choices (hooks p image base)
end Miri.Input.CompilerFunctionPointers
