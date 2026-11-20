import Miri.Interpreter.FunctionPointers

/-! Reservation identity is the erased concrete type, predicates and runtime salt.
A compiler CTFE salt-zero probe is not a witness for an arbitrary runtime cast:
pinned Miri chooses among 32 salts. Dense export IDs are not observable raw
AllocIds. Prepared catalogs certify the post-export TyCtxt continuation only;
missing keys must keep their Unsupported result. -/

/-! Source traits.rs symbolic vtable reservations. Vtables are not data bytes:
raw dereference is rejected by canonical MemoryState.getGlobalAlloc. -/
namespace Miri.Interpreter.VTableMachine
open Miri.ABI Miri.Memory
open MachineHooks (M State)
structure Entry where
  typeId : MIR.TyId
  dynamicType : Nat
  salt : Fin 32
  allocation : AllocId
structure Registry where
  entries : Array Entry

def Registry.empty : Registry := ⟨#[]⟩

/-- Merge the source-TCX symbolic vtable reservations into a fresh EvalWorld.
The key is the already erased/anonymized compiler type and dynamic predicate
identity together with Miri's allocation salt. -/
def Registry.mergePersistent (fresh live : Registry) : Except String Registry := do
  let sameKey (left right : Entry) :=
    left.typeId == right.typeId && left.dynamicType == right.dynamicType &&
      left.salt == right.salt
  let mut entries : Array Entry := #[]
  for entry in fresh.entries ++ live.entries do
    if let some old := entries.find? (fun old => sameKey old entry) then
      unless old.allocation == entry.allocation do
        throw "conflicting vtable AllocId for the same compiler key and salt"
    else
      if entries.any (fun old => old.allocation == entry.allocation) then
        throw "one vtable AllocId is assigned to multiple compiler keys or salts"
      entries := entries.push entry
  return ⟨entries⟩

/-- A source AllocId cannot denote both a symbolic vtable and either kind of
function pointer stored by FunctionPointers. -/
def Registry.ensureDisjointFromFunctions {Other : Type} (vtables : Registry)
    (functions : FunctionPointers.Registry Other) : Except String Unit := do
  for entry in vtables.entries do
    if functions.functions.any (·.allocation == entry.allocation) ||
        functions.extras.any (·.1 == entry.allocation) then
      throw "AllocId is shared by vtable and function-pointer registries"

/-- Restore the symbolic global metadata associated with persistent runtime
vtable identities. Existing fresh-world globals must be one well-formed vtable;
otherwise the same ID is already occupied by an incompatible allocation. -/
def Registry.restoreGlobals (vtables : Registry)
    (fresh live : MemoryState P E K) : Except String (MemoryState P E K) := do
  let mut memory := fresh
  for entry in vtables.entries do
    let present := memory.globalsForId entry.allocation
    if !present.isEmpty then
      unless present.size == 1 do
        throw "vtable AllocId appears more than once in fresh global memory"
      let some global := present[0]? | throw "vtable global lookup failed"
      unless global.kind == .vtable do
        throw "vtable AllocId collides with a non-vtable global"
    else
      if memory.hasIssuedId entry.allocation ||
          memory.live.any (·.1 == entry.allocation) ||
          memory.dead.any (·.allocId == entry.allocation) ||
          memory.hasImportedRuntimeId entry.allocation ||
          memory.byteGlobalKeys.any (·.2.2 == entry.allocation) ||
          memory.hasExtraFunctionId entry.allocation ||
          memory.hasVaListId entry.allocation then
        throw "vtable AllocId collides with a fresh-world allocation"
      let sourceGlobals := live.globalsForId entry.allocation
      unless sourceGlobals.size == 1 do
        throw "persistent vtable registry has missing or duplicate global metadata"
      let some source := sourceGlobals[0]? | throw "persistent vtable global lookup failed"
      unless source.kind == .vtable do
        throw "persistent vtable registry points to a non-vtable global"
      if live.live.any (·.1 == entry.allocation) ||
          live.dead.any (·.allocId == entry.allocation) ||
          live.byteGlobalKeys.any (·.2.2 == entry.allocation) ||
          live.hasExtraFunctionId entry.allocation ||
          live.hasVaListId entry.allocation then
        throw "persistent vtable AllocId collides with a non-global live allocation"
      memory := MemoryState.pushGlobal memory source
  return memory

structure Hooks (K User Other : Type) where
  functions : FunctionPointers.Hooks K User Other
  registry : User → Registry
  putRegistry : User → Registry → User
  target : RuntimeTargetDataLayout
  importedVTable : AllocId → M K User (Option (MIR.TyId × Nat))

/-- Source reserve_and_set_vtable_alloc key includes salt and both erased
compiler identities. Metadata uses source pointer alignment and size zero. -/
def reserve (h : Hooks K User Other) (ty : MIR.TyId) (dynType : Nat) (salt : Fin 32) : M K User AllocId := do
  let state ← get
  let registry := h.registry state.machine.user
  if let some entry := registry.entries.find? (fun e => e.typeId == ty && e.dynamicType == dynType && e.salt == salt) then
    return entry.allocation
  if state.machine.memory.sourceAllocIdWorldActive then
    throw (.unsupported "source vtable AllocId key/salt is not captured by the prepared raw-world profile")
  let align := h.target.defaultAddressSpacePointerSpec.pointerAlign
  let (memory,result) := state.machine.memory.reserveAllocId
  set {state with machine := {state.machine with memory}}
  let id ← match result with
    | .ok id => pure id
    | .error error => throw (.resourceExhaustion s!"vtable allocation ID: {reprStr error}")
  modify fun state => {state with machine := {state.machine with
    memory := MemoryState.pushGlobal state.machine.memory ⟨id,.vtable,.ZERO,align,.Not,some .vtable⟩
    user := h.putRegistry state.machine.user {registry with entries := registry.entries.push ⟨ty,dynType,salt,id⟩}}}
  return id

def globalVTable (h : Hooks K User Other) (id : AllocId) : M K User (Option (MIR.TyId × Nat)) := do
  if let some entry := (h.registry (← get).machine.user).entries.find? (·.allocation == id) then
    return some (entry.typeId,entry.dynamicType)
  if let .ok info := (← get).machine.memory.getAllocInfo id then
    if info.kind != .vtable then return none
  h.importedVTable id

/-- Compiler erase/monomorphic/predicate/method queries stay in base; all
symbolic allocation, provenance, salt and address operations are real state. -/
def hooks (h : Hooks K User Other)
    (base : VTableHooks Provenance (State K User) C CallInstance ABI) :
    VTableHooks Provenance (State K User) C CallInstance ABI :=
  {FunctionPointers.vtableHooks h.functions base with
    target := h.target.base
    globalVTable := fun _ => globalVTable h
    globalSalt := fun _ => return (← h.functions.chooseSalt).val
    reserveVTable := fun _ ty dynType salt => do
      if bound : salt < 32 then reserve h ty dynType ⟨salt,bound⟩
      else throw (.invalidProgram "vtable source salt outside 0..32")
    globalRootPointer := fun _ id =>
      return (← FunctionPointers.rootPointer h.functions id).withOptionalProvenance}
end Miri.Interpreter.VTableMachine
