import Lean.Util.Profile
import Miri.Input.CompilerProviders
import Miri.Input.Decoder
import Miri.Interpreter.IntrinsicSymbolsMachine

/-! Imported rustc GlobalAlloc::TypeId nodes seed the actual intrinsic symbol
registry before runtime reserve_and_set_type_id_alloc. Input allocation IDs and
runtime allocation IDs are connected only by the imported memory map. -/
namespace Miri.Input.CompilerIntrinsicSymbols
open Lean Miri.ABI Miri.Memory Miri.Interpreter

private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)

def typeHash (p : CompilerProviders.Prepared) (ty : MIR.TyId) : Except String U128 := do
  let source ← p.runtime.node ty |>.mapError toString
  let some facts := source.compilerFacts | throw "compiler TypeId hash evidence missing"
  let query ← facts.payload.getObjVal? "type_id_hash"
  unless (← query.getObjValAs? String "status") == "supported" do
    throw "compiler TypeId hash query unsupported"
  let text ← (← query.getObjVal? "value").getStr?
  unless !text.isEmpty && text.toList.all (fun c => c >= '0' && c <= '9') do
    throw "invalid compiler TypeId hash decimal encoding"
  let some value := text.toNat? | throw "invalid compiler TypeId hash value"
  unless value < 2^128 do throw "compiler TypeId hash exceeds u128"
  pure (BitVec.ofNat 128 value)

def importedTypeId (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Except String (Option MIR.TyId) := do
  let some info := memory.findGlobal? id | return none
  if info.kind != .typeId then return none
  let node ← image.sourceNode memory id
  unless node.status == .supported do throw "compiler TypeId allocation evidence unresolved"
  let some (.typeId ty) := node.data | throw "runtime TypeId allocation lacks typed compiler TypeId payload"
  let _ ← p.runtime.node ty |>.mapError toString
  pure (some ty)

private def addTypeId (registry : IntrinsicSymbolsMachine.Registry) (id : AllocId) (ty : MIR.TyId) :
    Except String IntrinsicSymbolsMachine.Registry := do
  if let some (previous,_) := registry.typeIds.find? (·.2 == ty) then
    unless previous == id do throw "conflicting compiler TypeId reservation identities"
    pure registry
  else
    unless !(registry.typeIds.any (·.1 == id)) do
      throw "one runtime allocation assigned distinct compiler TypeId identities"
    pure {registry with typeIds := registry.typeIds.push (id,ty)}

def seedImported (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (initial : IntrinsicSymbolsMachine.Registry) :
    Except String IntrinsicSymbolsMachine.Registry := do
  let input := p.program.input
  if let some world := input.compilerAllocIdWorld then
    unless RuntimeMetadata.JsonReflexivity.matchesRightOr (some p.sourceEquality) input.raw do
      throw "prepared TypeId catalog runtime metadata differs from its owning program"
    unless memory.sourceAllocIdWorldActive do
      throw "prepared TypeId catalog requires the active source AllocId world"
    unless image.source == input.allocations.filter (·.status == .supported) do
      throw "prepared TypeId catalog allocation image differs from its owning program"
    Miri.Input.validateCompilerAllocIdWorldRaw input.raw input.allocations (some world)
      |>.mapError fun error => s!"prepared AllocId world: {error}"
    -- Build the prepared key set independently of existing machine state so
    -- preseeded entries cannot validate themselves.
    let mut registry := {initial with typeIds := #[]}
    for row in world.dedupCatalog do
      if row.keyKind == .typeId then
        unless row.salts.size == 1 do throw "prepared TypeId key lacks its unique salt-zero outcome"
        let some result := row.salts[0]? | throw "prepared TypeId salt-zero outcome is absent"
        unless result.salt == 0 && result.allocationId == row.keyAllocationId do
          throw "prepared TypeId catalog row is not its exact salt-zero key witness"
        let id ← AllocationImage.runtimeId memory result.allocationId
        unless memory.sourceAllocIdForRuntime? id == some result.sourceAllocId do
          throw "prepared TypeId result raw AllocId does not match the active memory world"
        let some ty ← importedTypeId p image memory id
          | throw "prepared TypeId key witness is not an imported TypeId global"
        registry ← addTypeId registry id ty
    for entry in initial.typeIds do
      unless registry.typeIds.contains entry do
        throw "preexisting TypeId registry entry is absent from the validated prepared key catalog"
    pure registry
  else
    let mut registry := initial
    for (_,id) in memory.importedGlobalIds do
      if let some ty ← importedTypeId p image memory id then
        registry ← addTypeId registry id ty
    pure registry

def attachProfiled (profile : Lean.Options) (p : CompilerProviders.Prepared)
    (image : AllocationImage.Imported)
    (registry : IntrinsicSymbolsMachine.Access U) : MachineHooks.M K U Unit := do
  let state ← get
  let actual ← match profileit "startup.typeid_registry" profile fun _ =>
      seedImported p image state.machine.memory (registry.get state.machine.user) with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler TypeId globals: {reason}")
  modify fun state => {state with machine := {state.machine with user := registry.put state.machine.user actual}}

def attach (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (registry : IntrinsicSymbolsMachine.Access U) : MachineHooks.M K U Unit :=
  attachProfiled {} p image registry

theorem attach_profile_identity {K U : Type} (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (registry : IntrinsicSymbolsMachine.Access U) :
    attach (K := K) (U := U) p image registry =
      attachProfiled (K := K) (U := U) {} p image registry := rfl

/-- Missing hash/region compiler metadata remains a source query failure. The
registry preparation above must execute before the first dynamic reservation. -/
def typeIdLeaves (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) :
    IntrinsicSymbolsMachine.TypeIdLeaves K U C :=
  { hasErasableRegions := fun _ ty =>
      lift (CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context ty "has_erasable_regions")
    typeHash := fun _ ty => lift (typeHash p ty)
    u128Layout := fun _ => lift (p.primitiveLayout "u128")
    unitLayout := fun _ => lift (p.primitiveLayout "unit")
    importedTypeId := fun id => do lift (importedTypeId p image (← get).machine.memory id) }
end Miri.Input.CompilerIntrinsicSymbols
