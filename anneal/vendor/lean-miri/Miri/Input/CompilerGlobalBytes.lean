import Lean.Util.Profile
import Miri.Input.AllocationImage
import Miri.Interpreter.GlobalByteMachine
import Miri.Input.Decoder

/-! Import exact TCX byte/salt identity evidence. Probes that miss the imported
compiler image do not create runtime globals; subsequent reservation stays lazy.
Completeness is checked against every qualifying immutable imported allocation,
not inferred from a catalog that merely happens to contain some literals. -/
namespace Miri.Input.CompilerGlobalBytes
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
structure Prepared where
  strType : TyId
  keys : Array (Array UInt8 × Fin 32 × AllocId)

private def hexBytes (value : String) : Except String (Array UInt8) := do
  let chars := value.toList.toArray
  unless chars.size % 2 == 0 do throw "global byte query has odd hex length"
  let digit := fun c =>
    if c ≥ '0' && c ≤ '9' then Except.ok (c.toNat - '0'.toNat)
    else if c ≥ 'a' && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error "global byte query has invalid hex"
  let mut bytes := #[]
  for i in [:chars.size / 2] do
    let some hi := chars[2*i]? | throw "global byte hex high digit absent"
    let some lo := chars[2*i+1]? | throw "global byte hex low digit absent"
    bytes := bytes.push (UInt8.ofNat (16*(← digit hi)+(← digit lo)))
  pure bytes

private def candidate (global : GlobalAllocation) : Except String (Option (Array UInt8)) := do
  let some (.memory allocation) := global.payload | return none
  if allocation.mutability != .Not || allocation.align != .ONE then return none
  unless allocation.provenanceMap.provenances.isEmpty do return none
  if allocation.len != 0 then
    let initialized ← allocation.initializationMask.isRangeInitialized
      (allocRange .ZERO allocation.byteSize) |>.mapError toString
    unless initialized.isOk do return none
  return some (← allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len |>.mapError toString)

/-- Attach immediately after graph import, before source runtime reservations.
The exported graph must be the same complete identity universe that was probed.
Compiler pool identity/serialization remains an explicit exporter trust boundary. -/
def prepare (program : LoweredProgram) (runtime : RuntimeMetadata)
    (memory : MemoryState P E K)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "global byte query metadata document mismatch"
  if memory.byteGlobalKeysReady || !memory.byteGlobalKeys.isEmpty then
    throw "global byte keys already initialized"
  let source ← program.input.raw.getObjVal? "compiler_global_byte_queries"
  unless (← source.getObjValAs? String "status") == "supported" do throw "global byte compiler queries unavailable"
  unless (← source.getObjValAs? Nat "salt_count") == 32 do throw "global byte salt support differs from pinned source"
  let mut keys := #[]
  if let some world := program.input.compilerAllocIdWorld then
    Miri.Input.validateCompilerAllocIdWorldRaw program.input.raw program.input.allocations
      (some world) |>.mapError fun error => s!"compiler AllocId world: {error}"
    unless memory.sourceAllocIdWorldActive do
      throw "prepared source AllocId world was not installed before byte-key attachment"
    let mut runtimeByGraph : Std.HashMap Nat AllocId := {}
    for (graphId, runtimeId) in memory.importedGlobalIds do
      if runtimeByGraph.contains graphId then throw "duplicate imported graph ID while preparing byte-key catalog"
      runtimeByGraph := runtimeByGraph.insert graphId runtimeId
    let mut seen : Std.HashMap (String × Nat) Bool := {}
    for row in world.dedupCatalog do
      if row.keyKind == .bytes then
        let some imageHex := row.byteImageHex | throw "prepared byte-key catalog row lacks its exact image"
        let bytes ← hexBytes imageHex
        for result in row.salts do
          if proof : result.salt < 32 then
            let some id := runtimeByGraph[result.allocationId]? | throw s!"missing runtime mapping for compiler allocation {result.allocationId}"
            unless memory.sourceAllocIdForRuntime? id == some result.sourceAllocId do
              throw "prepared byte result raw AllocId does not match the active memory world"
            if seen.contains (imageHex, result.salt) then
              throw "prepared source AllocId world contains duplicate byte key/salt results"
            seen := seen.insert (imageHex, result.salt) true
            keys := keys.push (bytes,⟨result.salt,proof⟩,id)
          else throw "prepared source AllocId world byte-key salt exceeds 31"
  else
    let covered ← (← source.getObjVal? "covered_allocation_ids").getArr?
    let ids ← covered.mapM Json.getNat?
    let expected := program.input.allocations.map (·.id)
    unless ids.size == expected.size && ids.all expected.contains && expected.all ids.contains do
      throw "global byte query coverage differs from imported graph"
    unless ids.toList.eraseDups.length == ids.size do throw "duplicate global byte coverage identity"
    let mapped ← ids.mapM (AllocationImage.runtimeId memory)
    let actual := memory.globals.map (·.allocId)
    unless mapped.size == actual.size && mapped.all actual.contains && actual.all mapped.contains do
      throw "global byte keys must attach before runtime global reservations"
    let mut candidates := #[]
    for global in memory.globals do
      if let some bytes ← candidate global then candidates := candidates.push (bytes,global.allocId)
    let mut seen : Array (Array UInt8) := #[]
    for row in ← (← source.getObjVal? "candidates").getArr? do
      let bytes ← hexBytes (← row.getObjValAs? String "bytes_hex")
      unless candidates.any (·.1 == bytes) do throw "global byte query contains a noncandidate allocation"
      if seen.contains bytes then throw "duplicate global byte query content"
      seen := seen.push bytes
      let salts ← (← row.getObjVal? "salts").getArr?
      unless salts.size == 32 do throw "global byte candidate omits salt outcomes"
      for index in [:32] do
        let some result := salts[index]? | throw "global byte salt result absent"
        unless (← result.getObjValAs? Nat "salt") == index do throw "global byte salt index mismatch"
        let allocation ← result.getObjVal? "existing_allocation"
        unless allocation == .null do
          let id ← AllocationImage.runtimeId memory (← allocation.getObjValAs? Nat "allocation_id")
          unless candidates.any (fun entry => entry.1 == bytes && entry.2 == id) do
            throw "global byte salt query refers to incompatible global contents"
          if proof : index < 32 then keys := keys.push (bytes,⟨index,proof⟩,id)
          else throw "global byte salt exceeds support"
    unless candidates.all (fun entry => seen.contains entry.1) do
      throw "global byte query omits imported candidate content"
  let strType ← (← source.getObjVal? "str_type").getObjValAs? Nat "type_id"
  let node ← runtime.node strType |>.mapError toString
  unless node.shapeStatus == .supported && node.shapeKind == .str do
    throw "global byte str type is not the compiler str primitive"
  pure ⟨strType,keys⟩

def attachProfiled (profile : Lean.Options) (program : LoweredProgram) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : MachineHooks.M K U Prepared := do
  let state ← get
  let prepared ← match profileit "startup.alloc_bytes" profile fun _ =>
      prepare program runtime state.machine.memory sourceEquality with
    | .ok value => pure value | .error error => throw (.unsupported error)
  modify fun state => {state with machine := {state.machine with memory :=
    {state.machine.memory with byteGlobalKeys := prepared.keys, byteGlobalKeysReady := true}}}
  pure prepared

def attach (program : LoweredProgram) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) :
    MachineHooks.M K U Prepared :=
  attachProfiled {} program runtime sourceEquality

theorem attach_profile_identity {K U : Type} (program : LoweredProgram) (runtime : RuntimeMetadata)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw)) :
    attach (K := K) (U := U) program runtime sourceEquality =
      attachProfiled (K := K) (U := U) {} program runtime sourceEquality := rfl

def strLayout (runtime : RuntimeMetadata) (prepared : Prepared) : MachineHooks.M K U LocalLayout :=
  match runtime.lookup prepared.strType with
  | .ok value => pure value | .error error => throw (.unsupported (toString error))
end Miri.Input.CompilerGlobalBytes
