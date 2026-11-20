import Miri.Input.LowerMIR
import Miri.Input.RuntimeMetadata
import Miri.Memory.MemoryState

/-! Compiler global images are decoded into actual Allocation records only
through checked memory APIs. Export IDs never become runtime AllocIds; every
relocation is remapped through MemoryState.importedGlobalIds. Import is not
runtime access: getGlobalAlloc retains lazy initializer and machine-hook order.
Source: rustc_middle/mir/interpret/{allocation,mod}.rs and interpret/memory.rs.
-/
namespace Miri.Input
open Miri.ABI Miri.Memory

namespace AllocationImage
abbrev Result := Except String

private def checked (value : Except ε α) (showError : ε → String) : Result α :=
  value.mapError showError

private def size (n : Nat) : Result Size :=
  if n < 2^64 then pure (.ofBytes (UInt64.ofNat n)) else throw "allocation size exceeds u64"

private def bytes (hex : String) : Result (Array UInt8) := do
  let chars := hex.toList.toArray
  unless chars.size % 2 == 0 do throw "odd hexadecimal byte count"
  let digit (c : Char) : Result Nat :=
    if c ≥ '0' && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if c ≥ 'a' && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if c ≥ 'A' && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw "invalid hexadecimal allocation byte"
  let mut out := #[]
  for i in [:chars.size / 2] do
    let some hi := chars[2*i]? | throw "missing hexadecimal high nibble"
    let some lo := chars[2*i+1]? | throw "missing hexadecimal low nibble"
    out := out.push (UInt8.ofNat (16 * (← digit hi) + (← digit lo)))
  pure out

private def mutability : MemoryMutability → Result Memory.Mutability
  | .mutable => pure .Mut
  | .immutable => pure .Not
  | .unknown tag => throw s!"unknown allocation mutability {tag}"

/-- Resolve source graph identity; never use the decoder's reversible +1
embedding of export IDs as runtime allocation identity. -/
def runtimeId (memory : MemoryState P E K) (exportId : Input.AllocationId) : Result AllocId :=
  match memory.runtimeIdForExport? exportId with
  | some id => pure id
  | none => throw s!"missing runtime mapping for compiler allocation {exportId}"

def provenance (memory : MemoryState P E K) (exportId : Input.AllocationId)
    (immutable sharedRef : Bool) : Result CtfeProvenance := do
  if immutable && !sharedRef then throw "immutable CTFE provenance must also be shared"
  checked (CtfeProvenance.fromParts (← runtimeId memory exportId, immutable, sharedRef))
    (fun e => reprStr e)

/-- Preserve exact storage, initialized bytes, relocation offsets and CTFE
flags. Arbitrary initialization and pointer provenance are imported independently;
no pointer-containing byte range is silently cleared or normalized. -/
def decode (target : RuntimeTargetDataLayout) (memory : MemoryState P E K)
    (source : AllocationMemory) : Result (Allocation CtfeProvenance Unit) := do
  let raw ← bytes source.bytesHex
  unless raw.size == source.sizeBytes do throw "allocation byte size mismatch"
  let alignment ← checked (RuntimeMetadata.alignment source.alignBytes) toString
  let finalMutability ← mutability source.mutability
  let pointerSize ← checked (target.pointerSizeIn target.defaultAddressSpace) toString
  let mut cursor := 0
  for chunk in source.initializationRanges do
    unless chunk.startBytes == cursor && chunk.endBytesExclusive ≥ chunk.startBytes && chunk.endBytesExclusive ≤ raw.size do
      throw "initialization ranges overlap, leave gaps, or exceed allocation"
    cursor := chunk.endBytesExclusive
  unless cursor == raw.size do throw "initialization ranges do not cover allocation"
  let mut endOfPointer := 0
  for relocation in source.relocations do
    let start := relocation.storageOffsetBytes
    let finish := start + pointerSize.bytes.toNat
    unless start ≥ endOfPointer && finish ≤ raw.size do throw "overlapping or out-of-bounds relocation"
    endOfPointer := finish
    let encoded ← bytes relocation.targetOffsetEncodedBytes
    unless encoded.size == pointerSize.bytes.toNat && encoded == raw.extract start finish do
      throw "relocation bytes disagree with allocation storage or pointer width"
  let mut entries := #[]
  for relocation in source.relocations do
    let prov ← provenance memory relocation.target relocation.immutable relocation.sharedRef
    entries := entries.push (← size relocation.storageOffsetBytes, prov)
  let provenance ← checked (ProvenanceMap.fromPresortedPtrs entries) (fun e => reprStr e)
  let mut mask := InitMask.new (← size raw.size) true
  for chunk in source.initializationRanges do
    mask ← checked (mask.setRange (allocRange (← size chunk.startBytes)
      (← size (chunk.endBytesExclusive - chunk.startBytes))) chunk.initialized) toString
  let allocation ← checked (Allocation.fromCompilerImage raw alignment finalMutability mask provenance pointerSize) toString
  let readback ← checked (allocation.inspectWithUninitAndPtrOutsideInterpreter 0 raw.size) toString
  unless readback == raw do throw "allocation reconstruction changed compiler bytes"
  for i in [:raw.size] do
    let actual ← checked (allocation.initializationMask.get (← size i)) toString
    let some expected := source.initializationRanges.find? (fun chunk => chunk.startBytes ≤ i && i < chunk.endBytesExclusive)
      | throw "initialization evidence missing byte"
    unless actual == expected.initialized do throw "allocation reconstruction changed initialization"
  return allocation

/-- Source static predicates/layout queries are independent of initializer
materialization. They cannot be inferred from an initializer or target triple. -/
structure StaticInfo where
  size : Size
  align : Align
  mutability : Memory.Mutability
  isStatic : Bool
  foreignItem : Bool

structure Queries where
  staticInfo : StaticAllocation → Result StaticInfo

private def sourcePositions (source : Array AllocationNode) :
    KeyedArray Nat (Nat × Nat) Prod.fst := Id.run do
  let mut positions : KeyedArray Nat (Nat × Nat) Prod.fst := .empty Prod.fst
  for position in [:source.size] do
    if let some node := source[position]? then
      -- `Array.find?` returns the first matching row. Retaining only the first
      -- source position preserves that behavior for manually built images
      -- with duplicate source IDs.
      unless positions.contains node.id do
        positions := positions.push (node.id, position)
  return positions

structure SourceIndex (source : Array AllocationNode) where
  private mk ::
  positions : KeyedArray Nat (Nat × Nat) Prod.fst
  exact : positions = sourcePositions source

namespace SourceIndex

private def build (source : Array AllocationNode) : SourceIndex source :=
  ⟨sourcePositions source, rfl⟩

private def find? {source : Array AllocationNode} (index : SourceIndex source)
    (sourceId : Nat) : Option AllocationNode := do
  let (_, position) ← index.positions.find? sourceId
  source[position]?

end SourceIndex

structure Imported where
  source : Array AllocationNode
  initializers : Array (Nat × Allocation CtfeProvenance Unit)
  private sourceIndex : Option (SourceIndex source) := none

namespace Imported

/-- Construct a manually assembled image without a cached source lookup index.
This keeps direct test images compatible with the historical array lookup. -/
def ofSource (source : Array AllocationNode)
    (initializers : Array (Nat × Allocation CtfeProvenance Unit)) : Imported :=
  { source := source, initializers := initializers }

/-- Construct a manually assembled image with a fresh index tied to this exact
source array. Replacing the source cannot reuse this dependent cache. -/
def withSourceIndex (source : Array AllocationNode)
    (initializers : Array (Nat × Allocation CtfeProvenance Unit)) : Imported :=
  { source := source, initializers := initializers,
    sourceIndex := some (SourceIndex.build source) }

private def findSourceNode? (image : Imported) (sourceId : Nat) : Option AllocationNode :=
  match image.sourceIndex with
  | some index => SourceIndex.find? index sourceId
  | none => image.source.find? (·.id == sourceId)

end Imported

structure ImportResult (P E K : Type) where
  memory : MemoryState P E K
  outcome : Result Imported

private def metadata (target : RuntimeTargetDataLayout) (queries : Queries)
    (node : AllocationNode) : Result (GlobalAllocationKind × Size × Align × Memory.Mutability) := do
  unless node.status == .supported do throw s!"compiler allocation {node.id} has unresolved status {repr node.status}"
  let consistent := match node.kind, node.data with
    | .memory, some (.memory _) | .function, some (.function _) | .static, some (.static _)
    | .vtable, some (.vtable _) | .typeId, some (.typeId _) => true
    | _, _ => false
  unless consistent do throw "compiler allocation kind/payload mismatch"
  match node.data with
  | some (.memory image) => return (.memory, ← size image.sizeBytes,
      ← checked (RuntimeMetadata.alignment image.alignBytes) toString, ← mutability image.mutability)
  | some (.static value) =>
    let info ← queries.staticInfo value
    return (.static, info.size, info.align, info.mutability)
  | some (.function _) => pure (.function, .ZERO, .ONE, .Not)
  | some (.vtable _) =>
    let align ← checked (target.pointerAlignIn target.defaultAddressSpace) toString
    pure (.vtable, .ZERO, align.abi, .Not)
  | some (.typeId _) => pure (.typeId, .ZERO, .ONE, .Not)
  | none => throw s!"compiler allocation {node.id} has no typed payload"

/-- Register identities before reconstructing any bytes: cycles and forward
relocations therefore resolve through a complete source→runtime map. A failure
returns all IDs already consumed by the source allocation-ID supply. -/
def importGraph [DecidableEq K] (target : RuntimeTargetDataLayout)
    (definitions : Array DefinitionId) (queries : Queries) (nodes : Array AllocationNode)
    (initial : MemoryState P E K) : ImportResult P E K := Id.run do
  let mut memory := initial
  for node in nodes do
    let (kind, size, align, mutable) ← match metadata target queries node with
      | .ok value => pure value
      | .error e => return ⟨memory, .error e⟩
    let registered := MemoryLifecycle.registerImportedGlobal memory () node.id kind size align mutable
    memory := registered.memory
    match registered.outcome with
    | .error e => return ⟨memory, .error (toString e)⟩
    | .ok _ => pure ()
  let mut initializers := #[]
  for node in nodes do
    let id ← match runtimeId memory node.id with
      | .ok value => pure value
      | .error e => return ⟨memory, .error e⟩
    let payload ← match (do
        match node.data with
        | some (.memory source) => return (GlobalAllocationPayload.memory (← decode target memory source), none)
        | some (.static source) =>
          let info ← queries.staticInfo source
          let definition ← lookupDefinitionId definitions source.definitionId
          if source.globalInfo.map (·.foreignItem) |>.getD false then
            -- rustc represents an extern static as GlobalAlloc::Static, but
            -- Miri resolves its pointer through extern_static_pointer rather
            -- than evaluating an initializer. Preserve the compiler global
            -- identity and foreign-item flag without inventing backing bytes.
            return (.static definition info.isStatic source.threadLocal true, none)
          else
            let some sourceInitializer := source.initializer
              | throw "non-foreign static is missing its compiler initializer image"
            let initializer ← decode target memory sourceInitializer
            return (.static definition info.isStatic source.threadLocal false, some (definition, initializer))
        | some (.function _) => pure (.function, none)
        | some (.vtable _) => pure (.vtable, none)
        | some (.typeId _) => pure (.typeId, none)
        | none => throw "missing compiler allocation payload"
      : Result (GlobalAllocationPayload × Option (Nat × Allocation CtfeProvenance Unit))) with
      | .ok value => pure value
      | .error e => return ⟨memory, .error e⟩
    if let some initializer := payload.2 then initializers := initializers.push initializer
    memory := memory.setGlobalPayload id payload.1
  return ⟨memory, .ok (Imported.withSourceIndex nodes initializers)⟩

/-- Recover the exact compiler node for a runtime global identity. Function,
vtable, type-id, static and TLS leaf queries consume this retained metadata;
they are never approximated by interpreting memory bytes as a code pointer. -/
def Imported.sourceNode (image : Imported) (memory : MemoryState P E K)
    (id : AllocId) : Result AllocationNode := do
  let some sourceId := memory.importedGraphIdForRuntime? id
    | throw "runtime global has no imported source identity"
  let some node := image.findSourceNode? sourceId
    | throw "imported global source node is unavailable"
  pure node

/-- Reuse an exported successful eval_static_initializer query at the source
lazy-access hook. It remains fallible and never fabricates external/TLS data. -/
def Imported.evaluateStaticInitializer (image : Imported) (state : S) (definition : Nat) :
    MachineHookResult S (Allocation CtfeProvenance Unit) :=
  match image.initializers.find? (·.1 == definition) with
  | some (_, allocation) => ⟨state, .ok allocation⟩
  | none => ⟨state, .error s!"missing compiler static initializer query for definition {definition}"⟩

end AllocationImage
end Miri.Input
