import Miri.Input.Model
import Miri.Input.Decoder
import Miri.Memory.MemoryState

/-! Validated installation of the optional prepared post-export rustc
allocation-ID world. This keeps exporter graph IDs, dense Lean runtime IDs,
and raw rustc IDs as three separate namespaces. -/
namespace Miri.Input.CompilerAllocIdWorld
open Miri.Memory

set_option autoImplicit false in
def install {P E K : Type} (raw : Lean.Json) (world? : Option CompilerAllocIdWorld) (nodes : Array AllocationNode)
    (memory : MemoryState P E K) : Except String (MemoryState P E K) := do
  Miri.Input.validateCompilerAllocIdWorldRaw raw nodes world?
  let some world := world? | return memory
  if memory.sourceAllocIdWorldActive then throw "source AllocId world is already installed"
  if !memory.live.isEmpty || !memory.dead.isEmpty || !memory.extraFnPtrIds.isEmpty ||
      !memory.vaListIds.isEmpty || !memory.byteGlobalKeys.isEmpty || memory.byteGlobalKeysReady then
    throw "source AllocId world must be attached before any runtime allocation or byte-key setup"
  unless memory.sourceAllocIdByRuntime.isEmpty && memory.runtimeBySourceAllocId.isEmpty &&
      memory.opaqueSourceGlobalIds.isEmpty do
    throw "source AllocId runtime crosswalk was partially initialized"
  let supportedNodeCount := nodes.filter (·.status == .supported) |>.size
  unless memory.importedGlobalIds.size == supportedNodeCount && memory.globals.size == supportedNodeCount do
    throw "source AllocId world must cover every supported already-imported allocation"
  let mut runtimeByExport : Std.HashMap Nat AllocId := {}
  for (graphId, runtimeId) in memory.importedGlobalIds do
    if runtimeByExport.contains graphId then throw "duplicate imported exporter graph identity"
    runtimeByExport := runtimeByExport.insert graphId runtimeId
  let mut nodeIndexByExport : Std.HashMap Nat Nat := {}
  for (node, index) in nodes.toList.zipIdx do
    if nodeIndexByExport.contains node.id then throw "duplicate source AllocId allocation node graph identity"
    nodeIndexByExport := nodeIndexByExport.insert node.id index
  let mut byRuntime : Array (AllocId × UInt64) := #[]
  let mut bySource : Array (UInt64 × AllocId) := #[]
  let mut seenRuntime : Std.HashMap Nat Bool := {}
  let mut opaqueRawIds : Array UInt64 := #[]
  unless world.lastReservedSourceAllocId == world.finalSentinelSourceAllocId &&
      world.lastReservedSourceAllocId.toNat + 1 == world.nextSourceAllocId.toNat &&
      world.rawPool.size == world.lastReservedSourceAllocId.toNat do
    throw "source AllocId world frontier/pool invariant failed before installation"
  for (row, index) in world.rawPool.toList.zipIdx do
    if row.sourceAllocId.toNat != index + 1 then
      throw "source AllocId pool is not a contiguous prefix"
    match row.status with
    | .dangling =>
      unless row.kind == .dangling && row.allocationId.isNone do
        throw "source AllocId dangling pool row has a global payload"
    | .opaque =>
      unless row.kind != .dangling && row.allocationId.isNone do
        throw "source AllocId opaque pool row has an invalid shape"
      if let some graphId := row.opaqueAllocationId then
        let some nodeIndex := nodeIndexByExport[graphId]? | throw "opaque source AllocId graph node is absent"
        let some node := nodes[nodeIndex]? | throw "opaque source AllocId graph node index is absent"
        unless node.sourceAllocId == some row.sourceAllocId && node.status != .supported do
          throw "opaque source AllocId graph node does not match its unsupported raw identity"
      opaqueRawIds := opaqueRawIds.push row.sourceAllocId
    | .serialized =>
      unless row.kind != .dangling do throw "source AllocId serialized row is marked dangling"
      let some graphId := row.allocationId | throw "source AllocId serialized pool row lacks graph identity"
      let some nodeIndex := nodeIndexByExport[graphId]? | throw "source AllocId graph node is absent"
      let some node := nodes[nodeIndex]? | throw "source AllocId graph node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId do
        throw "source AllocId graph node has a different raw identity"
      let some runtimeId := runtimeByExport[graphId]? | throw "source AllocId graph node was not imported"
      if seenRuntime.contains runtimeId.value.toNat then throw "duplicate source AllocId runtime identity"
      seenRuntime := seenRuntime.insert runtimeId.value.toNat true
      byRuntime := byRuntime.push (runtimeId, row.sourceAllocId)
      bySource := bySource.push (row.sourceAllocId, runtimeId)
  unless byRuntime.size == memory.importedGlobalIds.size do
    throw "source AllocId world does not cover every imported runtime global"
  for (_, runtimeId) in memory.importedGlobalIds do
    unless seenRuntime.contains runtimeId.value.toNat do
      throw "imported runtime global has no source AllocId witness"
  return MemoryState.setSourceAllocIdCrosswalks
      { memory with
        sourceAllocIdWorldActive := true
        sourceAllocIdNext := world.nextSourceAllocId
        sourceAllocIdExhausted := false
        opaqueSourceGlobalIds := opaqueRawIds
        sourceByteImageFamilyComplete := world.completeKeyFamilies.contains .bytes }
      byRuntime bySource

end Miri.Input.CompilerAllocIdWorld
