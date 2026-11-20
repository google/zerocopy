import Lean

/-! Shared JSON payload graph transport. Nodes are resolved once in topological
order, and resolved Json values are reused directly at every reference site. -/
namespace Miri.Input.SharedPayloads

open Lean

private def markerKey : String := "$lean_miri_shared_ref"

private def pathKey (path key : String) : String :=
  if path.isEmpty then key else path ++ "." ++ key

private def objectFields (value : Json) : Except String (Array (String × Json)) := do
  match value with
  | .obj fields => pure fields.toList.toArray
  | _ => throw "expected object"

private def field (value : Json) (key path : String) : Except String Json := do
  value.getObjVal? key |>.mapError fun error =>
    s!"{path}: missing/invalid field `{key}` ({error})"

private def exactObjectFields (value : Json) (expected : List String)
    (path description : String) : Except String (Array (String × Json)) := do
  let fields ← objectFields value |>.mapError fun _ => s!"{path}: {description} must be an object"
  let names := fields.map Prod.fst
  unless names.size == expected.length && expected.all names.contains do
    throw s!"{path}: {description} has unexpected or missing fields"
  pure fields

/-- Resolved graph output. `nodeResolutionCount` is the number of catalog nodes
processed by the one-pass topological resolver. -/
structure ResolvedGraph where
  nodes : Array Json
  root : Json
  nodeResolutionCount : Nat
  deriving Inhabited

private def parseReference (value : Json) (path : String) : Except String Nat := do
  let _ ← exactObjectFields value [markerKey] path "shared reference"
  let descriptor ← field value markerKey path
  let index ← descriptor.getNat? |>.mapError fun error =>
    s!"{pathKey path markerKey}: expected unsigned integer node ID ({error})"
  pure index

private partial def resolveValue (available : Array Json) (totalCount limit : Nat)
    (value : Json) (path : String) : Except String (Option Json) := do
  match value with
  | .obj fields =>
    if (value.getObjVal? markerKey).isOk then
      let index ← parseReference value path
      if index >= available.size then
        if index >= totalCount then
          throw s!"{pathKey path markerKey}: node reference {index} is out of range"
        else if index >= limit then
          throw s!"{pathKey path markerKey}: node reference {index} is a forward reference"
        else
          throw s!"{pathKey path markerKey}: node reference {index} is out of range"
      match available[index]? with
      | some node => pure (some node)
      | none => throw s!"{pathKey path markerKey}: node reference {index} is out of range"
    else do
      let mut resolved := fields
      let mut changed := false
      for (key, child) in fields.toList do
        if let some replacement ← resolveValue available totalCount limit child (pathKey path key) then
          resolved := resolved.insert key replacement
          changed := true
      if changed then pure (some (.obj resolved)) else pure none
  | .arr values => do
    let mut resolved := #[]
    let mut changed := false
    for h : index in [:values.size] do
      have indexBound : index < values.size := Membership.mem.upper h
      let child := values[index]'indexBound
      match ← resolveValue available totalCount limit child s!"{path}[{index}]" with
      | none =>
        if changed then resolved := resolved.push child
      | some replacement =>
        if !changed then
          resolved := values.extract 0 index
          changed := true
        resolved := resolved.push replacement
    if changed then pure (some (.arr resolved)) else pure none
  | _ => pure none

private def parseCatalog (catalog : Json) : Except String (Array Json) := do
  let _ ← exactObjectFields catalog ["schema_version", "nodes"] "$.shared_payloads" "catalog"
  let version ← field catalog "schema_version" "$.shared_payloads"
  let version ← version.getNat? |>.mapError fun error =>
    s!"$.shared_payloads.schema_version: expected unsigned integer ({error})"
  unless version == 2 do
    throw "$.shared_payloads.schema_version: unsupported shared-payload schema version (expected 2)"
  let nodesValue ← field catalog "nodes" "$.shared_payloads"
  nodesValue.getArr? |>.mapError fun error =>
    s!"$.shared_payloads.nodes: expected array ({error})"

/-- Resolve the mandatory v2 shared-payload graph and strip its transport field.
Every node is resolved exactly once in array order; node references can only
point to earlier entries, while document references can point anywhere. -/
def resolveGraph (document : Json) : Except String ResolvedGraph := do
  let fields ← objectFields document |>.mapError fun _ =>
    "$: document must be an object containing shared_payloads"
  if fields.any (fun (key, _) => key == markerKey) then
    throw "$: a shared reference cannot occupy the document root"
  let some catalog := (document.getObjVal? "shared_payloads").toOption
    | throw "$.shared_payloads: missing mandatory shared-payload graph"
  let rawNodes ← parseCatalog catalog
  let mut nodes := #[]
  for (node, index) in rawNodes.toList.zipIdx do
    let nodePath := s!"$.shared_payloads.nodes[{index}]"
    let resolved ← resolveValue nodes rawNodes.size index node nodePath
    nodes := nodes.push (resolved.getD node)
  let mut rootFields := #[]
  for (key, value) in fields do
    if key == "shared_payloads" then continue
    let resolved ← resolveValue nodes nodes.size nodes.size value (pathKey "$" key)
    rootFields := rootFields.push (key, resolved.getD value)
  pure {
    nodes := nodes
    root := Json.mkObj rootFields.toList
    nodeResolutionCount := nodes.size
  }

/-- Resolve a shared graph, returning only its business document for decoder
callers that do not need the resolved node table. -/
def resolveCatalog (document : Json) : Except String Json := do
  return (← resolveGraph document).root

end Miri.Input.SharedPayloads
