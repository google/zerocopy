import Miri.Input.SharedPayloads

/-! Optional structural-hash memo for already resolved transport graphs.
The authoritative resolver still owns all input checks. Cached keys use the
same Json equality and hash; collisions are never treated as equality. A raw
noncanonical object, or an unexpected shape, disables this optimization.
-/
namespace Miri.Input.JsonTraversalCache
open Lean

structure Key where
  private mk ::
  value : Json
  digest : UInt64
  /-- Existing exporter node ID. Inline nodes are not independently memoized. -/
  id : Option Nat

instance : BEq Key where
  beq a b := a.value == b.value
instance : Hashable Key where
  hash a := a.digest

theorem Key.beq_eq (a b : Key) : (a == b) = (a.value == b.value) := rfl

inductive Node where
  | cached (key : Key) (children : Array Node)
  | uncached (value : Json)

def Node.value : Node → Json
  | .cached key _ => key.value
  | .uncached value => value

def Node.key : Node → Key
  | .cached key _ => key
  | .uncached value => ⟨value, hash value, none⟩

/-- Identity keys are confined to a single document traversal. Sharing is
supplied by the exporter, never inferred from hashes. -/
inductive IdentityKey where
  | node (id : Nat)
  | raw (key : Key)
  deriving BEq

instance : Hashable IdentityKey where
  hash
    | .node id => mixHash 31 (hash id)
    | .raw key => hash key

def Node.identity : Node → IdentityKey
  | .cached key _ => match key.id with
    | some id => .node id
    | none => .raw key
  | .uncached value => .raw ⟨value, hash value, none⟩

/-- Inline children are traversed under their shared parent, without creating
unique memo entries that can never be hit. Raw fallback keeps structural reuse. -/
def Node.shouldMemo : Node → Bool
  | .cached key _ => key.id.isSome
  | .uncached _ => true

private def Node.withId (node : Node) (id : Nat) : Node :=
  match node with
  | .cached key children =>
    if key.id.isSome then node else .cached { key with id := some id } children
  | .uncached _ => node

theorem uncached_hash_eq (value : Json) :
    hash (Node.uncached value).key = hash value := rfl

/-- Child positions follow the actual array or object's inorder traversal.
Only the internal builder supplies cached children; an absent child falls back
to the real JSON value, preserving checks rather than treating it as visited. -/
def Node.child (node : Node) (index : Nat) (fallback : Json) : Node :=
  match node with
  | .cached _ children => (children[index]?).getD (.uncached fallback)
  | .uncached _ => .uncached fallback

def Node.field (node : Node) (name : String) (fallback : Json) : Node := Id.run do
  let .obj fields := node.value | return .uncached fallback
  for ((key,_),index) in fields.toList.zipIdx do
    if key == name then return node.child index fallback
  return .uncached fallback

private partial def canonicalRaw : Json → Bool
  | .obj fields => Id.run do
      let mut previous : Option String := none
      for (key,value) in fields.toList do
        if let some old := previous then
          unless old < key do return false
        if !canonicalRaw value then return false
        previous := some key
      return true
  | .arr values => values.all canonicalRaw
  | _ => true

/-- Pair raw transport children with the authoritative resolver's actual JSON.
Reference edges reuse the earlier node, so computing the parent hash does not
recursively hash a resolved shared subtree. No JSON is normalized/replaced. -/
private partial def buildNode (available : Array Node) (raw actual : Json) : Option Node := do
  if let .obj fields := raw then
    if fields.contains "$lean_miri_shared_ref" then
      let id ← ((raw.getObjVal? "$lean_miri_shared_ref").bind Json.getNat?).toOption
      return ← available[id]?
  match raw, actual with
  | .arr source, .arr values =>
      if source.size != values.size then none else do
        let mut children := #[]
        let mut digest : UInt64 := 7
        for index in [:values.size] do
          let child ← buildNode available (← source[index]?) (← values[index]?)
          digest := mixHash digest child.key.digest
          children := children.push child
        return .cached ⟨actual, mixHash 23 digest, none⟩ children
  | .obj source, .obj fields =>
      let source := source.toList.toArray
      let entries := fields.toList.toArray
      if source.size != entries.size then none else do
        let mut children := #[]
        let mut digest : UInt64 := 7
        for index in [:entries.size] do
          let (name,value) ← entries[index]?
          let (sourceName,sourceValue) ← source[index]?
          if name != sourceName then return ← none
          let child ← buildNode available sourceValue value
          digest := mixHash digest (mixHash (hash name) child.key.digest)
          children := children.push child
        return .cached ⟨actual, mixHash 29 digest, none⟩ children
  | .arr _, _ | .obj _, _ => none
  | _, _ => return .cached ⟨actual, hash actual, none⟩ #[]

private def buildRoot (input : Json) (resolved : SharedPayloads.ResolvedGraph) : Option Node := do
  if !canonicalRaw input then return ← none
  let rawNodes ← (((input.getObjVal? "shared_payloads").bind fun j => j.getObjVal? "nodes").bind Json.getArr?).toOption
  if rawNodes.size != resolved.nodes.size then return ← none
  let mut available := #[]
  for index in [:rawNodes.size] do
    let node ← buildNode available (← rawNodes[index]?) (← resolved.nodes[index]?)
    available := available.push (node.withId index)
  let .obj fields := input | return ← none
  let business := Json.mkObj (fields.toList.filter (fun entry => entry.1 != "shared_payloads"))
  buildNode available business resolved.root

/-- Only this constructor path creates the optional cache from the same input
and resolver result. Fallback preserves arbitrary manually constructed Raw JSON.
The cache performs no readiness or semantic validation of its own. -/
def resolve (input : Json) (enabled : Bool := true) (profile : Options := {}) :
    Except String (SharedPayloads.ResolvedGraph × Node) := do
  let resolved ← SharedPayloads.resolveGraph input
  let node := if enabled then (profileit "decoder.traversal_hash_cache" profile (fun _ => buildRoot input resolved)).getD (.uncached resolved.root)
    else .uncached resolved.root
  return (resolved,node)

/-- Diagnostic consistency check; deliberately expensive, never used as a
readiness shortcut. It checks every cached child independently. -/
partial def Node.audit (node : Node) : Bool :=
  match node with
  | .uncached _ => true
  | .cached key children =>
    let values := match key.value with
      | .arr values => values
      | .obj fields => fields.toList.toArray.map Prod.snd
      | _ => #[]
    key.digest == hash key.value && values.size == children.size &&
      (values.zip children).all (fun (value,child) => value == child.value) &&
      children.all Node.audit

end Miri.Input.JsonTraversalCache
