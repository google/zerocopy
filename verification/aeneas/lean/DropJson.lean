/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Lean
public import DropOwnership
@[expose] public section

/-!
This decoder reads a complete Charon body, including its local declarations.
It accepts a deliberately small executable schema. Every operand is decoded in
evaluation order. It does not search JSON recursively for moves or accept an
externally supplied list of effects.

Source spans, comments, statement IDs, types, generic arguments, and the static
trait reference in drop glue cannot carry executable operands in this schema.
Their payloads are explicitly ignored here. The ordinary admission audit still
checks operations, types, function identities, and all execution dependencies.
This decoder supplies only the additional ownership condition for erasing a
conditional drop, under the compiler correspondence premise of DropOwnership.
-/

namespace AeneasSpecs.DropJson

open Lean DropOwnership

abbrev Decode := Except String

def require (condition : Bool) (message : String) : Decode Unit :=
  if condition then pure () else throw message

def fields (j : Json) (names : List String) : Decode Unit := do
  let obj ← j.getObj?
  let actual := obj.toList.map Prod.fst
  require (actual.length == names.length && actual.all names.contains)
    "unexpected or missing object fields"

def field := Json.getObjVal?

def variant (j : Json) : Decode (String × Json) := do
  let obj ← j.getObj?
  match obj.toList with
  | [kv] => pure kv
  | _ => throw "expected one constructor"

def tuple (j : Json) (n : Nat) : Decode (Array Json) := do
  let a ← j.getArr?
  require (a.size == n) "wrong constructor arity"
  pure a

def item (a : Array Json) (i : Nat) : Decode Json :=
  match a[i]? with
  | some j => pure j
  | none => throw "missing constructor argument"

def localIndex (count : Nat) (j : Json) : Decode Nat := do
  let i ← j.getNat?
  require (i < count) "local index out of bounds"
  pure i

def globalRef (j : Json) : Decode Unit := do
  fields j ["id", "generics"]
  let _ ← (← field j "id").getNat?
  -- Generic arguments describe types and constants, not runtime operands.
  pure ()

def functionRef (j : Json) : Decode Unit := do
  fields j ["kind", "generics"]
  let (tag, value) ← variant (← field j "kind")
  match tag with
  | "Fun" => let _ ← value.getNat?; pure ()
  | "Trait" =>
    let args ← tuple value 2
    let _ ← (← item args 1).getNat?
    -- The first argument is a static trait reference, not a place or operand.
    pure ()
  | _ => throw "unsupported function reference"

def directFunction (j : Json) : Decode Unit := do
  let (tag, value) ← variant j
  require (tag == "Regular") "unsupported executable function operand"
  functionRef value
  let (kind, _) ← variant (← field value "kind")
  require (kind == "Fun") "only direct function calls are supported"

def constant (j : Json) : Decode Unit := do
  let (tag, value) ← variant j
  require (tag == "Untagged") "unsupported constant wrapper"
  let args ← tuple value 2
  let (kind, payload) ← variant (← item args 0)
  -- The second argument is the static type of this constant.
  match kind with
  | "Global" => globalRef payload
  | "Bool" => let _ ← payload.getBool?; pure ()
  | "Adt" =>
    let a ← tuple payload 2
    require (← item a 0).isNull "only unit constants are supported"
    require (← (← item a 1).getArr?).isEmpty "only unit constants are supported"
  | "Opaque" =>
    require ((← payload.getStr?) == "Missing metadata") "unsupported opaque constant"
  | _ => throw "unsupported constant expression"

structure Place where
  root : Option Nat
  whole : Bool
  restricted : List Nat := []

def place : Nat → Nat → Json → Decode Place
  | 0, _, _ => throw "place nesting limit exceeded"
  | fuel + 1, count, j => do
    fields j ["kind", "ty"]
    let (tag, value) ← variant (← field j "kind")
    match tag with
    | "Local" => pure ⟨some (← localIndex count value), true, []⟩
    | "Global" => globalRef value; pure ⟨none, true, []⟩
    | "Projection" =>
      let args ← tuple value 2
      let base ← place fuel count (← item args 0)
      -- Dereference is the only supported projection. Its base cannot be a
      -- candidate local anywhere in the body, including disconnected code.
      require ((← (← item args 1).getStr?) == "Deref") "unsupported place projection"
      pure ⟨base.root, false, base.root.toList ++ base.restricted⟩
    | _ => throw "unsupported place constructor"

structure Audit where
  effects : List Effect := []
  restricted : List Nat := []

def Audit.append (a b : Audit) : Audit :=
  ⟨a.effects ++ b.effects, a.restricted ++ b.restricted⟩

def operand (fuel count : Nat) (j : Json) : Decode Audit := do
  let (tag, value) ← variant j
  match tag with
  | "Move" | "Copy" =>
    let p ← place fuel count value
    let effects := if tag == "Move" && p.whole then
        p.root.toList.map Effect.consume else []
    pure ⟨effects, p.restricted⟩
  | "Const" => constant value; pure {}
  | _ => throw "unsupported operand constructor"

def destination (fuel count : Nat) (j : Json) : Decode Audit := do
  let p ← place fuel count j
  let effects := if p.whole then p.root.toList.map Effect.define else []
  pure ⟨effects, p.restricted⟩

def rvalue (fuel count : Nat) (j : Json) : Decode Audit := do
  let (tag, value) ← variant j
  match tag with
  | "Use" =>
    let args ← tuple value 2
    require ((← (← item args 1).getStr?) == "Yes") "unsupported Use mode"
    operand fuel count (← item args 0)
  | "Ref" =>
    fields value ["place", "kind", "ptr_metadata"]
    let kind ← (← field value "kind").getStr?
    require (["Shared", "Mut"].contains kind) "unsupported reference kind"
    let p ← place fuel count (← field value "place")
    let metadata ← operand fuel count (← field value "ptr_metadata")
    pure ⟨metadata.effects, p.root.toList ++ p.restricted ++ metadata.restricted⟩
  | "BinaryOp" =>
    let args ← tuple value 3
    require ((← (← item args 0).getStr?) == "Eq") "unsupported binary operation"
    let left ← operand fuel count (← item args 1)
    let right ← operand fuel count (← item args 2)
    pure (left.append right)
  | _ => throw "unsupported rvalue constructor"

def simple (fuel count : Nat) (j : Json) : Decode Audit := do
  let (tag, value) ← variant j
  match tag with
  | "StorageLive" | "StorageDead" => pure ⟨[.define (← localIndex count value)], []⟩
  | "Assign" =>
    let args ← tuple value 2
    let rhs ← rvalue fuel count (← item args 1)
    let dest ← destination fuel count (← item args 0)
    pure (rhs.append dest)
  | "Borrowck" =>
    let (kind, p) ← variant value
    require (kind == "FakeRead") "unsupported borrow-checking statement"
    let p ← place fuel count p
    pure ⟨[], p.restricted⟩
  | _ => throw "unsupported simple statement"

def call (fuel count : Nat) (j : Json) : Decode Audit := do
  fields j ["func", "args", "dest"]
  directFunction (← field j "func")
  let args ← (← field j "args").getArr?
  let mut result : Audit := {}
  for arg in args do
    result := result.append (← operand fuel count arg)
  -- Restoring the destination in this node precedes every normal and unwind
  -- successor. Even an unwinding call cannot establish an empty destination.
  pure (result.append (← destination fuel count (← field j "dest")))

def dropLocal (fuel count : Nat) (j : Json) : Decode Nat := do
  require ((← (← field j "kind").getStr?) == "Conditional") "only conditional drops are supported"
  let p ← place fuel count (← field j "place")
  require p.whole "projected drop is unsupported"
  let some root := p.root | throw "drop of a global is unsupported"
  functionRef (← field j "fn_ptr")
  pure root

def abort (j : Json) : Decode Unit := do
  match j with
  | .str "UnwindTerminate" => pure ()
  | _ =>
    let (tag, path) ← variant j
    require (tag == "Panic") "unsupported abort constructor"
    let path ← path.getArr?
    for part in path do
      let (tag, args) ← variant part
      require (tag == "Ident") "unsupported panic name component"
      let args ← tuple args 2
      let _ ← (← item args 0).getStr?
      let _ ← (← item args 1).getNat?
    pure ()

def assertion (fuel count : Nat) (j : Json) : Decode Audit := do
  fields j ["cond", "expected", "check_kind"]
  let _ ← (← field j "expected").getBool?
  require (← field j "check_kind").isNull "unsupported assertion check kind"
  operand fuel count (← field j "cond")

def wrapper (structured : Bool) (j : Json) : Decode Json := do
  fields j (if structured then ["span", "id", "kind", "comments_before"]
    else ["span", "kind", "comments_before"])
  if structured then
    let _ ← (← field j "id").getNat?
  field j "kind"

structure Annotated where
  node : Node
  restricted : List Nat := []

def target (count : Nat) (j : Json) : Decode Nat := do
  let i ← j.getNat?
  require (i < count) "control target out of bounds"
  pure i

def switch (fuel count blocks : Nat) (j : Json) : Decode (Audit × List Nat) := do
  fields j ["data", "branches"]
  let successors ← (← field j "branches").getArr?
  require (!successors.isEmpty) "empty switch successor list"
  let successors ← successors.toList.mapM (target blocks)
  let data ← field j "data"
  fields data ["scrutinee", "branches", "fallback"]
  let (tag, scrutinee) ← variant (← field data "scrutinee")
  require (tag == "Value") "unsupported switch scrutinee"
  let effects ← operand fuel count scrutinee
  let branches ← (← field data "branches").getArr?
  for branch in branches do
    let branch ← tuple branch 2
    constant (← item branch 0)
    let _ ← target successors.length (← item branch 1)
  let _ ← target successors.length (← field data "fallback")
  pure (effects, successors)

def unstructured (fuel count : Nat) (j : Json) : Decode (List Annotated) := do
  let blocks ← j.getArr?
  require (!blocks.isEmpty) "empty unstructured body"
  blocks.toList.mapM fun block => do
    fields block ["statements", "terminator"]
    let statements ← (← field block "statements").getArr?
    let mut audit : Audit := {}
    for statement in statements do
      audit := audit.append (← simple fuel count (← wrapper false statement))
    let kind ← wrapper false (← field block "terminator")
    match kind with
    | .str "Return" | .str "UnwindResume" =>
      pure ⟨⟨audit.effects, none, []⟩, audit.restricted⟩
    | _ =>
      let (tag, value) ← variant kind
      match tag with
      | "Goto" =>
        fields value ["target"]
        pure ⟨⟨audit.effects, none, [← target blocks.size (← field value "target")]⟩, audit.restricted⟩
      | "Abort" => abort value; pure ⟨⟨audit.effects, none, []⟩, audit.restricted⟩
      | "Call" =>
        fields value ["call", "target", "on_unwind"]
        let total := audit.append (← call fuel count (← field value "call"))
        let normal ← target blocks.size (← field value "target")
        let unwind ← target blocks.size (← field value "on_unwind")
        pure ⟨⟨total.effects, none, [normal, unwind]⟩, total.restricted⟩
      | "Drop" =>
        fields value ["kind", "place", "fn_ptr", "target", "on_unwind"]
        let dropped ← dropLocal fuel count value
        let normal ← target blocks.size (← field value "target")
        let unwind ← target blocks.size (← field value "on_unwind")
        pure ⟨⟨audit.effects, some dropped, [normal, unwind]⟩, audit.restricted⟩
      | "Switch" =>
        let (branchAudit, successors) ← switch fuel count blocks.size value
        let total := audit.append branchAudit
        pure ⟨⟨total.effects, none, successors⟩, total.restricted⟩
      | "Assert" =>
        fields value ["assert", "target", "on_unwind"]
        let total := audit.append (← assertion fuel count (← field value "assert"))
        let normal ← target blocks.size (← field value "target")
        let unwind ← target blocks.size (← field value "on_unwind")
        pure ⟨⟨total.effects, none, [normal, unwind]⟩, total.restricted⟩
      | _ => throw "unsupported unstructured terminator"

abbrev Build := StateT (Array Annotated) Decode

def emit (a : Annotated) : Build Nat := do
  let nodes ← get
  set (nodes.push a)
  pure nodes.size

-- The continuation is explicit. Abrupt exits ignore it. Statements after an
-- abrupt exit are still decoded and remain conservative disconnected nodes.
def structured : Nat → Nat → Json → List Nat → Build Nat
  | 0, _, _, _ => throw "structured nesting limit exceeded"
  | fuel + 1, count, block, continuation => do
    fields block ["span", "id", "statements"]
    let _ ← (← field block "id").getNat?
    let statements ← (← field block "statements").getArr?
    let mut next := continuation
    for statement in statements.toList.reverse do
      let kind ← wrapper true statement
      let node ← match kind with
        | .str "Return" | .str "UnwindResume" => emit ⟨⟨[], none, []⟩, []⟩
        | _ => do
          let (tag, value) ← variant kind
          match tag with
          | "Abort" => abort value; emit ⟨⟨[], none, []⟩, []⟩
          | "Call" =>
            fields value ["call", "on_unwind"]
            let audit ← call fuel count (← field value "call")
            -- Falling through a cleanup is conservatively allowed to reach
            -- the same continuation. Its actual abrupt exits never do so.
            let unwind ← structured fuel count (← field value "on_unwind") next
            emit ⟨⟨audit.effects, none, next ++ [unwind]⟩, audit.restricted⟩
          | "Drop" =>
            fields value ["kind", "place", "fn_ptr", "on_unwind"]
            let dropped ← dropLocal fuel count value
            let unwind ← structured fuel count (← field value "on_unwind") next
            emit ⟨⟨[], some dropped, next ++ [unwind]⟩, []⟩
          | "Assert" =>
            fields value ["assert", "on_failure", "on_unwind"]
            let audit ← assertion fuel count (← field value "assert")
            abort (← field value "on_failure")
            let unwind ← structured fuel count (← field value "on_unwind") next
            emit ⟨⟨audit.effects, none, next ++ [unwind]⟩, audit.restricted⟩
          | _ =>
            -- Loop, Break, Continue, and every unknown constructor fail here.
            let audit ← simple fuel count kind
            emit ⟨⟨audit.effects, none, next⟩, audit.restricted⟩
      next := [node]
    emit ⟨⟨[], none, next⟩, []⟩

def locals (j : Json) : Decode Nat := do
  fields j ["arg_count", "locals"]
  let args ← (← field j "arg_count").getNat?
  let declarations ← (← field j "locals").getArr?
  require (args < declarations.size) "invalid argument count"
  for i in [:declarations.size] do
    let declaration ← item declarations i
    fields declaration ["index", "name", "span", "ty", "drop_flag_for"]
    require ((← (← field declaration "index").getNat?) == i) "locals are not densely indexed"
    require (← field declaration "drop_flag_for").isNull "drop flag locals are unsupported"
    let name ← field declaration "name"
    unless name.isNull do
      let _ ← name.getStr?
  pure declarations.size

def topological (nodes : List Node) : Nat → List Nat → List Nat → Decode (List Nat)
  | 0, remaining, order =>
    if remaining.isEmpty then pure order else throw "cyclic control flow"
  | fuel + 1, remaining, order => do
    if remaining.isEmpty then return order
    let some chosen := remaining.find? (fun i => remaining.all fun predecessor =>
      match nodes[predecessor]? with
      | some node => !node.successors.contains i
      | none => false) | throw "cyclic control flow"
    topological nodes fuel (remaining.erase chosen) (order ++ [chosen])

def reorder (count entry : Nat) (annotated : List Annotated) : Decode Graph := do
  let nodes := annotated.map Annotated.node
  let candidates := nodes.filterMap Node.candidateDrop
  let restricted := annotated.flatMap Annotated.restricted
  require (!(restricted.any candidates.contains)) "candidate local is projected or borrowed"
  require (entry < nodes.length) "invalid entry node"
  let order ← topological nodes nodes.length (List.range nodes.length) []
  let renamed ← order.mapM fun old => do
    let some node := nodes[old]? | throw "invalid node permutation"
    let successors ← node.successors.mapM fun successor => do
      require (successor < nodes.length) "invalid graph successor"
      pure (order.idxOf successor)
    pure { node with successors := successors }
  pure ⟨renamed, count, order.idxOf entry⟩

/-- Decode and check the complete executable schema before projecting effects.
The fixed nesting limit rejects exceptionally deep inputs rather than making
the executable decoder partial. Both structured and unstructured bodies are
reordered in Lean; every disconnected component participates in cycle checks. -/
def decode (body : Json) : Except String Graph := do
  let (tag, value) ← variant body
  fields value ["span", "bound_body_regions", "locals", "body", "comments"]
  let _ ← (← field value "bound_body_regions").getNat?
  let count ← locals (← field value "locals")
  match tag with
  | "Unstructured" => reorder count 0 (← unstructured 4096 count (← field value "body"))
  | "Structured" =>
    let (entry, nodes) ← (structured 4096 count (← field value "body") []).run #[]
    reorder count entry nodes.toList
  | _ => throw "unsupported body constructor"

/-- This is the proposition evaluated by each kernel-checked snapshot theorem. -/
def acceptBody (body : Json) : Bool :=
  match decode body with
  | .error _ => false
  | .ok graph => DropOwnership.accepted graph

theorem accepted_of_decoded {body : Json} {graph : Graph}
    (decoded : decode body = .ok graph) (checked : acceptBody body = true) :
    DropOwnership.accepted graph = true := by
  simpa [acceptBody, decoded] using checked

/-- A certificate about a raw body entails the ownership theorem for the graph
produced by this decoder. The separate compiler correspondence premise must
relate source executions to that graph's modeled executions. -/
theorem decoded_drop_empty {body : Json} {graph : Graph}
    (decoded : decode body = .ok graph) (checked : acceptBody body = true)
    {index slot : Nat} {owns : DropOwnership.Concrete}
    (reached : DropOwnership.Reachable graph index owns)
    (candidate : (graph.node index).candidateDrop = some slot) :
    ¬ DropOwnership.execute (graph.node index).effects owns slot :=
  DropOwnership.accepted_drop_empty (accepted_of_decoded decoded checked) reached candidate

end AeneasSpecs.DropJson
