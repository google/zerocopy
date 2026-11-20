import Miri.TreeBorrows.TreeState

/-! Exact current-state rendering used by Tree Borrows' `print_tree` diagnostic.
Diagnostic histories are intentionally absent because this source printer
renders current node names, permissions, protectors and exposure only. -/
namespace Miri.TreeBorrows.DiagnosticsRender
open Miri.ABI Miri.DataStructures

structure Node where
  tag : Miri.Memory.BorTag
  name : Option String
  exposed : Bool
  permissions : Array (Option Tree.LocationState)
  children : Array Node

private def orderedChildren (tree : BorrowTree) (node : TreeNode) :
    Except String (Array UniIndex) := do
  let mut keyed : Array (Miri.Memory.BorTag × UniIndex) := #[]
  for index in node.children do
    let some child := tree.nodes.get index
      | throw s!"Tree Borrows diagnostic: missing child {index.idx}"
    keyed := keyed.push (child.tag,index)
  return (keyed.qsort (fun a b => a.1.value < b.1.value)).map Prod.snd

partial def extractForest (tree : BorrowTree) (index : UniIndex)
    (ranges : Array (RangeMapSegment LocationTree)) (showUnnamed : Bool) :
    Except String (Array Node) := do
  let some node := tree.nodes.get index
    | throw s!"Tree Borrows diagnostic: missing node {index.idx}"
  let childIndices ← orderedChildren tree node
  let mut children : Array Node := #[]
  for child in childIndices do
    children := children ++ (← extractForest tree child ranges showUnnamed)
  if showUnnamed || node.debugName.isSome then
    let permissions := ranges.map fun range => (range.data.perms.get index).map id
    return #[Node.mk node.tag node.debugName node.isExposed permissions children]
  return children

private def shortPermission : Permission → String
  | .Cell => "Cel "
  | .ReservedFrz false => "Res "
  | .ReservedFrz true => "ResC"
  | .ReservedIM => "ReIM"
  | .Unique => "Unq "
  | .Frozen => "Frz "
  | .Disabled => "Dis "

private def paddingText (text : String) (count : Nat) : String :=
  String.join (List.replicate count text)

private def chars (text : String) : Nat := text.toList.length

private def headerAndPadding (ranges : Array (RangeMapSegment LocationTree)) :
    String × Array Nat := Id.run do
  let mut header := "0.."
  let mut padding := #[]
  for (range,position) in ranges.toList.zipIdx do
    if position > 0 then header := header ++ ".."
    let endText := toString range.range.stop
    let labelLength := chars endText + 2
    let targetLength := 6
    let totalLength := max targetLength labelLength
    header := header ++ paddingText " " (targetLength - min targetLength labelLength) ++ endText
    padding := padding.push (totalLength - targetLength)
  return (header,padding)

private def permissionCells (node : Node) (padding : Array Nat) : String := Id.run do
  let mut line := "|"
  for (permission,i) in node.permissions.toList.zipIdx do
    if i > 0 then line := line ++ "|"
    let cell := match permission with
      | none => "-----"
      | some state => (if state.accessed then " " else "?") ++ shortPermission state.permission
    line := line ++ paddingText " " (padding[i]?.getD 0) ++ cell
  return line ++ "|"

private def nodeTag (node : Node) : String :=
  match node.name with
  | none => s!"<{node.tag.value}>"
  | some name => s!"<{node.tag.value}={name}>"

private def protection (tags : ProtectedTags) (tag : Miri.Memory.BorTag) : String :=
  match tags.get tag with
  | none => ""
  | some .WeakProtector => " Weakly protected"
  | some .StrongProtector => " Strongly protected"

partial def nodeLines (node : Node) (padding : Array Nat) (tags : ProtectedTags)
    (indent : String) (lastChild wildcardRoot : Bool) : Array String := Id.run do
  let join := if wildcardRoot then "*" else if lastChild then "└" else "├"
  let branch := join ++ "─" ++ (if node.children.isEmpty then "─" else "┬") ++ "──"
  let line := permissionCells node padding ++ indent ++ branch ++ nodeTag node ++
    protection tags node.tag ++ (if node.exposed then " (exposed)" else "")
  let mut lines := #[line]
  for (child,i) in node.children.toList.zipIdx do
    let childIndent := indent ++ if lastChild then "  " else "│ "
    lines := lines ++ nodeLines child padding tags childIndent
      (i + 1 == node.children.size) false
  return lines

private def gapLine (padding : Array Nat) : String := Id.run do
  let mut line := "|"
  for (spaces,i) in padding.toList.zipIdx do
    if i > 0 then line := line ++ "|"
    line := line ++ paddingText " " spaces ++ "     "
  return line ++ "|"

/-- Produce the exact lines emitted by pinned `Tree::print_tree`; the caller
uses stderr `write_all` and ignores returned host I/O errors as upstream does. -/
def render (tree : BorrowTree) (protectedTags : ProtectedTags) (showUnnamed : Bool) :
    Except String (Array String) := do
  let ranges := tree.locations.iterAll
  let (header,padding) := headerAndPadding ranges
  let some mainRoot := tree.roots[0]? | throw "Tree Borrows diagnostic: allocation tree has no main root"
  let mainForest ← extractForest tree mainRoot ranges showUnnamed
  if mainForest.size > 1 then
    throw "Tree Borrows diagnostic: unnamed root splits into several visible trees"
  let mut wildcardTrees : Array Node := #[]
  for root in tree.roots.extract 1 tree.roots.size do
    let forest ← extractForest tree root ranges showUnnamed
    if forest.size > 1 then
      throw "Tree Borrows diagnostic: unnamed wildcard root splits into several visible trees"
    wildcardTrees := wildcardTrees ++ forest
  let hasVisible := mainForest.size > 0 || wildcardTrees.size > 0
  let mut block := #[header]
  if let some root := mainForest[0]? then
    block := block ++ nodeLines root padding protectedTags "" true false
  for root in wildcardTrees do
    block := block.push (gapLine padding)
    block := block ++ nodeLines root padding protectedTags "" true true
  let warning := "Warning: this tree is indicative only. Some tags may have been hidden."
  let width := max (block.foldl (fun width line => max width (chars line)) 0)
    (if !showUnnamed then chars warning else 0)
  let border := paddingText "─" width
  let mut lines := #[]
  if !hasVisible then
    lines := lines.push "This allocation does not contain named tags. Use `miri_print_borrow_state(_, true)` to also print unnamed tags."
  lines := lines.push border
  if !showUnnamed then lines := lines.push warning
  lines := lines ++ block
  lines := lines.push border
  return lines

end Miri.TreeBorrows.DiagnosticsRender
