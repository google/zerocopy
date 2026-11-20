import Miri.Interpreter.Call

/-! Pinned Miri helpers.rs `visit_freeze_sensitive` / UnsafeCellVisitor,
using rustc interpret/visitor.rs walk_value order. This visitor never reads a
local discriminant or follows a pointer into its pointee. Compiler predicates,
layout projection, dyn-vtable resolution and DST sizes are required leaves. -/
namespace Miri.TreeBorrows.FreezeVisitor
open Miri.ABI Miri.Memory Miri.Interpreter

abbrev M (S A : Type) := EStateM StepError S A

/-- The Boolean queries correspond to exact source type-kind tests; missing
metadata must fail. `projectBox` implements project_to_ptr_in_box and returns
its raw pointer field and allocator field, retaining layout/provenance. -/
structure Hooks (P S : Type) where
  target : PointerArithmetic
  debugAssertions : Bool
  isUnsafeCell : MIR.TyId → M S Bool
  typeIsFreeze : MIR.TyId → M S Bool
  isDynamic : MIR.TyId → M S Bool
  isBox : MIR.TyId → M S Bool
  isTooGeneric : MIR.TyId → M S Bool
  sizeAndAlign : MPlaceTy P → M S (Option (Size × Align))
  unpackDynTrait : MPlaceTy P → M S (MPlaceTy P)
  projectBox : MPlaceTy P → M S (MPlaceTy P × MPlaceTy P)
  projectField : MPlaceTy P → Nat → M S (MPlaceTy P)
  arrayLength : MPlaceTy P → M S UInt64
  projectIndex : MPlaceTy P → UInt64 → M S (MPlaceTy P)

private structure VisitState (S : Type) where
  external : S
  cursor : Size

private abbrev VM (S A : Type) := EStateM StepError (VisitState S) A

private def lift (action : M S A) : VM S A := fun state =>
  match action state.external with
  | .ok value external => .ok value { state with external }
  | .error error external => .error error { state with external }

private def addCursor (amount : Size) : VM S Unit := do
  let state ← get
  match state.cursor.add amount with
  | .error error => throw (.invalidProgram s!"freeze visitor address overflow: {reprStr error}")
  | .ok cursor => set { state with cursor }

/-- Source unsafe_cell_action: action calls occur before each cursor advance,
so an action failure preserves earlier external effects and stops immediately. -/
private def unsafeCellAction (startAddress address size : Size)
    (action : AllocRange → Bool → M S Unit) : VM S Unit := do
  let cursor := (← get).cursor
  unless address.bytes ≥ cursor.bytes do
    throw (.invalidProgram "UnsafeCell visitor fields are not in increasing address order")
  let frozenSize := Size.ofBytes (address.bytes - cursor.bytes)
  if frozenSize != Size.ZERO then
    let range := allocRange (Size.ofBytes (cursor.bytes - startAddress.bytes)) frozenSize
    lift (action range true)
  addCursor frozenSize
  let cursor := (← get).cursor
  if size != Size.ZERO then
    lift (action (allocRange (Size.ofBytes (cursor.bytes - startAddress.bytes)) size) false)
  addCursor size

private def wholeUnsafeCell (h : Hooks P S) (startAddress : Size)
    (place : MPlaceTy P) (action : AllocRange → Bool → M S Unit) : VM S Unit := do
  let dynamic ← lift (h.sizeAndAlign place)
  let size := dynamic.map Prod.fst |>.getD place.layout.layout.size
  -- Source omits even the address assertion for an empty UnsafeCell.
  if size != Size.ZERO then unsafeCellAction startAddress place.mplace.ptr.offset size action

/-- Depth-bounded executable visitor. The budget bounds recursive projection
only; exhaustion is a runner resource error, never a successful missing walk.
All sibling projections retain source DFS order and run before their own visit. -/
private def visitValue (h : Hooks P S) (startAddress : Size)
    (action : AllocRange → Bool → M S Unit) (budget : Nat)
    (place : MPlaceTy P) : VM S Unit := do
  match budget with
  | 0 => throw (.resourceExhaustion "freeze-sensitive visitor depth exhausted")
  | remaining + 1 =>
    let ty := place.layout.ty
    if ← lift (h.isUnsafeCell ty) then
      wholeUnsafeCell h startAddress place action
    else if ← lift (h.typeIsFreeze ty) then
      pure ()
    else if let .Union _ := place.layout.layout.fields then
      wholeUnsafeCell h startAddress place action
    else if let .Multiple .. := place.layout.layout.variants then
      -- Never read the discriminant of a non-Freeze multi-variant value.
      wholeUnsafeCell h startAddress place action
    else
      -- Source ValueVisitor::walk_value type-kind priority.
      if ← lift (h.isDynamic ty) then
        let inner ← lift (h.unpackDynTrait place)
        visitValue h startAddress action remaining inner
        return
      if ← lift (h.isBox ty) then
        let (_, allocator) ← lift (h.projectBox place)
        -- The inherited visit_box does not recurse through the pointer.
        visitValue h startAddress action remaining allocator
        return
      if ← lift (h.isTooGeneric ty) then throw (.invalidProgram "TooGeneric in value visitor")
      match place.layout.layout.fields with
      | .Primitive => pure ()
      | .Union _ => throw (.invalidProgram "freeze visitor reached union walk after union guard")
      | .Arbitrary _ memoryOrder =>
        for field in memoryOrder do
          let projected ← lift (h.projectField place field)
          visitValue h startAddress action remaining projected
      | .Array .. =>
        let length ← lift (h.arrayLength place)
        for index in [:length.toNat] do
          let field ← lift (h.projectIndex place (UInt64.ofNat index))
          visitValue h startAddress action remaining field
      match place.layout.layout.variants with
      | .Multiple .. => throw (.invalidProgram "freeze visitor reached discriminant walk after enum guard")
      | .Single _ | .Empty => pure ()

/-- Source helper including its debug size assertion and final zero-sized
UnsafeCell at the wrapping end pointer, which flushes trailing frozen bytes. -/
def visitFreezeSensitive (h : Hooks P S) (budget : Nat) (place : MPlaceTy P)
    (size : Size) (action : AllocRange → Bool → M S Unit) : M S Unit := fun external =>
  let computation : VM S Unit := do
    if h.debugAssertions then
      let dynamic ← lift (h.sizeAndAlign place)
      let actual := dynamic.map Prod.fst |>.getD place.layout.layout.size
      unless actual == size do throw (.invalidProgram "freeze visitor debug size assertion failed")
    let startAddress := place.mplace.ptr.offset
    visitValue h startAddress action budget place
    let endPointer ← match place.mplace.ptr.wrappingOffset size h.target with
      | .error error => throw (.invalidProgram s!"freeze visitor end pointer: {reprStr error}")
      | .ok pointer => pure pointer
    unsafeCellAction startAddress endPointer.offset Size.ZERO action
  match computation ⟨external, place.mplace.ptr.offset⟩ with
  | .ok () state => .ok () state.external
  | .error error state => .error error state.external

end Miri.TreeBorrows.FreezeVisitor
