import Miri.TreeBorrows.FreezeVisitor
import Miri.DataStructures.DedupRangeMap

/-! Stateful application of the source freeze-sensitive visitor to a private
map accumulator. Query effects remain in the caller's canonical state, while
the source's private permission map is returned only after a complete visit. -/
namespace Miri.TreeBorrows.FreezeMap
open Miri.ABI Miri.Memory Miri.Interpreter Miri.DataStructures

private structure Accumulator (S A : Type) where
  external : S
  value : A

private def liftExternal (action : EStateM StepError S B) :
    EStateM StepError (Accumulator S A) B := fun state =>
  match action state.external with
  | .ok value external => .ok value { state with external }
  | .error error external => .error error { state with external }

private def liftValue (action : EStateM StepError A Unit) :
    EStateM StepError (Accumulator S A) Unit := fun state =>
  match action state.value with
  | .ok () value => .ok () { state with value }
  | .error error value => .error error { state with value }

private def liftHooks (h : FreezeVisitor.Hooks P S) :
    FreezeVisitor.Hooks P (Accumulator S A) := {
  target := h.target
  debugAssertions := h.debugAssertions
  isUnsafeCell := fun ty => liftExternal (h.isUnsafeCell ty)
  typeIsFreeze := fun ty => liftExternal (h.typeIsFreeze ty)
  isDynamic := fun ty => liftExternal (h.isDynamic ty)
  isBox := fun ty => liftExternal (h.isBox ty)
  isTooGeneric := fun ty => liftExternal (h.isTooGeneric ty)
  sizeAndAlign := fun p => liftExternal (h.sizeAndAlign p)
  unpackDynTrait := fun p => liftExternal (h.unpackDynTrait p)
  projectBox := fun p => liftExternal (h.projectBox p)
  projectField := fun p idx => liftExternal (h.projectField p idx)
  arrayLength := fun p => liftExternal (h.arrayLength p)
  projectIndex := fun p idx => liftExternal (h.projectIndex p idx) }

/-- Execute actions in source visitor order. Query and earlier action effects
survive a later failure; the private accumulator is not exposed as a successful
map until the trailing frozen range has also been visited. -/
def visit (h : FreezeVisitor.Hooks P S) (budget : Nat) (place : MPlaceTy P)
    (size : Size) (initial : A) (action : AllocRange → Bool → EStateM StepError A Unit) :
    EStateM StepError S A := fun external =>
  let body := FreezeVisitor.visitFreezeSensitive (liftHooks h) budget place size
    (fun range frozen => liftValue (action range frozen))
  match body ⟨external, initial⟩ with
  | .ok () state => .ok state.value state.external
  | .error error state => .error error state.external

end Miri.TreeBorrows.FreezeMap
