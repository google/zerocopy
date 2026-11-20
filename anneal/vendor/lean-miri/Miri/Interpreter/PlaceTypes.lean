import Miri.Interpreter.MemoryOperand
import Miri.Interpreter.LocalsIdentity
import Miri.ABI.Layout
import Miri.MIR.Syntax

/-! Canonical typed runtime places shared by frame storage, call dispatch and
place execution. Byte-level MemoryOperandLayout is only a one-way memory API
projection; saved places always retain their original TyAndLayout. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

abbrev LocalLayout := TyAndLayout MIR.TyId

structure MPlaceTy (P : Type) where
  mplace : MemPlace P
  layout : LocalLayout
  deriving DecidableEq, Repr

inductive RuntimePlaceRef (P : Type) where
  | local (frameIndex localId : Nat) (offset : Option Size) (localsIdentity : LocalsIdentity)
  | memory (place : MemPlace P)
  deriving DecidableEq, Repr

structure RuntimePlace (P : Type) where
  ref : RuntimePlaceRef P
  layout : LocalLayout
  deriving DecidableEq, Repr

/-- Saved evaluated call/return destination. Both variants retain canonical
compiler type identity, including projected local destinations. -/
inductive RuntimeStackPlace (P : Type) where
  | memory (place : MPlaceTy P)
  | frameLocal (frameIndex localId : Nat) (offset : Option Size) (layout : LocalLayout)
      (localsIdentity : LocalsIdentity)
  deriving DecidableEq, Repr

namespace RuntimeStackPlace

def toRuntimePlace : RuntimeStackPlace P → RuntimePlace P
  | .memory place => ⟨.memory place.mplace, place.layout⟩
  | .frameLocal frame localId offset layout identity => ⟨.local frame localId offset identity, layout⟩

def layout : RuntimeStackPlace P → LocalLayout
  | .memory place => place.layout
  | .frameLocal _ _ _ layout _ => layout

end RuntimeStackPlace

namespace RuntimePlace

def stackView (place : RuntimePlace P) : RuntimeStackPlace P :=
  match place.ref with
  | .local frame localId offset identity => .frameLocal frame localId offset place.layout identity
  | .memory mplace => .memory ⟨mplace, place.layout⟩

@[simp] theorem stackView_toRuntimePlace (place : RuntimePlace P) :
    place.stackView.toRuntimePlace = place := by
  cases place with
  | mk ref layout => cases ref <;> rfl

end RuntimePlace

@[simp] theorem RuntimeStackPlace.toRuntimePlace_stackView (place : RuntimeStackPlace P) :
    place.toRuntimePlace.stackView = place := by
  cases place <;> rfl

end Miri.Interpreter
