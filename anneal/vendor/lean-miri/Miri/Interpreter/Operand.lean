import Miri.Interpreter.Immediate
import Miri.Memory.Access
import Miri.Interpreter.PointerOffset

/-! Stored operands and the low-level LocalState operations from pinned
`operand.rs`, `place.rs`, and `stack.rs`. Memory access and machine hooks are
required at higher-level accesses; the ghost accessor below never substitutes
for a Rust read. -/
namespace Miri.Interpreter

open Miri.Memory Miri.ABI

structure MemPlace (Prov : Type) where
  ptr : Pointer (Option Prov)
  metadata : MemPlaceMeta Prov
  misaligned : Option Misalignment
  deriving DecidableEq, Repr

inductive Operand (Prov : Type) where
  | immediate (value : Immediate Prov)
  | indirect (place : MemPlace Prov)
  deriving DecidableEq, Repr

inductive LocalValue (Prov : Type) where
  | dead
  | live (value : Operand Prov)
  deriving DecidableEq, Repr

/-- `Layout` will be the canonical imported TyAndLayout representation at the
integrated interpreter boundary. Its cached value is retained unchanged by
the selected source operations. -/
structure LocalState (Prov Layout : Type) where
  value : LocalValue Prov
  layout : Option Layout
  deriving DecidableEq, Repr

inductive LocalStateError where
  | deadLocal
  deriving DecidableEq, Repr

inductive OffsetMode where
  | inbounds
  | wrapping
  deriving DecidableEq, Repr

inductive MemPlaceOffsetError where
  | addedMetadataToThinPlace
  | offsetDoesNotFitI64 (offset : Size)
  | inbounds (reason : PointerOffsetError)
  | pointer (reason : PointerError)
  deriving DecidableEq, Repr

namespace MemPlace

def mapProvenance (self : MemPlace Prov) (f : Prov → Prov) : MemPlace Prov :=
  { self with ptr := self.ptr.mapProvenance (Option.map f) }

def toRef (self : MemPlace Prov) (layout : TargetDataLayout) :
    Except ImmediateError (Immediate Prov) :=
  Immediate.newPointerWithMeta self.ptr self.metadata layout

/-- Source `MemPlace::offset_with_meta_`: metadata cannot be added to a thin
place; inbounds mode checks the signed conversion and allocation bounds,
while wrapping mode uses the target-width pointer operation directly. -/
def offsetWithMeta {Prov ProvExtra : Type} (self : MemPlace Prov)
    (offset : Size) (mode : OffsetMode) (metadata : MemPlaceMeta Prov)
    (target : PointerArithmetic) (resolve : PointerResolver Prov ProvExtra)
    (lookup : LiveAllocationLookup) : Except MemPlaceOffsetError (MemPlace Prov) := do
  if metadata.hasMeta && !self.metadata.hasMeta then throw .addedMetadataToThinPlace
  let ptr ← match mode with
    | .inbounds => do
      if offset.bytes.toNat ≥ 2 ^ 63 then throw (.offsetDoesNotFitI64 offset)
      ptrOffsetInbounds target self.ptr (Int64.ofInt offset.bytes.toNat) resolve lookup
        |>.mapError .inbounds
    | .wrapping => self.ptr.wrappingOffset offset target |>.mapError .pointer
  return { self with ptr, metadata }

theorem mapProvenance_metadata (self : MemPlace Prov) (f : Prov → Prov) :
    (self.mapProvenance f).metadata = self.metadata := rfl

end MemPlace

namespace LocalState

def makeLiveUninit (self : LocalState Prov Layout) : LocalState Prov Layout :=
  { self with value := .live (.immediate .uninit) }

/-- Source ghost read for provenance visiting. It does not count as a read
in the abstract machine and performs no borrow/race hooks. -/
def asMplaceOrImmGhost (self : LocalState Prov Layout) :
    Option (Sum (Pointer (Option Prov) × MemPlaceMeta Prov) (Immediate Prov)) :=
  match self.value with
  | .dead => none
  | .live (.indirect place) => some (.inl (place.ptr, place.metadata))
  | .live (.immediate value) => some (.inr value)

def access (self : LocalState Prov Layout) : Except LocalStateError (Operand Prov) :=
  match self.value with
  | .dead => .error .deadLocal
  | .live value => .ok value

/-- Functional form of source `access_mut`: only a live operand is exposed
for mutation. It is still the caller's job to perform the machine access hook. -/
def modify (self : LocalState Prov Layout) (f : Operand Prov → Operand Prov) :
    Except LocalStateError (LocalState Prov Layout) := do
  let value ← self.access
  return { self with value := .live (f value) }

theorem dead_access (layout : Option Layout) :
    (LocalState.mk (.dead : LocalValue Prov) layout).access = .error .deadLocal := rfl

theorem access_success (self : LocalState Prov Layout) (operand : Operand Prov)
    (success : self.access = .ok operand) : self.value = .live operand := by
  cases h : self.value with
  | dead => simp [access, h] at success
  | live value =>
    simp [access, h] at success
    exact congrArg LocalValue.live success

theorem makeLiveUninit_preserves_layout (self : LocalState Prov Layout) :
    self.makeLiveUninit.layout = self.layout := rfl

theorem makeLiveUninit_access (self : LocalState Prov Layout) :
    self.makeLiveUninit.access = .ok (.immediate .uninit) := rfl

theorem dead_modify (layout : Option Layout) (f : Operand Prov → Operand Prov) :
    (LocalState.mk .dead layout).modify f = .error .deadLocal := rfl

end LocalState
end Miri.Interpreter
