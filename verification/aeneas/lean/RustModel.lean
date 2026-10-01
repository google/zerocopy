/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public meta import Lean
@[expose] public section

/-!
A `RustModel` interprets a raw Rust representation by either accepting it with a
mathematical value (`some`) or rejecting it (`none`). That `Option` is decoder
admission, separate from both a Rust `Option` payload and Aeneas execution
failure. There is no requirement to reconstruct a raw value from its model or
to preserve information that the operation contracts do not observe.

The builtin container models recursively decode their contents. One rejected
child rejects its container. Slices and arrays retain their length constraints
in proof fields; list decoding preserves length, so those constraints can be
transferred from the raw representation without a second runtime check.
-/

open Lean Lean.Meta Aeneas.Std
namespace AeneasSpecs

/-- The provider fixes both the mathematical type and the decoder. Two providers
may share a Model type while assigning different meanings or admission domains
to the same raw value, so contracts retain the actual provider explicitly. -/
class RustModel (Raw : Type u) where
  Model : Type u
  decode : Raw → Option Model

-- The associated type is transparent so ordinary rewriting and coercions can
-- identify a retained provider's Model with its named mathematical carrier.
attribute [reducible] RustModel.Model

abbrev ModelOf (Raw : Type u) [m : RustModel Raw] : Type u := m.Model

/-- Admission means that some mathematical witness exists. It does not require
a canonical witness, an encoder, or a separately authored validity predicate. -/
def isValid {Raw : Type u} [m : RustModel Raw] (raw : Raw) : Prop :=
  ∃ value, m.decode raw = some value

/-- Automatic contracts call this with their retained explicit provider. -/
def decoded {Raw : Type u} (m : RustModel Raw) (raw : Raw) (value : m.Model) : Prop :=
  m.decode raw = some value

@[reducible] instance modelBool : RustModel Bool := ⟨Bool, some⟩
@[reducible] instance modelNat : RustModel Nat := ⟨Nat, some⟩
@[reducible] instance modelInt : RustModel Int := ⟨Int, some⟩
@[reducible] instance modelUnit : RustModel Unit := ⟨Unit, some⟩

@[reducible] instance modelProd {α : Type u} {β : Type v} [ma : RustModel α] [mb : RustModel β] :
    RustModel (α × β) where
  Model := ma.Model × mb.Model
  decode raw := match ma.decode raw.1, mb.decode raw.2 with
    | some a, some b => some (a, b)
    | _, _ => none

-- Raw none is an admitted mathematical none. A raw some needs child decoding;
-- a rejected child returns decoder none, not an admitted Option payload.
@[reducible] instance modelOption {α : Type u} [ma : RustModel α] : RustModel (Option α) where
  Model := Option ma.Model
  decode | none => some none | some raw => (ma.decode raw).map some

def decodeList {α β : Type u} (decode : α → Option β) : List α → Option (List β)
  | [] => some []
  | raw :: raws => do return (← decode raw) :: (← decodeList decode raws)

/-- Each successful list step contributes exactly one output element. This
length equality transports the existing slice/array proof to the decoded list. -/
theorem decodeList_length {α β : Type u} (decode : α → Option β)
    {raws : List α} {values : List β} (h : decodeList decode raws = some values) :
    values.length = raws.length := by
  induction raws generalizing values with
  | nil => simp [decodeList] at h; subst values; rfl
  | cons raw raws ih =>
    simp only [decodeList] at h
    cases hd : decode raw <;> simp [hd] at h
    rename_i value
    cases hs : decodeList decode raws <;> simp [hs] at h
    rename_i tail
    subst values
    simp [ih hs]

@[reducible] instance modelList {α : Type u} [ma : RustModel α] : RustModel (List α) :=
  ⟨List ma.Model, decodeList ma.decode⟩

/-- Mathematical slice shape; its length bound needs no child decoder. -/
abbrev SliceValue (Element : Type u) :=
  { values : List Element // values.length ≤ Usize.max }

/-- Mathematical array shape; its fixed length needs no child decoder. -/
abbrev ArrayValue (Element : Type u) (n : Usize) :=
  { values : List Element // values.length = n.val }

@[reducible] instance modelSlice {α : Type u} [ma : RustModel α] : RustModel (Slice α) where
  Model := SliceValue ma.Model
  decode raw := match h : decodeList ma.decode raw.val with
    | none => none
    | some values => some ⟨values, (decodeList_length ma.decode h) ▸ raw.property⟩

@[reducible] instance modelArray {α : Type u} (n : Usize) [ma : RustModel α] :
    RustModel (Aeneas.Std.Array α n) where
  Model := ArrayValue ma.Model n
  decode raw := match h : decodeList ma.decode raw.val with
    | none => none
    | some values => some ⟨values, (decodeList_length ma.decode h) ▸ raw.property⟩

-- This is Rust's Ok/Err payload type. Either constructor is admitted exactly
-- when its selected child decodes, independently of Aeneas execution Result.
@[reducible] instance modelRustResult {α : Type u} {β : Type v} [ma : RustModel α] [mb : RustModel β] :
    RustModel (core.result.Result α β) where
  Model := core.result.Result ma.Model mb.Model
  decode | .Ok raw => (ma.decode raw).map .Ok | .Err raw => (mb.decode raw).map .Err

/-- Reject borrow continuations even when nested inside supported containers. -/
meta partial def rejectEscapingFunctions (carrierType : Expr) : MetaM Unit := do
  let carrierType ← whnf carrierType
  if carrierType.isForall then
    throwError "Unsupported escaping function or backward reconstruction in model carrier"
  -- Only type-valued arguments can hide another carrier. Values such as an
  -- array's fixed length are not recursively treated as modelable types.
  for arg in carrierType.getAppArgs do
    if (← whnf (← inferType arg)).isSort then rejectEscapingFunctions arg

end AeneasSpecs
