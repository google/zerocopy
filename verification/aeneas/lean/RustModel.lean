/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import Aeneas
public import Rust.Storage
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
  /-- Optional language-level byte interpretation. Absence means that this
  provider cannot establish byte-validity laws.
  This decoder operates independently of the optional library invariant. -/
  representation : Option (Rust.Storage.BitDecoder Raw) := none

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

/-- IntoBytes needs an available physical decoder whose entire language-valid
representation domain is initialized. A library decoder cannot shrink this
quantification: even a provider which rejects every mathematical value must
establish initialization for all bytes accepted by its physical decoder. -/
def RustModel.initializedRepresentation (Raw : Type u) [m : RustModel Raw] : Prop :=
  match m.representation with
  | none => False
  | some decoder => decoder.Initialized

/-- Constructing a typed value from bytes requires language-level decoding.
The unsupported-model case also fails closed. No invalid Raw is produced. -/
def RustModel.decodeBitsResult {Raw : Type u} (m : RustModel Raw)
    (bytes : List Rust.Storage.AMByte) : Result Raw :=
  match m.representation with
  | none => .fail .undef
  | some decoder => Result.ofOption (decoder.asStorageDecoder.run () bytes) .undef

/-- Compose execution with the retained provider's mathematical decoder.
An earlier execution failure or divergence is preserved. A rejected returned
value becomes `undef`, marking an unadmitted value of this modeled computation;
this does not assert that every optional model rejection immediately causes
undefined behavior in Rust. -/
def RustModel.decodeResult {Raw : Type u} (m : RustModel Raw)
    (run : Result Raw) : Result m.Model := do
  let raw ← run
  Result.ofOption (m.decode raw) .undef

/-- Language-level decoding followed by the retained mathematical decoder.
Failure at either stage is preserved, rather than supplying a default value. -/
def RustModel.decodeBytesResult {Raw : Type u} (m : RustModel Raw)
    (bytes : List Rust.Storage.AMByte) : Result m.Model :=
  m.decodeResult (m.decodeBitsResult bytes)

/-- Explicit metadata-indexed language decoding. No metadata is guessed from
byte length, and every rejected width, representation, or metadata returns undef. -/
def RustModel.decodeStorageBitsResult {Raw : Type u} {Metadata : Type v}
    [DecidableEq Metadata] (physical : Rust.Storage.StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List Rust.Storage.AMByte) : Result Raw :=
  Result.ofOption (physical.run metadata bytes) .undef

/-- Apply the retained mathematical provider after checked physical decoding.
An explicit decoder supplies the layout and language domain; it does not
supply a Rust ABI or provenance correspondence by virtue of its type. -/
def RustModel.decodeStorageResult {Raw : Type u} {Metadata : Type v}
    [DecidableEq Metadata] (m : RustModel Raw)
    (physical : Rust.Storage.StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List Rust.Storage.AMByte) : Result m.Model :=
  m.decodeResult (RustModel.decodeStorageBitsResult physical metadata bytes)

/-- One guarded composition underlies both Option admission and Aeneas failure. -/
theorem RustModel.decodeStorageResult_as_runWith {Raw : Type u} {Metadata : Type v}
    [DecidableEq Metadata] (m : RustModel Raw)
    (physical : Rust.Storage.StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List Rust.Storage.AMByte) :
    m.decodeStorageResult physical metadata bytes =
      Result.ofOption (physical.runWith m.decode metadata bytes) .undef := by
  cases language : physical.run metadata bytes with
  | none => simp [RustModel.decodeStorageResult, RustModel.decodeStorageBitsResult,
      RustModel.decodeResult, Rust.Storage.StorageDecoder.runWith, language]
  | some raw => simp [RustModel.decodeStorageResult, RustModel.decodeStorageBitsResult,
      RustModel.decodeResult, Rust.Storage.StorageDecoder.runWith, language]

/-- The fixed representation API is the Unit-metadata specialization. -/
theorem RustModel.decodeBytesResult_eq_decodeStorageResult {Raw : Type u} (m : RustModel Raw)
    (physical : Rust.Storage.BitDecoder Raw) (available : m.representation = some physical)
    (bytes : List Rust.Storage.AMByte) :
    m.decodeBytesResult bytes = m.decodeStorageResult physical.asStorageDecoder () bytes := by
  simp [RustModel.decodeBytesResult, RustModel.decodeBitsResult, available,
    RustModel.decodeStorageResult, RustModel.decodeStorageBitsResult]

@[simp] theorem RustModel.decodeResult_ok {Raw : Type u} (m : RustModel Raw) (raw : Raw) :
    m.decodeResult (.ok raw) = Result.ofOption (m.decode raw) .undef := by
  simp [RustModel.decodeResult]

@[simp] theorem RustModel.decodeResult_fail {Raw : Type u} (m : RustModel Raw) (error : Error) :
    m.decodeResult (.fail error) = .fail error := by
  simp [RustModel.decodeResult]

@[simp] theorem RustModel.decodeResult_div {Raw : Type u} (m : RustModel Raw) :
    m.decodeResult .div = .div := by
  simp [RustModel.decodeResult]

/-- A composed success records both the raw execution and this provider's
accepted mathematical value. Neither stage can erase the other's failure. -/
theorem RustModel.decodeResult_eq_ok_iff {Raw : Type u} (m : RustModel Raw)
    (run : Result Raw) (value : m.Model) :
    m.decodeResult run = .ok value ↔
      ∃ raw, run = .ok raw ∧ m.decode raw = some value := by
  cases run with
  | ret raw => cases decoded : m.decode raw <;> simp [decoded]
  | vis effect continuation => simp [RustModel.decodeResult]
  | div => simp

/-- A composed storage success retains the same physical and mathematical
providers, with neither admission stage hidden by the other. -/
theorem RustModel.decodeStorageResult_eq_ok_iff {Raw : Type u} {Metadata : Type v}
    [DecidableEq Metadata] (m : RustModel Raw)
    (physical : Rust.Storage.StorageDecoder Metadata Raw)
    (metadata : Metadata) (bytes : List Rust.Storage.AMByte) (value : m.Model) :
    m.decodeStorageResult physical metadata bytes = .ok value ↔
      ∃ raw, physical.run metadata bytes = some raw ∧ m.decode raw = some value := by
  rw [RustModel.decodeStorageResult_as_runWith,
    ← Rust.Storage.StorageDecoder.runWith_eq_some_iff]
  cases physical.runWith m.decode metadata bytes <;> simp

/-- Total correctness for the composition is the existing decoded-result post
on the original execution, with the provider and postcondition unchanged. -/
theorem RustModel.spec_decodeResult_iff {Raw : Type u} (m : RustModel Raw)
    (run : Result Raw) (post : m.Model → Prop) :
    WP.spec (m.decodeResult run) post ↔
      WP.spec run (fun raw => ∃ value, m.decode raw = some value ∧ post value) := by
  cases run with
  | ret raw => cases decoded : m.decode raw <;> simp [decoded]
  | vis effect continuation => simp [RustModel.decodeResult]
  | div => simp

/-- Partial correctness preserves divergence while still rejecting failures
and returned values that this provider cannot decode. -/
theorem RustModel.dspec_decodeResult_iff {Raw : Type u} (m : RustModel Raw)
    (run : Result Raw) (post : m.Model → Prop) :
    WP.dspec (m.decodeResult run) post ↔
      WP.dspec run (fun raw => ∃ value, m.decode raw = some value ∧ post value) := by
  cases run with
  | ret raw => cases decoded : m.decode raw <;> simp [decoded]
  | vis effect continuation => simp [RustModel.decodeResult]
  | div =>
    simp only [RustModel.decodeResult_div]
    constructor <;> intro _ <;> exact WP.dspec.div _

@[reducible] instance modelBool : RustModel Bool where
  Model := Bool
  decode := some
  representation := some Rust.Storage.boolDecoder
@[reducible] instance modelNat : RustModel Nat := { Model := Nat, «decode» := some }
@[reducible] instance modelInt : RustModel Int := { Model := Int, «decode» := some }
@[reducible] instance modelUnit : RustModel Unit where
  Model := Unit
  decode := some
  representation := some Rust.Storage.unitDecoder

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
  { Model := List ma.Model, «decode» := decodeList ma.decode }

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

/-- Explicit physical slice adapter. The caller supplies a usize element count,
including for zero-sized elements. Its value-level bound is carried by metadata,
so no count is inferred from byte length and no extra Nat admission guard is needed. -/
def RustModel.sliceStorageDecoder {α : Type u} (element : Rust.Storage.BitDecoder α) :
    Rust.Storage.StorageDecoder Usize (Slice α) where
  byteSize count := count.val * element.byteSize
  metadata := Slice.len
  decode count bytes := (Rust.Storage.arrayDecode element count.val bytes).map (fun values =>
    Slice.from values.val (by rw [values.property]; scalar_tac))

/-- The native slice adapter has exactly the fixed-count array admission domain;
only its carrier and explicit usize metadata differ. -/
theorem RustModel.sliceStorageDecoder_run {α : Type u} (element : Rust.Storage.BitDecoder α)
    (count : Usize) (bytes : List Rust.Storage.AMByte) :
    (RustModel.sliceStorageDecoder element).run count bytes =
      ((Rust.Storage.arrayDecoder element count.val).run bytes).map
        (fun values => Slice.from values.val (by rw [values.property]; scalar_tac)) := by
  by_cases width : bytes.length = count.val * element.byteSize
  · simp only [Rust.Storage.StorageDecoder.run, RustModel.sliceStorageDecoder,
      Rust.Storage.BitDecoder.run, Rust.Storage.arrayDecoder, width, ↓reduceIte]
    cases language : Rust.Storage.arrayDecode element count.val bytes with
    | none => rfl
    | some values =>
      have agrees : (Slice.from values.val (by rw [values.property]; scalar_tac)).len = count := by
        apply UScalar.eq_of_val_eq
        simp only [Slice.len_val, Slice.length, Slice.from_val, values.property]
      simp [agrees]
  · simp [Rust.Storage.StorageDecoder.run, RustModel.sliceStorageDecoder,
      Rust.Storage.BitDecoder.run, Rust.Storage.arrayDecoder, width]

/-- The slice adapter preserves the element initialization law. -/
theorem RustModel.sliceStorageDecoder_initialized {α : Type u}
    (element : Rust.Storage.BitDecoder α) (initialized : element.Initialized) :
    (RustModel.sliceStorageDecoder element).Initialized := by
  intro count bytes raw accepted
  have language := ((Rust.Storage.StorageDecoder.run_eq_some_iff _ _ _ _).mp accepted).2.1
  simp only [RustModel.sliceStorageDecoder] at language
  cases decoded : Rust.Storage.arrayDecode element count.val bytes with
  | none => simp [decoded] at language
  | some values => exact Rust.Storage.arrayDecode_initialized element initialized count.val bytes values decoded

@[reducible] instance modelArray {α : Type u} (n : Usize) [ma : RustModel α] :
    RustModel (Aeneas.Std.Array α n) where
  Model := ArrayValue ma.Model n
  decode raw := match h : decodeList ma.decode raw.val with
    | none => none
    | some values => some ⟨values, (decodeList_length ma.decode h) ▸ raw.property⟩
  representation := ma.representation.map (fun element =>
    (Rust.Storage.arrayDecoder element n.val).map
      (fun values => Aeneas.Std.Array.from values.val values.property))

/-- The language-level array representation concatenates element storage.
This theorem concerns every accepted representation, including padding bytes;
it never asks whether the optional library decoder accepts the decoded value. -/
theorem RustModel.initialized_array (α : Type u) [ma : RustModel α] (n : Usize)
    (element : RustModel.initializedRepresentation α) :
    @RustModel.initializedRepresentation (Aeneas.Std.Array α n) (@modelArray α n ma) := by
  cases representation : ma.representation with
  | none => simp [RustModel.initializedRepresentation, representation] at element
  | some decoder =>
    simp only [RustModel.initializedRepresentation, representation] at element
    unfold RustModel.initializedRepresentation
    rw [show (@modelArray α n ma).representation = ma.representation.map (fun element =>
      (Rust.Storage.arrayDecoder element n.val).map
        (fun values => Aeneas.Std.Array.from values.val values.property)) from rfl]
    rw [representation]
    simp only [Option.map_some]
    exact Rust.Storage.BitDecoder.map_initialized _ _
      (Rust.Storage.arrayDecoder_initialized decoder element n.val)

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
