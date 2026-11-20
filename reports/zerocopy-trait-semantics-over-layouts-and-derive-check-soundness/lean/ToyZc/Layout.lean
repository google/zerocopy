import ToyZc.Basic

/-!
# `repr(C)` layout algorithm

This module contains, in namespace `Toy.Zc`, a self-contained model of the `repr(C)` layout
algorithm: field placement with optional `packed(N)` / `align(N)` modifiers, unions, `repr(C)` and
primitive-representation enums with a tag, and flat `repr(C)` slice DSTs (closed-form size and the
largest fitting element count). `unionLayout` extends `reprCUnion` with the modifiers (and coincides
with it for the empty modifier, `unionLayout_none`).

All sizes are exact natural numbers (no `isize::MAX` overflow). Integer and enum-tag layouts
used later in this package assume `x86_64-unknown-linux-gnu` (integer alignment = size; a
`repr(C)` fieldless enum with discriminants in `i32` range has a 4-byte tag).
-/

namespace Toy.Zc

/-! ## Arithmetic primitives -/

/-- Minimal non-negative padding bytes to add to `n` to reach a multiple of `a`
    when `0 < a`. Totalized to `0` at `a = 0`. -/
def paddingNeeded (n a : Nat) : Nat :=
  if a = 0 then 0
  else
    let r := n % a
    if r = 0 then 0 else a - r

/-- Rounds `n` up to the least multiple of `a` that is `≥ n` (when `0 < a`).
    Totalized to `n` at `a = 0`. -/
def alignUp (n a : Nat) : Nat :=
  n + paddingNeeded n a

/-- Rounds `x` down to the greatest multiple of `a` that is `≤ x` (when `0 < a`).
    Totalized to `0` at `a = 0`. -/
def roundDown (x a : Nat) : Nat :=
  if a = 0 then 0 else (x / a) * a

theorem ex_alignUp_pos : alignUp 5 4 = 8 := rfl
theorem ex_alignUp_neg : alignUp 5 4 ≠ 5 := by decide
theorem ex_roundDown_pos : roundDown 7 4 = 4 := rfl
theorem ex_roundDown_neg : roundDown 7 4 ≠ 7 := by decide

/-- Unbundled layout parameters of a single sized field: byte `size` and alignment
    requirement `align`. -/
structure FieldLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- Mutually exclusive alignment modifiers applicable to a `#[repr(C)]` struct:
    * `none`: plain `#[repr(C)]`;
    * `packed n`: `#[repr(C, packed(n))]`, capping each field's effective alignment at `n`;
    * `aligned n`: `#[repr(C, align(n))]`, raising the struct's overall alignment to at least `n`. -/
inductive ReprModifier where
  | none
  | packed (n : Nat)
  | aligned (n : Nat)
  deriving Repr, DecidableEq, BEq

/-- Effective alignment used to position a field of natural alignment `a` under
    modifier `m`: `packed(p)` clamps each field's alignment to `min a p`. -/
def effFieldAlign (m : ReprModifier) (a : Nat) : Nat :=
  match m with
  | .packed p => min a p
  | .none | .aligned _ => a

/-! ## `repr(C)` structs -/

/-- Computed layout of a struct: byte offsets in declaration order, unpadded end
    cursor after the final field, total padded byte `size`, and overall `align`. -/
structure StructLayout where
  offsets : List Nat
  endOffset : Nat
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- Sequentially places `fields` in declaration order starting at byte offset `cursor`,
    aligning each field to `effFieldAlign m f.align` and advancing by `f.size`.
    Returns `(offsets, endOffset)`. -/
def placeFields (m : ReprModifier) (cursor : Nat) : List FieldLayout → List Nat × Nat
  | [] => ([], cursor)
  | f :: fs =>
    let off := alignUp cursor (effFieldAlign m f.align)
    let (restOffs, endOff) := placeFields m (off + f.size) fs
    (off :: restOffs, endOff)

/-- Maximum effective alignment across `fields`, with base `1` for empty structs. -/
def fieldsMaxAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  fields.foldl (fun acc f => max acc (effFieldAlign m f.align)) 1

/-- Overall alignment of a `#[repr(C)]` struct with modifier `m`. -/
def structAlign (m : ReprModifier) (fields : List FieldLayout) : Nat :=
  match m with
  | .aligned n => max (fieldsMaxAlign m fields) n
  | .none | .packed _ => fieldsMaxAlign m fields

/-- Compute the `#[repr(C)]` struct layout for `fields` under modifier `m`. -/
def reprCStruct (m : ReprModifier) (fields : List FieldLayout) : StructLayout :=
  let (offs, endOff) := placeFields m 0 fields
  let a := structAlign m fields
  { offsets := offs
    endOffset := endOff
    size := alignUp endOff a
    align := a }

theorem ex_reprCStruct_pos_three_ints :
    reprCStruct .none [⟨2, 2⟩, ⟨1, 1⟩, ⟨4, 4⟩] =
      { offsets := [0, 2, 4], endOffset := 8, size := 8, align := 4 } := rfl

theorem ex_reprCStruct_neg_no_padding_assumed :
    (reprCStruct .none [⟨1, 1⟩, ⟨4, 4⟩]).size ≠ 5 := by decide

/-! ## Unions -/

/-- Computed layout of a union: `size` and `align`. -/
structure UnionLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- Compute the `#[repr(C)]` union layout for `fields` : all fields at offset `0`. -/
def reprCUnion (fields : List FieldLayout) : UnionLayout :=
  let maxAlign := fields.foldl (fun acc f => max acc f.align) 1
  let maxSize := fields.foldl (fun acc f => max acc f.size) 0
  { size := alignUp maxSize maxAlign
    align := maxAlign }

/-- `#[repr(C)]` union layout under modifier `m`: every field at offset
`0`; alignment is the maximum effective field alignment (`packed(p)` clamps each field's
alignment to `min a p`; base `1`), raised to `n` under `align(n)`; size is the maximum field
size rounded up to that alignment (Rust Reference, "Type layout", `#[repr(C)]` unions and the
alignment modifiers). -/
def unionLayout (m : ReprModifier) (fields : List FieldLayout) : UnionLayout :=
  let a := fields.foldl (fun acc f => max acc (effFieldAlign m f.align)) 1
  let a' := match m with
    | .aligned n => max a n
    | .none | .packed _ => a
  let maxSize := fields.foldl (fun acc f => max acc f.size) 0
  { size := alignUp maxSize a'
    align := a' }

theorem unionLayout_none (fields : List FieldLayout) :
    unionLayout .none fields = reprCUnion fields := rfl

theorem ex_unionLayout_pos : unionLayout .none [⟨1, 1⟩, ⟨2, 2⟩] = ⟨2, 2⟩ := rfl
theorem ex_unionLayout_pos_packed : unionLayout (.packed 1) [⟨1, 1⟩, ⟨2, 2⟩] = ⟨2, 1⟩ := rfl
theorem ex_unionLayout_neg : (unionLayout (.aligned 4) [⟨1, 1⟩, ⟨2, 2⟩]).size ≠ 2 := by decide

/-! ## Enums -/

/-- Computed layout of a tagged data-carrying enum: total `size`, `align`, `tagOffset`, and for
each variant a list of byte offsets (relative to the start of the enum) of its payload fields. -/
structure EnumLayout where
  size : Nat
  align : Nat
  tagOffset : Nat
  variantFieldOffsets : List (List Nat)
  deriving Repr, DecidableEq, BEq

/-- `#[repr(C)]` data-carrying enum layout parameterized by the tag layout `tag`: the two-field
`#[repr(C)]` struct `{ tag, union { reprCStruct .none v | v ∈ variants } }` . -/
def reprCEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map (reprCStruct .none)
  let payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  let outer := reprCStruct .none [tag, ⟨payload.size, payload.align⟩]
  let payloadOffset := alignUp tag.size payload.align
  { size := outer.size
    align := outer.align
    tagOffset := outer.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.map (· + payloadOffset) }

/-- `#[repr(Int)]` data-carrying enum layout parameterized by primitive tag layout `tag`: the
`#[repr(C)]` union of per-variant `#[repr(C)]` structs `tag :: v` . -/
def reprIntEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let u := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  { size := u.size
    align := u.align
    tagOffset := match variantStructs with | [] => 0 | s :: _ => s.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.tail }

theorem ex_reprIntEnum_pos_u8_packs_after_tag :
    reprIntEnum ⟨1, 1⟩ [[⟨1, 1⟩, ⟨2, 2⟩], []] =
      { size := 4, align := 2, tagOffset := 0,
        variantFieldOffsets := [[1, 2], []] } := rfl

theorem ex_reprIntEnum_neg_not_reprC_u8 :
    (reprIntEnum ⟨1, 1⟩ [[⟨1, 1⟩, ⟨2, 2⟩], []]).size ≠ 6 := by decide

theorem ex_reprCEnum_pos :
    reprCEnum ⟨4, 4⟩ [[⟨1, 1⟩], []] =
      { size := 8, align := 4, tagOffset := 0, variantFieldOffsets := [[4], []] } := rfl

theorem ex_reprCEnum_neg_not_packed_after_tag :
    (reprCEnum ⟨1, 1⟩ [[⟨1, 1⟩, ⟨2, 2⟩], []]).size ≠ 4 := by decide

/-! ## Slice-tailed `repr(C)` DSTs -/

/-- Specification of a flat `#[repr(C)]` slice-tailed DST: fixed prefix `headFields`,
    alignment modifier `modifier`, and trailing slice `[T]` with element layout `elem`. -/
structure SliceDstSpec where
  modifier : ReprModifier
  headFields : List FieldLayout
  elem : FieldLayout
  deriving Repr, DecidableEq, BEq

/-- Byte offset at which the trailing slice `[T]` begins (independent of `n`). -/
def dstTailOffset (d : SliceDstSpec) : Nat :=
  let (_, headEnd) := placeFields d.modifier 0 d.headFields
  alignUp headEnd (effFieldAlign d.modifier d.elem.align)

/-- Overall alignment of the slice-tailed DST (independent of `n`). -/
def dstAlign (d : SliceDstSpec) : Nat :=
  structAlign d.modifier (d.headFields ++ [d.elem])

/-- Closed-form total byte size of the slice-tailed DST for `n` trailing elements:
    `alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)`. -/
def dstSize (d : SliceDstSpec) (n : Nat) : Nat :=
  alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)

theorem ex_dstSize_pos :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    dstTailOffset d = 3 ∧ dstAlign d = 2 ∧ dstSize d 0 = 4 ∧ dstSize d 1 = 4 ∧ dstSize d 2 = 6 := by
  decide

theorem ex_dstSize_neg_unaligned :
    let d : SliceDstSpec := ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩
    dstSize d 0 ≠ 3 := by
  decide

/-- Largest trailing slice element count `n` with `dstSize d n ≤ bufferLen` :
    `none` if `d.elem.size = 0` or if no `n` fits. -/
def maxSliceElems (d : SliceDstSpec) (bufferLen : Nat) : Option Nat :=
  if d.elem.size = 0 then none
  else
    let cap := roundDown bufferLen (dstAlign d)
    if cap < dstTailOffset d then none
    else some ((cap - dstTailOffset d) / d.elem.size)

theorem ex_maxSliceElems_pos_some :
    maxSliceElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 = some 1 := rfl

theorem ex_maxSliceElems_neg_naive :
    maxSliceElems ⟨.none, [⟨2, 2⟩, ⟨1, 1⟩], ⟨1, 1⟩⟩ 5 ≠ some 2 := by decide

end Toy.Zc
