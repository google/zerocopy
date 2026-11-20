import Toy.Layout.Struct

namespace Toy.Layout

/-!
# `#[repr(C)]` Unions, Target-Parameterized C-Enum Tags, and Data-Carrying Enums

This module models:

* `reprCUnion`: `#[repr(C)]` union layout (`r[layout.repr.c.union.size-align]`).
* `CEnumTarget`, `minFittingIntBytes`, `cEnumTagBytes`, `cEnumTagLayout`: target-parameterized
  C-enum tag sizing as a function of the discriminant range `[minDiscr, maxDiscr]` and the
  target's `c_enum_min_size` parameter (`rustc` `discr_range_of_repr`), capturing why bare
  `#[repr(C)]` enum tags are neither pointer-sized nor `c_int`-sized in general.
* `reprCEnum` (and `reprCEnumForTarget`): `#[repr(C)]` and `#[repr(C, Int)]` data-carrying
  enums modeled as `struct { tag, union { variants } }` (`r[layout.repr.c.adt]`,
  `r[layout.repr.primitive-c]`, RFC 2195), parameterized by the tag `FieldLayout`.
* `reprIntEnum`: `#[repr(Int)]` data-carrying enums modeled as a `#[repr(C)]` union of
  per-variant `#[repr(C)]` structs starting with `tag` (`r[layout.repr.primitive.adt]`,
  RFC 2195).
* Separate geometric soundness, structural characterization (`EnumSharedPayload` vs.
  `EnumPerVariantTagged`), alignment validity and equality, size ordering, target-specific
  tag-sizing divergences, and strict `#[repr(u8)]` vs. `#[repr(C, u8)]` separation.
-/

/-- Computed layout of a `#[repr(C)]` union (`r[layout.repr.c.union.size-align]`):
    all fields reside at offset `0`; `align` is the maximum field alignment (or `1` if
    empty) and `size` is the maximum field size rounded up to `align`. -/
structure UnionLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

/-- Compute the `#[repr(C)]` union layout for `fields`. -/
def reprCUnion (fields : List FieldLayout) : UnionLayout :=
  let maxAlign := fields.foldl (fun acc f => max acc f.align) 1
  let maxSize := fields.foldl (fun acc f => max acc f.size) 0
  { size := alignUp maxSize maxAlign
    align := maxAlign }

theorem ex_reprCUnion_pos_rounded :
    reprCUnion [⟨4, 4⟩, ⟨6, 2⟩] = { size := 8, align := 4 } := rfl

theorem ex_reprCUnion_neg_unrounded :
    (reprCUnion [⟨4, 4⟩, ⟨6, 2⟩]).size ≠ 6 := by decide

/-- Computed layout of a tagged data-carrying enum: total `size`, `align`, `tagOffset`
    (derived from the outer or variant struct's first field offset), and for each variant
    a list of byte offsets (relative to the start of the enum) of that variant's payload fields. -/
structure EnumLayout where
  size : Nat
  align : Nat
  tagOffset : Nat
  variantFieldOffsets : List (List Nat)
  deriving Repr, DecidableEq, BEq

/-! ## Target-Parameterized C-Enum Tag Sizing -/

/-- Whether every discriminant in `[minDiscr, maxDiscr]` fits in an unsigned `w`-byte
    two's-complement integer `[0, 2^(8*w) - 1]`. -/
def fitsUnsignedBytes (w : Nat) (minDiscr maxDiscr : Int) : Bool :=
  decide (0 ≤ minDiscr ∧ maxDiscr < (2 : Int) ^ (8 * w))

theorem ex_fitsUnsignedBytes_pos : fitsUnsignedBytes 1 0 255 = true := rfl
theorem ex_fitsUnsignedBytes_neg : fitsUnsignedBytes 1 0 256 = false := rfl

/-- Whether every discriminant in `[minDiscr, maxDiscr]` fits in a signed `w`-byte
    two's-complement integer `[-2^(8*w - 1), 2^(8*w - 1) - 1]`. -/
def fitsSignedBytes (w : Nat) (minDiscr maxDiscr : Int) : Bool :=
  if w = 0 then false
  else decide (-(2 : Int) ^ (8 * w - 1) ≤ minDiscr ∧ maxDiscr < (2 : Int) ^ (8 * w - 1))

theorem ex_fitsSignedBytes_pos : fitsSignedBytes 1 (-128) 127 = true := rfl
theorem ex_fitsSignedBytes_neg : fitsSignedBytes 1 (-129) 127 = false := rfl

/-- Smallest standard integer byte width in `{1, 2, 4, 8, 16}` capable of representing
    every discriminant in `[minDiscr, maxDiscr]` (all unsigned or all signed), modeling
    `min(unsigned_fit, signed_fit)` in `rustc`'s `discr_range_of_repr`
    (`compiler/rustc_middle/src/ty/layout.rs`). -/
def minFittingIntBytes (minDiscr maxDiscr : Int) : Nat :=
  if fitsUnsignedBytes 1 minDiscr maxDiscr || fitsSignedBytes 1 minDiscr maxDiscr then 1
  else if fitsUnsignedBytes 2 minDiscr maxDiscr || fitsSignedBytes 2 minDiscr maxDiscr then 2
  else if fitsUnsignedBytes 4 minDiscr maxDiscr || fitsSignedBytes 4 minDiscr maxDiscr then 4
  else if fitsUnsignedBytes 8 minDiscr maxDiscr || fitsSignedBytes 8 minDiscr maxDiscr then 8
  else 16

theorem ex_minFittingIntBytes_pos_small : minFittingIntBytes 0 1 = 1 := rfl
theorem ex_minFittingIntBytes_pos_signed_i16 : minFittingIntBytes (-1) 200 = 2 := rfl
theorem ex_minFittingIntBytes_pos_large64 : minFittingIntBytes 0 0x100000000 = 8 := rfl
theorem ex_minFittingIntBytes_neg_large_not_4 : minFittingIntBytes 0 0x100000000 ≠ 4 := by decide

/-- Target ABI parameters governing bare `#[repr(C)]` enum tag layout, modeling
    `TargetDataLayout::c_enum_min_size` (`c_enum_min_bits.unwrap_or(c_int_width)`) and
    target scalar integer alignment in `rustc` (`compiler/rustc_target/src/spec/mod.rs`,
    `compiler/rustc_middle/src/ty/layout.rs`). -/
structure CEnumTarget where
  /-- Minimum byte width of a C enum on this target (`4` on `x86_64-unknown-linux-gnu`;
      `1` on `arm-none` / `thumbv7m-none-eabi` / `hexagon-unknown-none-elf`). -/
  cEnumMinBytes : Nat
  /-- Byte layout `(size, align)` of a scalar integer of width `bytes` on this target. -/
  intLayout : Nat → FieldLayout

/-- Tag byte width selected for a bare `#[repr(C)]` enum with discriminant range
    `[minDiscr, maxDiscr]` on `target`: `max target.cEnumMinBytes (minFittingIntBytes minDiscr maxDiscr)`. -/
def cEnumTagBytes (target : CEnumTarget) (minDiscr maxDiscr : Int) : Nat :=
  max target.cEnumMinBytes (minFittingIntBytes minDiscr maxDiscr)

/-- Tag `FieldLayout` selected for a bare `#[repr(C)]` enum with discriminant range
    `[minDiscr, maxDiscr]` on `target`. -/
def cEnumTagLayout (target : CEnumTarget) (minDiscr maxDiscr : Int) : FieldLayout :=
  target.intLayout (cEnumTagBytes target minDiscr maxDiscr)

/-- Target C-enum ABI parameters for `x86_64-unknown-linux-gnu` (`c_enum_min_bits = None`,
    defaulting to `c_int_width = 32` bits -> `4` bytes; scalar integer alignment equals width). -/
def targetX86_64Linux : CEnumTarget :=
  { cEnumMinBytes := 4, intLayout := fun b => ⟨b, b⟩ }

/-- Target C-enum ABI parameters for `thumbv7m-none-eabi` (`arm-none` base sets
    `c_enum_min_bits: Some(8)` -> `1` byte, even though `c_int` is `4` bytes). -/
def targetThumbV7mNoneEabi : CEnumTarget :=
  { cEnumMinBytes := 1, intLayout := fun b => ⟨b, b⟩ }

/-- Target C-enum ABI parameters for `hexagon-unknown-none-elf` (`c_enum_min_bits: Some(8)`
    -> `1` byte). -/
def targetHexagonNoneElf : CEnumTarget :=
  { cEnumMinBytes := 1, intLayout := fun b => ⟨b, b⟩ }

theorem ex_cEnumTagLayout_pos_x86_64 :
    cEnumTagLayout targetX86_64Linux 0 1 = ⟨4, 4⟩ := rfl

theorem ex_cEnumTagLayout_pos_thumb :
    cEnumTagLayout targetThumbV7mNoneEabi 0 1 = ⟨1, 1⟩ := rfl

theorem ex_cEnumTagLayout_pos_x86_64_large_discr :
    cEnumTagLayout targetX86_64Linux 0x100000000 0x100000001 = ⟨8, 8⟩ := rfl

theorem ex_cEnumTagLayout_neg_thumb_not_c_int :
    cEnumTagLayout targetThumbV7mNoneEabi 0 1 ≠ ⟨4, 4⟩ := by decide

theorem ex_cEnumTarget_pos_x86_64_min :
    targetX86_64Linux.cEnumMinBytes = 4 ∧ targetX86_64Linux.intLayout 4 = ⟨4, 4⟩ :=
  ⟨rfl, rfl⟩

theorem ex_cEnumTarget_neg_thumb_min_not_4 :
    targetThumbV7mNoneEabi.cEnumMinBytes ≠ 4 := by decide

theorem ex_cEnumTagBytes_pos_x86_64 :
    cEnumTagBytes targetX86_64Linux 0 1 = 4 := rfl

theorem ex_cEnumTagBytes_pos_thumb :
    cEnumTagBytes targetThumbV7mNoneEabi 0 1 = 1 := rfl

theorem ex_cEnumTagBytes_neg_thumb_not_4 :
    cEnumTagBytes targetThumbV7mNoneEabi 0 1 ≠ 4 := by decide

/-- Concrete tag layouts for common targets, fixed-width primitive tags, and heuristics:
    * `cEnumTagX86_64`: `cEnumTagLayout targetX86_64Linux 0 1` (`⟨4, 4⟩`), the `x86_64-unknown-linux-gnu`
      tag for conforming discriminants (coinciding with `c_int` on that target);
    * `cEnumTagThumbV7m`: `cEnumTagLayout targetThumbV7mNoneEabi 0 1` (`⟨1, 1⟩`), the
      `thumbv7m-none-eabi` tag for small discriminants (`c_enum_min_bits = 8`);
    * `cIntLayout32Bit`: 4-byte `c_int` layout (known not to match conforming bare `#[repr(C)]`
      tags on `arm-none` / `thumb-none` / `hexagon`, and also diverges on non-conforming
      discriminants outside `int`/`unsigned int`, which the Rust Reference disallows and `rustc`
      currently widens to 8 bytes under the future-incompatibility lint
      `repr_c_enums_larger_than_int`);
    * `usizeTag64`: 8-byte pointer-sized layout (known not to match bare `#[repr(C)]` tags
      for small discriminants on `x86_64-unknown-linux-gnu`);
    * `u8Tag`, `u16Tag`: fixed-width primitive tags for `#[repr(u8)]`/`#[repr(C, u8)]` and
      `#[repr(u16)]`/`#[repr(C, u16)]`. -/
def cEnumTagX86_64 : FieldLayout := cEnumTagLayout targetX86_64Linux 0 1
def cEnumTagThumbV7m : FieldLayout := cEnumTagLayout targetThumbV7mNoneEabi 0 1
def cIntLayout32Bit : FieldLayout := ⟨4, 4⟩
def usizeTag64 : FieldLayout := ⟨8, 8⟩
def u8Tag : FieldLayout := ⟨1, 1⟩
def u16Tag : FieldLayout := ⟨2, 2⟩

/-! ## `reprCEnum` and `reprIntEnum` Layout Functions -/

/-- `#[repr(C)]` (and `#[repr(C, Int)]`) data-carrying enum layout parameterized by
    the tag layout `tag`. Modeled directly from `r[layout.repr.c.adt]` and RFC 2195 as the
    two-field `#[repr(C)]` struct `{ tag, union { reprCStruct .none v | v ∈ variants } }`.
    `tagOffset` is read from `outer.offsets`. -/
def reprCEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map (reprCStruct .none)
  let payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  let outer := reprCStruct .none [tag, ⟨payload.size, payload.align⟩]
  let payloadOffset := alignUp tag.size payload.align
  { size := outer.size
    align := outer.align
    tagOffset := outer.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.map (· + payloadOffset) }

/-- Target-parameterized bare `#[repr(C)]` enum layout: resolves `tag` from `target`
    and discriminant range `[minDiscr, maxDiscr]` via `cEnumTagLayout`, then applies
    `reprCEnum`. -/
def reprCEnumForTarget (target : CEnumTarget) (minDiscr maxDiscr : Int)
    (variants : List (List FieldLayout)) : EnumLayout :=
  reprCEnum (cEnumTagLayout target minDiscr maxDiscr) variants

theorem ex_reprCEnum_pos_reference_enum :
    reprCEnum cEnumTagX86_64 [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], [⟨4, 4⟩, ⟨1, 1⟩], []] =
      { size := 24, align := 8, tagOffset := 0,
        variantFieldOffsets := [[8], [8, 16], [8, 12], []] } := rfl

theorem ex_reprCEnum_neg_not_packed_after_tag :
    (reprCEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]).size ≠ 4 := by decide

theorem ex_reprCEnumForTarget_pos_thumb :
    reprCEnumForTarget targetThumbV7mNoneEabi 0 1 [[⟨1, 1⟩], []] =
      { size := 2, align := 1, tagOffset := 0, variantFieldOffsets := [[1], []] } := rfl

theorem ex_reprCEnumForTarget_neg_thumb_not_8 :
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 [[⟨1, 1⟩], []]).size ≠ 8 := by decide

/-- `#[repr(Int)]` data-carrying enum layout parameterized by primitive tag layout `tag`.
    Modeled directly from `r[layout.repr.primitive.adt]` and RFC 2195 as the `#[repr(C)]`
    union of per-variant `#[repr(C)]` structs `tag :: v`. `tagOffset` is read from the
    computed variant struct offsets (defaulting to `0` when `variants = []`). -/
def reprIntEnum (tag : FieldLayout) (variants : List (List FieldLayout)) : EnumLayout :=
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let u := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  { size := u.size
    align := u.align
    tagOffset := match variantStructs with | [] => 0 | s :: _ => s.offsets.headD 0
    variantFieldOffsets := variantStructs.map fun s => s.offsets.tail }

theorem ex_reprIntEnum_pos_u8_packs_after_tag :
    reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []] =
      { size := 4, align := 2, tagOffset := 0,
        variantFieldOffsets := [[1, 2], []] } := rfl

theorem ex_reprIntEnum_neg_not_reprC_u8 :
    (reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]).size ≠ 6 := by decide

/-! ## Separate Named Enum Layout Soundness and Structural Predicates -/

/-- The discriminant tag starts at byte offset `0`. Holds by construction of `reprCStruct`
    (`alignUp 0 _ = 0`) for both `reprCEnum` and `reprIntEnum`. -/
def EnumTagAtZero (E : EnumLayout) : Prop :=
  E.tagOffset = 0

theorem ex_enumTagAtZero_pos :
    EnumTagAtZero (reprCEnum cEnumTagX86_64 [[⟨1, 1⟩], []]) := rfl

theorem ex_enumTagAtZero_neg :
    ¬ EnumTagAtZero { size := 8, align := 4, tagOffset := 4, variantFieldOffsets := [[]] } := by
  simp [EnumTagAtZero]

/-- Definitional lemma: `reprCEnum` always places the tag at offset `0` because the outer
    struct places its first field at `alignUp 0 tag.align = 0`. -/
theorem reprCEnum_tagOffset_zero (tag : FieldLayout) (variants : List (List FieldLayout)) :
    EnumTagAtZero (reprCEnum tag variants) := by
  simp [EnumTagAtZero, reprCEnum, reprCStruct, placeFields, effFieldAlign, alignUp_zero]

/-- Definitional lemma: `reprIntEnum` always places the tag at offset `0`. -/
theorem reprIntEnum_tagOffset_zero (tag : FieldLayout) (variants : List (List FieldLayout)) :
    EnumTagAtZero (reprIntEnum tag variants) := by
  cases variants with
  | nil => rfl
  | cons v vs =>
    simp [EnumTagAtZero, reprIntEnum, reprCStruct, placeFields, effFieldAlign, alignUp_zero]

/-- Definitional lemma: in `reprIntEnum`, every variant struct places the tag at offset `0`. -/
theorem reprIntEnum_all_variants_tag_at_zero (tag : FieldLayout) (v : List FieldLayout) :
    (reprCStruct .none (tag :: v)).offsets.head? = some 0 := by
  simp [reprCStruct, placeFields, effFieldAlign, alignUp_zero]

/-- The enum's overall alignment is a power of two divisible by the tag's alignment
    and by every field's alignment in every variant. -/
def EnumAlignValid (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  IsPowerOfTwo E.align ∧
  tag.align ∣ E.align ∧
  ∀ v ∈ variants, ∀ f ∈ v, f.align ∣ E.align

theorem ex_enumAlignValid_pos :
    EnumAlignValid cEnumTagX86_64 [[⟨1, 1⟩], []] (reprCEnum cEnumTagX86_64 [[⟨1, 1⟩], []]) := by
  refine ⟨⟨2, rfl⟩, ⟨1, rfl⟩, ?_⟩
  intro v hv f hf
  simp at hv
  rcases hv with rfl | rfl
  · simp at hf
    rcases hf with rfl
    exact ⟨4, rfl⟩
  · cases hf

theorem ex_enumAlignValid_neg :
    ¬ EnumAlignValid ⟨4, 4⟩ [[⟨1, 1⟩]]
        { size := 4, align := 2, tagOffset := 0, variantFieldOffsets := [[4]] } := by
  intro ⟨_, ⟨q, hq⟩, _⟩
  simp at hq
  omega

/-- The enum's total size is a multiple of its alignment and at least `tag.size`. -/
def EnumSizeValid (tag : FieldLayout) (E : EnumLayout) : Prop :=
  E.align ∣ E.size ∧ tag.size ≤ E.size

theorem ex_enumSizeValid_pos :
    EnumSizeValid cEnumTagX86_64 (reprCEnum cEnumTagX86_64 [[⟨1, 1⟩], []]) :=
  ⟨⟨2, rfl⟩, by decide⟩

theorem ex_enumSizeValid_neg :
    ¬ EnumSizeValid cEnumTagX86_64
        { size := 0, align := 1, tagOffset := 0, variantFieldOffsets := [] } := by
  intro ⟨_, hle⟩
  simp [cEnumTagX86_64, cEnumTagLayout, targetX86_64Linux, cEnumTagBytes, minFittingIntBytes,
    fitsUnsignedBytes, fitsSignedBytes] at hle

/-- Every variant's payload fields match the variant's field count, start at or after
    `tag.size` (disjoint from the tag), are aligned to their own alignments inside the
    enum, are ordered non-overlapping, and lie within `[0, E.size]`. -/
def EnumVariantsValid (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  E.variantFieldOffsets.length = variants.length ∧
  ∀ (k : Nat) (hk : k < variants.length) (ho : k < E.variantFieldOffsets.length),
    let v := variants[k]
    let offs := E.variantFieldOffsets[k]
    offs.length = v.length ∧
    (∀ (j : Nat) (hj : j < v.length) (hjo : j < offs.length),
      tag.size ≤ offs[j] ∧
      v[j].align ∣ offs[j] ∧
      offs[j] + v[j].size ≤ E.size) ∧
    (∀ (j1 j2 : Nat) (h1 : j1 < v.length) (h2 : j2 < v.length)
       (ho1 : j1 < offs.length) (ho2 : j2 < offs.length),
      j1 < j2 → offs[j1] + v[j1].size ≤ offs[j2])

theorem ex_enumVariantsValid_pos :
    EnumVariantsValid cEnumTagX86_64 [[⟨1, 1⟩], []] (reprCEnum cEnumTagX86_64 [[⟨1, 1⟩], []]) := by
  have hE : reprCEnum cEnumTagX86_64 [[⟨1, 1⟩], []] =
      { size := 8, align := 4, tagOffset := 0, variantFieldOffsets := [[4], []] } := rfl
  rw [hE]
  refine ⟨rfl, ?_⟩
  intro k hk ho
  match k with
  | 0 =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj hjo
      match j with
      | 0 => exact ⟨by have : cEnumTagX86_64.size = 4 := rfl; simp [this], ⟨4, rfl⟩, by simp⟩
      | _ + 1 => simp at hj
    · intro j1 j2 h1 h2 ho1 ho2 hlt
      simp at h1 h2
      omega
  | 1 =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj _
      simp at hj
    · intro j1 j2 h1 _ _ _ _
      simp at h1
  | _ + 2 => simp at hk; omega

theorem ex_enumVariantsValid_neg_misaligned :
    ¬ EnumVariantsValid ⟨1, 1⟩ [[⟨2, 2⟩], [⟨3, 3⟩]]
        (reprCEnum ⟨1, 1⟩ [[⟨2, 2⟩], [⟨3, 3⟩]]) := by
  have hE : reprCEnum ⟨1, 1⟩ [[⟨2, 2⟩], [⟨3, 3⟩]] =
      { size := 6, align := 3, tagOffset := 0, variantFieldOffsets := [[3], [3]] } := rfl
  rw [hE]
  intro ⟨_, hvars⟩
  have h0 := (hvars 0 (by decide) (by decide)).2.1 0 (by decide) (by decide)
  rcases h0.2.1 with ⟨q, hq⟩
  simp at hq
  omega

/-- Shared-payload-union structural predicate distinguishing `#[repr(C)]` / `#[repr(C, Int)]`
    from `#[repr(Int)]` and from over-padded layouts: every variant's fields are placed at
    the common union offset `payloadOffset = alignUp tag.size payload.align` plus their
    per-variant `reprCStruct .none` offsets, and `E.size` is the least multiple of `E.align`
    at least `payloadOffset + payload.size`. -/
def EnumSharedPayload (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  let variantStructs := variants.map (reprCStruct .none)
  let payload := reprCUnion (variantStructs.map fun s => ⟨s.size, s.align⟩)
  let payloadOffset := alignUp tag.size payload.align
  E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.map (· + payloadOffset)) ∧
  IsLeastMultipleGe E.size (payloadOffset + payload.size) E.align

theorem ex_enumSharedPayload_pos :
    EnumSharedPayload u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []] (reprCEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]) := by
  refine ⟨rfl, by decide, ⟨3, rfl⟩, ?_⟩
  rintro m hle ⟨q, rfl⟩
  dsimp [reprCEnum, reprCUnion, reprCStruct, placeFields, structAlign, fieldsMaxAlign,
    effFieldAlign, alignUp, paddingNeeded, u8Tag] at hle ⊢
  omega

theorem ex_enumSharedPayload_neg_reprInt :
    ¬ EnumSharedPayload u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]
        (reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]) := by
  intro ⟨hoffs, _⟩
  revert hoffs
  decide

theorem ex_enumSharedPayload_neg_padded :
    ¬ EnumSharedPayload u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]
        { size := 64, align := 2, tagOffset := 0, variantFieldOffsets := [[10, 20], []] } := by
  intro ⟨hoffs, _⟩
  revert hoffs
  decide

/-- Per-variant tag-prefix structural predicate distinguishing `#[repr(Int)]` from
    `#[repr(C, Int)]` and from over-padded layouts: each variant `v` is laid out independently
    as `reprCStruct .none (tag :: v)` (allowing payload fields to pack immediately after
    `tag`), and `E.size` is the least multiple of `E.align` at least the maximum per-variant
    struct size. -/
def EnumPerVariantTagged (tag : FieldLayout) (variants : List (List FieldLayout)) (E : EnumLayout) : Prop :=
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let maxVarSize := variantStructs.foldl (fun acc s => max acc s.size) 0
  E.variantFieldOffsets = variantStructs.map (fun s => s.offsets.tail) ∧
  IsLeastMultipleGe E.size maxVarSize E.align

theorem ex_enumPerVariantTagged_pos :
    EnumPerVariantTagged u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []] (reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]) := by
  refine ⟨rfl, by decide, ⟨2, rfl⟩, ?_⟩
  rintro m hle ⟨q, rfl⟩
  have h1 : ((List.map (fun v => reprCStruct .none (u8Tag :: v)) [[⟨1, 1⟩, ⟨2, 2⟩], []]).foldl
      (fun acc s => max acc s.size) 0) = 4 := rfl
  have h2 : (reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]).size = 4 := rfl
  have h3 : (reprIntEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]).align = 2 := rfl
  change _ ≤ _ at hle
  rw [h1, h3] at hle
  rw [h2, h3]
  omega

theorem ex_enumPerVariantTagged_neg_reprC :
    ¬ EnumPerVariantTagged u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]
        (reprCEnum u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]) := by
  intro ⟨hoffs, _⟩
  revert hoffs
  decide

theorem ex_enumPerVariantTagged_neg_padded :
    ¬ EnumPerVariantTagged u8Tag [[⟨1, 1⟩, ⟨2, 2⟩], []]
        { size := 64, align := 2, tagOffset := 0, variantFieldOffsets := [[10, 20], []] } := by
  intro ⟨hoffs, _⟩
  revert hoffs
  decide

/-! ## Result 4: Enum Geometry, Alignment, Size Ordering, and Target Tag-Sizing Divergences -/

private theorem foldl_map_eq {α β γ : Type} (f : γ → β → γ) (h : α → β)
    (xs : List α) (init : γ) :
    (xs.map h).foldl f init = xs.foldl (fun acc x => f acc (h x)) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih (f init (h x))

private theorem placeFields_two_none (f1 f2 : FieldLayout) :
    placeFields .none 0 [f1, f2] =
      ([0, alignUp f1.size f2.align], alignUp f1.size f2.align + f2.size) := by
  rw [placeFields_cons, placeFields_cons]
  simp [placeFields, effFieldAlign, alignUp_zero]

private theorem reprCUnion_align_ge_one (fs : List FieldLayout) :
    1 ≤ (reprCUnion fs).align := by
  unfold reprCUnion
  exact foldl_max_ge_init_gen (fun (f : FieldLayout) => f.align) fs 1

private theorem reprCUnion_align_ge_mem (fs : List FieldLayout) {f : FieldLayout} (hf : f ∈ fs) :
    f.align ≤ (reprCUnion fs).align := by
  unfold reprCUnion
  exact foldl_max_ge_mem_gen (fun (g : FieldLayout) => g.align) fs 1 hf

private theorem reprCUnion_align_le (fs : List FieldLayout) (k : Nat)
    (hk1 : 1 ≤ k) (hfs : ∀ f ∈ fs, f.align ≤ k) :
    (reprCUnion fs).align ≤ k := by
  unfold reprCUnion
  exact foldl_max_le_gen (fun (g : FieldLayout) => g.align) fs 1 k hk1 hfs

private theorem reprCUnion_size_ge_mem (fs : List FieldLayout) {f : FieldLayout} (hf : f ∈ fs) :
    f.size ≤ (reprCUnion fs).size := by
  unfold reprCUnion
  dsimp only
  have h1 : f.size ≤ fs.foldl (fun acc g => max acc g.size) 0 :=
    foldl_max_ge_mem_gen (fun g => g.size) fs 0 hf
  exact Nat.le_trans h1 (le_alignUp _ _)

/-- Main Result 4a (geometric soundness and shared-payload structure of `reprCEnum`):
    Whenever all variant fields have power-of-two alignments (for *any* `tag`, even without
    an alignment hypothesis on `tag`), `reprCEnum tag variants` satisfies `EnumSizeValid`,
    `EnumVariantsValid`, and `EnumSharedPayload`. -/
theorem reprCEnum_geometry_of_vars_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    let E := reprCEnum tag variants
    EnumSizeValid tag E ∧
    EnumVariantsValid tag variants E ∧
    EnumSharedPayload tag variants E := by
  dsimp only
  let variantStructs := variants.map (reprCStruct .none)
  let uFields : List FieldLayout := variantStructs.map fun s => ⟨s.size, s.align⟩
  let payload := reprCUnion uFields
  let outer := reprCStruct .none [tag, ⟨payload.size, payload.align⟩]
  let payloadOffset := alignUp tag.size payload.align
  let E := reprCEnum tag variants
  have houter_parts := reprCStruct_eq_parts .none [tag, ⟨payload.size, payload.align⟩]
  have houter_end : outer.endOffset = payloadOffset + payload.size := by
    change (reprCStruct .none [tag, ⟨payload.size, payload.align⟩]).endOffset = _
    rw [houter_parts, placeFields_two_none]
  have hE_align_pos : 0 < E.align := by
    have h1 : 1 ≤ structAlign .none [tag, ⟨payload.size, payload.align⟩] :=
      structAlign_ge_one .none [tag, ⟨payload.size, payload.align⟩]
    change 0 < outer.align
    have hal : outer.align = structAlign .none [tag, ⟨payload.size, payload.align⟩] := by
      change (reprCStruct .none [tag, ⟨payload.size, payload.align⟩]).align = _
      rw [houter_parts]
    omega
  have hE_size_eq : E.size = alignUp (payloadOffset + payload.size) E.align := by
    change outer.size = alignUp (payloadOffset + payload.size) outer.align
    have hsz : outer.size = alignUp outer.endOffset outer.align := by
      dsimp only [outer]
      rw [houter_parts]
    rw [hsz, houter_end]
  have hshared : EnumSharedPayload tag variants E := by
    unfold EnumSharedPayload
    refine ⟨rfl, ?_⟩
    change IsLeastMultipleGe E.size (payloadOffset + payload.size) E.align
    rw [hE_size_eq]
    exact alignUp_isLeastMultipleGe hE_align_pos
  have hsz_valid : EnumSizeValid tag E := by
    unfold EnumSizeValid
    rw [hE_size_eq]
    refine ⟨dvd_alignUp hE_align_pos, ?_⟩
    have h1 : tag.size ≤ payloadOffset := le_alignUp tag.size payload.align
    have h2 : payloadOffset + payload.size ≤ alignUp (payloadOffset + payload.size) E.align :=
      le_alignUp _ _
    omega
  have hpay_pow2 : IsPowerOfTwo payload.align := by
    apply foldl_max_pow2_gen (fun f => f.align) uFields 1 ex_isPowerOfTwo_pos_1
    intro uf huf
    rcases List.mem_map.mp huf with ⟨s, hs, rfl⟩
    rcases List.mem_map.mp hs with ⟨v, hv, rfl⟩
    exact (reprCStruct_align_pow2_divides .none v (h_vars v hv) trivial).1
  have hpay_pos : 0 < payload.align := isPowerOfTwo_pos hpay_pow2
  have hpay_dvd_off : payload.align ∣ payloadOffset := dvd_alignUp hpay_pos
  refine ⟨hsz_valid, ?_, hshared⟩
  unfold EnumVariantsValid
  have hlen_outer : E.variantFieldOffsets.length = variants.length := by
    simp [E, reprCEnum]
  refine ⟨hlen_outer, ?_⟩
  intro k hk ho
  let v := variants[k]
  have hv_mem : v ∈ variants := List.getElem_mem hk
  let s := reprCStruct .none v
  have hs_mem : s ∈ variantStructs := List.mem_map_of_mem hv_mem
  have huf_mem : (⟨s.size, s.align⟩ : FieldLayout) ∈ uFields := List.mem_map_of_mem hs_mem
  have hs_pos : ∀ f ∈ v, AlignPos f := fun f hf => alignPow2_to_alignPos (h_vars v hv_mem f hf)
  have hs_inv := reprCStruct_invariants_of_align_pos .none v hs_pos ex_modifierPackPos_pos_none
  have hs_pow := reprCStruct_align_pow2_divides .none v (h_vars v hv_mem) trivial
  have hs_align_le_pay : s.align ≤ payload.align := reprCUnion_align_ge_mem uFields huf_mem
  have hs_align_dvd_pay : s.align ∣ payload.align :=
    isPowerOfTwo_dvd_of_le hs_pow.1 hpay_pow2 hs_align_le_pay
  have hs_align_dvd_off : s.align ∣ payloadOffset := Nat.dvd_trans hs_align_dvd_pay hpay_dvd_off
  have hs_size_le_pay : s.size ≤ payload.size := reprCUnion_size_ge_mem uFields huf_mem
  have hoffs_k : E.variantFieldOffsets[k] = s.offsets.map (· + payloadOffset) := by
    simp only [E, reprCEnum, List.getElem_map]
    rfl
  have hs_len : s.offsets.length = v.length := hs_inv.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hoffs_k, List.length_map]
    exact hs_len
  · intro j hj hjo
    have hjs : j < s.offsets.length := by dsimp only [v] at *; omega
    have hoffs_kj : (E.variantFieldOffsets[k])[j] = s.offsets[j] + payloadOffset := by
      simp [hoffs_k]
    change tag.size ≤ (E.variantFieldOffsets[k])[j] ∧
      v[j].align ∣ (E.variantFieldOffsets[k])[j] ∧
      (E.variantFieldOffsets[k])[j] + v[j].size ≤ E.size
    rw [hoffs_kj]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : tag.size ≤ payloadOffset := le_alignUp tag.size payload.align
      omega
    · have hdvd1 : v[j].align ∣ s.offsets[j] := by
        simpa [effFieldAlign] using hs_inv.2.1 j hj hjs
      have hdvd2 : v[j].align ∣ s.align := by
        simpa [effFieldAlign] using hs_pow.2 v[j] (List.getElem_mem hj)
      exact Nat.dvd_add hdvd1 (Nat.dvd_trans hdvd2 hs_align_dvd_off)
    · have hinb : s.offsets[j] + v[j].size ≤ s.endOffset := hs_inv.2.2.2.1 j hj hjs
      have hend_le_sz : s.endOffset ≤ s.size := hs_inv.2.2.2.2.1
      have hpay_le_E : payloadOffset + payload.size ≤ E.size := by
        rw [hE_size_eq]
        exact le_alignUp _ _
      omega
  · intro j1 j2 h1 h2 ho1 ho2 hlt
    have hjs1 : j1 < s.offsets.length := by dsimp only [v] at *; omega
    have hjs2 : j2 < s.offsets.length := by dsimp only [v] at *; omega
    have hoffs_kj1 : (E.variantFieldOffsets[k])[j1] = s.offsets[j1] + payloadOffset := by
      simp [hoffs_k]
    have hoffs_kj2 : (E.variantFieldOffsets[k])[j2] = s.offsets[j2] + payloadOffset := by
      simp [hoffs_k]
    change (E.variantFieldOffsets[k])[j1] + v[j1].size ≤ (E.variantFieldOffsets[k])[j2]
    rw [hoffs_kj1, hoffs_kj2]
    have hord : s.offsets[j1] + v[j1].size ≤ s.offsets[j2] :=
      hs_inv.2.2.1 j1 j2 h1 h2 hjs1 hjs2 hlt
    omega

theorem nv_reprCEnum_geometry_of_vars_pow2 :
    let variants : List (List FieldLayout) := [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], []]
    ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f := by
  dsimp only
  intro v hv f hf
  simp at hv
  rcases hv with rfl | rfl | rfl
  · simp at hf
    rcases hf with rfl
    exact ⟨2, rfl⟩
  · simp at hf
    rcases hf with rfl | rfl
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · cases hf

/-- Canonical counterexample dropping `h_vars` from `reprCEnum_geometry_of_vars_pow2`:
    with `tag = ⟨1, 1⟩` and `variants = [[⟨2, 2⟩], [⟨3, 3⟩]]`, `payloadOffset = alignUp 1 3 = 3`,
    placing variant 0's align-2 field at offset `3` and genuinely violating `EnumVariantsValid`
    (`¬ (2 ∣ 3)`). -/
theorem ce_reprCEnum_geometry_drop_vars_pow2 :
    let tag : FieldLayout := ⟨1, 1⟩
    let variants : List (List FieldLayout) := [[⟨2, 2⟩], [⟨3, 3⟩]]
    let E := reprCEnum tag variants
    ¬ (EnumSizeValid tag E ∧ EnumVariantsValid tag variants E ∧ EnumSharedPayload tag variants E) :=
  fun ⟨_, hv, _⟩ => ex_enumVariantsValid_neg_misaligned hv

/-- Main Result 4b (geometric soundness and per-variant structure of `reprIntEnum`):
    Whenever `variants` is non-empty and every variant field has positive alignment
    (`AlignPos` — neither `AlignPow2` nor any alignment hypothesis on `tag` is required
    for geometric placement), `reprIntEnum tag variants` satisfies `EnumSizeValid`,
    `EnumVariantsValid`, and `EnumPerVariantTagged`. -/
theorem reprIntEnum_geometry_of_nonempty_align_pos
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_nonempty : variants ≠ [])
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPos f) :
    let E := reprIntEnum tag variants
    EnumSizeValid tag E ∧
    EnumVariantsValid tag variants E ∧
    EnumPerVariantTagged tag variants E := by
  dsimp only
  let variantStructs := variants.map fun v => reprCStruct .none (tag :: v)
  let uFields : List FieldLayout := variantStructs.map fun s => ⟨s.size, s.align⟩
  let u := reprCUnion uFields
  let maxVarSize := variantStructs.foldl (fun acc s => max acc s.size) 0
  let E := reprIntEnum tag variants
  have hu_max_eq : uFields.foldl (fun acc f => max acc f.size) 0 = maxVarSize :=
    foldl_map_eq (fun acc (f : FieldLayout) => max acc f.size) (fun s => ⟨s.size, s.align⟩)
      variantStructs 0
  have hE_align_pos : 0 < E.align :=
    Nat.lt_of_lt_of_le (by decide : 0 < 1) (reprCUnion_align_ge_one uFields)
  have hE_size_eq : E.size = alignUp maxVarSize E.align := by
    change u.size = alignUp maxVarSize u.align
    unfold u reprCUnion
    dsimp only
    rw [hu_max_eq]
  have hper : EnumPerVariantTagged tag variants E := by
    unfold EnumPerVariantTagged
    refine ⟨rfl, ?_⟩
    change IsLeastMultipleGe E.size maxVarSize E.align
    rw [hE_size_eq]
    exact alignUp_isLeastMultipleGe hE_align_pos
  have hsz_valid : EnumSizeValid tag E := by
    unfold EnumSizeValid
    rw [hE_size_eq]
    refine ⟨dvd_alignUp hE_align_pos, ?_⟩
    cases hvs : variants with
    | nil => exact absurd hvs h_nonempty
    | cons v0 vs =>
      let s0 := reprCStruct .none (tag :: v0)
      have hs0_mem : s0 ∈ variantStructs := by
        simp [variantStructs, hvs, s0]
      have hs0_le_max : s0.size ≤ maxVarSize :=
        foldl_max_ge_mem_gen (fun s => s.size) variantStructs 0 hs0_mem
      have htag_le_s0 : tag.size ≤ s0.size := by
        have hparts0 := reprCStruct_eq_parts .none (tag :: v0)
        change tag.size ≤ (reprCStruct .none (tag :: v0)).size
        rw [hparts0]
        dsimp only
        rw [placeFields_cons]
        dsimp only [effFieldAlign]
        rw [alignUp_zero, Nat.zero_add]
        exact Nat.le_trans (cursor_le_placeFields_end .none tag.size v0) (le_alignUp _ _)
      have hmax_le_E : maxVarSize ≤ alignUp maxVarSize E.align := le_alignUp _ _
      omega
  refine ⟨hsz_valid, ?_, hper⟩
  unfold EnumVariantsValid
  have hlen_outer : E.variantFieldOffsets.length = variants.length := by
    simp [E, reprIntEnum]
  refine ⟨hlen_outer, ?_⟩
  intro k hk ho
  let v := variants[k]
  have hv_mem : v ∈ variants := List.getElem_mem hk
  let s := reprCStruct .none (tag :: v)
  have hs_mem : s ∈ variantStructs := List.mem_map_of_mem hv_mem
  have hs_le_max : s.size ≤ maxVarSize :=
    foldl_max_ge_mem_gen (fun x => x.size) variantStructs 0 hs_mem
  have hmax_le_E : maxVarSize ≤ E.size := by
    rw [hE_size_eq]
    exact le_alignUp _ _
  have hs_parts := reprCStruct_eq_parts .none (tag :: v)
  have hs_tail : s.offsets.tail = (placeFields .none tag.size v).1 := by
    change (reprCStruct .none (tag :: v)).offsets.tail = _
    rw [hs_parts]
    dsimp only
    rw [placeFields_cons]
    simp [effFieldAlign, alignUp_zero]
  have hs_end : s.endOffset = (placeFields .none tag.size v).2 := by
    change (reprCStruct .none (tag :: v)).endOffset = _
    rw [hs_parts]
    dsimp only
    rw [placeFields_cons]
    simp [effFieldAlign, alignUp_zero]
  have hs_end_le_sz : s.endOffset ≤ s.size := (reprCStruct_sizeMinimalAligned .none (tag :: v)).1
  have hoffs_k : E.variantFieldOffsets[k] = (placeFields .none tag.size v).1 := by
    have hk_eq : E.variantFieldOffsets[k] = s.offsets.tail := by
      simp [E, reprIntEnum, v, s]
    rw [hk_eq, hs_tail]
  have hv_len : (placeFields .none tag.size v).1.length = v.length :=
    placeFields_length .none tag.size v
  refine ⟨?_, ?_, ?_⟩
  · rw [hoffs_k]
    exact hv_len
  · intro j hj hjo
    have hj_pl : j < (placeFields .none tag.size v).1.length := by dsimp only [v] at *; omega
    have hoffs_kj : (E.variantFieldOffsets[k])[j] = (placeFields .none tag.size v).1[j] := by
      simp [hoffs_k]
    change tag.size ≤ (E.variantFieldOffsets[k])[j] ∧
      v[j].align ∣ (E.variantFieldOffsets[k])[j] ∧
      (E.variantFieldOffsets[k])[j] + v[j].size ≤ E.size
    rw [hoffs_kj]
    refine ⟨?_, ?_, ?_⟩
    · exact cursor_le_placeFields_getElem .none tag.size v j hj_pl
    · simpa [effFieldAlign] using
        placeFields_aligned .none tag.size v (h_vars v hv_mem) ex_modifierPackPos_pos_none j hj hj_pl
    · have hinb := placeFields_inBounds .none tag.size v j hj hj_pl
      omega
  · intro j1 j2 h1 h2 ho1 ho2 hlt
    have hj1_pl : j1 < (placeFields .none tag.size v).1.length := by dsimp only [v] at *; omega
    have hj2_pl : j2 < (placeFields .none tag.size v).1.length := by dsimp only [v] at *; omega
    have hoffs_kj1 : (E.variantFieldOffsets[k])[j1] = (placeFields .none tag.size v).1[j1] := by
      simp [hoffs_k]
    have hoffs_kj2 : (E.variantFieldOffsets[k])[j2] = (placeFields .none tag.size v).1[j2] := by
      simp [hoffs_k]
    change (E.variantFieldOffsets[k])[j1] + v[j1].size ≤ (E.variantFieldOffsets[k])[j2]
    rw [hoffs_kj1, hoffs_kj2]
    exact placeFields_orderedNonOverlapping .none tag.size v j1 j2 h1 h2 hj1_pl hj2_pl hlt

theorem nv_reprIntEnum_geometry_of_nonempty_align_pos :
    let variants : List (List FieldLayout) := [[⟨1, 1⟩, ⟨2, 2⟩], []]
    variants ≠ [] ∧ ∀ v ∈ variants, ∀ f ∈ v, AlignPos f := by
  refine ⟨by decide, ?_⟩
  intro v hv f hf
  simp at hv
  rcases hv with rfl | rfl
  · simp [AlignPos] at hf ⊢
    rcases hf with rfl | rfl <;> decide
  · cases hf

/-- Canonical counterexample dropping `h_nonempty` from
    `reprIntEnum_geometry_of_nonempty_align_pos`: with `variants = []` and `tag = cEnumTagX86_64`,
    `reprIntEnum` yields `size = 0 < 4 = tag.size`, violating `EnumSizeValid`. -/
theorem ce_reprIntEnum_geometry_drop_nonempty :
    let tag : FieldLayout := cEnumTagX86_64
    let variants : List (List FieldLayout) := []
    let E := reprIntEnum tag variants
    (∀ v ∈ variants, ∀ f ∈ v, AlignPos f) ∧
    ¬ (EnumSizeValid tag E ∧ EnumVariantsValid tag variants E ∧ EnumPerVariantTagged tag variants E) := by
  dsimp only
  refine ⟨(fun _ hv => nomatch hv), ?_⟩
  intro ⟨hsz, _, _⟩
  exact ex_enumSizeValid_neg hsz

/-- Canonical counterexample dropping `h_vars` (`AlignPos`) from
    `reprIntEnum_geometry_of_nonempty_align_pos`: with `tag = ⟨1, 1⟩` and `variants = [[⟨1, 0⟩]]`,
    variant 0's zero-aligned field is placed at offset `1`, violating `EnumVariantsValid`
    (`¬ (0 ∣ 1)`). -/
theorem ce_reprIntEnum_geometry_drop_vars_align_pos :
    let tag : FieldLayout := ⟨1, 1⟩
    let variants : List (List FieldLayout) := [[⟨1, 0⟩]]
    let E := reprIntEnum tag variants
    variants ≠ [] ∧
    ¬ (EnumSizeValid tag E ∧ EnumVariantsValid tag variants E ∧ EnumPerVariantTagged tag variants E) := by
  refine ⟨by decide, ?_⟩
  intro ⟨_, hv, _⟩
  have hE : reprIntEnum ⟨1, 1⟩ [[⟨1, 0⟩]] =
      { size := 2, align := 1, tagOffset := 0, variantFieldOffsets := [[1]] } := rfl
  rw [hE] at hv
  have h0 := (hv.2 0 (by decide) (by decide)).2.1 0 (by decide) (by decide)
  rcases h0.2.1 with ⟨q, hq⟩
  simp at hq

/-- Main Result 4c (alignment validity of `reprCEnum`): Whenever `tag` and all variant
    fields have power-of-two alignments, `(reprCEnum tag variants).align` is a power of two
    divisible by `tag.align` and every variant field alignment (`EnumAlignValid`). -/
theorem reprCEnum_align_valid_of_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_tag : AlignPow2 tag)
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    EnumAlignValid tag variants (reprCEnum tag variants) := by
  let variantStructs := variants.map (reprCStruct .none)
  let uFields : List FieldLayout := variantStructs.map fun s => ⟨s.size, s.align⟩
  let payload := reprCUnion uFields
  let E := reprCEnum tag variants
  have hpay_pow2 : IsPowerOfTwo payload.align := by
    apply foldl_max_pow2_gen (fun f => f.align) uFields 1 ex_isPowerOfTwo_pos_1
    intro uf huf
    rcases List.mem_map.mp huf with ⟨s, hs, rfl⟩
    rcases List.mem_map.mp hs with ⟨v, hv, rfl⟩
    exact (reprCStruct_align_pow2_divides .none v (h_vars v hv) trivial).1
  have houter_pow := reprCStruct_align_pow2_divides .none [tag, ⟨payload.size, payload.align⟩]
    (by
      intro g hg
      simp at hg
      rcases hg with rfl | rfl
      · exact h_tag
      · exact hpay_pow2)
    trivial
  have hE_align_eq : E.align = (reprCStruct .none [tag, ⟨payload.size, payload.align⟩]).align := rfl
  unfold EnumAlignValid
  rw [hE_align_eq]
  refine ⟨houter_pow.1, ?_, ?_⟩
  · simpa [effFieldAlign] using houter_pow.2 tag (by simp)
  · intro v hv f hf
    have hpay_dvd : payload.align ∣
        (reprCStruct .none [tag, ⟨payload.size, payload.align⟩]).align := by
      simpa [effFieldAlign] using houter_pow.2 ⟨payload.size, payload.align⟩ (by simp)
    let s := reprCStruct .none v
    have hs_pow := reprCStruct_align_pow2_divides .none v (h_vars v hv) trivial
    have huf_mem : (⟨s.size, s.align⟩ : FieldLayout) ∈ uFields :=
      List.mem_map_of_mem (List.mem_map_of_mem hv)
    have hs_le_pay : s.align ≤ payload.align := reprCUnion_align_ge_mem uFields huf_mem
    have hs_dvd_pay : s.align ∣ payload.align :=
      isPowerOfTwo_dvd_of_le hs_pow.1 hpay_pow2 hs_le_pay
    have hf_dvd_s : f.align ∣ s.align := by
      simpa [effFieldAlign] using hs_pow.2 f hf
    exact Nat.dvd_trans hf_dvd_s (Nat.dvd_trans hs_dvd_pay hpay_dvd)

theorem nv_reprCEnum_align_valid_of_pow2 :
    let tag := cEnumTagX86_64
    let variants : List (List FieldLayout) := [[⟨4, 4⟩], [⟨4, 4⟩, ⟨8, 8⟩], []]
    AlignPow2 tag ∧ ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f :=
  ⟨⟨2, rfl⟩, nv_reprCEnum_geometry_of_vars_pow2⟩

/-- Canonical counterexample dropping `h_tag` from `reprCEnum_align_valid_of_pow2`:
    variant fields are power-of-two aligned, yet `tag = ⟨3, 3⟩` produces `E.align = 3`,
    violating `IsPowerOfTwo E.align` and `2 ∣ E.align`. -/
theorem ce_reprCEnum_align_drop_tag_pow2 :
    let tag : FieldLayout := ⟨3, 3⟩
    let variants : List (List FieldLayout) := [[⟨2, 2⟩]]
    (∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) ∧
    ¬ EnumAlignValid tag variants (reprCEnum tag variants) := by
  refine ⟨?_, ?_⟩
  · intro v hv f hf
    simp at hv
    rcases hv with rfl
    simp at hf
    rcases hf with rfl
    exact ⟨1, rfl⟩
  · intro ⟨hpow, _, _⟩
    exact ex_isPowerOfTwo_neg_3 hpow

/-- Canonical counterexample dropping `h_vars` from `reprCEnum_align_valid_of_pow2`:
    `tag = ⟨2, 2⟩` is power-of-two aligned, yet `variants = [[⟨3, 3⟩]]` produces `E.align = 3`,
    violating `IsPowerOfTwo E.align` and `2 ∣ E.align`. -/
theorem ce_reprCEnum_align_drop_vars_pow2 :
    let tag : FieldLayout := ⟨2, 2⟩
    let variants : List (List FieldLayout) := [[⟨3, 3⟩]]
    AlignPow2 tag ∧
    ¬ EnumAlignValid tag variants (reprCEnum tag variants) :=
  ⟨⟨1, rfl⟩, fun ⟨hpow, _, _⟩ => ex_isPowerOfTwo_neg_3 hpow⟩

/-- Main Result 4d (alignment equality for non-empty enums): Whenever `variants ≠ []`,
    `reprIntEnum tag variants` and `reprCEnum tag variants` have the exact same overall
    alignment (without requiring power-of-two alignments). Combined with
    `reprCEnum_align_valid_of_pow2`, this immediately transfers `EnumAlignValid` to
    non-empty `reprIntEnum` layouts. -/
theorem reprIntEnum_align_eq_reprCEnum_align_of_nonempty
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_nonempty : variants ≠ []) :
    (reprIntEnum tag variants).align = (reprCEnum tag variants).align := by
  let variantStructsC := variants.map (reprCStruct .none)
  let uFieldsC : List FieldLayout := variantStructsC.map fun s => ⟨s.size, s.align⟩
  let payload := reprCUnion uFieldsC
  let outer := reprCStruct .none [tag, ⟨payload.size, payload.align⟩]
  let variantStructsI := variants.map fun v => reprCStruct .none (tag :: v)
  let uFieldsI : List FieldLayout := variantStructsI.map fun s => ⟨s.size, s.align⟩
  have houter_al := reprCStruct_alignIsMaxEffective .none [tag, ⟨payload.size, payload.align⟩]
  apply Nat.le_antisymm
  · -- A_I ≤ A_C
    apply reprCUnion_align_le uFieldsI outer.align houter_al.1
    intro uf huf
    rcases List.mem_map.mp huf with ⟨s, hs, rfl⟩
    rcases List.mem_map.mp hs with ⟨v, hv, rfl⟩
    have hs_al := reprCStruct_alignIsMaxEffective .none (tag :: v)
    apply hs_al.2.2.2 outer.align houter_al.1
    · intro g hg
      simp only [effFieldAlign]
      simp at hg
      rcases hg with hgt | hgv
      · subst g
        simpa [effFieldAlign] using houter_al.2.1 tag (by simp)
      · have hpay_le : payload.align ≤ outer.align := by
          simpa [effFieldAlign] using houter_al.2.1 ⟨payload.size, payload.align⟩ (by simp)
        let sv := reprCStruct .none v
        have hufC : (⟨sv.size, sv.align⟩ : FieldLayout) ∈ uFieldsC :=
          List.mem_map_of_mem (List.mem_map_of_mem hv)
        have hsv_le : sv.align ≤ payload.align := reprCUnion_align_ge_mem uFieldsC hufC
        have hg_le_sv : g.align ≤ sv.align := by
          have := (reprCStruct_alignIsMaxEffective .none v).2.1 g hgv
          simpa [effFieldAlign] using this
        omega
    · intro n hn; cases hn
  · -- A_C ≤ A_I
    let aI := (reprIntEnum tag variants).align
    have haI_1 : 1 ≤ aI := reprCUnion_align_ge_one uFieldsI
    apply houter_al.2.2.2 aI haI_1
    · intro g hg
      simp only [effFieldAlign]
      simp at hg
      rcases hg with hgt | hgp
      · subst g
        cases hvs : variants with
        | nil => exact absurd hvs h_nonempty
        | cons v0 vs =>
          let s0 := reprCStruct .none (tag :: v0)
          have hs0_mem : s0 ∈ variantStructsI := by
            simp [variantStructsI, hvs, s0]
          have huf0 : (⟨s0.size, s0.align⟩ : FieldLayout) ∈ uFieldsI :=
            List.mem_map_of_mem hs0_mem
          have hs0_le : s0.align ≤ aI := reprCUnion_align_ge_mem uFieldsI huf0
          have htag_le_s0 : tag.align ≤ s0.align := by
            have := (reprCStruct_alignIsMaxEffective .none (tag :: v0)).2.1 tag (by simp)
            simpa [effFieldAlign] using this
          omega
      · subst g
        apply reprCUnion_align_le uFieldsC aI haI_1
        intro uf huf
        rcases List.mem_map.mp huf with ⟨sv, hsv, rfl⟩
        rcases List.mem_map.mp hsv with ⟨v, hv, rfl⟩
        dsimp only
        let sI := reprCStruct .none (tag :: v)
        have hufI : (⟨sI.size, sI.align⟩ : FieldLayout) ∈ uFieldsI :=
          List.mem_map_of_mem (List.mem_map_of_mem hv)
        have hsI_le : sI.align ≤ aI := reprCUnion_align_ge_mem uFieldsI hufI
        have hsv_al := reprCStruct_alignIsMaxEffective .none v
        have hsv_le_sI : (reprCStruct .none v).align ≤ sI.align := by
          apply hsv_al.2.2.2 sI.align (reprCStruct_alignIsMaxEffective .none (tag :: v)).1
          · intro f hf
            have := (reprCStruct_alignIsMaxEffective .none (tag :: v)).2.1 f (by simp [hf])
            simpa [effFieldAlign] using this
          · intro n hn; cases hn
        exact Nat.le_trans hsv_le_sI hsI_le
    · intro n hn; cases hn

theorem nv_reprIntEnum_align_eq_reprCEnum_align_of_nonempty :
    let variants : List (List FieldLayout) := [[⟨1, 1⟩, ⟨2, 2⟩], []]
    variants ≠ [] := by
  decide

/-- Canonical counterexample dropping `h_nonempty` from
    `reprIntEnum_align_eq_reprCEnum_align_of_nonempty`: at `variants = []` and
    `tag = cEnumTagX86_64`, `reprIntEnum` has alignment `1` while `reprCEnum` has alignment `4`. -/
theorem ce_reprIntEnum_align_eq_drop_nonempty :
    (reprIntEnum cEnumTagX86_64 []).align = 1 ∧
    (reprCEnum cEnumTagX86_64 []).align = 4 ∧
    (reprIntEnum cEnumTagX86_64 []).align ≠ (reprCEnum cEnumTagX86_64 []).align := by
  decide

/-- Main Result 4e (size ordering): For any fixed tag layout `tag` and variant list
    `variants` with power-of-two alignments everywhere, the `#[repr(Int)]` layout is never
    larger than the `#[repr(C, Int)]` layout with the same tag (formalizing RFC 2195's
    informal space-usage claim). -/
theorem reprIntEnum_size_le_reprCEnum_size_of_pow2
    (tag : FieldLayout) (variants : List (List FieldLayout))
    (h_tag : AlignPow2 tag)
    (h_vars : ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) :
    (reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size := by
  cases hvs : variants with
  | nil =>
    have hzero : (reprIntEnum tag []).size = 0 := by
      simp [reprIntEnum, reprCUnion, alignUp_zero]
    rw [hzero]
    exact Nat.zero_le _
  | cons v0 vs =>
    rw [← hvs]
    have hne : variants ≠ [] := by rw [hvs]; simp
    let EC := reprCEnum tag variants
    let EI := reprIntEnum tag variants
    have hal_eq : EI.align = EC.align :=
      reprIntEnum_align_eq_reprCEnum_align_of_nonempty tag variants hne
    have hgeomC := reprCEnum_geometry_of_vars_pow2 tag variants h_vars
    have halC := reprCEnum_align_valid_of_pow2 tag variants h_tag h_vars
    have hEC_dvd_sz : EC.align ∣ EC.size := hgeomC.1.1
    let variantStructsC := variants.map (reprCStruct .none)
    let uFieldsC : List FieldLayout := variantStructsC.map fun s => ⟨s.size, s.align⟩
    let payload := reprCUnion uFieldsC
    let payloadOffset := alignUp tag.size payload.align
    have hpay_pow2 : IsPowerOfTwo payload.align := by
      apply foldl_max_pow2_gen (fun f => f.align) uFieldsC 1 ex_isPowerOfTwo_pos_1
      intro uf huf
      rcases List.mem_map.mp huf with ⟨s, hs, rfl⟩
      rcases List.mem_map.mp hs with ⟨v, hv, rfl⟩
      exact (reprCStruct_align_pow2_divides .none v (h_vars v hv) trivial).1
    have hpay_dvd_off : payload.align ∣ payloadOffset := dvd_alignUp (isPowerOfTwo_pos hpay_pow2)
    have hpay_sum_le_EC : payloadOffset + payload.size ≤ EC.size := hgeomC.2.2.2.1
    let variantStructsI := variants.map fun v => reprCStruct .none (tag :: v)
    let uFieldsI : List FieldLayout := variantStructsI.map fun s => ⟨s.size, s.align⟩
    have hmax_le_EC : uFieldsI.foldl (fun acc f => max acc f.size) 0 ≤ EC.size := by
      apply foldl_max_le_gen (fun f => f.size) uFieldsI 0 EC.size (Nat.zero_le EC.size)
      intro uf huf
      rcases List.mem_map.mp huf with ⟨sI, hsI, rfl⟩
      rcases List.mem_map.mp hsI with ⟨v, hv, rfl⟩
      dsimp only
      let sC := reprCStruct .none v
      have hsC_pow := reprCStruct_align_pow2_divides .none v (h_vars v hv) trivial
      have hufC_mem : (⟨sC.size, sC.align⟩ : FieldLayout) ∈ uFieldsC :=
        List.mem_map_of_mem (List.mem_map_of_mem hv)
      have hsC_al_le_pay : sC.align ≤ payload.align := reprCUnion_align_ge_mem uFieldsC hufC_mem
      have hsC_sz_le_pay : sC.size ≤ payload.size := reprCUnion_size_ge_mem uFieldsC hufC_mem
      have hsC_al_dvd_off : sC.align ∣ payloadOffset :=
        Nat.dvd_trans (isPowerOfTwo_dvd_of_le hsC_pow.1 hpay_pow2 hsC_al_le_pay) hpay_dvd_off
      have hf_dvd_off : ∀ f ∈ v, f.align ∣ payloadOffset := by
        intro f hf
        have hfs : f.align ∣ sC.align := by
          simpa [effFieldAlign] using hsC_pow.2 f hf
        exact Nat.dvd_trans hfs hsC_al_dvd_off
      have hsI_parts := reprCStruct_eq_parts .none (tag :: v)
      have hsC_parts := reprCStruct_eq_parts .none v
      have hsI_end_le : (placeFields .none 0 (tag :: v)).2 ≤ payloadOffset + payload.size := by
        rw [placeFields_cons]
        dsimp only [effFieldAlign]
        rw [alignUp_zero, Nat.zero_add]
        have hmono : (placeFields .none tag.size v).2 ≤ (placeFields .none payloadOffset v).2 :=
          placeFields_end_mono .none v (le_alignUp tag.size payload.align)
        have hshift := placeFields_shift_of_dvd 0 payloadOffset v hf_dvd_off
        rw [Nat.add_zero] at hshift
        have hshift_end : (placeFields .none payloadOffset v).2 =
            payloadOffset + (placeFields .none 0 v).2 := by
          rw [hshift]
        have hsC_end_le_sz : (placeFields .none 0 v).2 ≤ sC.size := by
          change (placeFields .none 0 v).2 ≤ (reprCStruct .none v).size
          rw [hsC_parts]
          exact le_alignUp _ _
        omega
      have hsI_pow := reprCStruct_align_pow2_divides .none (tag :: v)
        (by
          intro g hg
          simp at hg
          rcases hg with rfl | hgv
          · exact h_tag
          · exact h_vars v hv g hgv)
        trivial
      have hsI_al_le_EI : (reprCStruct .none (tag :: v)).align ≤ EI.align :=
        reprCUnion_align_ge_mem uFieldsI (List.mem_map_of_mem (List.mem_map_of_mem hv))
      have hsI_al_dvd_EC : structAlign .none (tag :: v) ∣ EC.align := by
        have hsI_al_eq : (reprCStruct .none (tag :: v)).align = structAlign .none (tag :: v) := by
          rw [hsI_parts]
        rw [← hsI_al_eq]
        exact isPowerOfTwo_dvd_of_le hsI_pow.1 halC.1 (by omega)
      rw [hsI_parts]
      dsimp only
      exact alignUp_le_of_dvd (Nat.le_trans hsI_end_le hpay_sum_le_EC)
        (Nat.dvd_trans hsI_al_dvd_EC hEC_dvd_sz)
    change alignUp (uFieldsI.foldl (fun acc f => max acc f.size) 0) EI.align ≤ EC.size
    rw [hal_eq]
    exact alignUp_le_of_dvd hmax_le_EC hEC_dvd_sz

theorem nv_reprIntEnum_size_le_reprCEnum_size_of_pow2 :
    let tag := u8Tag
    let variants : List (List FieldLayout) := [[⟨1, 1⟩, ⟨2, 2⟩], []]
    AlignPow2 tag ∧ ∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f := by
  refine ⟨⟨0, rfl⟩, ?_⟩
  intro v hv f hf
  simp at hv
  rcases hv with rfl | rfl
  · simp at hf
    rcases hf with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · cases hf

/-- Canonical counterexample dropping `h_tag` from `reprIntEnum_size_le_reprCEnum_size_of_pow2`:
    with non-power-of-two `tag = ⟨3, 3⟩` and power-of-two `variants = [[⟨4, 4⟩], [⟨4, 2⟩]]`,
    `reprIntEnum` gives size `12` whereas `reprCEnum` gives size `8` (`12 > 8`). -/
theorem ce_reprInt_le_reprC_drop_tag_pow2 :
    let tag : FieldLayout := ⟨3, 3⟩
    let variants : List (List FieldLayout) := [[⟨4, 4⟩], [⟨4, 2⟩]]
    (∀ v ∈ variants, ∀ f ∈ v, AlignPow2 f) ∧
    ¬ ((reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size) := by
  refine ⟨?_, by decide⟩
  intro v hv f hf
  simp at hv
  rcases hv with rfl | rfl
  · simp at hf
    rcases hf with rfl
    exact ⟨2, rfl⟩
  · simp at hf
    rcases hf with rfl
    exact ⟨1, rfl⟩

/-- Canonical counterexample dropping `h_vars` from `reprIntEnum_size_le_reprCEnum_size_of_pow2`:
    with power-of-two `tag = ⟨3, 1⟩` and `variants = [[⟨6, 2⟩], [⟨0, 3⟩]]`,
    `reprIntEnum` gives size `12` while `reprCEnum` gives size `9` (`12 > 9`). -/
theorem ce_reprInt_le_reprC_drop_vars_pow2 :
    let tag : FieldLayout := ⟨3, 1⟩
    let variants : List (List FieldLayout) := [[⟨6, 2⟩], [⟨0, 3⟩]]
    AlignPow2 tag ∧
    ¬ ((reprIntEnum tag variants).size ≤ (reprCEnum tag variants).size) :=
  ⟨⟨0, rfl⟩, by decide⟩

/-- Main Result 4f (fully proved): Concrete arithmetic divergences under the target-parameterized
    `reprCEnumForTarget` model showing that neither a pointer-sized tag heuristic (`usizeTag64`)
    nor a fixed 4-byte `c_int` heuristic (`cIntLayout32Bit`) matches bare `#[repr(C)]` across
    targets and discriminant ranges:
    1. On `targetX86_64Linux` (`cEnumMinBytes = 4`, discriminants `[0, 1]`),
       `[[⟨1, 1⟩], []]` has `size = 8, align = 4`, whereas `usizeTag64` gives `size = 16, align = 8`.
    2. On `targetThumbV7mNoneEabi` and `targetHexagonNoneElf` (`cEnumMinBytes = 1`,
       discriminants `[0, 1]`), `[[⟨1, 1⟩], []]` has `size = 2` (and `align = 1`; Hexagon and
       `cIntLayout32Bit` alignments are proved in `ce_reprCEnum_tag_sizing_divergence_aligns`),
       whereas `cIntLayout32Bit` gives `size = 8`.
    3. On `targetX86_64Linux` with out-of-`int`/`unsigned int`-range discriminants
       `[0x1_0000_0000, 0x1_0000_0001]` (non-conforming per `r[layout.repr.c.enum.discriminant]`;
       accepted by `rustc` only under the future-incompatibility lint
       `repr_c_enums_larger_than_int`), a field-less enum `[[], []]` has `size = 8, align = 8`,
       whereas `cIntLayout32Bit` gives `size = 4` (`align = 4` proved in
       `ce_reprCEnum_tag_sizing_divergence_aligns`). -/
theorem ce_reprCEnum_tag_sizing_divergence :
    let enumC_variants : List (List FieldLayout) := [[⟨1, 1⟩], []]
    let fieldless_variants : List (List FieldLayout) := [[], []]
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).size = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).align = 4 ∧
    (reprCEnum usizeTag64 enumC_variants).size = 16 ∧
    (reprCEnum usizeTag64 enumC_variants).align = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0 1 enumC_variants).size ≠
      (reprCEnum usizeTag64 enumC_variants).size ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).size = 2 ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).align = 1 ∧
    (reprCEnumForTarget targetHexagonNoneElf 0 1 enumC_variants).size = 2 ∧
    (reprCEnum cIntLayout32Bit enumC_variants).size = 8 ∧
    (reprCEnumForTarget targetThumbV7mNoneEabi 0 1 enumC_variants).size ≠
      (reprCEnum cIntLayout32Bit enumC_variants).size ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).size = 8 ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).align = 8 ∧
    (reprCEnum cIntLayout32Bit fieldless_variants).size = 4 ∧
    (reprCEnumForTarget targetX86_64Linux 0x100000000 0x100000001 fieldless_variants).size ≠
      (reprCEnum cIntLayout32Bit fieldless_variants).size := by
  decide

/-- Companion alignment statement for `ce_reprCEnum_tag_sizing_divergence`: establishes
    the three `align` equalities paired with the size divergences (`align = 1` on
    `targetHexagonNoneElf` for `enumC_variants`, and `align = 4` for `cIntLayout32Bit`
    on both `enumC_variants` and `fieldless_variants`). -/
theorem ce_reprCEnum_tag_sizing_divergence_aligns :
    let enumC_variants : List (List FieldLayout) := [[⟨1, 1⟩], []]
    let fieldless_variants : List (List FieldLayout) := [[], []]
    (reprCEnumForTarget targetHexagonNoneElf 0 1 enumC_variants).align = 1 ∧
    (reprCEnum cIntLayout32Bit enumC_variants).align = 4 ∧
    (reprCEnum cIntLayout32Bit fieldless_variants).align = 4 := by
  decide

/-- Main Result 4g (fully proved): Strict size and offset separation between `#[repr(u8)]`
    and `#[repr(C, u8)]` on `variants = [[⟨1, 1⟩, ⟨2, 2⟩], []]` (mirroring RFC 2195's
    `TwoCases` 4-byte vs. 6-byte example), together with separation by `EnumSharedPayload`
    and `EnumPerVariantTagged`. -/
theorem ce_reprIntEnum_lt_reprCEnum_u8 :
    let variants : List (List FieldLayout) := [[⟨1, 1⟩, ⟨2, 2⟩], []]
    (reprIntEnum u8Tag variants).size = 4 ∧
    (reprIntEnum u8Tag variants).variantFieldOffsets = [[1, 2], []] ∧
    (reprCEnum u8Tag variants).size = 6 ∧
    (reprCEnum u8Tag variants).variantFieldOffsets = [[2, 4], []] ∧
    (reprIntEnum u8Tag variants).size < (reprCEnum u8Tag variants).size ∧
    ¬ EnumSharedPayload u8Tag variants (reprIntEnum u8Tag variants) ∧
    ¬ EnumPerVariantTagged u8Tag variants (reprCEnum u8Tag variants) :=
  ⟨rfl, rfl, rfl, rfl, by decide, ex_enumSharedPayload_neg_reprInt, ex_enumPerVariantTagged_neg_reprC⟩

end Toy.Layout
