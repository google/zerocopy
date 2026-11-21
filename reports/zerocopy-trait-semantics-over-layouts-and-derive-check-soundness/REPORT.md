# zerocopy trait semantics over byte layouts and soundness of zerocopy-derive checks: a Lean 4 model

## Summary

This package is a Lean 4 model, checked by the Lean kernel and using no Mathlib, of four things at zerocopy v0.8.63 (`google/zerocopy`, commit `c55af491426ef53f35fb8c6e83f220fa07712e66`):

* the byte-level meaning of zerocopy's traits `FromZeros`, `FromBytes`, `IntoBytes`, `TryFromBytes` validity and `Unaligned`;
* the `repr(C)` and primitive-representation layout algorithms;
* the checks performed by `zerocopy-derive`;
* zerocopy's slice-DST metadata validation (`validate_cast_and_convert_metadata`).

Every result below is proved without `sorry`, and its axioms are among `propext`, `Classical.choice` and `Quot.sound`. The results are statements about this toy model. Model–system relation: none proved (the derive-check theorems relate the model's transcriptions of zerocopy-derive's checks to the model's own byte-level predicates; no theorem relates the model to zerocopy's or rustc's source). The kernel-checked theorems neither establish nor refute the corresponding claims about zerocopy v0.8.63, `zerocopy-derive` or rustc. Each connection to zerocopy or rustc is a separate claim, labelled `derived (modeling bridge)` under Findings, and is argued from cited source lines, not proved.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Results (one sentence each, with the key hypotheses; Lean names in parentheses). Every sentence is about the model. `SemFromZeros`, `SemFromBytes`, `SemIntoBytes` and `validInit` are the model's byte-level predicates; `implFromZeros`, `implFromBytes`, `implIntoBytes`, `implUnaligned`, `implImmutable`, `findZeroVariant`, `structPaddingOK`, `enumVariantCountOK`, `enumPaddingOK`, `unionPaddingOK` and `isSafe` are the model's transcriptions of zerocopy-derive's checks; `vccm` is the model of `validate_cast_and_convert_metadata`. All are defined under Findings. Their correspondence to zerocopy is a separate, unproved modeling bridge.

* **R1** (`Toy.Zc.semFromBytes_iff_validInit_total`, `Toy.Zc.semFromZeros_iff_validInit_zeros`, `Toy.Zc.semIntoBytes_iff_encodeL_init`): In the model, for every type description d: SemFromBytes d (every fully initialized byte vector decodes under the modeled representation Desc.rep d) holds iff the modeled validity check validInit accepts every byte list of length d.size; SemFromZeros d holds iff validInit accepts the all-zero byte list of length d.size; and SemIntoBytes d holds iff every byte below d.size of the modeled encoding of every well-typed value is initialized.
* **R2a** (`Toy.Zc.struct_fromBytes_iff_fields_fromBytes`, `Toy.Zc.struct_fromZeros_iff_fields_fromZeros`): In the model, for every modeled struct representation (repr(C) with or without packed(N) or align(N), or repr(transparent)) and every list of field descriptions, the struct description is SemFromBytes iff every field is SemFromBytes, and SemFromZeros iff every field is SemFromZeros, whether or not its modeled layout has padding.
* **R2c** (`Toy.Zc.struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited`): In the model, for a struct description (any modeled representation) whose field descriptions are all inhabited, the struct is SemIntoBytes iff every field is SemIntoBytes and the struct's modeled size equals the sum of its field sizes.
* **R2d** (`Toy.Zc.structPaddingOK_sound`): In the model, for a well-formed struct description (Desc.wf), if the modeled IntoBytes padding analysis structPaddingOK passes (repr(transparent); or repr(C, packed(1)); or repr(C) without align(N>1) and with at most one field; or the modeled size minus the sum of the field sizes is 0), then the struct's modeled size equals the sum of its field sizes.
* **R2e** (`Toy.Zc.derive_fromZeros_sound_of_wf`, `Toy.Zc.derive_fromBytes_sound_of_wf`, `Toy.Zc.derive_intoBytes_sound_of_wf`, `Toy.Zc.derive_unaligned_sound`): In the model, every well-formed description (Desc.wf) accepted by the modeled FromZeros, FromBytes or IntoBytes derive check (implFromZeros, implFromBytes, implIntoBytes, which include models of zerocopy's primitive impls; implIntoBytes in either setting of the union cfg) is SemFromZeros, SemFromBytes or SemIntoBytes respectively; and every description accepted by the modeled Unaligned derive check implUnaligned has modeled alignment 1 (no well-formedness needed).
* **R2f** (`Toy.Zc.derive_isSafe_eq_validInit_of_wf_of_length`): In the model, for every well-formed description and every byte list whose length is the description's modeled size, the modeled TryFromBytes::is_safe (isSafe: the model of the derived validator for structs, enums and unions together with zerocopy's primitive validators) returns exactly the model's validity check validInit.
* **R3a** (`Toy.Zc.fieldless_enum_fromBytes_iff_every_tag_is_discriminant`): In the model, a fieldless enum description with a primitive representation repr(t) is SemFromBytes iff every tag value n < 2^(8*width t) is the tag code (Desc.codes) of some variant's resolved discriminant.
* **R3b** (`Toy.Zc.enum_variant_count_check_sound`): In the model, if an enum description's resolved discriminants are pairwise distinct and representable in its tag type (discrsWF), then the modeled FromBytes variant-count check enumVariantCountOK (representation u8, i8, u16 or i16 and exactly 2^bits variants) implies that every tag value n < 2^(8*width) is the tag code of some resolved discriminant.
* **R3c** (`Toy.Zc.enum_fromBytes_of_count_check`): In the model, for an enum description (fieldless or data-carrying) whose resolved discriminants are distinct and representable (discrsWF), if the modeled variant-count check enumVariantCountOK passes and every field of every variant is SemFromBytes, then the enum is SemFromBytes; even when all of these hypotheses hold, the modeled derive check implFromBytes, which also runs findZeroVariant, can reject the enum (Toy.Zc.fromBytes_enum_rejected_by_findZeroVariant: the fieldless repr(u8) enum description nonLiteralZeroFullU8 satisfies them and is SemFromBytes, yet implFromBytes rejects it).
* **R3d** (`Toy.Zc.enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF`): In the model, for an enum description whose resolved discriminants are distinct and representable (discrsWF), the enum is SemFromZeros iff some variant has resolved discriminant 0 and every field of that variant is SemFromZeros.
* **R3e** (`Toy.Zc.findZeroVariant_sound`, `Toy.Zc.findZeroVariant_complete_of_no_unknown`, `Toy.Zc.enum_fromZeros_of_findZeroVariant`): In the model, findZeroVariant (the model of zerocopy-derive's syntactic find_zero_variant) is sound with respect to the model's discriminant resolver resolveDiscrs (if it returns Ok(i), resolveDiscrs assigns variant i the discriminant 0) and complete when it returns Err(false), that is, when it saw no non-literal discriminant (then no resolved discriminant is 0); and for distinct representable discriminants (discrsWF), Ok(i) together with SemFromZeros fields of variant i implies that the enum description is SemFromZeros.
* **R3f** (`Toy.Zc.enum_validInit_iff_first_matching_variant_valid`, `Toy.Zc.isSafe_enm_eq_validInit`): In the model, on byte lists of the enum description's modeled size, the modeled validity validInit of an enum holds exactly when the tag read from the bytes equals the tag code of some variant's discriminant and the fields of the first such variant are valid (validInit) at their modeled offsets; and if the modeled is_safe (isSafe) agrees with validInit on every field description at that field's size and the discriminants are distinct and representable (discrsWF), the modeled enum isSafe (including its model of the could_be_from_bytes shortcut) equals validInit.
* **R3g** (`Toy.Zc.enum_intoBytes_of_fields_of_padding_check`): In the model, for an enum description with repr(C) or a primitive representation, if every field of every variant is SemIntoBytes and the modeled enum_padding! check enumPaddingOK passes (for every variant, the modeled enum size minus (tag size + sum of the variant's field sizes) is 0), then the enum is SemIntoBytes.
* **R4a** (`Toy.Zc.union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited`): In the model, where a union value is a value written through one field, a union description whose field descriptions are inhabited is SemIntoBytes iff every field is SemIntoBytes and every field's modeled size equals the union's modeled size.
* **R4b** (`Toy.Zc.union_intoBytes_of_fields_of_padding_check`): In the model, where a union value is a value written through one field, if every field of a union description is SemIntoBytes and the modeled union_padding! check unionPaddingOK passes (for every field, the union's modeled size minus the field's size is 0), then the union is SemIntoBytes.
* **R4c** (`Toy.Zc.union_u8_u16_written_through_u8_leaves_uninit`): In the model, the description union { a: u8, b: u16 } (repr(C)) holding the value 7 written through a encodes as [init 7, uninit]; both field descriptions are SemIntoBytes, but the union is not.
* **R4d** (`Toy.Zc.permissive_union_validity_of_size_pos_not_intoBytes`): In the model's abstract-byte vocabulary, if a union's values were taken to be all abstract byte vectors of its size (the representation permissiveUnionRep, a validity that admits uninitialized bytes), then no union description of nonzero modeled size would satisfy IntoBytes, whatever its fields and whatever the modeled derive check says.
* **R5a** (`Toy.Zc.transmuteTotal_of_intoBytes_of_fromBytes`): In the model's abstract-byte vocabulary, for representations ra and rb over the same carrier of n abstract bytes, if no encoding of A contains uninit (ra.IntoBytes) and every fully initialized byte vector decodes as some B (rb.FromBytes), then decoding with rb after encoding with ra never fails (TransmuteTotal ra rb).
* **R5b** (`Toy.Zc.desc_transmute_total_of_size_ge`, `Toy.Zc.desc_transmute_total_of_size_eq`): In the model, for descriptions Src and Dst, if Src is SemIntoBytes, Dst is SemFromBytes and Dst's modeled size is at most Src's, then the modeled union-transmute transmuteVal, which decodes Dst from the first size(Dst) bytes of the encoding of a well-typed Src value, succeeds for every such value; the corollary desc_transmute_total_of_size_eq is the equal-size case.
* **R6a** (`Toy.Zc.vccm_sliceDst_returns_max_fitting_elems`): In the model, for a trailing-slice layout (TrailingSliceLayout) with positive size-rounding alignment, phase at most that alignment, and positive element size, when the alignment check passes, vccm (the model of validate_cast_and_convert_metadata) returns Ok((elems, split_at)) with elems the largest element count whose object size fits in bytes_len and split_at the prefix/suffix split for that size, and returns Err(Size) exactly when no element count fits.
* **R6d** (`Toy.Zc.vccm_sliceDst_start_aligned_of_align_dvd`): In the model, if the layout alignment divides the size base and the size-rounding alignment of a trailing-slice layout (so every object size is a multiple of it), then whenever vccm (the model of validate_cast_and_convert_metadata) returns Ok((elems, split_at)), the object starts at an aligned address: addr for a prefix cast, addr + split_at for a suffix cast.
* **R6b** (`Toy.Zc.normalizeDst_sizeForElems_eq_dstSize`): In the model, for a flat repr(C) slice DST description d (SliceDstSpec), the normalized trailing-slice layout normalizeDst d (base T - T mod A, size-rounding alignment A, phase T mod A, where T = dstTailOffset d is the trailing offset and A = dstAlign d the alignment) has object size dstSize d n, the closed-form repr(C) size, for every element count n.
* **R6c** (`Toy.Zc.vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned`): In the model, for a flat repr(C) slice DST description d, any layout alignment, and either cast type, when the alignment check passes, the element count returned by vccm (the modeled validation) on normalizeDst d equals maxSliceElems d bytes_len (the largest fitting count, or none).
* **R7a** (`Toy.Zc.immutable_not_byte_determined`): In the model, no property of descriptions that is ByteDetermined (depends only on the modeled layout, typing, encoder and decoder) coincides with implImmutable, the model of zerocopy's Immutable derive and impls: the descriptions UnsafeCell<u8> and u8 have the same modeled byte semantics but differ in implImmutable.
* **R7b** (`Toy.Zc.union_fromBytes_derive_not_necessary`, `Toy.Zc.union_fromZeros_derive_not_necessary`): In the model, the union description union { a: u8, b: bool } is SemFromBytes and union { a: u8, b: E } (E = Desc.noZero, a fieldless repr(u8) enum without a zero discriminant) is SemFromZeros, yet the modeled derive checks implFromBytes and implFromZeros reject them, because they require every field to have the trait.
* **R7c** (`Toy.Zc.unaligned_check_conjuncts_necessary`): In the model, each conjunct of the modeled Unaligned derive check implUnaligned is necessary: for each conjunct of its checks for repr(C) structs (no align(N>1); repr(packed) or all fields Unaligned), repr(transparent) structs (all fields Unaligned), enums (repr(u8)/repr(i8), shown for repr(u16) and repr(C); all fields Unaligned), and repr(C) unions (no align(N>1); repr(packed) or all fields Unaligned), there is a description (the witnesses in the Lean statement) that satisfies every other conjunct of its check, fails that one, is rejected, and has modeled alignment ≠ 1.

Each result has non-claims: things it does not show, together with the most tempting stronger readings. They are listed first under **Boundaries**. Read them before relying on a result. In particular, no result establishes that the real zerocopy derives are sound: soundness is shown for the model, and the model's fidelity to zerocopy is a modeling bridge.

## Applicability

**What is modeled, and how the subjects relate.**

* *zerocopy v0.8.63* (`google/zerocopy`, tag `v0.8.63`, commit `c55af491426ef53f35fb8c6e83f220fa07712e66`) is the system the definitions
  are meant to capture: the trait safety contracts, the `zerocopy-derive` checks, the primitive impls,
  `transmute!`, and `DstLayout::validate_cast_and_convert_metadata`. The Lean statements are about the
  model. The claim that the model matches zerocopy at this commit is the set of modeling bridges
  B1–B10 under Findings, argued from source lines quoted with `file:line` at this commit. Other zerocopy
  versions were not examined; Revalidation lists the source regions to compare.
* *Lean 4 v4.34.1* (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`) is the proof checker. The Lake project
  in `lean/` uses only core Lean: no Mathlib, no `Std`, and no `[[require]]`.
* *MiniRust* (`minirust/minirust`, commit `063d784186d3252bee242217f218223205c0b568`,
  `spec/lang/representation.md`) supplies the abstract-byte vocabulary (`uninit | init b`, encode and
  decode). Its permissive union validity is the contrast model of R4d.
* *The Rust Reference 1.81.0* ("Type layout") and *RFC 2195* (rust-lang/rfcs commit
  `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`) define the `repr(C)` and primitive-representation layouts that `reprCStruct`,
  `reprCUnion`, `unionLayout`, `reprCEnum` and `reprIntEnum` implement. *RFC 2835* (same rfcs
  commit) and rust-lang/rust commit `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`
  (`core::mem::TransmuteFrom` and the compiler's transmutability check) are context for R5b; they
  were read, not modeled.
* The papers listed as subjects are prior art. They are cited for comparison only, and no result
  depends on them.

**Model fidelity.** This is a toy model. Its known gaps:

No generics; no slice DSTs inside derived types; no `repr(Rust)`, no `repr(packed)` without `C`, no
`repr(C, Int)` (zerocopy rejects it), no `align(N)` on enums, no transparent unions; no field
invariants; primitives exactly `u8..u64`, `i8..i64`, `bool`; little-endian integers with alignment =
size; `repr(C)` enum tag = 4 bytes with discriminants restricted to `i32`; unbounded naturals (no
`isize::MAX`/`usize` overflow; `struct_padding!`'s `usize` subtraction is modeled by truncated
subtraction, which agrees whenever the size is at least the field-size sum, as on every
well-formed description); `is_safe` modeled for a `TryFromBytes`-top-level derive (the
FromBytes-top-level shortcut is not modeled); every type assumed inhabited by its derives except
where noted; union values written through one field.

The modeled primitives are exactly `u8, i8, u16, i16, u32, i32, u64, i64` and `bool`. There is no
`u128`/`i128`, `usize`/`isize`, floats, `char`, `NonZero*`, tuples, `PhantomData`, `ManuallyDrop`,
references or pointers. The target is modeled on `x86_64-unknown-linux-gnu`: integers are
little-endian, integer alignment equals integer size, and a `repr(C)` enum has a 4-byte tag holding an
`i32`-range discriminant. Sizes are unbounded natural numbers, so nothing here covers `isize::MAX`
or `usize` overflow. Slice DSTs are modeled only by the separate `TrailingSliceLayout`/`vccm`
vocabulary; `#[derive(KnownLayout)]` is not modeled, and `DstLayout.align` is a free parameter, as in
zerocopy. `is_safe` is modeled for a derive whose top-level trait is `TryFromBytes`. Union values are
values written through one field (bridge B7).

**Toolchain.** `leanprover/lean4:v4.34.1`, no Mathlib. The library target is `ToyZc` (modules
`ToyZc.Basic`, `Layout`, `Desc`, `Derive`, `Bridge`, `Lemmas`, `Union`, `ProofSupport`, `Struct`,
`Enum`, `Transmute`, `KnownLayout`, `NonClaims`, `Closure`), all in namespace `Toy.Zc`.

## Findings

Each result below has two basis lines. `Basis: execution (Lean kernel check)` means the displayed Lean statement was checked by the Lean kernel under the pinned toolchain, with only the standard axioms. The separate `Basis: derived (modeling bridge)` line says what the result means for zerocopy and names the bridges (B1–B10, below) that this reading relies on. The bridge line is reasoning, not proof.

### Definitions

Summary of the model (pseudo-Lean; comments describe behavior):

#### Foundations (`ToyZc/Basic.lean`, `ToyZc/Layout.lean`)

```lean
inductive AByte (D : Type) | uninit | init (d : D)
abbrev Bytes (D : Type) (n : Nat) := Vector (AByte D) n
structure Rep (α V : Type) where encode : V → α; decode : α → Option V
def Rep.IntoBytes (r : Rep (Bytes D n) V) : Prop := ∀ v, (r.encode v).IsInit
def Rep.FromBytes (r : Rep (Bytes D n) V) : Prop := ∀ x, x.IsInit → ∃ v, r.decode x = some v
def Rep.tryFrom (r : Rep (Bytes D n) V) (ds : Vector D n) : Option V := r.decode (Bytes.ofData ds)
def transmute (ra : Rep α A) (rb : Rep α B) (a : A) : Option B := rb.decode (ra.encode a)
def TransmuteTotal (ra : Rep α A) (rb : Rep α B) : Prop := ∀ a, ∃ b, transmute ra rb a = some b

def alignUp (n a : Nat) := n + paddingNeeded n a          -- least multiple of a ≥ n (a > 0); n at a = 0
def roundDown (x a : Nat) := if a = 0 then 0 else (x / a) * a
inductive ReprModifier | none | packed (n : Nat) | aligned (n : Nat)
def effFieldAlign : ReprModifier → Nat → Nat               -- packed p clamps to min a p
def reprCStruct (m : ReprModifier) (fields : List FieldLayout) : StructLayout
  -- offsets: alignUp(cursor, effFieldAlign m f.align) in order; size: alignUp(end, structAlign m fields)
def reprCUnion, unionLayout m, reprCEnum, reprIntEnum      -- union of fields; {tag, union of variant structs}; union of {tag, fields}
def dstTailOffset, dstAlign, dstSize d n := alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)
def maxSliceElems d len : Option Nat                       -- none if elem size 0 or nothing fits
```

The byte vocabulary is a subset of a larger one (the definedness order and the representation laws
are omitted, no statement uses them). `unionLayout m` adds `packed`/`align` to `reprCUnion`
(`unionLayout_none`).

#### Type descriptions (`ToyZc/Desc.lean`)

```lean
inductive IntTy | u8 | i8 | u16 | i16 | u32 | i32 | u64 | i64      -- width 1,1,2,2,4,4,8,8; align = width
inductive DiscrSyn | implicit | lit (n : Nat) | negLit (n : Nat) | other (value : Int)
inductive StructRepr | c (m : ReprModifier) | transparent
inductive EnumRepr | c | prim (t : IntTy)                            -- repr(C) tag: 4 bytes, i32-range discriminants
inductive UnionRepr | c (m : ReprModifier)
inductive Desc
  | int (t : IntTy) | bool | array (elem : Desc) (n : Nat)
  | strct (r : StructRepr) (fields : List Desc)
  | enm (r : EnumRepr) (variants : List (DiscrSyn × List Desc))
  | union (r : UnionRepr) (fields : List Desc)
  | cell (inner : Desc)                                              -- UnsafeCell<inner>
```

* `Desc.layout`: `int t ↦ (w, w)`, `bool ↦ (1, 1)`, `array e n ↦ (n·size e, align e)`, structs by
  `reprCStruct m` (transparent: `reprCStruct none`), enums by `reprCEnum` / `reprIntEnum` with the
  tag layout, unions by `unionLayout`, `cell t ↦ layout t`.
* `resolveDiscrs`: the compiler's discriminant values (implicit = previous + 1, first = 0).
  `discrCode t d := (d mod 2^(8·width t))` (two's complement). Tags are little-endian.
* `discrsWF r ds`: resolved discriminants pairwise distinct (`nodupInt`) **and** each within the tag
  type's range (`i32` for `repr(C)`). Counterexamples are given for dropping each half separately.
* `Desc.wf` (well-formedness): power-of-two modifiers (on the type and, recursively, on its fields);
  at most one non-1-ZST field in a transparent struct; at least one variant per enum and one field
  per union; `discrsWF`. Other compiler rules (e.g. E0588) are not enforced, so `wf`
  over-approximates accepted types.

#### Values and semantics

```lean
inductive Val | int (bytes : List Byte) | bool (b : Bool) | array (elems : List Val)
             | strct (fields : List Val) | enm (variant : Nat) (fields : List Val) | union (field : Nat) (v : Val)
def Desc.hasType : Desc → Val → Bool        -- typing judgment; TVal d := {v // d.hasType v}; Desc.Inhabited d := ∃ v, d.hasType v
def Desc.encodeL : Desc → Val → List (AByte Byte)
  -- ints: the bytes; bool: [0|1]; arrays: concatenation; structs: each field's encoding at its offset in an
  -- all-uninit buffer of the struct's size; enums: tag bytes at offset 0, then the variant's fields at their
  -- offsets; unions (value `union j v`): field j's encoding at offset 0, rest uninit. Always length d.size.
def Desc.decodeL : Desc → List (AByte Byte) → Option Val
  -- length must be d.size; ints: all bytes initialized; bool: [init 0] / [init 1]; structs: every field
  -- decodes from its own range (padding never read); enums: tag initialized, the first variant whose
  -- code equals the tag, then its fields; unions: the first field that decodes the prefix of its size.
def Desc.rep (d : Desc) : Rep (Bytes Byte d.size) (TVal d)   -- encode via encodeL, decode via decodeL (typed results)
def SemFromZeros d  := (d.rep.tryFrom (Vector.replicate d.size 0)).isSome = true
def SemFromBytes d  := d.rep.FromBytes
def SemIntoBytes d  := d.rep.IntoBytes
def validInit d bs  := match d.decodeL (bs.map init) with | some v => d.hasType v | none => false
def SemUnaligned d  := d.align = 1
```

On unions `Desc.rep` is not canonical (fully proved): `union_decode_encode_forgets_bytes` (decode
then encode forgets a byte; several successive field writes are not distinct values) and
`union_decode_not_monotone` (initializing an `uninit` byte changes the decoded field).

#### Modeled derive checks (`ToyZc/Derive.lean`)

Source paths: here, in the source-fidelity table and in the modeling bridges below, `D/`
abbreviates `zerocopy/zerocopy-derive/src/` and `Z/` abbreviates `zerocopy/src/` (paths in the
repository `google/zerocopy` at commit `c55af491426ef53f35fb8c6e83f220fa07712e66`).

Every nominal type in a description is assumed to request the derive; field bounds emitted by the
derives are discharged recursively.

| Check | Model | Source |
|---|---|---|
| `findZeroVariant` | transcription of the scan with `next_negative_discriminant` and `has_unknown_discriminants` | `D/derive/from_bytes.rs:19-90` |
| `implFromZeros` | struct/union: all fields; enum: `find_zero_variant = Ok(i)` and variant `i`'s fields; ints, bool, arrays, `UnsafeCell` by primitive impls | `D/derive/from_bytes.rs:91-180`; `Z/impls.rs:68-76, 101, 839, 905` |
| `implFromBytes` | `implFromZeros` ∧ struct/union: all fields; enum: `repr ∈ {u8,i8,u16,i16}` ∧ `variants.len() == 2^bits` ∧ all fields; bool: no | `D/derive/from_bytes.rs:106-121, 181-204`; `D/util.rs:982-1001` |
| `structPaddingOK` | transparent ∨ `is_packed_1` ∨ (`!is_align_gt_1` ∧ ≤ 1 field) ∨ `size_of::<Self>() - Σ size_of::<field>() == 0` | `D/derive/into_bytes.rs:99-144`; `Z/util/macro_util.rs:333-340` |
| `enumPaddingOK` | ∀ variant, `size_of::<Self>() - (size_of::<Tag>() + Σ size_of::<field>()) == 0` | `D/derive/into_bytes.rs:196-209`; `Z/util/macro_util.rs:420-442` |
| `unionPaddingOK` | ∀ field, `size_of::<Self>() - size_of::<field>() == 0` | `D/derive/into_bytes.rs:255-257`; `Z/util/macro_util.rs:386-400` |
| `implIntoBytes cfg` | struct: all fields ∧ `structPaddingOK`; enum: all fields ∧ `enumPaddingOK`; union: `cfg.unionIntoBytes` ∧ all fields ∧ `unionPaddingOK` | `D/derive/into_bytes.rs:89-259` (cfg gate 220-233) |
| `implUnaligned` | `repr(C)` struct/union: `!is_align_gt_1` ∧ (`is_packed_1` ∨ all fields); transparent struct: all fields; enum: (`repr(u8)` or `repr(i8)`) ∧ all fields; `u8`, `i8`, `bool` | `D/derive/unaligned.rs:19-80` |
| `implImmutable` | all fields; `UnsafeCell` never | `D/derive/mod.rs:19-31`; `Z/lib.rs:1640-1646` |
| `isSafe` | struct: all fields; enum: `could_be_from_bytes` shortcut, else tag match (first match) and the variant's fields; union: some field; bool: `byte < 2`; ints: `true` | `D/derive/try_from_bytes.rs:33-71, 121-346`; `Z/impls.rs:112-117, 853-868, 894-904` |

#### Slice-DST metadata (`ToyZc/KnownLayout.lean`)

`TrailingSliceLayout ⟨offset, elemSize, sizeBase, sizeAlign, sizePhase⟩` with
`sizeForElems n = sizeBase + alignUp (sizePhase + n·elemSize) sizeAlign` (`Z/layout.rs:153-207`);
`maxTrailingBytes` (`Z/layout.rs:252-341`); `vccm`, a transcription of
`validate_cast_and_convert_metadata` (`Z/layout.rs:1650-1797`) with bit masks replaced by
`roundDown` and the disjoint-bit OR by `+`; `startOffset ct split_at` (`0` for a prefix cast,
`split_at` for a suffix cast); `normalizeDst d` with base `T - T mod A`, phase `T mod A`. The layout
alignment `DstLayout.align` is a free parameter (as in zerocopy); `TrailingSliceLayout.offset` is not
read by the validation.

Exact Lean text of the semantic predicates and of the small definitions that the statements mention:

```lean
-- ToyZc/Basic.lean
def IntoBytes {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ v : V, (r.encode v).IsInit

-- ToyZc/Basic.lean
def FromBytes {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) : Prop :=
  ∀ x : Bytes D n, x.IsInit → ∃ v, r.decode x = some v

-- ToyZc/Basic.lean
def tryFrom {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) (ds : Vector D n) : Option V :=
  r.decode (Bytes.ofData ds)

-- ToyZc/Basic.lean
def transmute {α A B : Type} (ra : Rep α A) (rb : Rep α B) (a : A) : Option B :=
  rb.decode (ra.encode a)

-- ToyZc/Basic.lean
def TransmuteTotal {α A B : Type} (ra : Rep α A) (rb : Rep α B) : Prop :=
  ∀ a : A, ∃ b : B, transmute ra rb a = some b

-- ToyZc/Desc.lean
def Desc.rep (d : Desc) : Rep (Bytes Byte d.size) (TVal d) where
  encode v := toBytesN d.size (d.encodeL v.val)
  decode x :=
    match d.decodeL x.toList with
    | some v => if h : d.hasType v = true then some ⟨v, h⟩ else none
    | none => none

-- ToyZc/Desc.lean
def SemFromZeros (d : Desc) : Prop :=
  (d.rep.tryFrom (Vector.replicate d.size 0)).isSome = true

-- ToyZc/Desc.lean
def SemFromBytes (d : Desc) : Prop := d.rep.FromBytes

-- ToyZc/Desc.lean
def SemIntoBytes (d : Desc) : Prop := d.rep.IntoBytes

-- ToyZc/Desc.lean
def validInit (d : Desc) (bs : List Byte) : Bool :=
  match d.decodeL (bs.map .init) with
  | some v => d.hasType v
  | none => false

-- ToyZc/Desc.lean
def SemUnaligned (d : Desc) : Prop := d.align = 1

-- ToyZc/Desc.lean
def Desc.Inhabited (d : Desc) : Prop := ∃ v, d.hasType v = true

-- ToyZc/Transmute.lean
def transmuteVal (s d : Desc) (v : Val) : Option Val :=
  match d.decodeL (fit d.size (s.encodeL v)) with
  | some w => if d.hasType w then some w else none
  | none => none

-- ToyZc/KnownLayout.lean
def TrailingSliceLayout.sizeForElems (t : TrailingSliceLayout) (n : Nat) : Nat :=
  t.sizeBase + alignUp (t.sizePhase + n * t.elemSize) t.sizeAlign

-- ToyZc/KnownLayout.lean
def TrailingSliceLayout.maxTrailingBytes (t : TrailingSliceLayout) (avail : Nat) : Option Nat :=
  let roundedPhase := if t.sizePhase = 0 then 0 else t.sizeAlign
  let minimumSize := t.sizeBase + roundedPhase
  if avail < minimumSize then none
  else
    let extra := avail - minimumSize
    let aligned := roundDown extra t.sizeAlign
    let initialPadding := roundedPhase - t.sizePhase
    some (aligned + initialPadding)

-- ToyZc/KnownLayout.lean
def vccm (l : DstLayout) (addr bytesLen : Nat) (ct : CastType) : VccmResult :=
  if l.zstElem then .panic
  else if (addr + castOffset ct bytesLen) % l.align != 0 then .alignmentErr
  else
    match l.sizeInfo with
    | .sized size => if size > bytesLen then .sizeErr else .ok 0 (splitFor ct bytesLen size)
    | .sliceDst t =>
      match t.maxTrailingBytes bytesLen with
      | none => .sizeErr
      | some maxSlice =>
        let elems := maxSlice / t.elemSize
        let unused := maxSlice % t.elemSize
        let unusedAligned := roundDown unused t.sizeAlign
        let maxRounded := roundDown (bytesLen - t.sizeBase) t.sizeAlign
        let selfBytes := t.sizeBase + (maxRounded - unusedAligned)
        .ok elems (splitFor ct bytesLen selfBytes)

-- ToyZc/KnownLayout.lean
def TrailingSliceLayout.IsMaxFit (t : TrailingSliceLayout) (bytesLen n : Nat) : Prop :=
  t.sizeForElems n ≤ bytesLen ∧ ∀ k, t.sizeForElems k ≤ bytesLen → k ≤ n

-- ToyZc/KnownLayout.lean
def normalizeDst (d : SliceDstSpec) : TrailingSliceLayout where
  offset := dstTailOffset d
  elemSize := d.elem.size
  sizeBase := dstTailOffset d - dstTailOffset d % dstAlign d
  sizeAlign := dstAlign d
  sizePhase := dstTailOffset d % dstAlign d

-- ToyZc/Derive.lean
def structPaddingOK (r : StructRepr) (fs : List Desc) : Bool :=
  match r with
  | .transparent => true
  | .c m =>
    m.isPacked1 || (!m.isAlignGt1 && decide (fs.length ≤ 1)) ||
      ((Desc.structLayout r fs).size - (fs.map Desc.size).sum == 0)

-- ToyZc/Derive.lean
def enumPaddingOK (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  vs.all fun v => (Desc.enumLayout r vs).size - (r.tagTy.width + (v.2.map Desc.size).sum) == 0

-- ToyZc/Derive.lean
def unionPaddingOK (r : UnionRepr) (fs : List Desc) : Bool :=
  fs.all fun f => (Desc.unionLayout r fs).size - f.size == 0

-- ToyZc/Derive.lean
def enumVariantCountOK (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  match enumFromBytesBits r with
  | some b => vs.length == 2 ^ b
  | none => false

-- ToyZc/Derive.lean
def couldBeFromBytes (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  match enumFromBytesBits r with
  | some b => vs.all (fun v => v.2.isEmpty) && vs.length == 2 ^ b
  | none => false

-- ToyZc/Desc.lean
def discrsWF (r : EnumRepr) (ds : List DiscrSyn) : Bool :=
  let vals := resolveDiscrs ds
  nodupInt vals && vals.all fun v => decide (r.tagTy.minVal ≤ v ∧ v ≤ r.tagTy.maxVal)

-- ToyZc/Enum.lean
def enumTag (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) (bs : List Byte) : Nat :=
  leNat (slice bs (Desc.enumLayout r vs).tagOffset r.tagTy.width)

-- ToyZc/Enum.lean
def validFields : List Desc → List Nat → List Byte → Bool
  | [], _, _ => true
  | f :: fs, o :: os, bs => validInit f (slice bs o f.size) && validFields fs os bs
  | _ :: _, [], _ => false

-- ToyZc/Enum.lean
def validVariant : List (DiscrSyn × List Desc) → Nat → List (List Nat) → List Byte → Bool
  | (_, fs) :: _, 0, os :: _, bs => validFields fs os bs
  | _ :: vs, i + 1, _ :: oss, bs => validVariant vs i oss bs
  | _, _, _, _ => false

-- ToyZc/Enum.lean
def variantFields (vs : List (DiscrSyn × List Desc)) (i : Nat) : Option (List Desc) :=
  vs[i]?.map Prod.snd

-- ToyZc/Enum.lean
def Desc.Fieldless (vs : List (DiscrSyn × List Desc)) : Prop := ∀ v ∈ vs, v.2 = []

-- ToyZc/Struct.lean
def Desc.fieldSizeSum (fs : List Desc) : Nat := (fs.map Desc.size).sum

-- ToyZc/Union.lean
def permissiveUnionRep (n : Nat) : Rep (Bytes Byte n) (Bytes Byte n) := ⟨id, some⟩

-- ToyZc/KnownLayout.lean
def startOffset : CastType → Nat → Nat
  | .prefixCast, _ => 0
  | .suffixCast, splitAt => splitAt
```

Exact Lean text of the further package-local types, helper functions and witness constants that
appear in the displayed statements. In words:

* `Byte` is the payload of an initialized abstract byte (`UInt8`); `isInit` (full name
  `AByte.isInit`) tests whether an abstract byte is `init _`.
* `FieldLayout`, `StructLayout`, `UnionLayout` and `EnumLayout` are the layout records computed by
  the layout functions above; `Desc.structLayout`, `Desc.enumLayout` and `Desc.unionLayout` apply
  them to the field descriptions of a struct, enum or union, and `EnumRepr.tagTy` is the tag type
  of an enum representation (`i32` for `repr(C)`).
* `Desc.u8`, `Desc.u16`, `Desc.u32` abbreviate the integer descriptions (the statements also write
  them as `.u8`, `.u16`, `.u32`).
* `Desc.discrs vs` lists the resolved discriminants of the variants `vs`, and `Desc.codes r vs`
  their tag codes (`discrCode`: the discriminant modulo `2^(8·width)` of the tag type `r.tagTy`).
* `DeriveConfig` records whether `--cfg zerocopy_derive_union_into_bytes` is set; `cfgDefault` is
  the default build, with it unset.
* `ReprModifier.isPacked1` and `ReprModifier.isAlignGt1` model zerocopy-derive's `is_packed_1` and
  `is_align_gt_1`; `allUnaligned fs` (resp. `variantsUnaligned vs`) says that every field (of every
  variant) passes the modeled `Unaligned` check `implUnaligned`.
* `TrailingSliceLayout`, `SizeInfo`, `DstLayout` and `CastType` mirror zerocopy's types of the
  same names (`Z/layout.rs`); `VccmResult` is the outcome of the validation (`Ok((elems, split_at))`,
  `Err(Alignment)`, `Err(Size)`, or a panic for a zero-sized element); `castOffset` is the offset whose alignment the validation checks (`0`
  for a prefix cast, `bytes_len` for a suffix cast); `splitFor` is the returned `split_at` for an
  object of a given size; `DstLayout.zstElem` flags a zero-sized trailing element (the validation
  panics); `VccmResult.elems?` is the element count of a successful result and `none` otherwise.
* `SliceDstSpec` describes a flat `#[repr(C)]` slice DST by its modifier, the layouts of its sized
  head fields, and the layout of its trailing element; `dstTailOffset`, `dstAlign`, `dstSize` and
  `maxSliceElems` are its trailing-slice offset, its alignment, its size for `n` elements and its
  largest fitting element count (`none` for a zero-sized element or when nothing fits).
* `SameBytes d₁ d₂` says that two descriptions have the same modeled layout, typing judgment,
  encoder and decoder; `ByteDetermined P` says that `P` never distinguishes two such descriptions.
* Witness constants: `Desc.noZero` is `#[repr(u8)] enum E { A = 1 }` (no zero discriminant);
  `Desc.alignedByte` is `#[repr(C, align(2))] struct { a: u8 }` (size 2, one trailing padding
  byte); `nonLiteralZeroFullU8` is the list of 256 fieldless `repr(u8)` variants whose first
  discriminant is a non-literal expression that the compiler evaluates to `0` (`.other 0`) and whose
  remaining 255 discriminants are implicit (`1, …, 255`); `dupZeroNonLiteral` is the two variants
  `= ZERO { x: E }` (a non-literal expression evaluating to `0`, carrying one field of type
  `E = Desc.noZero`) and `= 0` (a literal), whose resolved discriminants coincide, so the enum
  violates the compiler's duplicate-discriminant rule E0081 and `discrsWF` fails.

```lean
-- ToyZc/Basic.lean
abbrev Byte := UInt8

-- ToyZc/Basic.lean
def isInit : AByte D → Bool
  | uninit => false
  | init _ => true

-- ToyZc/Layout.lean
structure FieldLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

-- ToyZc/Layout.lean
structure StructLayout where
  offsets : List Nat
  endOffset : Nat
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

-- ToyZc/Layout.lean
structure UnionLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq, BEq

-- ToyZc/Layout.lean
structure EnumLayout where
  size : Nat
  align : Nat
  tagOffset : Nat
  variantFieldOffsets : List (List Nat)
  deriving Repr, DecidableEq, BEq

-- ToyZc/Layout.lean
structure SliceDstSpec where
  modifier : ReprModifier
  headFields : List FieldLayout
  elem : FieldLayout
  deriving Repr, DecidableEq, BEq

-- ToyZc/Layout.lean
def dstTailOffset (d : SliceDstSpec) : Nat :=
  let (_, headEnd) := placeFields d.modifier 0 d.headFields
  alignUp headEnd (effFieldAlign d.modifier d.elem.align)

-- ToyZc/Layout.lean
def dstAlign (d : SliceDstSpec) : Nat :=
  structAlign d.modifier (d.headFields ++ [d.elem])

-- ToyZc/Layout.lean
def dstSize (d : SliceDstSpec) (n : Nat) : Nat :=
  alignUp (dstTailOffset d + n * d.elem.size) (dstAlign d)

-- ToyZc/Layout.lean
def maxSliceElems (d : SliceDstSpec) (bufferLen : Nat) : Option Nat :=
  if d.elem.size = 0 then none
  else
    let cap := roundDown bufferLen (dstAlign d)
    if cap < dstTailOffset d then none
    else some ((cap - dstTailOffset d) / d.elem.size)

-- ToyZc/Desc.lean
def EnumRepr.tagTy : EnumRepr → IntTy
  | .c => .i32
  | .prim t => t

-- ToyZc/Desc.lean
def Desc.structLayout (r : StructRepr) (fs : List Desc) : StructLayout := r.layout (Desc.layouts fs)

-- ToyZc/Desc.lean
def Desc.enumLayout (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : EnumLayout :=
  r.layout (Desc.variantLayouts vs)

-- ToyZc/Desc.lean
def Desc.unionLayout (r : UnionRepr) (fs : List Desc) : UnionLayout :=
  Toy.Zc.unionLayout r.modifier (Desc.layouts fs)

-- ToyZc/Desc.lean
abbrev Desc.u8 : Desc := .int .u8
abbrev Desc.u16 : Desc := .int .u16
abbrev Desc.u32 : Desc := .int .u32

-- ToyZc/Desc.lean
def Desc.discrs (vs : List (DiscrSyn × List Desc)) : List Int := resolveDiscrs (vs.map Prod.fst)

-- ToyZc/Desc.lean
def Desc.codes (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : List Nat :=
  (Desc.discrs vs).map (discrCode r.tagTy)

-- ToyZc/Derive.lean
structure DeriveConfig where
  /-- Whether `--cfg zerocopy_derive_union_into_bytes` is set (`D/derive/into_bytes.rs:220-233`). -/
  unionIntoBytes : Bool

-- ToyZc/Derive.lean
def ReprModifier.isPacked1 : ReprModifier → Bool
  | .packed 1 => true
  | _ => false

-- ToyZc/Derive.lean
def ReprModifier.isAlignGt1 : ReprModifier → Bool
  | .aligned n => decide (n > 1)
  | _ => false

-- ToyZc/Derive.lean
def allUnaligned : List Desc → Bool
  | [] => true
  | f :: fs => implUnaligned f && allUnaligned fs

-- ToyZc/Derive.lean
def variantsUnaligned : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => allUnaligned fs && variantsUnaligned vs

-- ToyZc/Derive.lean
abbrev cfgDefault : DeriveConfig := ⟨false⟩

-- ToyZc/KnownLayout.lean
structure TrailingSliceLayout where
  offset : Nat
  elemSize : Nat
  sizeBase : Nat
  sizeAlign : Nat
  sizePhase : Nat
  deriving Repr, DecidableEq

-- ToyZc/KnownLayout.lean
inductive SizeInfo where
  | sized (size : Nat)
  | sliceDst (t : TrailingSliceLayout)
  deriving Repr, DecidableEq

-- ToyZc/KnownLayout.lean
structure DstLayout where
  align : Nat
  sizeInfo : SizeInfo
  deriving Repr, DecidableEq

-- ToyZc/KnownLayout.lean
inductive CastType where
  | prefixCast
  | suffixCast
  deriving Repr, DecidableEq

-- ToyZc/KnownLayout.lean
inductive VccmResult where
  | ok (elems splitAt : Nat)
  | alignmentErr
  | sizeErr
  | panic
  deriving Repr, DecidableEq

-- ToyZc/KnownLayout.lean
def castOffset : CastType → Nat → Nat
  | .prefixCast, _ => 0
  | .suffixCast, bytesLen => bytesLen

-- ToyZc/KnownLayout.lean
def splitFor : CastType → Nat → Nat → Nat
  | .prefixCast, _, size => size
  | .suffixCast, bytesLen, size => bytesLen - size

-- ToyZc/KnownLayout.lean
def DstLayout.zstElem (l : DstLayout) : Bool :=
  match l.sizeInfo with
  | .sliceDst t => t.elemSize == 0
  | .sized _ => false

-- ToyZc/KnownLayout.lean
def VccmResult.elems? : VccmResult → Option Nat
  | .ok e _ => some e
  | _ => none

-- ToyZc/NonClaims.lean
def SameBytes (d₁ d₂ : Desc) : Prop :=
  d₁.layout = d₂.layout ∧ (∀ v, d₁.hasType v = d₂.hasType v) ∧
    (∀ v, d₁.encodeL v = d₂.encodeL v) ∧ (∀ x, d₁.decodeL x = d₂.decodeL x)

-- ToyZc/NonClaims.lean
def ByteDetermined (P : Desc → Prop) : Prop := ∀ d₁ d₂, SameBytes d₁ d₂ → (P d₁ ↔ P d₂)

-- ToyZc/Lemmas.lean
abbrev Desc.noZero : Desc := .enm (.prim .u8) [(.lit 1, [])]

-- ToyZc/Struct.lean
abbrev Desc.alignedByte : Desc := .strct (.c (.aligned 2)) [.u8]

-- ToyZc/Enum.lean
abbrev dupZeroNonLiteral : List (DiscrSyn × List Desc) := [(.other 0, [Desc.noZero]), (.lit 0, [])]

-- ToyZc/Enum.lean
def nonLiteralZeroFullU8 : List (DiscrSyn × List Desc) :=
  (.other 0, []) :: List.replicate 255 (.implicit, [])
```

Kernel-checked examples of the core definitions. Positive examples (`..._pos`) test that a definition admits an intended case and negative examples (`..._neg`) that it rejects an unintended one. Further negative examples appear as the `not_*` lemmas and counterexample theorems cited in the cards.

* `ToyZc/Derive.lean`: `ex_findZeroVariant_pos`, `ex_findZeroVariant_neg`, `ex_findZeroVariant_neg_unknown`, `ex_implFromZeros_pos`, `ex_implFromZeros_neg`, `ex_implFromBytes_pos`, `ex_implFromBytes_neg`, `ex_implIntoBytes_pos`, `ex_implIntoBytes_neg`, `ex_implIntoBytes_neg_union_gate`, `ex_structPaddingOK_pos_packed`, `ex_structPaddingOK_neg`, `ex_enumPaddingOK_pos`, `ex_enumPaddingOK_neg`, `ex_unionPaddingOK_pos`, `ex_unionPaddingOK_neg`, `ex_implUnaligned_pos`, `ex_implUnaligned_neg`, `ex_implImmutable_pos`, `ex_implImmutable_neg`, `ex_isSafe_pos`, `ex_isSafe_neg`, `ex_couldBeFromBytes_neg`
* `ToyZc/Desc.lean`: `ex_IntTy_width_pos`, `ex_IntTy_width_neg`, `ex_IntTy_range_pos`, `ex_IntTy_range_neg`, `ex_layout_pos_padded_struct`, `ex_layout_pos_union`, `ex_layout_pos_enum`, `ex_layout_neg_packed`, `ex_resolveDiscrs_pos`, `ex_resolveDiscrs_neg`, `ex_discrCode_pos`, `ex_discrCode_neg`, `ex_leBytes_pos`, `ex_leNat_pos`, `ex_leNat_neg`, `ex_isPow2_pos`, `ex_isPow2_neg`, `ex_discrsWF_pos`, `ex_discrsWF_neg_dup`, `ex_discrsWF_neg_range`, `ex_wf_pos`, `ex_wf_neg_transparent`, `ex_wf_neg_empty_enum`, `ex_wf_neg_dup_discr`
* `ToyZc/Enum.lean`: `ex_enumTag_pos`, `ex_validVariant_pos`, `ex_validVariant_neg`, `ex_Fieldless_pos`, `ex_Fieldless_neg`, `ex_couldBeFromBytes_pos`
* `ToyZc/KnownLayout.lean`: `ex_sizeForElems_pos`, `ex_sizeForElems_neg`, `ex_maxTrailingBytes_pos`, `ex_maxTrailingBytes_neg`, `ex_vccm_pos`, `ex_vccm_neg_align`, `ex_vccm_neg_size`, `ex_vccm_suffix`, `ex_normalizeDst_pos`, `ex_normalizeDst_neg`, `ex_isMaxFit_pos`, `ex_isMaxFit_neg`, `ex_vccm_sized_pos`, `ex_vccm_sized_neg`, `ex_startOffset_pos`, `ex_startOffset_neg`
* `ToyZc/Layout.lean`: `ex_alignUp_pos`, `ex_alignUp_neg`, `ex_roundDown_pos`, `ex_roundDown_neg`, `ex_reprCStruct_pos_three_ints`, `ex_reprCStruct_neg_no_padding_assumed`, `ex_unionLayout_pos`, `ex_unionLayout_pos_packed`, `ex_unionLayout_neg`, `ex_reprIntEnum_pos_u8_packs_after_tag`, `ex_reprIntEnum_neg_not_reprC_u8`, `ex_reprCEnum_pos`, `ex_reprCEnum_neg_not_packed_after_tag`, `ex_dstSize_pos`, `ex_dstSize_neg_unaligned`, `ex_maxSliceElems_pos_some`, `ex_maxSliceElems_neg_naive`
* `ToyZc/Lemmas.lean`: `ex_validInit_pos`, `ex_validInit_neg`, `ex_hasType_pos`, `ex_hasType_neg`, `ex_encodeL_pos`, `ex_encodeL_neg`, `ex_decodeL_pos`, `ex_decodeL_neg`, `ex_rep_pos`, `ex_rep_neg`, `ex_semUnaligned_pos`, `ex_semUnaligned_neg`
* `ToyZc/NonClaims.lean`: `ex_sameBytes_neg`, `ex_byteDetermined_neg`
* `ToyZc/Transmute.lean`: `ex_transmuteVal_pos`, `ex_transmuteVal_neg`
* `ToyZc/Union.lean`: `ex_inhabited_pos`

Basis: execution (Lean kernel check)

### Modeling bridges

Each bridge is a separate claim connecting a Lean definition to zerocopy at commit
`c55af491426ef53f35fb8c6e83f220fa07712e66`. None of them is kernel-checked.

Basis: derived (modeling bridge). Reasoning: source inspection of the cited lines plus the
documented contracts; the correspondence is argued, not proved.

As above, `D/` abbreviates `zerocopy/zerocopy-derive/src/` and `Z/` abbreviates `zerocopy/src/`
(paths in the repository `google/zerocopy` at the pinned commit).

* **B1.** `SemFromBytes` corresponds to `FromBytes`'s contract "it is sound to produce a `T` whose bytes are
  initialized to any sequence of valid `u8`s" (`Z/lib.rs:4266-4269`): the model's decoder is the
  validity of initialized bytes.
* **B2.** `SemFromZeros` corresponds to "sound to produce a `T` whose bytes are all initialized to zero"
  (`Z/lib.rs:3681-3683`).
* **B3.** `SemIntoBytes` corresponds to "sound to treat any `t: T` as an immutable `[u8]` of length
  `size_of_val(t)`" (`Z/lib.rs:5913-5916`). Because the model's bytes carry no provenance, this means
  "no encoding contains `uninit`". This is a by-value reading: the reference conversions also need
  `Immutable`, or `IntoBytes`/`FromBytes` in the other direction.
* **B4.** `validInit` corresponds to `is_safe`'s contract "if `is_safe(candidate)` returns true,
  `*candidate` contains a valid `Self`" (`Z/lib.rs:1911-1912`). On unions, `validInit` *is* zerocopy's
  conservative rule ("some field is valid", `D/derive/try_from_bytes.rs:292-296`), not Rust's
  unsettled union validity.
* **B5.** `SemUnaligned` corresponds to "If `T: Unaligned`, then `align_of::<T>() == 1`" (`Z/lib.rs:6507`).
* **B6.** For slice DSTs, `vccm` corresponds to the documented guarantees of
  `validate_cast_and_convert_metadata` (`Z/layout.rs:1546-1591`): element count (R6a) and start
  alignment under the completed-layout premise (R6d). `#[derive(KnownLayout)]` itself is not modeled.
* **B7.** Union values are values written through one field. This is one of the two readings discussed
  in zerocopy issue 1792 (the "union safety" option, which needs further Rust guarantees: only safe
  construction from fields, typed copies that preserve written bytes, and an `IntoBytes` library
  safety invariant). MiniRust at commit `063d784186d3252bee242217f218223205c0b568` instead stores all
  bytes of a union (permissive validity); R4d records the consequence.
* **B8.** Each modeled derive check (`findZeroVariant`, `implFromZeros`, `implFromBytes`,
  `structPaddingOK`, `enumPaddingOK`, `unionPaddingOK`, `implIntoBytes`, `implUnaligned`,
  `implImmutable`, `isSafe`) transcribes the cited zerocopy-derive code and primitive impls (tables
  below). It assumes that every nominal type in a description requests the derive being modeled,
  so field bounds are discharged recursively.
* **B9.** The layout functions (`reprCStruct`, `reprCUnion`, `unionLayout`, `reprCEnum`, `reprIntEnum`,
  `dstTailOffset`, `dstAlign`, `dstSize`) follow the Rust Reference 1.81.0 "Type layout" chapter and
  RFC 2195 on `x86_64-unknown-linux-gnu` (integers little-endian, integer alignment equal to size,
  `repr(C)` enum tag 4 bytes for `i32`-range discriminants). `discrsWF` and `Desc.wf` stand for the
  compiler rules the results rely on: distinct and representable discriminants (E0081, overflow),
  power-of-two `packed`/`align` arguments, at most one non-1-ZST field in a `repr(transparent)`
  struct, and at least one variant per `repr` enum (E0084) and one field per union. `resolveDiscrs`
  stands for the compiler's assignment of discriminant values (an explicit discriminant is the value
  of its expression, recorded as `.other v` when the expression is not a literal; an implicit one is
  the previous value plus 1, and `0` for the first variant).
* **B10.** `transmuteVal s d v` corresponds to the `#[repr(C, packed)]` union transmute used by
  `transmute!(#![allow(shrink)] ...)` (`Z/macros.rs:106-146`): the destination reads the first
  `size_of::<Dst>()` bytes of the source. `core::mem::TransmuteFrom` (rust-lang/rust commit
  `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, `library/core/src/mem/transmutability.rs:14-59`) uses
  the same union-transmute notion and also permits a larger destination whose extra bytes are
  trailing padding (`transmute_extend_into_trailing_padding_example`). The equal-size form
  `transmute!(...)` is a plain `core::mem::transmute` (`Z/macros.rs:161-192`), which coincides with
  the union transmute when the sizes are equal; `desc_transmute_total_of_size_eq` models it.


### Source fidelity of the modeled checks (zerocopy commit `c55af491426ef53f35fb8c6e83f220fa07712e66`)

| Model | Source (file:line) | Quoted condition |
|---|---|---|
| `findZeroVariantAux` start state | `D/derive/from_bytes.rs:27, 35` | `let mut next_negative_discriminant = Some(0);` … `let mut has_unknown_discriminants = false;` |
| implicit discriminant | `D/derive/from_bytes.rs:40-46` | `None => { match next_negative_discriminant.as_mut() { Some(0) => return Ok(i), Some(n) => *n -= 1, None => (), } }` |
| literal / negated literal | `D/derive/from_bytes.rs:49-52, 61-66` | `Some(0) => return Ok(i), Some(_) => next_negative_discriminant = None,` / `Some(x) => next_negative_discriminant = Some(x - 1),` |
| other expression | `D/derive/from_bytes.rs:82-85` | `_ => { has_unknown_discriminants = true; next_negative_discriminant = None; }` |
| `FromZeros` enum | `D/derive/from_bytes.rs:143-175` | `match find_zero_variant(enm) { Ok(index) => enm.variants.iter().nth(index).unwrap(),` … `Err(true) => { return ctx.error_or_skip(` … `Err(false) => { return ctx.error_or_skip(` …; bounds `parse_quote! { #ty: #zerocopy_crate::FromZeros }` for the fields of `zero_variant` only (`FieldBounds::Explicit(explicit_bounds)`) |
| `FromZeros` co-derives `TryFromBytes` | `D/derive/from_bytes.rs:98`; `D/derive/try_from_bytes.rs:343` | `let try_from_bytes = derive_try_from_bytes(ctx, top_level)?;`; `ImplBlockBuilder::new(ctx, enm, Trait::TryFromBytes, FieldBounds::ALL_SELF)` (omitted: always satisfied in the model) |
| `FromZeros` struct / union | `D/derive/from_bytes.rs:122-124, 177-180` | `FieldBounds::ALL_SELF` / `FieldBounds::All(&[TraitBound::Slf])` |
| `FromBytes` runs `FromZeros` | `D/derive/from_bytes.rs:113` | `let from_zeros = derive_from_zeros(ctx, top_level)?;` |
| `enumVariantCountOK` | `D/derive/from_bytes.rs:187-188`; `D/util.rs:998-999` | `let variants_required = 1usize << enum_size_from_repr(&repr)?; if enm.variants.len() != variants_required {` ; `Primitive(U8 \| I8) … => Ok(8)`, `Primitive(U16 \| I16) … => Ok(16)` (all other reprs: error) |
| `FromBytes` fields | `D/derive/from_bytes.rs:181-183, 199, 201-204` | `FieldBounds::ALL_SELF` (struct, enum), `FieldBounds::All(&[TraitBound::Slf])` (union) |
| `structPaddingOK` shortcuts | `D/derive/into_bytes.rs:99-101, 119, 124, 143` | `if is_transparent \|\| is_packed_1 {` … `} else if is_c && !repr.is_align_gt_1() && num_fields <= 1 {` … `} else if ctx.ast.generics.params.is_empty() {` … `(Some(PaddingCheck::Struct), false, None)` |
| `struct_padding!` | `Z/util/macro_util.rs:338, 63-64` | `$crate::util::macro_util::size_of::<$t>() - (0 $(+ $crate::util::macro_util::size_of::<$ts>())*)`, which must be `0`: `pub trait PaddingFree<T: ?Sized, const PADDING_BYTES: usize> {}` and only `impl<T: ?Sized> PaddingFree<T, 0> for () {}` |
| `IntoBytes` enum | `D/derive/into_bytes.rs:198, 206-207`; `Z/util/macro_util.rs:431-435` | `if !repr.is_c() && !repr.is_primitive() {`; `ImplBlockBuilder::new(ctx, enm, Trait::IntoBytes, FieldBounds::ALL_SELF) .padding_check(PaddingCheck::Enum { tag_type_definition })`; per variant `let padding = $crate::util::macro_util::size_of::<$t>() - ( $crate::util::macro_util::size_of::<$disc>() $(+ $crate::util::macro_util::size_of::<$ts>())* );` |
| `IntoBytes` union + gate | `D/derive/into_bytes.rs:212, 220, 229-230, 255-256`; `Z/util/macro_util.rs:393` | `// See #1792 for more context.`; `let cfg_compile_error = if cfg!(zerocopy_derive_union_into_bytes) {`; `#[cfg(not(zerocopy_derive_union_into_bytes))] #core::compile_error!(#error_message);`; `ImplBlockBuilder::new(ctx, unn, Trait::IntoBytes, FieldBounds::ALL_SELF) .padding_check(PaddingCheck::Union)`; per field `let padding = $crate::util::macro_util::size_of::<$t>() - $crate::util::macro_util::size_of::<$ts>();` |
| `implUnaligned` struct | `D/derive/unaligned.rs:26, 28-33` | `repr.unaligned_validate_no_align_gt_1()?;` `let field_bounds = if repr.is_packed_1() { FieldBounds::None } else if repr.is_c() \|\| repr.is_transparent() { FieldBounds::ALL_SELF } else { return ctx.error_or_skip(` … |
| `implUnaligned` enum | `D/derive/unaligned.rs:47, 49` | `repr.unaligned_validate_no_align_gt_1()?;` `if !repr.is_u8() && !repr.is_i8() {` → error |
| `implUnaligned` union | `D/derive/unaligned.rs:66, 68-71` | as for structs |
| `isPacked1`, `isAlignGt1` | `D/repr.rs:169-172, 148-150` | `self.get_packed().map(\|n\| n.get() == 1).unwrap_or(false)`; `self.get_align().map(\|n\| n.t.get() > 1).unwrap_or(false)` |
| `implImmutable` | `D/derive/mod.rs:19-31` | `ImplBlockBuilder::new(ctx, strct, Trait::Immutable, FieldBounds::ALL_SELF)` (and enum, union) |
| `isSafe` struct / fields | `D/derive/try_from_bytes.rs:33-71, 235-269` (`derive_variant_is_safe`, `derive_try_from_bytes_struct`; lines 39-41, 63, 69-71, 245, 250-253, 261) | `if fields.is_empty() { return Ok(quote!(true)); }`; per field `.try_into_safe::<_, #zerocopy_crate::BecauseImmutable>()`; `if ctx.invariant_span.is_none() { return Ok(quote! { true #(&& #field_checks.is_ok())* }); }` (the model has no field invariants, so only this branch is modeled); `let fields_is_safe = derive_variant_is_safe(ctx, &variant_id, &strct.fields)?;`; "We use `is_safe` to validate that each field is bit-valid, and only return `true` if all of them are. The bit validity of a struct is just the composition of the bit validities of its fields"; body `#fields_is_safe` |
| `isSafe` enum | `D/derive/try_from_bytes.rs:221-224, 327-329, 332-336` | `match #tag { #(#match_arms,)* _ => false, }`; `enum_size_from_repr(&repr).map(\|size\| enm.fields().is_empty() && enm.variants.len() == 1usize << size).unwrap_or(false)`; `(None, true) => unsafe { gen_trivial_is_safe_unchecked(ctx) }` |
| `isSafe` union | `D/derive/try_from_bytes.rs:292-296, 306` | "validate that any field is bit-valid … guaranteed to be no more strict than this definition. See #696"; `false #(\|\| { … #fields_is_safe … }())*` |
| primitive impls | `Z/impls.rs:68-76, 101, 115, 839-850, 853-868, 893-908` | integers: `Immutable, TryFromBytes, FromZeros, FromBytes, IntoBytes` (+ `Unaligned` for `u8`, `i8`); `bool: Immutable, FromZeros, IntoBytes, Unaligned`; bool validator `*byte.unaligned_as_ref() < 2`; `UnsafeCell<T>`: `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`, `TryFromBytes` (no `Immutable`); arrays: each trait iff the element |
| `vccm` | `Z/layout.rs:1688-1690, 1713-1716, 1723-1724, 1729-1731, 1736-1738, 1746, 1766-1778, 1785-1793` | `None => const_panic!("attempted to cast to slice type with zero-sized element"),`; `CastType::Prefix => 0, CastType::Suffix => bytes_len,`; `if (addr + offset) % self.align.get() != 0 { return Err(MetadataCastError::Alignment);`; sized: `if size > bytes_len { return Err(MetadataCastError::Size);`; `let max_slice_bytes = match trailing.max_trailing_bytes(bytes_len) {` … `None => return Err(MetadataCastError::Size),`; `let (elems, _) = max_elems_for_bytes(max_slice_bytes, trailing.elem_size);`; `let unused_bytes = max_slice_bytes % trailing.elem_size.get();`; `let unused_aligned_bytes = util::round_down_to_next_multiple_of_alignment(unused_bytes, size_align);`; `let self_bytes = trailing.size_base + (max_rounded_bytes - unused_aligned_bytes);`; `CastType::Prefix => self_bytes,` … `CastType::Suffix => bytes_len - self_bytes,` |
| `maxTrailingBytes` | `Z/layout.rs:283, 289-292, 298-301, 313, 321, 339` | `let rounded_phase = if size_phase == 0 { 0 } else { size_align.get() };`; `let minimum_size = match self.size_base.checked_add(rounded_phase) { Some(size) => size, None => return None, };`; `let extra_bytes = match available_bytes.checked_sub(minimum_size) { Some(bytes) => bytes, None => return None, };`; `let aligned_bytes = util::round_down_to_next_multiple_of_alignment(extra_bytes, size_align);`; `let initial_padding = rounded_phase - size_phase;`; `let trailing_bytes = aligned_bytes \| initial_padding;` (the disjoint-bit OR is modeled by `+`; the overflow branch of `checked_add` does not arise over unbounded naturals, and the failure of `checked_sub` is the model's `none` result when fewer bytes than the minimum size are available) |

Basis: source (quotations at the pinned commit) + derived (modeling bridge)

### Results

### R1-semantic-predicates-list-characterizations

- **Tier / kind / depth:** T0 / characterization / definitional. T0: definitional unfolding of the representation predicates to list-level statements; no new mathematics.
- **Plain claim:** In the model, for every type description d: SemFromBytes d (every fully initialized byte vector decodes under the modeled representation Desc.rep d) holds iff the modeled validity check validInit accepts every byte list of length d.size; SemFromZeros d holds iff validInit accepts the all-zero byte list of length d.size; and SemIntoBytes d holds iff every byte below d.size of the modeled encoding of every well-typed value is initialized.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Bridge.lean:46-47
theorem semFromBytes_iff_validInit_total (d : Desc) :
    SemFromBytes d ↔ ∀ bs : List Byte, bs.length = d.size → validInit d bs = true

-- lean/ToyZc/Bridge.lean:62-63
theorem semFromZeros_iff_validInit_zeros (d : Desc) :
    SemFromZeros d ↔ validInit d (List.replicate d.size 0) = true

-- lean/ToyZc/Bridge.lean:75-77
theorem semIntoBytes_iff_encodeL_init (d : Desc) :
    SemIntoBytes d ↔
      ∀ v, d.hasType v = true → ∀ i, i < d.size → ((d.encodeL v).getD i .uninit).isInit = true
```
- **Unfolded reading** (key definitions expanded; prose):

```text
SemFromBytes d := ∀ x : Bytes Byte d.size, x.IsInit → ∃ v, d.rep.decode x = some v
  ⟺ ∀ bs : List Byte, bs.length = d.size → validInit d bs = true
SemFromZeros d := (d.rep.tryFrom (replicate d.size 0)).isSome ⟺ validInit d (replicate d.size 0) = true
SemIntoBytes d := ∀ v : TVal d, (d.rep.encode v).IsInit
  ⟺ ∀ v, d.hasType v → ∀ i < d.size, (d.encodeL v)[i] ≠ uninit
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** definitional.
- **Non-vacuity witness:** u8 satisfies SemFromBytes, SemFromZeros and SemIntoBytes (each proved through the corresponding equivalence). (`Toy.Zc.semFromBytes_int`, `Toy.Zc.semFromZeros_int`, `Toy.Zc.semIntoBytes_int`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): FromBytes safety contract, zerocopy/src/lib.rs:4266-4269 ('it is sound to produce a T whose bytes are initialized to any sequence of valid u8s'); FromZeros, zerocopy/src/lib.rs:3681-3683; IntoBytes, zerocopy/src/lib.rs:5913-5916; TryFromBytes::is_safe, zerocopy/src/lib.rs:1907-1912; Unaligned, zerocopy/src/lib.rs:6507.
  - MiniRust, spec/lang/representation.md, minirust/minirust commit 063d784186d3252bee242217f218223205c0b568: representations as encode/decode over abstract bytes (the vocabulary these definitions follow).
  - Xavier Leroy and Sandrine Blazy, 'Formal verification of a C-like memory model and its uses for verifying program transformations', Journal of Automated Reasoning 41(1), 2008, DOI 10.1007/s10817-008-9099-0: a Coq memory model whose stored bytes are either undefined or concrete, with encode/decode of values to bytes (an earlier mechanized byte-representation vocabulary).
  - Harvey Tuch, Gerwin Klein, Michael Norrish, 'Types, Bytes, and Separation Logic', POPL 2007, DOI 10.1145/1190216.1190234: Isabelle/HOL model of typed values over a byte-addressed heap.
  - Kayvan Memarian, Victor B. F. Gomes, Brooks Davis, Stephen Kell, Alexander Richardson, Robert N. M. Watson, Peter Sewell, 'Exploring C semantics and pointer provenance', PACMPL 3(POPL), 2019, DOI 10.1145/3290380: byte-level representation with pointer provenance in C (the present model's bytes carry no provenance).
- **Design question:** Which precise byte-level predicates should stand for zerocopy's trait contracts when reasoning about derive checks?
- **Non-claims:** see Boundaries, R1.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B2, B3, B4. R1 is what lets the remaining results be read as statements about zerocopy's contracts: with abstract bytes `uninit | init b` and no provenance, "any initialized byte sequence is a valid `T`" is totality of the decoder on initialized bytes, and "every value can be viewed as `[u8]`" is "no encoding contains `uninit`".

### R2a-struct-fromBytes-fromZeros-iff-fields

- **Tier / kind / depth:** T1 / characterization / shallow. T1: stated informally in zerocopy's derive documentation (zerocopy/src/lib.rs:4167-4168, 1532-1533); made precise over an explicit decoder and layout. No mechanized version found (searched the cited sources, the Aeneas layout prototype, and web search for zerocopy formal verification).
- **Plain claim:** In the model, for every modeled struct representation (repr(C) with or without packed(N) or align(N), or repr(transparent)) and every list of field descriptions, the struct description is SemFromBytes iff every field is SemFromBytes, and SemFromZeros iff every field is SemFromZeros, whether or not its modeled layout has padding.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Struct.lean:84-85
theorem struct_fromBytes_iff_fields_fromBytes (r : StructRepr) (fs : List Desc) :
    SemFromBytes (.strct r fs) ↔ ∀ f ∈ fs, SemFromBytes f

-- lean/ToyZc/Struct.lean:121-122
theorem struct_fromZeros_iff_fields_fromZeros (r : StructRepr) (fs : List Desc) :
    SemFromZeros (.strct r fs) ↔ ∀ f ∈ fs, SemFromZeros f
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ bs, |bs| = size(S) → validInit S bs) ⟺ ∀ f ∈ fs, ∀ bs, |bs| = size f → validInit f bs   (S = strct r fs, any r)
validInit S (replicate size(S) 0) ⟺ ∀ f ∈ fs, validInit f (replicate size(f) 0)
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** shallow.
- **Non-vacuity witness:** #[repr(C)] struct { a: u8, b: u16 } (one padding byte) with FromBytes and FromZeros fields. (`Toy.Zc.nv_struct_fromBytes_fromZeros_padded`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): FromBytes derive analysis 'If the type is a struct, all of its fields must be FromBytes' and 'Whether a struct is soundly FromBytes therefore solely depends on whether its fields are FromBytes' (zerocopy/src/lib.rs:4131, 4167-4168); FromZeros analogues (zerocopy/src/lib.rs:1493, 1532-1533); derive code zerocopy/zerocopy-derive/src/derive/from_bytes.rs:122-124, 181-183.
  - Rust Unsafe Code Guidelines issue 174, 'Padding Bytes Guarantees?', https://github.com/rust-lang/unsafe-code-guidelines/issues/174 (cited by zerocopy for 'padding bytes do not have any validity constraints').
- **Design question:** Do the struct FromBytes/FromZeros derives need a repr or a padding check? (They need neither.)
- **Non-claims:** see Boundaries, R2a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B2, B8, B9. Read with B8, R2a says that zerocopy-derive's struct `FromBytes`/`FromZeros` derives (field bounds only, `D/derive/from_bytes.rs:122-124, 181-183`) need no `repr` or padding check for the modeled representations. The model's decoder never reads padding, following zerocopy's statement that padding bytes have no validity constraints (`zerocopy/src/lib.rs:4167-4168`).

### R2c-struct-intoBytes-iff-fields-and-no-padding

- **Tier / kind / depth:** T1 / characterization / substantive. T1: zerocopy states the no-padding criterion informally (zerocopy/src/lib.rs:5848-5849); this makes the equivalence precise, including the inhabitedness condition it silently needs.
- **Plain claim:** In the model, for a struct description (any modeled representation) whose field descriptions are all inhabited, the struct is SemIntoBytes iff every field is SemIntoBytes and the struct's modeled size equals the sum of its field sizes.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Struct.lean:172-175
theorem struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited (r : StructRepr) (fs : List Desc)
    (hInh : ∀ f ∈ fs, f.Inhabited) :
    SemIntoBytes (.strct r fs) ↔
      (∀ f ∈ fs, SemIntoBytes f) ∧ (Desc.strct r fs).size = Desc.fieldSizeSum fs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ f ∈ fs, ∃ v, f.hasType v) →
  (no encoding of S contains uninit ⟺ (∀ f ∈ fs, no encoding of f contains uninit) ∧ size(S) = Σ_{f∈fs} size f)
where size(S) = (r.layout (map layout fs)).size, the repr(C) algorithm reprCStruct.
```
- **Hypothesis ledger:**
  - `hInh`: Each field type has a value; needed for the left-to-right direction (an uninhabited field makes IntoBytes vacuous). Counterexample in canonical form: inhabitedness fails and the equivalence fails. Tightness: **tight: counterexample `Toy.Zc.ce_struct_intoBytes_iff_drop_inhabited`**.
  - `(right side) every field IntoBytes`: Conjunct of the characterization; a padded field type leaks uninit bytes even without top-level padding. Counterexample: inhabited fields, size = sum, not every field IntoBytes, struct not IntoBytes. Tightness: **tight: counterexample `Toy.Zc.ce_struct_drop_fields_intoBytes`**.
  - `(right side) size = sum of field sizes`: Conjunct of the characterization (no padding). Counterexample: inhabited IntoBytes fields, size 4 differs from sum 3, struct not IntoBytes. Tightness: **tight: counterexample `Toy.Zc.ce_padded_struct_of_intoBytes_fields_not_intoBytes`**.
- **Depth:** substantive.
- **Non-vacuity witness:** #[repr(C)] struct { a: u16, b: u8, c: u8 }: inhabited IntoBytes fields, size 4 = 2+1+1. (`Toy.Zc.nv_struct_intoBytes`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): IntoBytes derive analysis 'if the type has no generic parameters, it is IntoBytes if the type is sized and has no padding bytes' (zerocopy/src/lib.rs:5848-5849); struct_padding! (zerocopy/src/util/macro_util.rs:333-340).
  - Rust Reference 1.81.0, Type layout, https://doc.rust-lang.org/1.81.0/reference/type-layout.html (repr(C) struct layout).
  - Harvey Tuch, Gerwin Klein, Michael Norrish, 'Types, Bytes, and Separation Logic', POPL 2007, DOI 10.1145/1190216.1190234; and AutoCorres2 (M. Brecknell et al.), Archive of Formal Proofs, April 2024, https://isa-afp.org/entries/AutoCorres2.html: Isabelle/HOL formalizations of C struct layout with padding over byte heaps (C, not Rust; no derive checks).
  - Robbert Krebbers, 'The C Standard Formalized in Coq', PhD thesis, Radboud University Nijmegen, 2015, https://hdl.handle.net/2066/147182: Coq semantics of C11 including indeterminate padding bytes and unions.
  - Tahina Ramananandro, Gabriel Dos Reis, Xavier Leroy, 'Formal verification of object layout for C++ multiple inheritance', POPL 2011, DOI 10.1145/1926385.1926395: Coq-verified object layout algorithms including padding (C++ ABI, not Rust repr(C)).
- **Design question:** Is 'all fields IntoBytes and size = sum of field sizes' the right semantic target for the struct IntoBytes derive?
- **Non-claims:** see Boundaries, R2c.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B9. Read with B3 and B9, R2c is the semantic target that the struct `IntoBytes` derive approximates: `repr(C)` placement follows the Rust Reference's type-layout rules.

### R2d-struct-padding-analysis-sound

- **Tier / kind / depth:** T1 / theorem / shallow. T1: the shortcuts are justified by comments in zerocopy/zerocopy-derive/src/derive/into_bytes.rs:99-123; made precise, with the compiler rules they rely on isolated.
- **Plain claim:** In the model, for a well-formed struct description (Desc.wf), if the modeled IntoBytes padding analysis structPaddingOK passes (repr(transparent); or repr(C, packed(1)); or repr(C) without align(N>1) and with at most one field; or the modeled size minus the sum of the field sizes is 0), then the struct's modeled size equals the sum of its field sizes.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Struct.lean:499-501
theorem structPaddingOK_sound (r : StructRepr) (fs : List Desc)
    (hwf : (Desc.strct r fs).wf = true) (hP : structPaddingOK r fs = true) :
    (Desc.strct r fs).size = Desc.fieldSizeSum fs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
wf(S) → [ r = transparent ∨ (r = c m ∧ (m = packed 1 ∨ (¬(m = aligned n ∧ n > 1) ∧ |fs| ≤ 1) ∨ size(S) - Σ size f = 0)) ]
      → size(S) = Σ_{f∈fs} size f
```
- **Hypothesis ledger:**
  - `hwf`: Compiler rules used: at most one non-1-ZST field in repr(transparent); power-of-two packed/align arguments, both on the struct itself and (via Desc.wfAll) inside its fields (so a one-field repr(C, packed(N)) struct has no trailing padding). Tightness: **tight: counterexample `Toy.Zc.ce_structPaddingOK_drop_wf`, `Toy.Zc.ce_structPaddingOK_drop_wf_packed3`, `Toy.Zc.ce_structPaddingOK_drop_inner_wf`**.
  - `hP`: The modeled padding analysis of into_bytes.rs:99-144. Tightness: **tight: counterexample `Toy.Zc.ce_one_field_align_gt_1_has_trailing_padding`**.
- **Depth:** shallow.
- **Non-vacuity witness:** Each shortcut on a well-formed struct: transparent with a ZST and a u32, repr(C, packed) {u8,u16}, repr(C, packed(2)) {u32}, repr(C) {u16,u8,u8}. (`Toy.Zc.nv_structPaddingOK`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/into_bytes.rs:99-123 (shortcuts and their justification comments), 124-144 (padding check for non-generic structs); zerocopy/zerocopy-derive/src/repr.rs:148-150 (is_align_gt_1), 169-171 (is_packed_1); struct_padding! zerocopy/src/util/macro_util.rs:333-340.
  - Rust Reference 1.81.0, Type layout, 'a type with #[repr(packed(1))] (or #[repr(packed)]) will have no inter-field padding'.
- **Design question:** Is each shortcut of the struct IntoBytes padding analysis a sound replacement for the size check, and why is align(N>1) excluded?
- **Non-claims:** see Boundaries, R2d.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B8, B9. `structPaddingOK` transcribes `D/derive/into_bytes.rs:99-144` and `struct_padding!` (`zerocopy/src/util/macro_util.rs:333-340`), see the source-fidelity table. Combined with R2c, R2d reads as: the derive's padding analysis is sound for well-formed, non-generic modeled structs.

### R2e-derives-sound-on-well-formed-descriptions

- **Tier / kind / depth:** T1 / theorem / substantive. T1: zerocopy asserts soundness of its derives in prose and comments (its Kani proofs cover layout arithmetic, not derive checks); this is a precise soundness statement for a model of the checks, isolating the compiler rules used.
- **Plain claim:** In the model, every well-formed description (Desc.wf) accepted by the modeled FromZeros, FromBytes or IntoBytes derive check (implFromZeros, implFromBytes, implIntoBytes, which include models of zerocopy's primitive impls; implIntoBytes in either setting of the union cfg) is SemFromZeros, SemFromBytes or SemIntoBytes respectively; and every description accepted by the modeled Unaligned derive check implUnaligned has modeled alignment 1 (no well-formedness needed).
- **Lean statement(s):**

```lean
-- lean/ToyZc/Closure.lean:251-252
theorem derive_fromZeros_sound_of_wf (d : Desc) (hwf : d.wf = true) (h : implFromZeros d = true) :
    SemFromZeros d

-- lean/ToyZc/Closure.lean:296-297
theorem derive_fromBytes_sound_of_wf (d : Desc) (hwf : d.wf = true) (h : implFromBytes d = true) :
    SemFromBytes d

-- lean/ToyZc/Closure.lean:335-336
theorem derive_intoBytes_sound_of_wf (cfg : DeriveConfig) (d : Desc) (hwf : d.wf = true)
    (h : implIntoBytes cfg d = true) : SemIntoBytes d

-- lean/ToyZc/Closure.lean:371
theorem derive_unaligned_sound (d : Desc) (h : implUnaligned d = true) : SemUnaligned d
```
- **Unfolded reading** (key definitions expanded; prose):

```text
wf d → implFromZeros d → validInit d 0^size(d)
wf d → implFromBytes d → ∀ bs of length size(d), validInit d bs
wf d → implIntoBytes cfg d → no encoding of d contains uninit        (any cfg)
implUnaligned d → align(d) = 1                                       (no wf)
```
- **Hypothesis ledger:**
  - `hwf (derive_fromZeros_sound_of_wf, derive_fromBytes_sound_of_wf, derive_intoBytes_sound_of_wf; derive_unaligned_sound has no such hypothesis)`: Compiler rules the checks rely on: distinct, representable discriminants; nonempty unions; the repr(transparent) 1-ZST rule; power-of-two modifiers. Tightness: **tight: counterexample `Toy.Zc.ce_derive_fromZeros_drop_wf`, `Toy.Zc.ce_derive_fromBytes_drop_wf`, `Toy.Zc.ce_derive_intoBytes_drop_wf`**.
  - `h (the check; all four theorems)`: The modeled derive accepts the description. Counterexample: well-formed descriptions rejected by each check that lack the property. Tightness: **tight: counterexample `Toy.Zc.ce_derive_drop_check`**.
- **Depth:** substantive.
- **Non-vacuity witness:** {u8,u16} (well-formed) passes FromZeros and FromBytes; {u16,u8,u8} passes IntoBytes; repr(C, packed) {u8,u16} passes Unaligned. (`Toy.Zc.nv_derive_sound`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): derive entry points zerocopy/zerocopy-derive/src/lib.rs:130-137; checks in zerocopy/zerocopy-derive/src/derive/from_bytes.rs, derive/into_bytes.rs, derive/unaligned.rs; primitive impls zerocopy/src/impls.rs:68-76 (integers), 101 (bool), 839-850 (UnsafeCell), 893-908 (arrays).
- **Design question:** Are zerocopy's derive checks sound with respect to precise byte-level semantics on closed types, and which compiler rules do they silently depend on?
- **Non-claims:** see Boundaries, R2e.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B2, B3, B5, B8, B9. Every modeled check transcribes zerocopy-derive at the pinned commit together with the primitive impls in `zerocopy/src/impls.rs` (B8). So R2e reads as soundness of the derives for closed, non-generic types built from the modeled primitives that satisfy the compiler rules in `Desc.wf`.

### R2f-derived-isSafe-equals-validity

- **Tier / kind / depth:** T1 / theorem / substantive. T1: the SAFETY comments of the derived validators state this informally; made precise, with the length precondition and the discriminant rules isolated.
- **Plain claim:** In the model, for every well-formed description and every byte list whose length is the description's modeled size, the modeled TryFromBytes::is_safe (isSafe: the model of the derived validator for structs, enums and unions together with zerocopy's primitive validators) returns exactly the model's validity check validInit.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Closure.lean:430-431
theorem derive_isSafe_eq_validInit_of_wf_of_length (d : Desc) (hwf : d.wf = true) (bs : List Byte)
    (hlen : bs.length = d.size) : isSafe d bs = validInit d bs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
wf d → |bs| = size(d) → isSafe d bs = validInit d bs
(unions: validInit = "some field decodes its prefix", which is also what isSafe checks)
```
- **Hypothesis ledger:**
  - `hwf`: Distinct representable discriminants (the enum could_be_from_bytes shortcut relies on them) and the other compiler rules of Desc.wf. Tightness: **tight: counterexample `Toy.Zc.ce_derive_isSafe_drop_wf`**.
  - `hlen`: The bytes have the description's size; the validators never check the length (zerocopy only calls them on correctly sized candidates). Tightness: **tight: counterexample `Toy.Zc.ce_derive_isSafe_drop_hlen`**.
- **Depth:** substantive.
- **Non-vacuity witness:** The well-formed enum #[repr(u8)] enum { A(u8), B(bool) = 5 } and the 2-byte list [5, 1]. (`Toy.Zc.nv_derive_isSafe`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): struct validator derive_try_from_bytes_struct zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:235-269 (SAFETY comment 250-253) and the per-field conjunction derive_variant_is_safe 33-71 (without field invariants, true && each field check at 69-71); enum validator derive_is_safe and its SAFETY comment 207-226; union validator 282-307; could_be_from_bytes 322-341; TryFromBytes::is_safe contract zerocopy/src/lib.rs:1907-1912; primitive validators zerocopy/src/impls.rs:112-117 (bool), 853-868 (UnsafeCell), 894-904 (arrays).
- **Design question:** Does the derived TryFromBytes validator compute exactly the validity of the model on closed well-formed types, and what does it rely on?
- **Non-claims:** see Boundaries, R2f.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B4, B8. `isSafe` transcribes the generated `is_safe` of a `TryFromBytes`-top-level derive (`D/derive/try_from_bytes.rs`). On unions, the model's validity *is* zerocopy's conservative rule, so the union case of R2f is agreement with that rule, not with Rust's unsettled union validity.

### R3a-fieldless-enum-fromBytes-iff-all-tags

- **Tier / kind / depth:** T1 / characterization / shallow. T1: documented informally (zerocopy/src/lib.rs:4135-4136).
- **Plain claim:** In the model, a fieldless enum description with a primitive representation repr(t) is SemFromBytes iff every tag value n < 2^(8*width t) is the tag code (Desc.codes) of some variant's resolved discriminant.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:772-775
theorem fieldless_enum_fromBytes_iff_every_tag_is_discriminant (t : IntTy)
    (vs : List (DiscrSyn × List Desc)) (hfl : Desc.Fieldless vs) :
    SemFromBytes (.enm (.prim t) vs) ↔
      ∀ n, n < 2 ^ (8 * t.width) → n ∈ Desc.codes (.prim t) vs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ v ∈ vs, v.fields = []) →
  (∀ bs of length w, validInit (enm (prim t) vs) bs) ⟺ ∀ n < 2^(8w), ∃ i, (discr_i mod 2^(8w)) = n   (w = width t)
```
- **Hypothesis ledger:**
  - `hfl`: All variants are fieldless; with fields, every tag being a discriminant is not enough (canonical counterexample: not fieldless and the equivalence fails). Tightness: **tight: counterexample `Toy.Zc.ce_fieldless_enum_fromBytes_iff_drop_fieldless`**.
- **Depth:** shallow.
- **Non-vacuity witness:** repr(u8) enum with 256 fieldless variants 0..255. (`Toy.Zc.nv_fieldless_full_u8`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): FromBytes derive analysis 'The maximum number of discriminants must be used (so that every possible bit pattern is a valid one)' (zerocopy/src/lib.rs:4135-4136).
- **Design question:** What exactly must hold for a fieldless enum to be SemFromBytes?
- **Non-claims:** see Boundaries, R3a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B9. Tag placement (offset 0, little-endian, width of the primitive) and discriminant resolution follow the Rust Reference / RFC 2195 primitive-representation enum layout on the modeled target.

### R3b-enum-variant-count-check-sound

- **Tier / kind / depth:** T1 / theorem / substantive. T1: the pigeonhole reasoning behind the count check is implicit in zerocopy; made precise with its dependence on E0081 and range checks.
- **Plain claim:** In the model, if an enum description's resolved discriminants are pairwise distinct and representable in its tag type (discrsWF), then the modeled FromBytes variant-count check enumVariantCountOK (representation u8, i8, u16 or i16 and exactly 2^bits variants) implies that every tag value n < 2^(8*width) is the tag code of some resolved discriminant.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:813-815
theorem enum_variant_count_check_sound (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (hc : enumVariantCountOK r vs = true) :
    ∀ n, n < 2 ^ (8 * r.tagTy.width) → n ∈ Desc.codes r vs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
discriminants pairwise distinct ∧ each in [minVal t, maxVal t] → r ∈ {u8,i8,u16,i16} ∧ |vs| = 2^(8w)
  → ∀ n < 2^(8w), ∃ i, (discr_i mod 2^(8w)) = n
```
- **Hypothesis ledger:**
  - `hwf`: Distinct (compiler error E0081 otherwise) and representable discriminants; the count check is a pigeonhole argument that needs both (one counterexample drops each half). Tightness: **tight: counterexample `Toy.Zc.ce_count_check_drop_wf`, `Toy.Zc.ce_count_check_drop_representable`**.
  - `hc`: The count check itself (from_bytes.rs:187-197). Tightness: **tight: counterexample `Toy.Zc.ce_count_check_drop_count`**.
- **Depth:** substantive.
- **Non-vacuity witness:** repr(u8) enum with 256 implicit discriminants. (`Toy.Zc.nv_fieldless_full_u8`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/from_bytes.rs:184-200; zerocopy/zerocopy-derive/src/util.rs:982-1001 (enum_size_from_repr).
- **Design question:** Why is counting variants a sound substitute for checking that every bit pattern is a discriminant?
- **Non-claims:** see Boundaries, R3b.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B8, B9. `enumVariantCountOK` transcribes `D/derive/from_bytes.rs:187-197` and `enum_size_from_repr` (`zerocopy/zerocopy-derive/src/util.rs:982-1001`). `discrsWF` stands for the compiler's duplicate-discriminant error E0081 and the discriminant-overflow error, which the derive relies on but does not check.

### R3c-enum-fromBytes-derive-sound

- **Tier / kind / depth:** T1 / theorem / shallow. T1: informal in zerocopy/src/lib.rs:4132-4137; precise for data-carrying enums.
- **Plain claim:** In the model, for an enum description (fieldless or data-carrying) whose resolved discriminants are distinct and representable (discrsWF), if the modeled variant-count check enumVariantCountOK passes and every field of every variant is SemFromBytes, then the enum is SemFromBytes; even when all of these hypotheses hold, the modeled derive check implFromBytes, which also runs findZeroVariant, can reject the enum (Toy.Zc.fromBytes_enum_rejected_by_findZeroVariant: the fieldless repr(u8) enum description nonLiteralZeroFullU8 satisfies them and is SemFromBytes, yet implFromBytes rejects it).
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:820-823
theorem enum_fromBytes_of_count_check (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (hc : enumVariantCountOK r vs = true)
    (hF : ∀ v ∈ vs, ∀ f ∈ v.2, SemFromBytes f) :
    SemFromBytes (.enm r vs)
```
- **Unfolded reading** (key definitions expanded; prose):

```text
distinct representable discriminants → count check → (∀ variant, ∀ field, SemFromBytes field) → SemFromBytes (enm r vs)
```
- **Hypothesis ledger:**
  - `hwf`: Distinct and representable discriminants (one counterexample drops each half). Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromBytes_drop_wf`, `Toy.Zc.ce_enum_fromBytes_drop_representable`**.
  - `hc`: The count check. Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromBytes_drop_count`**.
  - `hF`: Every field of every variant is SemFromBytes. Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromBytes_drop_fields`**.
- **Depth:** shallow.
- **Non-vacuity witness:** repr(u8) enum with 256 variants, variant 0 carrying a u8. (`Toy.Zc.nv_enum_fromBytes_data`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/from_bytes.rs:106-121, 184-200; zerocopy/src/lib.rs:4132-4137.
  - Rust RFC 2195, 'Really Tagged Unions' (start date 2017-10-30), https://rust-lang.github.io/rfcs/2195-really-tagged-unions.html: specifies the repr(C) and repr(Int) layouts of data-carrying enums (tag followed by a union of variant structs) that the model's enum layout follows.
- **Design question:** Is the enum FromBytes derive sound for data-carrying enums?
- **Non-claims:** see Boundaries, R3c.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B8, B9. As for R3b, together with the field bounds of `D/derive/from_bytes.rs:199`.

### R3d-enum-fromZeros-iff-zero-variant

- **Tier / kind / depth:** T1 / characterization / shallow. T1: documented informally (zerocopy/src/lib.rs:1497-1500).
- **Plain claim:** In the model, for an enum description whose resolved discriminants are distinct and representable (discrsWF), the enum is SemFromZeros iff some variant has resolved discriminant 0 and every field of that variant is SemFromZeros.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:848-852
theorem enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF (r : EnumRepr)
    (vs : List (DiscrSyn × List Desc)) (hwf : discrsWF r (vs.map Prod.fst) = true) :
    SemFromZeros (.enm r vs) ↔
      ∃ i fs, (Desc.discrs vs)[i]? = some 0 ∧ variantFields vs i = some fs ∧
        ∀ f ∈ fs, SemFromZeros f
```
- **Unfolded reading** (key definitions expanded; prose):

```text
distinct representable discriminants →
  (validInit E 0^size(E) ⟺ ∃ i, discr_i = 0 ∧ ∀ f ∈ fields_i, validInit f 0^size(f))
```
- **Hypothesis ledger:**
  - `hwf`: Distinct representable discriminants: decoding selects the first variant with tag 0, which must be the zero variant (one counterexample drops each half). Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromZeros_iff_drop_wf`, `Toy.Zc.ce_enum_fromZeros_iff_drop_representable`**.
- **Depth:** shallow.
- **Non-vacuity witness:** repr(i8) enum { A(bool) = 3, B = -1, C(u16) } (C has discriminant 0). (`Toy.Zc.nv_enum_fromZeros`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): FromZeros derive analysis 'It must have a variant with a discriminant/tag of 0, and its fields must be FromZeros' (zerocopy/src/lib.rs:1497-1500).
  - Rust RFC 2195, 'Really Tagged Unions', https://rust-lang.github.io/rfcs/2195-really-tagged-unions.html (enum layouts with fields).
- **Design question:** What does an enum need in order to be FromZeros?
- **Non-claims:** see Boundaries, R3d.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B2, B9. The decoder selects the first variant whose code equals the tag. Under `discrsWF` this is the unique variant with that discriminant, as in Rust for accepted enums.

### R3e-find-zero-variant-and-enum-fromZeros-derive

- **Tier / kind / depth:** T1 / theorem / shallow. T1: correctness of the scan is argued in its comments (zerocopy/zerocopy-derive/src/derive/from_bytes.rs:14-90); made precise (soundness, conditional completeness).
- **Plain claim:** In the model, findZeroVariant (the model of zerocopy-derive's syntactic find_zero_variant) is sound with respect to the model's discriminant resolver resolveDiscrs (if it returns Ok(i), resolveDiscrs assigns variant i the discriminant 0) and complete when it returns Err(false), that is, when it saw no non-literal discriminant (then no resolved discriminant is 0); and for distinct representable discriminants (discrsWF), Ok(i) together with SemFromZeros fields of variant i implies that the enum description is SemFromZeros.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:929-930
theorem findZeroVariant_sound (ds : List DiscrSyn) (i : Nat) (h : findZeroVariant ds = .ok i) :
    (resolveDiscrs ds)[i]? = some 0

-- lean/ToyZc/Enum.lean:936-937
theorem findZeroVariant_complete_of_no_unknown (ds : List DiscrSyn)
    (h : findZeroVariant ds = .error false) : 0 ∉ resolveDiscrs ds

-- lean/ToyZc/Enum.lean:943-947
theorem enum_fromZeros_of_findZeroVariant (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true) (i : Nat)
    (hz : findZeroVariant (vs.map Prod.fst) = .ok i)
    (hF : ∀ fs, variantFields vs i = some fs → ∀ f ∈ fs, SemFromZeros f) :
    SemFromZeros (.enm r vs)
```
- **Unfolded reading** (key definitions expanded; prose):

```text
findZeroVariant ds = ok i → resolveDiscrs(ds)[i] = 0
findZeroVariant ds = error false → 0 ∉ resolveDiscrs(ds)
distinct representable discriminants → findZeroVariant = ok i → (∀ f ∈ fields_i, FromZeros f) → FromZeros E
```
- **Hypothesis ledger:**
  - `h (findZeroVariant ds = ok i)`: Premise of soundness (canonical counterexample: the search does not return variant 0 and variant 0 is not zero). Tightness: **tight: counterexample `Toy.Zc.ce_findZeroVariant_sound_drop_h`**.
  - `h (findZeroVariant ds = error false)`: Premise of completeness; with Err(true) (a non-literal discriminant was seen) a zero discriminant may exist. Tightness: **tight: counterexample `Toy.Zc.findZeroVariant_incomplete_with_unknown`**.
  - `hwf (enum_fromZeros_of_findZeroVariant)`: Distinct representable discriminants (one counterexample drops each half). Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromZeros_of_findZeroVariant_drop_wf`, `Toy.Zc.ce_enum_fromZeros_of_findZeroVariant_drop_representable`**.
  - `hz (enum_fromZeros_of_findZeroVariant)`: The search succeeds. Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromZeros_drop_findZero`**.
  - `hF (enum_fromZeros_of_findZeroVariant)`: Fields of the found variant are FromZeros. Tightness: **tight: counterexample `Toy.Zc.ce_enum_fromZeros_drop_fields`**.
- **Depth:** shallow.
- **Non-vacuity witness:** [= -2, implicit, implicit] (third variant is zero) and [= 1, implicit] (no zero) for the search; the i8 enum { A(bool) = 3, B = -1, C(u16) } with i = 2 for enum_fromZeros_of_findZeroVariant. (`Toy.Zc.nv_findZeroVariant`, `Toy.Zc.nv_enum_fromZeros_of_findZeroVariant`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/from_bytes.rs:14-90 (find_zero_variant and its comments), 125-176.
- **Design question:** Is the derive's syntactic zero-discriminant search sound, and what does it miss?
- **Non-claims:** see Boundaries, R3e.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B2, B8, B9. `findZeroVariant` transcribes `find_zero_variant` (`D/derive/from_bytes.rs:19-90`) branch by branch (source-fidelity table), and `resolveDiscrs` stands for the compiler's discriminant assignment (implicit = previous + 1, first = 0; B9). Read through these bridges, the soundness half of R3e says that when zerocopy-derive's `find_zero_variant` returns `Ok(i)`, the compiler resolves variant `i`'s discriminant to `0`, and the completeness half says that `Err(false)` means no variant has discriminant `0`. This reading is argued from the cited source, not proved.

### R3f-enum-tryFromBytes-validity-and-is-safe

- **Tier / kind / depth:** T1 / characterization / shallow. T1: the SAFETY comment of derive_is_safe (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:208-211) states this informally.
- **Plain claim:** In the model, on byte lists of the enum description's modeled size, the modeled validity validInit of an enum holds exactly when the tag read from the bytes equals the tag code of some variant's discriminant and the fields of the first such variant are valid (validInit) at their modeled offsets; and if the modeled is_safe (isSafe) agrees with validInit on every field description at that field's size and the discriminants are distinct and representable (discrsWF), the modeled enum isSafe (including its model of the could_be_from_bytes shortcut) equals validInit.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:960-964
theorem enum_validInit_iff_first_matching_variant_valid (r : EnumRepr)
    (vs : List (DiscrSyn × List Desc)) (bs : List Byte) (hlen : bs.length = (Desc.enm r vs).size) :
    validInit (.enm r vs) bs = true ↔
      ∃ i, (Desc.codes r vs).findIdx? (· == enumTag r vs bs) = some i ∧
        validVariant vs i (Desc.enumLayout r vs).variantFieldOffsets bs = true

-- lean/ToyZc/Enum.lean:971-975
theorem isSafe_enm_eq_validInit (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hwf : discrsWF r (vs.map Prod.fst) = true)
    (hfields : ∀ v ∈ vs, ∀ f ∈ v.2, ∀ bs, bs.length = f.size → isSafe f bs = validInit f bs)
    (bs : List Byte) (hlen : bs.length = (Desc.enm r vs).size) :
    isSafe (.enm r vs) bs = validInit (.enm r vs) bs
```
- **Unfolded reading** (key definitions expanded; prose):

```text
|bs| = size(E) → (validInit E bs ⟺ ∃ i, firstIndex(code = tag(bs)) = i ∧ ∀ k, validInit field_{i,k} (bs[off_{i,k} ..+ size]))
wf discriminants → (∀ fields, isSafe = validInit) → |bs| = size(E) → isSafe E bs = validInit E bs
```
- **Hypothesis ledger:**
  - `hlen (both theorems)`: The bytes have the enum's size (zerocopy only validates correctly sized candidates). Tightness: **tight: counterexample `Toy.Zc.ce_enum_validInit_drop_hlen`, `Toy.Zc.ce_isSafe_enm_drop_hlen`**.
  - `hwf (isSafe_enm_eq_validInit)`: Needed for the could_be_from_bytes shortcut. Tightness: **tight: counterexample `Toy.Zc.ce_isSafe_enm_drop_wf`**.
  - `hfields (isSafe_enm_eq_validInit)`: Inductive hypothesis on field types. Tightness: **tight: counterexample `Toy.Zc.ce_isSafe_enm_drop_fields`**.
- **Depth:** shallow.
- **Non-vacuity witness:** repr(u8) enum { A(u8), B(bool) = 5 } on [5, 1]: distinct representable discriminants, field validators agree with validity, correct length; evaluated also on [5, 2] and [4, 0]. (`Toy.Zc.nv_enum_validInit`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:121-227 (derive_is_safe; SAFETY comment 208-211), 315-346 (derive_try_from_bytes_enum, could_be_from_bytes at 322-329).
- **Design question:** Does the derived enum validator compute exactly enum validity, including its FromBytes-like shortcut?
- **Non-claims:** see Boundaries, R3f.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B4, B8, B9. The enum branch of `isSafe` transcribes `D/derive/try_from_bytes.rs:173-226, 327-336`: tag read, match against the variants' tag constants in declaration order, and the `could_be_from_bytes` shortcut.

### R3g-enum-intoBytes-padding-check-sound

- **Tier / kind / depth:** T1 / theorem / substantive. T1: informal in zerocopy/src/util/macro_util.rs:402-415.
- **Plain claim:** In the model, for an enum description with repr(C) or a primitive representation, if every field of every variant is SemIntoBytes and the modeled enum_padding! check enumPaddingOK passes (for every variant, the modeled enum size minus (tag size + sum of the variant's field sizes) is 0), then the enum is SemIntoBytes.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Enum.lean:1024-1026
theorem enum_intoBytes_of_fields_of_padding_check (r : EnumRepr) (vs : List (DiscrSyn × List Desc))
    (hF : ∀ v ∈ vs, ∀ f ∈ v.2, SemIntoBytes f) (hP : enumPaddingOK r vs = true) :
    SemIntoBytes (.enm r vs)
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ variant, ∀ field, IntoBytes field) → (∀ variant v, size(E) - (tagWidth + Σ_{f∈v} size f) = 0) → IntoBytes E
```
- **Hypothesis ledger:**
  - `hF`: Every field of every variant is IntoBytes (canonical counterexample: padding check passes, a field is not IntoBytes, the enum is not). Tightness: **tight: counterexample `Toy.Zc.ce_enum_intoBytes_drop_fields`**.
  - `hP`: The per-variant padding check. Tightness: **tight: counterexample `Toy.Zc.ce_enum_intoBytes_drop_padding`**.
- **Depth:** substantive.
- **Non-vacuity witness:** repr(u8) enum { A(u8), B(i8) }. (`Toy.Zc.nv_enum_intoBytes`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/into_bytes.rs:196-209; enum_padding! zerocopy/src/util/macro_util.rs:402-442; IntoBytes derive analysis for enums (zerocopy/src/lib.rs:5855-5859).
  - Rust Reference 1.81.0, Type layout (repr(C) and primitive representations of enums with fields).
  - Rust RFC 2195, 'Really Tagged Unions', https://rust-lang.github.io/rfcs/2195-really-tagged-unions.html (the tag-plus-variant-struct layouts the padding check reasons about).
- **Design question:** Is the per-variant size check a sound padding check for tagged enums?
- **Non-claims:** see Boundaries, R3g.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B8, B9. `enumPaddingOK` transcribes `PaddingCheck::Enum` (`D/derive/into_bytes.rs:205-208`; `enum_padding!`, `zerocopy/src/util/macro_util.rs:420-442`). Enum layouts follow RFC 2195.

### R4a-union-intoBytes-iff-full-size-fields

- **Tier / kind / depth:** T1 / characterization / shallow. T1: the assumption is stated in zerocopy issue 1792; made precise for an explicit union-value model, with the converse.
- **Plain claim:** In the model, where a union value is a value written through one field, a union description whose field descriptions are inhabited is SemIntoBytes iff every field is SemIntoBytes and every field's modeled size equals the union's modeled size.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Union.lean:107-109
theorem union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited (r : UnionRepr) (fs : List Desc)
    (hInh : ∀ f ∈ fs, f.Inhabited) :
    SemIntoBytes (.union r fs) ↔ ∀ f ∈ fs, SemIntoBytes f ∧ f.size = (Desc.union r fs).size
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ f ∈ fs, ∃ v, f.hasType v) →
  (∀ j, ∀ v : f_j, encode(union j v) = encode_{f_j}(v) ++ uninit^(size U - size f_j) has no uninit)
  ⟺ ∀ f ∈ fs, IntoBytes f ∧ size f = size U
```
- **Hypothesis ledger:**
  - `hInh`: Needed left to right: an uninhabited field can never be written (canonical counterexample: inhabitedness fails and the equivalence fails). Tightness: **tight: counterexample `Toy.Zc.ce_union_iff_drop_inhabited`**.
  - `(right side) every field IntoBytes`: Conjunct. Tightness: **tight: counterexample `Toy.Zc.ce_union_drop_fields_intoBytes`**.
  - `(right side) every field has the union's size`: Conjunct. Tightness: **tight: counterexample `Toy.Zc.ce_union_drop_full_size`**.
- **Depth:** shallow.
- **Non-vacuity witness:** #[repr(C)] union { a: u16, b: i16 }. (`Toy.Zc.nv_union_intoBytes`)
- **Prior art:**
  - zerocopy issue 1792, 'Restrict support for #[derive(IntoBytes)] on unions, work to guarantee forwards-compatible soundness', repository google/zerocopy, issue number 1792 (support 'is sound on the assumption that if every field of a union is IntoBytes and there is no extra padding before or after any field, then no bit-valid instance of that union can have uninitialized bytes').
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): union_padding! zerocopy/src/util/macro_util.rs:372-400.
  - Rust Unsafe Code Guidelines issue 533, 'Minimum guarantees for union construction and typed copies?', https://github.com/rust-lang/unsafe-code-guidelines/issues/533 (asks for typed copies of a union to preserve every byte position initialized in any valid value of any field).
- **Design question:** Under which union-value model is the union IntoBytes derive's size check sound and necessary?
- **Non-claims:** see Boundaries, R4a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B7, B9. R4a is about the written-through-a-field reading of union values (B7), one of the readings discussed in zerocopy issue 1792. Under permissive union validity, R4d applies instead.

### R4b-union-intoBytes-derive-sound

- **Tier / kind / depth:** T1 / theorem / shallow. T1: as R4a.
- **Plain claim:** In the model, where a union value is a value written through one field, if every field of a union description is SemIntoBytes and the modeled union_padding! check unionPaddingOK passes (for every field, the union's modeled size minus the field's size is 0), then the union is SemIntoBytes.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Union.lean:134-136
theorem union_intoBytes_of_fields_of_padding_check (r : UnionRepr) (fs : List Desc)
    (hF : ∀ f ∈ fs, SemIntoBytes f) (hP : unionPaddingOK r fs = true) :
    SemIntoBytes (.union r fs)
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(∀ f ∈ fs, IntoBytes f) → (∀ f ∈ fs, size U - size f = 0) → IntoBytes (union r fs)
```
- **Hypothesis ledger:**
  - `hF`: Every field IntoBytes (canonical counterexample: padding check passes, a field is not IntoBytes, the union is not). Tightness: **tight: counterexample `Toy.Zc.ce_union_drop_fields_intoBytes`**.
  - `hP`: The padding check union_padding! == 0 (canonical counterexample: IntoBytes fields, check fails, union not IntoBytes). Tightness: **tight: counterexample `Toy.Zc.ce_union_drop_full_size`**.
- **Depth:** shallow.
- **Non-vacuity witness:** #[repr(C)] union { a: u16, b: i16 } (accepted by the derive with the cfg set). (`Toy.Zc.nv_union_intoBytes`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/into_bytes.rs:211-259 (including the cfg gate at 220-233 and the comment 'Because we don't support generics, we don't need to worry about special-casing different reprs', 243-246).
- **Design question:** Is the union IntoBytes derive sound once union values are restricted to field writes?
- **Non-claims:** see Boundaries, R4b.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B7, B8. Under B7, R4b says that the union `IntoBytes` derive's conditions without the `cfg` gate (`D/derive/into_bytes.rs:211-259`, `union_padding!`) suffice. Whether Rust guarantees B7 is not settled (see Boundaries).

### R4c-union-u8-u16-counterexample

- **Tier / kind / depth:** T1 / counterexample / definitional. T1: the standard example of union padding; recorded concretely.
- **Plain claim:** In the model, the description union { a: u8, b: u16 } (repr(C)) holding the value 7 written through a encodes as [init 7, uninit]; both field descriptions are SemIntoBytes, but the union is not.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Union.lean:149-152
theorem union_u8_u16_written_through_u8_leaves_uninit :
    (Desc.union (.c .none) [.u8, .u16]).encodeL (.union 0 (.int [7])) = [.init 7, .uninit] ∧
    (∀ f ∈ [Desc.u8, Desc.u16], SemIntoBytes f) ∧
    ¬ SemIntoBytes (.union (.c .none) [.u8, .u16])
```
- **Unfolded reading** (key definitions expanded; prose):

```text
encode(union {a: u8, b: u16}, written through a with 7) = [init 7, uninit]
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** definitional.
- **Non-vacuity witness:** (counterexample; no non-vacuity witness needed) (`Toy.Zc.union_u8_u16_written_through_u8_leaves_uninit`)
- **Prior art:**
  - zerocopy issue 1792 (as in R4a).
- **Design question:** Reference point (the standard example of union padding, recorded concretely; it is also the tightness counterexample ce_union_drop_full_size of R4a/R4b): why does the union IntoBytes derive compare every field's size with the union's size?
- **Non-claims:** see Boundaries, R4c.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B7. A concrete instance of why `union_padding!` (`zerocopy/src/util/macro_util.rs:386-400`) is part of the derive.

### R4d-permissive-union-validity-of-size-pos-not-intoBytes

- **Tier / kind / depth:** T1 / impossibility / definitional. T1: the concern behind the cfg gate (zerocopy issue 1792; UCG issue 438) made precise; mathematically trivial.
- **Plain claim:** In the model's abstract-byte vocabulary, if a union's values were taken to be all abstract byte vectors of its size (the representation permissiveUnionRep, a validity that admits uninitialized bytes), then no union description of nonzero modeled size would satisfy IntoBytes, whatever its fields and whatever the modeled derive check says.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Union.lean:279-281
theorem permissive_union_validity_of_size_pos_not_intoBytes (r : UnionRepr) (fs : List Desc)
    (hn : 0 < (Desc.union r fs).size) :
    ¬ (permissiveUnionRep (Desc.union r fs).size).IntoBytes
```
- **Unfolded reading** (key definitions expanded; prose):

```text
0 < size U → ¬ IntoBytes ⟨encode := id, decode := some⟩ on Bytes Byte (size U)   (the value all-uninit is allowed)
```
- **Hypothesis ledger:**
  - `hn`: Nonzero size; a zero-size union is vacuously IntoBytes. Tightness: **tight: counterexample `Toy.Zc.ce_permissive_drop_size_pos`**.
- **Depth:** definitional.
- **Non-vacuity witness:** Any union of nonzero size, e.g. union { a: u16, b: i16 }. (`Toy.Zc.pc_written_union_intoBytes`)
- **Positive control:** `Toy.Zc.pc_written_union_intoBytes`
- **Prior art:**
  - MiniRust, spec/lang/representation.md, minirust/minirust commit 063d784186d3252bee242217f218223205c0b568, L313-343: a union 'simply stores the bytes directly'; its decode accepts every byte list of the right size (bytes outside chunks are dropped), with TODOs on padding (UCG 156) and validity (UCG 73) at L317-319.
  - Rust Unsafe Code Guidelines issue 438, 'What are the values of a union type? (in particular, what is the validity invariant of a union)', https://github.com/rust-lang/unsafe-code-guidelines/issues/438 (linked from zerocopy's derive docs).
  - Rust Unsafe Code Guidelines issue 533, 'Minimum guarantees for union construction and typed copies?', https://github.com/rust-lang/unsafe-code-guidelines/issues/533.
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): IntoBytes derive docs 'union bit validity is up in the air' (zerocopy/src/lib.rs:5805-5830).
  - Robbert Krebbers, 'The C Standard Formalized in Coq', PhD thesis, Radboud University Nijmegen, 2015, https://hdl.handle.net/2066/147182 (union values and indeterminate bytes in a mechanized C semantics).
  - zerocopy issue 1792 (google/zerocopy): short-term --cfg gate; long-term options 'Union validity' and 'Union safety'; the latter requires that 'It will never be safe to construct a union value other than from its fields or by overwriting one of its sub-fields' and that 'In a typed copy of a union value, any bytes previously written are preserved so long as those bytes are not written to a byte offset at which there is padding in all fields of the union'.
- **Design question:** What does the byte model explain about why union IntoBytes is gated behind --cfg zerocopy_derive_union_into_bytes?
- **Non-claims:** see Boundaries, R4d.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B3, B7. `permissiveUnionRep` models a union validity that admits every byte vector, as MiniRust at `063d784186d3252bee242217f218223205c0b568` does (`spec/lang/representation.md`). R4d explains why zerocopy gates the union `IntoBytes` derive behind `--cfg zerocopy_derive_union_into_bytes` (`D/derive/into_bytes.rs:220-233`): under that validity no nonzero-size union can satisfy the contract.

### R5a-transmute-total-of-intoBytes-of-fromBytes

- **Tier / kind / depth:** T0 / theorem / definitional. T0: a one-step consequence of the definitions of IntoBytes, FromBytes and transmute (the proof is the term fun a => hB (ra.encode a) (hA a)).
- **Plain claim:** In the model's abstract-byte vocabulary, for representations ra and rb over the same carrier of n abstract bytes, if no encoding of A contains uninit (ra.IntoBytes) and every fully initialized byte vector decodes as some B (rb.FromBytes), then decoding with rb after encoding with ra never fails (TransmuteTotal ra rb).
- **Lean statement(s):**

```lean
-- lean/ToyZc/Transmute.lean:33-35
theorem transmuteTotal_of_intoBytes_of_fromBytes {D A B : Type} {n : Nat}
    (ra : Rep (Bytes D n) A) (rb : Rep (Bytes D n) B)
    (hA : ra.IntoBytes) (hB : rb.FromBytes) : TransmuteTotal ra rb
```
- **Unfolded reading** (key definitions expanded):

```lean
ra.IntoBytes → rb.FromBytes → ∀ a, ∃ b, rb.decode (ra.encode a) = some b
```
- **Hypothesis ledger:**
  - `hA`: IntoBytes of the source. Tightness: **tight: counterexample `Toy.Zc.ce_transmuteTotal_drop_intoBytes`**.
  - `hB`: FromBytes of the destination. Tightness: **tight: counterexample `Toy.Zc.ce_transmuteTotal_drop_fromBytes`**.
- **Depth:** definitional.
- **Non-vacuity witness:** u16 to i16 in the Desc.rep representations. (`Toy.Zc.nv_transmuteTotal_rep`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): transmute! bounds Src: IntoBytes, Dst: FromBytes, size_of::<Src>() == size_of::<Dst>() (zerocopy/src/macros.rs:15-28).
  - Rust RFC 2835, 'Project Safe Transmute' (project-group RFC, start date 2019-12-06), https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html.
- **Design question:** What is the semantic content of transmute!'s trait bounds?
- **Non-claims:** see Boundaries, R5a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B3. R5a is the representation-level reason why a by-value transmute from an `IntoBytes` type to a `FromBytes` type of the same size cannot produce an invalid value (`transmute!`, `zerocopy/src/macros.rs:15-28`).

### R5b-desc-transmute-total-size-ge

- **Tier / kind / depth:** T1 / theorem / shallow. T1: the size relation of zerocopy's union-based transmute!(#![allow(shrink)] ...) made precise over descriptions as the uniform sufficient condition (with its necessity for the uniform statement); TransmuteFrom's more permissive per-pair rule (extension into trailing padding) is recorded as a boundary, not mechanized here.
- **Plain claim:** In the model, for descriptions Src and Dst, if Src is SemIntoBytes, Dst is SemFromBytes and Dst's modeled size is at most Src's, then the modeled union-transmute transmuteVal, which decodes Dst from the first size(Dst) bytes of the encoding of a well-typed Src value, succeeds for every such value; the corollary desc_transmute_total_of_size_eq is the equal-size case.
- **Lean statement(s):**

```lean
-- lean/ToyZc/Transmute.lean:52-54
theorem desc_transmute_total_of_size_ge (s d : Desc) (hsz : d.size ≤ s.size)
    (hI : SemIntoBytes s) (hF : SemFromBytes d) :
    ∀ v, s.hasType v = true → (transmuteVal s d v).isSome = true

-- lean/ToyZc/Transmute.lean:77-79
theorem desc_transmute_total_of_size_eq (s d : Desc) (hsz : s.size = d.size)
    (hI : SemIntoBytes s) (hF : SemFromBytes d) :
    ∀ v, s.hasType v = true → (transmuteVal s d v).isSome = true
```
- **Unfolded reading** (key definitions expanded; prose):

```text
size Dst ≤ size Src → IntoBytes Src → FromBytes Dst →
  ∀ v : Src, (decode_Dst (first size(Dst) bytes of encode_Src v, padded with uninit)).isSome
(corollary desc_transmute_total_of_size_eq: the case size Src = size Dst)
```
- **Hypothesis ledger:**
  - `hsz`: size Dst <= size Src; without it the uniform statement over all FromBytes destinations fails (u8 -> u16 reads an uninit byte). It is not necessary for every fixed pair: a destination whose extra bytes are trailing padding can be larger (transmute_extend_into_trailing_padding_example). Tightness: **tight: counterexample `Toy.Zc.ce_transmute_drop_size`**.
  - `hI`: IntoBytes Src. Tightness: **tight: counterexample `Toy.Zc.ce_transmute_drop_intoBytes`**.
  - `hF`: FromBytes Dst. Tightness: **tight: counterexample `Toy.Zc.ce_transmute_drop_fromBytes`**.
- **Depth:** shallow.
- **Non-vacuity witness:** u16 to i16 (equal sizes) and u32 to u16 (shrinking). (`Toy.Zc.nv_desc_transmute`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): transmute! bounds Src: IntoBytes, Dst: FromBytes, size_of::<Src>() == size_of::<Dst>() (zerocopy/src/macros.rs:15-28); with #![allow(shrink)], size_of::<Src>() >= size_of::<Dst>() is accepted (zerocopy/src/macros.rs:40-49), implemented by transmuting Src into a #[repr(C, packed)] union { src, dst } and reading dst (zerocopy/src/macros.rs:106-110, 124-129); the comment at 142-146 explains that this forces size_of::<Src>() >= size_of::<Dst>().
  - core::mem::TransmuteFrom (unstable, tracking issue rust-lang/rust#99571), library/core/src/mem/transmutability.rs at rust-lang/rust commit 6905905bb7727fd0f9223f5fdc9ad4e62236d5a2: soundness is defined by a union-transmute (L14-38), and 'union-transmutes permit conversions that extend the bits of Src with trailing padding to fill trailing uninitialized bytes of Self' (L41-44), with the example u8 to #[repr(C, align(2))] struct Dst(u8) (L46-58). TransmuteFrom therefore also allows size_of::<Src>() < size_of::<Dst>() when the extra destination bytes are padding; the compiler's check is in compiler/rustc_transmute (maybe_transmutable/mod.rs at the same commit, 'extension: size_of(Src) <= size_of(Dst)', L187).
  - Rust RFC 2835, 'Project Safe Transmute' (project-group RFC, start date 2019-12-06), https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html.
- **Design question:** Which size relation does a safe by-value transmute between IntoBytes and FromBytes types need?
- **Non-claims:** see Boundaries, R5b.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B3, B10. `transmuteVal` models the `#[repr(C, packed)]` union transmute that `transmute!(#![allow(shrink)] ...)` uses (`zerocopy/src/macros.rs:106-157`): the destination reads the first `size_of::<Dst>()` bytes of the source. The equal-size form `transmute!(...)` is a plain `core::mem::transmute` (`zerocopy/src/macros.rs:161-192`, call at line 188), which coincides with this union transmute when the two sizes are equal, so `desc_transmute_total_of_size_eq` is the model of plain `transmute!`. These correspondences are argued from the cited source, not proved.

### R6a-validate-cast-returns-max-fitting-elems

- **Tier / kind / depth:** T2 / theorem / substantive. T2: zerocopy's Kani harnesses establish the components of this property bit-precisely for the target's usize, power-of-two alignments, and components bounded by isize::MAX, phrased against max_trailing_bytes; this states the end-to-end characterization ('largest fitting count, error iff none fits') directly against an explicit maximality predicate, over unbounded naturals (all pointer widths) and for any positive rounding alignment, with independent minimal hypotheses.
- **Plain claim:** In the model, for a trailing-slice layout (TrailingSliceLayout) with positive size-rounding alignment, phase at most that alignment, and positive element size, when the alignment check passes, vccm (the model of validate_cast_and_convert_metadata) returns Ok((elems, split_at)) with elems the largest element count whose object size fits in bytes_len and split_at the prefix/suffix split for that size, and returns Err(Size) exactly when no element count fits.
- **Lean statement(s):**

```lean
-- lean/ToyZc/KnownLayout.lean:234-241
theorem vccm_sliceDst_returns_max_fitting_elems (align addr bytesLen : Nat) (ct : CastType)
    (t : TrailingSliceLayout) (hA : 0 < t.sizeAlign) (hP : t.sizePhase ≤ t.sizeAlign)
    (hE : 0 < t.elemSize) (hAl : (addr + castOffset ct bytesLen) % align = 0) :
    match vccm ⟨align, .sliceDst t⟩ addr bytesLen ct with
    | .ok elems splitAt =>
        t.IsMaxFit bytesLen elems ∧ splitAt = splitFor ct bytesLen (t.sizeForElems elems)
    | .sizeErr => ∀ n, bytesLen < t.sizeForElems n
    | _ => False
```
- **Unfolded reading** (key definitions expanded; prose):

```text
size(n) := base + alignUp(phase + n·elem, A);  0 < A → phase ≤ A → 0 < elem → aligned endpoint →
  vccm = ok(e, s) → size(e) ≤ len ∧ (∀ k, size(k) ≤ len → k ≤ e) ∧ s = split(size(e))
  vccm = sizeErr → ∀ n, len < size(n);   no other outcome
```
- **Hypothesis ledger:**
  - `hA`: 0 < size_align (NonZeroUsize in the source). Canonical counterexample: alignment 0 with phase 0 (so hP holds) returns a count that is not the largest. Tightness: **tight: counterexample `Toy.Zc.ce_vccm_drop_align_pos`**.
  - `hP`: phase <= size_align (zerocopy's RoundingAlignAndPhase::new asserts the stronger phase < align, zerocopy/src/layout.rs:72-96; the statement also holds at phase = align). Independent of hA. Tightness: **tight: counterexample `Toy.Zc.ce_vccm_drop_phase_lt`**.
  - `hE`: Nonzero element size (the source panics otherwise). Tightness: **tight: counterexample `Toy.Zc.ce_vccm_drop_elem_pos`**.
  - `hAl`: The alignment check passes. Tightness: **tight: counterexample `Toy.Zc.ce_vccm_drop_aligned`**.
- **Depth:** substantive.
- **Non-vacuity witness:** size_base 4, size_align 4, phase 3, element size 1, bytes_len 14 (prefix): Ok((5, 12)). (`Toy.Zc.nv_vccm_sliceDst`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/src/layout.rs:1546-1797 (documentation, guarantees 1572-1591, Kani contract harness, implementation); max_trailing_bytes zerocopy/src/layout.rs:236-341.
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): standalone Kani proof harnesses zerocopy/src/layout.rs:4258-4630, several pinned to the kissat SAT solver: prove_max_trailing_bytes (4436-4449), prove_max_trailing_bytes_components (4451-4468), prove_slice_dst_validator_selected_size_fits (4470-4514), prove_slice_dst_validator_rejects_larger_trailing_size (4516-4531), prove_slice_formula_contains_trailing_slice (4533-4551). They quantify over all target-width usize values subject to stated assumptions, with trailing-layout components at most DstLayout::MAX_SIZE = isize::MAX and power-of-two rounding alignments (any_bounded_trailing_layout, 4224-4254; any_layout_align, 4149-4160). This is the closest prior verification of this function.
- **Design question:** Does the slice-DST metadata computation return the largest fitting element count and fail exactly when none fits?
- **Non-claims:** see Boundaries, R6a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B6. `vccm` transcribes `validate_cast_and_convert_metadata` (`zerocopy/src/layout.rs:1650-1797`), replacing the bit-mask rounding by `roundDown` and the disjoint-bit OR by `+` (source-fidelity table). zerocopy's Kani harnesses (`zerocopy/src/layout.rs:4233-4630`) check related properties for bounded power-of-two layouts. R6a holds for all natural numbers, with any positive rounding alignment.

### R6d-validate-cast-start-aligned-of-align-dvd

- **Tier / kind / depth:** T2 / theorem / shallow. T2: zerocopy's Kani harnesses check the two steps separately for power-of-two alignments over usize; this states the composed guarantee for the modeled validation over unbounded naturals with divisibility hypotheses instead of power-of-two alignments, and isolates exactly which layout invariants it needs.
- **Plain claim:** In the model, if the layout alignment divides the size base and the size-rounding alignment of a trailing-slice layout (so every object size is a multiple of it), then whenever vccm (the model of validate_cast_and_convert_metadata) returns Ok((elems, split_at)), the object starts at an aligned address: addr for a prefix cast, addr + split_at for a suffix cast.
- **Lean statement(s):**

```lean
-- lean/ToyZc/KnownLayout.lean:345-348
theorem vccm_sliceDst_start_aligned_of_align_dvd (align addr bytesLen : Nat) (ct : CastType)
    (t : TrailingSliceLayout) (hdB : align ∣ t.sizeBase) (hdA : align ∣ t.sizeAlign)
    (elems splitAt : Nat) (hok : vccm ⟨align, .sliceDst t⟩ addr bytesLen ct = .ok elems splitAt) :
    (addr + startOffset ct splitAt) % align = 0
```
- **Unfolded reading** (key definitions expanded; prose):

```text
align ∣ base → align ∣ A → vccm ⟨align, sliceDst t⟩ addr len ct = ok(e, s) →
  prefix: addr ≡ 0 (mod align);   suffix: addr + s ≡ 0 (mod align)
(x % 0 = x in Lean, so align = 0 forces base = A = 0 and the statement still holds)
```
- **Hypothesis ledger:**
  - `hdB`: align divides size_base (part of the completed-layout premise of zerocopy/src/layout.rs:1574-1591). Tightness: **tight: counterexample `Toy.Zc.ce_vccm_start_drop_dvd_base`**.
  - `hdA`: align divides size_align (the other part; with size_base, it makes every object size a multiple of align). Tightness: **tight: counterexample `Toy.Zc.ce_vccm_start_drop_dvd_align`**.
  - `hok`: The validation succeeded with exactly these elems and split_at (the conclusion is about the returned split). Tightness: **tight: counterexample `Toy.Zc.ce_vccm_start_drop_ok`**.
- **Depth:** shallow.
- **Non-vacuity witness:** The flat DST #[repr(C)] struct { a: u16, b: u8, t: [u8] } normalized (base 2, rounding alignment 2, phase 1) with layout alignment 2, suffix cast of 9 bytes at address 1: Ok((5, 1)), object start 2. (`Toy.Zc.nv_vccm_start_aligned`, `Toy.Zc.normalizeDst_align_dvd`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): guarantee 'If this is a suffix cast: ... addr + split_at satisfies self's alignment' and 'suffix alignment relies on every object size being a multiple of the type's alignment' (zerocopy/src/layout.rs:1584-1591); Kani harnesses prove_finalized_slice_formula_is_aligned (4553-4568: size_base aligned and rounding alignment at least the outer alignment imply aligned object sizes) and prove_aligned_suffix_end_and_size_imply_aligned_start (4610-4630), for power-of-two alignments over usize.
- **Design question:** What layout invariant makes a successful suffix cast start at an aligned address, and is it independent of the element-count characterization?
- **Non-claims:** see Boundaries, R6d.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B6. The divisibility hypotheses state zerocopy's completed-layout condition (`zerocopy/src/layout.rs:1546-1591`): every object size is a multiple of the layout alignment.

### R6b-normalized-layout-size-equals-closed-form

- **Tier / kind / depth:** T1 / theorem / shallow. T1: the normalization identity is argued in comments (zerocopy/src/layout.rs:1376-1431) and checked by a Kani harness for power-of-two alignments over usize (4316-4349); made precise for flat repr(C) DSTs over unbounded naturals.
- **Plain claim:** In the model, for a flat repr(C) slice DST description d (SliceDstSpec), the normalized trailing-slice layout normalizeDst d (base T - T mod A, size-rounding alignment A, phase T mod A, where T = dstTailOffset d is the trailing offset and A = dstAlign d the alignment) has object size dstSize d n, the closed-form repr(C) size, for every element count n.
- **Lean statement(s):**

```lean
-- lean/ToyZc/KnownLayout.lean:406-407
theorem normalizeDst_sizeForElems_eq_dstSize (d : SliceDstSpec) (n : Nat) :
    (normalizeDst d).sizeForElems n = dstSize d n
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(T - T mod A) + alignUp(T mod A + n·e, A) = alignUp(T + n·e, A)   (T = dstTailOffset d, A = dstAlign d, e = elem size)
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** shallow.
- **Non-vacuity witness:** #[repr(C)] struct { a: u16, b: u8, t: [u8] } with 3 elements. (`Toy.Zc.nv_normalizeDst`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): TrailingSliceLayout size formula zerocopy/src/layout.rs:190-194; pad_to_align zerocopy/src/layout.rs:1350-1440.
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): Kani harness prove_trailing_slice_layout_normal_form (zerocopy/src/layout.rs:4316-4349, enabled under cfg(kani_slow)): checks that a layout with base (offset - phase) | prefix and phase offset mod align has the padded size offset + trailing + padding, the same normal-form identity, for power-of-two alignments over usize.
- **Design question:** Does zerocopy's normalized size formula agree with the closed-form repr(C) DST size?
- **Non-claims:** see Boundaries, R6b.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B6, B9. `normalizeDst` is the trailing-slice layout of a flat `repr(C)` slice DST in zerocopy's normalized form (`zerocopy/src/layout.rs:153-207`); `dstSize` follows the Rust Reference `repr(C)` rules.

### R6c-validate-cast-agrees-with-closed-form-max

- **Tier / kind / depth:** T1 / theorem / shallow. T1: agreement of two models of the same computation.
- **Plain claim:** In the model, for a flat repr(C) slice DST description d, any layout alignment, and either cast type, when the alignment check passes, the element count returned by vccm (the modeled validation) on normalizeDst d equals maxSliceElems d bytes_len (the largest fitting count, or none).
- **Lean statement(s):**

```lean
-- lean/ToyZc/KnownLayout.lean:426-429
theorem vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned (d : SliceDstSpec)
    (align addr bytesLen : Nat) (ct : CastType)
    (hAl : (addr + castOffset ct bytesLen) % align = 0) :
    (vccm ⟨align, .sliceDst (normalizeDst d)⟩ addr bytesLen ct).elems? = maxSliceElems d bytesLen
```
- **Unfolded reading** (key definitions expanded; prose):

```text
(addr + castOffset ct len) % align = 0 → elems(vccm ⟨align, sliceDst (normalizeDst d)⟩ addr len ct) = maxSliceElems d len
(any align, either cast type; zero-sized element: both sides none)
```
- **Hypothesis ledger:**
  - `hAl`: The alignment check passes (canonical counterexample: misaligned address, counts differ). Tightness: **tight: counterexample `Toy.Zc.ce_vccm_normalizeDst_drop_aligned`**.
- **Depth:** shallow.
- **Non-vacuity witness:** #[repr(C)] struct { a: u16, b: u8, t: [u8] } with bytes_len 9: both give 5. (`Toy.Zc.nv_vccm_normalizeDst`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/src/layout.rs:1650-1797.
- **Design question:** Do the two models of prefix- and suffix-cast element counts agree?
- **Non-claims:** see Boundaries, R6c.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B6, B9. As for R6a and R6b. Only the element count is compared; the layout alignment `align` is a free parameter, as in zerocopy's `DstLayout`.

### R7a-immutable-not-byte-determined

- **Tier / kind / depth:** T1 / impossibility / definitional. T1: folklore that interior mutability is not a byte property; made precise as non-definability.
- **Plain claim:** In the model, no property of descriptions that is ByteDetermined (depends only on the modeled layout, typing, encoder and decoder) coincides with implImmutable, the model of zerocopy's Immutable derive and impls: the descriptions UnsafeCell<u8> and u8 have the same modeled byte semantics but differ in implImmutable.
- **Lean statement(s):**

```lean
-- lean/ToyZc/NonClaims.lean:67-68
theorem immutable_not_byte_determined :
    ¬ ∃ P : Desc → Prop, ByteDetermined P ∧ ∀ d, P d ↔ implImmutable d = true
```
- **Unfolded reading** (key definitions expanded; prose):

```text
¬ ∃ P, (∀ d₁ d₂, same layout, typing, encoder, decoder → (P d₁ ↔ P d₂)) ∧ ∀ d, P d ↔ implImmutable d
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** definitional.
- **Non-vacuity witness:** UnsafeCell<u8> and u8. (`Toy.Zc.nv_immutable_witness`)
- **Positive control:** `Toy.Zc.pc_fromBytes_byte_determined`
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): Immutable internal safety 'given t: &T, t does not permit interior mutation of its referent' (zerocopy/src/lib.rs:1640-1646); UnsafeCell<T> has the same in-memory representation as T (zerocopy/src/impls.rs:842-848) and implements FromZeros, FromBytes, IntoBytes, Unaligned (zerocopy/src/impls.rs:839-850) and TryFromBytes (853-868), but not Immutable.
  - Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer, 'RustBelt: Securing the Foundations of the Rust Programming Language', PACMPL 2(POPL), 2018, DOI 10.1145/3158154; Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer, 'RefinedRust: A Type System for High-Assurance Verification of Rust Programs', PACMPL 8(PLDI), 2024, DOI 10.1145/3656422: Coq/Iris semantic models in which shared references to UnsafeCell-containing types are interpreted differently from plain data (interior mutability is not a property of the bytes).
- **Design question:** Which zerocopy traits are outside the reach of a byte-representation model?
- **Non-claims:** see Boundaries, R7a.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B8. `implImmutable` transcribes the `Immutable` derive (`zerocopy/zerocopy-derive/src/derive/mod.rs:19-31`) and the primitive impls (`UnsafeCell<T>` has no `Immutable` impl, `zerocopy/src/impls.rs:839-868`).

### R7b-union-derives-require-more-than-needed

- **Tier / kind / depth:** T1 / counterexample / definitional. T1: model-relative observation. zerocopy Discussion 696 discusses the all-fields bounds for union FromZeros/TryFromBytes (motivated by TryFromBytes being a supertrait of FromZeros); it does not state that one FromBytes field suffices under the 'some field is valid' validity.
- **Plain claim:** In the model, the union description union { a: u8, b: bool } is SemFromBytes and union { a: u8, b: E } (E = Desc.noZero, a fieldless repr(u8) enum without a zero discriminant) is SemFromZeros, yet the modeled derive checks implFromBytes and implFromZeros reject them, because they require every field to have the trait.
- **Lean statement(s):**

```lean
-- lean/ToyZc/NonClaims.lean:93-95
theorem union_fromBytes_derive_not_necessary :
    SemFromBytes (.union (.c .none) [.u8, .bool]) ∧
    implFromBytes (.union (.c .none) [.u8, .bool]) = false

-- lean/ToyZc/NonClaims.lean:104-106
theorem union_fromZeros_derive_not_necessary :
    SemFromZeros (.union (.c .none) [.u8, Desc.noZero]) ∧
    implFromZeros (.union (.c .none) [.u8, Desc.noZero]) = false
```
- **Unfolded reading** (key definitions expanded; prose):

```text
FromBytes (union {u8, bool}) ∧ ¬ implFromBytes (union {u8, bool});  FromZeros (union {u8, E}) ∧ ¬ implFromZeros (union {u8, E})
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** definitional.
- **Non-vacuity witness:** (counterexample) (`Toy.Zc.union_fromBytes_derive_not_necessary`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/from_bytes.rs:177-180, 201-204; union validity comment zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:292-296.
  - google/zerocopy Discussion 696, 'Whether/how to support TryFromBytes on unions?' (repository google/zerocopy; linked from zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:296): 'A union is FromZeros if all of its variants are FromZeros. Consequently, a union is TryFromBytes if all of its variants are TryFromBytes.'
- **Design question:** Are the union FromBytes/FromZeros derives' all-fields bounds necessary?
- **Non-claims:** see Boundaries, R7b.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B1, B2, B8. The modeled union `FromBytes`/`FromZeros` checks require every field to have the trait (`D/derive/from_bytes.rs:177-180, 201-204`). zerocopy Discussion 696 records why.

### R7c-unaligned-check-conjuncts-necessary

- **Tier / kind / depth:** T1 / counterexample / definitional. T1: concrete necessity witnesses for the documented conditions (zerocopy/zerocopy-derive/src/derive/unaligned.rs:19-23, 42-44, 59-63).
- **Plain claim:** In the model, each conjunct of the modeled Unaligned derive check implUnaligned is necessary: for each conjunct of its checks for repr(C) structs (no align(N>1); repr(packed) or all fields Unaligned), repr(transparent) structs (all fields Unaligned), enums (repr(u8)/repr(i8), shown for repr(u16) and repr(C); all fields Unaligned), and repr(C) unions (no align(N>1); repr(packed) or all fields Unaligned), there is a description (the witnesses in the Lean statement) that satisfies every other conjunct of its check, fails that one, is rejected, and has modeled alignment ≠ 1.
- **Lean statement(s):**

```lean
-- lean/ToyZc/NonClaims.lean:125-161
theorem unaligned_check_conjuncts_necessary :
    -- 1
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.strct (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.strct (.c (.aligned 2)) [.u8])) ∧
    -- 2
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.strct (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.strct (.c .none) [.u8, .u16])) ∧
    -- 3
    (allUnaligned [.u16] = false ∧
      implUnaligned (.strct .transparent [.u16]) = false ∧
      ¬ SemUnaligned (.strct .transparent [.u16])) ∧
    -- 4
    (variantsUnaligned [(.implicit, [])] = true ∧
      EnumRepr.prim .u16 ≠ .prim .u8 ∧ EnumRepr.prim .u16 ≠ .prim .i8 ∧
      implUnaligned (.enm (.prim .u16) [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u16) [(.implicit, [])]) ∧
      EnumRepr.c ≠ .prim .u8 ∧ EnumRepr.c ≠ .prim .i8 ∧
      implUnaligned (.enm .c [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm .c [(.implicit, [])])) ∧
    -- 5
    (variantsUnaligned [(.implicit, [.u16])] = false ∧
      implUnaligned (.enm (.prim .u8) [(.implicit, [.u16])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u8) [(.implicit, [.u16])])) ∧
    -- 6
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.union (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.union (.c (.aligned 2)) [.u8])) ∧
    -- 7
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.union (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.union (.c .none) [.u8, .u16]))
```
- **Unfolded reading** (key definitions expanded; prose):

```text
for each conjunct c of implUnaligned's struct (repr(C): !align>1, packed1 ∨ all fields; repr(transparent): all fields),
enum (repr u8/i8; all fields) and union (!align>1, packed1 ∨ all fields) checks:
  ∃ d, every other conjunct of d's check holds ∧ ¬ c ∧ implUnaligned d = false ∧ align(d) ≠ 1
```
- **Hypothesis ledger:** no hypotheses.
- **Depth:** definitional.
- **Non-vacuity witness:** (counterexample) (`Toy.Zc.unaligned_check_conjuncts_necessary`)
- **Prior art:**
  - zerocopy v0.8.63 (google/zerocopy, commit c55af491426ef53f35fb8c6e83f220fa07712e66): zerocopy/zerocopy-derive/src/derive/unaligned.rs:19-40 (structs: unaligned_validate_no_align_gt_1 at 26, is_packed_1 or repr(C)/repr(transparent) with all fields at 28-37), 42-57 (enums: 47, 49), 59-80 (unions: 66, 68-77); zerocopy/zerocopy-derive/src/repr.rs:148-150 (is_align_gt_1), 152-165 (unaligned_validate_no_align_gt_1), 169-171 (is_packed_1); Unaligned contract zerocopy/src/lib.rs:6507.
- **Design question:** Is every conjunct of the Unaligned derive needed?
- **Non-claims:** see Boundaries, R7c.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge): via B5, B8, B9. `implUnaligned` transcribes `D/derive/unaligned.rs:19-80` and `D/repr.rs:148-172`. Alignments follow the Rust Reference.

### Proved observations behind "stronger than needed" and "incomplete" remarks

Each remark in this report that a modeled check is incomplete, stronger than needed, or would be unsound without a compiler rule is backed by one of the following kernel-checked theorems about the model. Each theorem is about the model only; transferring such a remark to the real zerocopy-derive goes through the modeling bridge B8 and is argued, not proved.

* `Toy.Zc.findZeroVariant_incomplete_with_unknown` (R3e, R2e): In the model, `findZeroVariant` (the model of `find_zero_variant`) returns `Err(true)` for a single variant whose discriminant is a non-literal expression evaluating to `0` (`.other 0`); the `repr(u8)` enum description is `SemFromZeros`, but `implFromZeros` rejects it.
* `Toy.Zc.findZeroVariant_incomplete_nonliteral_before_implicit` (R3e, R2e): In the model, for a non-literal discriminant (`.other (-1)`) followed by an implicit one that resolves to `0`, `findZeroVariant` returns `Err(true)`; the `repr(i8)` enum description is `SemFromZeros`, but `implFromZeros` rejects it.
* `Toy.Zc.fromBytes_enum_rejected_by_findZeroVariant` (R3c): In the model, `implFromBytes` includes `implFromZeros`, and hence `findZeroVariant`, so it rejects the well-formed 256-variant `repr(u8)` enum description `nonLiteralZeroFullU8`, which passes `enumVariantCountOK` and is `SemFromBytes` and `SemFromZeros` but whose zero discriminant is non-literal.
* `Toy.Zc.union_fromBytes_derive_not_necessary` (R7b, R2e): In the model, `union { a: u8, b: bool }` is `SemFromBytes` although not every field is (`bool` is not); `implFromBytes` rejects it.
* `Toy.Zc.union_fromZeros_derive_not_necessary` (R7b): In the model, `union { a: u8, b: E }` (`E = Desc.noZero`) is `SemFromZeros` although not every field is (`E` is not); `implFromZeros` rejects it.
* `Toy.Zc.union_gate_rejects_intoBytes_union` (R4b): In the model, with the union `cfg` unset (`cfgDefault`), `implIntoBytes` rejects `union { a: u16, b: i16 }`, which is `SemIntoBytes` under the written-through-one-field value model.
* `Toy.Zc.transmute_shrink_example` (R5b): In the model, `transmuteVal` from `u32` to `u16` keeps the two low-address bytes (shown for one value). That this shrinking pair transmutes every value follows from R5b, whose hypotheses it satisfies (`nv_desc_transmute`), so equal sizes are not needed.
* `Toy.Zc.transmute_extend_into_trailing_padding_example` (R5b): In the model, `transmuteVal` from `u8` (size 1) to `Desc.alignedByte` (size 2) succeeds on every well-typed value, because the destination's extra byte is trailing padding that the decoder never reads; so `size Dst ≤ size Src` is not needed for this fixed pair.
* `Toy.Zc.unaligned_check_conjuncts_necessary` (R7c): In the model, every conjunct of the modeled `Unaligned` check `implUnaligned` is necessary: for each conjunct there is a description that satisfies every other conjunct of its check, fails that one, is rejected, and has modeled alignment ≠ 1.
* `Toy.Zc.ce_enum_fromZeros_of_findZeroVariant_drop_wf` (R3e): In the model, the enum description over `dupZeroNonLiteral` satisfies every hypothesis of `enum_fromZeros_of_findZeroVariant` except `discrsWF` (`findZeroVariant` returns `Ok(1)` and variant 1 has no fields), yet it is not `SemFromZeros`. `discrsWF` stands for the compiler's duplicate-discriminant rule E0081 (bridge B9).
* `Toy.Zc.union_decode_encode_forgets_bytes` (R1, R2f): In the model, on unions the decoder is not a left inverse of the encoder.
* `Toy.Zc.union_decode_not_monotone` (R1, R2f): In the model, on unions the decoder is not monotone in definedness.
* `Toy.Zc.vccm_normalizeDst_zst_both_none` (R6c): In the model, for a zero-sized trailing element `vccm` panics and `maxSliceElems` returns `none`, so both sides of R6c are `none`, although every element count fits.

```lean
-- lean/ToyZc/Enum.lean:1464-1468
theorem findZeroVariant_incomplete_with_unknown :
    findZeroVariant [.other 0] = .error true ∧ findZeroVariant [.other 0] ≠ .error false ∧
    0 ∈ resolveDiscrs [.other 0] ∧
    implFromZeros (.enm (.prim .u8) [(.other 0, [])]) = false ∧
    SemFromZeros (.enm (.prim .u8) [(.other 0, [])])

-- lean/ToyZc/Enum.lean:1481-1485
theorem findZeroVariant_incomplete_nonliteral_before_implicit :
    findZeroVariant [.other (-1), .implicit] = .error true ∧
    resolveDiscrs [.other (-1), .implicit] = [-1, 0] ∧
    implFromZeros (.enm (.prim .i8) [(.other (-1), []), (.implicit, [])]) = false ∧
    SemFromZeros (.enm (.prim .i8) [(.other (-1), []), (.implicit, [])])

-- lean/ToyZc/Enum.lean:1592-1598
theorem fromBytes_enum_rejected_by_findZeroVariant :
    (Desc.enm (.prim .u8) nonLiteralZeroFullU8).wf = true ∧
    enumVariantCountOK (.prim .u8) nonLiteralZeroFullU8 = true ∧
    findZeroVariant (nonLiteralZeroFullU8.map Prod.fst) = .error true ∧
    SemFromBytes (.enm (.prim .u8) nonLiteralZeroFullU8) ∧
    SemFromZeros (.enm (.prim .u8) nonLiteralZeroFullU8) ∧
    implFromBytes (.enm (.prim .u8) nonLiteralZeroFullU8) = false

-- lean/ToyZc/NonClaims.lean:93-95
theorem union_fromBytes_derive_not_necessary :
    SemFromBytes (.union (.c .none) [.u8, .bool]) ∧
    implFromBytes (.union (.c .none) [.u8, .bool]) = false

-- lean/ToyZc/NonClaims.lean:104-106
theorem union_fromZeros_derive_not_necessary :
    SemFromZeros (.union (.c .none) [.u8, Desc.noZero]) ∧
    implFromZeros (.union (.c .none) [.u8, Desc.noZero]) = false

-- lean/ToyZc/Union.lean:311-313
theorem union_gate_rejects_intoBytes_union :
    implIntoBytes cfgDefault (.union (.c .none) [.u16, .int .i16]) = false ∧
    SemIntoBytes (.union (.c .none) [.u16, .int .i16])

-- lean/ToyZc/Transmute.lean:97-98
theorem transmute_shrink_example :
    transmuteVal .u32 .u16 (.int [1, 2, 3, 4]) = some (.int [1, 2])

-- lean/ToyZc/Transmute.lean:105-107
theorem transmute_extend_into_trailing_padding_example :
    Desc.u8.size < Desc.alignedByte.size ∧ SemIntoBytes .u8 ∧
    ∀ v, Desc.u8.hasType v = true → (transmuteVal .u8 Desc.alignedByte v).isSome = true

-- lean/ToyZc/NonClaims.lean:125-161
theorem unaligned_check_conjuncts_necessary :
    -- 1
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.strct (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.strct (.c (.aligned 2)) [.u8])) ∧
    -- 2
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.strct (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.strct (.c .none) [.u8, .u16])) ∧
    -- 3
    (allUnaligned [.u16] = false ∧
      implUnaligned (.strct .transparent [.u16]) = false ∧
      ¬ SemUnaligned (.strct .transparent [.u16])) ∧
    -- 4
    (variantsUnaligned [(.implicit, [])] = true ∧
      EnumRepr.prim .u16 ≠ .prim .u8 ∧ EnumRepr.prim .u16 ≠ .prim .i8 ∧
      implUnaligned (.enm (.prim .u16) [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u16) [(.implicit, [])]) ∧
      EnumRepr.c ≠ .prim .u8 ∧ EnumRepr.c ≠ .prim .i8 ∧
      implUnaligned (.enm .c [(.implicit, [])]) = false ∧
      ¬ SemUnaligned (.enm .c [(.implicit, [])])) ∧
    -- 5
    (variantsUnaligned [(.implicit, [.u16])] = false ∧
      implUnaligned (.enm (.prim .u8) [(.implicit, [.u16])]) = false ∧
      ¬ SemUnaligned (.enm (.prim .u8) [(.implicit, [.u16])])) ∧
    -- 6
    ((ReprModifier.aligned 2).isAlignGt1 = true ∧
      ((ReprModifier.aligned 2).isPacked1 || allUnaligned [.u8]) = true ∧
      implUnaligned (.union (.c (.aligned 2)) [.u8]) = false ∧
      ¬ SemUnaligned (.union (.c (.aligned 2)) [.u8])) ∧
    -- 7
    ((ReprModifier.none).isAlignGt1 = false ∧ (ReprModifier.none).isPacked1 = false ∧
      allUnaligned [.u8, .u16] = false ∧
      implUnaligned (.union (.c .none) [.u8, .u16]) = false ∧
      ¬ SemUnaligned (.union (.c .none) [.u8, .u16]))

-- lean/ToyZc/Enum.lean:1397-1401
theorem ce_enum_fromZeros_of_findZeroVariant_drop_wf :
    discrsWF (.prim .u8) (dupZeroNonLiteral.map Prod.fst) = false ∧
    findZeroVariant (dupZeroNonLiteral.map Prod.fst) = .ok 1 ∧
    (∀ fs, variantFields dupZeroNonLiteral 1 = some fs → ∀ f ∈ fs, SemFromZeros f) ∧
    ¬ SemFromZeros (.enm (.prim .u8) dupZeroNonLiteral)

-- lean/ToyZc/Union.lean:323-327
theorem union_decode_encode_forgets_bytes :
    let U : Desc := .union (.c .none) [.u8, .u16]
    U.encodeL (.union 1 (.int [5, 9])) = [.init 5, .init 9] ∧
    U.decodeL [.init 5, .init 9] = some (.union 0 (.int [5])) ∧
    U.encodeL (.union 0 (.int [5])) = [.init 5, .uninit]

-- lean/ToyZc/Union.lean:334-337
theorem union_decode_not_monotone :
    let U : Desc := .union (.c .none) [.u16, .u8]
    U.decodeL [.init 5, .uninit] = some (.union 1 (.int [5])) ∧
    U.decodeL [.init 5, .init 9] = some (.union 0 (.int [5, 9]))

-- lean/ToyZc/KnownLayout.lean:585-588
theorem vccm_normalizeDst_zst_both_none :
    let d : SliceDstSpec := ⟨.none, [⟨4, 4⟩], ⟨0, 1⟩⟩
    vccm ⟨4, .sliceDst (normalizeDst d)⟩ 0 8 .prefixCast = .panic ∧ maxSliceElems d 8 = none ∧
    (∀ n, dstSize d n ≤ 8)
```

Basis: execution (Lean kernel check)

## Boundaries

### Non-claims (per result)

**R1-semantic-predicates-list-characterizations** (`Toy.Zc.semFromBytes_iff_validInit_total`, `Toy.Zc.semFromZeros_iff_validInit_zeros`, `Toy.Zc.semIntoBytes_iff_encodeL_init`):

* These are equivalences inside the model; they neither establish nor refute the corresponding claims about the safety contracts of zerocopy v0.8.63's `FromBytes`, `FromZeros` and `IntoBytes` traits. That SemFromBytes/SemFromZeros/SemIntoBytes match those documented contracts (zerocopy/src/lib.rs:4266-4269, 3681-3683, 5913-5916) is a modeling bridge.
* validInit is the exact validity of the model's decoder, not zerocopy's runtime check; the two are related only by R2f (derive_isSafe_eq_validInit_of_wf_of_length) for well-formed descriptions and bytes of the right length.
* Bytes carry no provenance; nothing here says anything about pointer-carrying types.
* On unions, validity (Desc.decodeL) is by definition zerocopy's conservative rule 'some field is valid', returning the first such field (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:292-296: 'The bit validity of a union is not yet well defined in Rust, but it is guaranteed to be no more strict than this definition'). Consequently Desc.rep on unions is not canonical: decoding then encoding can forget bytes (union_decode_encode_forgets_bytes) and decoding is not monotone in definedness (union_decode_not_monotone).
* The model has no field invariants (#[zerocopy(invariant)]) and its union validity coincides with the derived union validator, so it does not exhibit the TryFromBytes/IntoBytes asymmetry documented at zerocopy/src/lib.rs:1865-1873 ('for some T: TryFromBytes + IntoBytes, there exist values of t: T such that TryFromBytes::try_ref_from_bytes(t.as_bytes()) == None').
* The semantic predicates speak about by-value byte validity (what owned conversions such as transmute! or read_from_bytes need). zerocopy's reference conversions need more: FromBytes::ref_from_bytes and IntoBytes::as_bytes also require Self: Immutable (zerocopy/src/lib.rs:4390-4392, 5995-5997), which the byte model cannot express (R7a); FromBytes::mut_from_bytes also requires Self: IntoBytes (zerocopy/src/lib.rs:4680-4682); transmute_ref! requires Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, align_of::<Src>() >= align_of::<Dst>() and size compatibility (zerocopy/src/macros.rs:202-208); transmute_mut! requires FromBytes + IntoBytes on both Src and Dst plus the same alignment and size conditions (zerocopy/src/macros.rs:415-421). None of these is modeled.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R2a-struct-fromBytes-fromZeros-iff-fields** (`Toy.Zc.struct_fromBytes_iff_fields_fromBytes`, `Toy.Zc.struct_fromZeros_iff_fields_fromZeros`):

* Does not cover repr(Rust) structs, which zerocopy's FromBytes/FromZeros derives also accept without a repr (zerocopy/src/lib.rs:4143-4168); the model has no repr(Rust) layout.
* Padding bytes are unconstrained by the model's decoder; that Rust imposes no validity on padding is taken from zerocopy's documentation (citing UCG issue 174), not proved.
* Says nothing about generic structs, whose derive output differs.
* That a padded struct is FromBytes does not make reference casts available: FromBytes::mut_from_bytes additionally requires Self: IntoBytes (zerocopy/src/lib.rs:4680-4682), which a padded struct is not (R2c), and FromBytes::ref_from_bytes requires Self: Immutable (zerocopy/src/lib.rs:4390-4392).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R2c-struct-intoBytes-iff-fields-and-no-padding** (`Toy.Zc.struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited`):

* Uses the model's repr(C) placement (reprCStruct); the argument that the padding check is sound for repr(Rust) (fields never overlap) is not formalized.
* Does not cover structs with a trailing slice (zerocopy's PaddingCheck::ReprCStruct / DynamicPaddingFree path).
* Does not say that zerocopy's check is exactly this condition; see R2d for the check's shortcuts.
* SemIntoBytes is by-value byte initialization; IntoBytes::as_bytes(&self) additionally requires Self: Immutable (zerocopy/src/lib.rs:5995-5997), which is not a byte-level property (R7a).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R2d-struct-padding-analysis-sound** (`Toy.Zc.structPaddingOK_sound`):

* Does not model generic structs: zerocopy's generic paths (homogeneous_field_bounds, the Unaligned-fields fallback; zerocopy/zerocopy-derive/src/derive/into_bytes.rs:145-181) are out of scope.
* Does not model repr(packed) without C or repr(Rust), which zerocopy's derive also accepts (is_packed_1 holds for repr(packed) on any base repr).
* The one-field shortcut excludes align(N>1) precisely because a one-field repr(C, align(2)) struct gains trailing padding (ce_one_field_align_gt_1_has_trailing_padding); nothing is claimed about other excluded cases.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R2e-derives-sound-on-well-formed-descriptions** (`Toy.Zc.derive_fromZeros_sound_of_wf`, `Toy.Zc.derive_fromBytes_sound_of_wf`, `Toy.Zc.derive_intoBytes_sound_of_wf`, `Toy.Zc.derive_unaligned_sound`):

* Soundness only: the checks are not complete (findZeroVariant_incomplete_with_unknown, findZeroVariant_incomplete_nonliteral_before_implicit, union_fromBytes_derive_not_necessary).
* The IntoBytes statement holds in every DeriveConfig; it says nothing about whether the union cfg gate is needed for soundness in Rust (see R4d).
* Every nominal type is assumed to request the derive; impls written by hand, or derives not requested, are not modeled.
* Generic types, field invariants, slice DSTs, repr(Rust), and pointer types are not covered.
* Does not model #[derive(KnownLayout)] (zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-351) or zerocopy's construction of a type's DstLayout (DstLayout::for_type, DstLayout::for_repr_c_struct).
* The real #[derive(FromZeros)] first expands the TryFromBytes derive (zerocopy/zerocopy-derive/src/derive/from_bytes.rs:98), which bounds the fields of every variant by TryFromBytes (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:343), not only the zero variant's fields. Every description in the model implements TryFromBytes, so the model omits these bounds; outside the model (generic or invariant-carrying field types) they can make the derive reject an enum whose zero variant's fields are FromZeros.
* The semantic predicates speak about by-value byte validity (what owned conversions such as transmute! or read_from_bytes need). zerocopy's reference conversions need more: FromBytes::ref_from_bytes and IntoBytes::as_bytes also require Self: Immutable (zerocopy/src/lib.rs:4390-4392, 5995-5997), which the byte model cannot express (R7a); FromBytes::mut_from_bytes also requires Self: IntoBytes (zerocopy/src/lib.rs:4680-4682); transmute_ref! requires Src: IntoBytes + Immutable, Dst: FromBytes + Immutable, align_of::<Src>() >= align_of::<Dst>() and size compatibility (zerocopy/src/macros.rs:202-208); transmute_mut! requires FromBytes + IntoBytes on both Src and Dst plus the same alignment and size conditions (zerocopy/src/macros.rs:415-421). None of these is modeled.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R2f-derived-isSafe-equals-validity** (`Toy.Zc.derive_isSafe_eq_validInit_of_wf_of_length`):

* On unions the equality is with Desc.decodeL, which is defined as zerocopy's own rule 'some field is valid' (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:292-296); for unions the theorem therefore records agreement with that modeled rule, not that the derived union validator is exact for Rust, whose union validity is unsettled (it is only guaranteed to be no stricter).
* The model has no field invariants (#[zerocopy(invariant)]) and its union validity coincides with the derived union validator, so it does not exhibit the TryFromBytes/IntoBytes asymmetry documented at zerocopy/src/lib.rs:1865-1873 ('for some T: TryFromBytes + IntoBytes, there exist values of t: T such that TryFromBytes::try_ref_from_bytes(t.as_bytes()) == None').
* Models the validator for a derive whose top-level trait is TryFromBytes; the FromBytes-top-level shortcut try_gen_trivial_is_safe (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:347-393) is not modeled.
* Says nothing about uninitialized input bytes (is_safe is only called on initialized bytes) or about field invariants.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3a-fieldless-enum-fromBytes-iff-all-tags** (`Toy.Zc.fieldless_enum_fromBytes_iff_every_tag_is_discriminant`):

* Does not say the derive checks this condition directly; the derive counts variants (R3b).
* Does not cover repr(C) enums or enums with align(N). (Source observation, not a theorem: zerocopy-derive's FromBytes derive rejects repr(C) enums, enum_size_from_repr at zerocopy/zerocopy-derive/src/util.rs:982-1001; the modeled check enumVariantCountOK is false for EnumRepr.c by definition.)
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3b-enum-variant-count-check-sound** (`Toy.Zc.enum_variant_count_check_sound`):

* The check's soundness depends on the compiler rejecting duplicate or out-of-range discriminants; the derive itself does not check this.
* Does not claim that the count check (enumVariantCountOK) is necessary for SemFromBytes: it rejects repr(C) and 32/64-bit primitive representations outright (matching zerocopy-derive's u8/i8/u16/i16 cap), although R3a characterizes SemFromBytes for every primitive width; and for data-carrying enums, or without distinct representable discriminants, the variant count does not determine SemFromBytes.
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3c-enum-fromBytes-derive-sound** (`Toy.Zc.enum_fromBytes_of_count_check`):

* The derive additionally runs the FromZeros check (find_zero_variant); that conjunct is not needed for FromBytes and makes the check incomplete for enums whose zero discriminant is written as a non-literal expression. Proved in the model (Toy.Zc.fromBytes_enum_rejected_by_findZeroVariant): the well-formed repr(u8) enum nonLiteralZeroFullU8 (first variant = ZERO, a non-literal expression the compiler evaluates to 0, then 255 implicit variants 1..255) passes enumVariantCountOK and is SemFromBytes and SemFromZeros, but find_zero_variant returns Err(true) and implFromBytes rejects it. That zerocopy-derive rejects the corresponding Rust enum is a modeling bridge (zerocopy/zerocopy-derive/src/derive/from_bytes.rs:113, 143-162).
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3d-enum-fromZeros-iff-zero-variant** (`Toy.Zc.enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF`):

* Does not say how the zero variant is found; the derive's syntactic search is R3e and is incomplete.
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* The real #[derive(FromZeros)] first expands the TryFromBytes derive (zerocopy/zerocopy-derive/src/derive/from_bytes.rs:98), which bounds the fields of every variant by TryFromBytes (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:343), not only the zero variant's fields. Every description in the model implements TryFromBytes, so the model omits these bounds; outside the model (generic or invariant-carrying field types) they can make the derive reject an enum whose zero variant's fields are FromZeros.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3e-find-zero-variant-and-enum-fromZeros-derive** (`Toy.Zc.findZeroVariant_sound`, `Toy.Zc.findZeroVariant_complete_of_no_unknown`, `Toy.Zc.enum_fromZeros_of_findZeroVariant`):

* find_zero_variant is incomplete: a non-literal discriminant expression that either evaluates to 0 (findZeroVariant_incomplete_with_unknown) or precedes an implicit discriminant that resolves to 0 (findZeroVariant_incomplete_nonliteral_before_implicit; the source's diagnostic says such a discriminant may 'define or imply which variant has a discriminant of zero', zerocopy/zerocopy-derive/src/derive/from_bytes.rs:150-152) makes the search return Err(true), so the derive rejects some FromZeros enums.
* Without the compiler's E0081 rule the FromZeros derive would be unsound (ce_enum_fromZeros_of_findZeroVariant_drop_wf, where the modeled check accepts and the enum is not FromZeros).
* Literal discriminants above u128::MAX (where the source's parse can fail) are not modeled.
* The real #[derive(FromZeros)] first expands the TryFromBytes derive (zerocopy/zerocopy-derive/src/derive/from_bytes.rs:98), which bounds the fields of every variant by TryFromBytes (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:343), not only the zero variant's fields. Every description in the model implements TryFromBytes, so the model omits these bounds; outside the model (generic or invariant-carrying field types) they can make the derive reject an enum whose zero variant's fields are FromZeros.
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* Modeling bridge, not proved: reading R3e as a statement about rustc and zerocopy-derive needs bridge B9 (resolveDiscrs computes the compiler's discriminant values: implicit = previous + 1, first = 0) and bridge B8 (findZeroVariant transcribes find_zero_variant, zerocopy/zerocopy-derive/src/derive/from_bytes.rs:19-90). Under these bridges, find_zero_variant returning Ok(i) means that the compiler resolves variant i's discriminant to 0.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3f-enum-tryFromBytes-validity-and-is-safe** (`Toy.Zc.enum_validInit_iff_first_matching_variant_valid`, `Toy.Zc.isSafe_enm_eq_validInit`):

* Does not model the FromBytes-top-level shortcut try_gen_trivial_is_safe (zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:347-393).
* Does not model field invariants (#[zerocopy(invariant)]), which can make is_safe stricter than validity.
* Says nothing about uninitialized input bytes (is_safe is only called on initialized bytes).
* The right-hand side uses the first matching variant (findIdx?); with duplicate discriminants an existential 'some variant matches and its fields are valid' would differ, which is why the characterization is stated with the first match.
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R3g-enum-intoBytes-padding-check-sound** (`Toy.Zc.enum_intoBytes_of_fields_of_padding_check`):

* Does not cover repr(Rust) enums (niche layouts). (Source observation, not a theorem: the IntoBytes derive rejects enums that are neither repr(C) nor primitive-repr, zerocopy/zerocopy-derive/src/derive/into_bytes.rs:198.)
* Does not cover enums with #[repr(..., align(N))] (not in the model's AST), repr(C) enums whose discriminants need a tag other than the 4-byte i32-range tag, or repr(Rust) enums (niches).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R4a-union-intoBytes-iff-full-size-fields** (`Toy.Zc.union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited`):

* The union value model is 'written through one field'. Values produced by successive writes through different fields (e.g. write b: u16, then overwrite a: u8) are not distinct values of the model (union_decode_encode_forgets_bytes). The claim is relative to this value model; it is sound for Rust only under guarantees Rust has not made: either union bit validity forbids uninit at bytes initialized in every valid value of every field, or (zerocopy issue 1792, rust-lang/unsafe-code-guidelines issue 533) it is never safe to construct a union value other than from its fields, typed copies of a union preserve every byte written at a position that is not padding in all fields, and IntoBytes carries a library safety invariant that values are only constructed from fields.
* Proved for the written-through-one-field value model; under a permissive union validity that admits uninitialized bytes it fails: no union of nonzero size is IntoBytes there (R4d). Rust has not settled union validity.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R4b-union-intoBytes-derive-sound** (`Toy.Zc.union_intoBytes_of_fields_of_padding_check`):

* The cfg gate (into_bytes.rs:220-233) is not a semantic condition in the model: the check with the cfg unset rejects a union that is IntoBytes here (union_gate_rejects_intoBytes_union).
* The union value model is 'written through one field'. Values produced by successive writes through different fields (e.g. write b: u16, then overwrite a: u8) are not distinct values of the model (union_decode_encode_forgets_bytes). The claim is relative to this value model; it is sound for Rust only under guarantees Rust has not made: either union bit validity forbids uninit at bytes initialized in every valid value of every field, or (zerocopy issue 1792, rust-lang/unsafe-code-guidelines issue 533) it is never safe to construct a union value other than from its fields, typed copies of a union preserve every byte written at a position that is not padding in all fields, and IntoBytes carries a library safety invariant that values are only constructed from fields.
* Does not show the derive is sound for Rust unions; that depends on the unsettled union validity (R4d).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R4c-union-u8-u16-counterexample** (`Toy.Zc.union_u8_u16_written_through_u8_leaves_uninit`):

* Shows only that the size conjunct of the union check is needed; it is not evidence about Rust's union validity.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R4d-permissive-union-validity-of-size-pos-not-intoBytes** (`Toy.Zc.permissive_union_validity_of_size_pos_not_intoBytes`):

* Does not claim Rust adopts permissive union validity; it records that, if union values may contain uninitialized bytes, IntoBytes for unions of nonzero size cannot be a property of the bit-valid values alone, which is the concern behind the cfg gate.
* Does not explain the choice of a --cfg over a Cargo feature (a policy decision recorded in zerocopy issue 1792: a --cfg must be enabled by the top-level crate).
* Escape hatches (each defeats the impossibility only together with the conditions listed): (a) Rust restricts union bit validity so that a byte initialized in every valid value of every field is initialized in the union (the 'union validity' option of zerocopy issue 1792); or (b) under permissive bit validity, IntoBytes becomes a library safety invariant (union values only constructed from fields, documented on IntoBytes) AND Rust guarantees that safe code cannot construct a union value other than from its fields AND that typed copies preserve every byte written at a position that is not padding in all fields (the 'union safety' option of issue 1792; rust-lang/unsafe-code-guidelines issue 533). Restricting safe construction alone is not enough: unsafe code could still produce an uninitialized but bit-valid union value (e.g. MaybeUninit::uninit().assume_init()) and pass it to safe code. The positive control pc_written_union_intoBytes models only the field-write value set, i.e. the outcome of (a) or (b).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R5a-transmute-total-of-intoBytes-of-fromBytes** (`Toy.Zc.transmuteTotal_of_intoBytes_of_fromBytes`):

* Equal sizes are built into the carrier type; see R5b for differing sizes.
* By-value transmute! forgets Src without running its destructor (zerocopy/src/macros.rs:35-38); reference transmutes need more than IntoBytes/FromBytes (transmute_ref!: Immutable on both sides, alignment, size compatibility, zerocopy/src/macros.rs:202-208; transmute_mut!: FromBytes + IntoBytes on both sides, alignment, size compatibility, zerocopy/src/macros.rs:415-421). Not modeled.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R5b-desc-transmute-total-size-ge** (`Toy.Zc.desc_transmute_total_of_size_ge`, `Toy.Zc.desc_transmute_total_of_size_eq`):

* Size equality is not necessary (transmute_shrink_example: u32 -> u16), and size Dst <= size Src is necessary only for the statement quantified over all FromBytes destinations (ce_transmute_drop_size: u8 -> u16); for a fixed padded destination it is not: u8 to #[repr(C, align(2))] struct { a: u8 } (size 2) succeeds for every value (transmute_extend_into_trailing_padding_example), as core::mem::TransmuteFrom's union-transmute also permits.
* The transmute model is a union-transmute (Src written through one field of a repr(C) union, Dst read through another, bytes beyond Src uninit). zerocopy's transmute!(#![allow(shrink)] ...) implements exactly this with a #[repr(C, packed)] union and core::mem::transmute, which forces size Dst <= size Src (zerocopy/src/macros.rs:106-110, 142-146); agreement with Rust's semantics of that construction is a modeling bridge.
* desc_transmute_total_of_size_eq (equal sizes; the bounds of plain transmute!, zerocopy/src/macros.rs:15-28) is a one-line corollary kept as a reference point; it is not a separate result.
* By-value transmute! forgets Src without running its destructor (zerocopy/src/macros.rs:35-38); reference transmutes (transmute_ref!, transmute_mut!) need Immutable or bidirectional FromBytes + IntoBytes plus alignment and size conditions (zerocopy/src/macros.rs:202-208, 415-421). Not modeled.
* Modeling bridge, not proved (B10): transmuteVal is the model of zerocopy's transmute!(#![allow(shrink)] ...), which is implemented by a #[repr(C, packed)] union-transmute (zerocopy/src/macros.rs:106-157); the equal-size form transmute!(...) is a plain core::mem::transmute (zerocopy/src/macros.rs:161-192, call at 188), which coincides with the union-transmute at equal sizes, so desc_transmute_total_of_size_eq is the model of plain transmute!.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R6a-validate-cast-returns-max-fitting-elems** (`Toy.Zc.vccm_sliceDst_returns_max_fitting_elems`):

* Unbounded naturals: usize overflow and the debug assertion addr + bytes_len <= usize::MAX are not modeled.
* Bit-mask arithmetic is replaced by its arithmetic meaning for power-of-two alignments (a modeling bridge; the theorem itself holds for any positive alignment).
* The layout alignment align is a free parameter, not related to the trailing-slice layout (even align = 0 is admitted, where the check reads addr + offset = 0). R6a therefore says nothing about the alignment of the object's start for a suffix cast; that guarantee (zerocopy/src/layout.rs:1584-1591) needs the divisibility hypotheses of R6d. R6a also does not use the containment condition on the trailing slice's offset (the offset field is not read by the validation).
* Does not establish that zerocopy's for_repr_c_struct produces such layouts for real types (see R6b for flat repr(C) DSTs).
* Does not model #[derive(KnownLayout)] (zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-351) or zerocopy's construction of a type's DstLayout (DstLayout::for_type, DstLayout::for_repr_c_struct).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R6d-validate-cast-start-aligned-of-align-dvd** (`Toy.Zc.vccm_sliceDst_start_aligned_of_align_dvd`):

* No positivity, phase, or element-size hypothesis is needed; the validation's own endpoint check supplies alignment of addr (prefix) or addr + bytes_len (suffix). The theorem does not say the returned count is maximal (that is R6a).
* With align = 0, Lean's 0 ∣ x means x = 0 and x % 0 = x, so the hypotheses require t.sizeBase = 0 and t.sizeAlign = 0, and the conclusion (addr + startOffset ct splitAt) % align = 0 reads addr + startOffset ct splitAt = 0; the theorem has no 0 < align hypothesis.
* normalizeDst_align_dvd shows that the normalized layout of a flat repr(C) slice DST with layout alignment dstAlign d satisfies both hypotheses; whether zerocopy's own DstLayout for real types does is not modeled.
* Does not model #[derive(KnownLayout)] (zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-351) or zerocopy's construction of a type's DstLayout (DstLayout::for_type, DstLayout::for_repr_c_struct).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R6b-normalized-layout-size-equals-closed-form** (`Toy.Zc.normalizeDst_sizeForElems_eq_dstSize`):

* Does not claim zerocopy's for_repr_c_struct produces exactly normalizeDst d (under packed(N) it can keep a larger rounding alignment with the same sizes).
* Does not model #[derive(KnownLayout)] (zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-351) or zerocopy's construction of a type's DstLayout (DstLayout::for_type, DstLayout::for_repr_c_struct).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R6c-validate-cast-agrees-with-closed-form-max** (`Toy.Zc.vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned`):

* For zero-sized elements both sides are none for different reasons (panic vs. none); no largest count exists (vccm_normalizeDst_zst_both_none).
* Only element counts are compared (split_at is dropped), and the layout alignment is arbitrary rather than dstAlign d; start alignment is R6d (with normalizeDst_align_dvd for align = dstAlign d).
* With align = 0 the alignment hypothesis (addr + castOffset ct bytesLen) % align = 0 reads addr + castOffset ct bytesLen = 0, because Lean defines x % 0 = x; the theorem has no 0 < align hypothesis, so at align = 0 the hypothesis is not "no alignment constraint" but holds exactly when addr + castOffset ct bytesLen = 0.
* Does not model #[derive(KnownLayout)] (zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-351) or zerocopy's construction of a type's DstLayout (DstLayout::for_type, DstLayout::for_repr_c_struct).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R7a-immutable-not-byte-determined** (`Toy.Zc.immutable_not_byte_determined`):

* Says nothing about what Immutable guarantees; it only shows that the byte model cannot express it.
* Escape hatch: a model with interior-mutability information (not modeled) could express it.
* The contrast is with the semantic byte predicates: SemFromBytes is byte-determined (pc_fromBytes_byte_determined). The syntactic derive checks implFromBytes/implFromZeros are not byte-determined either (they reject semantically qualifying types, R7b), so the result is about the absence of a byte-level semantic counterpart for Immutable (interior mutability), not about syntactic checks in general.
* Since FromBytes::ref_from_bytes, IntoBytes::as_bytes and transmute_ref! require Immutable (zerocopy/src/lib.rs:4390-4392, 5995-5997; zerocopy/src/macros.rs:202-208), the byte model alone cannot justify those reference conversions.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R7b-union-derives-require-more-than-needed** (`Toy.Zc.union_fromBytes_derive_not_necessary`, `Toy.Zc.union_fromZeros_derive_not_necessary`):

* Relative to the model's union validity ('some field is valid', zerocopy's documented sufficient condition); it does not say zerocopy should relax the derive, which may serve purposes outside the model (e.g. code that reads every field).
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

**R7c-unaligned-check-conjuncts-necessary** (`Toy.Zc.unaligned_check_conjuncts_necessary`):

* Necessity is shown per conjunct on specific descriptions, not as a characterization of Unaligned.
* Model-relative: statements are about the toy model: closed non-generic descriptions built from the primitives u8, i8, u16, i16, u32, i32, u64, i64 and bool (no u128/i128, usize/isize, floats, char, NonZero*, tuples, PhantomData, ManuallyDrop, references or pointers); little-endian integers whose alignment equals their size (modeled on x86_64-unknown-linux-gnu); repr(C) enums restricted to a 4-byte tag holding i32-range discriminants; no align(N) on enums; unbounded natural-number sizes. Agreement with zerocopy and rustc is a modeling bridge argued from cited source lines, not a kernel-checked fact.

### Escape hatches of the impossibility results

* **R4d** (`permissive_union_validity_of_size_pos_not_intoBytes`): dropping `hn` (nonzero size) defeats it (`ce_permissive_drop_size_pos`, a zero-size union is vacuously `IntoBytes`). Replacing permissive union validity by the written-through-a-field reading also defeats it: the positive control `pc_written_union_intoBytes` exhibits a nonzero-size union that is `IntoBytes` there. So R4d is about permissive validity only. It does not show that union `IntoBytes` is unsound in Rust, which has not settled union validity.
* **R7a** (`immutable_not_byte_determined`): the result is relative to the byte-level semantics of the model (layout, typing, encoder, decoder). A model that records interior mutability would escape it. The positive control `pc_fromBytes_byte_determined` shows that a byte-level predicate (`SemFromBytes`) is byte-determined, so the obstruction is specific to `Immutable`.

### Hypotheses whose tightness is unknown or harmless

None. Every hypothesis of every result is labelled `tight` and has a kernel-checked counterexample theorem stating that all other hypotheses hold and the conclusion fails.

### Disproved or dropped statements

None. All 26 results were proved exactly as stated; no statement was found false and none was left unproved.

### Not examined

* Generic types, `repr(Rust)` types (including niche-optimized enums), `repr(packed)` without `C`, `repr(C, Int)` enums, `align(N)` on enums, transparent unions, and slice DSTs inside derived types (`PaddingCheck::ReprCStruct`).
* Field invariants (`#[zerocopy(invariant)]`), pointer provenance, floating-point types, and the `FromBytes`-top-level `is_safe` shortcut.
* `#[derive(KnownLayout)]`, `usize`/`isize::MAX` overflow, targets other than the modeled `x86_64-unknown-linux-gnu` assumptions, and zerocopy versions other than v0.8.63.
* Reference conversions (`ref_from_bytes`, `as_bytes`, `transmute_ref!`, `transmute_mut!`), which need `Immutable` or additional bounds that the byte model cannot express (R7a).

### Stronger conclusions this package does not establish

* That zerocopy's real derives are sound: soundness is proved for the modeled checks (R2e), and their agreement with zerocopy-derive is the modeling bridge B8.
* That the checks are complete: they are not (see the proved observations under Findings).
* That the union `IntoBytes` derive is sound in Rust: R4a and R4b hold under the written-through-a-field reading, and R4d shows that under permissive validity no nonzero-size union is `IntoBytes`.
* That `validInit` equals Rust's validity on unions: on unions it is zerocopy's conservative rule by construction (B4).
* That R6a–R6d cover zerocopy's overflow behavior: sizes are unbounded naturals.

## Evidence

**Kernel check** (observed 2026-11-20). Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), no Mathlib, no dependencies. `lake build` of `lean/` succeeds. No Lean source contains `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`.
Lean's `collectAxioms` over all 1622 non-internal declarations of the `ToyZc` modules finds only subsets of `propext`, `Classical.choice`, `Quot.sound` (0 exceptions). The per-declaration record is `audit/axioms.json`.

**Statement hashes.** For every Lean name referenced by `results.json` (results, non-vacuity witnesses, positive controls and counterexamples), `audit/statements.json` records two hashes. The statement hash is the SHA-256 of Lean's `repr` of the declaration's type. The closure hash is the SHA-256 of the newline-joined, sorted lines `name : repr(type) [:= repr(value)]` for every `ToyZc` constant reachable from the type, where theorem bodies are excluded and definitions are followed through their values. A change to a statement or to any definition it depends on changes these hashes.

| Lean name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `Toy.Zc.ce_count_check_drop_count` | R3b counterexample (hc) | Quot.sound, propext | `c0054f91ee0c8c6d120c16d8318b14eb146396df0c985ba9d90a9414b8f2b835` | `65dfc3304fa82d12be540f443aa5b6ac338ac9c3a67a575bc4163c506f33eb6a` (69) |
| `Toy.Zc.ce_count_check_drop_representable` | R3b counterexample (hwf) | Quot.sound, propext | `47d7b5aaf4128d49ddbca6b8dfbfd0a94a73bc07fed01e92338e23b44a4928f9` | `f419474e6fecfa8aec6ec48a0aa17d07489a84373ef2e2728ec2b7f8b8ec8c19` (70) |
| `Toy.Zc.ce_count_check_drop_wf` | R3b counterexample (hwf) | Quot.sound, propext | `ac00898938d03e0c41db11316029c4619e0bc8dd9023bd49077ad5253e6f043e` | `3248a8c5beae58e0241873569f8d6b2ced49e0e72af17e06bb20addcb569a8cf` (70) |
| `Toy.Zc.ce_derive_drop_check` | R2e counterexample (h (the check; all four theorems)) | Classical.choice, Quot.sound, propext | `aaeaea7d1f491df190affae2bb4b1f8d01fc5b30c5e4f669d8c7635c8df0f247` | `580fa6e846aec700a7af5b9838bbfe01b4f7788adb935b6c10c367b2bbee1a2e` (303) |
| `Toy.Zc.ce_derive_fromBytes_drop_wf` | R2e counterexample (hwf (derive_fromZeros_sound_of_wf, derive_fromBytes_sound_of_wf, derive_intoBytes_sound_of_wf; derive_unaligned_sound has no such hypothesis)) | Classical.choice, Quot.sound, propext | `8d9c68b882348c864965b1e350148bdadf2c3d04635e27031c742bb7bc5a3db5` | `99e2d122acf0f2d89838787ec6e535512d7873a1f445d8a18fd37b152d9aea2f` (254) |
| `Toy.Zc.ce_derive_fromZeros_drop_wf` | R2e counterexample (hwf (derive_fromZeros_sound_of_wf, derive_fromBytes_sound_of_wf, derive_intoBytes_sound_of_wf; derive_unaligned_sound has no such hypothesis)) | Quot.sound, propext | `56867355e1e92c489ccd1c9a0f4a0b1ec27a780b79ca69449fd83187a7031616` | `7db4aa36023a4c9e72eba436352711752891d6f4f1dd84b37ae80a267cd39b8d` (242) |
| `Toy.Zc.ce_derive_intoBytes_drop_wf` | R2e counterexample (hwf (derive_fromZeros_sound_of_wf, derive_fromBytes_sound_of_wf, derive_intoBytes_sound_of_wf; derive_unaligned_sound has no such hypothesis)) | Classical.choice, Quot.sound, propext | `97dd1aea0adafca863dfb1ef01e68ab219f32f12b56660ef87099c70e28c4a21` | `ec748aadbb524db63d55671176a990684406b6e31781810a227ac7645fd62a70` (255) |
| `Toy.Zc.ce_derive_isSafe_drop_hlen` | R2f counterexample (hlen) | propext | `0dd5697614eb5cf4c2f258775a072a402a379d0b0b5b83e2286e6df191776675` | `23c79e8185eadf33112473d1900432af359287a4cac6ae4ffd62396376e5411f` (224) |
| `Toy.Zc.ce_derive_isSafe_drop_wf` | R2f counterexample (hwf) | propext | `dc02d7431977f5e840cd859e6b7bee339b2fb33f3ab42120073111f822ff99a0` | `d30a2d0c8b31e86d09f43347e019c450d362829946f082c020eb8bc568a37e74` (224) |
| `Toy.Zc.ce_enum_fromBytes_drop_count` | R3c counterexample (hc) | Classical.choice, Quot.sound, propext | `d7e68251b0dcd0ecaa691c8d56aa38069d13c8dddb95c9f8d54b1f88fb8d1da5` | `a49533e5368c2e72ecaadd10efe1e1b2ab1a28987212c254e1fccccb3cd9318f` (227) |
| `Toy.Zc.ce_enum_fromBytes_drop_fields` | R3c counterexample (hF) | Classical.choice, Quot.sound, propext | `418a4ee479c3dd1a8e52d8266ff56ba47bea793ddfe765bd8e372aa5b9eebd3a` | `31f3586b92a668b0388372bd2da34bcc9074c1ac34b1206ec701b7aff9e137f2` (228) |
| `Toy.Zc.ce_enum_fromBytes_drop_representable` | R3c counterexample (hwf) | Classical.choice, Quot.sound, propext | `cc3ad86aac5013ffe9c2a0c8bc16381352f2bc59747bf134424a8d3d3cf6aee8` | `83c859cbfa70355072139b72e3deac01c008b10fe162e48b165c00f398eef53f` (228) |
| `Toy.Zc.ce_enum_fromBytes_drop_wf` | R3c counterexample (hwf) | Classical.choice, Quot.sound, propext | `141f4f0f7e3c0620ddf24fada2932aee2711426a8247acbe7299b04cb3f79428` | `e2e284b560bcc222834193ce3f641f3e7c1417c3680c993e51aed3943b400b02` (228) |
| `Toy.Zc.ce_enum_fromZeros_drop_fields` | R3e counterexample (hF (enum_fromZeros_of_findZeroVariant)) | Quot.sound, propext | `d2441fe75f148555b57676ca58041a516c8932cb0394de253d140044ad8e2033` | `7b745d050c7524e9fa1c517e7a26b216439285b5eb0816cb911f7c5e9ad782db` (226) |
| `Toy.Zc.ce_enum_fromZeros_drop_findZero` | R3e counterexample (hz (enum_fromZeros_of_findZeroVariant)) | Quot.sound, propext | `cc836ece3d49de8eb19f78d303101582d48796e3dddb28e299b6bdc69d73cd65` | `7b745d050c7524e9fa1c517e7a26b216439285b5eb0816cb911f7c5e9ad782db` (226) |
| `Toy.Zc.ce_enum_fromZeros_iff_drop_representable` | R3d counterexample (hwf) | Quot.sound, propext | `868b33164bd8805faca9eb4d452c867d4c9d0e46b5e6e751b7a6eeae7e18ec53` | `657c190c45a93e107a87982d9f56548ba45b6946d144edab76b601f6b01d09a8` (219) |
| `Toy.Zc.ce_enum_fromZeros_iff_drop_wf` | R3d counterexample (hwf) | Quot.sound, propext | `81518f864e7b8a86508ff4c57b5c99a4bbfdc92ef8db238eb227ccb2e783270f` | `c5f8653facb2bc777caae46cc133dc4e27e670bc3c4697b6662759f03290b1fe` (235) |
| `Toy.Zc.ce_enum_fromZeros_of_findZeroVariant_drop_representable` | R3e counterexample (hwf (enum_fromZeros_of_findZeroVariant)) | Quot.sound, propext | `cb1d589c766ebc5b779aa49c7f9c8d7b746743c77a846e097929e5f39256347d` | `7b745d050c7524e9fa1c517e7a26b216439285b5eb0816cb911f7c5e9ad782db` (226) |
| `Toy.Zc.ce_enum_fromZeros_of_findZeroVariant_drop_wf` | R3e counterexample (hwf (enum_fromZeros_of_findZeroVariant)) | Quot.sound, propext | `269beda9a7a85b4296ab14f44a63f66f84a3d3ab3f3dc2bbf6e5856ff5580389` | `bb33c1df3baebfc16963cd4c8b1fda99d678a51d832ba0c72ac42ca466934b92` (227) |
| `Toy.Zc.ce_enum_intoBytes_drop_fields` | R3g counterexample (hF) | Classical.choice, Quot.sound, propext | `bf9ea2819ff9a69d35bdf2e63e187c1841b6ac556598ba21e425a9fed06a1475` | `f05a69aa955de0a28425f0228645cf52fe7c605e30308c4e986af03424e7841a` (215) |
| `Toy.Zc.ce_enum_intoBytes_drop_padding` | R3g counterexample (hP) | Classical.choice, Quot.sound, propext | `9c73c0e9442c3ff0227d269fe8a400d6ede969713f9db25ee4b3ce77fa15a41d` | `09c39423c8e472b0adb9ccca6c8fd97e46f8e5e315104fb957a71ffff9c2767b` (214) |
| `Toy.Zc.ce_enum_validInit_drop_hlen` | R3f counterexample (hlen (both theorems)) | propext | `33434e184a66f81247d5601841079a5098efc1c8cc25983791a19f1c3b66641a` | `869734d58e3a96b0ec719b2cbbc962f019323e2136816c409d7136b24cf9805f` (193) |
| `Toy.Zc.ce_fieldless_enum_fromBytes_iff_drop_fieldless` | R3a counterexample (hfl) | Classical.choice, Quot.sound, propext | `aa2c26c1ef4b9b860f399f2e2cd37e0df211034234ce44d8eb8027b81f422dd5` | `cd97cfbbfadd4121eed2139e5165d53c6832e7c6fee9adb15b6e9c7db3e4a4df` (212) |
| `Toy.Zc.ce_findZeroVariant_sound_drop_h` | R3e counterexample (h (findZeroVariant ds = ok i)) | propext | `0d8cc5579d49c02972873da609b6d5588a0f5711ae3f93c35731bc507c742d9b` | `b6b7952b655bb5cb55d2c1e0cfe2f0e22cca20c16e6542d5319164dfc0c3e746` (18) |
| `Toy.Zc.ce_isSafe_enm_drop_fields` | R3f counterexample (hfields (isSafe_enm_eq_validInit)) | propext | `f10561dda47dacad6df6bb31c8f69151cf2a2979b1a10997b8fc17a75806aded` | `8b4bc5201c71c2055d0e9d53433610a21da93e02c5f4fb646e7a09779ffe13e7` (216) |
| `Toy.Zc.ce_isSafe_enm_drop_hlen` | R3f counterexample (hlen (both theorems)) | propext | `e5ca7d863efad4c01db2dfeb4a655e45de36d41c11f51d47dcdbf13a0416feee` | `5d1c61131f529405fc5776dcd355159cf0a041ef7861b4ffb5a5a7d6db45e729` (215) |
| `Toy.Zc.ce_isSafe_enm_drop_wf` | R3f counterexample (hwf (isSafe_enm_eq_validInit)) | propext | `0eb9c39f8abddc73b0964de79432885696e97a9e68b9e7afd836d70fbdaab044` | `8b4bc5201c71c2055d0e9d53433610a21da93e02c5f4fb646e7a09779ffe13e7` (216) |
| `Toy.Zc.ce_one_field_align_gt_1_has_trailing_padding` | R2d counterexample (hP) | Classical.choice, Quot.sound, propext | `2bb237657a9ce072a1203d7fec0e52b418f7c51aa9b8157633c34bf7fd67d8a3` | `48c02b684a1299dfb45f7eb0a9a9776621544551861f9f6e81ef53e8bdfc75b2` (241) |
| `Toy.Zc.ce_padded_struct_of_intoBytes_fields_not_intoBytes` | R2c counterexample ((right side) size = sum of field sizes) | Classical.choice, Quot.sound, propext | `4124230f94c05efec8cbeb9be901f8fd0ae32cde0f51a32c1625ddbce3b13324` | `1096411b09e8edb7ec5c224cba9e9e6a4c8611138f791c9ade88694b4a7b24e0` (225) |
| `Toy.Zc.ce_permissive_drop_size_pos` | R4d counterexample (hn) | Quot.sound, propext | `37e96d8da09f188fb6182255f72d5a3cf4109904c16ac24cd84648a7fe63c571` | `acc92b539bd077010d1924869453be0bfcbdc634eaef28cf158bc3489f94b338` (123) |
| `Toy.Zc.ce_structPaddingOK_drop_inner_wf` | R2d counterexample (hwf) | propext | `704f5bb7e02cea8cbb061c4b2c389a4b2fc82605e49ef178d004681764015b2d` | `bb12fe0802be70fdaed9cc8a66433a029d0f81ae8b6f1ac0282f236647101734` (147) |
| `Toy.Zc.ce_structPaddingOK_drop_wf` | R2d counterexample (hwf) | propext | `05384b198bf9ffe7b40112c044af10cbd5034f5b34a3280c3749cc88735ee5ef` | `695d244513faf469344924a7b3e3fd85fcb4d69227ff3c3cb9697c7c686a2f05` (148) |
| `Toy.Zc.ce_structPaddingOK_drop_wf_packed3` | R2d counterexample (hwf) | propext | `6dbeb0806ee12d2dea916f765c837585e4868ab075224b40f942a4ed8308bbd2` | `8cacb1f2bdc23e4893ed27907f556850ffaf1f123a995770bfd407e0057582b1` (147) |
| `Toy.Zc.ce_struct_drop_fields_intoBytes` | R2c counterexample ((right side) every field IntoBytes) | Classical.choice, Quot.sound, propext | `c1efa22e1967c0c70bbbf7344c3527142dfa0369198f8192c50265ba55c27f85` | `56795c7a4c46afa77103700ab3037f449c8ffbbeadb73c33f5fff98cf2a38770` (215) |
| `Toy.Zc.ce_struct_intoBytes_iff_drop_inhabited` | R2c counterexample (hInh) | Classical.choice, Quot.sound, propext | `3fadaedc525c46dec25ca3069b88b217f2e240f6500fb44ab637181166a8f1c1` | `abc48a30cd161eefed09ef4d1cf8cd470b203b5300a14d34d418d8bec475f41e` (214) |
| `Toy.Zc.ce_transmuteTotal_drop_fromBytes` | R5a counterexample (hB) | Classical.choice, Quot.sound, propext | `9959a6a907363bbf1dcfd0593f938d540492493c934ddbfb549fb7697bd7b6e0` | `3d204952b509429abc994b34e8058aed97cf93e0641cf478150a384d7fd4527d` (96) |
| `Toy.Zc.ce_transmuteTotal_drop_intoBytes` | R5a counterexample (hA) | Classical.choice, Quot.sound, propext | `727a76ae7258270d0b54be4ca7368bacf743090457ea2ca414204d6c5c4141e1` | `0f7b1b26ee8acc349e3cc7f85ccf7107178e4f984b7563dfe8c773fd6e065f0b` (99) |
| `Toy.Zc.ce_transmute_drop_fromBytes` | R5b counterexample (hF) | Classical.choice, Quot.sound, propext | `1f6988bcdeb9f3c3670aa86852f4729039a6a7fed13e83c69332eb12451956a0` | `8d1663f9e5017fedbf1c3ead374c9d5b55293bcf007c039295d38730bbdd8bc5` (216) |
| `Toy.Zc.ce_transmute_drop_intoBytes` | R5b counterexample (hI) | Classical.choice, Quot.sound, propext | `ce5561b655dbea218206feba787ba43479fc04ca71dca455cf62538e25a347e1` | `18e3da75777c954fa2edb37369332d7805be06a40ec2ec969ab2b6b7c7de12be` (219) |
| `Toy.Zc.ce_transmute_drop_size` | R5b counterexample (hsz) | Classical.choice, Quot.sound, propext | `2e62a98360fdff225129cc371a810952c873bed4ea062120baf3199c38046642` | `88c71a7b98d847a7b87c044ff5af3aee497112d434694bf67468282f91d605f4` (217) |
| `Toy.Zc.ce_union_drop_fields_intoBytes` | R4a counterexample ((right side) every field IntoBytes); R4b counterexample (hF) | Classical.choice, Quot.sound, propext | `925c385cba17a5562d6a29d2c85a3896675f76dc01a5aa3e0b4746325c901725` | `f3044d6ce7f6baf2d44f5ff71606f457450be1b5c27bf13fcecb0caab4ac633a` (215) |
| `Toy.Zc.ce_union_drop_full_size` | R4a counterexample ((right side) every field has the union's size); R4b counterexample (hP) | Classical.choice, Quot.sound, propext | `bd2a718e5d1b0c61888eeca6afffdf9a2884dabd1c408a572b1e71b269c9977b` | `f3044d6ce7f6baf2d44f5ff71606f457450be1b5c27bf13fcecb0caab4ac633a` (215) |
| `Toy.Zc.ce_union_iff_drop_inhabited` | R4a counterexample (hInh) | Classical.choice, Quot.sound, propext | `f7801f896946a3feeed209ce31c6d223f012e893f0baf46fe9e3984bcaedee6e` | `e3ab16d33947638c1267d7eb352ac9dac69c12a204305fcf06b3e03e1d9e43a2` (212) |
| `Toy.Zc.ce_vccm_drop_align_pos` | R6a counterexample (hA) | none | `e905e620a1ef9e5bd3c63fb9f7751b4942ba065826aeac62e317dc7bcda80d9b` | `819196d3809b3edaec4d22da90a0415e27700a76a2bb2909c8746ea331e24418` (40) |
| `Toy.Zc.ce_vccm_drop_aligned` | R6a counterexample (hAl) | none | `272e327b1f3afd64b870cfb311cb8a0d19a0243644031dc39b5fbc97d5f0cf79` | `14f2b83dad48f39585aff1b8d1ff2b86d950bb35688d44b6124ae461ba0b53b0` (40) |
| `Toy.Zc.ce_vccm_drop_elem_pos` | R6a counterexample (hE) | none | `6f878cd523add3fe7b201bb3729fba517e0d6ffc673a26e4ea33101aff83ab56` | `6ad3b48e2a26b013f9bc7330779caf95055e367e7f6a31cc9bf8de9bc7c35bcf` (36) |
| `Toy.Zc.ce_vccm_drop_phase_lt` | R6a counterexample (hP) | none | `7839ee147c5e8f378279c25e3fb39cda06e1bf6c636a143997a62d633080e694` | `819196d3809b3edaec4d22da90a0415e27700a76a2bb2909c8746ea331e24418` (40) |
| `Toy.Zc.ce_vccm_normalizeDst_drop_aligned` | R6c counterexample (hAl) | propext | `77915dcb4c1c98716740d233a8e71e4a058019e907c8f0d4d23b20a94b177877` | `352e5d45351b906b5870e79fb5812e1e226438c574e4635080e09e543841d51c` (73) |
| `Toy.Zc.ce_vccm_start_drop_dvd_align` | R6d counterexample (hdA) | propext | `e0fe54e9312af71496631f7500bbd186c728ab34e1620756577ace8a84713b45` | `ca2cc57f3868018f47242c7c3e6081107f580e8f5ec2fb1fb1e024488e1367b4` (37) |
| `Toy.Zc.ce_vccm_start_drop_dvd_base` | R6d counterexample (hdB) | propext | `d7f6675b036e5fa8321bf175634943b335b860fee8a956ab01cb1e4ea46a9903` | `ca2cc57f3868018f47242c7c3e6081107f580e8f5ec2fb1fb1e024488e1367b4` (37) |
| `Toy.Zc.ce_vccm_start_drop_ok` | R6d counterexample (hok) | propext | `dae6475d99adaa72462d0300e2ada46045733a21fff1f007c43db522ccf72f7f` | `b593536989d9644332c5610c8dc212e683426f19da287e41c73b12d733736a3f` (38) |
| `Toy.Zc.derive_fromBytes_sound_of_wf` | R2e result | Classical.choice, Quot.sound, propext | `aa98c33f6ed07bc80e66789a3dc2f8c8b779b3f6669e7e421c281ba5a15fbc8b` | `99e2d122acf0f2d89838787ec6e535512d7873a1f445d8a18fd37b152d9aea2f` (254) |
| `Toy.Zc.derive_fromZeros_sound_of_wf` | R2e result | Classical.choice, Quot.sound, propext | `365d7ade4acec932cd7db64fc760012c961ae0dad93fd3c7a4ccbd6b13fbcef4` | `924b6609146a1c70e6bc2fa14bafa8518103080448fa8ac48aac09b3ed0447ac` (240) |
| `Toy.Zc.derive_intoBytes_sound_of_wf` | R2e result | Classical.choice, Quot.sound, propext | `f5eb2ae2683976dc16a8a3be1b3ea7f028dfd2332634791e499ce65708d55d14` | `1502e87740eda3b46639251cd98ab65341387a52be4b09126bb7c37f2761f267` (252) |
| `Toy.Zc.derive_isSafe_eq_validInit_of_wf_of_length` | R2f result | Classical.choice, Quot.sound, propext | `957d26e0b80af494e5f1a066872e393c946bd31500dc6e76f873022fe4eaeae1` | `72cf1f2dad180bebe4cda2a9d8b8e008f47e60f7153e58f83711aea766289644` (223) |
| `Toy.Zc.derive_unaligned_sound` | R2e result | Quot.sound, propext | `b2d7edc95748b81e17c4834503500b3f3a5e70009f092fb153de610fe76e453a` | `8e31c2ea1c26261923831267496b7b86a8956f6e52b500f258e0b96d4d102aca` (133) |
| `Toy.Zc.desc_transmute_total_of_size_eq` | R5b result | Classical.choice, Quot.sound, propext | `9ce1bc5c56b55291bd515751c36229b0e1a005095c05ca7bf24e3d2310c07be8` | `c514fc384074e409a15f6ddb2b60b2b2c9bbb4e7484c2017baa2fc7f6d87ac3e` (215) |
| `Toy.Zc.desc_transmute_total_of_size_ge` | R5b result | Classical.choice, Quot.sound, propext | `de22dc7673f0682defdc8016f91297ef3260b1513cf721aeec2a07ee0b2bae84` | `c514fc384074e409a15f6ddb2b60b2b2c9bbb4e7484c2017baa2fc7f6d87ac3e` (215) |
| `Toy.Zc.enum_fromBytes_of_count_check` | R3c result | Classical.choice, Quot.sound, propext | `95444f30a9fef4add7f5ad7690a2fcf8733c39e57aec32463461fe36df8cea29` | `a49533e5368c2e72ecaadd10efe1e1b2ab1a28987212c254e1fccccb3cd9318f` (227) |
| `Toy.Zc.enum_fromZeros_iff_zero_variant_fields_fromZeros_of_discrsWF` | R3d result | Classical.choice, Quot.sound, propext | `5f7d943d5eef9446a0968cc15d599fe4143d5eb652b780c0491e9724ba90fd5e` | `657c190c45a93e107a87982d9f56548ba45b6946d144edab76b601f6b01d09a8` (219) |
| `Toy.Zc.enum_fromZeros_of_findZeroVariant` | R3e result | Classical.choice, Quot.sound, propext | `41dfd3aa5aac18797c0476317cfa8191ca1d85bd862aadb05ab983559fa4b4da` | `72c3f9b17428125ab2ba91f357f5f92bb5e8bde22d828ed5b399786313693837` (225) |
| `Toy.Zc.enum_intoBytes_of_fields_of_padding_check` | R3g result | Classical.choice, Quot.sound, propext | `b493bbed7ebb08b29e778368d1576f1249a46068dc2b0c01365b9dce9a35278b` | `0a166404755563578f7a6bd205ba570e15b89afd07a5bec45ef40755a878757e` (212) |
| `Toy.Zc.enum_validInit_iff_first_matching_variant_valid` | R3f result | Classical.choice, Quot.sound, propext | `406426ae71d6b72ef4ba6c6046cb5aaaf5ee7c8bb2f1cbad058968a7d6b3db4b` | `869734d58e3a96b0ec719b2cbbc962f019323e2136816c409d7136b24cf9805f` (193) |
| `Toy.Zc.enum_variant_count_check_sound` | R3b result | Classical.choice, Quot.sound, propext | `cfba5aba54ddef3e2478c918fac66ad422abbdfdb30d4f9129d548cd5e822a2e` | `65dfc3304fa82d12be540f443aa5b6ac338ac9c3a67a575bc4163c506f33eb6a` (69) |
| `Toy.Zc.fieldless_enum_fromBytes_iff_every_tag_is_discriminant` | R3a result | Classical.choice, Quot.sound, propext | `cc87da533596fcfb3e26bccc8e63e8b163806016e6ca7525bd3eba5df97bb255` | `17af8aba627aabc353348831928dd16b6a04a6d5fcec15c5499a8e128b2a8e8b` (211) |
| `Toy.Zc.findZeroVariant_complete_of_no_unknown` | R3e result | Quot.sound, propext | `9727c46f410011bf9df2ad0cfb94709d1430a0d12573e5a22ed97052de7c9ac8` | `b6b7952b655bb5cb55d2c1e0cfe2f0e22cca20c16e6542d5319164dfc0c3e746` (18) |
| `Toy.Zc.findZeroVariant_incomplete_with_unknown` | R3e counterexample (h (findZeroVariant ds = error false)) | Quot.sound, propext | `793ecbc7b812d766c5f08a735e2fbe27f5ea1dc6a425960962f39590dcb06a84` | `1b9a61bdf2c088a438a41f04a01eb986c5117e5ad26b03e430c7ae6f54dff92e` (222) |
| `Toy.Zc.findZeroVariant_sound` | R3e result | Quot.sound, propext | `6592a8ba79b7aa98ecc519c50f4960424951bccec543c1eff45514e09db99224` | `b6b7952b655bb5cb55d2c1e0cfe2f0e22cca20c16e6542d5319164dfc0c3e746` (18) |
| `Toy.Zc.immutable_not_byte_determined` | R7a result | propext | `840d514b8bcef083a1a6b142fef5ccb5b16130b8c9b0558a43a6c301049e7034` | `0edccc903a77ca53139029e7dd582e45b46e41fb1ee4152afd5285f33bc9992d` (207) |
| `Toy.Zc.isSafe_enm_eq_validInit` | R3f result | Classical.choice, Quot.sound, propext | `344fd1a9f2916991928d2ec551fc509881c4500e380e0f9e769f689bb46a857e` | `5d1c61131f529405fc5776dcd355159cf0a041ef7861b4ffb5a5a7d6db45e729` (215) |
| `Toy.Zc.normalizeDst_align_dvd` | R6d non-vacuity | Quot.sound, propext | `bc91fd55ea91ea43b2f5ed70d3f7b50fb76c3905301718257c74bcf9220e6d85` | `e42d7b260b9d02fa1f6e921551540e7f777d0051e1a0545d5a1c54fdcc3eb1bc` (33) |
| `Toy.Zc.normalizeDst_sizeForElems_eq_dstSize` | R6b result | Quot.sound, propext | `c2e9490e4544d4320a859466ff5257f5b6ceb2308d079a32a0b07e3184ecb670` | `4b9bdb5e41e8cf01f93dea3ae458fa958bc4c051a775e548a9fa309f1e6dcaae` (37) |
| `Toy.Zc.nv_derive_isSafe` | R2f non-vacuity | propext | `c0c31b3415bea5ccedf38b966f7620a51fd7de2c614833d7f699608703b7b985` | `71783b2619e5ffddd1198fde0fe0f4eaff86f8f05dcf2d118bc8611581d10443` (137) |
| `Toy.Zc.nv_derive_sound` | R2e non-vacuity | propext | `668fe0c3ca25d20356ac405d029592f860a1dab6ed808cdb3524c2e6c609b49b` | `046035e72c2ac04106f68bec2c9bd05ce80a14e151c72e10aad52a1c5dc42c26` (205) |
| `Toy.Zc.nv_desc_transmute` | R5b non-vacuity | Classical.choice, Quot.sound, propext | `656d999c07ba4d03fcf469a443588539687539e7afac148b72f935d46e5bd918` | `29f08152d75feae5378abb69ad3298dae8a924b46a3c9e031c5c6699363afc47` (215) |
| `Toy.Zc.nv_enum_fromBytes_data` | R3c non-vacuity | Classical.choice, Quot.sound, propext | `a65224d5a17e979dd1b2936d7425af2c91f33666b2dfedeabdc72327019c743d` | `75d592b1768a97cf58a67707fb701031925c29e362b4f60f35b81df3eb8f0089` (228) |
| `Toy.Zc.nv_enum_fromZeros` | R3d non-vacuity | Classical.choice, Quot.sound, propext | `91b7e6a0f3dd9fb49c055d5b2492b673917aaa2530d0da310f3ed9dcf6ddf7ac` | `8793e5ed9f1b0b38fb5c14c75caff5c253ca4721e2636c3d08734758e9099b3f` (226) |
| `Toy.Zc.nv_enum_fromZeros_of_findZeroVariant` | R3e non-vacuity | Classical.choice, Quot.sound, propext | `31eb1f9e6fb397c6bf0963af79497ad2628a0b77034e8c803333e52892a50b6c` | `8793e5ed9f1b0b38fb5c14c75caff5c253ca4721e2636c3d08734758e9099b3f` (226) |
| `Toy.Zc.nv_enum_intoBytes` | R3g non-vacuity | Classical.choice, Quot.sound, propext | `22216583285af769d654694000fda05f3fa9c561212df9c990902e65b0e286b4` | `ca5ab58f42f0ed7c3c73534b75f9d44a8a22e6f9cc03e98422d3364f29b89369` (213) |
| `Toy.Zc.nv_enum_validInit` | R3f non-vacuity | Classical.choice, Quot.sound, propext | `69b8773ac49f9ed35006f3f459f7a5c43b9386413957bfa24729c5493285a44b` | `71280250604503f8f9d4fd392ec123fe9af6a3700db106ce3cd79764ed1001c6` (216) |
| `Toy.Zc.nv_fieldless_full_u8` | R3a non-vacuity; R3b non-vacuity | propext | `1c03d9b186b7988923c550d69d8db2bb96d85245803df930c04c0176fa182d2b` | `cabd2711c2cc820955a9195058737b052f435f7aa759bc2592e94b6932ca163c` (98) |
| `Toy.Zc.nv_findZeroVariant` | R3e non-vacuity | none | `c3f0d9342db5dde8353eff286d3d7bcbba231b0611ea0b3303b511312f5224d8` | `87e5d51505f1acad0456fe08ad0a0b54679eb881acf1df201acafb6e5eb5fb72` (13) |
| `Toy.Zc.nv_immutable_witness` | R7a non-vacuity | propext | `b5fae821a63700d919162b0acc4cd59843e886394b57b8adafc7afc8494f7ee0` | `66203f227d52dd91142ab15ab9c06818c9d5af47c006fcce8dae0b5eca0c8f19` (207) |
| `Toy.Zc.nv_normalizeDst` | R6b non-vacuity | none | `c2ce4f33ba975e70ea9e14ee8308b554c81afa36701931923accd2875d6a00c2` | `615ad3a785ef4b2b5f467b3c8d4028b3ea7c72059e0b8b4558d073127fcf581c` (38) |
| `Toy.Zc.nv_structPaddingOK` | R2d non-vacuity | propext | `43f253716e1f57dca6aae0f3abb49d6c4ccd1d63034327bc4c3efd46025eeedd` | `7e83224bad3b8d71cbbdb31082d0098a4664720a8100538cfa2c8a81b2822c19` (149) |
| `Toy.Zc.nv_struct_fromBytes_fromZeros_padded` | R2a non-vacuity | Classical.choice, Quot.sound, propext | `c645878a2523fc506cf21e834cc20100676dc95ec3e3435a2b00195b32c325a1` | `266decedf7c97bf9f28c5e2ef93764ebb163796026a520a7496f71faffc6947d` (217) |
| `Toy.Zc.nv_struct_intoBytes` | R2c non-vacuity | Classical.choice, Quot.sound, propext | `1f98a81cbf15fd574294448e0c6f689ae21bb8756979bbb4f93ecba41e2f76a4` | `1cfc99364a1f52e44d8b52a5dae50f3d9f1fd37e547d720d0c6adf456d11192a` (215) |
| `Toy.Zc.nv_transmuteTotal_rep` | R5a non-vacuity | Classical.choice, Quot.sound, propext | `92f16b40e6b603a38126098ab8a19e8410bc40dc812b7560b182aaa0869aaed4` | `001840d5f7157cb2f1bee2c0e569ac842ac3be46de2a1595482b8ce7051515ee` (211) |
| `Toy.Zc.nv_union_intoBytes` | R4a non-vacuity; R4b non-vacuity | Classical.choice, Quot.sound, propext | `78839a0ba63f19ac0249ba016bfa633bd006de2559b550752dcfaddb4e240c5f` | `6606418794579ccfde428f21b2040f2f009f3aadfd04166a5a08b8e5fa55852d` (237) |
| `Toy.Zc.nv_vccm_normalizeDst` | R6c non-vacuity | propext | `a891e61c0e299c39991a3bb673c295048726f2d69c69605862f310327677f6bc` | `352e5d45351b906b5870e79fb5812e1e226438c574e4635080e09e543841d51c` (73) |
| `Toy.Zc.nv_vccm_sliceDst` | R6a non-vacuity | none | `23b7bc4c0a18822132f62e4101747669c6a7009bf6afeb96d5fbfe9c4802bd67` | `2c464f8a6c277b35f000bcc908b234fcea12842ab37ac37f82ad585cd080a827` (37) |
| `Toy.Zc.nv_vccm_start_aligned` | R6d non-vacuity | propext | `cfa8caba49dc16caf55bad66385377a285f711c70b2bfd3ffdc1059ecde6f985` | `42d6096df8404342e45a11ae79538137dfb4cc8dd061c369600a1f2e4a975140` (67) |
| `Toy.Zc.pc_fromBytes_byte_determined` | R7a positive control | Classical.choice, Quot.sound, propext | `e7b815fd3475fa5201d63755c4401a6626162a10f48cad27b74ade5f40bfcad2` | `6e7b21b796f59785bc9eee5e6fd72f5dff6c950abd0e22e590b9072de87ab788` (212) |
| `Toy.Zc.pc_written_union_intoBytes` | R4d non-vacuity; R4d positive control | Classical.choice, Quot.sound, propext | `06c7be8533058fc3a68498e417807380a1f94ad4801e4d9a3384b0c96097e5ed` | `043524c3f77ee8f7d921bae2009cbb4b29da9e221fac120609a9e894ebf48784` (236) |
| `Toy.Zc.permissive_union_validity_of_size_pos_not_intoBytes` | R4d result | Quot.sound, propext | `c6bb47129765ab908c6fd4268ec0eedc734bdef3908db012b17131412a7149af` | `ac2c8758e567aa86efd4c72bc76889c5d6757dd7db5b2e59c3dec692c3971e8e` (122) |
| `Toy.Zc.semFromBytes_iff_validInit_total` | R1 result | Classical.choice, Quot.sound, propext | `092fc06ce0d5fcede384d8b90e3b5704eaedeac51f809d04b5eef0314212198e` | `c6a56cf119b69f6e7e543f15a691bb4c9067a09cf64cb4665adf6d52bf61c935` (211) |
| `Toy.Zc.semFromBytes_int` | R1 non-vacuity | Classical.choice, Quot.sound, propext | `cbf284277686c05c2ade1a6402b7b2fa78f88461d45a4d20d550bba15fda8918` | `b29bb1db64f191f5c9e6d2cbabbd3ec94d77813ca73e731032c454103ed401d9` (210) |
| `Toy.Zc.semFromZeros_iff_validInit_zeros` | R1 result | Quot.sound, propext | `140a9b752d21c9e1130c07a2df54a0932d1a8a6631b9ec3e3dc7c24b28904f78` | `c6411098b53c33285af18bedb2601b58aedd7c77302738897497f05737f6ec96` (209) |
| `Toy.Zc.semFromZeros_int` | R1 non-vacuity | Classical.choice, Quot.sound, propext | `762ed6ed44a106301f3188dace6775de32f1d995f5556c1dd35e3ef0cd45d81c` | `3d67142a367e0016d71b4107d66b256b194a2605389ce242fa06f27d284ece42` (208) |
| `Toy.Zc.semIntoBytes_iff_encodeL_init` | R1 result | Classical.choice, Quot.sound, propext | `e2bf169f94a2de3a1d0decc440ba97e3df7c6bf442988f567786b84d3464834f` | `a8a5876af93016ef73e21c2e06c8fb6582bcfa163c496d79ce5c0dabf6aef81a` (210) |
| `Toy.Zc.semIntoBytes_int` | R1 non-vacuity | Classical.choice, Quot.sound, propext | `e4362ddef79aab99423ea87f4a1e8484f9a309c1fbfac529a954629a634c4c42` | `a8a5876af93016ef73e21c2e06c8fb6582bcfa163c496d79ce5c0dabf6aef81a` (210) |
| `Toy.Zc.structPaddingOK_sound` | R2d result | Classical.choice, Quot.sound, propext | `6f2b57efffd9c62501bc15b1dd2b9456020ddb61d4ce0bfd8ec95e568a9879d4` | `493850e850cc118bf86e139dadddf5073c55f2f6bca547814f30dc38aa9b3838` (146) |
| `Toy.Zc.struct_fromBytes_iff_fields_fromBytes` | R2a result | Classical.choice, Quot.sound, propext | `aadf72fd07886e4a28a183c6175fee3952b496e1877d92414e8cbd65857aac24` | `b29bb1db64f191f5c9e6d2cbabbd3ec94d77813ca73e731032c454103ed401d9` (210) |
| `Toy.Zc.struct_fromZeros_iff_fields_fromZeros` | R2a result | Classical.choice, Quot.sound, propext | `f0d278589096d9fad09745b6db9f8d880a82f6f5a18fa63e3a1a8ab4e408a57d` | `3d67142a367e0016d71b4107d66b256b194a2605389ce242fa06f27d284ece42` (208) |
| `Toy.Zc.struct_intoBytes_iff_fields_intoBytes_no_padding_of_inhabited` | R2c result | Classical.choice, Quot.sound, propext | `7416c9734930f1c43fc57d6a04792e7946756a95dd8933ca5ecf3f31a9dfea07` | `1ce23f8f71a41f124cc98323c9e28bf2f55f30f1a6719ae13140e9ead24b2fad` (212) |
| `Toy.Zc.transmuteTotal_of_intoBytes_of_fromBytes` | R5a result | propext | `cad4af01bcc49ae15d69a03737a49429e84a1f738960ebe810428ca277b27662` | `88884d44fce696a9960790633d1a89aa2931323658ac86edeb67f440a3150cf5` (17) |
| `Toy.Zc.unaligned_check_conjuncts_necessary` | R7c result; R7c non-vacuity | propext | `0d00c78de84a711d664a027207bb53d716d7e469027b627cd48f4100f0c109e7` | `ff35b06bfcc6687d388584ef3bef174c41787347e603f33728f808585d2de80d` (141) |
| `Toy.Zc.union_fromBytes_derive_not_necessary` | R7b result; R7b non-vacuity | Classical.choice, Quot.sound, propext | `31658c04a59cbecd1755f993e1e66d75708876a136d5911bd45f89f32ae309c2` | `8fe9db267c09e006a2f12324bdd5aed205a22268c7bf5677a963b252f4c6a902` (238) |
| `Toy.Zc.union_fromZeros_derive_not_necessary` | R7b result | Quot.sound, propext | `184f04e12c335787dd5f5ab586bea53f1d2b6bcc4791353e1028b462bfce6dc8` | `ec9f10f4deccea2c4deda466458db453490d1a5d6c349da002917e0cb0af61be` (224) |
| `Toy.Zc.union_intoBytes_iff_fields_intoBytes_full_size_of_inhabited` | R4a result | Classical.choice, Quot.sound, propext | `299d0ddef64b1d7d84c81c1e755a4b677d535a88804791c09a52b758e53e21f5` | `c65f023a29bd0b12096c5b48cfec54b9c91b0928293c5918a5445427d4913cc8` (211) |
| `Toy.Zc.union_intoBytes_of_fields_of_padding_check` | R4b result | Classical.choice, Quot.sound, propext | `d09fbd77dc3f5e87f9e34e9dbdf87b321c210792411f83d948b764830adcc91f` | `964a4904afb26e3b22752e50d905260d52732a2f85dd353fbe24834851fd7ead` (212) |
| `Toy.Zc.union_u8_u16_written_through_u8_leaves_uninit` | R4c result; R4c non-vacuity | Classical.choice, Quot.sound, propext | `cbefe559285820c2272083b160199e48065a3be38098f83618c6ccf641ffa843` | `99834c92a976015996a3b2e9fc99d6790b85763b340e5612b9a1255cb9343581` (212) |
| `Toy.Zc.vccm_normalizeDst_elems_eq_maxSliceElems_of_aligned` | R6c result | Classical.choice, Quot.sound, propext | `ea14765a7e817ed038ab6e6d87bb70422b916662cb9ff102f7995e95c5b8129c` | `e251b4a523eaf46f8b5e3955a2be3cba16666975852f373d966c040b4f05ff73` (72) |
| `Toy.Zc.vccm_sliceDst_returns_max_fitting_elems` | R6a result | Classical.choice, Quot.sound, propext | `b4363af099c42b5362b31fbece3de57b602ce4ab20cf57c613ed5e3dba4a6077` | `682685b3b213b1783a29174d749a3115ab0beaed3d14608c9f1ac343b6c9e7b8` (45) |
| `Toy.Zc.vccm_sliceDst_start_aligned_of_align_dvd` | R6d result | Quot.sound, propext | `4e1f8b1cddb9d6f9e9c6df7312a783753ab066b1e43b10696133888ecf9d9ade` | `ca2cc57f3868018f47242c7c3e6081107f580e8f5ec2fb1fb1e024488e1367b4` (37) |

The additional observation `Toy.Zc.fromBytes_enum_rejected_by_findZeroVariant` (cited in the R3c non-claims) uses the axioms: Classical.choice, Quot.sound, propext.

**Primary sources** (the commit and tag records below and the DOI records were re-checked on 2026-11-20):

* zerocopy: repository `google/zerocopy`, tag `v0.8.63` (annotated tag object `1092386b65969d18bd37750b5ebe74bcd34cabf1`), commit `c55af491426ef53f35fb8c6e83f220fa07712e66`. The files and line ranges used are quoted in the source-fidelity table and in each card: `zerocopy/zerocopy-derive/src/derive/{from_bytes,into_bytes,try_from_bytes,unaligned,mod}.rs`, `zerocopy/zerocopy-derive/src/{repr,util}.rs`, `zerocopy/src/{lib,impls,macros,layout}.rs`, `zerocopy/src/util/{mod,macro_util}.rs`.
* Lean 4: repository `leanprover/lean4`, tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
* MiniRust: repository `minirust/minirust`, commit `063d784186d3252bee242217f218223205c0b568`, `spec/lang/representation.md`.
* Rust: repository `rust-lang/rust`, commit `6905905bb7727fd0f9223f5fdc9ad4e62236d5a2`, `library/core/src/mem/transmutability.rs` lines 14-59 (`TransmuteFrom`, unstable, tracking issue 99571) and `compiler/rustc_transmute/src/maybe_transmutable/mod.rs` line 187.
* The Rust Reference 1.81.0, "Type layout", https://doc.rust-lang.org/1.81.0/reference/type-layout.html
* RFC 2195 "Really Tagged Unions" (`text/2195-really-tagged-unions.md`) and RFC 2835 "Project Safe Transmute" (`text/2835-project-safe-transmute.md`): repository `rust-lang/rfcs`, commit `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4` (the most recent commit touching either file when checked on 2026-11-20); rendered at https://rust-lang.github.io/rfcs/2195-really-tagged-unions.html and https://rust-lang.github.io/rfcs/2835-project-safe-transmute.html, which are moving pages.
* X. Leroy, S. Blazy, "Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations", Journal of Automated Reasoning, 2008, DOI 10.1007/s10817-008-9099-0.
* H. Tuch, G. Klein, M. Norrish, "Types, Bytes, and Separation Logic", POPL 2007, DOI 10.1145/1190216.1190234.
* K. Memarian et al., "Exploring C Semantics and Pointer Provenance", PACMPL 3 (POPL), 2019, DOI 10.1145/3290380.
* T. Ramananandro, G. Dos Reis, X. Leroy, "Formal Verification of Object Layout for C++ Multiple Inheritance", POPL 2011, DOI 10.1145/1926385.1926395.
* R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, "RustBelt: Securing the Foundations of the Rust Programming Language", PACMPL 2 (POPL), 2018, DOI 10.1145/3158154.
* L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, "RefinedRust: A Type System for High-Assurance Verification of Rust Programs", PACMPL 8 (PLDI), 2024, DOI 10.1145/3656422.
* R. Krebbers, "The C Standard Formalized in Coq", PhD thesis, Radboud University Nijmegen, 2015, https://hdl.handle.net/2066/147182
* M. Brecknell et al., "AutoCorres2", Archive of Formal Proofs, April 2024, https://isa-afp.org/entries/AutoCorres2.html; earliest release archive listed on that page: `afp-AutoCorres2-2024-05-26` (Isabelle2024). Limitation: the entry page is a moving document, and no content hash of the release archive is recorded here. AutoCorres2 is cited as prior art for comparison only; no result depends on it.

Issue and discussion threads (zerocopy issue 1792 and Discussion 696; Unsafe Code Guidelines issues 174, 438 and 533) are cited in the cards as background for design choices only. No claim in this report rests on them.

## Revalidation

Requirements: `elan`, which selects the toolchain pinned in `lean/lean-toolchain`, and `python3`.
No network access is needed beyond the toolchain download.

Primary check, run from the package directory:

```sh
python3 support/revalidate.py .
```

The script never modifies the package. It copies `lean/` to a temporary directory, runs `lake build`,
and checks that no Lean source contains `sorry`, `admit` or `native_decide`, or declares an `axiom`.
It then generates and runs a small Lean program that computes, with Lean's `collectAxioms`, the axioms
of every declaration of the `ToyZc` library and fails if any declaration uses an axiom other than
`propext`, `Classical.choice` or `Quot.sound`. For every Lean name referenced by `results.json`, it
recomputes the statement hash and the closure hash described under Evidence and compares them with
`audit/statements.json`. It prints `REVALIDATED` on success. The script's docstring states exactly
what is hashed.

Manual check of the build and the axioms of every card-referenced declaration:

```sh
cd lean
lake build
lake env lean AxiomAudit.lean    # prints `#print axioms` for every name referenced by results.json
```

To check whether the bridges still hold for a newer zerocopy revision, diff the regions quoted in the
source-fidelity table between `c55af491426ef53f35fb8c6e83f220fa07712e66` and the new revision:
`zerocopy/zerocopy-derive/src/derive/{from_bytes,into_bytes,try_from_bytes,unaligned,mod}.rs`,
`zerocopy/zerocopy-derive/src/{repr,util}.rs`, `zerocopy/src/util/macro_util.rs` (padding macros),
`zerocopy/src/impls.rs` (primitive impls), `zerocopy/src/macros.rs` (`transmute!`), and
`zerocopy/src/layout.rs` (`validate_cast_and_convert_metadata`, `TrailingSliceLayout`). If a quoted
condition changed, the corresponding Lean check (`Toy.Zc.impl*`, `structPaddingOK`, `enumPaddingOK`,
`unionPaddingOK`, `findZeroVariant`, `isSafe`, `vccm`) must be updated and the affected results
re-proved. A passing `revalidate.py` run establishes the kernel facts only, not the bridges.
