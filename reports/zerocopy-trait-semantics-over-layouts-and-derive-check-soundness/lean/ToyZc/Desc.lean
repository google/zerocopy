import ToyZc.Layout

/-!
# Type descriptions, their layouts, and their byte representations

This module defines the type-description AST of the package and its semantics.

* `Desc`: primitive integers (`IntTy`), `bool`, arrays `[T; n]`, structs with
  `repr(C)` (optionally `packed(N)` or `align(N)`) or `repr(transparent)`, enums with
  `repr(C)` or `repr(Int)` (fieldless or data-carrying; discriminants given syntactically,
  `DiscrSyn`), `repr(C)` unions (optionally `packed(N)` / `align(N)`), and `UnsafeCell<T>`
  (`cell`, used only to show that `Immutable` is not a byte-level property).
* `Desc.layout`: the `repr(C)` layout of every description, computed with the
  `reprCStruct`, `reprCEnum`, `reprIntEnum`, and `unionLayout`.
* `Val`, `Desc.hasType`: a universal value type and the typing judgment.
* `Desc.encodeL` / `Desc.decodeL`: list-level encoder and decoder over abstract bytes.
* `Desc.rep`: the semantic interpretation of a description as a representation
  `Rep (Bytes Byte d.size) (TVal d)` in the sense of the byte-representation vocabulary of `ToyZc.Basic`.
* `SemFromZeros`, `SemFromBytes`, `SemIntoBytes`, `validInit`, `SemUnaligned`: the semantic
  trait predicates.

## Modeling choices (simplifications)

* No generics. Every description is a concrete, closed type; consequently zerocopy's
  `IntoBytes` struct derive always takes the "no generics: emit a padding check" path.
* No slice DSTs inside `Desc` (slice-tailed DSTs are modeled separately in
  `ToyZc.KnownLayout`). In particular zerocopy's `PaddingCheck::ReprCStruct` is not modeled.
* No `repr(Rust)` (default representation) types, no `repr(packed)` without `C`, no
  `repr(C, Int)` enums (zerocopy rejects that combination), no `align(N)` on enums,
  no `repr(transparent)` unions.
* Primitives: exactly `u8, i8, u16, i16, u32, i32, u64, i64` and `bool` (no `u128`/`i128`,
  `usize`/`isize`, floats, `char`, `NonZero*`, tuples, `PhantomData`, `ManuallyDrop`, references or
  pointers).
* Target assumptions (modeled on `x86_64-unknown-linux-gnu`): integers are little-endian and
  integer alignment equals integer size. A `repr(C)` enum always has a 4-byte tag holding an
  `i32`-range discriminant; descriptions whose `repr(C)` discriminants do not fit in `i32` are
  excluded by `Desc.wf`, so `repr(C)` enums with other tag sizes are not modeled.
* Discriminants are given syntactically (`DiscrSyn`) so that zerocopy's syntactic
  `find_zero_variant` can be modeled faithfully; `other v` stands for a discriminant
  expression that is not an (optionally negated) integer literal and that the compiler
  evaluates to `v`.
* Union values are values *written through one field* (`Val.union j v`): the encoding writes
  field `j`'s encoding at offset `0` and leaves the remaining bytes `uninit`. Decoding accepts
  the bytes if *some* field decodes the corresponding prefix, returning the first such field (this
  is exactly the conservative rule of zerocopy's derived union validator,
  `zerocopy/zerocopy-derive/src/derive/try_from_bytes.rs:292-296`; Rust has not settled union
  validity). Consequently `Desc.rep` on unions is not canonical: decoding then encoding can forget
  bytes, and decoding is not monotone in definedness (`union_decode_encode_forgets_bytes`,
  `union_decode_not_monotone`). Values produced by successive writes through different fields
  are not distinct values of the model. `ToyZc.Union` contrasts this with a permissive union
  validity.
* Field invariants (`#[zerocopy(invariant)]`), `Immutable`'s interior-mutability semantics,
  pointer provenance, and floating-point types are not modeled.
-/

namespace Toy.Zc

/-! ## The AST -/

/-- Primitive integer types (`u8`, `i8`, …, `u64`, `i64`). -/
inductive IntTy where
  | u8 | i8 | u16 | i16 | u32 | i32 | u64 | i64
  deriving DecidableEq, Repr

namespace IntTy

/-- Byte width of the integer type. -/
def width : IntTy → Nat
  | u8 | i8 => 1
  | u16 | i16 => 2
  | u32 | i32 => 4
  | u64 | i64 => 8

/-- Whether the integer type is signed. -/
def signed : IntTy → Bool
  | i8 | i16 | i32 | i64 => true
  | _ => false

/-- Least value of the integer type. -/
def minVal (t : IntTy) : Int :=
  if t.signed then -((2 : Int) ^ (8 * t.width - 1)) else 0

/-- Greatest value of the integer type. -/
def maxVal (t : IntTy) : Int :=
  if t.signed then (2 : Int) ^ (8 * t.width - 1) - 1 else (2 : Int) ^ (8 * t.width) - 1

end IntTy

theorem ex_IntTy_width_pos : IntTy.u16.width = 2 := rfl
theorem ex_IntTy_width_neg : IntTy.u16.width ≠ 1 := by decide
theorem ex_IntTy_range_pos : IntTy.i8.minVal = -128 ∧ IntTy.i8.maxVal = 127 := by decide
theorem ex_IntTy_range_neg : IntTy.u8.maxVal ≠ 127 := by decide

/-- The syntax of an enum variant's discriminant, as seen by a procedural macro:
* `implicit`: no `= expr` (the compiler uses the previous discriminant plus one, or `0` first);
* `lit n`: `= n` for an integer literal `n`;
* `negLit n`: `= -n` for an integer literal `n`;
* `other v`: any other expression (e.g. a constant or `1 + 1`); the compiler evaluates it to `v`,
  but a procedural macro cannot. -/
inductive DiscrSyn where
  | implicit
  | lit (n : Nat)
  | negLit (n : Nat)
  | other (value : Int)
  deriving DecidableEq, Repr

/-- Representations a struct can have in the model: `repr(C)` with an optional `packed(N)` or
`align(N)` modifier, or `repr(transparent)`. -/
inductive StructRepr where
  | c (m : ReprModifier)
  | transparent
  deriving DecidableEq, Repr

/-- Representations an enum can have in the model: `repr(C)` or `repr(Int)`. -/
inductive EnumRepr where
  | c
  | prim (t : IntTy)
  deriving DecidableEq, Repr

/-- Representations a union can have in the model: `repr(C)` with an optional modifier. -/
inductive UnionRepr where
  | c (m : ReprModifier)
  deriving DecidableEq, Repr

/-- The modifier of a union representation. -/
def UnionRepr.modifier : UnionRepr → ReprModifier
  | .c m => m

/-- The integer type that holds an enum's tag: the primitive for `repr(Int)`, and an `i32`-like
4-byte integer for `repr(C)` (`c_int` on the modeled target). -/
def EnumRepr.tagTy : EnumRepr → IntTy
  | .c => .i32
  | .prim t => t

/-- A closed (non-generic) Rust type description. Enum variants are pairs of a syntactic
discriminant and a list of field types. -/
inductive Desc where
  /-- A primitive integer. -/
  | int (t : IntTy)
  /-- `bool`. -/
  | bool
  /-- The array `[elem; n]`. -/
  | array (elem : Desc) (n : Nat)
  /-- A struct with representation `r` and the given field types (in declaration order). -/
  | strct (r : StructRepr) (fields : List Desc)
  /-- An enum with representation `r` and the given variants (in declaration order). -/
  | enm (r : EnumRepr) (variants : List (DiscrSyn × List Desc))
  /-- A union with representation `r` and the given field types. -/
  | union (r : UnionRepr) (fields : List Desc)
  /-- `UnsafeCell<inner>`: same layout and bytes as `inner`. -/
  | cell (inner : Desc)

/-! ## Layout -/

/-- Struct layout for a representation: `repr(C, m)` uses `reprCStruct m`; `repr(transparent)`
uses `reprCStruct .none`, which coincides with the transparent layout whenever at most one field is
not a 1-ZST (enforced by `Desc.wf`). -/
def StructRepr.layout : StructRepr → List FieldLayout → StructLayout
  | .c m, ls => reprCStruct m ls
  | .transparent, ls => reprCStruct .none ls

/-- Tag layout of an enum representation (integer alignment equals integer size). -/
def EnumRepr.tagLayout (r : EnumRepr) : FieldLayout := ⟨r.tagTy.width, r.tagTy.width⟩

/-- Enum layout: `reprCEnum` for `repr(C)`, `reprIntEnum` for `repr(Int)`. -/
def EnumRepr.layout (r : EnumRepr) (vls : List (List FieldLayout)) : EnumLayout :=
  match r with
  | .c => reprCEnum r.tagLayout vls
  | .prim _ => reprIntEnum r.tagLayout vls

mutual
/-- The `(size, align)` layout of a description. -/
def Desc.layout : Desc → FieldLayout
  | .int t => ⟨t.width, t.width⟩
  | .bool => ⟨1, 1⟩
  | .array e n => ⟨n * e.layout.size, e.layout.align⟩
  | .strct r fs => let L := r.layout (Desc.layouts fs); ⟨L.size, L.align⟩
  | .enm r vs => let E := r.layout (Desc.variantLayouts vs); ⟨E.size, E.align⟩
  | .union r fs => let U := unionLayout r.modifier (Desc.layouts fs); ⟨U.size, U.align⟩
  | .cell t => t.layout
/-- Layouts of a list of descriptions. -/
def Desc.layouts : List Desc → List FieldLayout
  | [] => []
  | f :: fs => f.layout :: Desc.layouts fs
/-- Field layouts of each variant. -/
def Desc.variantLayouts : List (DiscrSyn × List Desc) → List (List FieldLayout)
  | [] => []
  | (_, fs) :: vs => Desc.layouts fs :: Desc.variantLayouts vs
end

/-- Size in bytes of a description. -/
abbrev Desc.size (d : Desc) : Nat := d.layout.size

/-- Alignment of a description. -/
abbrev Desc.align (d : Desc) : Nat := d.layout.align

/-- Struct layout of a struct description's fields. -/
def Desc.structLayout (r : StructRepr) (fs : List Desc) : StructLayout := r.layout (Desc.layouts fs)

/-- Enum layout of an enum description. -/
def Desc.enumLayout (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : EnumLayout :=
  r.layout (Desc.variantLayouts vs)

/-- Union layout of a union description. -/
def Desc.unionLayout (r : UnionRepr) (fs : List Desc) : UnionLayout :=
  Toy.Zc.unionLayout r.modifier (Desc.layouts fs)

/-- Common descriptions. -/
abbrev Desc.u8 : Desc := .int .u8
abbrev Desc.u16 : Desc := .int .u16
abbrev Desc.u32 : Desc := .int .u32
abbrev Desc.i8 : Desc := .int .i8

theorem ex_layout_pos_padded_struct :
    (Desc.strct (.c .none) [.u8, .u16]).layout = ⟨4, 2⟩ := rfl
theorem ex_layout_pos_union : (Desc.union (.c .none) [.u8, .u16]).layout = ⟨2, 2⟩ := rfl
theorem ex_layout_pos_enum : (Desc.enm (.prim .u8) [(.implicit, [.u8]), (.implicit, [.u16])]).layout
    = ⟨4, 2⟩ := rfl
theorem ex_layout_neg_packed :
    (Desc.strct (.c (.packed 1)) [.u8, .u16]).layout ≠ ⟨4, 2⟩ := by decide

/-! ## Discriminants -/

/-- Rust's discriminant resolution: an implicit discriminant is the previous one plus one
(`0` for the first variant); literals denote themselves; `other v` denotes `v`. The argument
`nxt` is the value an implicit discriminant takes at this position. -/
def resolveAux : List DiscrSyn → Int → List Int
  | [], _ => []
  | d :: ds, nxt =>
    let v : Int := match d with
      | .implicit => nxt
      | .lit n => n
      | .negLit n => -(n : Int)
      | .other v => v
    v :: resolveAux ds (v + 1)

/-- Resolved discriminant values of a list of syntactic discriminants. -/
def resolveDiscrs (ds : List DiscrSyn) : List Int := resolveAux ds 0

theorem ex_resolveDiscrs_pos :
    resolveDiscrs [.implicit, .lit 5, .implicit, .negLit 2, .implicit] = [0, 5, 6, -2, -1] := rfl
theorem ex_resolveDiscrs_neg : resolveDiscrs [.lit 3, .implicit] ≠ [3, 1] := by decide

/-- The tag code (bit pattern read as an unsigned number) of discriminant `d` in a tag of type
`t`: `d mod 2^(8·width)` (two's complement for negative `d`). -/
def discrCode (t : IntTy) (d : Int) : Nat := (d % ((2 : Int) ^ (8 * t.width))).toNat

theorem ex_discrCode_pos : discrCode .i8 (-1) = 255 := by decide
theorem ex_discrCode_neg : discrCode .i8 (-1) ≠ 1 := by decide

/-- Resolved discriminants of an enum description's variants. -/
def Desc.discrs (vs : List (DiscrSyn × List Desc)) : List Int := resolveDiscrs (vs.map Prod.fst)

/-- Tag codes of an enum description's variants. -/
def Desc.codes (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : List Nat :=
  (Desc.discrs vs).map (discrCode r.tagTy)

/-- Little-endian encoding of `n` in `w` bytes (`n mod 256^w`). -/
def leBytes : Nat → Nat → List Byte
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

/-- Little-endian decoding of a byte list. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

theorem ex_leBytes_pos : leBytes 2 258 = [2, 1] := rfl
theorem ex_leNat_pos : leNat [2, 1] = 258 := rfl
theorem ex_leNat_neg : leNat [2, 1] ≠ 513 := by decide

/-! ## Well-formedness (the compiler rules the results depend on) -/

/-- Boolean power-of-two test (for arguments below `2^64`). -/
def isPow2 (n : Nat) : Bool := (List.range 64).any fun k => 2 ^ k == n

theorem ex_isPow2_pos : isPow2 8 = true := by decide
theorem ex_isPow2_neg : isPow2 6 = false := by decide

/-- A `packed(N)` / `align(N)` argument is a power of two (the compiler rejects others). -/
def ReprModifier.wf : ReprModifier → Bool
  | .none => true
  | .packed p => isPow2 p
  | .aligned n => isPow2 n

/-- Pairwise distinctness of a list of integers. -/
def nodupInt : List Int → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupInt xs

/-- The compiler's discriminant rules, as far as the model needs them: resolved discriminants
are pairwise distinct (error E0081) and representable in the tag type (overflow is an error;
for `repr(C)` the model additionally restricts to the `i32` range). -/
def discrsWF (r : EnumRepr) (ds : List DiscrSyn) : Bool :=
  let vals := resolveDiscrs ds
  nodupInt vals && vals.all fun v => decide (r.tagTy.minVal ≤ v ∧ v ≤ r.tagTy.maxVal)

theorem ex_discrsWF_pos : discrsWF (.prim .u8) [.implicit, .lit 255] = true := by decide
theorem ex_discrsWF_neg_dup : discrsWF (.prim .u8) [.lit 1, .implicit, .lit 2] = false := by
  decide
theorem ex_discrsWF_neg_range : discrsWF (.prim .u8) [.lit 256] = false := by decide

mutual
/-- **Well-formedness.** The compiler rules the results depend on: power-of-two modifiers,
at most one field of a `repr(transparent)` struct that is not a 1-ZST (size `0`, align `1`),
at least one variant per enum (a `repr` on a zero-variant enum is error E0084), at least one
field per union, and `discrsWF`. Other compiler rules (e.g. E0588, a `packed` type containing
an `align` type) are not enforced, so `wf` over-approximates the set of accepted types. -/
def Desc.wf : Desc → Bool
  | .int _ => true
  | .bool => true
  | .array e _ => e.wf
  | .strct (.c m) fs => m.wf && Desc.wfAll fs
  | .strct .transparent fs =>
      Desc.wfAll fs &&
        decide ((Desc.layouts fs).countP (fun l => !(l.size == 0 && l.align == 1)) ≤ 1)
  | .enm r vs => !vs.isEmpty && Desc.wfVariants vs && discrsWF r (vs.map Prod.fst)
  | .union (.c m) fs => !fs.isEmpty && m.wf && Desc.wfAll fs
  | .cell t => t.wf
/-- Well-formedness of every description in a list. -/
def Desc.wfAll : List Desc → Bool
  | [] => true
  | f :: fs => f.wf && Desc.wfAll fs
/-- Well-formedness of every field of every variant. -/
def Desc.wfVariants : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => Desc.wfAll fs && Desc.wfVariants vs
end

theorem ex_wf_pos : (Desc.strct .transparent [.strct (.c .none) [], .int .u32]).wf = true := by
  decide
theorem ex_wf_neg_transparent : (Desc.strct .transparent [.int .u8, .int .u16]).wf = false := by
  decide
theorem ex_wf_neg_empty_enum : (Desc.enm (.prim .u8) []).wf = false := by decide
theorem ex_wf_neg_dup_discr :
    (Desc.enm (.prim .u8) [(.lit 0, []), (.lit 0, [])]).wf = false := by decide

/-! ## Values and typing -/

/-- Universal values. Integers are represented by their little-endian bytes; enum values by
the variant's index (declaration order) and its field values; union values by the index of the
field they were written through and that field's value. A `cell` holds a value of its inner
type directly. -/
inductive Val where
  | int (bytes : List Byte)
  | bool (b : Bool)
  | array (elems : List Val)
  | strct (fields : List Val)
  | enm (variant : Nat) (fields : List Val)
  | union (field : Nat) (v : Val)

mutual
/-- Typing judgment: `v` is a value of the type described by `d`. -/
def Desc.hasType : Desc → Val → Bool
  | .int t, .int bs => bs.length == t.width
  | .bool, .bool _ => true
  | .array e n, .array vs => vs.length == n && vs.all (fun v => e.hasType v)
  | .strct _ fs, .strct vs => Desc.hasTypes fs vs
  | .enm _ vs, .enm i fvs => Desc.hasTypeVariant vs i fvs
  | .union _ fs, .union j v => Desc.hasTypeField fs j v
  | .cell t, v => t.hasType v
  | _, _ => false
/-- Pointwise typing of field values. -/
def Desc.hasTypes : List Desc → List Val → Bool
  | [], [] => true
  | f :: fs, v :: vs => f.hasType v && Desc.hasTypes fs vs
  | _, _ => false
/-- Typing of the fields of variant `i`. -/
def Desc.hasTypeVariant : List (DiscrSyn × List Desc) → Nat → List Val → Bool
  | (_, fs) :: _, 0, fvs => Desc.hasTypes fs fvs
  | _ :: vs, i + 1, fvs => Desc.hasTypeVariant vs i fvs
  | [], _, _ => false
/-- Typing of a union value written through field `j`. -/
def Desc.hasTypeField : List Desc → Nat → Val → Bool
  | f :: _, 0, v => f.hasType v
  | _ :: fs, j + 1, v => Desc.hasTypeField fs j v
  | [], _, _ => false
end

/-- Values of the type described by `d`. -/
abbrev TVal (d : Desc) := {v : Val // d.hasType v = true}

/-- `d` describes an inhabited type. -/
def Desc.Inhabited (d : Desc) : Prop := ∃ v, d.hasType v = true

/-! ## Encoding and decoding -/

/-- Abstract bytes with `UInt8` payload. -/
abbrev AB := AByte Byte

/-- Truncate or pad (with `uninit`) a byte list to length `n`. -/
def fit (n : Nat) (l : List AB) : List AB := (l ++ List.replicate n (AByte.uninit : AB)).take n

/-- Overwrite `buf` with `src` starting at offset `o` (bytes past the end of `buf` are dropped). -/
def writeAt : List AB → Nat → List AB → List AB
  | buf, _, [] => buf
  | [], _, _ :: _ => []
  | _ :: bs, 0, s :: ss => s :: writeAt bs 0 ss
  | b :: bs, n + 1, s :: ss => b :: writeAt bs n (s :: ss)

/-- The `len` elements of `x` starting at offset `o`. -/
def slice {α : Type} (x : List α) (o len : Nat) : List α := (x.drop o).take len

/-- The payloads of a fully initialized byte list (`none` if some byte is `uninit`). -/
def allInit : List AB → Option (List Byte)
  | [] => some []
  | .init d :: xs => (allInit xs).map (d :: ·)
  | .uninit :: _ => none

mutual
/-- Encoder: the abstract bytes of value `v` at type `d` (length `d.size`; padding bytes are
`uninit`; ill-typed values encode as all-`uninit`). -/
def Desc.encodeL : Desc → Val → List AB
  | .int t, .int bs => fit t.width (bs.map .init)
  | .bool, .bool b => [.init (if b then 1 else 0)]
  | .array e n, .array vs => fit (n * e.size) (vs.flatMap fun v => e.encodeL v)
  | .strct r fs, .strct vs =>
      let L := r.layout (Desc.layouts fs)
      fit L.size (Desc.writeFields fs L.offsets vs (List.replicate L.size .uninit))
  | .enm r vs, .enm i fvs =>
      let E := r.layout (Desc.variantLayouts vs)
      let code := ((Desc.codes r vs)[i]?).getD 0
      let buf := writeAt (List.replicate E.size .uninit) E.tagOffset
        ((leBytes r.tagTy.width code).map .init)
      fit E.size (Desc.writeVariant vs i E.variantFieldOffsets fvs buf)
  | .union r fs, .union j v =>
      let U := Toy.Zc.unionLayout r.modifier (Desc.layouts fs)
      fit U.size (Desc.writeField fs j v (List.replicate U.size .uninit))
  | .cell t, v => t.encodeL v
  | d, _ => List.replicate d.size (AByte.uninit : AB)
/-- Write each field's encoding at its offset. -/
def Desc.writeFields : List Desc → List Nat → List Val → List AB → List AB
  | f :: fs, o :: os, v :: vs, buf => Desc.writeFields fs os vs (writeAt buf o (f.encodeL v))
  | _, _, _, buf => buf
/-- Write the fields of variant `i`. -/
def Desc.writeVariant : List (DiscrSyn × List Desc) → Nat → List (List Nat) → List Val →
    List AB → List AB
  | (_, fs) :: _, 0, os :: _, fvs, buf => Desc.writeFields fs os fvs buf
  | _ :: vs, i + 1, _ :: oss, fvs, buf => Desc.writeVariant vs i oss fvs buf
  | _, _, _, _, buf => buf
/-- Write a union value through field `j` (at offset `0`). -/
def Desc.writeField : List Desc → Nat → Val → List AB → List AB
  | f :: _, 0, v, buf => writeAt buf 0 (f.encodeL v)
  | _ :: fs, j + 1, v, buf => Desc.writeField fs j v buf
  | [], _, _, buf => buf
end

mutual
/-- Decoder: the value denoted by abstract bytes `x` at type `d`, if `x` has length `d.size`
and is valid. Padding bytes are never read. -/
def Desc.decodeL : Desc → List AB → Option Val
  | .int t, x => if x.length = t.width then (allInit x).map .int else none
  | .bool, x => match x with
    | [.init b] => if b = 0 then some (.bool false) else if b = 1 then some (.bool true) else none
    | _ => none
  | .array e n, x =>
      if x.length = n * e.size then
        ((List.range n).mapM fun k => e.decodeL (slice x (k * e.size) e.size)).map .array
      else none
  | .strct r fs, x =>
      let L := r.layout (Desc.layouts fs)
      if x.length = L.size then (Desc.decodeFields fs L.offsets x).map .strct else none
  | .enm r vs, x =>
      let E := r.layout (Desc.variantLayouts vs)
      if x.length = E.size then
        match allInit (slice x E.tagOffset r.tagTy.width) with
        | none => none
        | some tbs =>
          match (Desc.codes r vs).findIdx? (· == leNat tbs) with
          | none => none
          | some i => (Desc.decodeVariant vs i E.variantFieldOffsets x).map (.enm i)
      else none
  | .union r fs, x =>
      let U := Toy.Zc.unionLayout r.modifier (Desc.layouts fs)
      if x.length = U.size then Desc.decodeField fs 0 x else none
  | .cell t, x => t.decodeL x
/-- Decode each field from its own byte range. -/
def Desc.decodeFields : List Desc → List Nat → List AB → Option (List Val)
  | [], _, _ => some []
  | f :: fs, o :: os, x =>
    match f.decodeL (slice x o f.size), Desc.decodeFields fs os x with
    | some v, some vs => some (v :: vs)
    | _, _ => none
  | _ :: _, [], _ => none
/-- Decode the fields of variant `i`. -/
def Desc.decodeVariant : List (DiscrSyn × List Desc) → Nat → List (List Nat) → List AB →
    Option (List Val)
  | (_, fs) :: _, 0, os :: _, x => Desc.decodeFields fs os x
  | _ :: vs, i + 1, _ :: oss, x => Desc.decodeVariant vs i oss x
  | _, _, _, _ => none
/-- Decode a union: the first field (from index `j` on) that decodes the prefix of its size. -/
def Desc.decodeField : List Desc → Nat → List AB → Option Val
  | [], _, _ => none
  | f :: fs, j, x =>
    match f.decodeL (x.take f.size) with
    | some v => some (.union j v)
    | none => Desc.decodeField fs (j + 1) x
end

/-! ## The semantic interpretation as a representation -/

/-- A byte list as a fixed-length byte vector (`uninit` past the end of the list). -/
def toBytesN (n : Nat) (l : List AB) : Bytes Byte n := Vector.ofFn fun i => l.getD i.val .uninit

/-- **Semantic interpretation.** The description `d` as a representation of its values
`TVal d` in `d.size` abstract bytes: encode with `Desc.encodeL`; decode with `Desc.decodeL`,
keeping only well-typed results. -/
def Desc.rep (d : Desc) : Rep (Bytes Byte d.size) (TVal d) where
  encode v := toBytesN d.size (d.encodeL v.val)
  decode x :=
    match d.decodeL x.toList with
    | some v => if h : d.hasType v = true then some ⟨v, h⟩ else none
    | none => none

/-- **Semantic `FromZeros`**: the all-zero byte vector of length `d.size` decodes. -/
def SemFromZeros (d : Desc) : Prop :=
  (d.rep.tryFrom (Vector.replicate d.size 0)).isSome = true

/-- **Semantic `FromBytes`**: every fully initialized byte vector of length `d.size` decodes. -/
def SemFromBytes (d : Desc) : Prop := d.rep.FromBytes

/-- **Semantic `IntoBytes`**: no encoding of a value of `d` contains `uninit`. -/
def SemIntoBytes (d : Desc) : Prop := d.rep.IntoBytes

/-- **Semantic `TryFromBytes` validity**: the decidable validity check on initialized bytes
(`true` iff the bytes `init bs[0], …` decode to a well-typed value). -/
def validInit (d : Desc) (bs : List Byte) : Bool :=
  match d.decodeL (bs.map .init) with
  | some v => d.hasType v
  | none => false

/-- **Semantic `Unaligned`**: the alignment is `1`. -/
def SemUnaligned (d : Desc) : Prop := d.align = 1

end Toy.Zc
