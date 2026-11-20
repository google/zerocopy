import ToyZc.Desc

/-!
# Models of zerocopy's derive checks

Each derive is modeled as a Boolean function on descriptions, following zerocopy-derive at tag
`v0.8.63` (commit `c55af491426ef53f35fb8c6e83f220fa07712e66`, repository `google/zerocopy`).
Line numbers below refer to that commit. Paths are relative to the repository root:
`D/` abbreviates `zerocopy/zerocopy-derive/src/`, and `Z/` abbreviates `zerocopy/src/`.

Every nominal type in a description is assumed to request the derive being modeled, so a
field type "implements" a trait exactly when the corresponding check (or zerocopy's primitive
impl) accepts it; the checks are therefore recursive. The derives emit `field: Trait` bounds
that the compiler discharges; the recursion models that discharge.

Modeling notes common to all checks:
* No generics, so the derives' generic-only paths (`homogeneous_field_bounds`, the
  `Unaligned`-fields fallback, `FieldBounds::Explicit` for generic padding) never apply.
* No field invariants (`#[zerocopy(invariant)]`), so `ctx.invariant_span` is always `None`.
* `TryFromBytes` is implemented by every description in the model: the struct and union
  `TryFromBytes` derives impose no `repr` condition, and the enum derive accepts `repr(C)` and
  `repr(Int)`, which are the only enum representations in the AST. The `FromZeros` derive first
  expands the `TryFromBytes` derive (`from_bytes.rs:98`), whose `field: TryFromBytes` bounds range
  over the fields of *every* variant (`try_from_bytes.rs:343`); these bounds are therefore always
  satisfied here and are omitted. Outside the model (generic or invariant-carrying field types)
  they can make the real derive reject an enum whose zero variant's fields are `FromZeros`.
-/

namespace Toy.Zc

/-- Build configuration relevant to the derives. -/
structure DeriveConfig where
  /-- Whether `--cfg zerocopy_derive_union_into_bytes` is set (`D/derive/into_bytes.rs:220-233`). -/
  unionIntoBytes : Bool

/-- `is_packed_1` (`D/repr.rs:169-172`): the representation has `packed` or `packed(1)`. -/
def ReprModifier.isPacked1 : ReprModifier → Bool
  | .packed 1 => true
  | _ => false

/-- `is_align_gt_1` (`D/repr.rs:148-150`): the representation has `align(N)` with `N > 1`. -/
def ReprModifier.isAlignGt1 : ReprModifier → Bool
  | .aligned n => decide (n > 1)
  | _ => false

/-! ## `find_zero_variant` (`D/derive/from_bytes.rs:19-90`) -/

/-- Faithful model of `find_zero_variant`. The state `next` is `next_negative_discriminant`:
`some n` means the next implicit discriminant is `-n`; `none` means it is positive or unknown.
`unk` is `has_unknown_discriminants`. Returns `.ok i` if variant `i` has discriminant zero,
and `.error unk` otherwise. (`lit n` always parses; the parse-failure branches of the source
only matter for literals above `u128::MAX`, which `Desc.wf` excludes.) -/
def findZeroVariantAux : List DiscrSyn → Nat → Option Nat → Bool → Except Bool Nat
  | [], _, _, unk => .error unk
  | d :: ds, i, next, unk =>
    match d with
    | .implicit =>
      match next with
      | some 0 => .ok i
      | some (n + 1) => findZeroVariantAux ds (i + 1) (some n) unk
      | none => findZeroVariantAux ds (i + 1) none unk
    | .lit 0 => .ok i
    | .lit (_ + 1) => findZeroVariantAux ds (i + 1) none unk
    | .negLit 0 => .ok i
    | .negLit (x + 1) => findZeroVariantAux ds (i + 1) (some x) unk
    | .other _ => findZeroVariantAux ds (i + 1) none true

/-- `find_zero_variant` on a list of syntactic discriminants. -/
def findZeroVariant (ds : List DiscrSyn) : Except Bool Nat := findZeroVariantAux ds 0 (some 0) false

theorem ex_findZeroVariant_pos : findZeroVariant [.negLit 2, .implicit, .implicit] = .ok 2 := rfl
theorem ex_findZeroVariant_neg : findZeroVariant [.lit 1, .implicit] = .error false := rfl
theorem ex_findZeroVariant_neg_unknown : findZeroVariant [.other 0, .implicit] = .error true := rfl

/-! ## `FromZeros` (`D/derive/from_bytes.rs:91-105, 122-180`) -/

mutual
/-- Model of `#[derive(FromZeros)]` together with zerocopy's primitive impls:
* integers, `bool`: implemented (`Z/impls.rs:68-76`, `Z/impls.rs:101`);
* `[T; N]`: iff `T` (`Z/impls.rs:905`); `UnsafeCell<T>`: iff `T` (`Z/impls.rs:839`);
* struct: every field `FromZeros` (`FieldBounds::ALL_SELF`, `from_bytes.rs:122-124`);
* enum: the representation is `repr(C)` or `repr(Int)` (always, in the AST;
  `from_bytes.rs:130-141`), `find_zero_variant` returns `Ok(i)` (`from_bytes.rs:143-162`), and
  every field of variant `i` is `FromZeros` (`from_bytes.rs:164-175`);
* union: every field `FromZeros` (`from_bytes.rs:177-180`). -/
def implFromZeros : Desc → Bool
  | .int _ => true
  | .bool => true
  | .array e _ => implFromZeros e
  | .strct _ fs => allFromZeros fs
  | .enm _ vs =>
    match findZeroVariant (vs.map Prod.fst) with
    | .ok i => variantFromZeros vs i
    | .error _ => false
  | .union _ fs => allFromZeros fs
  | .cell t => implFromZeros t
/-- Every description in the list passes `implFromZeros`. -/
def allFromZeros : List Desc → Bool
  | [] => true
  | f :: fs => implFromZeros f && allFromZeros fs
/-- Every field of variant `i` passes `implFromZeros`. -/
def variantFromZeros : List (DiscrSyn × List Desc) → Nat → Bool
  | (_, fs) :: _, 0 => allFromZeros fs
  | _ :: vs, i + 1 => variantFromZeros vs i
  | [], _ => false
end

/-! ## `FromBytes` (`D/derive/from_bytes.rs:106-121, 181-204`; `D/util.rs:982-1001`) -/

/-- `enum_size_from_repr` (`D/util.rs:982-1001`): `8` for `u8`/`i8`, `16` for `u16`/`i16`,
error otherwise. -/
def enumFromBytesBits : EnumRepr → Option Nat
  | .prim .u8 | .prim .i8 => some 8
  | .prim .u16 | .prim .i16 => some 16
  | _ => none

/-- The variant-count check of the enum `FromBytes` derive (`from_bytes.rs:187-197`):
`variants.len() == 1 << enum_size_from_repr(repr)?`. -/
def enumVariantCountOK (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  match enumFromBytesBits r with
  | some b => vs.length == 2 ^ b
  | none => false

mutual
/-- Model of `#[derive(FromBytes)]` with zerocopy's primitive impls. The derive first runs the
`FromZeros` derive (`from_bytes.rs:113`), so its check is a conjunct:
* integers: implemented; `bool`: not implemented (`Z/impls.rs:101`); arrays, `UnsafeCell`: iff
  the element / inner type (`Z/impls.rs:906`, `Z/impls.rs:840`);
* struct: `FromZeros` check and every field `FromBytes` (`from_bytes.rs:181-183`);
* enum: `FromZeros` check, `enumVariantCountOK`, every field of every variant `FromBytes`
  (`from_bytes.rs:184-200`);
* union: `FromZeros` check and every field `FromBytes` (`from_bytes.rs:201-204`). -/
def implFromBytes : Desc → Bool
  | .int _ => true
  | .bool => false
  | .array e _ => implFromBytes e
  | .strct r fs => implFromZeros (.strct r fs) && allFromBytes fs
  | .enm r vs => implFromZeros (.enm r vs) && enumVariantCountOK r vs && variantsFromBytes vs
  | .union r fs => implFromZeros (.union r fs) && allFromBytes fs
  | .cell t => implFromBytes t
/-- Every description in the list passes `implFromBytes`. -/
def allFromBytes : List Desc → Bool
  | [] => true
  | f :: fs => implFromBytes f && allFromBytes fs
/-- Every field of every variant passes `implFromBytes`. -/
def variantsFromBytes : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => allFromBytes fs && variantsFromBytes vs
end

/-! ## `IntoBytes` (`D/derive/into_bytes.rs:89-259`; `Z/util/macro_util.rs:333-442`) -/

/-- The padding analysis of the struct `IntoBytes` derive (`into_bytes.rs:99-144`), for a
non-generic struct whose last field is not a syntactic slice:
* `repr(transparent)` or `is_packed_1`: no padding check (`into_bytes.rs:99-118`);
* else `repr(C)` without `align(N > 1)` and at most one field: no padding check
  (`into_bytes.rs:119-123`);
* else (no generics): `PaddingCheck::Struct` (`into_bytes.rs:124-144`), i.e.
  `struct_padding!` = `size_of::<Self>() - Σ size_of::<field>()` must be `0`
  (`macro_util.rs:333-340`, `PaddingFree<T, 0>` at `macro_util.rs:63-64`). -/
def structPaddingOK (r : StructRepr) (fs : List Desc) : Bool :=
  match r with
  | .transparent => true
  | .c m =>
    m.isPacked1 || (!m.isAlignGt1 && decide (fs.length ≤ 1)) ||
      ((Desc.structLayout r fs).size - (fs.map Desc.size).sum == 0)

/-- `PaddingCheck::Enum` (`into_bytes.rs:205-208`): `enum_padding!` (`macro_util.rs:420-442`)
is the maximum over variants of `size_of::<Self>() - (size_of::<Tag>() + Σ size_of::<field>())`
and must be `0`. -/
def enumPaddingOK (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  vs.all fun v => (Desc.enumLayout r vs).size - (r.tagTy.width + (v.2.map Desc.size).sum) == 0

/-- `PaddingCheck::Union` (`into_bytes.rs:255-257`): `union_padding!` (`macro_util.rs:386-400`)
is the maximum over fields of `size_of::<Self>() - size_of::<field>()` and must be `0`. -/
def unionPaddingOK (r : UnionRepr) (fs : List Desc) : Bool :=
  fs.all fun f => (Desc.unionLayout r fs).size - f.size == 0

mutual
/-- Model of `#[derive(IntoBytes)]` with zerocopy's primitive impls:
* integers, `bool`: implemented (`Z/impls.rs:68-76`, `Z/impls.rs:101`); arrays, `UnsafeCell`:
  iff the element / inner type (`Z/impls.rs:907`, `Z/impls.rs:841`);
* struct: every field `IntoBytes` and `structPaddingOK` (`into_bytes.rs:183-193`);
* enum: `repr(C)` or `repr(Int)` (always, in the AST; `into_bytes.rs:197-203`), every field of
  every variant `IntoBytes` (`FieldBounds::ALL_SELF`, `into_bytes.rs:206`), `enumPaddingOK`;
* union: the `cfg` is set (`into_bytes.rs:220-233`), the representation is `repr(C)`
  (always, in the AST; `into_bytes.rs:247-253`), every field `IntoBytes`, `unionPaddingOK`. -/
def implIntoBytes (cfg : DeriveConfig) : Desc → Bool
  | .int _ => true
  | .bool => true
  | .array e _ => implIntoBytes cfg e
  | .strct r fs => allIntoBytes cfg fs && structPaddingOK r fs
  | .enm r vs => variantsIntoBytes cfg vs && enumPaddingOK r vs
  | .union r fs => cfg.unionIntoBytes && allIntoBytes cfg fs && unionPaddingOK r fs
  | .cell t => implIntoBytes cfg t
/-- Every description in the list passes `implIntoBytes`. -/
def allIntoBytes (cfg : DeriveConfig) : List Desc → Bool
  | [] => true
  | f :: fs => implIntoBytes cfg f && allIntoBytes cfg fs
/-- Every field of every variant passes `implIntoBytes`. -/
def variantsIntoBytes (cfg : DeriveConfig) : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => allIntoBytes cfg fs && variantsIntoBytes cfg vs
end

/-! ## `Unaligned` (`D/derive/unaligned.rs:11-80`) -/

mutual
/-- Model of `#[derive(Unaligned)]` with zerocopy's primitive impls:
* `u8`, `i8`, `bool`: implemented; other integers: not (`Z/impls.rs:68-76`, `Z/impls.rs:101`);
  arrays, `UnsafeCell`: iff the element / inner type (`Z/impls.rs:908`, `Z/impls.rs:849`);
* struct and union: no `align(N > 1)`, and either `is_packed_1` (no field bounds) or `repr(C)` /
  `repr(transparent)` with every field `Unaligned` (`unaligned.rs:24-40`, `unaligned.rs:64-80`);
* enum: no `align(N > 1)` (always, in the AST), `repr(u8)` or `repr(i8)`, and every field
  `Unaligned` (`unaligned.rs:45-57`). -/
def implUnaligned : Desc → Bool
  | .int t => t == .u8 || t == .i8
  | .bool => true
  | .array e _ => implUnaligned e
  | .strct (.c m) fs => !m.isAlignGt1 && (m.isPacked1 || allUnaligned fs)
  | .strct .transparent fs => allUnaligned fs
  | .enm r vs => (r == .prim .u8 || r == .prim .i8) && variantsUnaligned vs
  | .union (.c m) fs => !m.isAlignGt1 && (m.isPacked1 || allUnaligned fs)
  | .cell t => implUnaligned t
/-- Every description in the list passes `implUnaligned`. -/
def allUnaligned : List Desc → Bool
  | [] => true
  | f :: fs => implUnaligned f && allUnaligned fs
/-- Every field of every variant passes `implUnaligned`. -/
def variantsUnaligned : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => allUnaligned fs && variantsUnaligned vs
end

/-! ## `Immutable` (`D/derive/mod.rs:19-31`) -/

mutual
/-- Model of `#[derive(Immutable)]` (every field `Immutable`, `FieldBounds::ALL_SELF`) with
zerocopy's primitive impls: integers and `bool` are `Immutable` (`Z/impls.rs:68-76`,
`Z/impls.rs:101`), arrays iff the element (`Z/impls.rs:893`), and `UnsafeCell<T>` never (no
impl exists; its internal safety contract, `Z/lib.rs:1640-1646`, is "no interior mutation"). -/
def implImmutable : Desc → Bool
  | .int _ => true
  | .bool => true
  | .array e _ => implImmutable e
  | .strct _ fs => allImmutable fs
  | .enm _ vs => variantsImmutable vs
  | .union _ fs => allImmutable fs
  | .cell _ => false
/-- Every description in the list passes `implImmutable`. -/
def allImmutable : List Desc → Bool
  | [] => true
  | f :: fs => implImmutable f && allImmutable fs
/-- Every field of every variant passes `implImmutable`. -/
def variantsImmutable : List (DiscrSyn × List Desc) → Bool
  | [] => true
  | (_, fs) :: vs => allImmutable fs && variantsImmutable vs
end

/-! ## `TryFromBytes::is_safe` (`D/derive/try_from_bytes.rs`) -/

/-- `could_be_from_bytes` (`try_from_bytes.rs:327-329`): `repr(u8/i8/u16/i16)`, no fields at all,
and exactly `2^bits` variants. -/
def couldBeFromBytes (r : EnumRepr) (vs : List (DiscrSyn × List Desc)) : Bool :=
  match enumFromBytesBits r with
  | some b => vs.all (fun v => v.2.isEmpty) && vs.length == 2 ^ b
  | none => false

mutual
/-- Model of the generated (or primitive) `TryFromBytes::is_safe` on initialized bytes, for a
derive whose top-level trait is `TryFromBytes` (the `FromBytes`-top-level shortcut
`try_gen_trivial_is_safe`, `try_from_bytes.rs:347-393`, returns `true` only after the compiler has
accepted `Self: FromBytes`, and is not modeled):
* integers: `true` (no validator; `Z/impls.rs:68-76`); `bool`: `byte < 2` (`Z/impls.rs:113-116`);
* arrays: every element (`Z/impls.rs:894-904`, `Z/impls.rs:934`); `UnsafeCell`: the inner type
  (`Z/impls.rs:853`);
* struct: every field's `is_safe` on its bytes (`try_from_bytes.rs:235-269`, `69-71`);
* enum: `true` if `couldBeFromBytes` (`try_from_bytes.rs:332-336`); otherwise read the tag
  (`try_from_bytes.rs:173-183`), match it against the variants' tag constants in declaration
  order, and check the fields of the matching variant; no match gives `false`
  (`try_from_bytes.rs:207-226`);
* union: some field's `is_safe` on that field's bytes (`try_from_bytes.rs:282-307`). -/
def isSafe : Desc → List Byte → Bool
  | .int _, _ => true
  | .bool, bs =>
    match bs with
    | [b] => decide (b < 2)
    | _ => false
  | .array e n, bs => (List.range n).all fun k => isSafe e (slice bs (k * e.size) e.size)
  | .strct r fs, bs => isSafeFields fs (Desc.structLayout r fs).offsets bs
  | .enm r vs, bs =>
    if couldBeFromBytes r vs then true
    else
      let E := Desc.enumLayout r vs
      match (Desc.codes r vs).findIdx? (· == leNat (slice bs E.tagOffset r.tagTy.width)) with
      | some i => isSafeVariant vs i E.variantFieldOffsets bs
      | none => false
  | .union _ fs, bs => isSafeUnion fs bs
  | .cell t, bs => isSafe t bs
/-- Conjunction of the fields' `is_safe` on their byte ranges. -/
def isSafeFields : List Desc → List Nat → List Byte → Bool
  | [], _, _ => true
  | f :: fs, o :: os, bs => isSafe f (slice bs o f.size) && isSafeFields fs os bs
  | _ :: _, [], _ => false
/-- `is_safe` of the fields of variant `i`. -/
def isSafeVariant : List (DiscrSyn × List Desc) → Nat → List (List Nat) → List Byte → Bool
  | (_, fs) :: _, 0, os :: _, bs => isSafeFields fs os bs
  | _ :: vs, i + 1, _ :: oss, bs => isSafeVariant vs i oss bs
  | _, _, _, _ => false
/-- Disjunction over union fields of `is_safe` on the field's prefix. -/
def isSafeUnion : List Desc → List Byte → Bool
  | [], _ => false
  | f :: fs, bs => isSafe f (bs.take f.size) || isSafeUnion fs bs
end

/-! ## Examples of the checks (fully proved) -/

/-- A `repr(C)` struct `{ a: u8, b: u16 }` (one byte of padding). -/
abbrev Desc.paddedPair : Desc := .strct (.c .none) [.u8, .u16]

/-- A `repr(C)` struct `{ a: u16, b: u8, c: u8 }` (no padding). -/
abbrev Desc.fullTriple : Desc := .strct (.c .none) [.u16, .u8, .u8]

/-- The configuration with the union `cfg` unset (the default) and set. -/
abbrev cfgDefault : DeriveConfig := ⟨false⟩
abbrev cfgUnion : DeriveConfig := ⟨true⟩

theorem ex_implFromZeros_pos : implFromZeros (.enm (.prim .u8) [(.lit 3, []), (.lit 0, [.bool])])
    = true := by decide
theorem ex_implFromZeros_neg : implFromZeros (.enm (.prim .u8) [(.lit 3, []), (.implicit, [])])
    = false := by decide
theorem ex_implFromBytes_pos : implFromBytes Desc.paddedPair = true := by decide
theorem ex_implFromBytes_neg : implFromBytes (.strct (.c .none) [.u8, .bool]) = false := by decide
theorem ex_implIntoBytes_pos : implIntoBytes cfgDefault Desc.fullTriple = true := by decide
theorem ex_implIntoBytes_neg : implIntoBytes cfgDefault Desc.paddedPair = false := by decide
theorem ex_implIntoBytes_neg_union_gate :
    implIntoBytes cfgDefault (.union (.c .none) [.u16, .array .u8 2]) = false ∧
    implIntoBytes cfgUnion (.union (.c .none) [.u16, .array .u8 2]) = true := by decide
theorem ex_structPaddingOK_pos_packed : structPaddingOK (.c (.packed 1)) [.u8, .u16] = true := by
  decide
theorem ex_structPaddingOK_neg : structPaddingOK (.c (.aligned 2)) [.u8] = false := by decide
theorem ex_enumPaddingOK_pos : enumPaddingOK (.prim .u8) [(.implicit, [.u8]), (.implicit, [.i8])]
    = true := by decide
theorem ex_enumPaddingOK_neg : enumPaddingOK (.prim .u8) [(.implicit, [.u8]), (.implicit, [.u16])]
    = false := by decide
theorem ex_unionPaddingOK_pos : unionPaddingOK (.c .none) [.u16, .array .u8 2] = true := by decide
theorem ex_unionPaddingOK_neg : unionPaddingOK (.c .none) [.u8, .u16] = false := by decide
theorem ex_implUnaligned_pos : implUnaligned (.strct (.c (.packed 1)) [.u8, .u16]) = true := by
  decide
theorem ex_implUnaligned_neg : implUnaligned (.strct (.c .none) [.u8, .u16]) = false := by decide
theorem ex_implImmutable_pos : implImmutable Desc.paddedPair = true := by decide
theorem ex_implImmutable_neg : implImmutable (.strct (.c .none) [.cell .u8]) = false := by decide
theorem ex_isSafe_pos : isSafe (.enm (.prim .u8) [(.lit 3, [.bool])]) [3, 1] = true := by decide
theorem ex_isSafe_neg : isSafe (.enm (.prim .u8) [(.lit 3, [.bool])]) [3, 2] = false := by decide
theorem ex_couldBeFromBytes_neg : couldBeFromBytes (.prim .u8) [(.implicit, [])] = false := by
  decide

end Toy.Zc
