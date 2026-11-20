# Packed Representations, Unaligned Reference UB, Slice DST Layout Algebra, and Interior-Mutable Field Projections

## Summary

`Basis: normative + source + execution + derived`

Combining `#[repr(packed(N))]` with slice dynamically sized types (`SliceDst`), interior mutability (`UnsafeCell<T>` / `Cell<T>`), custom `Drop`, and `Pin` creates delicate interactions across layout calculation, reference validity, MIR drop elaboration, and aliasing rules:

1. **Shallow clamping vs. inner rounding retention:** `#[repr(packed(N))]` ($N = 2^k \in [1, 2^{29}]$) clamps each direct field's alignment to $\min(\text{align}(F_i), N)$ and caps outer object alignment at $\min(\text{natural\_align}, N)$ (`src/type-layout.md:632-654`; `compiler/rustc_abi/src/layout.rs:780-816`), disabling `Scalar`/`ScalarPair` ABI promotion (`L842-895`) without altering internal padding or alignment *inside* field types. Wrapping an aligned `#[repr(C)]` slice DST inside `#[repr(C, packed(2))]` lowers `obj_align` to `2` while retaining the inner tail's rounding modulus `size_align = 4` (`google/zerocopy@ec133ce4`, `zerocopy/src/layout.rs:1473-1486`; `proofs-rs/lean-miri@c92d1d97`, `DynamicLayout.lean:56-71`), verified across `1,980` combinations (`0` mismatches).
2. **Unaligned references vs. `&raw const` / `read_unaligned`:** Forming `&packed.f` or `&mut packed.f`—even transiently or for zero-element slices `&packed.tail`—creates an invalid reference (`src/behavior-considered-undefined.md:78-97, 147-149`), rejected statically by `CheckPackedRef` (`E0793`, `check_packed_ref.rs:27-49`) and dynamically by Miri (`Rvalue.lean:80-90`, `TypedRetag.lean:102-105`). Direct `Copy` reads (`let v = packed.f;`) on aligned base places avoid misaligned `*` dereferences, whereas raw-pointer field access requires `Rvalue::RawPtr` (`&raw const`/`&raw mut`, `RetagMode.Raw`, `Rvalue.lean:95-104`) paired with `ptr::read_unaligned` / `ptr::write_unaligned` (`core/src/ptr/mod.rs:1842-1862, 2052-2065`).
3. **Packed `Drop` (`E0509`, `AddMovesForPackedDrops`, and `Pin`):** To avoid passing unaligned references to `drop_in_place`, `AddMovesForPackedDrops` (`add_moves_for_packed_drops.rs:36-111`) moves misaligned fields to aligned stack temporaries prior to dropping. This forces `wfcheck` (`wfcheck.rs:1056-1091`) to reject unsized tails in `#[repr(packed)]` when `tail_ty.needs_drop(...)` is `true` (motivating `ManuallyDrop` in `zerocopy-derive/src/derive/known_layout.rs:211-220`), leaves custom `Drop` implementations subject to both `E0509` and `E0793`, and makes structural `Pin` inside packed types unsound (`check.rs:1672-1681`, `PinV2OnPacked`; `zerocopy/src/wrappers.rs:104-119`).
4. **Packed `UnsafeCell` / `Cell` projections:** Tree Borrows `FreezeVisitor` (`FreezeVisitor.lean:49-117`) marks misaligned `UnsafeCell` byte ranges as `Permission.Cell` (`SharedReadWrite`). Yet `UnsafeCell::get(&self)` and `Cell::set(&self, v)` require aligned `&self`; misaligned access requires `UnsafeCell::raw_get(&raw const packed.cell)` (`cell.rs:2497-2501`) plus `read_unaligned`/`write_unaligned`. Furthermore, `Cell<Unalign<u32>>` (`Copy`, `Unaligned`, `align = 1`, safe `.get()`/`.set()`) and `Unalign<Cell<u32>>` (`!Copy`, `!Unaligned`, requires aligned `try_deref` or stack copy-and-writeback `Unalign::update`) do not commute.

## Applicability

`Basis: documentation + source`

These findings govern unsafe systems code, zero-copy layout crates, and MIR verifiers across the nine subjects in `REPORT.json`:

- **Rust language, compiler, and standard library (`rust-lang/rust@4b5350e87e48`, `rust-lang/reference@a286e1ecb8ce`, `rust-lang/rfcs@f43d5789b838`):** Covers `#[repr(packed(N))]` layout (`rustc_abi`), WF checks (`check.rs`, `wfcheck.rs`), MIR passes (`check_packed_ref.rs`, `add_moves_for_packed_drops.rs`, `shim.rs`, `elaborate_drop.rs`), `ptr::{read,write}_unaligned`, and `UnsafeCell::raw_get`.
- **Zero-copy casting and wrappers (`google/zerocopy@ec133ce4d799`):** Covers `zerocopy/src/{layout,wrappers,impls}.rs`, `zerocopy/src/pointer/ptr.rs`, and `zerocopy/zerocopy-derive/src/{repr.rs, derive/known_layout.rs, derive/into_bytes.rs}`.
- **Mechanized semantics and verification (`proofs-rs/lean-miri@c92d1d9754c9`, `joshlf/anneal@c131b320eeeb`, `leanprover/lean4` `v4.34.1` `5045d0056413`):** Links Miri's `DynamicLayout`, `Projection`, `Rvalue`, `MemoryOperand`, and `FreezeVisitor` directly to prelude-only Lean 4 obligations.
- **Relationship to adjacent corpus packages:** Extends `zerocopy-knownlayout-slicedst-rounding-phase-and-split-at-padding-overlap` (which treats `RoundingAlignAndPhase` and `split_at_mut` padding overlap) into `#[repr(packed(N))]` DST composition, MIR unaligned-reference checks, packed `Drop` elaboration, and `UnsafeCell`/`Cell` projection rules; complements `zerocopy-validity-predicates-projection-layout-and-ffi-intrinsics`, `rust-aggregate-dst-and-target-layout-guarantees`, `rust-reference-layout-guarantees-target-abi-limits-and-semver-snares`, and `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute`.

## Findings

### 1. Shallow Field Clamping, `E0587` vs. `ALIGNED_FIELDS_IN_PACKED`, and ABI Suppression

`Basis: normative + source`

Under the Rust Reference (`rust-lang/reference@a286e1ecb8ce`, `src/type-layout.md:632-654`), `#[repr(packed)]` (`N = 1`) or `#[repr(packed(N))]` ($N = 2^k \in [1, 2^{29}]$) alters struct and union layout shallowly:
- Each direct field $F_i$ is placed using alignment $\min(\text{align}(F_i), N)$, and outer struct alignment becomes $\max_i \min(\text{align}(F_i), N) \le N$ (`compiler/rustc_abi/src/layout.rs:780-816`).
- **Non-transitivity (`type-layout.md:635`):** `packed(N)` never alters internal padding or alignment inside $F_i$'s own type. Placing `#[repr(C)] struct Inner { a: u32, b: u8 }` (`size = 8, align = 4`) inside `#[repr(C, packed(1))] struct Outer { tag: u8, f: Inner }` locates `f` at offset `1` while retaining `f`'s size `8` and `3` internal trailing padding bytes (`Outer` size `9`, `align = 1`).
- **Conflict diagnostics (`compiler/rustc_hir_analysis/src/check/check.rs:1668-1782`):** `#[repr(packed(P), align(A))]` on the same item triggers hard error **`E0587`** (`L1699-1706`); conflicting `packed` attributes trigger **`E0634`** (`L1682-1696`). Transitively embedding a `#[repr(align(A))]` struct/union inside `#[repr(packed)]` historically emitted `E0588`—which `rustc_error_codes/src/error_codes/E0588.md` notes is *"no longer emitted by the compiler"*—and is now diagnosed via the **`ALIGNED_FIELDS_IN_PACKED`** lint when `repr.c()` transitively contains `repr.align.is_some()` (`check_packed_inner`, `L1707-1782`), while `rustc_abi/src/layout.rs:417, 438, 606, 784, 931` propagates `max_repr_align`.
- **ABI suppression (`compiler/rustc_abi/src/layout.rs:488-493, 842-895`):** Newtype promotion to `BackendRepr::Scalar` or `ScalarPair` requires `align == field.align` (`L842`, `L887-894`). Whenever `packed(N)` lowers outer alignment below a scalar field's natural alignment (e.g., `Unalign<u32>`), `rustc` emits `BackendRepr::Memory { sized: true }` so ABI calls do not assume aligned registers.

---

### 2. Layout Algebra: Outer Alignment Relaxation vs. Inner `SliceDst` Rounding Equivalence

`Basis: source + execution + derived`

When a `#[repr(C, packed(P))]` struct ends in an unsized slice DST $T_{\text{tail}}$, compiler/Miri dynamic layout and `google/zerocopy`'s static layout algebra agree across every element count:

1. **`proofs-rs/lean-miri@c92d1d9754c9` (`DynamicLayout.lean:49-71`, `PlaceDynamic.lean:68-85`):** With prefix offset $\text{off}$, prefix alignment $a_{\text{pre}} \le P$, and recursive tail $(s_{\text{tail}}, a_{\text{tail}})$, Miri clamps $a'_{\text{tail}} = \min(a_{\text{tail}}, P)$, sets $a_{\text{full}} = \max(a_{\text{pre}}, a'_{\text{tail}})$, $\text{adj} = \text{alignTo}(\text{off}, a'_{\text{tail}})$, and $s_{\text{full}} = \text{alignTo}(\text{adj} + s_{\text{tail}}, a_{\text{full}})$, asserting `fullSize == codegenSize` and `<= isize::MAX`. `Projection::field` (`PlaceDynamic.lean:77-79`) clamps `tail`'s field offset alignment by `packedAlign` ($P$), while $s_{\text{tail}}$ already includes $T_{\text{tail}}$'s internal `size_align` rounding.
2. **`google/zerocopy@ec133ce4d799` (`zerocopy/src/layout.rs:1153-1184, 1231-1377, 1405-1495`):** `DstLayout::extend(field, repr_packed)` clamps `field_align = min(field.align, P)`, shifts `trailing.offset` and `trailing.size_base` by `off`, and preserves `trailing.size_rounding_align_and_phase` unchanged. Then `DstLayout::pad_to_align()` (`L1430-1488`) branches on `size_align < self.align`: whenever `size_align >= self.align` (`L1473-1486`, the `packed(P)` case where inner rounding exceeds $P$), `size_align` keeps the inner modulus while only `size_base` rounds up to `self.align` ($P$).

| Pattern | Concrete Type | `obj_align` | `offset` | `size_base` | `size_align` | `size_for_elems(0, 1, 2, 5)` | Safe `&tail` / `KnownLayout` Status |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| **1. Direct Packed Slice** | `#[repr(C, packed(1))] struct Direct { b: u8, a: u32, tail: [u32] }` | `1` | `5` | `5` | `1` | `5, 9, 13, 25` | `IntoBytes` legal (`derive/into_bytes.rs:99-118`), **yet `&d.tail` is `E0793`/UB at offset `5` even at `elems = 0`!** |
| **2. Nested `repr(C)` DST in `packed(2)`** | `#[repr(C)] struct In { a: u32, t: [u8] }`; `#[repr(C, packed(2))] struct Out { b: u8, i: In }` | `2` | `6` | `6` | **`4`** | `6, 10, 10, 14` | Inner `size_align = 4 > obj_align = 2` retained; sizes are $2 \pmod 4$, `requires_dynamic_padding = true` |
| **3a. Aligned Tail Wire** | `#[repr(C)] struct WireA { hdr: PackedHdr5B, payload: [u32] }` | `4` | `8` | `8` | `4` | `8, 12, 16, 28` | `3` bytes static padding `[5..8)`; `&wire.payload` (`&[u32]`) is always `4`-aligned and sound |
| **3b. Unalign Tail Wire** | `#[repr(C)] struct WireU { b: u8, a: Unalign<u32>, payload: [Unalign<u32>] }` | `1` | `5` | `5` | `1` | `5, 9, 13, 25` | Zero padding (`IntoBytes` + `Unaligned`); `&wire.payload` (`&[Unalign<u32>]`) is safe at any byte offset |

*(On generic homogeneous slice DSTs with `#[repr(C, packed(P))]`, `zerocopy-derive/src/derive/into_bytes.rs:145-166` proves padding freedom because every field size is a multiple of `align_of::<T>()` and thus of `min(align_of::<T>(), P)`.)*

---

### 3. Unaligned `&T` / `&mut T` UB vs. `&raw const` / `read_unaligned` MIR Lowering

`Basis: normative + source + derived`

The Rust Reference (`src/behavior-considered-undefined.md:78-97, 147-159`) and `library/core/src/ptr/mod.rs:1998-2033` separate four MIR operations:

1. **Forming `&packed.f` / `&mut packed.f` (`E0793`):** Even if immediately cast (`&packed.f as *const F`), or for a ZST / zero-length slice `&packed.tail` (`elems = 0`), creating a misaligned reference produces an invalid value (`behavior-considered-undefined.md:148`). MIR lint `CheckPackedRef` (`check_packed_ref.rs:27-49`) diagnoses `context.is_borrow()` on `util::place_unalignment` as `E0793`; Miri (`Rvalue.lean:80-90`, `TypedRetag.lean:102-105`) triggers `checkPtrAccess` + `enforceValidity` UB.
2. **Direct place copy (`let x = packed.f;` for `T: Copy`):** A place is *"based on a misaligned pointer"* (`behavior-considered-undefined.md:82-88`) only when its **last `*` projection** dereferences a misaligned pointer for the *pointer's* type. Accessing `.f` on an aligned `&Packed` / local triggers no misaligned `*`; `rustc` lowers the load at packed alignment. Conversely, taking `fp = &raw const packed.f` (`*const u32`) and evaluating `*fp` dereferences a misaligned `*const u32`, faulting `alignmentCheckFailed` (`MemoryOperand.lean:103-118`).
3. **`&raw const packed.f` / `&raw mut packed.f` (`Rvalue::RawPtr`, RFC 2582):** `Rvalue.lean:95-104` evaluates `evalPlace choice src false` and `toRef` under `RetagMode.Raw`, preserving provenance without reference alignment checks or Tree Borrows protector retagging.
4. **`ptr::read_unaligned` / `ptr::write_unaligned` (`library/core/src/ptr/mod.rs:1842-1862, 2052-2065`):** `core` casts `src`/`dst` to private `#[repr(packed)] struct Unaligned<T>(T)` (`align = 1, size = size_of::<T>()`), executes typed `ptr::read` / `ptr::write` (preserving pointer provenance bytes), and converts via value-level `mem::transmute_neo`.

---

### 4. The Three-Way Seam: `#[repr(packed)]`, `Drop` (`E0509` / `AddMovesForPackedDrops`), `Pin`, and `UnsafeCell`/`Cell`

`Basis: normative + source + derived`

#### A. Packed `Drop`, `AddMovesForPackedDrops`, and Unsized-Tail Restrictions

1. **`AddMovesForPackedDrops` (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:36-111`):** Running over both user MIR and `DropShimElaborator` shims (`shim.rs:346-369`, `elaborate_drop.rs:733-750`), this pass rewrites every `TerminatorKind::Drop { place }` where `util::place_unalignment` is `Some` into `StorageLive(_temp); _temp = move place; drop(_temp) -> bb_dead; StorageDead(_temp);` so `drop_in_place` receives an aligned stack local.
2. **Unsized tail ban (`compiler/rustc_hir_analysis/src/check/wfcheck.rs:1056-1091`):** Because `_temp = move place` requires `Sized`, `wfcheck` computes `needs_drop_copy = || packed && tail_ty.needs_drop(...)` and forces a `FieldSized` obligation on the tail whenever `true`. Thus `zerocopy-derive/src/derive/known_layout.rs:211-220` wraps the trailing field of `__ZerocopyKnownLayoutMaybeUninit` in `core::mem::ManuallyDrop<...>` (`needs_drop == false`) so generic packed slice DSTs compile.
3. **Custom `Drop` + `E0509` (`E0509.md`) and `Pin` unsoundness (`check.rs:1672-1681`, `wrappers.rs:104-119`):** Under custom `Drop`, `E0509` bans moving fields out of `self` while `E0793` bans borrowing over-aligned fields, forcing `&raw mut self.f` + `read_unaligned`/`write_unaligned` cleanup. Moreover, because `AddMovesForPackedDrops` relocates fields to `_temp` before `Drop::drop` runs, structural `Pin` projection violates RFC 2349 (`PinV2OnPacked` in `check.rs:1675-1681`), so `zerocopy::Unalign<T>` prohibits `Pin<&mut T>` projection.

#### B. Packed `UnsafeCell<T>` / `Cell<T>` Projections and Non-Commutativity

1. **Tree Borrows `FreezeVisitor` (`proofs-rs/lean-miri@c92d1d9754c9`, `FreezeVisitor.lean:49-117`, `TypedRetag.lean:56-72`):** On `#[repr(C, packed)] struct PackedCell { tag: u8, cell: UnsafeCell<u32> }`, `visitValue` walks `FieldsShape::Arbitrary` by byte offset, marking `[0, 1)` `Permission.Frozen` and misaligned `[1, 5)` **`Permission.Cell`** (`SharedReadWrite`).
2. **Alignment-safe projection (`library/core/src/cell.rs:2436, 2497-2501`):** Calling `packed.cell.get()` forms `&UnsafeCell<u32>` at offset `1` (`E0793`/UB). Sound single-threaded access must use `UnsafeCell::raw_get(&raw const packed.cell)` followed by `ptr::read_unaligned` / `ptr::write_unaligned`.
3. **`Cell<Unalign<u32>>` vs. `Unalign<Cell<u32>>` (`zerocopy/src/{impls.rs:827-854, wrappers.rs:149-169, 339-405}`):** `Cell<Unalign<u32>>` implements `Unaligned` (`align = 1`), `FromBytes`, `IntoBytes`, and safe shared `.get()`/`.set(Unalign::new(v))` at any offset. Conversely, `Cell<u32>` is neither `Copy` nor `Unaligned`: `Unalign<Cell<u32>>` lacks `.get()`/`.clone()`, fails `try_deref()` whenever `addr % 4 != 0`, and requires `&mut self` for `Unalign::update` (`wrappers.rs:339-395`, copying to the stack and writing back via `WriteBackOnDrop`).

---

### 5. Prelude-Only Lean 4 (`v4.34.1`) Mechanization (`Verification.PackedDstLayout`)

`Basis: source + derived`

The standalone Lean 4 module below obeys `joshlf/anneal@c131b320` Pass-1 syntax rules (`TrustedBoundary.lean:487-595`: `prelude` + `Init.*` only, zero `sorry`, zero custom axioms, no `do`, `{ x with ... }`, `/`, `%`, or `omega`):

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic

namespace Verification.PackedDstLayout

def alignTo (x a : Nat) : Nat :=
  let rem := Nat.mod x a
  match Nat.beq rem 0 with
  | true  => x
  | false => x + (a - rem)

structure TrailingSliceLayout where
  offset    : Nat
  elemSize  : Nat
  sizeBase  : Nat
  sizeAlign : Nat
  sizePhase : Nat

inductive SizeInfo where
  | sized (bytes : Nat)
  | sliceDst (trailing : TrailingSliceLayout)

structure DstLayout where
  objAlign : Nat
  sizeInfo : SizeInfo

def DstLayout.sizeForElems (L : DstLayout) (elems : Nat) : Nat :=
  match L.sizeInfo with
  | .sized b => b
  | .sliceDst t => t.sizeBase + alignTo (t.sizePhase + elems * t.elemSize) t.sizeAlign

def natMin (a b : Nat) : Nat :=
  match Nat.ble a b with | true => a | false => b

def natMax (a b : Nat) : Nat :=
  match Nat.ble a b with | true => b | false => a

def zcExtend (cur fld : DstLayout) (packedOpt : Option Nat) : Option DstLayout :=
  let maxA := match packedOpt with | some p => p | none => 536870912
  let fAlign := natMin fld.objAlign maxA
  let newAlign := natMax cur.objAlign fAlign
  match cur.sizeInfo with
  | .sliceDst _ => none
  | .sized preSz =>
    let off := alignTo preSz fAlign
    match fld.sizeInfo with
    | .sized fSz => some ⟨newAlign, .sized (off + fSz)⟩
    | .sliceDst tr =>
      some ⟨newAlign, .sliceDst ⟨off + tr.offset, tr.elemSize, off + tr.sizeBase, tr.sizeAlign, tr.sizePhase⟩⟩

def zcPadToAlign (L : DstLayout) : DstLayout :=
  match L.sizeInfo with
  | .sized b => ⟨L.objAlign, .sized (alignTo b L.objAlign)⟩
  | .sliceDst tr =>
    match Nat.blt tr.sizeAlign L.objAlign with
    | true =>
      let roundedBase := alignTo tr.sizeBase tr.sizeAlign
      let fixed := roundedBase + tr.sizePhase
      let phase := Nat.mod fixed L.objAlign
      let base := fixed - phase
      ⟨L.objAlign, .sliceDst ⟨tr.offset, tr.elemSize, base, L.objAlign, phase⟩⟩
    | false =>
      let base := alignTo tr.sizeBase L.objAlign
      ⟨L.objAlign, .sliceDst ⟨tr.offset, tr.elemSize, base, tr.sizeAlign, tr.sizePhase⟩⟩

def miriPackedDstSizeAlign (packedOpt : Option Nat) (prefixFields : List (Nat × Nat))
    (tailDst : DstLayout) (elems : Nat) : Nat × Nat :=
  let pre := prefixFields.foldl
    (fun acc fld =>
      let fa := match packedOpt with | some p => natMin fld.2 p | none => fld.2
      (alignTo acc.1 fa + fld.1, natMax acc.2 fa))
    (0, 1)
  let tailSz := tailDst.sizeForElems elems
  let effTailAlign := match packedOpt with | some p => natMin tailDst.objAlign p | none => tailDst.objAlign
  let fullAlign := natMax pre.2 effTailAlign
  let adjusted := alignTo pre.1 effTailAlign
  (alignTo (adjusted + tailSz) fullAlign, fullAlign)

def fieldRefBorrowAllowed (fieldByteOffset fieldNatAlign : Nat) : Bool :=
  Nat.beq (Nat.mod fieldByteOffset fieldNatAlign) 0

def packedTailDropWf (isPacked tailIsSized tailNeedsDrop : Bool) : Bool :=
  (!isPacked) || tailIsSized || (!tailNeedsDrop)

def u8L : DstLayout := ⟨1, .sized 1⟩
def u32L : DstLayout := ⟨4, .sized 4⟩
def sliceU8L : DstLayout := ⟨1, .sliceDst ⟨0, 1, 0, 1, 0⟩⟩

def innerDst : DstLayout :=
  match zcExtend ⟨1, .sized 0⟩ u32L none with
  | some c1 =>
    match zcExtend c1 sliceU8L none with
    | some c2 => zcPadToAlign c2
    | none => ⟨1, .sized 0⟩
  | none => ⟨1, .sized 0⟩

def nestedPacked2Dst : DstLayout :=
  match zcExtend ⟨1, .sized 0⟩ u8L (some 2) with
  | some c1 =>
    match zcExtend c1 innerDst (some 2) with
    | some c2 => zcPadToAlign c2
    | none => ⟨1, .sized 0⟩
  | none => ⟨1, .sized 0⟩

theorem nestedPacked2_retains_inner_rounding :
    nestedPacked2Dst.objAlign = 2 ∧
    nestedPacked2Dst.sizeForElems 0 = 6 ∧
    nestedPacked2Dst.sizeForElems 1 = 10 ∧
    nestedPacked2Dst.sizeForElems 2 = 10 ∧
    nestedPacked2Dst.sizeForElems 5 = 14 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nestedPacked2_matches_miri_concrete :
    (nestedPacked2Dst.sizeForElems 0, nestedPacked2Dst.objAlign) =
      miriPackedDstSizeAlign (some 2) [(1, 1)] innerDst 0 ∧
    (nestedPacked2Dst.sizeForElems 1, nestedPacked2Dst.objAlign) =
      miriPackedDstSizeAlign (some 2) [(1, 1)] innerDst 1 ∧
    (nestedPacked2Dst.sizeForElems 5, nestedPacked2Dst.objAlign) =
      miriPackedDstSizeAlign (some 2) [(1, 1)] innerDst 5 := ⟨rfl, rfl, rfl⟩

theorem direct_packed_u32_tail_ref_rejected_even_at_zero_elems :
    fieldRefBorrowAllowed 5 4 = false := rfl

theorem packed_unsized_tail_drop_banned :
    packedTailDropWf true false true = false ∧
    packedTailDropWf true false false = true := ⟨rfl, rfl⟩

end Verification.PackedDstLayout
```

## Boundaries

`Basis: normative + source + derived`

- **`#[repr(Rust)]` field-reordering heuristics (`not examined`):** While `compiler/rustc_abi/src/layout.rs:655-745` (`alignment_group_key`, `NicheBias`) was inspected, empirical layouts across `-Z randomize-layout` permutations were `not examined`.
- **Unsized `dyn Trait` inside `#[repr(packed)]` (`unknown` / `unsupported`):** `wfcheck.rs:1056-1091` admits unsized tails in `#[repr(packed)]` only when `!tail_ty.needs_drop`; dynamic vtable drop-glue edges under `!needs_drop` generic bounds remain `unknown`, while packed `dyn Trait` tails with `needs_drop == true` are `unsupported`.
- **Misaligned hardware atomic accesses (`known not to apply`):** Even though Tree Borrows labels `UnsafeCell` bytes inside `AtomicU32` as `Permission.Cell`, hardware atomic loads/stores on misaligned packed fields are `known not to apply` (unconditionally UB).
- **Unsized `T` in `zerocopy::Unalign<T>` (`unsupported`):** `Unalign<T>` (`wrappers.rs:104-119`) requires `T: Sized`; `Unalign<[u32]>` is `unsupported` (use `[Unalign<u32>]`).
- **Dynamic Miri / Lean 4 execution (`not examined`):** Local `cargo miri` and `lean` CLI invocations were `not examined` dynamically during this pass; Python layout-equivalence and `FreezeVisitor` verification executed locally.

## Evidence

`Basis: source + documentation + execution`

- **`google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`):** `zerocopy/src/layout.rs:1153-1184, 1231-1377, 1405-1495`; `zerocopy/src/wrappers.rs:104-119, 149-169, 202-211, 292-315, 339-405`; `zerocopy/src/impls.rs:827-854`; `zerocopy/src/pointer/ptr.rs:439-545`; `zerocopy/zerocopy-derive/src/{repr.rs:31-174, derive/known_layout.rs:112-119, 202-223, derive/into_bytes.rs:99-118, 145-166}`.
- **`rust-lang/rust` (`4b5350e87e487aed08ab2f9f0160a4b2616438bc`):** `compiler/rustc_abi/src/layout.rs:417, 438, 488-493, 606, 780-816, 842-895, 931`; `compiler/rustc_hir_analysis/src/check/{check.rs:1668-1782, wfcheck.rs:1056-1091}`; `compiler/rustc_error_codes/src/error_codes/{E0587,E0588,E0509,E0793}.md`; `compiler/rustc_mir_transform/src/{check_packed_ref.rs:27-49, add_moves_for_packed_drops.rs:36-111, shim.rs:346-369, elaborate_drop.rs:733-750}`; `library/core/src/ptr/mod.rs:1842-1862, 1998-2065`; `library/core/src/cell.rs:438-443, 2436-2501`.
- **`rust-lang/reference` (`a286e1ecb8ce193d50056e4bb042eea9b23876ef`) & `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** `src/type-layout.md:632-680`; `src/behavior-considered-undefined.md:78-97, 147-159`; RFCs 2349 and 2582.
- **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`):** `Miri/Interpreter/{DynamicLayout.lean:49-71, Projection.lean:132-149, PlaceDynamic.lean:68-85, Rvalue.lean:80-104, MemoryOperand.lean:103-118, TypedRetag.lean:56-105}`, `Miri/TreeBorrows/FreezeVisitor.lean:49-117`; `trusted/audit/TrustedBoundary.lean:487-595`; Villani et al. (`10.1145/3735592`); Jung et al. (`10.1145/3371109`).
- **Probe Execution (`2026-11-20`, Python 3, Linux `x86_64`, `Basis: execution`):** Executed §Revalidation probe (`exit 0`), output: `PACKED_DST_PROBE_OK checked=1980 nested_sizes=[6, 10, 10, 14] perms=[(0, 1, 'Frozen'), (1, 5, 'Cell')]`.

## Revalidation

`Basis: execution + derived`

1. **Source Diff Checks:** Diff `zerocopy/src/{layout.rs,wrappers.rs,impls.rs}`, `compiler/rustc_abi/src/layout.rs`, `compiler/rustc_hir_analysis/src/check/{check.rs,wfcheck.rs}`, `compiler/rustc_mir_transform/src/{check_packed_ref.rs,add_moves_for_packed_drops.rs}`, and `Miri/Interpreter/DynamicLayout.lean`.
2. **Deterministic Packed-DST Equivalence & `FreezeVisitor` Probe (Python 3.10+ stdlib only, `< 0.1s`):**

```python
#!/usr/bin/env python3
from __future__ import annotations
from dataclasses import dataclass

def align_to(x: int, a: int) -> int:
    assert a > 0 and (a & (a - 1)) == 0
    rem = x % a
    return x if rem == 0 else x + (a - rem)

@dataclass(frozen=True)
class DstLayout:
    obj_align: int
    is_dst: bool
    sized_size: int = 0
    offset: int = 0
    elem_size: int = 0
    size_base: int = 0
    size_align: int = 1
    size_phase: int = 0

    @staticmethod
    def sized(size: int, align: int) -> "DstLayout":
        return DstLayout(obj_align=align, is_dst=False, sized_size=size)

    @staticmethod
    def slice_of(elem_size: int, elem_align: int) -> "DstLayout":
        return DstLayout(obj_align=elem_align, is_dst=True, offset=0, elem_size=elem_size, size_base=0, size_align=1, size_phase=0)

    def size_for_elems(self, elems: int) -> int:
        if not self.is_dst:
            return self.sized_size
        return self.size_base + align_to(self.size_phase + elems * self.elem_size, self.size_align)

def zc_for_repr_c_struct(repr_align: int | None, repr_packed: int | None, fields: list[DstLayout]) -> DstLayout:
    assert not (repr_align is not None and repr_packed is not None)
    cur = DstLayout.sized(0, repr_align if repr_align is not None else 1)
    max_align = repr_packed if repr_packed is not None else (1 << 29)
    for f in fields:
        assert not cur.is_dst
        field_align = min(f.obj_align, max_align)
        align = max(cur.obj_align, field_align)
        off = align_to(cur.sized_size, field_align)
        if not f.is_dst:
            cur = DstLayout.sized(off + f.sized_size, align)
        else:
            cur = DstLayout(obj_align=align, is_dst=True, offset=off + f.offset, elem_size=f.elem_size, size_base=off + f.size_base, size_align=f.size_align, size_phase=f.size_phase)
    if not cur.is_dst:
        return DstLayout.sized(align_to(cur.sized_size, cur.obj_align), cur.obj_align)
    if cur.size_align < cur.obj_align:
        rounded_base = align_to(cur.size_base, cur.size_align)
        fixed = rounded_base + cur.size_phase
        phase = fixed & (cur.obj_align - 1)
        return DstLayout(obj_align=cur.obj_align, is_dst=True, offset=cur.offset, elem_size=cur.elem_size, size_base=fixed - phase, size_align=cur.obj_align, size_phase=phase)
    return DstLayout(obj_align=cur.obj_align, is_dst=True, offset=cur.offset, elem_size=cur.elem_size, size_base=align_to(cur.size_base, cur.obj_align), size_align=cur.size_align, size_phase=cur.size_phase)

def miri_dynamic_size_align(repr_packed: int | None, prefix: list[tuple[int, int]], inner_dst: DstLayout, elems: int) -> tuple[int, int]:
    off, pre_align = 0, 1
    for f_size, f_align in prefix:
        fa = min(f_align, repr_packed) if repr_packed is not None else f_align
        pre_align = max(pre_align, fa)
        off = align_to(off, fa) + f_size
    tail_size = inner_dst.size_for_elems(elems)
    eff_tail_align = min(inner_dst.obj_align, repr_packed) if repr_packed is not None else inner_dst.obj_align
    full_align = max(pre_align, eff_tail_align)
    full_size = align_to(align_to(off, eff_tail_align) + tail_size, full_align)
    assert full_size == align_to(off + tail_size, full_align)
    return full_size, full_align

def freeze_visitor_byte_perms(field_spans: list[tuple[int, int, bool]], total_size: int) -> list[tuple[int, int, str]]:
    cursor, out = 0, []
    for off, sz, is_uc in field_spans:
        assert off >= cursor
        if off > cursor:
            out.append((cursor, off, "Frozen"))
        cursor = off
        if sz > 0:
            out.append((cursor, cursor + sz, "Cell" if is_uc else "Frozen"))
            cursor += sz
    if cursor < total_size:
        out.append((cursor, total_size, "Frozen"))
    return out

if __name__ == "__main__":
    checked_configs = 0
    for repr_packed in [None, 1, 2, 4, 8]:
        for pre_fields in [[(1, 1)], [(1, 1), (4, 4)], [(2, 2), (1, 1)]]:
            for inner_kind in [
                DstLayout.slice_of(4, 4),
                DstLayout.slice_of(1, 1),
                zc_for_repr_c_struct(None, None, [DstLayout.sized(4, 4), DstLayout.slice_of(1, 1)]),
                zc_for_repr_c_struct(None, None, [DstLayout.sized(1, 1), DstLayout.sized(8, 8), DstLayout.slice_of(2, 2)]),
            ]:
                zc = zc_for_repr_c_struct(None, repr_packed, [DstLayout.sized(s, a) for s, a in pre_fields] + [inner_kind])
                for elems in range(0, 33):
                    assert (zc.size_for_elems(elems), zc.obj_align) == miri_dynamic_size_align(repr_packed, pre_fields, inner_kind, elems)
                    checked_configs += 1
    direct = zc_for_repr_c_struct(None, 1, [DstLayout.sized(1, 1), DstLayout.sized(4, 4), DstLayout.slice_of(4, 4)])
    assert direct.obj_align == 1 and direct.offset == 5 and direct.size_align == 1 and (direct.offset % 4) != 0
    assert [direct.size_for_elems(n) for n in (0, 1, 2, 3)] == [5, 9, 13, 17]
    inner = zc_for_repr_c_struct(None, None, [DstLayout.sized(4, 4), DstLayout.slice_of(1, 1)])
    nested = zc_for_repr_c_struct(None, 2, [DstLayout.sized(1, 1), inner])
    assert nested.obj_align == 2 and nested.offset == 6 and nested.size_base == 6 and nested.size_align == 4
    assert [nested.size_for_elems(n) for n in (0, 1, 2, 5)] == [6, 10, 10, 14]
    perms = freeze_visitor_byte_perms([(0, 1, False), (1, 4, True)], 5)
    assert perms == [(0, 1, "Frozen"), (1, 5, "Cell")]
    print(f"PACKED_DST_PROBE_OK checked={checked_configs} nested_sizes={[nested.size_for_elems(n) for n in (0, 1, 2, 5)]} perms={perms}")
```

3. **Lean `v4.34.1` and Miri Replay:** Extract `Verification.PackedDstLayout` to `/tmp/PackedDstLayout.lean` and run `lean /tmp/PackedDstLayout.lean` (`5045d0056413`), and run `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test` contrasting `&packed.cell` (UB) against `UnsafeCell::raw_get(&raw const packed.cell)` (`read_unaligned`/`write_unaligned`, sound).
