-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Control.Except
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics.Ops
public import Trusted.MirSemantics.Enum
public import Trusted.MirSemantics.Layout
public import Trusted.MirSemantics.Memory
public import Trusted.MirSemantics.Bytes

@[expose] public section

namespace Trusted.MirSemantics

open Trusted.MirAst

/-!
# Core Library Contract Semantics (`Trusted.MirSemantics.CoreContracts`)

Operational semantics for modeled `core` operations (`CoreCallOp` additions)
aligned with pinned `rustc` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
- `core::ops::Index` / `IndexMut` for `Range<usize>` and `RangeFrom<usize>`
- `core::num` scalar methods (`is_multiple_of`, `next_multiple_of`, `div_ceil`,
  `checked_{add,mul,sub,shl}`, `saturating_add`, `wrapping_{shl,shr}`,
  `leading_zeros`, `count_ones`, `trailing_zeros`, `next_power_of_two`,
  `overflowing_{add,sub,mul}`)
- `core::cmp::{min, max}`
- `core::slice::{is_empty, split_at, split_at_mut}`
- `core::mem::replace`
- `core::option::Option::{is_some, is_none, take, unwrap}`

Safe panicking traps (out-of-bounds slice and array ranges, `split_at` past
length, and `Option::unwrap` on `None`) return `CoreCallOutcome.panic` from
`execCoreContractOpOutcome`. `evalTerminatorV2` routes `.panic` through
`evalCorePanicAbort` (`.aborted` under an eligible `--panic abort`), while
`CoreCallOutcome.toExcept` maps it to `corePanicTrap` for `Except`-returning
callers such as `execCoreContractOp`.
-/

/-- Fail-closed trap returned when a safe `core` precondition panics
(distinct from `.undefined` memory UB; maps to `.unsupported` in this profile).
The slice-range, `split_at`, and `Option::unwrap` panics reach it only through
`CoreCallOutcome.toExcept`; `evalTerminatorV2` dispatches their
`CoreCallOutcome.panic` via `evalCorePanicAbort` instead.

Matches the panicking branches in `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`:
- `library/core/src/slice/index.rs:38-55` (`slice_index_fail`)
- `library/core/src/slice/mod.rs:1956,1990`: `None => panic!("mid > len")`
- `library/core/src/option.rs:2251-2253` (`unwrap_failed`:
  `panic("called `Option::unwrap()` on a `None` value")`) -/
noncomputable def corePanicTrap : FaultKind := .unsupported

/-- Outcome of evaluating a `CoreCallOp` with a modeled safe panic path
(distinct from structural `.unsupported` and memory-UB `.undefined` faults),
allowing `evalTerminatorV2` to map safe panics to `.done (.aborted ...)` under
`--panic abort` while keeping structural faults fail-closed. -/
inductive CoreCallOutcome where
  | ok (val : Val) (mem : MemoryState)
  | panic
  | fault (k : FaultKind)

/-- Project `CoreCallOutcome` to `Except FaultKind (Val × MemoryState)`,
mapping `.panic` to `corePanicTrap`. -/
noncomputable def CoreCallOutcome.toExcept :
    CoreCallOutcome → Except FaultKind (Val × MemoryState)
  | .ok v m => .ok (v, m)
  | .panic => .error corePanicTrap
  | .fault k => .error k

/-- Lift a contract result that has no modeled panic path into
`CoreCallOutcome`, mapping every error to `.fault`. -/
noncomputable def CoreCallOutcome.ofExcept :
    Except FaultKind (Val × MemoryState) → CoreCallOutcome
  | .ok (v, m) => .ok v m
  | .error k => .fault k

/-- Count leading zero bits across the lowest `n` bit positions of `bits`,
returning `w.bitWidth` when `bits = 0`. Mirrors `leading_zeros` in
`library/core/src/num/uint_macros.rs:153-155` and
`library/core/src/num/int_macros.rs:112-114` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const fn leading_zeros(self) -> u32 {
>     return intrinsics::ctlz(self as $ActualT);
> }" -/
noncomputable def leadingZerosFrom (bits : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if Nat.beq (Nat.land (Nat.shiftRight bits n) 1) 1 then 0
    else 1 + leadingZerosFrom bits n

/-- Count `1` bits across the lowest `n` bit positions of `bits`. Mirrors
`count_ones` in `library/core/src/num/uint_macros.rs:84-86` and
`library/core/src/num/int_macros.rs:76` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const fn count_ones(self) -> u32 {
>     return intrinsics::ctpop(self);
> }" -/
noncomputable def countOnesFrom (bits : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.land bits 1 + countOnesFrom (Nat.shiftRight bits 1) n

/-- Count trailing zero bits across the lowest `n` bit positions of `bits`,
returning `n` when all `n` low bits are `0`. Mirrors `trailing_zeros` in
`library/core/src/num/uint_macros.rs:177-179` and
`library/core/src/num/int_macros.rs:130-132` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const fn trailing_zeros(self) -> u32 {
>     return intrinsics::cttz(self);
> }" -/
noncomputable def trailingZerosFrom (bits : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    if Nat.beq (Nat.land bits 1) 1 then 0
    else 1 + trailingZerosFrom (Nat.shiftRight bits 1) n

/-- Compute `self.next_power_of_two()` on unsigned `w`-bit `bits`, failing
closed via `corePanicTrap` when `bits > 2^(w.bitWidth - 1)` (where `core`
overflows `one_less_than_next_power_of_two() + 1` and panics under
`#[rustc_inherit_overflow_checks]` or wraps to `0` in release). Mirrors
`library/core/src/num/uint_macros.rs:3873-3906` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const fn next_power_of_two(self) -> Self {
>     self.one_less_than_next_power_of_two() + 1
> }" -/
noncomputable def execNextPowerOfTwo (w : IntWidth) (bits : Nat) :
    Except FaultKind ScalarVal :=
  if Nat.blt (Nat.pow 2 (w.bitWidth - 1)) bits then
    .error corePanicTrap
  else
    let res :=
      if Nat.ble bits 1 then 1
      else
        let z := leadingZerosFrom (bits - 1) w.bitWidth
        let oneLess := Nat.shiftRight (Nat.pow 2 w.bitWidth - 1) z
        oneLess + 1
    .ok ⟨w, false, truncateBits w (BitVec.ofNat 128 res)⟩

/-- Compute `self.next_multiple_of(rhs)` on unsigned `w`-bit values, failing
closed via `corePanicTrap` when `rhs = 0` (`self % 0` panics) or when
`self + (rhs - r)` overflows `2^w.bitWidth` under
`#[rustc_inherit_overflow_checks]`. Mirrors
`library/core/src/num/uint_macros.rs:3789-3794` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "pub const fn next_multiple_of(self, rhs: Self) -> Self {
>     match self % rhs {
>         0 => self,
>         r => self + (rhs - r)
>     }
> }" -/
noncomputable def execNextMultipleOf (w : IntWidth) (l r : Nat) :
    Except FaultKind ScalarVal :=
  if Nat.beq r 0 then
    .error corePanicTrap
  else
    let rem := Nat.mod l r
    let res := if Nat.beq rem 0 then l else l + (r - rem)
    if Nat.ble (Nat.pow 2 w.bitWidth) res then
      .error corePanicTrap
    else
      .ok ⟨w, false, truncateBits w (BitVec.ofNat 128 res)⟩

/-- Signed maximum representable integer at width `w` (`2^(w - 1) - 1`). -/
noncomputable def signedMaxInt (w : IntWidth) : Int :=
  HPow.hPow (2 : Int) (w.bitWidth - 1) - 1

/-- Unsigned maximum representable integer at width `w` (`2^w - 1`). -/
noncomputable def unsignedMaxInt (w : IntWidth) : Int :=
  HPow.hPow (2 : Int) w.bitWidth - 1

/-- Detect mathematical overflow past the 128-bit `BitVec 128` carrier used by
`truncateScalar`, matching `hostOverflow` in `evalArithOp`. -/
noncomputable def intHostOverflow (s : Bool) (value : Int) : Bool :=
  if s then
    decide (value < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide (HPow.hPow (2 : Int) 127 ≤ value)
  else
    decide (value < 0) || decide (HPow.hPow (2 : Int) 128 ≤ value)

/-- Truncate mathematical integer `value` to `(w, s)`, reporting overflow when
`value` exceeds either `(w, s)` or the 128-bit host carrier. -/
noncomputable def truncateScalarWithHostOverflow (w : IntWidth) (s : Bool)
    (value : Int) : Except FaultKind (ScalarVal × Bool) :=
  match truncateScalar w s value with
  | .error k => .error k
  | .ok (sv, truncOvf) => .ok (sv, intHostOverflow s value || truncOvf)

/-- Saturate mathematical integer `value` to `(w, s)`, matching
`intrinsics::saturating_add(self, rhs)` in
`library/core/src/num/uint_macros.rs:2427-2429` and
`library/core/src/num/int_macros.rs:1959-1961` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). -/
noncomputable def saturateScalar (w : IntWidth) (s : Bool) (value : Int) :
    Except FaultKind ScalarVal :=
  match truncateScalarWithHostOverflow w s value with
  | .error k => .error k
  | .ok (sv, ovf) =>
    if !ovf then
      .ok sv
    else if s then
      if decide (value < 0) then
        .ok ⟨w, true, truncateBits w (bvOfInt 128 (signedMinInt w))⟩
      else
        .ok ⟨w, true, truncateBits w (bvOfInt 128 (signedMaxInt w))⟩
    else if decide (value < 0) then
      .ok ⟨w, false, 0⟩
    else
      .ok ⟨w, false, truncateBits w (bvOfInt 128 (unsignedMaxInt w))⟩

/-- Execute a checked integer arithmetic contract (`checked_{add,mul,sub}`)
returning `Option<T>`, matching `library/core/src/num/uint_macros.rs`
(`896-901`, `1050-1055`, `1288-1289`) and `library/core/src/num/int_macros.rs`
(`591-594`, `731-734`, `871-874`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "let (a, b) = self.overflowing_mul(rhs);
> if intrinsics::unlikely(b) { None } else { Some(a) }" -/
noncomputable def execCheckedArith (op : BinOp) (w : IntWidth) (s : Bool)
    (lSv rSv : ScalarVal) (m : MemoryState) :
    Except FaultKind (Val × MemoryState) :=
  let l := decodeScalar lSv
  let r := decodeScalar rSv
  let mathVal : Option Int :=
    match op with
    | .add => some (l + r)
    | .sub => some (l - r)
    | .mul => some (l * r)
    | _ => none
  match mathVal with
  | none => .error .unsupported
  | some v =>
    match truncateScalarWithHostOverflow w s v with
    | .error k => .error k
    | .ok (resSv, ovf) =>
      if ovf then .ok (.optionVal none, m)
      else .ok (.optionVal (some (.scalar resSv)), m)

/-- Execute an overflowing integer arithmetic contract
(`overflowing_{add,sub,mul}`) returning `(T, bool)`, matching
`library/core/src/num/uint_macros.rs:2955-2958,3054-3057,3177-3180` and
`library/core/src/num/int_macros.rs:2563-2566,2669-2672,2775-2778`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "let (a, b) = intrinsics::mul_with_overflow(self as $ActualT,
>     rhs as $ActualT);
> (a as Self, b)" -/
noncomputable def execOverflowingArith (op : BinOp) (w : IntWidth) (s : Bool)
    (lSv rSv : ScalarVal) (m : MemoryState) :
    Except FaultKind (Val × MemoryState) :=
  let l := decodeScalar lSv
  let r := decodeScalar rSv
  let mathVal : Option Int :=
    match op with
    | .add => some (l + r)
    | .sub => some (l - r)
    | .mul => some (l * r)
    | _ => none
  match mathVal with
  | none => .error .unsupported
  | some v =>
    match truncateScalarWithHostOverflow w s v with
    | .error k => .error k
    | .ok (resSv, ovf) =>
      .ok (.tuple [.scalar resSv, .bool ovf], m)

/-- Execute `core::ops::Index<Range<usize>>` or `Index<RangeFrom<usize>>` on
`&[elem]` / `&mut [elem]` (`index_mut` shares the same bounds and panic
behavior), returning `CoreCallOutcome` so out-of-bounds ranges return `.panic`
rather than `.fault`, matching `library/core/src/slice/index.rs:435-458,567-588`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "if let Some(new_len) = usize::checked_sub(self.end, self.start)
>     && self.end <= slice.len()"
> "if self.start > slice.len() {
>     slice_index_fail(self.start, slice.len(), slice.len())
> }" -/
noncomputable def execSliceSubsliceOutcome (m : MemoryState)
    (reqMut inMut : Mutability) (elem : MirTy) (p : PtrVal) (len : UInt64)
    (startOff endOff : Nat) : CoreCallOutcome :=
  if !isSizedNoRefV2Ty elem then
    .fault .unsupported
  else if Mutability.beq inMut .shared && Mutability.beq reqMut .mut then
    .fault .undefined
  else
    match refValidInMem m inMut (.slice elem) (.slicePtr p len) with
    | .error k => .fault k
    | .ok () =>
      if !Nat.ble startOff endOff || !Nat.ble endOff len.toNat then
        .panic
      else
        match layoutOfTyV2 elem with
        | none => .fault .unsupported
        | some lay =>
          match ptrAddInMem m lay.size p startOff with
          | .error k => .fault k
          | .ok p' => .ok (.slicePtr p' (UInt64.ofNat (endOff - startOff))) m

/-- `Except`-projected wrapper over `execSliceSubsliceOutcome`. -/
noncomputable def execSliceSubslice (m : MemoryState)
    (reqMut inMut : Mutability) (elem : MirTy) (p : PtrVal) (len : UInt64)
    (startOff endOff : Nat) : Except FaultKind (Val × MemoryState) :=
  (execSliceSubsliceOutcome m reqMut inMut elem p len startOff endOff).toExcept

/-- Execute `core::ops::Index<Range<usize>>` or `Index<RangeFrom<usize>>` on
`&[elem; len]` / `&mut [elem; len]` (`index_mut` shares the same bounds and
panic behavior), returning `CoreCallOutcome` so out-of-bounds ranges return
`.panic`, matching `library/core/src/array/mod.rs:383-405` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "fn index(&self, index: I) -> &Self::Output {
>     Index::index(self as &[T], index)
> }" -/
noncomputable def execArraySubsliceOutcome (m : MemoryState)
    (reqMut inMut : Mutability) (elem : MirTy) (len : Nat) (p : PtrVal)
    (startOff endOff : Nat) : CoreCallOutcome :=
  if !isSizedNoRefV2Ty elem || !Nat.blt len (Nat.pow 2 64) then
    .fault .unsupported
  else if Mutability.beq inMut .shared && Mutability.beq reqMut .mut then
    .fault .undefined
  else
    match refValidInMem m inMut (.array elem len) (.ptr p) with
    | .error k => .fault k
    | .ok () =>
      execSliceSubsliceOutcome m reqMut inMut elem p (UInt64.ofNat len)
        startOff endOff

/-- Execute `core::slice::split_at` or `split_at_mut` returning a structured
`CoreCallOutcome`: validates `elem`, forbids `&[T]` -> `&mut [T]` upgrades,
validates the input slice in `m`, returns `.panic` when `mid > len`, and
otherwise returns `(prefix, suffix)` where `prefix` covers `[p, p + mid*size)`
and `suffix` covers `[p + mid*size, p + len*size)` (disjoint spans whose union
equals the input span, preserving provenance on both subslices). Matches
`library/core/src/slice/mod.rs:1953-1958,1987-1992,2154-2162` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "match self.split_at_checked(mid) {
>     Some(pair) => pair,
>     None => panic!("mid > len"),
> }" -/
noncomputable def execSliceSplitAtOutcome (m : MemoryState)
    (reqMut inMut : Mutability) (elem : MirTy) (p : PtrVal) (len : UInt64)
    (mid : Nat) : CoreCallOutcome :=
  if !isSizedNoRefV2Ty elem then
    .fault .unsupported
  else if Mutability.beq inMut .shared && Mutability.beq reqMut .mut then
    .fault .undefined
  else
    match refValidInMem m inMut (.slice elem) (.slicePtr p len) with
    | .error k => .fault k
    | .ok () =>
      if !Nat.ble mid len.toNat then
        .panic
      else
        match layoutOfTyV2 elem with
        | none => .fault .unsupported
        | some lay =>
          match ptrAddInMem m lay.size p mid with
          | .error k => .fault k
          | .ok p' =>
            let prefixVal := Val.slicePtr p (UInt64.ofNat mid)
            let suffixVal := Val.slicePtr p' (UInt64.ofNat (len.toNat - mid))
            .ok (.tuple [prefixVal, suffixVal]) m

/-- Type-checked `CoreCallOp.sliceSplitAt` entry point returning
`CoreCallOutcome` so `evalTerminatorV2` can distinguish safe `mid > len`
panics from structural `.unsupported` and memory-UB `.undefined` faults. -/
noncomputable def execSliceSplitAtCall (m : MemoryState) (reqMut : Mutability)
    (elem : MirTy) (args : List (MirTy × Val)) (dstTy : MirTy) :
    CoreCallOutcome :=
  match args with
  | [(.ref inMut (.slice inElem), .slicePtr p len),
     (.int .isize false, .scalar midSv)] =>
    match dstTy with
    | .tuple [.ref outMut1 (.slice outE1), .ref outMut2 (.slice outE2)] =>
      if !MirTy.beq elem inElem || !MirTy.beq elem outE1 ||
          !MirTy.beq elem outE2 || !Mutability.beq reqMut outMut1 ||
          !Mutability.beq reqMut outMut2 then
        .fault .unsupported
      else
        let mid := (truncateBits .isize midSv.bits).toNat
        execSliceSplitAtOutcome m reqMut inMut elem p len mid
    | _ => .fault .unsupported
  | _ => .fault .unsupported

/-- Execute `core::mem::replace::<ty>(dst : &mut ty, src : ty) -> ty`,
matching `library/core/src/mem/mod.rs:916,930-932` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):

> "let result = crate::intrinsics::read_via_copy(dest);
> crate::intrinsics::write_via_move(dest, src);
> result" -/
noncomputable def execMemReplace (m : MemoryState) (ty : MirTy) (p : PtrVal)
    (srcVal : Val) : Except FaultKind (Val × MemoryState) :=
  if !isSizedNoRefV2Ty ty || !checkValV2 srcVal ty then
    .error .unsupported
  else if !refsValidInMem m ty srcVal then
    .error .undefined
  else
    match layoutOfTyV2 ty with
    | none => .error .unsupported
    | some lay =>
      match p.allocId with
      | none =>
        if Nat.beq p.offsetBytes.toNat 0 || Nat.blt 0 lay.size ||
            !Nat.beq (Nat.mod p.offsetBytes.toNat
              (Nat.pow 2 lay.alignLog2)) 0 then
          .error .undefined
        else
          match decodeValV2 profileV2TargetEndian ty [] with
          | .ok (some oldVal) => .ok (oldVal, m)
          | .ok none => .error .undefined
          | .error k => .error k
      | some aid =>
        match findAllocation aid m.allocations with
        | none => .error .undefined
        | some a =>
          if !a.live || !Mutability.beq a.mutability .mut then
            .error .undefined
          else
            let place : MemPlace := ⟨aid, p.offsetBytes.toNat⟩
            match loadIndirectV2 m ty place with
            | .error k => .error k
            | .ok none => .error .undefined
            | .ok (some oldVal) =>
              match storeIndirectV2 m ty place srcVal with
              | .error k => .error k
              | .ok m1 => .ok (oldVal, m1)

/-- Validate and read `&Option<inner>` from memory via pointer `p`
(`library/core/src/option.rs:597-606`, `rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). Fails closed unless `inner` has a
fixed ref-free representation and a verified `Option<inner>` layout. -/
noncomputable def loadOptionRefV2 (m : MemoryState) (reqMut : Mutability)
    (inner : MirTy) (p : PtrVal) : Except FaultKind (Option Val) :=
  let optTy := MirTy.option inner
  if !isSizedNoRefV2Ty inner || !isOptionPayloadSupportedV2 inner then
    .error .unsupported
  else
    match refValidInMem m reqMut optTy (.ptr p) with
    | .error k => .error k
    | .ok () =>
      match p.allocId with
      | none => .error .undefined
      | some aid =>
        match loadIndirectV2 m optTy ⟨aid, p.offsetBytes.toNat⟩ with
        | .error k => .error k
        | .ok (some (.optionVal v)) => .ok v
        | .ok _ => .error .undefined

/-- Execute `CoreCallOp` contract calls added for `core` scalars, slices,
`mem::replace`, `Range`, and `Option` (`rust-lang/rust`
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`). Existing Profile v2 slice and raw
pointer ops are handled in `execCoreCallOp` and wrapped via
`execCoreCallWithMem`.

Upstream implementations for non-helper arms:
- `<[T]>::is_empty` (`library/core/src/slice/mod.rs:136-138`):
  `self.len() == 0`
- `<uint>::is_multiple_of` (`library/core/src/num/uint_macros.rs:3840-3845`):
  `match rhs { 0 => self == 0, _ => self % rhs == 0 }`
- `<uint>::div_ceil` (`library/core/src/num/uint_macros.rs:3755-3763`):
  `if rhs == 0` panics (`corePanicTrap`); otherwise
  `let d := l / r; if l % r > 0 then d + 1 else d`
- `checked_shl` (`library/core/src/num/uint_macros.rs:1975-1983`,
  `int_macros.rs:1412-1420`):
  `if rhs < Self::BITS then Some(self.unchecked_shl(rhs)) else None`
- `wrapping_{shl,shr}` (`library/core/src/num/uint_macros.rs:2836,2880` and
  `int_macros.rs:2400,2437`): `self.unchecked_shl(rhs & (Self::BITS - 1))`
  (equivalent to `rhs % BITS` for power-of-2 integer widths)
- `Ord::min` (`library/core/src/cmp.rs:1073-1078`):
  `if other < self { other } else { self }` (returns `self` on equal values)
- `Ord::max` (`library/core/src/cmp.rs:1034-1039`):
  `if other < self { self } else { other }` (returns `other` on equal values)
- `Option::{is_some, is_none}` (`library/core/src/option.rs:632-634,681-683`):
  `matches!(*self, Some(_))` and `!self.is_some()`
- `Option::take` (`library/core/src/option.rs:1900-1903`):
  `mem::replace(self, None)`

This covers the operations without a modeled panic path;
`execCoreContractOpOutcome` dispatches the slice-range, `split_at`, and
`Option::unwrap` operations, which can panic. -/
noncomputable def execCoreContractOpInfallible (m : MemoryState)
    (op : CoreCallOp) (args : List (MirTy × Val)) (dstTy : MirTy) :
    Except FaultKind (Val × MemoryState) :=
  match op, args with
  | .sliceIsEmpty elem, [(.ref reqMut (.slice inElem), .slicePtr p len)] =>
    if !MirTy.beq elem inElem || !MirTy.beq dstTy .bool ||
        !isSizedNoRefV2Ty elem then
      .error .unsupported
    else
      match refValidInMem m reqMut (.slice elem) (.slicePtr p len) with
      | .error k => .error k
      | .ok () => .ok (.bool (Nat.beq len.toNat 0), m)
  | .numIsMultipleOf w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||
        !MirTy.beq dstTy .bool then
      .error .unsupported
    else
      let l := (truncateBits w lSv.bits).toNat
      let r := (truncateBits w rSv.bits).toNat
      if Nat.beq r 0 then .ok (.bool (Nat.beq l 0), m)
      else .ok (.bool (Nat.beq (Nat.mod l r) 0), m)
  | .numNextMultipleOf w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||
        !MirTy.beq dstTy (.int w false) then
      .error .unsupported
    else
      let l := (truncateBits w lSv.bits).toNat
      let r := (truncateBits w rSv.bits).toNat
      match execNextMultipleOf w l r with
      | .error k => .error k
      | .ok sv => .ok (.scalar sv, m)
  | .numDivCeil w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if s || ls || rs || !IntWidth.beq w lw || !IntWidth.beq w rw ||
        !MirTy.beq dstTy (.int w false) then
      .error .unsupported
    else
      let l := (truncateBits w lSv.bits).toNat
      let r := (truncateBits w rSv.bits).toNat
      if Nat.beq r 0 then
        .error corePanicTrap
      else
        let d := Nat.div l r
        let res := if Nat.blt 0 (Nat.mod l r) then d + 1 else d
        .ok (.scalar ⟨w, false, truncateBits w (BitVec.ofNat 128 res)⟩, m)
  | .numCheckedAdd w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.option (.int w s)) then
      .error .unsupported
    else
      execCheckedArith .add w s lSv rSv m
  | .numCheckedMul w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.option (.int w s)) then
      .error .unsupported
    else
      execCheckedArith .mul w s lSv rSv m
  | .numCheckedSub w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.option (.int w s)) then
      .error .unsupported
    else
      execCheckedArith .sub w s lSv rSv m
  | .numCheckedShl w s,
      [(.int lw ls, .scalar lSv), (.int .i32 false, .scalar rSv)] =>
    if !IntWidth.beq w lw || !(s == ls) ||
        !MirTy.beq dstTy (.option (.int w s)) then
      .error .unsupported
    else
      let amt := (truncateBits .i32 rSv.bits).toNat
      if !Nat.blt amt w.bitWidth then
        .ok (.optionVal none, m)
      else
        match evalShiftOp .shl w s (decodeScalar lSv) (Int.ofNat amt) with
        | .error k => .error k
        | .ok res => .ok (.optionVal (some res), m)
  | .numSaturatingAdd w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.int w s) then
      .error .unsupported
    else
      match saturateScalar w s (decodeScalar lSv + decodeScalar rSv) with
      | .error k => .error k
      | .ok sv => .ok (.scalar sv, m)
  | .numWrappingShl w s,
      [(.int lw ls, .scalar lSv), (.int .i32 false, .scalar rSv)] =>
    if !IntWidth.beq w lw || !(s == ls) || !MirTy.beq dstTy (.int w s) then
      .error .unsupported
    else
      let amt := Nat.mod (truncateBits .i32 rSv.bits).toNat w.bitWidth
      match evalShiftOp .shl w s (decodeScalar lSv) (Int.ofNat amt) with
      | .error k => .error k
      | .ok res => .ok (res, m)
  | .numWrappingShr w s,
      [(.int lw ls, .scalar lSv), (.int .i32 false, .scalar rSv)] =>
    if !IntWidth.beq w lw || !(s == ls) || !MirTy.beq dstTy (.int w s) then
      .error .unsupported
    else
      let amt := Nat.mod (truncateBits .i32 rSv.bits).toNat w.bitWidth
      match evalShiftOp .shr w s (decodeScalar lSv) (Int.ofNat amt) with
      | .error k => .error k
      | .ok res => .ok (res, m)
  | .numLeadingZeros w s, [(.int lw ls, .scalar lSv)] =>
    if !IntWidth.beq w lw || !(s == ls) ||
        !MirTy.beq dstTy (.int .i32 false) then
      .error .unsupported
    else
      let bits := (truncateBits w lSv.bits).toNat
      let count := leadingZerosFrom bits w.bitWidth
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 count)⟩, m)
  | .numCountOnes w s, [(.int lw ls, .scalar lSv)] =>
    if !IntWidth.beq w lw || !(s == ls) ||
        !MirTy.beq dstTy (.int .i32 false) then
      .error .unsupported
    else
      let bits := (truncateBits w lSv.bits).toNat
      let count := countOnesFrom bits w.bitWidth
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 count)⟩, m)
  | .numTrailingZeros w s, [(.int lw ls, .scalar lSv)] =>
    if !IntWidth.beq w lw || !(s == ls) ||
        !MirTy.beq dstTy (.int .i32 false) then
      .error .unsupported
    else
      let bits := (truncateBits w lSv.bits).toNat
      let count := trailingZerosFrom bits w.bitWidth
      .ok (.scalar ⟨.i32, false, truncateBits .i32 (BitVec.ofNat 128 count)⟩, m)
  | .numNextPowerOfTwo w s, [(.int lw ls, .scalar lSv)] =>
    if s || ls || !IntWidth.beq w lw || !MirTy.beq dstTy (.int w false) then
      .error .unsupported
    else
      match execNextPowerOfTwo w (truncateBits w lSv.bits).toNat with
      | .error k => .error k
      | .ok sv => .ok (.scalar sv, m)
  | .numOverflowingAdd w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.tuple [.int w s, .bool]) then
      .error .unsupported
    else
      execOverflowingArith .add w s lSv rSv m
  | .numOverflowingSub w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.tuple [.int w s, .bool]) then
      .error .unsupported
    else
      execOverflowingArith .sub w s lSv rSv m
  | .numOverflowingMul w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.tuple [.int w s, .bool]) then
      .error .unsupported
    else
      execOverflowingArith .mul w s lSv rSv m
  | .cmpMin w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.int w s) then
      .error .unsupported
    else if decide (decodeScalar lSv ≤ decodeScalar rSv) then
      .ok (.scalar lSv, m)
    else
      .ok (.scalar rSv, m)
  | .cmpMax w s,
      [(.int lw ls, .scalar lSv), (.int rw rs, .scalar rSv)] =>
    if !IntWidth.beq w lw || !IntWidth.beq w rw || !(s == ls) || !(s == rs) ||
        !MirTy.beq dstTy (.int w s) then
      .error .unsupported
    else if decide (decodeScalar rSv < decodeScalar lSv) then
      .ok (.scalar lSv, m)
    else
      .ok (.scalar rSv, m)
  | .memReplace ty, [(.ref .mut argPt, .ptr p), (srcTy, srcVal)] =>
    if !MirTy.beq ty argPt || !MirTy.beq ty srcTy || !MirTy.beq ty dstTy then
      .error .unsupported
    else
      execMemReplace m ty p srcVal
  | .optionIsSome inner, [(.ref reqMut (.option inInner), .ptr p)] =>
    if !MirTy.beq inner inInner || !MirTy.beq dstTy .bool then
      .error .unsupported
    else
      match loadOptionRefV2 m reqMut inner p with
      | .error k => .error k
      | .ok optV => .ok (.bool optV.isSome, m)
  | .optionIsNone inner, [(.ref reqMut (.option inInner), .ptr p)] =>
    if !MirTy.beq inner inInner || !MirTy.beq dstTy .bool then
      .error .unsupported
    else
      match loadOptionRefV2 m reqMut inner p with
      | .error k => .error k
      | .ok optV => .ok (.bool optV.isNone, m)
  | .optionTake inner, [(.ref .mut (.option inInner), .ptr p)] =>
    if !MirTy.beq inner inInner || !MirTy.beq dstTy (.option inner) then
      .error .unsupported
    else
      execMemReplace m (.option inner) p (.optionVal none)
  | _, _ => .error .unsupported

/-- Execute a `CoreContracts` operation returning `CoreCallOutcome`, so the
safe unconditional panics of `sliceIndexRange`, `sliceIndexRangeFrom`,
`sliceSplitAt`, and `optionUnwrap` on `None` return `.panic`, while structural
and UB errors return `.fault`. Every other operation lifts
`execCoreContractOpInfallible` via `CoreCallOutcome.ofExcept`.

`Option::unwrap` follows `library/core/src/option.rs:1010-1015,2251-2253`
(`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`):
`match self { Some(val) => val, None => unwrap_failed() }` -/
noncomputable def execCoreContractOpOutcome (m : MemoryState) (op : CoreCallOp)
    (args : List (MirTy × Val)) (dstTy : MirTy) : CoreCallOutcome :=
  match op, args with
  | .sliceIndexRange reqMut elem,
      [(.ref inMut (.slice inElem), .slicePtr p len),
       (.range (.int .isize false), .range startOff endOff)] =>
    match dstTy with
    | .ref outMut (.slice outElem) =>
      if !MirTy.beq elem inElem || !MirTy.beq elem outElem ||
          !Mutability.beq reqMut outMut then
        .fault .unsupported
      else
        execSliceSubsliceOutcome m reqMut inMut elem p len startOff.toNat
          endOff.toNat
    | _ => .fault .unsupported
  | .sliceIndexRange reqMut elem,
      [(.ref inMut (.array inElem len), .ptr p),
       (.range (.int .isize false), .range startOff endOff)] =>
    match dstTy with
    | .ref outMut (.slice outElem) =>
      if !MirTy.beq elem inElem || !MirTy.beq elem outElem ||
          !Mutability.beq reqMut outMut then
        .fault .unsupported
      else
        execArraySubsliceOutcome m reqMut inMut elem len p startOff.toNat
          endOff.toNat
    | _ => .fault .unsupported
  | .sliceIndexRangeFrom reqMut elem,
      [(.ref inMut (.slice inElem), .slicePtr p len),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)] =>
    match dstTy with
    | .ref outMut (.slice outElem) =>
      if !MirTy.beq elem inElem || !MirTy.beq elem outElem ||
          !Mutability.beq reqMut outMut then
        .fault .unsupported
      else
        execSliceSubsliceOutcome m reqMut inMut elem p len startOff.toNat
          len.toNat
    | _ => .fault .unsupported
  | .sliceIndexRangeFrom reqMut elem,
      [(.ref inMut (.array inElem len), .ptr p),
       (.rangeFrom (.int .isize false), .rangeFrom startOff)] =>
    match dstTy with
    | .ref outMut (.slice outElem) =>
      if !MirTy.beq elem inElem || !MirTy.beq elem outElem ||
          !Mutability.beq reqMut outMut then
        .fault .unsupported
      else
        execArraySubsliceOutcome m reqMut inMut elem len p startOff.toNat len
    | _ => .fault .unsupported
  | .sliceSplitAt reqMut elem, args =>
    execSliceSplitAtCall m reqMut elem args dstTy
  | .optionUnwrap inner, [(.option inInner, .optionVal optV)] =>
    if !MirTy.beq inner inInner || !MirTy.beq inner dstTy then
      .fault .unsupported
    else
      match optV with
      | some v =>
        if !refsValidInMem m inner v then
          .fault .undefined
        else
          .ok v m
      | none => .panic
  | .sliceIndexRange _ _, _ | .sliceIndexRangeFrom _ _, _
  | .optionUnwrap _, _ =>
    .fault .unsupported
  | _, _ =>
    CoreCallOutcome.ofExcept (execCoreContractOpInfallible m op args dstTy)

/-- `Except`-projected wrapper over `execCoreContractOpOutcome`, mapping
`.panic` to `corePanicTrap`. -/
noncomputable def execCoreContractOp (m : MemoryState) (op : CoreCallOp)
    (args : List (MirTy × Val)) (dstTy : MirTy) :
    Except FaultKind (Val × MemoryState) :=
  (execCoreContractOpOutcome m op args dstTy).toExcept

end Trusted.MirSemantics

end
