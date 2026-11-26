-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Div.Basic
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-!
# Generic Wrapper, Const-Generic Array, and Pointer Instantiations

Formal specification for 90 captured items from unmodified `zerocopy/src/`
(`1` non-generic `unsafe` macro safety fence `util::macros::__unsafe` in
`scope.roots` plus `89` explicit concrete `--instantiate` monomorphizations in
`scope.instantiations`: `4` substantive generic `util::macro_util::must_use<T>`
functions at `bool`, `u32`, `u8`, and `usize`, and `85` generic trait sealing
markers across `Unalign<T>`, `ReadOnly<T>`, `Wrapping<T>`, `ManuallyDrop<T>`,
`core::mem::MaybeUninit<T>`, `wrappers::MaybeUninit<T>`, `[T; N]`,
`PhantomData<T>`, `*const T`, `*mut T`, `AtomicPtr<T>`, `UnsafeCell<T>`,
`Cell<T>`, and `Option<T>`), paired with
`Trusted.MirSemantics.{Bytes,Layout,Memory}` theorems and explicitly labeled
`Spec`-local array codecs:

1. **Captured monomorphized MIR contract (`CapturedGenericMatrixSpec`):** Binds
   all 90 captured `Program.bodies` in exact `DefId` order (`0..89`):
   - `util::macros::__unsafe` (`isUnsafe = true`, `argumentCount = 0`, total
     `()` return and memory-preserving 2-step execution across every
     `MemoryState`);
   - `util::macro_util::must_use::<{bool, u32, u8, usize}>`
     (`isUnsafe = false`, `argumentCount = 1`, universally quantified total
     identity return `ReturnsTotal program defId [v] v` and 2-step
     `Operand.move` execution preserving every `MemoryState`); and
   - `85` monomorphized `only_derive_is_allowed_to_implement_this_trait` markers
     (`isUnsafe = false`, `argumentCount = 0`, `ReturnsTotal` returning `()`,
     and memory-preserving 2-step execution across every `MemoryState`).
   Other generic methods in `wrappers.rs`, `lib.rs`, and `util/` remain outside
   Profile v1 (`Unalign::new`, `ReadOnly::{new,into_inner}`, and
   `MaybeUninit::uninit` have ADT locals; `Unalign::into_inner`,
   `MaybeUninit::{new,assume_init}`, and `validate_aligned_to` emit unwind
   cleanup blocks; `Unalign::{get,deref_unchecked}` take `&` references;
   `Unalign::{get_ptr,get_mut_ptr}`, `AsAddress::addr`, and
   `KnownLayout::{raw_from_ptr_len,pointer_to_metadata}` use raw pointers;
   `macro_util::__size_of::size_of` emits `TerminatorKind::Call`).
2. **Model-side wrapper, array, pointer, and ZST laws
   (`GenericWrapperAndArrayModelSpec`):**
   - *Proved directly on `Trusted.MirSemantics.{Bytes,Layout,Memory}`:*
     - **`Unalign<T>` alignment-1 vs. aligned indirect memory access:** Proves
       on `writeBytes`, `readBytes`, `loadIndirect`, and `storeIndirect` that
       `alignLog2 = 0` (`2^0 = 1`) reads and writes any encoded Day-1 value
       `encodeVal` at every in-bounds byte offset `off` (including odd offsets)
       and recovers the exact bytes, whereas `loadIndirect` and
       `storeIndirect` at `off = 1` fault with `.error .undefined` for every
       multi-byte integer width `w ≠ .i8` (`0 < (intLayout w).alignLog2`).
     - **`MaybeUninit<T>` uninitialized-byte refusal:** Proves on
       `Trusted.MirSemantics.Bytes` that for every integer width `w`, sign
       `s`, and `TargetEndian`, `uninitBuf := List.replicate w.byteSize .uninit`
       has `initBytes? uninitBuf = none`, decodes via `decodeVal` as
       `.ok none`, and can never equal `encodeVal endian (.int w s) v`.
     - **64-bit thin-pointer `is_zeroed` and ZST `0`-byte laws:** Proves
       `(intLayout .isize).size = 8` and
       `decodeUInt endian raw = 0 ↔ raw = List.replicate 8 0` for all 8-byte
       buffers (with non-zero refutation at `1 :: List.replicate 7 0`), plus
       `0`-byte `readBytes`/`writeBytes` known-allocation totality and `.unit`
       trait laws modeling ZST `PhantomData<T>`.
   - *`Spec`-local array codec & Profile v1 boundaries:* Because Profile v1
     (`layoutOfTy`, `encodeVal`, `decodeVal`) does not lower `Struct`, `Union`,
     `Array`, `Slice`, or raw pointers (`MirTy.array`, `MirTy.slice`, and
     `MirTy.rawPtr` are Profile v2 only), `[T; N]` contiguous array lifting
     (`encodeArray`/`decodeArray` proving `IsFromZeros`/`IsFromBytes`/
     `IsIntoBytes` over `n` elements for all 12 integer types, plus `[bool; 4]`
     `0x02` `FromBytes` refutation) is defined as a `Spec`-local codec over
     `Trusted.MirSemantics.Bytes`. `Immutable` interior-mutability soundness is
     not modeled; Part 1 only records which selected `Immutable` impls exist
     (e.g. `ReadOnly<UnsafeCell<u32>>`), and the absence of `Immutable` for
     `UnsafeCell`/`Cell` is not verified by this unit.
-/

/-- `u8` value wrapper into `Trusted.MirAst.Val`. -/
def u8Val (n : BitVec 8) : Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 n.toNat⟩

/-- `u32` value wrapper into `Trusted.MirAst.Val`. -/
def u32Val (n : BitVec 32) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n.toNat⟩

/-- `usize` (64-bit) value wrapper into `Trusted.MirAst.Val`. -/
def usizeVal (n : BitVec 64) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

/-- Closed 6-kind tag (`Fin 6`) for captured items in `Program.bodies`:
`0 = unsafeFence`, `1 = safeMarker`, `2 = mustUseBool`, `3 = mustUseU32`,
`4 = mustUseU8`, `5 = mustUseUsize` (represented via `Fin 6 × String` so no
equation-compiler or recursor auxiliary triggers `unused_spec_binding`). -/
abbrev BodyContract : Type := Fin 6 × String

def bcUnsafeFence (identity : String) : BodyContract :=
  (⟨0, Nat.zero_lt_succ 5⟩, identity)

def bcSafeMarker (identity : String) : BodyContract :=
  (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 4)⟩, identity)

def bcMustUseBool (identity : String) : BodyContract :=
  (⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 3))⟩, identity)

def bcMustUseU32 (identity : String) : BodyContract :=
  (⟨3, Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2)))⟩, identity)

def bcMustUseU8 (identity : String) : BodyContract :=
  (⟨4, Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1))))⟩, identity)

def bcMustUseUsize (identity : String) : BodyContract :=
  (⟨5, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ
    (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0)))))⟩, identity)

/-- Exact 90-entry catalog of captured items in `Program.bodies` (`0..89`). -/
def genericUnitCatalog : List BodyContract := [
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for *const u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for *mut u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::mem::maybe_uninit::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::_::<impl KnownLayout for wrappers::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::<impl TryFromBytes for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::mem::maybe_uninit::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromBytes for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for *const u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for *mut u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::mem::maybe_uninit::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<&u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl FromZeros for core::option::Option<core::ptr::non_null::NonNull<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for *const u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for *mut u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for core::mem::maybe_uninit::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Immutable for core::option::Option<core::num::nonzero::NonZero<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl IntoBytes for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for *const u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for *mut u8>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for [u32; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::mem::manually_drop::ManuallyDrop<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::mem::maybe_uninit::MaybeUninit<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::num::wrapping::Wrapping<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<&u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl TryFromBytes for core::option::Option<core::ptr::non_null::NonNull<u8>>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for [u8; 4]>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::cell::Cell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::cell::UnsafeCell<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::marker::PhantomData<*const u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::mem::manually_drop::ManuallyDrop<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::mem::maybe_uninit::MaybeUninit<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::_::<impl Unaligned for core::num::wrapping::Wrapping<u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::atomics::atomic_ptr::_::<impl FromZeros for core::sync::atomic::Atomic<*mut u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::atomics::atomic_ptr::_::<impl KnownLayout for core::sync::atomic::Atomic<*mut u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::impls::atomics::atomic_ptr::_::<impl TryFromBytes for core::sync::atomic::Atomic<*mut u8>>::only_derive_is_allowed_to_implement_this_trait",
  bcMustUseBool
    "rust-path-v1::util::macro_util::must_use::<bool>",
  bcMustUseU32
    "rust-path-v1::util::macro_util::must_use::<u32>",
  bcMustUseU8
    "rust-path-v1::util::macro_util::must_use::<u8>",
  bcMustUseUsize
    "rust-path-v1::util::macro_util::must_use::<usize>",
  bcUnsafeFence
    "rust-path-v1::util::macros::__unsafe",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl FromBytes for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl FromBytes for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl FromZeros for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl FromZeros for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl Immutable for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl Immutable for wrappers::read_only_def::ReadOnly<core::cell::UnsafeCell<u32>>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl Immutable for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl IntoBytes for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl IntoBytes for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl KnownLayout for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl KnownLayout for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl TryFromBytes for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl TryFromBytes for wrappers::read_only_def::ReadOnly<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl Unaligned for wrappers::Unalign<u32>>::only_derive_is_allowed_to_implement_this_trait",
  bcSafeMarker
    "rust-path-v1::wrappers::_::<impl Unaligned for wrappers::read_only_def::ReadOnly<u8>>::only_derive_is_allowed_to_implement_this_trait"
]

/-! ## Part 1: Captured Monomorphized MIR Contract -/

/-- Total-correctness MIR call outcome at `defId` with empty caller memory. -/
def ReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

/-- Typed, non-vacuous per-contract input domain for `Specs.safety`. -/
def ContractValidArgs (args : List Val) (c : BodyContract) : Prop :=
  if Nat.beq c.1.val 2 then ∃ b : Bool, args = [.bool b]
  else if Nat.beq c.1.val 3 then ∃ n : BitVec 32, args = [u32Val n]
  else if Nat.beq c.1.val 4 then ∃ n : BitVec 8, args = [u8Val n]
  else if Nat.beq c.1.val 5 then ∃ n : BitVec 64, args = [usizeVal n]
  else args = []

/-- Non-vacuous identity-keyed safety precondition over all 90 captured items.
-/
def safetyPrecondition (identity : String) (args : List Val) : Prop :=
  ∃ c : BodyContract,
    c ∈ genericUnitCatalog ∧
    c.2 = identity ∧
    ContractValidArgs args c

/-- Two-step memory-preserving execution of a zero-argument `()` body
(`isUnsafe` parameterized so `unsafeFence` and `safeMarker` share the exact step
relation). -/
def ZeroArgUnitBodyAt (program : Program) (defId : DefId)
    (identity : String) (expectedUnsafe : Bool) : Prop :=
  ∃ b : Body,
    Trusted.MirSemantics.getElem? program.bodies defId = some b ∧
    b.identity = identity ∧
    b.isUnsafe = expectedUnsafe ∧
    b.argumentCount = 0 ∧
    ReturnsTotal program defId [] .unit ∧
    ∀ mem : MemoryState,
      ∃ s₁ : State,
        Step program
          { frames := [⟨defId, 0, 0, [.immediate none], none, none, none⟩],
             callerMem := ⟨[]⟩, mem := mem }
          (.step s₁) ∧
        s₁.mem = mem ∧
        Step program s₁ (.done (.returned ⟨.unit, ⟨[]⟩⟩))

/-- Two-step memory-preserving `Operand.move` identity execution for a
1-argument `util::macro_util::must_use::<T>` instantiation at `ty : MirTy`. -/
def UnaryMoveIdentityAt {α : Type} (program : Program)
    (defId : DefId) (identity : String) (ty : MirTy) (encode : α → Val) :
    Prop :=
  ∃ b : Body,
    Trusted.MirSemantics.getElem? program.bodies defId = some b ∧
    b.identity = identity ∧
    b.isUnsafe = false ∧
    b.argumentCount = 1 ∧
    b.locals = [ty, ty] ∧
    ∀ x : α,
      ReturnsTotal program defId [encode x] (encode x) ∧
      ∀ mem : MemoryState,
        ∃ s₁ : State,
          Step program
            { frames := [⟨defId, 0, 0,
                [.immediate none, .immediate (some (encode x))],
                none, none, none⟩],
               callerMem := ⟨[]⟩, mem := mem }
            (.step s₁) ∧
          s₁.mem = mem ∧
          Step program s₁ (.done (.returned ⟨encode x, ⟨[]⟩⟩))

/-- Dispatch each `BodyContract` entry at `defId` to its full MIR specification.
-/
def BodyContractAt (program : Program) (defId : DefId)
    (c : BodyContract) : Prop :=
  if Nat.beq c.1.val 0 then ZeroArgUnitBodyAt program defId c.2 true
  else if Nat.beq c.1.val 2 then
    UnaryMoveIdentityAt program defId c.2 .bool Val.bool
  else if Nat.beq c.1.val 3 then
    UnaryMoveIdentityAt program defId c.2 (.int .i32 false) u32Val
  else if Nat.beq c.1.val 4 then
    UnaryMoveIdentityAt program defId c.2 (.int .i8 false) u8Val
  else if Nat.beq c.1.val 5 then
    UnaryMoveIdentityAt program defId c.2 (.int .isize false) usizeVal
  else ZeroArgUnitBodyAt program defId c.2 false

/-- Complete MIR contract over all 90 captured items in `Program.bodies`. -/
def CapturedGenericMatrixSpec (program : Program) : Prop :=
  program.bodies.length = genericUnitCatalog.length ∧
  ∀ (defId : DefId) (c : BodyContract),
    Trusted.MirSemantics.getElem? genericUnitCatalog defId = some c →
    BodyContractAt program defId c

/-! ## Part 2: `Trusted.MirSemantics` & `Spec`-Local Wrapper/Array Models -/

/-- `FromZeros` byte-validity contract on `Trusted.MirSemantics.Bytes`. -/
def IsFromZeros (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ (layout : LayoutData) (v : Val),
    layoutOfTy ty = some layout ∧
    decodeVal endian ty (List.replicate layout.size (.init 0 none)) =
      .ok (some v) ∧
    checkVal v ty = true

/-- `FromBytes` byte-validity contract on `Trusted.MirSemantics.Bytes`. -/
def IsFromBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout : LayoutData,
    layoutOfTy ty = some layout ∧
    ∀ (bs : List AllocByte) (raw : List UInt8),
      bs.length = layout.size →
      initBytes? bs = some raw →
      ∃ v : Val, decodeVal endian ty bs = .ok (some v) ∧ checkVal v ty = true

/-- `IntoBytes` byte-validity contract on `Trusted.MirSemantics.Bytes` (every
well-formed value encodes to `layout.size` initialized provenance-free bytes).
-/
def IsIntoBytes (endian : TargetEndian) (ty : MirTy) : Prop :=
  ∃ layout : LayoutData,
    layoutOfTy ty = some layout ∧
    (∀ v : Val, checkVal v ty = true →
      ∃ bs : List AllocByte, encodeVal endian ty v = .ok bs) ∧
    (∀ (v : Val) (bs : List AllocByte),
      encodeVal endian ty v = .ok bs →
      bs.length = layout.size ∧
      ∃ raw : List UInt8,
        initBytes? bs = some raw ∧
        bs = raw.map (fun b => AllocByte.init b none))

/-- `Unaligned` layout contract on `Trusted.MirSemantics.Layout`
(`alignLog2 = 0`, i.e., 1-byte alignment). -/
def IsUnaligned (ty : MirTy) : Prop :=
  ∃ layout : LayoutData, layoutOfTy ty = some layout ∧ layout.alignLog2 = 0

/-- Single-allocation test `MemoryState` with `allocId = 1`, `alignLog2 = 4`,
mutable `17` uninitialized bytes (used to contrast `alignLog2 = 0` vs.
multi-byte `loadIndirect`/`storeIndirect` at odd offset `1`). -/
def sampleUnalignedArena : MemoryState :=
  { nextAllocId := 2,
    allocations := [{
      allocId := 1,
      alignLog2 := 4,
      mutability := .mut,
      bytes := List.replicate 17 .uninit,
      live := true
    }] }

/-- `Trusted.MirSemantics.Memory` alignment-1 (`Unalign<T>`) vs. naturally
aligned indirect access theorem:
1. For every single-allocation mutable `MemoryState` (`alloc.live = true`),
   non-ZST `ty` (`layoutOfTy ty = some layout`, `0 < layout.size`), encoded
   value `encodeVal profileTargetEndian ty v = .ok bs` (`bs.length =
   layout.size`), and arbitrary in-bounds byte offset `off` (`off + layout.size
   ≤ alloc.bytes.length`), `writeBytes` at `alignLog2 = 0` succeeds and
   `readBytes` at `alignLog2 = 0` recovers `.ok bs` regardless of `off`'s
   alignment.
2. Conversely, at odd offset `1` inside `sampleUnalignedArena`, `loadIndirect`
   and `storeIndirect` fault with `.error .undefined` for every multi-byte
   integer type `.int w s` (`w ≠ .i8`), while `writeBytes`/`readBytes` at
   `alignLog2 = 0` followed by `decodeVal` succeeds for every `BitVec 32` `u32`
   scalar and recovers the exact `Val`. -/
def UnalignMemorySound : Prop :=
  (∀ (alloc : Allocation) (nextId off : Nat) (ty : MirTy)
      (layout : LayoutData) (v : Val) (bs : List AllocByte),
    alloc.live = true →
    alloc.mutability = .mut →
    layoutOfTy ty = some layout →
    0 < layout.size →
    encodeVal profileTargetEndian ty v = .ok bs →
    bs.length = layout.size →
    off + layout.size ≤ alloc.bytes.length →
    let m : MemoryState := { nextAllocId := nextId, allocations := [alloc] }
    let place : MemPlace := ⟨alloc.allocId, off⟩
    ∃ m' : MemoryState,
      writeBytes m place 0 bs = .ok m' ∧
      readBytes m' place layout.size 0 = .ok bs) ∧
  (∀ (w : IntWidth) (s : Bool), w ≠ .i8 →
    loadIndirect sampleUnalignedArena (.int w s) ⟨1, 1⟩ = .error .undefined ∧
    ∀ v : Val, checkVal v (.int w s) = true →
      storeIndirect sampleUnalignedArena (.int w s) ⟨1, 1⟩ v =
        .error .undefined) ∧
  (∀ x : BitVec 32,
    ∃ (bs : List AllocByte) (m' : MemoryState),
      encodeVal profileTargetEndian (.int .i32 false) (u32Val x) = .ok bs ∧
      writeBytes sampleUnalignedArena ⟨1, 1⟩ 0 bs = .ok m' ∧
      readBytes m' ⟨1, 1⟩ 4 0 = .ok bs ∧
      decodeVal profileTargetEndian (.int .i32 false) bs =
        .ok (some (u32Val x)))

/-- `Spec`-local contiguous array encoder concatenating `encodeVal` byte slices
back-to-back with zero inter-element padding (Profile v1 `layoutOfTy`,
`encodeVal`, and `decodeVal` do not handle `[T; N]`; `MirTy.array` is Profile
v2 only). -/
noncomputable def encodeArray (endian : TargetEndian) (ty : MirTy) :
    List Val → Except FaultKind (List AllocByte)
  | [] => .ok []
  | v :: vs =>
    match encodeVal endian ty v, encodeArray endian ty vs with
    | .ok bs, .ok rest => .ok (bs ++ rest)
    | .error k, _ => .error k
    | .ok _, .error k => .error k

/-- `Spec`-local contiguous `n`-element array decoder slicing `n * elemSize`
bytes into `elemSize`-byte element windows (`MirTy` Profile v1 does not model
`[T; N]`). -/
noncomputable def decodeArray (endian : TargetEndian) (ty : MirTy)
    (elemSize : Nat) : Nat → List AllocByte →
      Except FaultKind (Option (List Val))
  | 0, bs =>
    if Nat.beq bs.length 0 then .ok (some []) else .error .unsupported
  | n + 1, bs =>
    if !Nat.beq bs.length ((n + 1) * elemSize) then
      .error .unsupported
    else
      match decodeVal endian ty (bs.take elemSize),
          decodeArray endian ty elemSize n (bs.drop elemSize) with
      | .error k, _ => .error k
      | .ok _, .error k => .error k
      | .ok (some v), .ok (some vs) => .ok (some (v :: vs))
      | .ok none, .ok _ => .ok none
      | .ok (some _), .ok none => .ok none

/-- `Spec`-local `FromZeros` contract for `[T; n]` over `decodeArray`. -/
def ArrayFromZeros (endian : TargetEndian) (ty : MirTy)
    (n : Nat) : Prop :=
  ∃ (layout : LayoutData) (vs : List Val),
    layoutOfTy ty = some layout ∧
    decodeArray endian ty layout.size n
      (List.replicate (n * layout.size) (.init 0 none)) = .ok (some vs) ∧
    vs.length = n ∧
    ∀ v : Val, v ∈ vs → checkVal v ty = true

/-- `Spec`-local `FromBytes` contract for `[T; n]` over `decodeArray`. -/
def ArrayFromBytes (endian : TargetEndian) (ty : MirTy)
    (n : Nat) : Prop :=
  ∃ layout : LayoutData,
    layoutOfTy ty = some layout ∧
    ∀ (bs : List AllocByte) (raw : List UInt8),
      bs.length = n * layout.size →
      initBytes? bs = some raw →
      ∃ vs : List Val,
        decodeArray endian ty layout.size n bs = .ok (some vs) ∧
        vs.length = n ∧
        ∀ v : Val, v ∈ vs → checkVal v ty = true

/-- `Spec`-local `IntoBytes` contract for `[T; n]` over `encodeArray` (every
well-formed `n`-element vector encodes to `n * layout.size` initialized
provenance-free bytes). -/
def ArrayIntoBytes (endian : TargetEndian) (ty : MirTy)
    (n : Nat) : Prop :=
  ∃ layout : LayoutData,
    layoutOfTy ty = some layout ∧
    ∀ vs : List Val,
      vs.length = n →
      (∀ v : Val, v ∈ vs → checkVal v ty = true) →
      ∃ (bs : List AllocByte) (raw : List UInt8),
        encodeArray endian ty vs = .ok bs ∧
        bs.length = n * layout.size ∧
        initBytes? bs = some raw ∧
        bs = raw.map (fun b => AllocByte.init b none)

/-- `Spec`-local `[T; N]` contiguous array lifting laws and `[bool; 4]`
`FromBytes` refutation over `Trusted.MirSemantics.Bytes`. -/
def ArrayCodecSound : Prop :=
  (∀ (endian : TargetEndian) (ty : MirTy) (n : Nat),
    (IsFromZeros endian ty → ArrayFromZeros endian ty n) ∧
    (IsFromBytes endian ty → ArrayFromBytes endian ty n) ∧
    (IsIntoBytes endian ty → ArrayIntoBytes endian ty n)) ∧
  (∀ (endian : TargetEndian) (w : IntWidth) (s : Bool) (n : Nat),
    ArrayFromZeros endian (.int w s) n ∧
    ArrayFromBytes endian (.int w s) n ∧
    ArrayIntoBytes endian (.int w s) n) ∧
  (∀ endian : TargetEndian,
    ArrayFromZeros endian .bool 4 ∧
    ArrayIntoBytes endian .bool 4 ∧
    decodeArray endian .bool 1 4
      [.init 0 none, .init 0 none, .init 2 none, .init 0 none] =
        .error .undefined ∧
    ¬ ArrayFromBytes endian .bool 4)

/-- `Trusted.MirSemantics.Bytes` uninitialized-buffer behavior for
`MaybeUninit<T>`: an all-`.uninit` slice has `initBytes? = none`, decodes via
`decodeVal` to `.ok none`, and is never produced by `encodeVal`. -/
def MaybeUninitSound : Prop :=
  ∀ (endian : TargetEndian) (w : IntWidth) (s : Bool),
    let uninitBuf := List.replicate w.byteSize AllocByte.uninit
    initBytes? uninitBuf = none ∧
    decodeVal endian (.int w s) uninitBuf = .ok none ∧
    ∀ v : Val, encodeVal endian (.int w s) v ≠ .ok uninitBuf

/-- 64-bit thin-pointer `pointer::is_zeroed` iff characterization and zero-sized
`PhantomData`-style `0`-byte memory/codec laws on `Trusted.MirSemantics`. -/
def PointerAndZstSound : Prop :=
  ((intLayout .isize).size = 8 ∧
    ∀ endian : TargetEndian,
      decodeUInt endian (List.replicate 8 (0 : UInt8)) = 0 ∧
      decodeUInt endian ((1 : UInt8) :: List.replicate 7 (0 : UInt8)) ≠ 0 ∧
      ∀ raw : List UInt8,
        raw.length = 8 →
        (decodeUInt endian raw = 0 ↔ raw = List.replicate 8 (0 : UInt8))) ∧
  (layoutOfTy .unit = some ⟨0, 0⟩ ∧
    (∀ endian : TargetEndian,
      IsFromZeros endian .unit ∧
      IsFromBytes endian .unit ∧
      IsIntoBytes endian .unit ∧
      IsUnaligned .unit) ∧
    (∀ (m : MemoryState) (place : MemPlace) (a : Allocation),
      findAllocation place.allocId m.allocations = some a →
      readBytes m place 0 0 = .ok [] ∧
      writeBytes m place 0 [] = .ok m))

/-- Combined Part 2 specification. -/
def GenericWrapperAndArrayModelSpec : Prop :=
  UnalignMemorySound ∧
  ArrayCodecSound ∧
  MaybeUninitSound ∧
  PointerAndZstSound

noncomputable def specs : Specs :=
  ⟨safetyPrecondition,
    fun program =>
      CapturedGenericMatrixSpec program ∧ GenericWrapperAndArrayModelSpec⟩

end Spec
