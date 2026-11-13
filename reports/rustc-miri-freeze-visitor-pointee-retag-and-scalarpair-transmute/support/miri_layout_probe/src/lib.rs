// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![cfg(test)]
#![allow(invalid_reference_casting, dead_code)]

use std::cell::UnsafeCell;
use std::marker::PhantomPinned;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::pin::Pin;

// ============================================================================
// Part 1(a): Struct mixing Freeze fields, padding, and UnsafeCell<u32>
// ============================================================================

#[repr(C)]
struct MixedStruct {
    a: u8,               // offset 0..1 (Frozen)
    // padding:          // offset 1..4 (Frozen! Swept into frozen_size = 4 - 0)
    b: UnsafeCell<u32>,  // offset 4..8 (Cell)
}

#[repr(C)]
struct TrailingPadStruct {
    cell: UnsafeCell<u32>, // offset 0..4 (Cell)
    flag: u8,              // offset 4..5 (Frozen)
    // trailing padding:   // offset 5..8 (Frozen! Swept by final end_ptr flush)
}

#[test]
fn struct_unsafecell_field_write_ok() {
    let s = MixedStruct { a: 7, b: UnsafeCell::new(10) };
    let r: &MixedStruct = &s;
    let raw_b = (r as *const MixedStruct as *mut u8).wrapping_add(4) as *mut u32;
    unsafe {
        *raw_b = 42;
        assert_eq!(*r.b.get(), 42);
        assert_eq!(r.a, 7);
    }
}

#[test]
#[ignore]
fn struct_padding_write_via_shared_ref_is_ub() {
    let s = MixedStruct { a: 7, b: UnsafeCell::new(10) };
    let r: &MixedStruct = &s;
    // Offset 1 is inter-field padding between `a: u8` (0..1) and `b: UnsafeCell<u32>` (4..8).
    // `visit_freeze_sensitive` marks [0..4) as `frozen = true` (`Permission::Frozen`).
    let raw_pad = (r as *const MixedStruct as *mut u8).wrapping_add(1);
    unsafe {
        *raw_pad = 0xAA;
    }
}

#[test]
#[ignore]
fn struct_trailing_padding_write_via_shared_ref_is_ub() {
    let s = TrailingPadStruct { cell: UnsafeCell::new(10), flag: 1 };
    let r: &TrailingPadStruct = &s;
    // Offset 5 is trailing padding after `flag: u8` (4..5).
    // The final `unsafe_cell_action(end_ptr, Size::ZERO)` marks [4..8) as `Frozen`.
    let raw_pad = (r as *const TrailingPadStruct as *mut u8).wrapping_add(5);
    unsafe {
        *raw_pad = 0xBB;
    }
}

// ============================================================================
// Part 1(b): Multi-variant enum vs. Single-inhabited-variant enum
// ============================================================================

#[repr(C, u64)]
enum MultiEnum {
    Frozen(u64),
    SharedMut(UnsafeCell<u64>),
}

enum Void {}

// In `repr(Rust)` (without `#[repr(C)]`), `absent(Dead(Void))` is true and
// `!repr.inhibit_enum_layout_opt()` is true (`rustc_abi/src/layout.rs:360, 378`),
// so `SingleInhabitedRustEnum` gets `Variants::Single { index: 0 }` and recurses into `MixedStruct`.
enum SingleInhabitedRustEnum {
    Active(MixedStruct),
    Dead(Void),
}

// By contrast, adding `#[repr(C)]` sets `repr.inhibit_enum_layout_opt() == true`, forcing
// `Variants::Multiple` even when `Dead(Void)` is uninhabited!
#[repr(C)]
enum SingleInhabitedReprCEnum {
    Active(MixedStruct),
    Dead(Void),
}

#[test]
fn multivariant_enum_mutate_frozen_payload_and_discriminant_ok() {
    let e = MultiEnum::Frozen(42);
    let r: &MultiEnum = &e;
    let raw_e = r as *const MultiEnum as *mut MultiEnum;
    let raw_payload = (raw_e as *mut u64).wrapping_add(1);
    unsafe {
        // 1. Mutate the `Frozen(u64)` payload through a pointer derived from `&MultiEnum`:
        *raw_payload = 99;
        match r {
            MultiEnum::Frozen(v) => assert_eq!(*v, 99),
            MultiEnum::SharedMut(_) => panic!("unexpected variant"),
        }
        // 2. Mutate the discriminant tag AND payload to `SharedMut` while `r: &MultiEnum` is live:
        *raw_e = MultiEnum::SharedMut(UnsafeCell::new(777));
        match r {
            MultiEnum::Frozen(_) => panic!("unexpected variant"),
            MultiEnum::SharedMut(c) => assert_eq!(*c.get(), 777),
        }
    }
}

#[test]
fn repr_c_uninhabited_variant_forces_variants_multiple_cell_ok() {
    // Because `#[repr(C)]` sets `inhibit_enum_layout_opt() = true`, `SingleInhabitedReprCEnum`
    // has `Variants::Multiple` and therefore its entire range (including `MixedStruct.a`) is `Cell`!
    let e = SingleInhabitedReprCEnum::Active(MixedStruct { a: 10, b: UnsafeCell::new(20) });
    let r: &SingleInhabitedReprCEnum = &e;
    let SingleInhabitedReprCEnum::Active(inner_ref) = r else { unreachable!() };
    // Write to `a` through a pointer with `r`'s provenance (not `inner_ref`'s retagged provenance):
    let offset_of_a = (std::ptr::addr_of!(inner_ref.a) as usize) - (r as *const _ as usize);
    let raw_a_from_r = (r as *const SingleInhabitedReprCEnum as *mut u8).wrapping_add(offset_of_a);
    unsafe {
        *raw_a_from_r = 99;
    }
}

#[test]
#[ignore]
fn single_inhabited_variant_enum_freezes_frozen_field_ub() {
    // In `repr(Rust)`, `Dead(Void)` is pruned as `absent`, so `SingleInhabitedRustEnum` has
    // `Variants::Single { index: 0 }`. `UnsafeCellVisitor` walks into `Active(MixedStruct)`
    // and freezes `MixedStruct.a` ([0..4) is `Permission::Frozen`)!
    let e = SingleInhabitedRustEnum::Active(MixedStruct { a: 10, b: UnsafeCell::new(20) });
    let r: &SingleInhabitedRustEnum = &e;
    let raw_a = r as *const SingleInhabitedRustEnum as *mut u8;
    unsafe {
        *raw_a = 99;
    }
}

// ============================================================================
// Part 1(c): Unions with UnsafeCell variant vs. all-Freeze variants
// ============================================================================

#[repr(C)]
union UnionWithSmallCell {
    a: u64,
    b: ManuallyDrop<UnsafeCell<u32>>,
}

#[repr(C)]
union UnionAllFreeze {
    a: u64,
    b: u32,
}

#[test]
fn union_with_unsafecell_entire_size_is_cell_ok() {
    let u = UnionWithSmallCell { a: 0x0102_0304_0506_0708 };
    let r: &UnionWithSmallCell = &u;
    // Write to bytes 4..8 (outside the 4-byte `UnsafeCell<u32>` field `b`, inside `a: u64`).
    // Because `FieldsShape::Union` with `!is_freeze` calls `unsafe_cell_action` on the entire
    // union place [0..8), bytes [4..8) are ALSO `Permission::Cell`.
    let raw_upper = (r as *const UnionWithSmallCell as *mut u32).wrapping_add(1);
    unsafe {
        *raw_upper = 0xDEAD_BEEF;
        let _ = r.a;
    }
}

#[test]
#[ignore]
fn union_all_freeze_write_is_ub() {
    let u = UnionAllFreeze { a: 42 };
    let r: &UnionAllFreeze = &u;
    let raw = r as *const UnionAllFreeze as *mut u32;
    unsafe {
        *raw = 99;
    }
}

// ============================================================================
// Part 1(d): Zero-sized UnsafeCell<()> ((u32, UnsafeCell<()>))
// ============================================================================

#[repr(C)]
struct WithZstCell(u32, UnsafeCell<()>);

#[repr(C)]
struct PairWithZstCell {
    first: WithZstCell,
    second: u32,
}

#[repr(C)]
struct PairPureFreeze {
    first: u32,
    second: u32,
}

#[test]
#[ignore]
fn zst_unsafecell_inbounds_is_frozen_ub() {
    let x = WithZstCell(10, UnsafeCell::new(()));
    let r: &WithZstCell = &x;
    // Even though `WithZstCell: !Freeze`, `visit_freeze_sensitive` skips 0-sized `UnsafeCell<()>`
    // (`unsafe_cell_size != Size::ZERO` is false) and marks in-bounds [0..4) as `Frozen`!
    let raw = r as *const WithZstCell as *mut u32;
    unsafe {
        *raw = 20;
    }
}

#[test]
fn zst_unsafecell_outside_perm_is_cell_ok() {
    let p = PairWithZstCell {
        first: WithZstCell(10, UnsafeCell::new(())),
        second: 20,
    };
    // Retagging `r: &WithZstCell` gives:
    // - inside_perms [0..4): `Permission::Frozen` (from `visit_freeze_sensitive`)
    // - outside_perm [4..8): `Permission::Cell` (from `ty_is_freeze == false`!)
    let r: &WithZstCell = &p.first;
    let raw_second = (r as *const WithZstCell as *const u32).wrapping_add(1) as *mut u32;
    unsafe {
        *raw_second = 99;
        assert_eq!(r.0, 10);
        assert_eq!(*raw_second, 99);
    }
}

#[test]
#[ignore]
fn pure_freeze_outside_perm_is_frozen_ub() {
    let p = PairPureFreeze { first: 10, second: 20 };
    let r: &u32 = &p.first;
    // Here `u32: Freeze`, so `outside_perm` at [4..8) is `Permission::Frozen`.
    let raw_second = (r as *const u32).wrapping_add(1) as *mut u32;
    unsafe {
        *raw_second = 99;
    }
}

// ============================================================================
// Part 2: Box<T>, Pin<&mut T>, PhantomPinned, and Box<UnsafeCell<u32>>
// ============================================================================

fn consume_box_on_fn_entry(b: Box<u32>) -> u32 {
    let v = *b;
    // `Box<u32>` gets `WeakProtector` on `FnEntry`, allowing deallocation inside the callee!
    drop(b);
    v
}

#[test]
fn box_unpin_fn_entry_weak_protector_dealloc_ok() {
    let b = Box::new(123u32);
    assert_eq!(consume_box_on_fn_entry(b), 123);
}

#[test]
fn box_unsafecell_default_retag_allows_foreign_write_ok() {
    let b = Box::new(UnsafeCell::new(10u32));
    let raw: *mut u32 = b.get();
    // Moving `b` inside the same function uses `RetagMode::Default` (`is_protected = false`).
    // Because `UnsafeCell<u32>` is `!Freeze` and `is_protected == false`, `b2` gets `ReservedIM`.
    let b2 = b;
    unsafe {
        // Foreign write through `raw` (parent tag) while `b2` is `ReservedIM`:
        *raw = 55;
        // Reading through `b2` afterwards succeeds!
        assert_eq!(*b2.get(), 55);
    }
}

fn callee_with_box_unsafecell(b: Box<UnsafeCell<u32>>, raw: *mut u32) -> u32 {
    // On `FnEntry`, `is_protected == true`, so `is_protected || frozen` is `true`!
    // Thus `b` gets `ReservedFrz` (NOT `ReservedIM`!) with `WeakProtector` on [0..4).
    // A foreign write through `raw` transitions `b` from `ReservedFrz` to `Disabled`!
    unsafe {
        *raw = 77;
        *b.get()
    }
}

#[test]
#[ignore]
fn box_unsafecell_fn_entry_is_reserved_frz_not_im_ub() {
    let b = Box::new(UnsafeCell::new(10u32));
    let raw: *mut u32 = b.get();
    let _ = callee_with_box_unsafecell(b, raw);
}

struct PinnedData(u32, PhantomPinned);

fn callee_box_pinned(mut b: Box<PinnedData>, raw: *mut u32) -> u32 {
    unsafe {
        b.0 = 10;
        *raw = 20;
        let x = b.0;
        *raw = 30;
        x + *raw
    }
}

fn callee_pin_mut_pinned(mut p: Pin<&mut PinnedData>, raw: *mut u32) -> u32 {
    unsafe {
        p.as_mut().get_unchecked_mut().0 = 100;
        *raw = 200;
        let x = p.0;
        *raw = 300;
        x + *raw
    }
}

#[test]
fn phantom_pinned_box_and_pin_mut_never_retagged_ok() {
    let mut b = Box::new(PinnedData(1, PhantomPinned));
    let raw = std::ptr::addr_of_mut!((*b).0);
    // Neither `Box<PinnedData>` nor `Pin<&mut PinnedData>` is retagged on `Default` or `FnEntry`!
    let res1 = callee_box_pinned(b, raw);
    assert_eq!(res1, 50);

    let mut val = PinnedData(1, PhantomPinned);
    let raw2 = std::ptr::addr_of_mut!(val.0);
    let pin_ref = unsafe { Pin::new_unchecked(&mut val) };
    let res2 = callee_pin_mut_pinned(pin_ref, raw2);
    assert_eq!(res2, 500);
}

// ============================================================================
// Part 3: ScalarPair bOffset, Inter-Element Padding, and Transmute
// ============================================================================

#[repr(C)]
#[derive(Copy, Clone)]
struct PairU8U32(u8, u32); // size = 8, align = 4: a = u8 at 0..1, padding at 1..4, b = u32 at 4..8

#[test]
#[ignore]
fn transmute_init_bytes_to_scalar_pair_resets_padding_to_uninit() {
    let bytes: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    // Transmuting `[u8; 8]` to `PairU8U32` validates the destination at `PairU8U32` with
    // `reset_provenance_and_padding = true`, resetting padding bytes [1..4) to `uninit`!
    let p: PairU8U32 = unsafe { std::mem::transmute(bytes) };
    let ptr = &p as *const PairU8U32 as *const u8;
    unsafe {
        let _pad_byte = *ptr.add(1);
    }
}

#[test]
#[ignore]
fn transmute_scalar_pair_with_init_padding_to_maybe_uninit_resets_padding() {
    let mut p = PairU8U32(1, 0x0506_0708);
    let ptr = &mut p as *mut PairU8U32 as *mut u8;
    unsafe {
        // Explicitly initialize padding bytes [1..4) in memory:
        ptr.add(1).write(0xAA);
        ptr.add(2).write(0xBB);
        ptr.add(3).write(0xCC);
        assert_eq!(ptr.add(1).read(), 0xAA);

        // Now transmute `p` to `[MaybeUninit<u8>; 8]`:
        // `copy_op_allow_transmute` runs `validate_place` at `src.layout()` (`PairU8U32`) with
        // `reset_provenance_and_padding = true` on `dest`, resetting `dest[1..4]` to `uninit`!
        let out: [MaybeUninit<u8>; 8] = std::mem::transmute(p);
        assert_eq!(out[0].assume_init(), 1);
        let _ = out[1].assume_init(); // UB: uninitialized!
    }
}
