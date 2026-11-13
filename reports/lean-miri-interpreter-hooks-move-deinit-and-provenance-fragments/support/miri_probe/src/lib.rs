// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![feature(core_intrinsics, custom_mir)]
#![allow(internal_features)]

use std::intrinsics::mir::*;

#[repr(C)]
pub struct NonCopy(pub u64);

// ============================================================================
// Probe 1: Operand::Move in Rvalue::Use vs. TerminatorKind::Call
// ============================================================================

/// Custom MIR that takes a raw pointer `p = &raw const x`, executes
/// `y = Move(x)` via `Rvalue::Use(Operand::Move(x))`, and then reads `*p` as
/// `u64` to check whether `x` remains initialized in memory.
///
/// In `rustc_const_eval` (`operand.rs:847`) and `lean-miri` (`Operand.lean`),
/// `eval_operand` treats `Operand::Move` identically to `Operand::Copy`:
/// - It does NOT perform a Tree Borrows Write access on `x`;
/// - It does NOT deinitialize `x` in `InitMask` (so reading `*p` as `u64`
///   after `Move(x)` still sees initialized `42u64`).
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub unsafe fn mir_rvalue_move_after_raw_ptr(out_moved: *mut u64, out_old: *mut u64) {
    mir! {
        let x: NonCopy;
        let p: *const NonCopy;
        let y: NonCopy;
        let p_u64: *const u64;
        {
            x = NonCopy(42_u64);
            p = &raw const x;
            // Rvalue::Use(Operand::Move(x)) on a memory-backed local `x`
            y = Move(x);
            *out_moved = y.0;
            p_u64 = p as *const u64;
            // Read the moved-from memory location `x` after `Move(x)`
            *out_old = *p_u64;
            Return()
        }
    }
}

#[inline(never)]
pub fn sink_non_copy(v: NonCopy) -> u64 {
    v.0
}

/// Custom MIR that passes `Move(*p)` into a function call `sink_non_copy(Move(*p))`
/// where `move_definitely_disjoint` is false (because `*p` has a `Deref`
/// projection), triggering `FnArg::InPlace` -> `protect_in_place_function_argument`
/// -> `write_uninit` in `rust-lang/miri` (`machine.rs:1857-1876`) and
/// `lean-miri` (`MachineHooks.lean:365-387`).
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub unsafe fn mir_call_move_deref_deinits(p: *mut NonCopy) -> u64 {
    mir! {
        {
            Call(RET = sink_non_copy(Move(*p)), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            Return()
        }
    }
}

/// Custom MIR that passes `Move(x)` directly into `sink_non_copy(Move(x))`
/// after forcing `x` into memory via `p0 = &raw const x`. Because `x` is
/// memory-backed (`Operand::Indirect`), `eval_fn_call_argument` returns
/// `FnArg::InPlace(mplace)`, and `pass_argument` calls
/// `protect_in_place_function_argument`, which retags `x` as `Mutable` +
/// `FnEntry` and writes `uninit` to `x`.
#[custom_mir(dialect = "runtime", phase = "optimized")]
pub unsafe fn mir_call_move_local_deinits_and_writes(read_old_after_call: bool) -> u64 {
    mir! {
        let x: NonCopy;
        let p0: *const NonCopy;
        let p: *const u64;
        let old_val: u64;
        {
            x = NonCopy(99_u64);
            p0 = &raw const x;
            p = p0 as *const u64;
            Call(RET = sink_non_copy(Move(x)), ReturnTo(bb1), UnwindContinue())
        }
        bb1 = {
            match read_old_after_call {
                true => bb_read,
                _ => bb_done,
            }
        }
        bb_read = {
            old_val = *p;
            RET = old_val;
            Return()
        }
        bb_done = {
            Return()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::MaybeUninit;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn test_rvalue_move_does_not_deinit_or_tb_write() {
        unsafe {
            let mut moved = 0u64;
            let mut old = 0u64;
            mir_rvalue_move_after_raw_ptr(&mut moved, &mut old);
            assert_eq!(moved, 42);
            // In rustc_const_eval / Miri, Rvalue::Use(Operand::Move(x)) does NOT
            // deinitialize `x` or perform a Tree Borrows write access.
            assert_eq!(old, 42);

            // Calling `sink_non_copy(Move(x))` without reading `*p` afterwards succeeds:
            let r = mir_call_move_local_deinits_and_writes(false);
            assert_eq!(r, 99);
        }
    }

    /// Negative UB witness: passing `Move(x)` as a `Call` argument when `x`
    /// is memory-backed (`Operand::Indirect`) triggers `FnArg::InPlace` ->
    /// `protect_in_place_function_argument` -> `write_uninit`, which deinitializes
    /// `x` in `InitMask` (and performs a Tree Borrows Write through the new
    /// FnEntry-protected tag). Reading `*p` afterwards fails with uninitialized
    /// memory UB.
    #[test]
    #[ignore]
    fn test_ub_call_move_local_deinits_in_place_arg() {
        unsafe {
            let _ = mir_call_move_local_deinits_and_writes(true);
        }
    }

    #[test]
    fn test_pointer_copy_maybe_uninit_vs_u8() {
        let mut target: u64 = 12345;
        let ptr: *mut u64 = &raw mut target;

        // Case A: Copy pointer via `[MaybeUninit<u8>; 8]` whole-array copy.
        let ptr_mu_arr: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(ptr) };
        let copied_arr: [MaybeUninit<u8>; 8] = ptr_mu_arr;
        let recovered_a: *mut u64 = unsafe { std::mem::transmute(copied_arr) };
        unsafe {
            *recovered_a += 1;
        }
        assert_eq!(target, 12346);

        // Case B: Copy pointer byte-by-byte in a `MaybeUninit<u8>` loop.
        // Because `MaybeUninit<u8>` has `BackendRepr::Scalar(Scalar::Union { Int(I8) })`,
        // `read_immediate_from_mplace_raw` returns `None` and `copy_op` uses 1-byte
        // `mem_copy`, creating `PointerFrag` entries that reassemble on load.
        let mut loop_mu_arr: [MaybeUninit<u8>; 8] = [MaybeUninit::uninit(); 8];
        for i in 0..8 {
            loop_mu_arr[i] = ptr_mu_arr[i];
        }
        let recovered_b: *mut u64 = unsafe { std::mem::transmute(loop_mu_arr) };
        unsafe {
            *recovered_b += 10;
        }
        assert_eq!(target, 12356);

        // Case C: Copy pointer byte-by-byte to an UNALIGNED offset (+3 bytes) inside a
        // `[MaybeUninit<u8>; 24]` buffer and load via `read_unaligned()`. `PointerFrag`
        // stores `idx: 0..8` and `(prov, bytes)`, NOT the allocation offset, so shifting
        // a pointer's bytes to an arbitrary (even unaligned) offset preserves provenance.
        let mut big_buf: [MaybeUninit<u8>; 24] = [MaybeUninit::uninit(); 24];
        for i in 0..8 {
            big_buf[3 + i] = ptr_mu_arr[i];
        }
        let recovered_shifted: *mut u64 =
            unsafe { (big_buf.as_ptr().add(3) as *const *mut u64).read_unaligned() };
        unsafe {
            *recovered_shifted += 100;
        }
        assert_eq!(target, 12456);

        // Case D: Copy pointer via `[u8; 8]` (or `u8` loop).
        // Under `offsetIsAddr = true` (runtime Miri), reading `u8` (`Scalar::Initialized`)
        // calls `read_scalar(..., read_provenance = false)`, which strips provenance
        // and produces integer bytes (address bits without provenance).
        let mut u8_arr: [u8; 8] = [0u8; 8];
        for i in 0..8 {
            u8_arr[i] = unsafe { ptr_mu_arr[i].assume_init() };
        }
        let addr_from_u8: usize = usize::from_ne_bytes(u8_arr);
        assert_eq!(addr_from_u8, ptr.addr());
    }

    /// Negative UB witness: copying a pointer byte-by-byte through `u8`
    /// (`Scalar::Initialized`) strips provenance (`read_provenance = false`),
    /// so dereferencing the transmuted `[u8; 8]` fails with dangling/no-provenance UB.
    #[test]
    #[ignore]
    fn test_ub_u8_copy_strips_provenance() {
        let mut target: u64 = 12345;
        let ptr: *mut u64 = &raw mut target;
        let ptr_mu_arr: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(ptr) };
        let mut u8_arr: [u8; 8] = [0u8; 8];
        for i in 0..8 {
            u8_arr[i] = unsafe { ptr_mu_arr[i].assume_init() };
        }
        let stripped_ptr: *mut u64 = unsafe { std::mem::transmute(u8_arr) };
        unsafe {
            *stripped_ptr = 999;
        }
    }

    #[test]
    fn test_chimeric_splice_same_tag_same_vs_diff_offset() {
        let mut buf: [u64; 2] = [10, 20];
        let base: *mut u64 = buf.as_mut_ptr();
        // p1 and p2 have the EXACT SAME provenance `(alloc_id, tag)`:
        let p1: *mut u64 = base;
        let p2: *mut u64 = base.wrapping_add(1);

        let p1_bytes: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(p1) };
        let p2_bytes: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(p2) };
        let p1_clone_bytes: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(p1) };

        // Splice 1: bytes 0..4 from `p1` and bytes 4..8 from `p1_clone` (same tag AND same offset).
        // Both have identical `(prov, bytes)`, so `inspectFragments` succeeds and preserves provenance.
        let mut same_offset_splice: [MaybeUninit<u8>; 8] = [MaybeUninit::uninit(); 8];
        for i in 0..4 {
            same_offset_splice[i] = p1_bytes[i];
        }
        for i in 4..8 {
            same_offset_splice[i] = p1_clone_bytes[i];
        }
        let p_same: *mut u64 = unsafe { std::mem::transmute(same_offset_splice) };
        unsafe {
            *p_same = 77;
        }
        assert_eq!(buf[0], 77);

        // Splice 2: bytes 0..4 from `p1` and bytes 4..8 from `p2` (same tag, DIFFERENT offset).
        // Even though the upper 4 bytes (bytes 4..8) of `p1` and `p2` are equal in value on 64-bit,
        // `ptrFragments` snapshotted the full 8-byte array `bytes` of `p1` vs `p2`, so
        // `frag1.bytes != frag2.bytes` and `inspectFragments` returns `None` (stripping provenance).
        let mut chimeric_splice: [MaybeUninit<u8>; 8] = [MaybeUninit::uninit(); 8];
        for i in 0..4 {
            chimeric_splice[i] = p1_bytes[i];
        }
        for i in 4..8 {
            chimeric_splice[i] = p2_bytes[i];
        }
        let p_chimeric: *mut u64 = unsafe { std::mem::transmute(chimeric_splice) };
        assert_eq!(p_chimeric.addr(), p1.addr());
    }

    /// Negative UB witness: dereferencing the chimeric pointer spliced from
    /// bytes `0..4` of `p1` and bytes `4..8` of `p2 = p1.wrapping_add(1)` (which
    /// share the exact same `(alloc_id, tag)`) fails because `frag1.bytes != frag2.bytes`
    /// strips provenance during `inspectFragments`.
    #[test]
    #[ignore]
    fn test_ub_chimeric_splice_same_tag_diff_offset_strips_prov() {
        let mut buf: [u64; 2] = [10, 20];
        let base: *mut u64 = buf.as_mut_ptr();
        let p1: *mut u64 = base;
        let p2: *mut u64 = base.wrapping_add(1);

        let p1_bytes: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(p1) };
        let p2_bytes: [MaybeUninit<u8>; 8] = unsafe { std::mem::transmute(p2) };

        let mut chimeric_splice: [MaybeUninit<u8>; 8] = [MaybeUninit::uninit(); 8];
        for i in 0..4 {
            chimeric_splice[i] = p1_bytes[i];
        }
        for i in 4..8 {
            chimeric_splice[i] = p2_bytes[i];
        }
        let p_chimeric: *mut u64 = unsafe { std::mem::transmute(chimeric_splice) };
        unsafe {
            *p_chimeric = 88;
        }
    }

    #[test]
    fn test_unwind_with_valid_fn_entry_protector() {
        fn callee_panics_with_protected_mut(
            x: &mut u64,
            root_ptr: *mut (u64, u64),
            out_sibling: &mut Option<*mut u64>,
        ) {
            *x = 555;
            // Reborrow field `.0` (`[0..8)`), which is disjoint from `x` (`[8..16)`).
            let z_ref: &mut u64 = unsafe { &mut (*root_ptr).0 };
            *out_sibling = Some(z_ref as *mut u64);
            panic!("unwind while x is FnEntry-protected on field .1");
        }

        let mut pair: (u64, u64) = (100, 200);
        let root_ptr: *mut (u64, u64) = &raw mut pair;
        let mut sibling_ptr: Option<*mut u64> = None;
        let res = catch_unwind(AssertUnwindSafe(|| {
            let x_ref: &mut u64 = unsafe { &mut (*root_ptr).1 };
            callee_panics_with_protected_mut(x_ref, root_ptr, &mut sibling_ptr);
        }));
        assert!(res.is_err());
        assert_eq!(pair.1, 555);
        // Field `.0` (`[0..8)`) was NOT accessed by `x`, so `x`'s `FnExit(Write)` during
        // `UnwindResume` only ran on `[8..16)` and left `z_ptr` valid on `[0..8)`.
        let z_ptr = sibling_ptr.unwrap();
        unsafe {
            *z_ptr = 777;
        }
        assert_eq!(pair.0, 777);
    }

    /// Negative UB witness: deallocating an allocation while an active frame holds
    /// an accessed non-`Cell` `StrongProtector` on it immediately fails in
    /// `deallocateBorrowRange` with `ProtectedDealloc`.
    #[test]
    #[ignore]
    fn test_ub_dealloc_local_with_active_strong_protector() {
        unsafe {
            let layout = std::alloc::Layout::new::<u64>();
            let raw = std::alloc::alloc(layout) as *mut u64;
            *raw = 10;
            fn dealloc_while_protected(r: &mut u64, raw: *mut u64, layout: std::alloc::Layout) {
                *r = 20;
                unsafe {
                    std::alloc::dealloc(raw as *mut u8, layout);
                }
            }
            dealloc_while_protected(&mut *raw, raw, layout);
        }
    }

    /// Negative UB witness: `UnwindResume` runs `before_stack_pop` ->
    /// `release_protector` (`perform_protector_end_access`), emitting an implicit
    /// `FnExit(Write)` access on every location where an `FnEntry`-protected tag
    /// reached `Unique, accessed = true`.
    /// Here, on a 16-byte pair `(u64, u64)`, `x: &mut u64` borrows `.1` (`[8..16)`)
    /// and writes `*x = 555` (`Unique, accessed = true` at `[8..16)`).
    /// Next, still inside `callee`, we reborrow `z_ref = &mut (*root_ptr).0` (`[0..8)`).
    /// Retagging `z_ref` only accesses `[0..8)` (where `x` has `accessed = false`) and
    /// gives `z_ref` lazy outside permission `ReservedFrz, accessed = false` at `[8..16)`.
    /// Then `callee` panics. During `UnwindResume`, `x`'s protector release emits
    /// `FnExit(Write)` at `[8..16)`, transitioning `z_ref` at `[8..16)` to `Disabled`.
    #[test]
    #[ignore]
    fn test_ub_unwind_protector_end_access_disables_sibling() {
        fn callee_panics_after_creating_sibling(
            x: &mut u64,
            root_ptr: *mut (u64, u64),
            out_sibling: &mut Option<*mut u64>,
        ) {
            *x = 555;
            let z_ref: &mut u64 = unsafe { &mut (*root_ptr).0 };
            *out_sibling = Some(z_ref as *mut u64);
            panic!("unwind triggers FnExit(Write) on x at [8..16), disabling z_ref at [8..16)!");
        }

        let mut pair: (u64, u64) = (100, 200);
        let root_ptr: *mut (u64, u64) = &raw mut pair;
        let mut sibling_ptr: Option<*mut u64> = None;
        let res = catch_unwind(AssertUnwindSafe(|| {
            let x_ref: &mut u64 = unsafe { &mut (*root_ptr).1 };
            callee_panics_after_creating_sibling(x_ref, root_ptr, &mut sibling_ptr);
        }));
        assert!(res.is_err());
        let z_ptr = sibling_ptr.unwrap();
        // Accessing `[8..16)` through `z_ptr.add(1)` after `catch_unwind` is UB because
        // `UnwindResume` ran `perform_protector_end_access` (`FnExit(Write)`) on `x`.
        unsafe {
            *z_ptr.add(1) = 999;
        }
    }
}
