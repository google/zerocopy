// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(dead_code)]

use core::cell::Cell;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct U64Range {
    pub min: u64,
    pub max: u64,
}

impl U64Range {
    pub fn new(min: u64, max: u64) -> Self {
        Self { min, max }
    }
    pub fn max(&self) -> u64 {
        self.max
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct OuterScalarData {
    pub value: u64,
    pub unknown_mask: u64,
    pub unwritten_mask: u64,
    pub urange: U64Range,
}

impl OuterScalarData {
    pub fn max(&self) -> u64 {
        let top = (!0u64). leading_zeros();
        let _ = top;
        self.urange.max
    }

    // Pattern 2: Chained projections (((*_1).3: U64Range).1: u64) + intra-body shared borrow
    pub fn check_urange_max(&self) -> bool {
        self.urange.max <= self.max()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EbpfInsn {
    pub code: u8,
    pub dst_src: u8,
    pub offset: i16,
    pub imm: i32,
}

impl EbpfInsn {
    pub fn code(&self) -> u8 {
        self.code
    }
    pub fn set_code(&mut self, code: u8) {
        self.code = code;
    }
    pub fn set_offset(&mut self, offset: i16) {
        self.offset = offset;
    }
    pub fn add_to_code(&mut self, delta: u8) {
        self.code = self.code.wrapping_add(delta);
    }
}

pub struct CompCtx {
    pub reg: u64,
}

pub struct DataDeps {
    pub mask: u64,
}

impl DataDeps {
    pub fn atomic(&mut self, ctx: &CompCtx, slot: u64) {
        self.mask |= ctx.reg ^ slot;
    }
}

pub struct DepTracker {
    pub ctx: CompCtx,
    pub deps: DataDeps,
}

// Pattern 1a: Un-reseated top-level &T and &mut T parameters
pub fn param_unreseated(dst: &mut u64, src: &u64) {
    *dst = (*dst).wrapping_add(*src);
}

// Pattern 1b: Re-seated top-level &mut T parameter
pub fn param_reseated<'a>(mut r: &'a mut u64, fallback: &'a mut u64, use_fallback: bool) {
    if use_fallback {
        r = fallback;
    }
    *r += 100;
}

// Pattern 3a: Two-phase borrow with overlapping shared borrow of the EXACT SAME PlacePath
// Mirrors starnix/ebpf_core `program::apply_struct_access_mapping::bb24`:
//   instruction.set_code((instruction.code() & !BPF_SIZE_MASK) | BPF_DW);
pub fn two_phase_same_path_shared_read(insn: &mut EbpfInsn) {
    insn.set_code((insn.code() & !0x07) | 0x18);
}

// Pattern 3b: Two-phase borrow of field 1 with overlapping shared borrow of field 0
// Mirrors starnix/ebpf_core `DependencyTracker::atomic_add::bb0`:
//   self.deps.atomic(&self.context, ...)
pub fn two_phase_disjoint_field_shared_borrow(dt: &mut DepTracker) {
    dt.deps.atomic(&dt.ctx, 1);
}

// Pattern 3c: Two-phase borrow of field 1 where argument evaluation mutates field 0 BEFORE activation!
// Allowed by rustc borrowck and Miri (Stacked Borrows & Tree Borrows) because field 1 (`dt.deps`)
// and field 0 (`dt.ctx.reg`) are disjoint PlacePaths under `*_1`.
// Demonstrates why root-local Eager Copy-In/Copy-Out is UNSOUND (snapshotting `*_1` into `_tp` at
// reservation would overwrite `dt.ctx.reg += 5` when `_tp` writes back on return).
pub fn two_phase_disjoint_field_mut_during_reservation(dt: &mut DepTracker) {
    dt.deps.atomic(
        {
            dt.ctx.reg += 5;
            &dt.ctx
        },
        1,
    );
}

// Pattern 4a: Nested reborrow chain (&mut *r -> &mut (*r1).max) + split field mutable borrows
pub fn nested_reborrow_and_split_fields(r: &mut U64Range) -> u64 {
    let r1: &mut U64Range = &mut *r;
    let r2: &mut u64 = &mut r1.max;
    *r2 = (*r2).wrapping_add(10);
    let r_min: &mut u64 = &mut r.min;
    let r_max: &mut u64 = &mut r.max;
    *r_min = (*r_min).wrapping_add(3);
    *r_max = (*r_max).wrapping_add(*r_min);
    r.max
}

// Pattern 4b: Conditional mutable borrow joining at a CFG merge block
pub fn conditional_mut_borrow(cond: bool, delta: u64) -> (u64, u64) {
    let mut a = 10u64;
    let mut b = 20u64;
    let r: &mut u64 = if cond { &mut a } else { &mut b };
    *r = (*r).wrapping_add(delta);
    (a, b)
}

// Pattern 5a: Tuple of mutable references (`Derefer` + `EraseDerefTemps` emits `WithRetag::No` copy of `&mut u64`)
pub fn tuple_of_mut_refs(delta: u64) -> (u64, u64) {
    let mut a = 10u64;
    let mut b = 20u64;
    let pair = (&mut a, &mut b);
    *pair.0 += delta;
    *pair.1 += *pair.0;
    (a, b)
}

// Pattern 5b: Match guard over enum containing `&mut T` (`Derefer` emits `WithRetag::No` copy of `&mut u64`)
// Mirrors starnix/ebpf_core `verifier::Type::set_null::bb2[10]`.
pub enum MaybeRef<'a> {
    NullOr { id: &'a mut u64, flag: bool },
    Other,
}

pub fn match_guard_nested_mut_ref(m: MaybeRef<'_>, target: &u64) -> bool {
    match m {
        MaybeRef::NullOr { id, .. } if *id == *target => {
            *id = 0;
            true
        }
        _ => false,
    }
}

// Pattern 6a: Shared aliasing on `Freeze` types (sound under Place-Path Lens)
pub fn shared_alias_freeze(x: &u64, y: &u64) -> u64 {
    *x + *y
}

// Pattern 6b: Interior mutability (`UnsafeCell` / `Cell<u64>`) breaking read-frame invariance when aliased
pub fn interior_mutability_cell(x: &Cell<u64>, y: &Cell<u64>) -> u64 {
    let before = x.get();
    y.set(before + 10);
    x.get()
}

pub fn run_all_safe_probes() {
    let mut x = 5u64;
    let y = 7u64;
    param_unreseated(&mut x, &y);
    assert_eq!(x, 12);

    let mut f = 99u64;
    param_reseated(&mut x, &mut f, true);
    assert_eq!(x, 12);
    assert_eq!(f, 199);

    let s = OuterScalarData {
        value: 10,
        unknown_mask: 0,
        unwritten_mask: 0,
        urange: U64Range::new(0, 10),
    };
    assert!(s.check_urange_max());

    let mut insn = EbpfInsn {
        code: 0x61, // BPF_LDX | BPF_MEM | BPF_W
        dst_src: 0,
        offset: 0,
        imm: 0,
    };
    two_phase_same_path_shared_read(&mut insn);
    assert_eq!(insn.code, (0x61 & !0x07) | 0x18);

    let mut dt = DepTracker {
        ctx: CompCtx { reg: 0b1010 },
        deps: DataDeps { mask: 0b0100 },
    };
    two_phase_disjoint_field_shared_borrow(&mut dt);
    assert_eq!(dt.deps.mask, 0b0100 | (0b1010 ^ 1));

    let mut dt2 = DepTracker {
        ctx: CompCtx { reg: 10 },
        deps: DataDeps { mask: 0 },
    };
    two_phase_disjoint_field_mut_during_reservation(&mut dt2);
    assert_eq!(dt2.ctx.reg, 15);
    assert_eq!(dt2.deps.mask, 15 ^ 1);

    let mut rng = U64Range::new(5, 15);
    assert_eq!(nested_reborrow_and_split_fields(&mut rng), 33);
    assert_eq!(rng.min, 8);

    assert_eq!(conditional_mut_borrow(true, 5), (15, 20));
    assert_eq!(conditional_mut_borrow(false, 5), (10, 25));

    assert_eq!(tuple_of_mut_refs(5), (15, 35));

    let mut id_val = 77u64;
    assert!(match_guard_nested_mut_ref(
        MaybeRef::NullOr {
            id: &mut id_val,
            flag: true
        },
        &77u64
    ));
    assert_eq!(id_val, 0);

    let val = 21u64;
    assert_eq!(shared_alias_freeze(&val, &val), 42);

    let cell = Cell::new(5u64);
    // When x and y alias the same Cell, y.set(15) mutates x.get() from 5 to 15!
    assert_eq!(interior_mutability_cell(&cell, &cell), 15);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_safe_probes() {
        run_all_safe_probes();
    }
}
