// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[repr(C)]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

#[inline(never)]
pub fn get_mut_a_unwritten(x: &mut Pair) -> &mut u32 {
    // Retags `&mut x.a` on `[0, 4)` without writing to `x` or `&mut x.a`.
    // At frame exit, `x`'s `FnEntry` tag `t_arg` is still
    // `ReservedFrz { conflicted: false }` on `[0, 8)` and emits an implicit
    // `Read` with `SkipChildrenOfAccessed`.
    &mut x.a
}

#[inline(never)]
pub fn get_mut_a_written(x: &mut Pair) -> &mut u32 {
    // Retags `&mut x.a` on `[0, 4)` and writes through `r` before returning.
    // At frame exit, `t_arg` is `Unique` (`Active`) on `[0, 4)` and
    // `ReservedFrz` on `[4, 8)`, emitting implicit `Write` on `[0, 4)` and
    // implicit `Read` on `[4, 8)` with `SkipChildrenOfAccessed`.
    let r = &mut x.a;
    *r += 10;
    r
}

#[inline(never)]
pub fn outer_protected_unwritten(p: &mut Pair) -> u32 {
    let r = get_mut_a_unwritten(p);
    // Write through `t_ret` while `p` (`t_outer`) is `FnEntry`-protected:
    // `t_ret`, `t_arg`, and `t_outer` all receive `Local Write` on `[0, 4)`
    // and become `Unique`.
    *r = 42;
    let r_val = *r;
    // After `r`'s last use, `p` (`t_outer`, ancestor of `t_ret`) can be used
    // again across `[0, 8)` without violating `t_outer`'s protector (`t_ret` is
    // unprotected, so foreign access to `t_ret` is harmless once `r` is dead).
    p.b += 1;
    r_val + p.b
}

#[inline(never)]
pub fn outer_protected_written(p: &mut Pair) -> u32 {
    let r = get_mut_a_written(p);
    *r += 5;
    let r_val = *r;
    p.b += 2;
    r_val + p.b
}

#[inline(never)]
pub fn outer_interleaved_disjoint_field_via_parent_tag(p: &mut Pair) -> u32 {
    // Derive a raw pointer to `p.b` (`[4, 8)`) carrying `p`'s tag `t_outer`
    // (`&raw mut` does not create a child `Unique` tag).
    let b_ptr: *mut u32 = &raw mut p.b;
    let r: *mut u32 = get_mut_a_unwritten(p);
    unsafe {
        *r = 42;
        // Writing to `[4, 8)` through `t_outer` while `r` (`t_ret`, covering
        // `[0, 4)`) is still live only performs a Foreign Write on `t_ret` at
        // `[4, 8)` (where `t_ret` has `accessed = false`), leaving `t_ret`
        // `Unique` on `[0, 4)`.
        *b_ptr += 1;
        *r += *b_ptr;
        *r
    }
}

#[inline(never)]
pub fn both_halves_protected(left: &mut [u32], right: &mut [u32]) {
    // Both `left` and `right` have `FnEntry` strong protectors in the same
    // call frame covering disjoint byte ranges `[0, 8)` and `[8, 16)` of the
    // same allocation.
    left[0] += right[0];
    right[1] += left[1];
}

#[inline(never)]
pub fn outer_split_at_mut(slice: &mut [u32]) {
    let (left, right) = slice.split_at_mut(2);
    left[0] = 10;
    right[0] = 20;
    left[1] = 30;
    right[1] = 40;
    both_halves_protected(left, right);
    left[0] += 1;
    right[1] += 1;
}

#[inline(never)]
pub fn outer_iter_mut(slice: &mut [u32]) {
    let mut it = slice.iter_mut();
    let e0 = it.next().unwrap();
    let e1 = it.next().unwrap();
    let e2 = it.next().unwrap();
    *e2 = 300;
    *e0 = 100;
    *e1 = 200;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_case1_and_case2_get_mut_unwritten_and_written() {
        let mut pair = Pair { a: 1, b: 10 };
        let res1 = outer_protected_unwritten(&mut pair);
        assert_eq!(res1, 53);
        assert_eq!(pair.a, 42);
        assert_eq!(pair.b, 11);

        let res2 = outer_protected_written(&mut pair);
        assert_eq!(res2, (42 + 10 + 5) + 13);
        assert_eq!(pair.a, 57);
        assert_eq!(pair.b, 13);
    }

    #[test]
    fn test_disjoint_field_via_parent_tag_while_reborrow_live() {
        let mut pair = Pair { a: 1, b: 10 };
        let res = outer_interleaved_disjoint_field_via_parent_tag(&mut pair);
        assert_eq!(res, 53);
        assert_eq!(pair.a, 53);
        assert_eq!(pair.b, 11);
    }

    #[test]
    fn test_split_at_mut_and_dual_protected_callee() {
        let mut arr = [1u32, 2, 3, 4];
        outer_split_at_mut(&mut arr);
        assert_eq!(arr, [31, 30, 20, 71]);
    }

    #[test]
    fn test_iter_mut_successive_reborrows() {
        let mut arr = [1u32, 2, 3];
        outer_iter_mut(&mut arr);
        assert_eq!(arr, [100, 200, 300]);
    }

    #[test]
    #[ignore]
    fn neg_parent_write_on_subrange_disables_returned_reborrow() {
        let mut pair = Pair { a: 1, b: 2 };
        let p = &mut pair;
        let a_ptr: *mut u32 = &raw mut p.a;
        let r: *mut u32 = get_mut_a_unwritten(p);
        unsafe {
            // Activates `t_ret` to `Unique` on `[0, 4)`.
            *r = 10;
            // Foreign Write through `t_parent` on `[0, 4)` transitions `t_ret`
            // to `Disabled`.
            *a_ptr = 20;
            // UB: `ChildAccessForbidden(Disabled)`.
            let _bad = *r;
        }
    }

    #[test]
    #[ignore]
    fn neg_split_at_mut_cross_half_raw_write_disables_sibling() {
        let mut arr = [1u32, 2, 3, 4];
        let (left, right) = arr.split_at_mut(2);
        // Activates `t_right` to `Unique` on `[8, 12)` and transitions `t_left`
        // at `[8, 12)` from unaccessed `Reserved` to `Disabled`.
        right[0] = 30;
        unsafe {
            // Raw pointer derived from `t_left` writes into `rightRange`
            // `[8, 12)`. Because `split_at_mut` mints distinct sibling tags
            // `t_left != t_right`, `t_left` is `Disabled` at `[8, 12)`,
            // raising `ChildAccessForbidden(Disabled)` UB immediately.
            left.as_mut_ptr().add(2).write(99);
        }
        let _bad = right[0];
    }
}
