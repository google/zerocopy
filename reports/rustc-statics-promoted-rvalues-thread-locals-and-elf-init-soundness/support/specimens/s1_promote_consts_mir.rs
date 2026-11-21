#![crate_type = "lib"]
#![allow(dead_code, unused_variables, unconditional_panic, clippy::all)]

use std::cell::Cell;

pub struct HasDrop(pub u32);
impl Drop for HasDrop {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

#[inline(never)]
pub const fn checked_pos(x: u32) -> u32 {
    assert!(x > 0);
    x + 1
}

// Positive 1: constant array index (1 < 3) + non-zero constant divisor (100 / 4).
#[no_mangle]
#[inline(never)]
pub fn promo_arith_and_index() -> &'static u32 {
    let r: &'static u32 = &([10u32, 20, 30][1] + (100u32 / 4));
    r
}

// Positive 2: mutable borrow of empty array literal (`&mut [u32; 0]` coerced to `&'static mut [u32]`).
#[no_mangle]
#[inline(never)]
pub fn promo_empty_mut_slice() -> usize {
    let s: &'static mut [u32] = &mut [];
    s.len()
}

// Positive 3: temporary used twice (`uses > 1` -> `keep_original = true` while borrowing `&r`).
#[no_mangle]
#[inline(never)]
pub fn promo_multiuse_temp() -> (u32, &'static u32) {
    let t = 77u32 + 3u32;
    (t, &77u32)
}

// Negative 1: interior mutability (`HasMutInterior`) prevents promotion.
#[no_mangle]
#[inline(never)]
pub fn reject_unsafecell() -> u32 {
    let c = &Cell::new(42u32);
    c.set(c.get() + 1);
    c.get()
}

// Negative 2: `NeedsDrop` prevents promotion even for pure constructor.
#[no_mangle]
#[inline(never)]
pub fn reject_needs_drop() -> u32 {
    let d = &HasDrop(7);
    d.0
}

// Negative 3: fallible division/modulo/index inside dead runtime branch must NOT promote
// the panicking computation; `&([1, 2][5])` promotes only the backing `[1, 2]` array while
// keeping the runtime bounds check (`validate_candidate` checks `validate_local(place.local)`),
// whereas `&([1, 2][5] + 1)` rejects promotion completely via `validate_place` `idx < len`.
#[no_mangle]
#[inline(never)]
pub fn reject_fallible_div_and_oob(flag: bool) -> u32 {
    if flag {
        let a = &(1u32 / 0);
        let b = &(i32::MIN / -1);
        let c = &([1u32, 2][5]);
        let d = &([1u32, 2][5] + 1);
        (*a).wrapping_add(*b as u32).wrapping_add(*c).wrapping_add(*d)
    } else {
        9
    }
}

// Negative 3b: nested out-of-bounds index inside an rvalue expression (`[1, 2][5] + 1`).
#[no_mangle]
#[inline(never)]
pub fn reject_nested_oob_index(flag: bool) -> u32 {
    if flag {
        let d = &([1u32, 2][5] + 1);
        *d
    } else {
        7
    }
}

// Negative 4: non-`#[rustc_promotable]` `const fn` is NOT promoted in normal `fn`.
#[no_mangle]
#[inline(never)]
pub fn reject_const_fn_in_fn() -> u32 {
    let r = &checked_pos(5);
    *r
}

// Positive/Negative 5: inside `const`, `checked_pos(5)` in guaranteed-executed START_BLOCK IS
// promoted, while `checked_pos(0)` in dead `if false` block is NOT promoted.
pub const SAFE_PROMO_IN_CONST: u32 = {
    let r = &checked_pos(5);
    if false {
        let _ = &checked_pos(0);
    }
    *r
};
