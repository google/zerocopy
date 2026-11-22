// Part A1 (run natively and under Miri): type identity of `&pin mut T` and `Pin<&mut T>`,
// explicit and implicit structural projection through a `#[pin_v2]` struct, implicit pinned
// reborrowing without `.as_mut()`, and `Drop::pin_drop` for a pinned value and for a value
// that was never pinned and is moved before it is dropped.
//
// Deliberately contains no closures and no `async`: on the examined compilers those would
// reach the capture-analysis failure exercised by the `c*` probes.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::any::TypeId;
use std::cell::Cell;
use std::marker::PhantomPinned;
use std::pin::{Pin, pin};

thread_local! {
    /// `pin_drop` calls on a leaf whose address equals the address it was first pinned at.
    static DROP_PINNED_IN_PLACE: Cell<u32> = const { Cell::new(0) };
    /// `pin_drop` calls on a leaf whose address differs from the address it was pinned at.
    static DROP_PINNED_MOVED: Cell<u32> = const { Cell::new(0) };
    /// `pin_drop` calls on a leaf that was never observed through a pinned reference.
    static DROP_NEVER_PINNED: Cell<u32> = const { Cell::new(0) };
}

#[pin_v2]
struct Leaf {
    /// Address at which this value was first observed through `&pin mut Leaf` (0 = never).
    pinned_at: Cell<usize>,
    _pin: PhantomPinned,
}

impl Leaf {
    fn new() -> Leaf {
        Leaf { pinned_at: Cell::new(0), _pin: PhantomPinned }
    }

    fn addr(&self) -> usize {
        self as *const Leaf as usize
    }

    fn observe(&pin mut self) {
        if self.pinned_at.get() == 0 {
            self.pinned_at.set(self.addr());
        }
    }
}

impl Drop for Leaf {
    fn pin_drop(&pin mut self) {
        let counter = match self.pinned_at.get() {
            0 => &DROP_NEVER_PINNED,
            a if a == self.addr() => &DROP_PINNED_IN_PLACE,
            _ => &DROP_PINNED_MOVED,
        };
        counter.set(counter.get() + 1);
    }
}

#[pin_v2]
struct Pair {
    left: Leaf,
    right: u32,
}

/// Explicit projection: `left` stays pinned (`Leaf: !Unpin`), `right: u32` is `Unpin` and may
/// be bound with a plain `ref mut`.
fn explicit(r: &pin mut Pair) -> u32 {
    let &pin mut Pair { ref pin mut left, ref mut right } = r;
    let left: Pin<&mut Leaf> = left;
    let right: &mut u32 = right;
    left.observe();
    *right += 1;
    *right
}

/// Match-ergonomics projection: both bindings become pinned references.
fn implicit(r: &pin mut Pair) -> u32 {
    let Pair { left, right } = r;
    let left: Pin<&mut Leaf> = left;
    let mut right: Pin<&mut u32> = right;
    left.observe();
    *right += 10;
    *right
}

/// `r` is used three times; each use is an implicit pinned reborrow, not a move.
fn reborrow_three_times(mut r: &pin mut Pair) -> u32 {
    let a = explicit(r);
    let b = implicit(r);
    let c = explicit(r);
    a + b + c
}

/// A plain `Pin<&mut T>` parameter accepts a `&pin mut T` argument and vice versa.
fn takes_pin_path(r: Pin<&mut Pair>) -> u32 {
    takes_pin_sugar(r)
}

fn takes_pin_sugar(r: &pin mut Pair) -> u32 {
    r.right
}

fn main() {
    let same_tid = TypeId::of::<&'static pin mut Leaf>() == TypeId::of::<Pin<&'static mut Leaf>>()
        && TypeId::of::<&'static pin const Leaf>() == TypeId::of::<Pin<&'static Leaf>>();

    let proj_sum;
    let right_after;
    {
        let mut pair = pin!(Pair { left: Leaf::new(), right: 0 });
        proj_sum = reborrow_three_times(pair.as_mut());
        right_after = takes_pin_path(pair.as_mut());
    } // `pair` is dropped in place here.

    {
        // Never pinned: built, moved to the heap, moved back to the stack, then dropped.
        let on_stack = Pair { left: Leaf::new(), right: 0 };
        let on_heap = Box::new(on_stack);
        let back_on_stack = *on_heap;
        drop(back_on_stack);
    }

    println!(
        "SAME_TID={same_tid} PROJ_SUM={proj_sum} RIGHT_AFTER={right_after} \
         DROP_PINNED_IN_PLACE={} DROP_PINNED_MOVED={} DROP_NEVER_PINNED={}",
        DROP_PINNED_IN_PLACE.get(),
        DROP_PINNED_MOVED.get(),
        DROP_NEVER_PINNED.get(),
    );
}
