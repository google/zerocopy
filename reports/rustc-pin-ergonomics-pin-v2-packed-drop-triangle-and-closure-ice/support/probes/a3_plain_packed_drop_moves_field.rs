// Part A3: the drop-glue move for under-aligned fields of a packed struct, shown without any
// structural pinning of the packed type (so it is accepted by every examined compiler).
//
// `Leaf::pin_drop` records the address it is called at. `PackedOwner` and `PlainOwner` are not
// `#[pin_v2]` and are never pinned; the only difference between them is `#[repr(packed)]`.
// Expected: the leaf of the packed owner is destroyed outside the owner's storage (it was
// moved to an aligned temporary first), the leaf of the plain owner inside it.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::cell::Cell;
use std::mem::size_of;

thread_local! {
    static DROPPED_AT: Cell<usize> = const { Cell::new(0) };
}

/// Alignment 8.
#[pin_v2]
struct Leaf {
    _big: u64,
}

impl Drop for Leaf {
    fn pin_drop(&pin mut self) {
        let here: &Leaf = &*self;
        DROPPED_AT.set(here as *const Leaf as usize);
    }
}

#[repr(packed)]
struct PackedOwner {
    _pad: u8,
    _leaf: Leaf,
}

struct PlainOwner {
    _pad: u8,
    _leaf: Leaf,
}

fn inside(start: usize, size: usize) -> bool {
    let at = DROPPED_AT.get();
    at >= start && at < start + size
}

fn main() {
    let packed_start;
    {
        let owner = PackedOwner { _pad: 1, _leaf: Leaf { _big: 2 } };
        packed_start = &owner as *const PackedOwner as usize;
    }
    let packed_inside = inside(packed_start, size_of::<PackedOwner>());

    let plain_start;
    {
        let owner = PlainOwner { _pad: 1, _leaf: Leaf { _big: 2 } };
        plain_start = &owner as *const PlainOwner as usize;
    }
    let plain_inside = inside(plain_start, size_of::<PlainOwner>());

    println!(
        "PACKED_OWNER_FIELD_DROPPED_INSIDE_OWNER={packed_inside} \
         PLAIN_OWNER_FIELD_DROPPED_INSIDE_OWNER={plain_inside}"
    );
}
