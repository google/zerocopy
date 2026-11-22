// Part A2: `#[pin_v2]` combined with `#[repr(packed)]`.
//
// `Node` has alignment 1, so a reference to `outer.mid.node` is permitted even though `Outer`
// is packed. `Mid` has alignment 8, so inside the packed `Outer` it is under-aligned, and the
// drop glue of `Outer` moves `mid` (and the `Node` inside it) to an aligned temporary before
// running destructors. The program pins `Node` in place through safe structural projection
// and then compares that address with the address `Node::pin_drop` observes.
//
// Expected: either the compiler rejects the `#[pin_v2] #[repr(packed)]` definition, or the
// program prints `PACKED_PINNED_FIELD_DROPPED_IN_PLACE=false` (a violated pin guarantee in
// code that contains no `unsafe`).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::cell::Cell;
use std::marker::PhantomPinned;
use std::pin::pin;

thread_local! {
    static PINNED_AT: Cell<usize> = const { Cell::new(0) };
    static DROPPED_AT: Cell<usize> = const { Cell::new(0) };
}

/// Alignment 1 and `!Unpin`.
#[pin_v2]
struct Node {
    _bytes: [u8; 4],
    _pin: PhantomPinned,
}

impl Node {
    fn touch(&pin mut self) {
        let here: &Node = &*self;
        PINNED_AT.set(here as *const Node as usize);
    }
}

impl Drop for Node {
    fn pin_drop(&pin mut self) {
        let here: &Node = &*self;
        DROPPED_AT.set(here as *const Node as usize);
    }
}

/// Alignment 8.
#[pin_v2]
struct Mid {
    _big: u64,
    node: Node,
}

#[pin_v2]
#[repr(packed)]
struct Outer {
    _pad: u8,
    mid: Mid,
}

fn main() {
    {
        let mut outer = pin!(Outer {
            _pad: 1,
            mid: Mid { _big: 2, node: Node { _bytes: [3; 4], _pin: PhantomPinned } },
        });
        let &pin mut Outer { mid: Mid { ref pin mut node, .. }, .. } = outer.as_mut();
        node.touch();
    }
    let (pinned_at, dropped_at) = (PINNED_AT.get(), DROPPED_AT.get());
    println!(
        "PACKED_PINNED_FIELD_DROPPED_IN_PLACE={}",
        pinned_at != 0 && pinned_at == dropped_at
    );
}
