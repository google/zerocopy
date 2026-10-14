//@ compile-flags: --minirust-tree-borrows

/// UB-free counterpart to `tests/pass/tree_borrows/cell_inside_struct.rs`.

use std::cell::Cell;

struct Foo {
    field1: Cell<u32>,
}

pub fn main() {
    let root = Foo { field1: Cell::new(88) };

    unsafe {
        let a = &root;
        let a: *mut Foo = a as *const _ as *mut _;

        // Writing to `field1`, which is interior mutable, should be allowed.
        (*a).field1.set(10);
    }
}
