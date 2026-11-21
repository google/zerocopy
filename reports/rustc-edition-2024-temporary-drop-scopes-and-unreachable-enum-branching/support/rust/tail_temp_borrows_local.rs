//! A block tail expression whose temporary (`Ref<'_, Vec<u8>>`, which has a
//! destructor) borrows a local declared in the same block.

use std::cell::RefCell;

fn len_of_local() -> usize {
    let c = RefCell::new(vec![1u8, 2, 3]);
    c.borrow().len()
}

fn main() {
    println!("LEN={}", len_of_local());
}
