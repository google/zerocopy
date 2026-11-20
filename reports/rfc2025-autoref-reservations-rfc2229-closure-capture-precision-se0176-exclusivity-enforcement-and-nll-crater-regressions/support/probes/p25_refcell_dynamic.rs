// Rust's library-level dynamic exclusivity check (RefCell); run it to observe the panic.
use std::cell::RefCell;
fn main() {
    let c = RefCell::new(vec![1u32]);
    let r = c.try_borrow_mut();
    println!("first borrow_mut ok: {}", r.is_ok());
    let s = c.try_borrow();
    println!("overlapping borrow ok: {}", s.is_ok());
    drop(s);
    drop(r);
    let _g = c.borrow_mut();
    let _h = c.borrow(); // panics: already mutably borrowed
}
