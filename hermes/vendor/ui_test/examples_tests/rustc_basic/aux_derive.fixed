//@aux-build:derive_proc_macro.rs

#[macro_use]
extern crate derive_proc_macro;

fn main() {
    let mut x = Foo;
    x = Foo;
    //~^ ERROR: cannot assign twice
}

#[derive(Something)]
struct Foo;
