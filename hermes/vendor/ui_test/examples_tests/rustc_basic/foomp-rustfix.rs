#![deny(warnings)]

fn main() {
    let mut x = 42;
    //~^ ERROR: does not need to be mutable
    println!("{x}");
}
