#![deny(warnings)]

use std::env::args;

fn main() {
    println!("{}", args().skip(1).collect::<Vec<_>>().join(" "));
}
