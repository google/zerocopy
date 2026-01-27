#![deny(warnings)]

use std::env::current_dir;

fn main() {
    println!("{}", current_dir().unwrap().to_string_lossy());
}
