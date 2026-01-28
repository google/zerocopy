#![deny(warnings)]

use std::io::prelude::*;
use std::io::{stdin, stdout};

fn main() {
    let mut input: String = String::new();
    stdin().read_to_string(&mut input).unwrap();
    let output = input.replace('x', "y");
    stdout().write_all(output.as_ref()).unwrap();
}
