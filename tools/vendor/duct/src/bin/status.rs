#![deny(warnings)]

use std::env::args;
use std::process::exit;

fn main() {
    let status = args()
        .nth(1)
        .map(|s| s.parse::<i32>().expect("not a valid status"))
        .unwrap_or(0);
    exit(status);
}
