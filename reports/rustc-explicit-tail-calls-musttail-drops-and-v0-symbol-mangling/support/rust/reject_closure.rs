// Expected to be REJECTED: `become` inside a closure body.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

fn leaf(x: u64) -> u64 {
    x
}

fn main() {
    let f = |x: u64| -> u64 { become leaf(x) };
    println!("{}", f(1));
}
