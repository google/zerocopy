// Expected to be REJECTED: caller and callee signatures differ (u64 vs u32 argument).
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

fn narrow(x: u32) -> u64 {
    x as u64
}

fn caller(x: u64) -> u64 {
    become narrow(x as u32)
}

fn main() {
    println!("{}", caller(1));
}
