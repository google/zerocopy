// Expected to be REJECTED: same argument and return types, different ABI.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

extern "C" fn c_callee(x: u64) -> u64 {
    x
}

fn caller(x: u64) -> u64 {
    become c_callee(x)
}

fn main() {
    println!("{}", caller(1));
}
