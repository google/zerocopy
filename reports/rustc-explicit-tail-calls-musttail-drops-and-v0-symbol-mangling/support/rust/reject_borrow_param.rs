// Expected to be REJECTED: the argument borrows a by-value parameter of the caller.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

fn callee_ref(r: &u64, _v: u64) -> u64 {
    *r
}

fn caller(_r: &u64, v: u64) -> u64 {
    become callee_ref(&v, 0)
}

fn main() {
    println!("{}", caller(&1, 2));
}
