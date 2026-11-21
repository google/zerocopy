// Expected to be REJECTED: the argument borrows a caller local, and the caller's
// frame is gone by the time the callee runs.
#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

fn callee_ref(r: &u64) -> u64 {
    *r
}

fn caller(x: &u64) -> u64 {
    let local = *x + 1;
    become callee_ref(&local)
}

fn main() {
    println!("{}", caller(&1));
}
