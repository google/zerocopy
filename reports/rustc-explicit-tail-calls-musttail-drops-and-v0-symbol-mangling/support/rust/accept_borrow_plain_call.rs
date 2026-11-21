// Control for `reject_borrow_local.rs`: the identical borrow is ACCEPTED when the
// transfer is an ordinary call, because the caller's frame outlives the callee.
fn callee_ref(r: &u64) -> u64 {
    *r
}

fn caller(x: &u64) -> u64 {
    let local = *x + 1;
    return callee_ref(&local);
}

fn main() {
    println!("ACCEPTED_PLAIN_CALL_RESULT={}", caller(&1));
}
