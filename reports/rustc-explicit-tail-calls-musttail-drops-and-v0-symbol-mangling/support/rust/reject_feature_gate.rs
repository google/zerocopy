// Expected to be REJECTED: `become` without the `explicit_tail_calls` feature gate.
fn leaf(x: u64) -> u64 {
    x
}

fn caller(x: u64) -> u64 {
    become leaf(x)
}

fn main() {
    println!("{}", caller(1));
}
