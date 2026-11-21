//! A reference to a block-tail temporary that is used after the block ends.

fn main() {
    let n = { &String::from("1234") }.len();
    println!("N={}", n);
}
