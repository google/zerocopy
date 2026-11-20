// Reproducer from rust-lang/rust issue 164163 ("Unsound two-phase borrow accepted by compiler"), verbatim logic.
pub fn main() {
    let mut a: Vec<u64> = vec![1];
    let mut b: Vec<u64> = vec![2];
    let mut p: &mut Vec<u64> = &mut a;
    let s: &u64;
    p.push({
        s = &p[0];
        p = &mut b;
        0
    });
    for _ in 0..64 { p.push(7); }
    println!("{}", *s);
}
