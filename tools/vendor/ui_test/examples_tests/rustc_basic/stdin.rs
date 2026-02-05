//@run

fn main() {
    let mut n = 0;
    for line in std::io::stdin().lines() {
        n += 1;
        eprintln!("{}", line.unwrap());
    }
    assert_eq!(n, 6);
}
