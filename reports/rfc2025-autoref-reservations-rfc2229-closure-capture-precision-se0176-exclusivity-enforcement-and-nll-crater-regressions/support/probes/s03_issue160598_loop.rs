// Loop/break variant of the issue-160598 shape (no labeled block), to test older toolchains.
fn main() {
    let mut v = Some(0i32);
    let mut r: Option<&mut i32> = None;
    loop {
        r = Some(v.insert(match true { false => break, true => 1 }));
        break;
    }
    let s = &v;
    let before = *s;
    *r.unwrap() = 2;
    println!("{:?} {:?}", before, *s);
}
