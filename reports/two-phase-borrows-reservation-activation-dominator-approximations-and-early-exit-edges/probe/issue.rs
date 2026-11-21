#![forbid(unsafe_code)]
fn main() {
    let mut v = Some(0i32);
    let mut r: Option<&mut i32> = None;
    'b: {
        r = Some(v.insert(match true { false => break 'b, true => 1 }));
    }
    let s = &v;              // accepted; should be E0502
    let before = *s;
    *r.unwrap() = 2;
    println!("{:?} {:?}", before, *s);
}
