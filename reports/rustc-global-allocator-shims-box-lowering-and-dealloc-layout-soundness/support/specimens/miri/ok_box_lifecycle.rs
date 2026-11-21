//! Ordinary `Box` lifecycles, including a full move out of the box and a raw round trip with
//! the correct type. Expected: no error and no leak.
#![allow(dead_code)]
struct Pair {
    first: Box<u64>,
    second: Box<u64>,
}

fn main() {
    let b = Box::new(Pair { first: Box::new(1), second: Box::new(2) });
    let p: Pair = *b;
    assert_eq!(*p.first + *p.second, 3);
    let raw = Box::into_raw(Box::new(5u64));
    let back = unsafe { Box::from_raw(raw) };
    assert_eq!(*back, 5);
    let u = Box::<u64>::new_uninit();
    drop(u);
    let w = Box::write(Box::new_uninit(), 9u64);
    assert_eq!(*w, 9);
    let v = vec![Box::new(1u8), Box::new(2u8)];
    assert_eq!(v.len(), 2);
    println!("ok");
}
