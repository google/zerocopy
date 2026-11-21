//! Zero-sized boxes and vectors: construction, use and destruction without any allocation.
#[repr(align(64))]
struct Zst64;

fn main() {
    let a = Box::new(());
    assert_eq!(&*a as *const () as usize, 1);
    let b = Box::new(Zst64);
    assert_eq!(&*b as *const Zst64 as usize, 64);
    let mut v: Vec<()> = Vec::with_capacity(1000);
    assert_eq!(v.capacity(), usize::MAX);
    for _ in 0..1000 {
        v.push(());
    }
    assert_eq!(v.len(), 1000);
    drop(a);
    drop(b);
    drop(v);
    println!("ok");
}
