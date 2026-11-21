// Allocation-elision probe (Rust). Mode chosen by argv[1].
use std::hint::black_box;
fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let n: usize = 1usize << 50; // 1 PiB
    match mode.as_str() {
        "unused" => {
            let v: Vec<u8> = Vec::with_capacity(n);
            drop(v);
            println!("with_capacity(2^50) unused: returned");
        }
        "observed" => {
            let v: Vec<u8> = Vec::with_capacity(n);
            black_box(&v);
            println!("with_capacity(2^50) observed: returned");
        }
        "try_reserve" => {
            let mut v: Vec<u8> = Vec::new();
            match v.try_reserve(n) {
                Ok(()) => println!("try_reserve(2^50): Ok"),
                Err(e) => println!("try_reserve(2^50): Err({e})"),
            }
        }
        "box" => {
            let b = Box::new([0u8; 64]);
            drop(b);
            println!("Box::new([0u8; 64]) unused: returned");
        }
        _ => eprintln!("usage: elide unused|observed|try_reserve|box"),
    }
}
