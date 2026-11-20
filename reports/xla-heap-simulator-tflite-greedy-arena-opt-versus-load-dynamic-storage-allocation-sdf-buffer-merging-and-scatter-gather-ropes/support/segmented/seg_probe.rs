// Representation sizes and copy behaviour of segmented buffers in the `bytes`
// crate, plus std::io::IoSlice. Build:
//   rustc --edition 2021 --crate-type rlib --crate-name bytes -O \
//     --cfg 'feature="std"' <bytes checkout>/src/lib.rs -o libbytes.rlib
//   rustc --edition 2021 -O seg_probe.rs --extern bytes=libbytes.rlib -L .
use bytes::buf::Chain;
use bytes::{Buf, Bytes};
use std::hint::black_box;
use std::io::IoSlice;
use std::mem::size_of;
use std::time::Instant;

fn main() {
    println!("size_of::<Bytes>()={}", size_of::<Bytes>());
    println!("size_of::<Chain<Bytes,Bytes>>()={}", size_of::<Chain<Bytes, Bytes>>());
    println!(
        "size_of::<Chain<Chain<Bytes,Bytes>,Bytes>>()={}",
        size_of::<Chain<Chain<Bytes, Bytes>, Bytes>>()
    );
    println!("size_of::<IoSlice>()={}", size_of::<IoSlice<'static>>());
    println!("size_of::<&[u8]>()={}", size_of::<&'static [u8]>());

    const MIB: usize = 1 << 20;
    let a = Bytes::from(vec![1u8; MIB]);
    let b = Bytes::from(vec![2u8; MIB]);

    // copy_to_bytes inside the first segment: expected to share, not copy.
    let iters = 2000;
    let t0 = Instant::now();
    let mut shared_same_ptr = 0usize;
    for _ in 0..iters {
        let mut c = a.clone().chain(b.clone());
        let out = c.copy_to_bytes(MIB / 2);
        if out.as_ptr() == a.as_ptr() {
            shared_same_ptr += 1;
        }
        black_box(out);
    }
    let within = t0.elapsed().as_secs_f64() / iters as f64;

    // copy_to_bytes spanning the boundary: Chain allocates and copies.
    let t1 = Instant::now();
    let mut spanning_same_ptr = 0usize;
    for _ in 0..iters {
        let mut c = a.clone().chain(b.clone());
        c.advance(MIB / 2);
        let out = c.copy_to_bytes(MIB);
        if out.as_ptr() == unsafe { a.as_ptr().add(MIB / 2) } {
            spanning_same_ptr += 1;
        }
        black_box(out);
    }
    let spanning = t1.elapsed().as_secs_f64() / iters as f64;

    println!(
        "copy_to_bytes(512KiB) within first segment: {:.3} us/op, result aliases source in {}/{} runs",
        within * 1e6,
        shared_same_ptr,
        iters
    );
    println!(
        "copy_to_bytes(1MiB) spanning boundary: {:.3} us/op, result aliases source in {}/{} runs",
        spanning * 1e6,
        spanning_same_ptr,
        iters
    );

    // chunks_vectored exposes both segments without copying.
    let c = a.clone().chain(b.clone());
    let mut iov = [IoSlice::new(&[]); 4];
    let n = c.chunks_vectored(&mut iov);
    println!("chunks_vectored filled {} IoSlice entries (lens {:?})", n, iov[..n].iter().map(|s| s.len()).collect::<Vec<_>>());
}
