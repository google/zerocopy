#![feature(custom_mir, core_intrinsics)]
use std::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "initial")]
fn mir_prog_1(a: u64, b: u64) -> u64 {
    mir! {
        let t1: u64;
        let t2: u64;
        let t3: (u64, bool);
        {
            t3 = Checked(a + b);
            t1 = t3.0;
            t2 = t1 ^ 0x9e3779b97f4a7c15_u64;
            RET = t2 >> 3;
            Return()
        }
    }
}

fn hash_step(mut h: u64, v: u64) -> u64 {
    h ^= v;
    h = h.wrapping_mul(0x100000001b3);
    h
}

fn main() {
    let mut acc = 0xcbf29ce484222325_u64;
    for i in 0..50_u64 {
        let x = i.wrapping_mul(0x517cc1b727220a95);
        let y = (!i).wrapping_add(0x123456789abcdef0);
        let r1 = mir_prog_1(x >> 1, y >> 1);
        let r2 = x.wrapping_add(y).rotate_left((i as u32) & 63);
        let r3 = (x as i64).wrapping_neg() as u64 ^ y.swap_bytes();
        acc = hash_step(acc, r1 ^ r2 ^ r3);
    }
    println!("HASH={:016x}", acc);
}
