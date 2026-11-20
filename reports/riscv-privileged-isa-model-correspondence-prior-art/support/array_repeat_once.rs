// Probe: Rust array-repeat `[e; N]` evaluates `e` once (copies the value),
// mirroring Miralis model_checking/src/symbolic.rs `ctx.regs = [any!(usize); 32]`
// and `ctx.csr.pmpaddr = [any!(usize) >> 10; 64]`.
use std::sync::atomic::{AtomicU64, Ordering};
static CALLS: AtomicU64 = AtomicU64::new(0);
fn any_usize() -> usize { CALLS.fetch_add(1, Ordering::SeqCst) as usize + 1000 }
fn main() {
    let regs = [any_usize(); 32];
    let pmpaddr = [any_usize() >> 1; 64];
    let all_regs_equal = regs.iter().all(|&r| r == regs[0]);
    let all_pmpaddr_equal = pmpaddr.iter().all(|&a| a == pmpaddr[0]);
    println!("calls={} all_regs_equal={} all_pmpaddr_equal={}", CALLS.load(Ordering::SeqCst), all_regs_equal, all_pmpaddr_equal);
}
