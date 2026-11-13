#![allow(unused)]
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering, fence};
use std::sync::Arc;
use std::thread;

#[cfg(target_os = "linux")]
fn pin_thread_to_core(core_id: usize) {
    unsafe {
        let mut cpuset: [u64; 16] = [0; 16];
        let idx = (core_id % 1024) / 64;
        let bit = (core_id % 1024) % 64;
        cpuset[idx] |= 1u64 << bit;
        // __NR_sched_setaffinity: 203 on x86_64, 122 on aarch64
        #[cfg(target_arch = "x86_64")]
        core::arch::asm!(
            "syscall",
            in("rax") 203usize,
            in("rdi") 0usize,
            in("rsi") 128usize,
            in("rdx") cpuset.as_ptr(),
            lateout("rcx") _,
            lateout("r11") _,
            lateout("rax") _,
        );
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!(
            "svc #0",
            in("x8") 122usize,
            in("x0") 0usize,
            in("x1") 128usize,
            in("x2") cpuset.as_ptr(),
            lateout("x0") _,
        );
    }
}

#[repr(align(64))]
struct AlignedAtomic(AtomicU32);

struct TwoThreadHarness {
    x: AlignedAtomic,
    y: AlignedAtomic,
    r0: Box<[u32]>,
    r1: Box<[u32]>,
    go: AlignedAtomic,
    done: AlignedAtomic,
}

fn run_two_thread_litmus<F0, F1>(iters: usize, f0: F0, f1: F1, pred: fn(u32, u32, u32, u32) -> bool) -> usize
where
    F0: Fn(&AtomicU32, &AtomicU32) -> u32 + Send + Sync + 'static,
    F1: Fn(&AtomicU32, &AtomicU32) -> u32 + Send + Sync + 'static,
{
    let x = Arc::new(AlignedAtomic(AtomicU32::new(0)));
    let y = Arc::new(AlignedAtomic(AtomicU32::new(0)));
    let start_epoch = Arc::new(AtomicUsize::new(0));
    let done0 = Arc::new(AtomicUsize::new(0));
    let done1 = Arc::new(AtomicUsize::new(0));
    let out0 = Arc::new(AtomicU32::new(0));
    let out1 = Arc::new(AtomicU32::new(0));

    let x0 = x.clone();
    let y0 = y.clone();
    let se0 = start_epoch.clone();
    let d0 = done0.clone();
    let o0 = out0.clone();

    let t0 = thread::spawn(move || {
        pin_thread_to_core(0);
        for i in 1..=iters {
            while se0.load(Ordering::Acquire) != i {
                std::hint::spin_loop();
            }
            let v = f0(&x0.0, &y0.0);
            o0.store(v, Ordering::Relaxed);
            d0.store(i, Ordering::Release);
        }
    });

    let x1 = x.clone();
    let y1 = y.clone();
    let se1 = start_epoch.clone();
    let d1 = done1.clone();
    let o1 = out1.clone();

    let t1 = thread::spawn(move || {
        pin_thread_to_core(1);
        for i in 1..=iters {
            while se1.load(Ordering::Acquire) != i {
                std::hint::spin_loop();
            }
            let v = f1(&x1.0, &y1.0);
            o1.store(v, Ordering::Relaxed);
            d1.store(i, Ordering::Release);
        }
    });

    pin_thread_to_core(2);
    let mut weak = 0usize;
    for i in 1..=iters {
        x.0.store(0, Ordering::Relaxed);
        y.0.store(0, Ordering::Relaxed);
        fence(Ordering::SeqCst);
        start_epoch.store(i, Ordering::Release);
        while done0.load(Ordering::Acquire) != i || done1.load(Ordering::Acquire) != i {
            std::hint::spin_loop();
        }
        let v0 = out0.load(Ordering::Relaxed);
        let v1 = out1.load(Ordering::Relaxed);
        let fx = x.0.load(Ordering::Relaxed);
        let fy = y.0.load(Ordering::Relaxed);
        if pred(v0, v1, fx, fy) {
            weak += 1;
        }
    }
    t0.join().unwrap();
    t1.join().unwrap();
    weak
}

// Exported assembly inspection kernels for AArch64 (+v8a vs +lse,+rcpc) and x86_64
#[no_mangle]
pub extern "C" fn asm_sb_relaxed(x: &AtomicU32, y: &AtomicU32) -> u32 {
    x.store(1, Ordering::Relaxed);
    y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn asm_sb_seqcst_fence(x: &AtomicU32, y: &AtomicU32) -> u32 {
    x.store(1, Ordering::Relaxed);
    fence(Ordering::SeqCst);
    y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn asm_sb_seqcst_ops(x: &AtomicU32, y: &AtomicU32) -> u32 {
    x.store(1, Ordering::SeqCst);
    y.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C" fn asm_mp_rel_acq(x: &AtomicU32, y: &AtomicU32) -> u32 {
    x.store(1, Ordering::Relaxed);
    y.store(1, Ordering::Release);
    y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn asm_rmw_acqrel(x: &AtomicU32) -> u32 {
    x.fetch_add(1, Ordering::AcqRel)
}

fn main() {
    let iters = std::env::args().nth(1).and_then(|s| s.parse::<usize>().ok()).unwrap_or(200_000);

    // 1. SB (Store Buffering) Relaxed: x=1; r0=y || y=1; r1=x -> weak: r0==0 && r1==0
    let sb_rlx = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::Relaxed); y.load(Ordering::Relaxed) },
        |x, y| { y.store(1, Ordering::Relaxed); x.load(Ordering::Relaxed) },
        |r0, r1, _fx, _fy| r0 == 0 && r1 == 0,
    );

    // 2. SB+fence(SeqCst): x=1; fence(SeqCst); r0=y || y=1; fence(SeqCst); r1=x -> weak: r0==0 && r1==0
    let sb_sc_fence = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::Relaxed); fence(Ordering::SeqCst); y.load(Ordering::Relaxed) },
        |x, y| { y.store(1, Ordering::Relaxed); fence(Ordering::SeqCst); x.load(Ordering::Relaxed) },
        |r0, r1, _fx, _fy| r0 == 0 && r1 == 0,
    );

    // 3. SB+SeqCst ops (`xchg` on x86_64, `stlr`+`ldar` on AArch64):
    let sb_sc_ops = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::SeqCst); y.load(Ordering::SeqCst) },
        |x, y| { y.store(1, Ordering::SeqCst); x.load(Ordering::SeqCst) },
        |r0, r1, _fx, _fy| r0 == 0 && r1 == 0,
    );

    // 4. SB+RMW (`lock xadd` on x86_64):
    let sb_rmw = run_two_thread_litmus(
        iters,
        |x, y| { x.fetch_add(1, Ordering::SeqCst); y.load(Ordering::Relaxed) },
        |x, y| { y.fetch_add(1, Ordering::SeqCst); x.load(Ordering::Relaxed) },
        |r0, r1, _fx, _fy| r0 == 0 && r1 == 0,
    );

    // 5. MP (Message Passing) Relaxed: x=1; y=1 || r0=y; r1=x -> weak: r0==1 && r1==0
    let mp_rlx = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::Relaxed); y.store(1, Ordering::Relaxed); 0 },
        |x, y| { let r0 = y.load(Ordering::Relaxed); let r1 = x.load(Ordering::Relaxed); (r0 << 1) | r1 },
        |_v0, v1, _fx, _fy| v1 == 0b10, // r0==1 && r1==0
    );

    // 6. MP Release/Acquire: x=1(Rlx); y=1(Rel) || r0=y(Acq); r1=x(Rlx) -> weak: r0==1 && r1==0
    let mp_rel_acq = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::Relaxed); y.store(1, Ordering::Release); 0 },
        |x, y| { let r0 = y.load(Ordering::Acquire); let r1 = x.load(Ordering::Relaxed); (r0 << 1) | r1 },
        |_v0, v1, _fx, _fy| v1 == 0b10,
    );

    // 7. LB (Load Buffering) Relaxed: r0=x; y=1 || r1=y; x=1 -> weak: r0==1 && r1==1
    let lb_rlx = run_two_thread_litmus(
        iters,
        |x, y| { let r0 = x.load(Ordering::Relaxed); y.store(1, Ordering::Relaxed); r0 },
        |x, y| { let r1 = y.load(Ordering::Relaxed); x.store(1, Ordering::Relaxed); r1 },
        |r0, r1, _fx, _fy| r0 == 1 && r1 == 1,
    );

    // 8. 2+2W (Two-plus-Two Writes) Relaxed: x=1; y=2 || y=1; x=2 -> weak final state: fx==1 && fy==1
    let two_plus_two_w = run_two_thread_litmus(
        iters,
        |x, y| { x.store(1, Ordering::Relaxed); y.store(2, Ordering::Relaxed); 0 },
        |x, y| { y.store(1, Ordering::Relaxed); x.store(2, Ordering::Relaxed); 0 },
        |_r0, _r1, fx, fy| fx == 1 && fy == 1,
    );

    // 9. CoRR (Coherence Read-Read): x=1 || r0=x; r1=x -> weak: r0==1 && r1==0
    let corr = run_two_thread_litmus(
        iters,
        |x, _y| { x.store(1, Ordering::Relaxed); 0 },
        |x, _y| { let r0 = x.load(Ordering::Relaxed); let r1 = x.load(Ordering::Relaxed); (r0 << 1) | r1 },
        |_v0, v1, _fx, _fy| v1 == 0b10,
    );

    println!(
        "{{\"iters\":{},\"SB_Relaxed\":{},\"SB_SeqCst_Fence\":{},\"SB_SeqCst_Ops\":{},\"SB_RMW_SeqCst\":{},\"MP_Relaxed\":{},\"MP_RelAcq\":{},\"LB_Relaxed\":{},\"2+2W_Relaxed\":{},\"CoRR\":{}}}",
        iters, sb_rlx, sb_sc_fence, sb_sc_ops, sb_rmw, mp_rlx, mp_rel_acq, lb_rlx, two_plus_two_w, corr
    );
}
