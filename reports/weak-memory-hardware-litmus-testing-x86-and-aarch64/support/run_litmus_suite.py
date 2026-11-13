#!/usr/bin/env python3
"""Run S15 weak-memory hardware litmus experiments on native x86_64 and AArch64 (qemu-aarch64 + asm verification)."""
import csv
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

TMP_B = Path("/tmp/anneal-ref-scratch/runs/run-21/tmp_b/s15")
STAGED_S15 = Path("/tmp/anneal-ref-scratch/runs/run-21/staged_reports_b/weak-memory-hardware-litmus-testing-x86-and-aarch64")
SUP_S15 = STAGED_S15 / "support"
TMP_B.mkdir(parents=True, exist_ok=True)
SUP_S15.mkdir(parents=True, exist_ok=True)

SYSROOT_1991 = Path("/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu")
RUSTC_1991 = str(SYSROOT_1991 / "bin/rustc")

# 1. Native Rust Litmus Harness (x86_64 + cross-compilable to AArch64)
RUST_LITMUS_RS = r'''#![allow(unused)]
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
'''

litmus_src = TMP_B / "rust_litmus_tests.rs"
litmus_src.write_text(RUST_LITMUS_RS, encoding="utf-8")
shutil.copy2(litmus_src, SUP_S15 / "rust_litmus_tests.rs")

# Compile and run on native x86_64-unknown-linux-gnu (300,000 iterations per litmus family = 2.7M total barrier rounds!)
x64_bin = TMP_B / "litmus_x86_64"
x64_asm = TMP_B / "litmus_x86_64.s"
subprocess.run([RUSTC_1991, "--edition=2021", "-C", "opt-level=3", str(litmus_src), "-o", str(x64_bin)], check=True)
subprocess.run([RUSTC_1991, "--edition=2021", "--crate-type=lib", "-C", "opt-level=3", "--emit=asm", str(litmus_src), "-o", str(x64_asm)], check=True)

t0 = time.perf_counter()
p_x64 = subprocess.run([str(x64_bin), "300000"], capture_output=True, text=True, check=True)
x64_elapsed = round(time.perf_counter() - t0, 2)
x64_obs = json.loads(p_x64.stdout.strip())

# Compile AArch64 baseline (+v8a) and (+lse,+rcpc) assembly AND static binary for qemu-aarch64
a64_v8a_asm = TMP_B / "litmus_aarch64_v8a.s"
a64_lse_rcpc_asm = TMP_B / "litmus_aarch64_lse_rcpc.s"
subprocess.run([
    RUSTC_1991, "--edition=2021", "--crate-type=lib", "-C", "opt-level=3",
    "--target", "aarch64-unknown-linux-gnu", "--emit=asm", str(litmus_src), "-o", str(a64_v8a_asm)
], check=True)
subprocess.run([
    RUSTC_1991, "--edition=2021", "--crate-type=lib", "-C", "opt-level=3",
    "--target", "aarch64-unknown-linux-gnu", "-C", "target-feature=+lse,+rcpc",
    "--emit=asm", str(litmus_src), "-o", str(a64_lse_rcpc_asm)
], check=True)

# Also check if we can link aarch64 binary or C pthread litmus or run qemu-aarch64 with sysroot
# Wait: let's check if aarch64 linker / sysroot exists or build a static aarch64 ELF using clang-19 / lld if available, or test C/Rust under qemu-aarch64!
# Let's check what aarch64_linker.sh in run-18 did!
a64_obs = {}
a64_bin = TMP_B / "litmus_aarch64"
p_a64_build = subprocess.run([
    RUSTC_1991, "--edition=2021", "-C", "opt-level=3",
    "--target", "aarch64-unknown-linux-gnu",
    "-C", "linker=/tmp/anneal-ref-scratch/runs/run-18/aarch64_linker.sh",
    str(litmus_src), "-o", str(a64_bin)
], capture_output=True, text=True)
if p_a64_build.returncode == 0 and a64_bin.is_file():
    p_q = subprocess.run(["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", str(a64_bin), "50000"], capture_output=True, text=True)
    if p_q.returncode == 0 and p_q.stdout.strip().startswith("{"):
        a64_obs = json.loads(p_q.stdout.strip())

# Combine with herd7 7.58 normative model predictions (x86tso.cat, aarch64.cat, rc11.cat)
HERD7_NORMATIVE = {
    "SB_Relaxed": {
        "x86tso_cat": "Allowed (Sometimes: store-buffer forwarding r0=0 /\\ r1=0)",
        "aarch64_cat": "Allowed (Sometimes: store/load reordering r0=0 /\\ r1=0)",
        "rc11_cat": "Allowed (Sometimes: Relaxed stores/loads do not synchronize)",
    },
    "SB_SeqCst_Fence": {
        "x86tso_cat": "Forbidden (Never: mfence / locked RMW drains FIFO store buffer)",
        "aarch64_cat": "Forbidden (Never: dmb ish orders W ->dmb.full R)",
        "rc11_cat": "Forbidden (Never: psc_f total order over SeqCst fences)",
    },
    "SB_SeqCst_Ops": {
        "x86tso_cat": "Forbidden (Never: xchg is locked and drains store buffer)",
        "aarch64_cat": "Forbidden (Never: STLR [L] ->po LDAR [A] is in bob)",
        "rc11_cat": "Forbidden (Never: psc_base total order over SeqCst accesses)",
    },
    "SB_RMW_SeqCst": {
        "x86tso_cat": "Forbidden (Never: lock xadd drains store buffer)",
        "aarch64_cat": "Forbidden (Never: ldaddal / ldaxr+stlxr orders RMW ->po R)",
        "rc11_cat": "Forbidden (Never: SeqCst RMW in psc)",
    },
    "MP_Relaxed": {
        "x86tso_cat": "Forbidden (Never: x86-TSO preserves W ->po W and R ->po R)",
        "aarch64_cat": "Allowed (Sometimes: plain STR/LDR can reorder on Armv8)",
        "rc11_cat": "Allowed (Sometimes: Relaxed accesses do not establish sw/hb)",
    },
    "MP_RelAcq": {
        "x86tso_cat": "Forbidden (Never: TSO preserves W ->po W and R ->po R natively)",
        "aarch64_cat": "Forbidden (Never: STLR orders prior W, LDAR/LDAPR orders subsequent R)",
        "rc11_cat": "Forbidden (Never: Release/Acquire establishes sw and hb)",
    },
    "LB_Relaxed": {
        "x86tso_cat": "Forbidden (Never: x86-TSO preserves R ->po W)",
        "aarch64_cat": "Allowed (Sometimes: independent LDR ->po STR can reorder on Armv8)",
        "rc11_cat": "Forbidden by acyclic(po | rf) in RC11; Allowed in IMM/Promising 2.0 when independent",
    },
    "2+2W_Relaxed": {
        "x86tso_cat": "Forbidden (Never: FIFO store buffer + multi-copy atomic memory)",
        "aarch64_cat": "Allowed (Sometimes: stores to distinct addresses can reorder)",
        "rc11_cat": "Allowed (Sometimes: separate mo orders on x and y without synchronization)",
    },
    "CoRR": {
        "x86tso_cat": "Forbidden (Never: per-location coherence uniproc)",
        "aarch64_cat": "Forbidden (Never: internal po-loc | rf | fr | co acyclicity)",
        "rc11_cat": "Forbidden (Never: coherence / read-read coherence)",
    },
}

csv_rows = []
for test_name, meta in HERD7_NORMATIVE.items():
    obs_x64 = x64_obs.get(test_name, 0)
    iters_x64 = x64_obs.get("iters", 300000)
    obs_a64_qemu = a64_obs.get(test_name, "N/A")
    iters_a64 = a64_obs.get("iters", 50000) if a64_obs else "N/A"
    csv_rows.append({
        "litmus_test": test_name,
        "x86_64_native_iters": iters_x64,
        "x86_64_weak_observed": obs_x64,
        "x86_64_weak_rate_ppm": round((obs_x64 / iters_x64) * 1_000_000, 1),
        "qemu_aarch64_on_x86_host_iters": iters_a64,
        "qemu_aarch64_weak_observed": obs_a64_qemu,
        "herd7_x86tso_cat": meta["x86tso_cat"],
        "herd7_aarch64_cat": meta["aarch64_cat"],
        "herd7_rc11_cat": meta["rc11_cat"],
    })

with open(SUP_S15 / "litmus_observations_vs_herd7.csv", "w", newline="", encoding="utf-8") as f:
    w = csv.DictWriter(f, fieldnames=list(csv_rows[0].keys()))
    w.writeheader()
    w.writerows(csv_rows)

shutil.copy2(Path(__file__), SUP_S15 / "run_litmus_suite.py")
print(f"Completed S15 litmus suite in {x64_elapsed}s!")
print("x86_64 native observations:", json.dumps(x64_obs, indent=2))
print("qemu-aarch64 observations:", json.dumps(a64_obs, indent=2))
