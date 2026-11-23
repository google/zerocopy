#!/usr/bin/env python3
"""Reproducible probe of LLVM GlobalOpt / InstCombine / SROA / DSE boundaries
for x86_64 SeqCst and Release/AcqRel atomic store-buffer draining under
rustc -Copt-level=3 -Clto=fat.
"""

import pathlib
import re
import subprocess
import sys
import tempfile


RUST_SRC = r"""
#![crate_type = "cdylib"]
extern crate alloc;
use alloc::boxed::Box;
use core::sync::atomic::{compiler_fence, fence, AtomicUsize, Ordering};

pub static X: AtomicUsize = AtomicUsize::new(0);
pub static Y: AtomicUsize = AtomicUsize::new(0);
pub static Z: AtomicUsize = AtomicUsize::new(0);
pub static PUB_ADDR: AtomicUsize = AtomicUsize::new(0);
pub static BIT_OUT: AtomicUsize = AtomicUsize::new(0);

static PRIV_WRITE_ONLY: AtomicUsize = AtomicUsize::new(0);
static PRIV_SAME_INIT: AtomicUsize = AtomicUsize::new(1);
static PRIV_DIFF_INIT_LOAD: AtomicUsize = AtomicUsize::new(0);
static PRIV_SWAP_SAME_INIT: AtomicUsize = AtomicUsize::new(1);
static PRIV_CAS_SAME_INIT: AtomicUsize = AtomicUsize::new(0);
static PRIV_DSE_TWO_STORES: AtomicUsize = AtomicUsize::new(0);

#[no_mangle]
pub extern "C" fn keep_io_live(vx: usize, vy: usize) -> usize {
    X.store(vx, Ordering::Relaxed);
    Y.store(vy, Ordering::Relaxed);
    Z.store(vx, Ordering::Relaxed);
    X.load(Ordering::Relaxed)
        .wrapping_add(Y.load(Ordering::Relaxed))
        .wrapping_add(Z.load(Ordering::Relaxed))
        .wrapping_add(PUB_ADDR.load(Ordering::Relaxed))
        .wrapping_add(BIT_OUT.load(Ordering::Relaxed))
        .wrapping_add(PRIV_SAME_INIT.load(Ordering::SeqCst))
        .wrapping_add(PRIV_DIFF_INIT_LOAD.load(Ordering::Relaxed))
        .wrapping_add(PRIV_DSE_TWO_STORES.load(Ordering::Relaxed))
}

#[no_mangle]
pub extern "C" fn elim_priv_write_only() -> usize {
    X.store(1, Ordering::Release);
    PRIV_WRITE_ONLY.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_priv_same_init() -> usize {
    X.store(1, Ordering::Release);
    PRIV_SAME_INIT.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_box_leaked_unescaped() -> usize {
    X.store(1, Ordering::Release);
    let b = Box::leak(Box::new(AtomicUsize::new(0)));
    b.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_local_expose_roundtrip() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    let ptr = core::ptr::with_exposed_provenance::<AtomicUsize>(addr);
    X.store(1, Ordering::Release);
    unsafe { (*ptr).store(1, Ordering::SeqCst); }
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_local_branch_ne0() -> usize {
    X.store(1, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    if addr != 0 {
        local.store(1, Ordering::SeqCst);
    }
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_rlx() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_acq() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Acquire);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_rel() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Release);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_acqrel() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::AcqRel);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn keep_hw_fence_sc() -> usize {
    X.store(1, Ordering::Release);
    fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_idempotent_add0_sc() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn keep_published_exposed_addr() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    PUB_ADDR.store(addr, Ordering::Release);
    X.store(1, Ordering::Release);
    local.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_branched_exposed_addr() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    if addr & 8 != 0 {
        BIT_OUT.store(1, Ordering::Release);
    }
    X.store(1, Ordering::Release);
    local.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_diff_init_with_load() -> usize {
    X.store(1, Ordering::Release);
    PRIV_DIFF_INIT_LOAD.store(42, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_swap_same_init() -> usize {
    X.store(1, Ordering::Release);
    PRIV_SWAP_SAME_INIT.swap(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_cas_same_init() -> usize {
    X.store(1, Ordering::Release);
    let _ = PRIV_CAS_SAME_INIT.compare_exchange(0, 0, Ordering::SeqCst, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_dse_two_seqcst_stores() -> usize {
    PRIV_DSE_TWO_STORES.store(1, Ordering::SeqCst);
    X.store(1, Ordering::Release);
    PRIV_DSE_TWO_STORES.store(2, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}
"""


def extract_fn_asm(asm_text: str, fn_name: str) -> str:
    m = re.search(
        rf"(?ms)^\s*\.globl\s+{re.escape(fn_name)}\b.*?^{re.escape(fn_name)}:\n(.*?)^\.Lfunc_end",
        asm_text,
    )
    if m:
        return m.group(1)
    alias = re.search(rf"(?m)^{re.escape(fn_name)}\s*=\s*([A-Za-z0-9_.]+)\s*$", asm_text)
    if alias:
        return extract_fn_asm(asm_text, alias.group(1))
    raise AssertionError(f"missing function {fn_name} in assembly")


def has_serializing_atomic(body: str) -> bool:
    return bool(re.search(r"\b(xchgq|mfence|lock)\b", body))


def main() -> int:
    rustc = subprocess.check_output(["rustc", "-vV"], text=True)
    with tempfile.TemporaryDirectory() as d:
        src = pathlib.Path(d) / "probe.rs"
        asm = pathlib.Path(d) / "probe.s"
        src.write_text(RUST_SRC, encoding="utf-8")
        subprocess.run(
            [
                "rustc",
                "--edition=2021",
                "--target=x86_64-unknown-linux-gnu",
                "-Copt-level=3",
                "-Clto=fat",
                "--emit=asm",
                str(src),
                "-o",
                str(asm),
            ],
            check=True,
        )
        asm_text = asm.read_text(encoding="utf-8")

    eliminated = [
        "elim_priv_write_only",
        "elim_priv_same_init",
        "elim_box_leaked_unescaped",
        "elim_local_expose_roundtrip",
        "elim_local_branch_ne0",
        "elim_idempotent_add0_rlx",
        "elim_idempotent_add0_acq",
        "elim_idempotent_add0_rel",
        "elim_idempotent_add0_acqrel",
    ]
    preserved = [
        "keep_hw_fence_sc",
        "keep_idempotent_add0_sc",
        "keep_published_exposed_addr",
        "keep_branched_exposed_addr",
        "keep_priv_diff_init_with_load",
        "keep_priv_swap_same_init",
        "keep_priv_cas_same_init",
        "keep_dse_two_seqcst_stores",
    ]

    for fn in eliminated:
        body = extract_fn_asm(asm_text, fn)
        assert not has_serializing_atomic(body), f"expected 0 xchg/lock in {fn}, got:\n{body}"

    for fn in preserved:
        body = extract_fn_asm(asm_text, fn)
        assert has_serializing_atomic(body), f"expected xchg/lock in {fn}, got:\n{body}"

    dse_body = extract_fn_asm(asm_text, "keep_dse_two_seqcst_stores")
    assert len(re.findall(r"\bxchgq\b", dse_body)) == 2, f"expected 2 xchgq in DSE check, got:\n{dse_body}"

    print(f"PASS: x86_64 -Copt-level=3 -Clto=fat SeqCst/RMW elimination boundary verified ({len(eliminated)} eliminated, {len(preserved)} preserved).")
    for line in rustc.strip().splitlines()[:2]:
        print(" ", line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
