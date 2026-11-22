#!/usr/bin/env python3
"""Empirical rustc + Miri probe for Edition 2024 `gen` & `async gen` blocks:
- Part A: Movable `gen` (`Unpin`, `FusedIterator`, mid-yield `core::mem::swap`,
  `BitMatrix` `storage_conflicts` saved-local slot aliasing (`257 B` vs `513 B`),
  and `#73137` assignment-handoff layout) + pinned `async gen` (`!Unpin`,
  self-borrow across `yield` and `.await`, `for await`, normal-return fusing),
  executed natively + under Miri Stacked Borrows + under Miri Tree Borrows.
- Part B: 4-way post-panic & post-return coroutine resumption matrix (`gen`,
  `async gen`, `async`, and raw `#[coroutine]` movable/static), reproducing the
  live post-panic `gen` fusing bug (`CoroutineArgs::POISONED` -> `ResumedAfterPanic`).
- Part C: 11-case compile-time soundness & edition-gate matrix (Edition 2021 vs
  2024 `gen` keyword, non-unit `return`, `E0626` on local & by-value upvar borrows
  vs allowed external-ref & `Box` deref borrows, `async gen` self-borrow acceptance
  and `!Unpin` `E0277`, `gen` unconditional `Unpin` with `PhantomPinned`, and
  built-in `FusedIterator`).
- Part D: Live `-Zdump-mir=StateTransform`, `-Zvalidate-mir`, and `-Zprint-type-sizes`
  capture for `gen`, `async gen`, and disjoint/handoff/overlapping saved locals.

Runs completely offline using only the active `rustc` toolchain and its bundled
`rust-src` library sources to construct a hermetic Miri sysroot (`core`,
`compiler_builtins`, `alloc`).
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
from pathlib import Path
import re
import shutil
import socket
import subprocess
import sys
import tempfile
from typing import Any


def _find_rustc_and_miri() -> tuple[str, str, Path]:
    rustc = shutil.which("rustc")
    if not rustc:
        cand = Path.home() / ".cargo" / "bin" / "rustc"
        if cand.exists():
            rustc = str(cand)
    if not rustc:
        raise RuntimeError("rustc not found in PATH or ~/.cargo/bin")

    sysroot_proc = subprocess.run(
        [rustc, "--print", "sysroot"],
        capture_output=True,
        text=True,
        check=True,
        timeout=15,
    )
    toolchain_root = Path(sysroot_proc.stdout.strip())
    miri_cand = toolchain_root / "bin" / "miri"
    if miri_cand.exists():
        miri_bin = str(miri_cand)
    else:
        found_miri = shutil.which("miri")
        if not found_miri:
            raise RuntimeError("miri driver binary not found in toolchain sysroot or PATH")
        miri_bin = found_miri
    return rustc, miri_bin, toolchain_root


def _clean_env() -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    path_parts = env.get("PATH", "").split(os.pathsep)
    if cargo_bin not in path_parts and os.path.isdir(cargo_bin):
        env["PATH"] = os.pathsep.join([cargo_bin, *path_parts])
    return env


def _scrub_text(text: str, tmp_dir: Path | None = None) -> str:
    out = text
    if tmp_dir is not None:
        out = out.replace(str(tmp_dir.resolve()), "<TMP>")
        out = out.replace(str(tmp_dir), "<TMP>")
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    host = socket.gethostname()
    if host:
        out = out.replace(host, "<HOST>")
    out = re.sub(r"/tmp/[^\s:\"']+", "<TMP>", out)
    return out


def _extract_error_codes(stderr: str) -> list[str]:
    return sorted(set(re.findall(r"error\[E\d{4}\]", stderr)))


def _build_hermetic_miri_sysroot(
    rustc: str, toolchain_root: Path, env: dict[str, str], sysroot_dir: Path
) -> None:
    """Build a self-contained offline Miri sysroot (core + compiler_builtins + alloc)."""
    host_proc = subprocess.run(
        [rustc, "-vV"], env=env, capture_output=True, text=True, check=True, timeout=15
    )
    host_triple = "x86_64-unknown-linux-gnu"
    for line in host_proc.stdout.splitlines():
        if line.startswith("host:"):
            host_triple = line.split(":", 1)[1].strip()
            break

    lib_src = toolchain_root / "lib" / "rustlib" / "src" / "rust" / "library"
    libdir = sysroot_dir / "lib" / "rustlib" / host_triple / "lib"
    libdir.mkdir(parents=True, exist_ok=True)

    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=core",
            "--crate-type=rlib",
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(lib_src / "core" / "src" / "lib.rs"),
            "-o",
            str(libdir / "libcore.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=120,
    )

    cb_rs = sysroot_dir / "compiler_builtins_stub.rs"
    cb_rs.write_text(
        "#![feature(compiler_builtins)]\n#![no_std]\n#![compiler_builtins]\n",
        encoding="utf-8",
    )
    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=compiler_builtins",
            "--crate-type=rlib",
            "--sysroot",
            str(sysroot_dir),
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(cb_rs),
            "-o",
            str(libdir / "libcompiler_builtins.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )

    subprocess.run(
        [
            rustc,
            "--edition=2024",
            "--crate-name=alloc",
            "--crate-type=rlib",
            "--sysroot",
            str(sysroot_dir),
            "-Zalways-encode-mir",
            "-Cpanic=abort",
            "--cap-lints=allow",
            str(lib_src / "alloc" / "src" / "lib.rs"),
            "-o",
            str(libdir / "liballoc.rlib"),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
        timeout=90,
    )


MIRI_PREAMBLE = """#![feature(gen_blocks, async_for_loop, async_iterator)]
#![no_std]
#![no_main]
extern crate alloc;
use alloc::{format, string::String};
use core::{
    alloc::{GlobalAlloc, Layout},
    async_iter::AsyncIterator,
    future::Future,
    iter::FusedIterator,
    marker::PhantomPinned,
    mem,
    pin::{Pin, pin},
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

unsafe extern "Rust" {
    fn miri_alloc(size: usize, align: usize) -> *mut u8;
    fn miri_dealloc(ptr: *mut u8, size: usize, align: usize);
    fn miri_write_to_stdout(bytes: &[u8]);
}

struct MiriHostAlloc;
unsafe impl GlobalAlloc for MiriHostAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { miri_alloc(layout.size(), layout.align()) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { miri_dealloc(ptr, layout.size(), layout.align()) }
    }
}

#[global_allocator]
static GLOBAL_MIRI_ALLOC: MiriHostAlloc = MiriHostAlloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

fn emit_line(s: &str) {
    unsafe {
        miri_write_to_stdout(s.as_bytes());
        miri_write_to_stdout(b"\\n");
    }
}
"""

NATIVE_PREAMBLE = """#![feature(gen_blocks, async_for_loop, async_iterator)]
use core::{
    async_iter::AsyncIterator,
    future::Future,
    iter::FusedIterator,
    marker::PhantomPinned,
    mem,
    pin::{Pin, pin},
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

fn emit_line(s: &str) {
    println!("{s}");
}
"""

PART_A_SHARED_BODY = """
fn is_unpin<T: Unpin>(_: &T) -> bool {
    true
}

fn is_fused_iterator<T: FusedIterator>(_: &T) -> bool {
    true
}

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker {
        RawWaker::new(core::ptr::null(), &VTABLE)
    }
    unsafe fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn block_on<F: Future>(fut: F) -> F::Output {
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut fut = pin!(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(v) => return v,
            Poll::Pending => {}
        }
    }
}

struct YieldOnce(bool);
impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if !self.0 {
            self.0 = true;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

#[inline(never)]
fn make_gen_pair(base: i32) -> impl Iterator<Item = i32> + FusedIterator + Unpin {
    gen move {
        let mut x = base + 1;
        yield x;
        x += 1;
        yield x;
    }
}

fn run_part_a() -> String {
    // 1. Unpin + FusedIterator + mid-yield core::mem::swap + post-return fusing
    let mut g1 = make_gen_pair(10);
    let mut g2 = make_gen_pair(20);
    let unpin_ok = is_unpin(&g1);
    let fused_trait_ok = is_fused_iterator(&g1);

    let g_pp = gen {
        let _pp = PhantomPinned;
        yield 1u8;
        let _keep = _pp;
    };
    let unpin_with_pp = is_unpin(&g_pp);

    let s1 = g1.next();
    mem::swap(&mut g1, &mut g2);
    let s2 = g1.next();
    let s3 = g1.next();
    let s4 = g2.next();
    let fused = (g1.next(), g1.next());

    // 2. BitMatrix storage_conflicts saved-local slot aliasing:
    //    (a) disjoint scopes -> a and b overlap in storage -> 257 B (1B discr + 256B)
    let mut g_disjoint = gen {
        {
            let mut a = [1u8; 256];
            a[0] = 3;
            yield a[0];
            yield a[255];
        }
        {
            let mut b = [2u8; 256];
            b[0] = 5;
            yield b[0];
            yield b[255];
        }
    };
    let sz_disjoint = mem::size_of_val(&g_disjoint);

    //    (b) simultaneous liveness across yield 2 -> 513 B (1B discr + 256B + 256B)
    let mut g_overlap = gen {
        let mut a = [1u8; 256];
        a[0] = 2;
        yield a[0];
        let mut b = [3u8; 256];
        b[0] = 4;
        yield b[0];
        yield a[255] + b[255];
    };
    let sz_overlap = mem::size_of_val(&g_overlap);

    //    (c) #73137 pattern: a live across yield 1 only, then `b = a` (single assignment
    //        where a is last-used and b is initialized), b live across yield 2 only.
    let mut g_handoff = gen {
        let mut a = [1u8; 256];
        a[0] = 7;
        yield a[0];
        let mut b = a;
        b[1] = 8;
        yield b[1];
        yield b[255];
    };
    let sz_handoff = mem::size_of_val(&g_handoff);

    let sum_disjoint: u32 = (&mut g_disjoint).map(|x| x as u32).sum();
    let sum_overlap: u32 = (&mut g_overlap).map(|x| x as u32).sum();
    let sum_handoff: u32 = (&mut g_handoff).map(|x| x as u32).sum();

    // 3. Pinned self-borrowing async gen consumed via `for await` + normal-return fusing
    let (ag_sum, ag_addr_stable, ag_returned_fused) = block_on(async {
        let mut stable = true;
        let stream = async gen {
            let arr = [10u32, 20, 30, 40];
            let r: &[u32] = &arr[..];
            let p0 = r.as_ptr() as usize;
            yield (r[0] + r[1], p0);
            YieldOnce(false).await;
            let p1 = r.as_ptr() as usize;
            yield (r[2] + r[3], p1);
            YieldOnce(false).await;
            let p2 = r.as_ptr() as usize;
            yield (r[0] + r[1] + r[2] + r[3] - 16, p2);
        };
        let mut total = 0u32;
        let mut first_ptr: Option<usize> = None;
        for await (val, ptr) in stream {
            if let Some(p0) = first_ptr {
                if ptr != p0 {
                    stable = false;
                }
            } else {
                first_ptr = Some(ptr);
            }
            total += val;
        }

        // Verify normal completion fusing on async gen directly via AsyncIterator::poll_next
        let mut s2 = pin!(async gen {
            yield 42u32;
        });
        let waker = noop_waker();
        let mut cx = Context::from_waker(&waker);
        let p_first = s2.as_mut().poll_next(&mut cx);
        let p_done1 = s2.as_mut().poll_next(&mut cx);
        let p_done2 = s2.as_mut().poll_next(&mut cx);
        let p_done3 = s2.as_mut().poll_next(&mut cx);
        let fused_ok = p_first == Poll::Ready(Some(42))
            && p_done1 == Poll::Ready(None)
            && p_done2 == Poll::Ready(None)
            && p_done3 == Poll::Ready(None);
        (total, stable, fused_ok)
    });

    format!(
        "UNPIN={} UNPIN_PP={} FUSED_TRAIT={} SWAP={:?},{:?},{:?},{:?} FUSED={:?} \
SZ_DISJOINT={} SZ_OVERLAP={} SZ_HANDOFF_73137={} SUMS={},{},{} \
ASYNC_GEN=({}, {}) ASYNC_GEN_RETURNED_FUSED={}",
        unpin_ok,
        unpin_with_pp,
        fused_trait_ok,
        s1,
        s2,
        s3,
        s4,
        fused,
        sz_disjoint,
        sz_overlap,
        sz_handoff,
        sum_disjoint,
        sum_overlap,
        sum_handoff,
        ag_sum,
        ag_addr_stable,
        ag_returned_fused
    )
}
"""

PART_A_NATIVE_MAIN = """
fn main() {
    emit_line(&run_part_a());
}
"""

PART_A_MIRI_MAIN = """
#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    emit_line(&run_part_a());
    0
}
"""


def run_part_a(
    rustc: str, miri_bin: str, miri_sysroot: Path, env: dict[str, str]
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        native_rs = tmp / "part_a_native.rs"
        native_bin = tmp / "part_a_native"
        native_rs.write_text(
            NATIVE_PREAMBLE + PART_A_SHARED_BODY + PART_A_NATIVE_MAIN, encoding="utf-8"
        )
        cproc = subprocess.run(
            [rustc, "--edition=2024", "-Zvalidate-mir", str(native_rs), "-o", str(native_bin)],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        native_stdout = ""
        native_rc = -1
        if cproc.returncode == 0:
            rproc = subprocess.run(
                [str(native_bin)], env=env, capture_output=True, text=True, timeout=30
            )
            native_rc = rproc.returncode
            native_stdout = _scrub_text(rproc.stdout.strip(), tmp)

        miri_rs = tmp / "part_a_miri.rs"
        miri_rs.write_text(
            MIRI_PREAMBLE + PART_A_SHARED_BODY + PART_A_MIRI_MAIN, encoding="utf-8"
        )
        sb_proc = subprocess.run(
            [
                miri_bin,
                "--sysroot",
                str(miri_sysroot),
                "--edition=2024",
                "-Cpanic=abort",
                str(miri_rs),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        tb_proc = subprocess.run(
            [
                miri_bin,
                "--sysroot",
                str(miri_sysroot),
                "--edition=2024",
                "-Cpanic=abort",
                "-Zmiri-tree-borrows",
                str(miri_rs),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        return {
            "compile_rc": cproc.returncode,
            "compile_stderr": _scrub_text(cproc.stderr, tmp),
            "native_rc": native_rc,
            "native_stdout": native_stdout,
            "miri_sb_rc": sb_proc.returncode,
            "miri_sb_stdout": _scrub_text(sb_proc.stdout.strip(), tmp),
            "miri_sb_stderr": _scrub_text(sb_proc.stderr.strip(), tmp),
            "miri_tb_rc": tb_proc.returncode,
            "miri_tb_stdout": _scrub_text(tb_proc.stdout.strip(), tmp),
            "miri_tb_stderr": _scrub_text(tb_proc.stderr.strip(), tmp),
            "all_three_outputs_identical": (
                native_rc == 0
                and sb_proc.returncode == 0
                and tb_proc.returncode == 0
                and native_stdout == _scrub_text(sb_proc.stdout.strip(), tmp)
                and native_stdout == _scrub_text(tb_proc.stdout.strip(), tmp)
            ),
        }


PART_B_SOURCE = r"""#![feature(gen_blocks, async_iterator, coroutines, coroutine_trait, stmt_expr_attributes)]
use core::{
    async_iter::AsyncIterator,
    future::Future,
    ops::Coroutine,
    pin::pin,
    task::{Context, RawWaker, RawWakerVTable, Waker},
};
use std::panic::{AssertUnwindSafe, catch_unwind};

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker {
        RawWaker::new(core::ptr::null(), &VTABLE)
    }
    unsafe fn noop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn extract_panic_msg(payload: Box<dyn core::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string-panic>".to_string()
    }
}

fn main() {
    // 1. `gen` block post-panic resumption bug (with reachable return path too)
    let should_panic = true;
    let mut g = gen {
        yield 1i32;
        if should_panic {
            panic!("mid-gen-boom");
        }
        yield 2i32;
    };
    let g_step1 = g.next();
    let g_step2 = catch_unwind(AssertUnwindSafe(|| g.next())).err().map(extract_panic_msg);
    let g_step3 = match catch_unwind(AssertUnwindSafe(|| g.next())) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    println!("GEN: STEP1={g_step1:?} STEP2_PANIC={g_step2:?} STEP3_{g_step3}");

    // 2. `async gen` block post-panic resumption
    let waker = noop_waker();
    let mut cx = Context::from_waker(&waker);
    let mut ag = pin!(async gen {
        yield 1i32;
        if should_panic {
            panic!("mid-async-gen-boom");
        }
        yield 2i32;
    });
    let ag_step1 = ag.as_mut().poll_next(&mut cx);
    let ag_step2 = catch_unwind(AssertUnwindSafe(|| ag.as_mut().poll_next(&mut cx)))
        .err()
        .map(extract_panic_msg);
    let ag_step3 = match catch_unwind(AssertUnwindSafe(|| ag.as_mut().poll_next(&mut cx))) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    println!("ASYNC_GEN: STEP1={ag_step1:?} STEP2_PANIC={ag_step2:?} STEP3_{ag_step3}");

    // 3. `async` block post-return and post-panic resumption
    let mut af_done = pin!(async { 7i32 });
    let af_r1 = af_done.as_mut().poll(&mut cx);
    let af_r2 = match catch_unwind(AssertUnwindSafe(|| af_done.as_mut().poll(&mut cx))) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    let mut af_boom = pin!(async {
        if should_panic {
            panic!("mid-async-boom");
        }
        0i32
    });
    let af_p1 = catch_unwind(AssertUnwindSafe(|| af_boom.as_mut().poll(&mut cx)))
        .err()
        .map(extract_panic_msg);
    let af_p2 = match catch_unwind(AssertUnwindSafe(|| af_boom.as_mut().poll(&mut cx))) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    println!("ASYNC: AFTER_RETURN=({af_r1:?}, {af_r2}) AFTER_PANIC=({af_p1:?}, {af_p2})");

    // 4. Raw `#[coroutine]` post-return and post-panic resumption
    let mut co_done = pin!(#[coroutine] || {
        yield 1i32;
        99i32
    });
    let co_r1 = co_done.as_mut().resume(());
    let co_r2 = co_done.as_mut().resume(());
    let co_r3 = match catch_unwind(AssertUnwindSafe(|| co_done.as_mut().resume(()))) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    let mut co_boom = pin!(#[coroutine] || {
        yield 1i32;
        if should_panic {
            panic!("mid-coro-boom");
        }
        0i32
    });
    let co_p1 = co_boom.as_mut().resume(());
    let co_p2 = catch_unwind(AssertUnwindSafe(|| co_boom.as_mut().resume(())))
        .err()
        .map(extract_panic_msg);
    let co_p3 = match catch_unwind(AssertUnwindSafe(|| co_boom.as_mut().resume(()))) {
        Ok(v) => format!("RETURNED={v:?}"),
        Err(e) => format!("PANICKED={:?}", extract_panic_msg(e)),
    };
    println!("COROUTINE: AFTER_RETURN=({co_r1:?}, {co_r2:?}, {co_r3}) AFTER_PANIC=({co_p1:?}, {co_p2:?}, {co_p3})");
}
"""


def run_part_b(rustc: str, env: dict[str, str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        src = tmp / "part_b.rs"
        bin_path = tmp / "part_b"
        src.write_text(PART_B_SOURCE, encoding="utf-8")
        cproc = subprocess.run(
            [rustc, "--edition=2024", "-Zvalidate-mir", str(src), "-o", str(bin_path)],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        stdout_lines: list[str] = []
        native_rc = -1
        if cproc.returncode == 0:
            rproc = subprocess.run(
                [str(bin_path)], env=env, capture_output=True, text=True, timeout=30
            )
            native_rc = rproc.returncode
            stdout_lines = [
                _scrub_text(line.strip(), tmp)
                for line in rproc.stdout.splitlines()
                if line.strip()
            ]
        return {
            "compile_rc": cproc.returncode,
            "compile_stderr": _scrub_text(cproc.stderr, tmp),
            "native_rc": native_rc,
            "stdout_lines": stdout_lines,
        }


PART_C_CASES: list[tuple[str, str, str]] = [
    (
        "edition2021_gen_accepted_as_ident",
        "2021",
        "pub fn f() -> i32 { let gen = 7; gen }\n",
    ),
    (
        "edition2024_gen_keyword_rejected_as_ident",
        "2024",
        "pub fn f() -> i32 { let gen = 7; gen }\n",
    ),
    (
        "gen_non_unit_return_rejected",
        "2024",
        """#![feature(gen_blocks)]
pub fn f() -> impl Iterator<Item = i32> {
    gen {
        yield 1;
        return 99;
    }
}
""",
    ),
    (
        "gen_self_borrow_across_yield_rejected_e0626",
        "2024",
        """#![feature(gen_blocks)]
pub fn f() -> impl Iterator<Item = i32> {
    gen {
        let x = 42;
        let r = &x;
        yield 1;
        yield *r;
    }
}
""",
    ),
    (
        "async_gen_self_borrow_across_yield_accepted",
        "2024",
        """#![feature(gen_blocks, async_iterator)]
pub fn f() -> impl core::async_iter::AsyncIterator<Item = i32> {
    async gen {
        let x = 42;
        let r = &x;
        yield 1;
        yield *r;
    }
}
""",
    ),
    (
        "gen_move_upvar_borrow_across_yield_rejected_e0626",
        "2024",
        """#![feature(gen_blocks)]
pub fn f(upvar: i32) -> impl Iterator<Item = i32> {
    gen move {
        let r = &upvar;
        yield 1;
        yield *r;
    }
}
""",
    ),
    (
        "gen_external_ref_reborrow_across_yield_accepted",
        "2024",
        """#![feature(gen_blocks)]
pub fn f<'a>(ext: &'a [i32]) -> impl Iterator<Item = i32> + 'a {
    gen move {
        let r = &ext[0];
        yield *r;
        yield *r;
    }
}
""",
    ),
    (
        "gen_box_deref_borrow_across_yield_check",
        "2024",
        """#![feature(gen_blocks)]
pub fn f() -> impl Iterator<Item = i32> {
    gen {
        let b = Box::new(42i32);
        let r = &*b;
        yield *r;
        yield *r;
    }
}
""",
    ),
    (
        "async_gen_is_not_unpin_rejected_e0277",
        "2024",
        """#![feature(gen_blocks, async_iterator)]
fn assert_unpin<T: Unpin>(_: T) {}
pub fn f() {
    let ag = async gen {
        yield 1i32;
    };
    assert_unpin(ag);
}
""",
    ),
    (
        "gen_with_phantom_pinned_is_unpin_accepted",
        "2024",
        """#![feature(gen_blocks)]
use core::marker::PhantomPinned;
fn assert_unpin<T: Unpin>(_: T) {}
pub fn f() {
    let g = gen {
        let p = PhantomPinned;
        yield 1i32;
        let _ = p;
    };
    assert_unpin(g);
}
""",
    ),
    (
        "gen_block_is_fused_iterator_accepted",
        "2024",
        """#![feature(gen_blocks)]
fn assert_fused<T: core::iter::FusedIterator>(_: T) {}
pub fn f() {
    let g = gen {
        yield 1i32;
    };
    assert_fused(g);
}
""",
    ),
]


def run_part_c(rustc: str, env: dict[str, str]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        for name, edition, src_code in PART_C_CASES:
            src_file = tmp / f"{name}.rs"
            rlib_file = tmp / f"lib{name}.rlib"
            src_file.write_text(src_code, encoding="utf-8")
            proc = subprocess.run(
                [
                    rustc,
                    f"--edition={edition}",
                    "--crate-type=lib",
                    "-Zvalidate-mir",
                    str(src_file),
                    "-o",
                    str(rlib_file),
                ],
                env=env,
                capture_output=True,
                text=True,
                timeout=60,
            )
            stderr_clean = _scrub_text(proc.stderr, tmp)
            out[name] = {
                "edition": edition,
                "rc": proc.returncode,
                "error_codes": _extract_error_codes(stderr_clean),
                "stderr": stderr_clean,
            }
    return out


PART_A2_MIRI_PREAMBLE = """#![feature(gen_blocks)]
#![no_std]
#![no_main]
extern crate alloc;
use alloc::{boxed::Box, format, string::String};
use core::{
    alloc::{GlobalAlloc, Layout},
    mem,
};

unsafe extern "Rust" {
    fn miri_alloc(size: usize, align: usize) -> *mut u8;
    fn miri_dealloc(ptr: *mut u8, size: usize, align: usize);
    fn miri_write_to_stdout(bytes: &[u8]);
}

struct MiriHostAlloc;
unsafe impl GlobalAlloc for MiriHostAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { miri_alloc(layout.size(), layout.align()) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { miri_dealloc(ptr, layout.size(), layout.align()) }
    }
}

#[global_allocator]
static GLOBAL_MIRI_ALLOC: MiriHostAlloc = MiriHostAlloc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

fn emit_line(s: &str) {
    unsafe {
        miri_write_to_stdout(s.as_bytes());
        miri_write_to_stdout(b"\\n");
    }
}
"""

PART_A2_BOX_SWAP_SHARED = """
fn make_box_deref_gen(v: i32) -> impl Iterator<Item = i32> + Unpin {
    gen move {
        let b = Box::new(v);
        let r: &i32 = &*b;
        yield *r;
        yield *r + 100;
    }
}

fn run_part_a2_box_swap() -> String {
    let mut g1 = make_box_deref_gen(11);
    let mut g2 = make_box_deref_gen(22);
    let a = g1.next();
    mem::swap(&mut g1, &mut g2);
    let b = g1.next();
    let c = g1.next();
    let d = g2.next();
    format!("BOX_DEREF_SWAP={a:?},{b:?},{c:?},{d:?}")
}
"""


def run_part_a2_box_swap(
    rustc: str, miri_bin: str, miri_sysroot: Path, env: dict[str, str]
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        native_rs = tmp / "part_a2_native.rs"
        native_bin = tmp / "part_a2_native"
        native_src = (
            "#![feature(gen_blocks)]\nuse core::mem;\nfn emit_line(s: &str) { println!(\"{s}\"); }\n"
            + PART_A2_BOX_SWAP_SHARED
            + "\nfn main() { emit_line(&run_part_a2_box_swap()); }\n"
        )
        native_rs.write_text(native_src, encoding="utf-8")
        cproc = subprocess.run(
            [rustc, "--edition=2024", "-Zvalidate-mir", str(native_rs), "-o", str(native_bin)],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )
        native_rc = -1
        native_stdout = ""
        if cproc.returncode == 0:
            rproc = subprocess.run(
                [str(native_bin)], env=env, capture_output=True, text=True, timeout=30
            )
            native_rc = rproc.returncode
            native_stdout = _scrub_text(rproc.stdout.strip(), tmp)

        miri_rs = tmp / "part_a2_miri.rs"
        miri_src = (
            PART_A2_MIRI_PREAMBLE
            + PART_A2_BOX_SWAP_SHARED
            + '\n#[unsafe(no_mangle)]\nfn miri_start(_argc: isize, _argv: *const *const u8) -> isize { emit_line(&run_part_a2_box_swap()); 0 }\n'
        )
        miri_rs.write_text(miri_src, encoding="utf-8")
        sb_proc = subprocess.run(
            [
                miri_bin,
                "--sysroot",
                str(miri_sysroot),
                "--edition=2024",
                "-Cpanic=abort",
                str(miri_rs),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        tb_proc = subprocess.run(
            [
                miri_bin,
                "--sysroot",
                str(miri_sysroot),
                "--edition=2024",
                "-Cpanic=abort",
                "-Zmiri-tree-borrows",
                str(miri_rs),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        return {
            "compile_rc": cproc.returncode,
            "native_rc": native_rc,
            "native_stdout": native_stdout,
            "miri_sb_rc": sb_proc.returncode,
            "miri_sb_stdout": _scrub_text(sb_proc.stdout.strip(), tmp),
            "miri_sb_stderr": _scrub_text(sb_proc.stderr.strip(), tmp),
            "miri_tb_rc": tb_proc.returncode,
            "miri_tb_stdout": _scrub_text(tb_proc.stdout.strip(), tmp),
            "miri_tb_stderr": _scrub_text(tb_proc.stderr.strip(), tmp),
        }


PART_D_SOURCE = r"""#![feature(gen_blocks, async_iterator)]

pub fn make_gen_cond_panic(boom: bool) -> impl Iterator<Item = i32> {
    gen move {
        yield 1;
        if boom {
            panic!("boom");
        }
        yield 2;
    }
}

pub fn make_async_gen_cond_panic(boom: bool) -> impl core::async_iter::AsyncIterator<Item = i32> {
    async gen move {
        yield 1;
        if boom {
            panic!("async-boom");
        }
        yield 2;
    }
}

pub fn make_gen_disjoint() -> impl Iterator<Item = u8> {
    gen {
        {
            let mut a = [1u8; 256];
            a[0] = 3;
            yield a[0];
            yield a[255];
        }
        {
            let mut b = [2u8; 256];
            b[0] = 5;
            yield b[0];
            yield b[255];
        }
    }
}

pub fn make_gen_handoff_73137() -> impl Iterator<Item = u8> {
    gen {
        let mut a = [1u8; 256];
        a[0] = 7;
        yield a[0];
        let mut b = a;
        b[1] = 8;
        yield b[1];
        yield b[255];
    }
}

pub fn make_gen_overlap() -> impl Iterator<Item = u8> {
    gen {
        let mut a = [1u8; 256];
        a[0] = 2;
        yield a[0];
        let mut b = [3u8; 256];
        b[0] = 4;
        yield b[0];
        yield a[255] + b[255];
    }
}

pub fn force_layouts() -> (usize, usize, usize, usize, usize) {
    (
        core::mem::size_of_val(&make_gen_cond_panic(false)),
        core::mem::size_of_val(&make_async_gen_cond_panic(false)),
        core::mem::size_of_val(&make_gen_disjoint()),
        core::mem::size_of_val(&make_gen_handoff_73137()),
        core::mem::size_of_val(&make_gen_overlap()),
    )
}
"""


def _filter_type_sizes(stdout: str) -> list[str]:
    lines = stdout.splitlines()
    captured: list[str] = []
    keep = False
    for line in lines:
        if line.startswith("print-type-size type: `"):
            keep = (
                "gen block@" in line
                or "async gen block@" in line
            )
        if keep:
            captured.append(line)
    return captured


def _extract_coroutine_layout_header(mir_text: str) -> str:
    lines = mir_text.splitlines()
    out: list[str] = []
    in_layout = False
    depth = 0
    for line in lines:
        if line.startswith("fn "):
            out.append(line)
        elif "coroutine layout {" in line:
            in_layout = True
            depth = line.count("{") - line.count("}")
            out.append(line)
        elif in_layout:
            out.append(line)
            depth += line.count("{") - line.count("}")
            if depth <= 0:
                break
    return "\n".join(out)


def run_part_d(rustc: str, env: dict[str, str]) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        src = tmp / "part_d.rs"
        dump_dir = tmp / "mir_dump"
        dump_dir.mkdir(parents=True, exist_ok=True)
        out_rlib = tmp / "libpart_d.rlib"
        src.write_text(PART_D_SOURCE, encoding="utf-8")

        proc = subprocess.run(
            [
                rustc,
                "--edition=2024",
                "--crate-type=lib",
                "-O",
                "-Zvalidate-mir",
                "-Zprint-type-sizes",
                f"-Zdump-mir-dir={dump_dir}",
                "-Zdump-mir=StateTransform|coroutine_resume",
                str(src),
                "-o",
                str(out_rlib),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
        )

        mir_extracts: dict[str, str] = {}
        layout_headers: dict[str, str] = {}
        for mf in sorted(dump_dir.glob("*.mir")):
            name = mf.name
            if "coroutine_resume.0.mir" not in name:
                continue
            text = _scrub_text(mf.read_text(encoding="utf-8"), tmp)
            if "cond_panic" in name:
                mir_extracts[name] = text
            if (
                "make_gen_disjoint" in name
                or "make_gen_handoff_73137" in name
                or "make_gen_overlap" in name
            ):
                layout_headers[name] = _extract_coroutine_layout_header(text)

        return {
            "compile_rc": proc.returncode,
            "compile_stderr": _scrub_text(proc.stderr, tmp),
            "type_size_lines": _filter_type_sizes(_scrub_text(proc.stdout, tmp)),
            "mir_extracts": mir_extracts,
            "layout_headers": layout_headers,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Optional JSON output file")
    args = parser.parse_args()

    rustc, miri_bin, toolchain_root = _find_rustc_and_miri()
    env = _clean_env()

    rustc_vv = subprocess.run(
        [rustc, "-vV"], env=env, capture_output=True, text=True, check=True, timeout=15
    ).stdout.strip()
    miri_v = subprocess.run(
        [miri_bin, "--version"], env=env, capture_output=True, text=True, check=True, timeout=15
    ).stdout.strip()

    with tempfile.TemporaryDirectory() as sysroot_td:
        miri_sysroot = Path(sysroot_td) / "miri_sysroot"
        _build_hermetic_miri_sysroot(rustc, toolchain_root, env, miri_sysroot)

        result = {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime(
                "%Y-%m-%dT%H:%M:%SZ"
            ),
            "rustc_version": rustc_vv,
            "miri_version": miri_v,
            "part_a_gen_async_gen_swap_for_await_and_miri": run_part_a(
                rustc, miri_bin, miri_sysroot, env
            ),
            "part_a2_box_deref_swap_miri_sb_vs_tb": run_part_a2_box_swap(
                rustc, miri_bin, miri_sysroot, env
            ),
            "part_b_post_panic_fusing_4way": run_part_b(rustc, env),
            "part_c_compile_time_soundness_gates": run_part_c(rustc, env),
            "part_d_mir_lowering_and_type_sizes": run_part_d(rustc, env),
        }

    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.out} ({len(rendered)} bytes)")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
