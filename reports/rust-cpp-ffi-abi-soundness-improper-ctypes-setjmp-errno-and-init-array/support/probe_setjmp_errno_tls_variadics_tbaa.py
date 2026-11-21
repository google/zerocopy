#!/usr/bin/env python3
"""Executable reproducer suite for:
1. setjmp/longjmp across Rust frames (Drop bypass, jmp_buf layout & PTR_MANGLE,
   removal of #[ffi_returns_twice] in rustc 1.78+).
2. errno & TLS FFI contracts (__errno_location IE TLS, POSIX signal handler
   clobbering errno, async Future thread migration corrupting errno & C __thread,
   STT_TLS vs STT_OBJECT linker mismatch, and #[thread_local] stability).
3. C variadics (... / VaList): stable 1.99+ Rust variadic fn definition called
   from C with default promotions, VaArgSafe compile-time rejections vs call-site
   non-FFI blind spot, and register-bank mismatch UB (i32 vs double).
4. C TBAA (strict aliasing) & restrict miscompilation under gcc -O2 vs -O0 /
   -fno-strict-aliasing, with emitted .o disassembly establishing the machine-code
   verification TCB advantage.

Uses only Python 3.10+ stdlib and cleans up all temporary build artifacts via
tempfile.TemporaryDirectory().
"""

import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


def rustc_cmd(toolchain):
    return ["rustc", f"+{toolchain}"] if toolchain else ["rustc"]


def extract_disasm_fn(dis, sym, max_lines=14):
    lines = []
    in_fn = False
    for line in dis.splitlines():
        if f"<{sym}>:" in line:
            in_fn = True
            lines.append(line.strip())
            continue
        if in_fn:
            if not line.strip():
                break
            lines.append(line.strip())
    return lines[:max_lines]


def probe_setjmp_longjmp(tmpdir, toolchain):
    c_src = Path(tmpdir) / "sj.c"
    c_src.write_text(r"""
#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static jmp_buf g_env;

void c_trigger_longjmp(int val) {
    longjmp(g_env, val);
}

int c_run_with_setjmp(void (*cb)(void), size_t *out_jmpbuf_size, uint64_t *out_saved_rsp, uint64_t *out_saved_pc) {
    *out_jmpbuf_size = sizeof(jmp_buf);
    int r = setjmp(g_env);
    if (r == 0) {
        // On glibc x86_64: __jmpbuf indices are RBX=0, RBP=1, R12=2, R13=3, R14=4, R15=5, RSP=6, PC=7
        // Note: RBP, RSP, PC are PTR_MANGLE'd with %fs:0x30!
        uint64_t words[8] = {0};
        memcpy(words, &g_env, sizeof(words));
        *out_saved_rsp = words[6];
        *out_saved_pc = words[7];
        cb();
        return 0;
    }
    return r;
}
""")
    rs_src = Path(tmpdir) / "sj_main.rs"
    rs_src.write_text(r"""
use core::sync::atomic::{AtomicU32, Ordering};

static DROPS: AtomicU32 = AtomicU32::new(0);
static MUT_SLOT: AtomicU32 = AtomicU32::new(0);

struct LockGuard<'a>(&'a mut u32);
impl Drop for LockGuard<'_> {
    fn drop(&mut self) {
        *self.0 += 1;
        DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

unsafe extern "C" {
    fn c_run_with_setjmp(
        cb: extern "C" fn(),
        out_jmpbuf_size: *mut usize,
        out_saved_rsp: *mut u64,
        out_saved_pc: *mut u64,
    ) -> i32;
    fn c_trigger_longjmp(val: i32) -> !;
}

extern "C" fn rust_frame_bypassed_by_longjmp() {
    let mut local_lock_released = 0u32;
    let _g = LockGuard(&mut local_lock_released);
    // UB under Rust Reference [undefined.runtime] and RFC 2945: longjmp deallocates
    // this non-POF Rust frame without running LockGuard::drop or exiting protector scope!
    unsafe { c_trigger_longjmp(77) }
}

fn main() {
    let mut jb_size = 0usize;
    let mut mangled_rsp = 0u64;
    let mut mangled_pc = 0u64;
    let ret = unsafe {
        c_run_with_setjmp(
            rust_frame_bypassed_by_longjmp,
            &raw mut jb_size,
            &raw mut mangled_rsp,
            &raw mut mangled_pc,
        )
    };
    let stack_probe = 0u64;
    let approx_rsp = (&raw const stack_probe) as u64;
    println!("sizeof_jmp_buf={}", jb_size);
    println!("setjmp_returned={}", ret);
    println!("rust_drops_executed={}", DROPS.load(Ordering::SeqCst));
    println!("saved_rsp_mangled_differs_from_stack={}", (mangled_rsp ^ approx_rsp) > 0x10000000);
    println!("mangled_rsp_hex=0x{:016x}", mangled_rsp);
    println!("mangled_pc_hex=0x{:016x}", mangled_pc);
    let _ = MUT_SLOT.load(Ordering::Relaxed);
}
""")
    c_obj = Path(tmpdir) / "sj.o"
    subprocess.run(["gcc", "-O2", "-c", str(c_src), "-o", str(c_obj)], check=True)
    exe = Path(tmpdir) / "sj_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + ["--edition=2024", "-C", "opt-level=2", str(rs_src), "-C", f"link-arg={c_obj}", "-o", str(exe)],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v

    # Check #[ffi_returns_twice] removal error on rustc
    rt_src = Path(tmpdir) / "rt_check.rs"
    rt_src.write_text("#![feature(ffi_returns_twice)]\nunsafe extern \"C\" { #[ffi_returns_twice] fn my_setjmp() -> i32; }\n")
    rt_run = subprocess.run(
        rustc_cmd(toolchain) + ["--edition=2024", "--crate-type=lib", "--emit=metadata", str(rt_src), "-o", str(Path(tmpdir) / "rt.rmeta")],
        capture_output=True,
        text=True,
    )
    res["ffi_returns_twice_status"] = rt_run.returncode
    res["ffi_returns_twice_stderr"] = " | ".join(
        l.strip() for l in rt_run.stderr.splitlines() if l.startswith("error")
    )
    return res


def probe_errno_and_tls(tmpdir, toolchain, nightly_tc):
    c_src = Path(tmpdir) / "errno_tls.c"
    c_src.write_text(r"""
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <unistd.h>

__thread uint64_t c_tls_var = 0x1122334455667788ULL;

int c_get_errno(void) { return errno; }
void c_set_errno(int e) { errno = e; }
uint64_t c_get_tls_var(void) { return c_tls_var; }
void c_set_tls_var(uint64_t v) { c_tls_var = v; }

static void bad_sigusr1_handler(int sig) {
    (void)sig;
    // Fails to save/restore errno -> clobbers interrupted thread's errno with ENOENT (2)!
    int fd = open("/nonexistent_anneal_probe_path_9f8e7d", O_RDONLY);
    if (fd >= 0) close(fd);
}

static void good_sigusr1_handler(int sig) {
    (void)sig;
    int saved = errno;
    int fd = open("/nonexistent_anneal_probe_path_9f8e7d", O_RDONLY);
    if (fd >= 0) close(fd);
    errno = saved;
}

void c_install_and_raise_bad_signal(void) {
    struct sigaction sa = {0};
    sa.sa_handler = bad_sigusr1_handler;
    sigaction(SIGUSR1, &sa, NULL);
    raise(SIGUSR1);
}

void c_install_and_raise_good_signal(void) {
    struct sigaction sa = {0};
    sa.sa_handler = good_sigusr1_handler;
    sigaction(SIGUSR1, &sa, NULL);
    raise(SIGUSR1);
}
""")
    c_obj = Path(tmpdir) / "errno_tls.o"
    subprocess.run(["gcc", "-O2", "-c", str(c_src), "-o", str(c_obj)], check=True)
    dis = subprocess.check_output(["objdump", "-d", str(c_obj)], text=True)
    sym_table = subprocess.check_output(["readelf", "-s", str(c_obj)], text=True)
    tls_sym_line = next((l.strip() for l in sym_table.splitlines() if "c_tls_var" in l), "")

    # 1. Live signal clobber + async Future migration across OS threads
    rs_src = Path(tmpdir) / "errno_tls_main.rs"
    rs_src.write_text(r"""
use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::sync::mpsc;

unsafe extern "C" {
    fn c_get_errno() -> i32;
    fn c_set_errno(e: i32);
    fn c_get_tls_var() -> u64;
    fn c_set_tls_var(v: u64);
    fn c_install_and_raise_bad_signal();
    fn c_install_and_raise_good_signal();
}

fn noop_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker { RawWaker::new(core::ptr::null(), &VT) }
    unsafe fn noop(_: *const ()) {}
    static VT: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VT)) }
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

fn main() {
    // Part A: Signal handler clobbering errno
    unsafe {
        c_set_errno(11); // EAGAIN
        let before_bad = c_get_errno();
        c_install_and_raise_bad_signal();
        let after_bad = c_get_errno();

        c_set_errno(11); // EAGAIN
        c_install_and_raise_good_signal();
        let after_good = c_get_errno();
        println!("signal_before_errno={}", before_bad);
        println!("signal_after_bad_handler_errno={}", after_bad);
        println!("signal_after_good_handler_errno={}", after_good);
    }

    // Part B: Async Future migrated from Worker A to Worker B across .await
    let mut fut = Box::pin(async {
        unsafe {
            c_set_errno(13); // EACCES
            c_set_tls_var(0xAAAA_1001);
        }
        YieldOnce(false).await;
        unsafe { (c_get_errno(), c_get_tls_var()) }
    });

    let (tx, rx) = mpsc::channel();
    // Worker A runs Poll 1
    let t_a = std::thread::spawn(move || {
        let w = noop_waker();
        let mut cx = Context::from_waker(&w);
        let p1 = fut.as_mut().poll(&mut cx);
        assert!(matches!(p1, Poll::Pending));
        tx.send(fut).unwrap();
    });
    // Worker B has its own errno/TLS and runs Poll 2 on the migrated Future
    let t_b = std::thread::spawn(move || {
        unsafe {
            c_set_errno(22); // EINVAL
            c_set_tls_var(0xBBBB_2002);
        }
        let mut migrated = rx.recv().unwrap();
        let w = noop_waker();
        let mut cx = Context::from_waker(&w);
        match migrated.as_mut().poll(&mut cx) {
            Poll::Ready((observed_errno, observed_tls)) => (observed_errno, observed_tls),
            Poll::Pending => panic!("expected ready"),
        }
    });
    t_a.join().unwrap();
    let (obs_errno, obs_tls) = t_b.join().unwrap();
    println!("async_migrated_observed_errno={}", obs_errno);
    println!("async_migrated_observed_tls=0x{:x}", obs_tls);
}
""")
    exe = Path(tmpdir) / "errno_tls_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + ["--edition=2024", "-C", "opt-level=2", str(rs_src), "-C", f"link-arg={c_obj}", "-o", str(exe)],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {
        "c_get_errno_asm": extract_disasm_fn(dis, "c_get_errno"),
        "c_tls_var_readelf": tls_sym_line,
    }
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v

    # 2. STT_TLS vs STT_OBJECT linker mismatch when Rust omits #[thread_local]:
    #    Compare GNU ld.bfd (rejects!) vs rust-lld (silently links and reads ELF header at offset 0x30!)
    bad_tls_rs = Path(tmpdir) / "bad_tls_link.rs"
    bad_tls_rs.write_text(r"""
unsafe extern "C" {
    static c_tls_var: u64;
}
fn main() {
    println!("0x{:016x}", unsafe { c_tls_var });
}
""")
    bad_bfd = subprocess.run(
        rustc_cmd(toolchain)
        + ["--edition=2024", str(bad_tls_rs), "-C", f"link-arg={c_obj}", "-C", "link-arg=-fuse-ld=bfd", "-o", str(Path(tmpdir) / "bad_tls_bfd")],
        capture_output=True,
        text=True,
    )
    res["stt_tls_mismatch_bfd_returncode"] = bad_bfd.returncode
    res["stt_tls_mismatch_bfd_stderr"] = " | ".join(
        l.strip() for l in bad_bfd.stderr.splitlines() if "TLS" in l or "mismatch" in l or "bad value" in l
    )[:400]

    bad_lld_bin = Path(tmpdir) / "bad_tls_lld"
    bad_lld = subprocess.run(
        rustc_cmd(toolchain)
        + ["--edition=2024", str(bad_tls_rs), "-C", f"link-arg={c_obj}", "-o", str(bad_lld_bin)],
        capture_output=True,
        text=True,
    )
    res["stt_tls_mismatch_lld_returncode"] = bad_lld.returncode
    if bad_lld.returncode == 0:
        lld_val = subprocess.check_output([str(bad_lld_bin)], text=True).strip()
        elf_hdr_30 = int.from_bytes(bad_lld_bin.read_bytes()[0x30:0x38], "little")
        res["stt_tls_mismatch_lld_runtime_val"] = lld_val
        res["stt_tls_mismatch_lld_elf_hdr_0x30"] = f"0x{elf_hdr_30:016x}"
        res["stt_tls_mismatch_lld_read_elf_header"] = (lld_val == f"0x{elf_hdr_30:016x}")

    # 3. Nightly #[thread_local] extern "C" static succeeds and reads live C __thread
    if nightly_tc:
        ok_tls_rs = Path(tmpdir) / "ok_tls_link.rs"
        ok_tls_rs.write_text(r"""
#![feature(thread_local)]
unsafe extern "C" {
    #[thread_local]
    static mut c_tls_var: u64;
    fn c_get_tls_var() -> u64;
}
fn main() {
    unsafe {
        let initial = c_tls_var;
        c_tls_var = 0xCAFE_BABE_1234_5678;
        let seen_by_c = c_get_tls_var();
        println!("nightly_tls_initial=0x{:x}", initial);
        println!("nightly_tls_seen_by_c=0x{:x}", seen_by_c);
    }
}
""")
        ok_exe = Path(tmpdir) / "ok_tls_bin"
        subprocess.run(
            rustc_cmd(nightly_tc) + ["--edition=2024", str(ok_tls_rs), "-C", f"link-arg={c_obj}", "-o", str(ok_exe)],
            check=True,
        )
        ok_out = subprocess.check_output([str(ok_exe)], text=True)
        for line in ok_out.strip().splitlines():
            k, v = line.split("=", 1)
            res[k] = v
    return res


def probe_c_variadics(tmpdir, toolchain):
    c_src = Path(tmpdir) / "var.c"
    c_src.write_text(r"""
#include <stdarg.h>
#include <stdint.h>

// Defined in Rust (stable 1.99+ c_variadic!)
double rust_sum_promoted(int count, ...);

double c_call_rust_variadic(void) {
    uint8_t a = 5;
    int16_t b = -7;
    float c = 3.5f;
    // C default argument promotions: u8->int, i16->int, float->double
    return rust_sum_promoted(3, a, b, c);
}

// Reads a double via va_arg (expects xmm0 on SysV x86_64)
double c_va_read_double(int tag, ...) {
    va_list ap;
    va_start(ap, tag);
    double d = va_arg(ap, double);
    va_end(ap);
    return d;
}
""")
    rs_src = Path(tmpdir) / "var_main.rs"
    rs_src.write_text(r"""
use core::ffi::{c_double, c_int};

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_sum_promoted(count: c_int, mut args: ...) -> c_double {
    assert_eq!(count, 3);
    unsafe {
        let a: c_int = args.next_arg();
        let b: c_int = args.next_arg();
        let c: c_double = args.next_arg();
        (a + b) as f64 + c
    }
}

unsafe extern "C" {
    fn c_call_rust_variadic() -> c_double;
    fn c_va_read_double(tag: c_int, ...) -> c_double;
}

fn main() {
    unsafe {
        let promoted_sum = c_call_rust_variadic();
        let right = c_va_read_double(1, 42.5_f64);
        // Type mismatch: pass i32 (in %esi) where C va_arg expects double (from %xmm0)!
        let wrong = c_va_read_double(1, 42_i32);
        println!("stable_rust_variadic_promoted_sum={}", promoted_sum);
        println!("va_right_double={}", right);
        println!("va_wrong_i32_read_as_double_bits=0x{:016x}", wrong.to_bits());
        println!("va_wrong_equals_42_5={}", wrong == 42.5);
    }
}
""")
    c_obj = Path(tmpdir) / "var.o"
    subprocess.run(["gcc", "-O2", "-c", str(c_src), "-o", str(c_obj)], check=True)
    exe = Path(tmpdir) / "var_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + ["--edition=2024", "-C", "opt-level=2", str(rs_src), "-C", f"link-arg={c_obj}", "-o", str(exe)],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v

    # Confirm VaList::next_arg::<f32> is rejected by VaArgSafe on 1.99.1
    va_err_rs = Path(tmpdir) / "va_arg_f32_err.rs"
    va_err_rs.write_text("pub unsafe extern \"C\" fn f(_n: i32, mut ap: ...) -> f32 { unsafe { ap.next_arg::<f32>() } }\n")
    r_err = subprocess.run(
        rustc_cmd(toolchain) + ["--edition=2024", "--crate-type=lib", "--emit=metadata", str(va_err_rs), "-o", str(Path(tmpdir) / "va_err.rmeta")],
        capture_output=True,
        text=True,
    )
    res["va_arg_f32_returncode"] = r_err.returncode
    res["va_arg_f32_stderr"] = " | ".join(
        l.strip() for l in r_err.stderr.splitlines() if l.startswith("error") or "VaArgSafe" in l
    )[:300]
    return res


def probe_tbaa_and_restrict(tmpdir, toolchain):
    c_src = Path(tmpdir) / "tbaa.c"
    c_src.write_text(r"""
#include <stdint.h>

// Violates C11/C23 6.5p7 effective type / strict aliasing if a and b alias!
uint32_t c_tbaa_write_read(uint32_t *a, float *b) {
    *a = 1;
    *b = 2.0f; // IEEE-754 bits: 0x40000000
    return *a;
}

// Violates C11/C23 6.7.3.1 restrict if a and b alias!
uint32_t c_restrict_write_read(uint32_t *restrict a, uint32_t *restrict b) {
    *a = 10;
    *b = 20;
    return *a;
}
""")
    rs_src = Path(tmpdir) / "tbaa_main.rs"
    rs_src.write_text(r"""
unsafe extern "C" {
    fn c_tbaa_write_read(a: *mut u32, b: *mut f32) -> u32;
    fn c_restrict_write_read(a: *mut u32, b: *mut u32) -> u32;
}

fn main() {
    let mut word: u32 = 0;
    let p_u32: *mut u32 = &raw mut word;
    let p_f32: *mut f32 = p_u32.cast();
    let tbaa_ret = unsafe { c_tbaa_write_read(p_u32, p_f32) };
    let mem_after_tbaa = word;

    word = 0;
    let restrict_ret = unsafe { c_restrict_write_read(p_u32, p_u32) };
    let mem_after_restrict = word;

    println!("tbaa_ret=0x{:08x}", tbaa_ret);
    println!("mem_after_tbaa=0x{:08x}", mem_after_tbaa);
    println!("restrict_ret={}", restrict_ret);
    println!("mem_after_restrict={}", mem_after_restrict);
}
""")
    configs = [
        ("O0", ["-O0"]),
        ("O2_fno_strict_aliasing", ["-O2", "-fno-strict-aliasing"]),
        ("O2_default", ["-O2"]),
    ]
    results = {}
    for label, flags in configs:
        obj = Path(tmpdir) / f"tbaa_{label}.o"
        subprocess.run(["gcc"] + flags + ["-c", str(c_src), "-o", str(obj)], check=True)
        dis = subprocess.check_output(["objdump", "-d", str(obj)], text=True)
        exe = Path(tmpdir) / f"tbaa_{label}"
        subprocess.run(
            rustc_cmd(toolchain)
            + ["--edition=2024", "-C", "opt-level=2", str(rs_src), "-C", f"link-arg={obj}", "-o", str(exe)],
            check=True,
        )
        out = subprocess.check_output([str(exe)], text=True)
        entry = {
            "gcc_flags": flags,
            "asm_tbaa": extract_disasm_fn(dis, "c_tbaa_write_read"),
            "asm_restrict": extract_disasm_fn(dis, "c_restrict_write_read"),
        }
        for line in out.strip().splitlines():
            k, v = line.split("=", 1)
            entry[k] = v
        results[label] = entry
    return results


def main():
    toolchain = "1.99.1" if shutil.which("rustup") else None
    nightly_tc = "nightly" if shutil.which("rustup") else None
    with tempfile.TemporaryDirectory() as tmpdir:
        def sub(name):
            p = Path(tmpdir) / name
            p.mkdir()
            return p
        report = {
            "gcc_version": subprocess.check_output(["gcc", "--version"], text=True).splitlines()[0],
            "rustc_version": subprocess.check_output(rustc_cmd(toolchain) + ["-Vv"], text=True).splitlines()[0],
            "setjmp_longjmp": probe_setjmp_longjmp(sub("s1"), toolchain),
            "errno_and_tls": probe_errno_and_tls(sub("s2"), toolchain, nightly_tc),
            "c_variadics": probe_c_variadics(sub("s3"), toolchain),
            "tbaa_and_restrict": probe_tbaa_and_restrict(sub("s4"), toolchain),
        }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
