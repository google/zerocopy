#!/usr/bin/env python3
"""Executable reproducer suite for C++ ABI specifics (Itanium C++ ABI vs Rust extern "C"):
1. Non-trivial-for-calls classes (invisible reference / hidden sret) vs Rust by-value ABI,
   including CopyNonTriv (trivially move-constructible + trivially destructible yet
   non-trivial for calls!) and [[clang::trivial_abi]] ignored by GCC 15.2.0.
2. Self-referential libstdc++ std::string SSO dangling interior pointer after Rust bitwise move.
3. Member function pointers (16 B {ptr, adj}), null data-member pointer (-1 != 0),
   multiple-inheritance `this` adjustment, and vtable negative-offset layout (offset-to-top, RTTI).
4. Static-local guard variables (__cxa_guard_acquire/release), .init_array running before
   Rust main(), __cxa_atexit / __dso_handle running after Rust main(), and link-order SIOF.
5. Live cross-language C++ exceptions vs Rust panics across extern "C" and extern "C-unwind"
   (Rust Drop + C++ catch, catch_unwind foreign abort, C++ catch(...) rethrow vs swallow abort,
   C++ noexcept std::terminate, and extern "C" UB silently skipping Rust Drop).

Uses only Python 3.10+ stdlib and cleans up all temporary build artifacts via
tempfile.TemporaryDirectory().
"""

import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path


def rustc_cmd(toolchain):
    return ["rustc", f"+{toolchain}"] if toolchain else ["rustc"]


def run_subproc(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    sig_name = None
    if r.returncode < 0:
        try:
            sig_name = signal.Signals(-r.returncode).name
        except ValueError:
            sig_name = f"SIG{-r.returncode}"
    return {
        "returncode": r.returncode,
        "signal": sig_name,
        "stdout": r.stdout.strip(),
        "stderr": r.stderr.strip(),
    }


def probe_nontrivial_calls(tmpdir, toolchain):
    cpp = Path(tmpdir) / "nontriv.cpp"
    cpp.write_text(r"""
#include <cstdint>
#include <cstdio>
#include <type_traits>

struct Triv {
    uint64_t x;
};

struct NonTrivDtor {
    uint64_t x;
    ~NonTrivDtor();
};
NonTrivDtor::~NonTrivDtor() { asm volatile("" ::: "memory"); }

// Trivially move-constructible AND trivially destructible, yet non-trivial copy ctor!
// cxx's default rust::IsRelocatable<CopyNonTriv> is true, yet Itanium §3.1.1 marks it
// non-trivial for the purposes of calls!
struct CopyNonTriv {
    uint64_t x;
    CopyNonTriv(uint64_t v) : x(v) {}
    CopyNonTriv(const CopyNonTriv &o) : x(o.x) { asm volatile("" ::: "memory"); }
    CopyNonTriv(CopyNonTriv &&) = default;
    ~CopyNonTriv() = default;
};

struct [[clang::trivial_abi]] ClangTrivAbi {
    uint64_t x;
    ~ClangTrivAbi();
};
ClangTrivAbi::~ClangTrivAbi() { asm volatile("" ::: "memory"); }

static_assert(sizeof(Triv) == 8 && sizeof(NonTrivDtor) == 8 && sizeof(CopyNonTriv) == 8);
static_assert(std::is_trivially_move_constructible_v<CopyNonTriv>);
static_assert(std::is_trivially_destructible_v<CopyNonTriv>);
static_assert(!std::is_trivially_copy_constructible_v<CopyNonTriv>);

extern "C" {
Triv id_triv(Triv t) { return t; }
NonTrivDtor id_nontriv_dtor(NonTrivDtor t) { return t; }
CopyNonTriv id_copynontriv(CopyNonTriv t) { return t; }
ClangTrivAbi id_clang_triv_abi(ClangTrivAbi t) { return t; }

// Does not dereference `t` so we can observe the corrupted address passed in %rdi by Rust!
uint64_t observe_nontriv_addr(NonTrivDtor t) {
    return reinterpret_cast<uintptr_t>(&t);
}
uint64_t deref_nontriv_val(NonTrivDtor t) {
    return t.x;
}
}
""")
    obj = Path(tmpdir) / "nontriv.o"
    comp = subprocess.run(
        ["g++", "-std=c++23", "-O2", "-Wall", "-c", str(cpp), "-o", str(obj)],
        capture_output=True,
        text=True,
        check=True,
    )
    dis = subprocess.check_output(["objdump", "-d", str(obj)], text=True)

    def extract_fn(sym):
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
        return lines[:12]

    rs = Path(tmpdir) / "call_nontriv.rs"
    rs.write_text(r"""
#[repr(C)]
#[derive(Copy, Clone)]
pub struct FakeNonTriv { pub x: u64 }

unsafe extern "C" {
    fn observe_nontriv_addr(t: FakeNonTriv) -> u64;
    fn deref_nontriv_val(t: FakeNonTriv) -> u64;
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let v = FakeNonTriv { x: 0xDEAD_BEEF_CAFE_BABE };
    if mode == "crash" {
        let r = unsafe { deref_nontriv_val(v) };
        println!("val=0x{:x}", r);
    } else {
        let addr = unsafe { observe_nontriv_addr(v) };
        println!("observed_cpp_param_addr=0x{:016x}", addr);
    }
}
""")
    exe = Path(tmpdir) / "call_nontriv"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-D",
            "improper-ctypes",
            "-C",
            "opt-level=2",
            str(rs),
            "-C",
            f"link-arg={obj}",
            "-C",
            "link-arg=-lstdc++",
            "-o",
            str(exe),
        ],
        check=True,
    )
    obs = run_subproc([str(exe), "observe"])
    crash = run_subproc([str(exe), "crash"])
    return {
        "gpp_warnings": comp.stderr.strip(),
        "asm_id_triv": extract_fn("id_triv"),
        "asm_id_nontriv_dtor": extract_fn("id_nontriv_dtor"),
        "asm_id_copynontriv": extract_fn("id_copynontriv"),
        "asm_id_clang_triv_abi": extract_fn("id_clang_triv_abi"),
        "rust_call_observe": obs,
        "rust_call_deref_crash": crash,
    }


def probe_sso_self_referential_move(tmpdir, toolchain):
    cpp = Path(tmpdir) / "sso.cpp"
    cpp.write_text(r"""
#include <cstdint>
#include <cstring>
#include <new>
#include <string>

extern "C" {
size_t cxx_string_size() { return sizeof(std::string); }
size_t cxx_string_align() { return alignof(std::string); }
void cxx_string_init_short(void *slot, const char *s) {
    new (slot) std::string(s);
}
uintptr_t cxx_string_data_addr(const void *slot) {
    const auto *p = static_cast<const std::string *>(slot);
    return reinterpret_cast<uintptr_t>(p->data());
}
void cxx_string_read_bytes(const void *slot, char *out, size_t n) {
    const auto *p = static_cast<const std::string *>(slot);
    std::memcpy(out, p->data(), n);
}
}
""")
    obj = Path(tmpdir) / "sso.o"
    subprocess.run(["g++", "-std=c++23", "-O2", "-c", str(cpp), "-o", str(obj)], check=True)
    rs = Path(tmpdir) / "sso_main.rs"
    rs.write_text(r"""
use core::mem::MaybeUninit;

#[repr(C, align(8))]
struct RawCxxString([u8; 32]);

unsafe extern "C" {
    fn cxx_string_size() -> usize;
    fn cxx_string_align() -> usize;
    fn cxx_string_init_short(slot: *mut u8, s: *const u8);
    fn cxx_string_data_addr(slot: *const u8) -> usize;
    fn cxx_string_read_bytes(slot: *const u8, out: *mut u8, n: usize);
}

#[inline(never)]
fn make_and_bitwise_move() -> (Box<RawCxxString>, usize, usize) {
    let mut stack_slot = MaybeUninit::<RawCxxString>::uninit();
    let old_ptr: *mut [u8; 32] = stack_slot.as_mut_ptr().cast();
    let old_addr = old_ptr as usize;
    unsafe {
        cxx_string_init_short(old_ptr.cast(), b"hello\0".as_ptr());
        let data_before = cxx_string_data_addr(old_ptr.cast());
        // Rust bitwise memcpy move onto the heap (equivalent to passing/returning by value)
        let moved = Box::new(core::ptr::read(old_ptr.cast::<RawCxxString>()));
        // Overwrite the old stack slot (simulating stack frame reuse after return)
        core::ptr::write_volatile(old_ptr, [b'X'; 32]);
        (moved, old_addr, data_before)
    }
}

fn main() {
    unsafe {
        assert_eq!(cxx_string_size(), 32);
        assert_eq!(cxx_string_align(), 8);
        let (moved, old_addr, data_before) = make_and_bitwise_move();
        let new_addr = (&*moved as *const RawCxxString) as usize;
        let data_after = cxx_string_data_addr((&*moved as *const RawCxxString).cast());
        let mut buf = [0u8; 5];
        cxx_string_read_bytes((&*moved as *const RawCxxString).cast(), buf.as_mut_ptr(), 5);
        println!("sizeof_std_string={}", cxx_string_size());
        println!("old_slot_addr=0x{:x}", old_addr);
        println!("data_ptr_before_move=0x{:x}", data_before);
        println!("sso_interior_offset={}", data_before - old_addr);
        println!("new_slot_addr=0x{:x}", new_addr);
        println!("data_ptr_after_move=0x{:x}", data_after);
        println!("dangling_points_into_old_slot={}", data_after == data_before && data_after != new_addr + (data_before - old_addr));
        println!("corrupted_bytes_read={}", core::str::from_utf8(&buf).unwrap_or("?"));
        // Intentionally leak `moved` (not invoking ~std::string on corrupted object)
        core::mem::forget(moved);
    }
}
""")
    exe = Path(tmpdir) / "sso_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-C",
            "opt-level=2",
            str(rs),
            "-C",
            f"link-arg={obj}",
            "-C",
            "link-arg=-lstdc++",
            "-o",
            str(exe),
        ],
        check=True,
    )
    out = subprocess.check_output([str(exe)], text=True)
    res = {}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v
    return res


def probe_memptrs_vtables_mi(tmpdir):
    cpp = Path(tmpdir) / "abi_layout.cpp"
    cpp.write_text(r"""
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <typeinfo>

struct A {
    uint64_t a = 0xAA;
    virtual ~A() = default;
    virtual int va() { return 1; }
    int nonvirt_a() { return 10; }
};

struct B {
    uint64_t b = 0xBB;
    virtual ~B() = default;
    virtual int vb() { return 2; }
    int nonvirt_b() { return 20; }
};

struct D : A, B {
    uint64_t d = 0xDD;
    int va() override { return 11; }
    int vb() override { return 22; }
};

struct VBase { uint64_t v = 0x77; };
struct VDer : virtual VBase {
    uint64_t x = 0x88;
    virtual ~VDer() = default;
};

struct MemPtrBits { uint64_t ptr; int64_t adj; };

int main() {
    D d;
    B *pb = static_cast<B *>(&d);
    auto base_delta = reinterpret_cast<uintptr_t>(pb) - reinterpret_cast<uintptr_t>(&d);

    int (D::*p_nv_a)() = &A::nonvirt_a;
    int (D::*p_nv_b)() = &B::nonvirt_b;
    int (D::*p_va)() = &D::va;
    int (D::*p_vb)() = &D::vb;
    uint64_t D::*p_null_data = nullptr;
    uint64_t D::*p_field_a = &A::a;

    MemPtrBits b_nva{}, b_nvb{}, b_va{}, b_vb{};
    std::memcpy(&b_nva, &p_nv_a, sizeof(b_nva));
    std::memcpy(&b_nvb, &p_nv_b, sizeof(b_nvb));
    std::memcpy(&b_va, &p_va, sizeof(b_va));
    std::memcpy(&b_vb, &p_vb, sizeof(b_vb));
    int64_t null_data_bits = 0, field_a_bits = 0;
    std::memcpy(&null_data_bits, &p_null_data, sizeof(null_data_bits));
    std::memcpy(&field_a_bits, &p_field_a, sizeof(field_a_bits));

    // Inspect vtable of D (primary A-in-D vptr at offset 0, secondary B-in-D vptr at offset 16)
    const int64_t *vptr_primary = *reinterpret_cast<const int64_t *const *>(&d);
    const int64_t *vptr_secondary = *reinterpret_cast<const int64_t *const *>(pb);
    const auto *ti_primary = reinterpret_cast<const std::type_info *>(vptr_primary[-1]);
    const auto *ti_secondary = reinterpret_cast<const std::type_info *>(vptr_secondary[-1]);

    VDer vd;
    const int64_t *vptr_vder = *reinterpret_cast<const int64_t *const *>(&vd);
    int64_t vbase_offset = vptr_vder[-3];

    printf("sizeof_mfp=%zu\n", sizeof(p_nv_a));
    printf("sizeof_dmp=%zu\n", sizeof(p_null_data));
    printf("null_data_member_ptr_bits=%lld\n", (long long)null_data_bits);
    printf("field_a_member_ptr_bits=%lld\n", (long long)field_a_bits);
    printf("mi_D_to_B_this_shift=%zu\n", base_delta);
    printf("mfp_nonvirt_a=ptr:0x%llx,adj:%lld,is_virt_bit:%llu\n", (unsigned long long)b_nva.ptr, (long long)b_nva.adj, (unsigned long long)(b_nva.ptr & 1));
    printf("mfp_nonvirt_b=ptr:0x%llx,adj:%lld,is_virt_bit:%llu\n", (unsigned long long)b_nvb.ptr, (long long)b_nvb.adj, (unsigned long long)(b_nvb.ptr & 1));
    printf("mfp_virt_va=ptr:0x%llx,adj:%lld,vtable_byte_off:%llu\n", (unsigned long long)b_va.ptr, (long long)b_va.adj, (unsigned long long)(b_va.ptr - 1));
    printf("mfp_virt_vb=ptr:0x%llx,adj:%lld,vtable_byte_off:%llu\n", (unsigned long long)b_vb.ptr, (long long)b_vb.adj, (unsigned long long)(b_vb.ptr - 1));
    printf("vptr_primary_offset_to_top=%lld\n", (long long)vptr_primary[-2]);
    printf("vptr_secondary_offset_to_top=%lld\n", (long long)vptr_secondary[-2]);
    printf("vptr_rtti_match=%d\n", (ti_primary == ti_secondary && std::strcmp(ti_primary->name(), typeid(D).name()) == 0) ? 1 : 0);
    printf("vder_vbase_offset_at_neg3=%lld\n", (long long)vbase_offset);
    return 0;
}
""")
    exe = Path(tmpdir) / "abi_layout"
    subprocess.run(["g++", "-std=c++23", "-O2", str(cpp), "-o", str(exe)], check=True)
    out = subprocess.check_output([str(exe)], text=True)
    res = {}
    for line in out.strip().splitlines():
        k, v = line.split("=", 1)
        res[k] = v
    return res


def probe_init_array_siof_and_guards(tmpdir, toolchain):
    tu_a = Path(tmpdir) / "tu_a.cpp"
    tu_a.write_text(r"""
#include <cstdint>
#include <cstdio>

extern "C" uint32_t RUST_SHARED_GLOBAL;

struct GlobalA {
    uint32_t val;
    GlobalA() : val(100) {
        RUST_SHARED_GLOBAL += 42;
        std::printf("[init_array:GlobalA] RUST_SHARED_GLOBAL=%u\n", RUST_SHARED_GLOBAL);
        std::fflush(stdout);
    }
    ~GlobalA() {
        std::printf("[cxa_atexit:~GlobalA] running_after_rust_main\n");
        std::fflush(stdout);
    }
};

GlobalA g_a;

struct LocalStatic {
    uint32_t x;
    LocalStatic() : x(777) {}
    ~LocalStatic() {}
};

extern "C" uint32_t get_local_static() {
    static LocalStatic s;
    return s.x;
}
""")
    tu_b = Path(tmpdir) / "tu_b.cpp"
    tu_b.write_text(r"""
#include <cstdint>
#include <cstdio>

struct GlobalA { uint32_t val; GlobalA(); ~GlobalA(); };
extern GlobalA g_a;

struct GlobalB {
    uint32_t observed_a;
    GlobalB() : observed_a(g_a.val) {
        std::printf("[init_array:GlobalB] observed_g_a_val=%u\n", observed_a);
        std::fflush(stdout);
    }
};

GlobalB g_b;

extern "C" uint32_t get_siof_observed() { return g_b.observed_a; }
""")
    obj_a = Path(tmpdir) / "tu_a.o"
    obj_b = Path(tmpdir) / "tu_b.o"
    subprocess.run(["g++", "-std=c++23", "-O2", "-c", str(tu_a), "-o", str(obj_a)], check=True)
    subprocess.run(["g++", "-std=c++23", "-O2", "-c", str(tu_b), "-o", str(obj_b)], check=True)

    dis_a = subprocess.check_output(["objdump", "-d", str(obj_a)], text=True)
    rel_a = subprocess.check_output(["readelf", "-r", str(obj_a)], text=True)
    nm_a = subprocess.check_output(["nm", "-u", str(obj_a)], text=True)
    has_guard_acquire = "__cxa_guard_acquire" in nm_a
    has_guard_release = "__cxa_guard_release" in nm_a
    has_cxa_atexit = "__cxa_atexit" in nm_a
    has_dso_handle = "__dso_handle" in nm_a
    has_init_array = ".rela.init_array" in rel_a

    rs = Path(tmpdir) / "siof_main.rs"
    rs.write_text(r"""
use core::sync::atomic::{AtomicU32, Ordering};

#[unsafe(no_mangle)]
pub static RUST_SHARED_GLOBAL: AtomicU32 = AtomicU32::new(0);

unsafe extern "C" {
    fn get_siof_observed() -> u32;
    fn get_local_static() -> u32;
}

fn main() {
    unsafe {
        println!("[rust_main] RUST_SHARED_GLOBAL_at_entry={}", RUST_SHARED_GLOBAL.load(Ordering::SeqCst));
        println!("[rust_main] siof_observed={}", get_siof_observed());
        println!("[rust_main] local_static={}", get_local_static());
    }
}
""")
    exe_ab = Path(tmpdir) / "siof_ab"
    exe_ba = Path(tmpdir) / "siof_ba"
    for exe, order in [(exe_ab, [obj_a, obj_b]), (exe_ba, [obj_b, obj_a])]:
        subprocess.run(
            rustc_cmd(toolchain)
            + [
                "--edition=2024",
                "-C",
                "opt-level=2",
                str(rs),
                "-C",
                f"link-arg={order[0]}",
                "-C",
                f"link-arg={order[1]}",
                "-C",
                "link-arg=-lstdc++",
                "-o",
                str(exe),
            ],
            check=True,
        )
    out_ab = subprocess.check_output([str(exe_ab)], text=True).strip().splitlines()
    out_ba = subprocess.check_output([str(exe_ba)], text=True).strip().splitlines()
    return {
        "tu_a_has_init_array_reloc": has_init_array,
        "tu_a_has_cxa_guard_acquire": has_guard_acquire,
        "tu_a_has_cxa_guard_release": has_guard_release,
        "tu_a_has_cxa_atexit": has_cxa_atexit,
        "tu_a_has_dso_handle": has_dso_handle,
        "link_order_A_then_B": out_ab,
        "link_order_B_then_A": out_ba,
    }


def probe_cpp_exceptions_and_c_unwind(tmpdir, toolchain):
    cpp = Path(tmpdir) / "eh_cpp.cpp"
    cpp.write_text(r"""
#include <cstdint>
#include <cstdio>
#include <stdexcept>

struct CppGuard {
    uint32_t *counter;
    ~CppGuard() { (*counter)++; }
};

extern "C" {
void cpp_throw_runtime_error() {
    throw std::runtime_error("cpp_boom");
}

int cpp_try_call_rust(void (*fn)()) {
    try {
        fn();
        return 0;
    } catch (const std::runtime_error &e) {
        std::printf("cpp_caught_msg=%s\n", e.what());
        std::fflush(stdout);
        return 1;
    }
}

void cpp_rethrow_rust_panic(void (*fn)(), uint32_t *cpp_drops) {
    CppGuard g{cpp_drops};
    try {
        fn();
    } catch (...) {
        throw;
    }
}

void cpp_swallow_rust_panic(void (*fn)(), uint32_t *cpp_drops) {
    CppGuard g{cpp_drops};
    try {
        fn();
    } catch (...) {
        // Swallowing a Rust panic destroys _Unwind_Exception -> calls __rust_drop_panic!
    }
}

void cpp_noexcept_call_rust(void (*fn)()) noexcept {
    fn();
}
}
""")
    obj = Path(tmpdir) / "eh_cpp.o"
    subprocess.run(
        ["g++", "-std=c++23", "-O2", "-fexceptions", "-c", str(cpp), "-o", str(obj)],
        check=True,
    )
    rs = Path(tmpdir) / "eh_main.rs"
    rs.write_text(r"""
use std::sync::atomic::{AtomicU32, Ordering};

static RUST_DROPS: AtomicU32 = AtomicU32::new(0);

struct RustGuard;
impl Drop for RustGuard {
    fn drop(&mut self) {
        RUST_DROPS.fetch_add(1, Ordering::SeqCst);
    }
}

unsafe extern "C-unwind" {
    fn cpp_throw_runtime_error();
    fn cpp_try_call_rust(f: extern "C-unwind" fn()) -> i32;
    fn cpp_rethrow_rust_panic(f: extern "C-unwind" fn(), cpp_drops: *mut u32);
    fn cpp_swallow_rust_panic(f: extern "C-unwind" fn(), cpp_drops: *mut u32);
    fn cpp_noexcept_call_rust(f: extern "C-unwind" fn());
}

#[allow(clashing_extern_declarations)]
unsafe extern "C" {
    #[link_name = "cpp_throw_runtime_error"]
    fn cpp_throw_wrong_extern_c();
}

extern "C-unwind" fn rust_passthrough_c_unwind() {
    let _g = RustGuard;
    unsafe { cpp_throw_runtime_error(); }
}

extern "C-unwind" fn rust_passthrough_wrong_extern_c() {
    let _g = RustGuard;
    // UB! Calling throwing C++ function through `extern "C"` (nounwind, no landing pad)!
    unsafe { cpp_throw_wrong_extern_c(); }
}

extern "C-unwind" fn rust_do_panic() {
    panic!("rust_boom");
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "1_cpp_throw_through_rust_c_unwind" => {
            let caught = unsafe { cpp_try_call_rust(rust_passthrough_c_unwind) };
            println!("caught={} rust_drops={}", caught, RUST_DROPS.load(Ordering::SeqCst));
        }
        "2_cpp_throw_into_catch_unwind" => {
            let _ = std::panic::catch_unwind(|| unsafe { cpp_throw_runtime_error() });
            println!("unexpected_return");
        }
        "3_rust_panic_cpp_rethrow" => {
            let mut cpp_drops = 0u32;
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                cpp_rethrow_rust_panic(rust_do_panic, &raw mut cpp_drops);
            }));
            println!("rust_caught_err={} cpp_drops={}", res.is_err(), cpp_drops);
        }
        "4_rust_panic_cpp_swallow" => {
            let mut cpp_drops = 0u32;
            unsafe { cpp_swallow_rust_panic(rust_do_panic, &raw mut cpp_drops); }
            println!("unexpected_return cpp_drops={}", cpp_drops);
        }
        "5_rust_panic_cpp_noexcept" => {
            unsafe { cpp_noexcept_call_rust(rust_do_panic); }
            println!("unexpected_return");
        }
        "6_cpp_throw_wrong_extern_c_ub" => {
            let caught = unsafe { cpp_try_call_rust(rust_passthrough_wrong_extern_c) };
            println!("caught={} rust_drops={}", caught, RUST_DROPS.load(Ordering::SeqCst));
        }
        _ => panic!("unknown mode"),
    }
}
""")
    exe = Path(tmpdir) / "eh_main"
    subprocess.run(
        rustc_cmd(toolchain)
        + [
            "--edition=2024",
            "-C",
            "opt-level=2",
            "-C",
            "panic=unwind",
            str(rs),
            "-C",
            f"link-arg={obj}",
            "-C",
            "link-arg=-lstdc++",
            "-o",
            str(exe),
        ],
        check=True,
    )
    modes = [
        "1_cpp_throw_through_rust_c_unwind",
        "2_cpp_throw_into_catch_unwind",
        "3_rust_panic_cpp_rethrow",
        "4_rust_panic_cpp_swallow",
        "5_rust_panic_cpp_noexcept",
        "6_cpp_throw_wrong_extern_c_ub",
    ]
    return {m: run_subproc([str(exe), m]) for m in modes}


def main():
    toolchain = "1.99.1" if shutil.which("rustup") else None
    with tempfile.TemporaryDirectory() as tmpdir:
        out = {
            "gpp_version": subprocess.check_output(["g++", "--version"], text=True).splitlines()[0],
            "rustc_version": subprocess.check_output(rustc_cmd(toolchain) + ["-Vv"], text=True).splitlines()[0],
            "nontrivial_calls": probe_nontrivial_calls(Path(tmpdir) / "p1" if not os.makedirs(Path(tmpdir) / "p1") else Path(tmpdir) / "p1", toolchain),
            "sso_self_referential": probe_sso_self_referential_move(Path(tmpdir) / "p2" if not os.makedirs(Path(tmpdir) / "p2") else Path(tmpdir) / "p2", toolchain),
            "memptrs_vtables_mi": probe_memptrs_vtables_mi(Path(tmpdir) / "p3" if not os.makedirs(Path(tmpdir) / "p3") else Path(tmpdir) / "p3"),
            "init_array_siof_guards": probe_init_array_siof_and_guards(Path(tmpdir) / "p4" if not os.makedirs(Path(tmpdir) / "p4") else Path(tmpdir) / "p4", toolchain),
            "cpp_exceptions_c_unwind": probe_cpp_exceptions_and_c_unwind(Path(tmpdir) / "p5" if not os.makedirs(Path(tmpdir) / "p5") else Path(tmpdir) / "p5", toolchain),
        }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
