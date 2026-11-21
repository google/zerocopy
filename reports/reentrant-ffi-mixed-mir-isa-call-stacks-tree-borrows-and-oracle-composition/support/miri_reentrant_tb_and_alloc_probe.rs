//! Standalone Miri (`-Zmiri-tree-borrows`) probe verifying:
//! 1. Reentrant FFI callback Tree Borrows protector behavior (valid child write,
//!    invalid sibling write, invalid foreign read + outer write conflict).
//! 2. Exposed vs. unexposed provenance across FFI callbacks (`expose_provenance`
//!    / `with_exposed_provenance` vs. `.addr()` unexposed stack-local guess).
//! 3. Foreign `malloc(0)` / `free` / `realloc(p, 0)` vs. Rust `GlobalAlloc`
//!    (`MiriMemoryKind::C` vs. `MiriMemoryKind::Rust` and `NonNull::dangling()`).
//!
//! Run under Miri (tested with `miri 0.1.0 (3ef0c22cdb 2026-11-11)`):
//!   MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test --lib

use std::alloc::{Layout, alloc, dealloc};
use std::ffi::c_void;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

unsafe extern "C" {
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
    fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void;
}

/// Simulates a C FFI trampoline (`extern "C"`) that receives an opaque
/// `user_data` pointer and invokes a Rust `extern "C" fn` callback.
#[inline(never)]
extern "C" fn c_trampoline(ud: *mut c_void, cb: extern "C" fn(*mut c_void)) {
    cb(ud);
}

static GLOBAL_SIBLING_PTR: AtomicPtr<u32> = AtomicPtr::new(std::ptr::null_mut());
static GLOBAL_EXPOSED_ADDR: AtomicUsize = AtomicUsize::new(0);

// ---------------------------------------------------------------------------
// 1. Reentrant callbacks and outer Rust `&mut T` FnEntry protectors
// ---------------------------------------------------------------------------

#[inline(never)]
fn outer_child_callback(x: &mut u32) -> u32 {
    extern "C" fn cb(ud: *mut c_void) {
        // Derived from `x`'s FnEntry-protected tag -> LocalAccess on `x`.
        unsafe {
            *(ud as *mut u32) = 99;
        }
    }
    let raw: *mut u32 = x;
    c_trampoline(raw.cast::<c_void>(), cb);
    *x
}

#[test]
fn ok_reentrant_callback_child_write_activates_outer_protector() {
    let mut val = 10u32;
    assert_eq!(outer_child_callback(&mut val), 99);
    assert_eq!(val, 99);
}

#[inline(never)]
fn outer_sibling_write_callback(x: &mut u32) -> u32 {
    extern "C" fn cb(_ud: *mut c_void) {
        // ForeignWrite via sibling/ancestor pointer while `x` has active FnEntry StrongProtector!
        let p = GLOBAL_SIBLING_PTR.load(Ordering::Relaxed);
        unsafe {
            *p = 77;
        }
    }
    c_trampoline(std::ptr::null_mut(), cb);
    *x
}

#[test]
fn ub_reentrant_callback_sibling_write_violates_outer_protector() {
    let mut val = 10u32;
    let root: *mut u32 = &raw mut val;
    GLOBAL_SIBLING_PTR.store(root, Ordering::Relaxed);
    unsafe {
        let _ = outer_sibling_write_callback(&mut *root);
    }
}

#[inline(never)]
fn outer_foreign_read_then_write_callback(x: &mut u32) -> u32 {
    extern "C" fn cb(_ud: *mut c_void) {
        // ForeignRead while `x` is Protected ReservedFrz(false) -> transitions to
        // Protected ReservedFrz(true) (conflicted).
        let p = GLOBAL_SIBLING_PTR.load(Ordering::Relaxed);
        let _observed = unsafe { *p };
    }
    c_trampoline(std::ptr::null_mut(), cb);
    // ChildWrite on Protected ReservedFrz(true) -> Tree Borrows UB!
    *x = 123;
    *x
}

#[test]
fn ub_reentrant_callback_foreign_read_conflicts_outer_reserved_mut() {
    let mut val = 10u32;
    let root: *mut u32 = &raw mut val;
    GLOBAL_SIBLING_PTR.store(root, Ordering::Relaxed);
    unsafe {
        let _ = outer_foreign_read_then_write_callback(&mut *root);
    }
}

#[inline(never)]
fn outer_foreign_read_without_write_callback(x: &mut u32) -> u32 {
    extern "C" fn cb(_ud: *mut c_void) {
        // ForeignRead while `x` is Protected ReservedFrz(false) -> ReservedFrz(true).
        // Because `outer` only READS `x` (never activates it to Unique), this is valid
        // under Tree Borrows (two-phase / deferred activation)!
        let p = GLOBAL_SIBLING_PTR.load(Ordering::Relaxed);
        let _observed = unsafe { *p };
    }
    c_trampoline(std::ptr::null_mut(), cb);
    *x
}

#[test]
fn ok_reentrant_callback_foreign_read_if_outer_mut_never_writes() {
    let mut val = 10u32;
    let root: *mut u32 = &raw mut val;
    GLOBAL_SIBLING_PTR.store(root, Ordering::Relaxed);
    let r = unsafe { outer_foreign_read_without_write_callback(&mut *root) };
    assert_eq!(r, 10);
}

// ---------------------------------------------------------------------------
// 2. Exposed provenance (`expose_provenance` / `with_exposed_provenance`)
//    vs. unexposed stack-local address guessing
// ---------------------------------------------------------------------------

#[inline(never)]
fn outer_exposed_child_wildcard(x: &mut u32) -> u32 {
    extern "C" fn cb(_ud: *mut c_void) {
        let addr = GLOBAL_EXPOSED_ADDR.load(Ordering::Relaxed);
        let p: *mut u32 = std::ptr::with_exposed_provenance_mut(addr);
        unsafe {
            *p = 55;
        }
    }
    let addr = (x as *mut u32).expose_provenance();
    GLOBAL_EXPOSED_ADDR.store(addr, Ordering::Relaxed);
    c_trampoline(std::ptr::null_mut(), cb);
    *x
}

#[test]
fn ok_exposed_child_wildcard_write_preserves_outer_protector() {
    let mut val = 10u32;
    assert_eq!(outer_exposed_child_wildcard(&mut val), 55);
}

#[inline(never)]
fn outer_unexposed_child_exposed_root_wildcard(x: &mut u32) -> u32 {
    extern "C" fn cb(_ud: *mut c_void) {
        let addr = GLOBAL_EXPOSED_ADDR.load(Ordering::Relaxed);
        let p: *mut u32 = std::ptr::with_exposed_provenance_mut(addr);
        // Only root (ancestor) is exposed; `x` is NOT exposed -> local_writes == 0,
        // total == 1 -> ForeignAccess -> ProtectorViolation UB!
        unsafe {
            *p = 66;
        }
    }
    c_trampoline(std::ptr::null_mut(), cb);
    *x
}

#[test]
fn ub_exposed_root_unexposed_child_wildcard_write_violates_protector() {
    let mut val = 10u32;
    let root: *mut u32 = &raw mut val;
    let addr = root.expose_provenance();
    GLOBAL_EXPOSED_ADDR.store(addr, Ordering::Relaxed);
    unsafe {
        let _ = outer_unexposed_child_exposed_root_wildcard(&mut *root);
    }
}

#[test]
fn ok_both_root_and_child_exposed_wildcard_write_either_access_optimistic() {
    let mut val = 10u32;
    let root: *mut u32 = &raw mut val;
    let _root_addr = root.expose_provenance();
    // Inside `outer_exposed_child_wildcard`, `x` is ALSO exposed (`local_writes = 1`,
    // `total = 2`), so wildcard relatedness at `x` is `EitherAccess` -> optimistic no-op!
    assert_eq!(unsafe { outer_exposed_child_wildcard(&mut *root) }, 55);
}

#[test]
fn ub_unexposed_stack_local_addr_guess_fails() {
    let secret: u32 = 0xDEAD_BEEF;
    // `.addr()` inspects the integer address WITHOUT exposing provenance!
    let guessed_addr: usize = (&raw const secret).addr();
    let forged: *const u32 = std::ptr::with_exposed_provenance(guessed_addr);
    unsafe {
        let v = std::ptr::read(forged);
        std::hint::black_box(v);
    }
}

// ---------------------------------------------------------------------------
// 3. Foreign C `malloc(0)` / `free` / `realloc` vs. Rust `GlobalAlloc`
// ---------------------------------------------------------------------------

#[test]
fn ok_c_malloc_zero_allocates_and_frees_once() {
    unsafe {
        let p = malloc(0);
        assert!(!p.is_null());
        free(p);
        // `free(NULL)` is a legal no-op in C.
        free(std::ptr::null_mut());
    }
}

#[test]
fn ub_c_malloc_zero_double_free() {
    unsafe {
        let p = malloc(0);
        free(p);
        free(p);
    }
}

#[test]
fn ub_cross_allocator_rust_alloc_freed_by_c_free() {
    unsafe {
        let layout = Layout::new::<u64>();
        let p = alloc(layout);
        assert!(!p.is_null());
        free(p.cast::<c_void>());
    }
}

#[test]
fn ub_cross_allocator_c_malloc_freed_by_rust_dealloc() {
    unsafe {
        let layout = Layout::new::<u64>();
        let p = malloc(layout.size());
        assert!(!p.is_null());
        dealloc(p.cast::<u8>(), layout);
    }
}

#[test]
fn ub_c_free_on_rust_dangling_zst_ptr() {
    unsafe {
        let p = NonNull::<u64>::dangling().as_ptr();
        free(p.cast::<c_void>());
    }
}

#[test]
fn ub_c_realloc_size_zero() {
    unsafe {
        let p = malloc(16);
        assert!(!p.is_null());
        let _ = realloc(p, 0);
    }
}
