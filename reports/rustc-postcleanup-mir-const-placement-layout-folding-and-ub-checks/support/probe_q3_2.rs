// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(internal_features)]
#![feature(
    core_intrinsics,
    intrinsics,
    ub_checks,
    rustc_attrs,
    panic_internals,
    fmt_arguments_from_str,
    const_eval_select,
    decl_macro
)]

use core::hint;
use core::intrinsics;
use core::ptr::{self, NonNull};
use core::slice;
use core::ub_checks;

// Exact replica of `core::ub_checks` internals (`library/core/src/ub_checks.rs#L52-L202`)
// and `const_eval_select` (`library/core/src/intrinsics/mod.rs#L2427-L2469`).
pub mod local_ub_checks {
    use core::intrinsics::{self, const_eval_select};

    pub(crate) macro const_eval_select_macro {
        (
            @capture$([$($binders:tt)*])? { $($arg:ident : $ty:ty = $val:expr),* $(,)? } $( -> $ret:ty )? :
            if const
                $(#[$compiletime_attr:meta])* $compiletime:block
            else
                $(#[$runtime_attr:meta])* $runtime:block
        ) => {{
            #[inline]
            $(#[$runtime_attr])*
            fn runtime$(<$($binders)*>)?($($arg: $ty),*) $( -> $ret )? {
                $runtime
            }

            #[inline]
            $(#[$compiletime_attr])*
            const fn compiletime$(<$($binders)*>)?($($arg: $ty),*) $( -> $ret )? {
                $(let _ = $arg;)*
                $compiletime
            }

            const_eval_select(($($val,)*), compiletime, runtime)
        }},
        (
            @capture$([$($binders:tt)*])? { $($arg:ident : $ty:ty),* $(,)? } $( -> $ret:ty )? :
            if const
                $(#[$compiletime_attr:meta])* $compiletime:block
            else
                $(#[$runtime_attr:meta])* $runtime:block
        ) => {
            const_eval_select_macro!(
                @capture$([$($binders)*])? { $($arg : $ty = $arg),* } $(-> $ret)? :
                if const
                    $(#[$compiletime_attr])* $compiletime
                else
                    $(#[$runtime_attr])* $runtime
            )
        },
    }

    macro_rules! assert_unsafe_precondition {
        ($kind:ident, $message:expr, ($($name:ident:$ty:ty = $arg:expr),*$(,)?) => $e:expr $(,)?) => {
            {
                #[rustc_no_mir_inline]
                #[inline]
                #[rustc_nounwind]
                #[track_caller]
                const fn precondition_check($($name:$ty),*) {
                    if !$e {
                        let msg = concat!("unsafe precondition(s) violated: ", $message,
                            "\n\nThis indicates a bug in the program. \
                            This Undefined Behavior check is optional, and cannot be relied on for safety.");
                        ::core::panicking::panic_nounwind_fmt(::core::fmt::Arguments::from_str(msg), false);
                    }
                }

                if $crate::local_ub_checks::$kind() {
                    precondition_check($($arg,)*);
                }
            }
        };
    }
    pub(crate) use assert_unsafe_precondition;

    pub use intrinsics::ub_checks as check_library_ub;

    #[inline(always)]
    pub const fn check_language_ub() -> bool {
        const_eval_select_macro!(
            @capture {} -> bool:
            if const {
                false
            } else {
                !cfg!(miri)
            }
        ) && intrinsics::ub_checks()
    }

    #[inline]
    pub const fn maybe_is_aligned_and_not_null(
        ptr: *const (),
        align: usize,
        is_zst: bool,
    ) -> bool {
        const_eval_select_macro!(
            @capture { ptr: *const (), align: usize, is_zst: bool } -> bool:
            if const {
                is_zst || !ptr.is_null()
            } else {
                (ptr.addr() & (align - 1) == 0) && (is_zst || !ptr.is_null())
            }
        )
    }

    #[inline]
    pub const fn is_valid_allocation_size(size: usize, len: usize) -> bool {
        let max_len = if size == 0 { usize::MAX } else { (isize::MAX as usize) / size };
        len <= max_len
    }

    #[inline]
    pub const fn maybe_is_nonoverlapping(
        src: *const (),
        dst: *const (),
        size: usize,
        count: usize,
    ) -> bool {
        const_eval_select_macro!(
            @capture { src: *const (), dst: *const (), size: usize, count: usize } -> bool:
            if const {
                true
            } else {
                let Some(size) = size.checked_mul(count) else { return false };
                let diff = (src.addr()).abs_diff(dst.addr());
                diff >= size
            }
        )
    }
}

// ---------------------------------------------------------------------------
// Part 1: Direct pointer dereference probes (CheckAlignment / CheckNull)
// ---------------------------------------------------------------------------

pub unsafe fn probe_deref_u32(ptr: *const u32) -> u32 {
    unsafe { *ptr }
}

pub unsafe fn probe_deref_write_u32(ptr: *mut u32, val: u32) {
    unsafe { *ptr = val }
}

pub unsafe fn probe_deref_u8(ptr: *const u8) -> u8 {
    unsafe { *ptr }
}

// ---------------------------------------------------------------------------
// Part 2: Calls to sysroot `core` functions
// ---------------------------------------------------------------------------

pub unsafe fn call_slice_from_raw_parts<'a>(data: *const u32, len: usize) -> &'a [u32] {
    unsafe { slice::from_raw_parts(data, len) }
}

pub unsafe fn call_ptr_read(src: *const u32) -> u32 {
    unsafe { ptr::read(src) }
}

pub unsafe fn call_ptr_write(dst: *mut u32, src: u32) {
    unsafe { ptr::write(dst, src) }
}

pub unsafe fn call_ptr_copy_nonoverlapping(src: *const u32, dst: *mut u32, count: usize) {
    unsafe { ptr::copy_nonoverlapping(src, dst, count) }
}

pub unsafe fn call_non_null_new_unchecked(ptr: *mut u32) -> NonNull<u32> {
    unsafe { NonNull::new_unchecked(ptr) }
}

pub unsafe fn call_unreachable_unchecked() -> ! {
    unsafe { hint::unreachable_unchecked() }
}

pub unsafe fn call_u32_unchecked_add(a: u32, b: u32) -> u32 {
    unsafe { a.unchecked_add(b) }
}

// ---------------------------------------------------------------------------
// Part 3: Local replicas of `library/core` bodies so `mir_drops_elaborated_and_const_checked`
// (`Runtime(PostCleanup)`) is dumped for the callee bodies themselves under all 4 flag combos.
// ---------------------------------------------------------------------------

pub const unsafe fn body_slice_from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T] {
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "slice::from_raw_parts requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`",
        (
            data: *const () = data as *const (),
            size: usize = size_of::<T>(),
            align: usize = align_of::<T>(),
            len: usize = len,
        ) =>
        local_ub_checks::maybe_is_aligned_and_not_null(data, align, false)
            && local_ub_checks::is_valid_allocation_size(size, len)
    );
    unsafe { &*ptr::slice_from_raw_parts(data, len) }
}

#[rustc_do_not_const_check]
pub const unsafe fn body_ptr_read<T>(src: *const T) -> T {
    #[cfg(debug_assertions)]
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "ptr::read requires that the pointer argument is aligned and non-null",
        (
            addr: *const () = src as *const (),
            align: usize = align_of::<T>(),
            is_zst: bool = size_of::<T>() == 0,
        ) => local_ub_checks::maybe_is_aligned_and_not_null(addr, align, is_zst)
    );
    unsafe { intrinsics::read_via_copy(src) }
}

#[rustc_do_not_const_check]
pub const unsafe fn body_ptr_write<T>(dst: *mut T, src: T) {
    #[cfg(debug_assertions)]
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "ptr::write requires that the destination pointer is aligned and non-null",
        (
            addr: *const () = dst as *const (),
            align: usize = align_of::<T>(),
            is_zst: bool = size_of::<T>() == 0,
        ) => local_ub_checks::maybe_is_aligned_and_not_null(addr, align, is_zst)
    );
    unsafe { intrinsics::write_via_move(dst, src) }
}

#[rustc_do_not_const_check]
pub const unsafe fn body_ptr_copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap",
        (
            src: *const () = src as *const (),
            dst: *const () = dst as *const (),
            size: usize = size_of::<T>(),
            align: usize = align_of::<T>(),
            count: usize = count,
        ) => {
            let zero_size = count == 0 || size == 0;
            local_ub_checks::maybe_is_aligned_and_not_null(src, align, zero_size)
                && local_ub_checks::maybe_is_aligned_and_not_null(dst, align, zero_size)
                && local_ub_checks::maybe_is_nonoverlapping(src, dst, size, count)
        }
    );
    unsafe { intrinsics::copy_nonoverlapping(src, dst, count) }
}

#[rustc_do_not_const_check]
pub const unsafe fn body_non_null_new_unchecked<T>(ptr: *mut T) -> NonNull<T> {
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "NonNull::new_unchecked requires that the pointer is non-null",
        (ptr: *mut () = ptr as *mut ()) => !ptr.is_null()
    );
    unsafe { core::mem::transmute(ptr) }
}

pub const unsafe fn body_unreachable_unchecked() -> ! {
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "hint::unreachable_unchecked must never be reached",
        () => false
    );
    unsafe { intrinsics::unreachable() }
}

pub const unsafe fn body_u32_unchecked_add(lhs: u32, rhs: u32) -> u32 {
    local_ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "`u32::unchecked_add` cannot overflow",
        (lhs: u32 = lhs, rhs: u32 = rhs) => !lhs.overflowing_add(rhs).1,
    );
    unsafe { intrinsics::unchecked_add(lhs, rhs) }
}

// Direct `core::ub_checks::assert_unsafe_precondition!(check_library_ub, ...)` in user/library code,
// which directly calls `core::ub_checks::check_library_ub()` (= `intrinsics::ub_checks()`) and lowers
// to `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` in the caller's own `Runtime(PostCleanup)` MIR!
pub const unsafe fn body_check_library_ub(x: u32) -> u32 {
    ub_checks::assert_unsafe_precondition!(
        check_library_ub,
        "x must be non-zero",
        (x: u32 = x) => x != 0,
    );
    x
}

// Direct check of `intrinsics::ub_checks()` and `intrinsics::overflow_checks()`
// (Note: `contract_checks` is rejected by `check_intrinsic_type` E0093 in 1.98/1.101.)
pub const fn body_runtime_checks_intrinsics() -> (bool, bool) {
    (
        intrinsics::ub_checks(),
        intrinsics::overflow_checks(),
    )
}
