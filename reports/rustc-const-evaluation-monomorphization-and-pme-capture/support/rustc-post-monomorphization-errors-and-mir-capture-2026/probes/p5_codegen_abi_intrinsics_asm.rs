// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
#![cfg_attr(nightly_intrinsics, feature(repr_simd, core_intrinsics))]

#[cfg(abi_vector_no_feature)]
pub mod abi_vec {
    #[repr(simd)]
    pub struct AvxVec([f64; 4]);

    pub extern "C" fn pass_avx_by_val(x: AvxVec) -> AvxVec {
        x
    }
}

#[cfg(nightly_intrinsics)]
pub mod intrinsics_probe {
    pub enum Void {}

    pub unsafe fn bad_simd_add<T: Copy>(a: T, b: T) -> T {
        core::intrinsics::simd::simd_add(a, b)
    }

    #[cfg(call_bad_simd)]
    pub fn trigger_bad_simd() -> u32 {
        unsafe { bad_simd_add(1u32, 2u32) }
    }

    pub fn runtime_assert_inhabited<T>() {
        core::intrinsics::assert_inhabited::<T>();
    }

    #[cfg(call_runtime_uninhabited)]
    pub fn trigger_runtime_uninhabited() {
        runtime_assert_inhabited::<Void>();
    }

    pub fn const_assert_inhabited<T>() {
        const {
            core::intrinsics::assert_inhabited::<T>();
        }
    }

    #[cfg(call_const_uninhabited)]
    pub fn trigger_const_uninhabited() {
        const_assert_inhabited::<Void>();
    }
}

pub struct AsmConst<T>(core::marker::PhantomData<T>);
impl<T> AsmConst<T> {
    pub const VAL: usize = {
        assert!(core::mem::size_of::<T>() == 4);
        4
    };
}

pub unsafe fn asm_with_const<T>() {
    unsafe {
        core::arch::asm!("/* {} */", const AsmConst::<T>::VAL);
    }
}

#[cfg(call_asm_const_fail)]
pub fn trigger_asm_const_fail() {
    unsafe {
        asm_with_const::<u64>();
    }
}
