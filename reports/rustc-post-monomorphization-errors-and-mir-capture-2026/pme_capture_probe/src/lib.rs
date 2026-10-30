// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![crate_type = "lib"]
#![allow(unreachable_code, dead_code)]

/// 1. Private conditional helper (safe only when `x + y <= usize::MAX`).
fn add(x: usize, y: usize) -> usize {
    x + y
}

/// 2. Public guarded caller establishing `x <= 1000` before calling `add(x, x)`.
pub fn double_bounded(x: usize) -> usize {
    if x <= 1000 { add(x, x) } else { 0 }
}

/// 3. Generic `const` block PME (`const { assert!(N <= 1000); }`).
pub fn const_bounded_add<const N: usize>(x: usize) -> usize {
    const {
        assert!(N <= 1000);
    }
    if x <= 1000 { x + N } else { 0 }
}

/// 4a. `zerocopy`-style `transmute_ref` using inline `const { assert!(...); }`.
pub fn transmute_ref<'a, Src, Dst>(src: &'a Src) -> &'a Dst {
    const {
        assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());
        assert!(core::mem::align_of::<Src>() >= core::mem::align_of::<Dst>());
    }
    unsafe { &*(src as *const Src as *const Dst) }
}

/// 4b. `zerocopy`-style `transmute_ref` using `static_assert!` (`StaticAssert::ASSERT`).
pub fn transmute_ref_static_assert<'a, Src, Dst>(src: &'a Src) -> &'a Dst {
    trait StaticAssert {
        const ASSERT: bool;
    }
    impl<S, D> StaticAssert for (core::marker::PhantomData<S>, core::marker::PhantomData<D>) {
        const ASSERT: bool = {
            let ok = core::mem::size_of::<S>() == core::mem::size_of::<D>()
                && core::mem::align_of::<S>() >= core::mem::align_of::<D>();
            assert!(ok);
            ok
        };
    }
    assert!(<(core::marker::PhantomData<Src>, core::marker::PhantomData<Dst>) as StaticAssert>::ASSERT);
    unsafe { &*(src as *const Src as *const Dst) }
}

/// 5. Dead-branch mentioned item PME (`if false { let _ = const_bounded_add::<N>(x); }`).
pub fn dead_call_pme<const N: usize>(x: usize) -> usize {
    if false {
        let _ = const_bounded_add::<N>(x);
    }
    x
}

/// 6. Code after `return;` (CFG-unreachable in `mir_built`, no PME).
pub fn after_return_no_pme<const N: usize>(x: usize) -> usize {
    return x;
    const {
        assert!(N <= 1000);
    };
}
