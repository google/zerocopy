#![no_std]
#![allow(dead_code, unused_variables, unconditional_panic)]

// 1. Direct `if false { const { ... } }` vs. `if b { const { ... } }`
pub fn case1a_if_false_const_assert<T>() {
    if false {
        const { assert!(core::mem::size_of::<T>() == 8) };
    }
}

pub fn case1b_if_b_const_assert<T>(b: bool) {
    if b {
        const { assert!(core::mem::size_of::<T>() == 8) };
    }
}

// 2. Callee with PME under `if false` vs. `if b`
fn callee_with_pme<T>() {
    const { assert!(core::mem::size_of::<T>() == 8) };
}

pub fn case2a_if_false_callee_pme<T>() {
    if false {
        callee_with_pme::<T>();
    }
}

pub fn case2b_if_b_callee_pme<T>(b: bool) {
    if b {
        callee_with_pme::<T>();
    }
}

pub unsafe fn case2c_caller_branch_callee_transmute<T: Copy>(b: bool, x: T) -> u64 {
    if b {
        callee_with_pme::<T>();
    }
    unsafe { core::mem::transmute_copy(&x) }
}

pub unsafe fn case2d_sneaky_branch_const_transmute<T: Copy>(b: bool, x: T) -> u64 {
    if b {
        const { assert!(core::mem::size_of::<T>() == 8) };
    }
    unsafe { core::mem::transmute_copy(&x) }
}

// 3. Dead local assignment `let _ = const { ... };`
pub fn case3a_generic_dead_local_const_assign<T>() {
    let _ = const { assert!(core::mem::size_of::<T>() == 4) };
}

// 3b. The exact `canary_concrete_mismatched_pme_rejected` pattern
trait SizeEq<Src, Dst> {
    const ASSERT: ();
}
impl<Src, Dst> SizeEq<Src, Dst> for () {
    const ASSERT: () = assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>());
}
fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst {
    let () = <() as SizeEq<Src, Dst>>::ASSERT;
    unsafe { core::mem::transmute_copy(&x) }
}
pub fn case3b_concrete_mismatched_caller(x: usize) -> bool {
    transmute_checked::<usize, bool>(x)
}
pub fn case3d_if_false_concrete_assoc_const() {
    if false {
        let _ = <() as SizeEq<u64, u32>>::ASSERT;
    }
}
pub fn case3e_if_false_concrete_inline_const() {
    if false {
        let _ = const { assert!(core::mem::size_of::<u64>() == 4) };
    }
}

// 4. Constructs where `Body::required_consts` at `Runtime(PostCleanup)` is NOT
// emitted as `Stmt::EvalConst` by `extract.rs`:
// 4a. Promoted borrow of a `()` constant (`&const { () }`)
pub fn case4a_promoted_unit_const() {
    let _r: &() = &const { () };
}

// 4b. Unit `const` block passed directly as a call argument `eat_unit(const { () })`
fn eat_unit(_u: ()) {}
pub fn case4b_const_as_call_arg() {
    eat_unit(const { () });
}

// 4c. Unit `const` block inside a tuple aggregate `(const { () }, 1usize)`
pub fn case4c_const_in_aggregate() -> usize {
    let t = (const { () }, 1usize);
    t.1
}

// 4d. Value-producing `const { 8usize }`
pub fn case4d_value_const() -> usize {
    const { core::mem::size_of::<usize>() }
}
