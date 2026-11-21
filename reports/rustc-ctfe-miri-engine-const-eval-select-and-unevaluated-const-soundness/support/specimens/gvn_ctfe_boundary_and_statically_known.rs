#![feature(core_intrinsics, const_raw_ptr_comparison)]
#![allow(internal_features, dead_code)]

use core::hint::black_box;
use core::intrinsics::is_val_statically_known;

static STATIC_A: u64 = 111;
static STATIC_B: u64 = 222;

// 1. `guaranteed_eq` in CTFE:
// - Distinct statics strictly in-bounds -> guaranteed unequal (`Some(false)`).
// - Same static same offset -> guaranteed equal (`Some(true)`).
// - Pointers into `GlobalAlloc::Memory` (const slice allocations) -> indeterminate (`None`)
//   because const allocations may be deduplicated or duplicated across CGUs (#128775).
pub const STATIC_SAME_EQ: Option<bool> =
    (&raw const STATIC_A).guaranteed_eq(&raw const STATIC_A);
pub const STATIC_DIFF_EQ: Option<bool> =
    (&raw const STATIC_A).guaranteed_eq(&raw const STATIC_B);
pub const CONST_MEM_GUARANTEED_EQ: Option<bool> = {
    let a: &[u8] = b"hello_ctfe";
    let b: &[u8] = b"hello_ctfe";
    a.as_ptr().guaranteed_eq(b.as_ptr())
};

// 2. `is_val_statically_known` in CTFE always returns `false` (`CompileTimeMachine::call_intrinsic`).
pub const CTFE_IVSK_LITERAL: bool = is_val_statically_known(42_usize);

#[inline]
pub const fn ivsk_scalar_branch(x: usize) -> usize {
    // Sound usage: both branches compute `x * 3` (fast shift+add vs loop/mul).
    if is_val_statically_known(x) {
        (x << 1).wrapping_add(x)
    } else {
        x.wrapping_mul(3)
    }
}

#[inline]
pub fn ivsk_observable_oracle(x: usize) -> u32 {
    // Deliberately oracle-sensitive helper to measure `-O0` vs `-O3` folding of `@llvm.is.constant`.
    if is_val_statically_known(x) { 1 } else { 0 }
}

#[inline]
pub fn ivsk_non_immediate_array(arr: [u64; 4]) -> bool {
    // Non-immediate `OperandValue::Ref` lowers unconditionally to `false` in `rustc_codegen_llvm`!
    is_val_statically_known(arr)
}

#[inline(never)]
pub fn gvn_scalar_vs_ptr_probe(x: u64) -> (u64, bool, usize) {
    // Scalar `const {}` expression: GVN evaluates `Const::Unevaluated` via `DummyMachine`
    // and folds `(c + 9)` into `Const::Val(51_u64)` because it has no provenance.
    let c = const { 6_u64 * 7_u64 };
    let folded_scalar = c + 9;

    // Pointer-to-int round-trip & cross-allocation comparison: illegal in CTFE, untouched by GVN
    // (`AddressBase::Local` + `may_have_provenance`), deterministic at runtime and in Miri.
    let local_val = x.wrapping_add(1);
    let raw = &raw const local_val;
    let exposed_addr = raw.expose_provenance();
    let roundtrip = core::ptr::with_exposed_provenance::<u64>(exposed_addr);
    let rt_read = unsafe { *roundtrip };
    let cross_cmp = (&raw const STATIC_A as usize) != (&raw const STATIC_B as usize);

    (folded_scalar + rt_read - local_val, cross_cmp, exposed_addr & 0)
}

fn main() {
    let (folded, cross_cmp, zero_mask) = gvn_scalar_vs_ptr_probe(black_box(17));
    let known_const_arg = ivsk_observable_oracle(42);
    let known_opaque_arg = ivsk_observable_oracle(black_box(42));
    let non_imm = ivsk_non_immediate_array([1, 2, 3, 4]);
    let sound_ct = const { ivsk_scalar_branch(9) };
    let sound_rt = ivsk_scalar_branch(9);

    assert_eq!(STATIC_SAME_EQ, Some(true));
    assert_eq!(STATIC_DIFF_EQ, Some(false));
    assert_eq!(CONST_MEM_GUARANTEED_EQ, None);
    assert!(!CTFE_IVSK_LITERAL);
    assert_eq!(folded, 51);
    assert!(cross_cmp);
    assert_eq!(zero_mask, 0);
    assert!(!non_imm);
    assert_eq!(sound_ct, 27);
    assert_eq!(sound_rt, 27);

    println!(
        "STATIC_SAME={:?} STATIC_DIFF={:?} CONST_MEM_EQ={:?} CTFE_IVSK={} KNOWN_CONST={} KNOWN_OPAQUE={} NON_IMM={} FOLDED={}",
        STATIC_SAME_EQ,
        STATIC_DIFF_EQ,
        CONST_MEM_GUARANTEED_EQ,
        CTFE_IVSK_LITERAL,
        known_const_arg,
        known_opaque_arg,
        non_imm,
        folded
    );
}
