#![allow(dead_code, unused_variables, internal_features)]
#![feature(core_intrinsics)]

// ============================================================================
// Structs with different representations
// ============================================================================

pub struct ReprRust {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
pub struct ReprC {
    pub a: u32,
    pub b: u32,
}

#[repr(transparent)]
pub struct TransparentWrap(pub usize);

#[repr(C)]
pub struct NestedC {
    pub tag: u32,
    pub inner: ReprC,
}

// ============================================================================
// Deliverable 1: Value-producing `const { ... }` blocks, named `const` items,
// and associated constants
// ============================================================================

pub const FREE_LIT: usize = 42;
pub const FREE_COMP: usize = 40 + 2;
pub const FREE_SIZE_OF_RUST: usize = core::mem::size_of::<ReprRust>();

pub trait HasSize<T> {
    const SIZE: usize;
    const IS_EIGHT: bool;
}

impl<T> HasSize<T> for () {
    const SIZE: usize = core::mem::size_of::<T>();
    const IS_EIGHT: bool = core::mem::size_of::<T>() == 8;
}

pub trait SelfSized {
    const SELF_SIZE: usize;
}

impl SelfSized for ReprRust {
    const SELF_SIZE: usize = core::mem::size_of::<Self>();
}

// 1a: `const { usize::BITS }` (references core::num::<impl usize>::BITS)
pub fn d1_const_usize_bits() -> u32 {
    const { usize::BITS }
}

// 1b: Pure literal in `const { 42usize }` vs arithmetic `const { 40usize + 2 }`
pub fn d1_const_lit_block() -> usize {
    const { 42usize }
}

pub fn d1_const_arith_block() -> usize {
    const { 40usize + 2 }
}

// 1c: Generic `const { core::mem::size_of::<T>() }` (captures outer type param T)
pub fn d1_const_generic_size_of<T>() -> usize {
    const { core::mem::size_of::<T>() }
}

// 1d: Generic with 2 outer type params `fn<A, B>()` where `const` block uses `B`
pub fn d1_const_generic_two_params<A, B>() -> usize {
    const { core::mem::size_of::<B>() }
}

// 1e: Generic boolean `const { core::mem::size_of::<T>() == 8 }`
pub fn d1_const_generic_eq_eight<T>() -> bool {
    const { core::mem::size_of::<T>() == 8 }
}

// 1f: Concrete `#[repr(Rust)]` boolean `const { core::mem::size_of::<ReprRust>() == 8 }`
pub fn d1_const_repr_rust_eq_eight() -> bool {
    const { core::mem::size_of::<ReprRust>() == 8 }
}

// 1g: Associated constants `<() as HasSize<T>>::SIZE`, `IS_EIGHT`, and `<ReprRust as SelfSized>::SELF_SIZE`
pub fn d1_assoc_const_generic<T>() -> usize {
    <() as HasSize<T>>::SIZE
}

pub fn d1_assoc_const_is_eight<T>() -> bool {
    <() as HasSize<T>>::IS_EIGHT
}

pub fn d1_assoc_const_self_sized() -> usize {
    <ReprRust as SelfSized>::SELF_SIZE
}

// 1h: Named free constants
pub fn d1_use_free_consts() -> usize {
    let a = FREE_LIT;
    let b = FREE_COMP;
    let c = FREE_SIZE_OF_RUST;
    a + b + c
}

// 1i: Composite return value from `const { (1u32, 2u32) }`
pub fn d1_const_composite_tuple() -> (u32, u32) {
    const { (1u32, 2u32) }
}

// 1j: `const { ... }` used inside an `if` condition or binary op
pub fn d1_const_in_branch<T>(x: usize) -> usize {
    if const { core::mem::size_of::<T>() == 8 } {
        x + const { core::mem::align_of::<T>() }
    } else {
        x
    }
}

// ============================================================================
// Deliverable 2: Pre-folded `AnonConst` array/repeat lengths
// (`[elem; size_of::<T>()]` and `[0u8; size_of::<T>()]`)
// ============================================================================

// 2a: Literal length `[0u8; 8]` (inferred local type)
pub fn d2_repeat_literal_8() -> u8 {
    let buf = [0u8; 8];
    buf[0]
}

// 2b: Constant arithmetic length `[0u8; 4 + 4]` (layout-independent non-literal)
pub fn d2_repeat_const_arith() -> u8 {
    let buf = [0u8; 4 + 4];
    buf[0]
}

// 2c: Inferred local type `let buf = [0u8; core::mem::size_of::<ReprRust>()];`
pub fn d2_repeat_inferred_size_of_rust() -> u8 {
    let buf = [0u8; core::mem::size_of::<ReprRust>()];
    buf[0]
}

// 2d: Explicit local type `let buf: [u8; core::mem::size_of::<ReprRust>()] = [0u8; 8];`
pub fn d2_local_ty_explicit_size_of_rust() -> u8 {
    let buf: [u8; core::mem::size_of::<ReprRust>()] = [0u8; 8];
    buf[0]
}

// 2e: Function parameter `&[u8; core::mem::size_of::<ReprRust>()]` and `transmute_copy`
pub fn d2_arg_ref_array_size_of_rust(b: &[u8; core::mem::size_of::<ReprRust>()]) -> ReprRust {
    unsafe { core::mem::transmute_copy(b) }
}

// 2f: Inferred local `let buf = [0u8; core::mem::size_of::<ReprRust>()];` passed via `&buf` to `transmute_copy`
pub fn d2_local_buf_transmute_to_rust() -> ReprRust {
    let buf = [0u8; core::mem::size_of::<ReprRust>()];
    unsafe { core::mem::transmute_copy(&buf) }
}

// 2g: Return type `[u8; core::mem::size_of::<ReprC>()]`
pub fn d2_ret_array_size_of_c(x: ReprC) -> [u8; core::mem::size_of::<ReprC>()] {
    unsafe { core::mem::transmute_copy(&x) }
}

// 2h: Unsupported layout-dependent expression `[0u8; core::mem::size_of::<ReprRust>() + 1]`
// (Must fail closed!)
pub fn d2_repeat_unsupported_layout_expr() -> u8 {
    let buf = [0u8; core::mem::size_of::<ReprRust>() + 1];
    buf[0]
}

// ============================================================================
// Deliverable 3: `offset_of!` (`LayoutQuery::OffsetOf`) and `UbChecks`
// ============================================================================

// 3a: Single-field `offset_of!(ReprC, b)`
pub fn d3_offset_of_repr_c() -> usize {
    core::mem::offset_of!(ReprC, b)
}

// 3b: Single-field `offset_of!(ReprRust, b)`
pub fn d3_offset_of_repr_rust() -> usize {
    core::mem::offset_of!(ReprRust, b)
}

// 3c: Nested `offset_of!(NestedC, inner.b)`
pub fn d3_offset_of_nested_c() -> usize {
    core::mem::offset_of!(NestedC, inner.b)
}

// 3d: Tuple-struct `offset_of!(TransparentWrap, 0)`
pub fn d3_offset_of_transparent() -> usize {
    core::mem::offset_of!(TransparentWrap, 0)
}

// 3e: `UbChecks` (`core::intrinsics::ub_checks()` lowered to `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`)
pub unsafe fn d3_ub_checks_intrinsic(src: *const u8, dst: *mut u8, count: usize) -> bool {
    let chk = core::intrinsics::ub_checks();
    unsafe {
        core::intrinsics::copy_nonoverlapping(src, dst, count);
    }
    chk
}
