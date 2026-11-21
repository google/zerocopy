#![feature(no_core, lang_items, intrinsics, rustc_attrs, auto_traits, unboxed_closures)]
#![allow(internal_features)]
#![no_core]

// Standalone `#![no_core]` specimen executed directly by `miri` without external crates-io sysroot
// dependencies. Exercises Miri's runtime `EvalContext` vs `CompileTimeMachine` across:
// 1. Pointer-to-integer round-trip (`PointerExposeProvenance` -> `PointerWithExposedProvenance`),
// 2. Divergent `const_eval_select` (`CE1`: `0` in CTFE vs `1` in Miri runtime, both `rc == 0`),
// 3. `is_val_statically_known` (`false` in both CTFE and Miri runtime),
// 4. Optional `--cfg case_rodata_write_ub` (`CE2`: writing through `&UnsafeCell<u64>` transmuted
//    from an immutable read-only allocation triggers Miri `Undefined Behavior: writing to alloc...
//    which is read-only`).

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "sync"]
pub unsafe trait Sync {}
#[lang = "destruct"]
pub trait Destruct {}
#[lang = "tuple_trait"]
pub trait Tuple {}
#[lang = "fn_once"]
pub trait FnOnce<Args: Tuple> {
    #[lang = "fn_once_output"]
    type Output;
    extern "rust-call" fn call_once(self, args: Args) -> Self::Output;
}

impl Copy for usize {}
impl Copy for isize {}
impl Copy for u64 {}
impl Copy for bool {}
impl<T: PointeeSized> Copy for *const T {}
impl<T: PointeeSized> Copy for *mut T {}
impl<T: PointeeSized> Copy for &T {}
unsafe impl Sync for u64 {}

#[lang = "unsafe_cell"]
#[repr(transparent)]
pub struct UnsafeCell<T: PointeeSized> {
    value: T,
}

#[rustc_intrinsic]
const fn const_eval_select<ARG: Tuple, F, G, RET>(arg: ARG, called_in_const: F, called_at_rt: G) -> RET
where
    F: FnOnce<ARG, Output = RET>,
    G: FnOnce<ARG, Output = RET>;

#[rustc_intrinsic]
const fn is_val_statically_known<T: Copy>(_val: T) -> bool;

const fn ct_arm(_x: u64) -> u64 {
    0
}

fn rt_arm(_x: u64) -> u64 {
    1
}

const CT_SELECT_VAL: u64 = const_eval_select((5_u64,), ct_arm, rt_arm);
const CT_IVSK_VAL: bool = is_val_statically_known(42_usize);
static IMMUT_RODATA: u64 = 100;

#[lang = "start"]
fn start<T>(_main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    #[cfg(case_rodata_write_ub)]
    unsafe {
        // Simulates `CE2`: if an `UnsafeCell<u64>` constant were interned into immutable `.rodata`
        // (`Mutability::Not`) without per-use copying, mutating through its pointer faults in Miri.
        let cell_ptr = &raw const IMMUT_RODATA as *const UnsafeCell<u64>;
        let raw_mut = cell_ptr as *mut u64;
        *raw_mut = 999;
    }

    let local: u64 = 77;
    let p = &raw const local;
    let exposed_addr = p as usize;
    let roundtrip = exposed_addr as *const u64;
    let loaded = unsafe { *roundtrip };

    let rt_select_val = const_eval_select((5_u64,), ct_arm, rt_arm);
    let rt_ivsk_val = is_val_statically_known(42_usize);

    // Exit code encodes exact witness tuple:
    // - `10`: loaded == 77, CT_SELECT_VAL == 0, rt_select_val == 1, CT_IVSK_VAL == false, rt_ivsk_val == false (e.g. `-Zmiri-seed=1`)
    // - `11`: loaded == 77, CT_SELECT_VAL == 0, rt_select_val == 1, CT_IVSK_VAL == false, rt_ivsk_val == true  (e.g. `-Zmiri-seed=0`)
    match (loaded, CT_SELECT_VAL, rt_select_val, CT_IVSK_VAL, rt_ivsk_val) {
        (77, 0, 1, false, false) => 10,
        (77, 0, 1, false, true) => 11,
        _ => 99,
    }
}

fn main() {}
