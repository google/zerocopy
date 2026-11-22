#![crate_type = "lib"]
#![feature(core_intrinsics)]
#![allow(unused, dead_code, deref_nullptr, internal_features)]

//! Empirical MIR phase-separation and unwind-metadata probes comparing
//! `MirPhase::Runtime(RuntimePhase::PostCleanup)` against
//! `MirPhase::Runtime(RuntimePhase::Optimized)` (the phase returned by
//! `TyCtxt::instance_mir` and consumed by `rustc_public`).

pub unsafe fn probe_zst_deref(p: *mut ()) {
    unsafe {
        let _x: () = *p;
        *p = ();
    }
}

pub unsafe fn probe_div_zero_unchecked(x: u32) -> u32 {
    unsafe { core::intrinsics::unchecked_div(0u32, x) }
}

pub fn probe_div_zero_checked(x: u32) -> u32 {
    0u32 / x
}

pub unsafe fn probe_place_mention(p: *const u32) {
    unsafe {
        let _ = *p;
    }
}

pub fn probe_storage_markers(x: u32) -> u32 {
    let a = {
        let tmp = x.wrapping_add(1);
        tmp.wrapping_mul(3)
    };
    let b = {
        let tmp2 = a.wrapping_add(7);
        tmp2 ^ 0x55
    };
    b
}

pub unsafe fn probe_unreachable_prop(p: *const u32, flag: bool) -> u32 {
    if flag {
        unsafe {
            let v = *p;
            let _ = v.wrapping_add(1);
            core::hint::unreachable_unchecked()
        }
    } else {
        42
    }
}

pub struct Guard(pub u32);

impl Drop for Guard {
    fn drop(&mut self) {
        if self.0 == 0 {
            panic!("double panic in drop");
        }
    }
}

pub fn probe_unwind_cleanup(x: u32) {
    let _g = Guard(x);
    if x == 1 {
        panic!("normal panic");
    }
}

pub extern "C" fn probe_unwind_abi_terminate(x: u32) -> u32 {
    if x == 0 {
        panic!("cannot unwind across extern C");
    }
    x
}
