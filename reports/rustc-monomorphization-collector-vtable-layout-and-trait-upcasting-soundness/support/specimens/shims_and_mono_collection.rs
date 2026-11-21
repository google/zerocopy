//! Specimen 2: InstanceKind shims (VTableShim, ReifyShim x3 triggers,
//! ClosureOnceShim, FnPtrShim for FnPtr and FnDef, DropGlue Some & reified None)
//! and Lazy vs Eager (-C link-dead-code=yes) mono-item collection delta.

#![feature(unsized_fn_params)]
#![allow(internal_features)]

use std::panic::Location;

pub trait ByValConsume {
    fn consume(self, x: u64) -> u64;
}

pub trait DynSpeak {
    fn speak(&self) -> u64;
    fn tracked_on_impl(&self) -> u32;
}

pub struct Payload(pub u64);

impl ByValConsume for Payload {
    #[inline(never)]
    fn consume(self, x: u64) -> u64 {
        self.0 + x
    }
}

impl DynSpeak for Payload {
    #[inline(never)]
    fn speak(&self) -> u64 {
        self.0 * 3
    }
    #[track_caller]
    #[inline(never)]
    fn tracked_on_impl(&self) -> u32 {
        Location::caller().line()
    }
}

#[track_caller]
#[inline(never)]
pub fn tracked_free(x: u64) -> u32 {
    let _ = x;
    Location::caller().line()
}

pub fn call_via_fn_trait<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 {
    f(x)
}

pub fn call_via_fnonce<F: FnOnce(u64) -> u64>(f: F, x: u64) -> u64 {
    f(x)
}

#[inline(never)]
pub fn plain_fn(x: u64) -> u64 {
    x + 11
}

pub struct CopyNoDrop(pub u64);

pub struct UnusedDrop(pub u64);
impl Drop for UnusedDrop {
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

pub trait UnusedDefaultTrait {
    fn unused_default(&self) -> u64 {
        999
    }
}
impl UnusedDefaultTrait for CopyNoDrop {}

#[allow(dead_code)]
fn dead_non_generic() -> u64 {
    12345
}

#[no_mangle]
#[inline(never)]
pub fn reify_tracked_fn() -> fn(u64) -> u32 {
    tracked_free
}

#[no_mangle]
#[inline(never)]
pub fn reify_virtual_method() -> fn(&(dyn DynSpeak + 'static)) -> u64 {
    <dyn DynSpeak + 'static as DynSpeak>::speak
}

fn main() {
    // 1. VTableShim: by-value self: Self on Box<dyn ByValConsume>
    let bx: Box<dyn ByValConsume> = Box::new(Payload(10));
    let r_vtable_shim = bx.consume(5);

    // 2. ReifyShim #1: #[track_caller] free fn -> fn pointer
    let direct_line = tracked_free(1);
    let reified_tracked = reify_tracked_fn();
    let reified_line = reified_tracked(1);

    // 3. ReifyShim #2: <dyn DynSpeak as DynSpeak>::speak -> fn pointer
    let reified_virtual = reify_virtual_method();
    let p = Payload(20);
    let dyn_ref: &(dyn DynSpeak + 'static) = &p;
    let r_virt_reify = reified_virtual(dyn_ref);

    // 4. ReifyShim #3: #[track_caller] impl method in non-#[track_caller] trait vtable
    let r_vtable_track = dyn_ref.tracked_on_impl();

    // 5. ClosureOnceShim: FnMut capturing closure invoked via FnOnce, plus Box<dyn FnOnce> (VTableShim)
    let base = 7u64;
    let mut acc = 0u64;
    let mut mut_cl = move |x: u64| {
        acc += x + base;
        acc
    };
    let _ = mut_cl(1);
    let r_cl_once = call_via_fnonce(mut_cl, 2);
    let boxed_once: Box<dyn FnOnce(u64) -> u64> = Box::new(move |x: u64| x + base);
    let r_box_once = boxed_once(3);

    // 6. FnPtrShim: both fn pointer and fn item passed to F: Fn(u64) -> u64
    let fp: fn(u64) -> u64 = plain_fn;
    let r_fnptr_shim = call_via_fn_trait(fp, 4);
    let r_fndef_shim = call_via_fn_trait(plain_fn, 5);

    // 7. DropGlue(_, None): indirect reification forces emission of no-op drop glue
    let mut nd = CopyNoDrop(42);
    let drop_noop_ptr: unsafe fn(*mut CopyNoDrop) = std::ptr::drop_in_place::<CopyNoDrop>;
    unsafe {
        drop_noop_ptr(&mut nd as *mut CopyNoDrop);
    }

    println!("vtable_shim={r_vtable_shim}");
    println!("direct_line={direct_line}");
    println!("reified_line={reified_line}");
    println!("virt_reify={r_virt_reify}");
    println!("vtable_track={r_vtable_track}");
    println!("cl_once={r_cl_once}");
    println!("box_once={r_box_once}");
    println!("fnptr={r_fnptr_shim}");
    println!("fndef={r_fndef_shim}");
}
