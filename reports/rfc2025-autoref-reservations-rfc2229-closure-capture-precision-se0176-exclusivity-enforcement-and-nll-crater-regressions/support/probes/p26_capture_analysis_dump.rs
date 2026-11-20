// Nightly-only: dump the capture analysis with the internal #[rustc_capture_analysis] attribute.
#![feature(rustc_attrs, stmt_expr_attributes)]
pub struct Inner { x: u32, y: u32 }
pub struct S { inner: Inner, raw: *mut u32, boxed: Box<Inner>, arr: [u32; 2], shr: &'static Inner }
pub fn f(s: S) {
    let c = #[rustc_capture_analysis] || {
        let _a = s.inner.x;          // field path
        let _b = unsafe { *s.raw };  // deref of raw pointer
        let _c = s.boxed.y;          // through Box
        let _d = s.arr[1];           // index
        let _e = s.shr.x;            // through shared reference
    };
    c();
}
