// Part A5 (compiled to LLVM IR, not run): which functions the drop glue of a type that
// implements only `Drop::pin_drop` calls. The driver searches the IR for the call comments
// `<a5_drop_glue_forwarding::OnlyPinDrop as core::ops::drop::Drop>::drop` and `...::pin_drop`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[pin_v2]
pub struct OnlyPinDrop(pub u32);

impl Drop for OnlyPinDrop {
    fn pin_drop(&pin mut self) {
        std::hint::black_box(self.0);
    }
}

pub fn consume(x: OnlyPinDrop) {
    drop(x)
}
