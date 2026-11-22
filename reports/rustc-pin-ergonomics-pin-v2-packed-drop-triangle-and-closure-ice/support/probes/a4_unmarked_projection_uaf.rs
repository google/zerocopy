// Part A4: explicit `&pin mut` projection through a struct that is NOT `#[pin_v2]`.
//
// `Wrapper<F>` never opted into structural pinning and (legally, in safe code) implements
// `Unpin` unconditionally. If the compiler nevertheless lets an explicit `&pin mut` pattern
// project `Pin<&mut Wrapper<F>>` to `Pin<&mut F>`, safe code can poll a self-referential
// future, move it, free its old storage, and poll it again.
//
// Expected: either the compiler rejects the pattern ("cannot project on type that is not
// `#[pin_v2]`"), or the program compiles and Miri reports a use-after-free although neither
// crate contains `unsafe`.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

/// Not `#[pin_v2]`, so a manual (safe) `Unpin` impl is permitted.
struct Wrapper<F>(F);
impl<F> Unpin for Wrapper<F> {}

fn poll_inner<F: Future>(w: &mut Wrapper<F>, cx: &mut Context<'_>) -> Poll<F::Output> {
    // `Wrapper<F>: Unpin`, so `Pin::new` is safe.
    let p: Pin<&mut Wrapper<F>> = Pin::new(w);
    // Pin projection to `Pin<&mut F>` although `F: !Unpin` and `Wrapper` never opted in.
    let &pin mut Wrapper(ref pin mut f) = p;
    f.poll(cx)
}

fn main() {
    let mut cx = Context::from_waker(Waker::noop());
    // Poll once inside a heap allocation, then move the half-polled future out and free the
    // allocation it was pinned in.
    let mut moved = {
        let mut boxed = Box::new(Wrapper(a4_selfref_future::self_ref()));
        assert!(poll_inner(&mut boxed, &mut cx).is_pending());
        *boxed
    };
    match poll_inner(&mut moved, &mut cx) {
        Poll::Ready(v) => println!("UNMARKED_PROJECTION_RESULT={v}"),
        Poll::Pending => println!("UNMARKED_PROJECTION_RESULT=pending"),
    }
}
