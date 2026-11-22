// Control: the closure of c07 compiled WITHOUT `feature(pin_ergonomics)`.
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub fn f<F: Future>(fut: Pin<&mut F>, cx: &mut Context<'_>) -> Poll<F::Output> {
    let c = |q: Pin<&mut F>, cx: &mut Context<'_>| q.poll(cx);
    c(fut, cx)
}
