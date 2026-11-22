// A by-value `Pin<&mut Self>` method call on a pinned reference inside a closure.
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

pub fn f<F: Future>(fut: Pin<&mut F>, cx: &mut Context<'_>) -> Poll<F::Output> {
    let c = |q: Pin<&mut F>, cx: &mut Context<'_>| q.poll(cx);
    c(fut, cx)
}
