// A captured `Pin<&mut T>` polled inside a `poll_fn` closure (rust-lang/rust issue 154782).
#![feature(pin_ergonomics)]
#![allow(incomplete_features)]
#![forbid(unsafe_code)]
#![crate_type = "lib"]

use core::pin::Pin;
use core::task::Poll;

pub fn test_idempotency<T>(mut x: Pin<&mut T>) -> impl Future + '_
where
    T: Future<Output = ()>,
{
    core::future::poll_fn(move |cx| {
        assert_eq!(x.as_mut().poll(cx), Poll::Ready(()));
        Poll::Ready(())
    })
}
