// Helper crate for Part A4, compiled WITHOUT `feature(pin_ergonomics)`: an ordinary
// compiler-generated self-referential future (`r` borrows `data` across the suspension point).
#![forbid(unsafe_code)]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct YieldOnce(bool);

impl Future for YieldOnce {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            Poll::Pending
        }
    }
}

pub fn self_ref() -> impl Future<Output = u8> {
    async {
        let data = [7u8; 32];
        let r = &data;
        YieldOnce(false).await;
        r[0]
    }
}
