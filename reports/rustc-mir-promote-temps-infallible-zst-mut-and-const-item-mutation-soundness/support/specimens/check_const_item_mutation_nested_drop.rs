use std::sync::atomic::{AtomicU32, Ordering};

static NESTED_DROPS: AtomicU32 = AtomicU32::new(0);

struct Inner {
    val: u32,
}

impl Drop for Inner {
    fn drop(&mut self) {
        NESTED_DROPS.fetch_add(self.val, Ordering::SeqCst);
    }
}

struct Outer {
    inner: Inner,
}

impl Outer {
    fn set_inner(&mut self, v: u32) {
        self.inner.val = v;
    }
}

const O: Outer = Outer { inner: Inner { val: 0 } };

fn main() {
    O.inner.val = 42;
    O.set_inner(1);
    println!("NESTED_DROPS={}", NESTED_DROPS.load(Ordering::SeqCst));
}
