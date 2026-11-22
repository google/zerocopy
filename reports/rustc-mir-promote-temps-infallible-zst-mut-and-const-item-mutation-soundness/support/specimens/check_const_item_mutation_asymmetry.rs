use std::sync::atomic::{AtomicU32, Ordering};

static OBSERVED_DROPS: AtomicU32 = AtomicU32::new(0);

struct DropLogger {
    val: u32,
}

impl DropLogger {
    fn set(&mut self, v: u32) {
        self.val = v;
    }
}

impl Drop for DropLogger {
    fn drop(&mut self) {
        OBSERVED_DROPS.fetch_add(self.val, Ordering::SeqCst);
    }
}

struct PlainVal {
    val: u32,
}

struct PtrWrap {
    ptr: *mut u32,
}

const C_DIRECT: DropLogger = DropLogger { val: 0 };
const C_NODROP: PlainVal = PlainVal { val: 0 };

#[inline(never)]
pub fn demo_const_mutation_paths(sink: &mut u32) {
    C_DIRECT.val = 10;
    C_DIRECT.set(15);
    C_DIRECT.val = 50;
    C_NODROP.val = 99;
    let c_ptr = PtrWrap { ptr: sink as *mut u32 };
    unsafe {
        *c_ptr.ptr = 7;
    }
}

fn main() {
    let mut local_sink = 0u32;
    demo_const_mutation_paths(&mut local_sink);
    println!("OBSERVED_DROPS={}", OBSERVED_DROPS.load(Ordering::SeqCst));
}
