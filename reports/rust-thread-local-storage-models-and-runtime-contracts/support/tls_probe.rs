#![feature(thread_local, cfg_target_thread_local)]
#![allow(unused, static_mut_refs)]

use std::cell::Cell;

#[cfg(target_thread_local)]
#[thread_local]
pub static mut RAW_TLS_U64: u64 = 0x1122_3344_5566_7788;

#[repr(align(64))]
pub struct Aligned64(pub [u64; 8]);

#[cfg(target_thread_local)]
#[thread_local]
pub static mut RAW_TLS_ALIGN64: Aligned64 = Aligned64([1; 8]);

pub struct HasDrop(pub u64);
impl Drop for HasDrop {
    #[inline(never)]
    fn drop(&mut self) {
        std::hint::black_box(self.0);
    }
}

thread_local! {
    pub static CONST_NODROP: Cell<u64> = const { Cell::new(42) };
    pub static CONST_DROP: Cell<HasDrop> = const { Cell::new(HasDrop(99)) };
    pub static LAZY_NODROP: Cell<u64> = Cell::new(std::hint::black_box(7));
    pub static LAZY_DROP: Cell<HasDrop> = Cell::new(HasDrop(std::hint::black_box(13)));
}

#[no_mangle]
pub fn access_all_tls() -> u64 {
    let mut sum = 0;
    #[cfg(target_thread_local)]
    unsafe {
        RAW_TLS_U64 += 1;
        sum += RAW_TLS_U64 + RAW_TLS_ALIGN64.0[0];
    }
    sum += CONST_NODROP.get();
    CONST_DROP.with(|c| sum += unsafe { (*c.as_ptr()).0 });
    sum += LAZY_NODROP.get();
    LAZY_DROP.with(|c| sum += unsafe { (*c.as_ptr()).0 });
    sum
}
