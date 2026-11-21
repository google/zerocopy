#![feature(used_with_arg)]
#![allow(dead_code)]

use std::sync::atomic::{AtomicU64, Ordering};

static CTOR_LOG: AtomicU64 = AtomicU64::new(0);

#[link_section = ".custom_plain"]
static PLAIN_UNUSED: u64 = 0x1010_2020_3030_4040;

#[used(compiler)]
#[link_section = ".custom_comp"]
#[no_mangle]
static USED_COMP: u64 = 0xAAAA_BBBB_CCCC_DDDD;

#[used(linker)]
#[link_section = ".custom_link"]
#[no_mangle]
static USED_LINK: u64 = 0x1111_2222_3333_4444;

#[used]
#[link_section = ".custom_bare"]
#[no_mangle]
static USED_BARE: u64 = 0x5555_6666_7777_8888;

#[inline(never)]
unsafe extern "C" fn pre_main_ctor() {
    CTOR_LOG.store(0xC070_0000_0000_0001, Ordering::SeqCst);
}

#[used(linker)]
#[link_section = ".init_array"]
#[no_mangle]
static INIT_ARRAY_CTOR: unsafe extern "C" fn() = pre_main_ctor;

fn main() {
    let observed = CTOR_LOG.load(Ordering::SeqCst);
    println!("CTOR_OBSERVED=0x{:x}", observed);
    assert_eq!(observed, 0xC070_0000_0000_0001);
}
