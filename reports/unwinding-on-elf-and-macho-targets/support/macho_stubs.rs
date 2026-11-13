#![no_std]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[no_mangle]
pub extern "C" fn rust_eh_personality() {}
#[no_mangle]
pub extern "C" fn _Unwind_Resume() -> ! { loop {} }
#[no_mangle]
pub extern "C" fn _RNvNvNtCsdnanKjkF2cC_3std9panicking12catch_unwind7cleanup() {}
#[no_mangle]
pub extern "C" fn _RNvNtCs3bJEMBXHbwl_4core9panicking19panic_cannot_unwind() -> ! { loop {} }
#[no_mangle]
pub extern "C" fn _RNvCs5fGHjzWXRav_7___rustc14___rust_dealloc() {}
