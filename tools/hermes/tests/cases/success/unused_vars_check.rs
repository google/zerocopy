#![deny(unused_variables)]

///@ lean model unused_vars_test
///@ requires true
#[deny(unused_variables)]
pub unsafe fn unused_vars_test(x: i32) {
    unsafe {
        // Real body uses x
        let _ = x;
    }
}

pub fn main() {
    unsafe {
        unused_vars_test(42);
    }
}
