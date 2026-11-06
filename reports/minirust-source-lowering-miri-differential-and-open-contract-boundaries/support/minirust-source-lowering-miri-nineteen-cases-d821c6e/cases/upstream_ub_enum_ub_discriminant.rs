fn main() {
    unsafe {
        let x = 12u8;
        let x_ptr: *const u8 = &x;
        let cast_ptr = x_ptr as *const Option<bool>;
        // Valid values for the tag are `0..=2`; ensure we reject this one.
        let _val = matches!(*cast_ptr, None);
    }
}
