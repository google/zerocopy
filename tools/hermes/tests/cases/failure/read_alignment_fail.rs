///@ lean spec test_read_alignment_fail(p: ConstPtr U16)
///@ requires h_align : (Memory.addr p) % 2 = 0
///@ requires h_init : Memory.is_initialized p
///@ proof
///@   simp_all
unsafe fn test_read_alignment_fail(p: *const u16) -> u32 {
    let p32 = p as *const u32;
    // Should fail: u16 alignment (2) does not imply u32 alignment (4)
    unsafe { std::ptr::read(p32) }
}

fn main() {}
