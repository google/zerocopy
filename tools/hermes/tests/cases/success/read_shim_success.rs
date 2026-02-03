///@ lean spec test_read_success(p: ConstPtr U32)
///@ requires h_align : (Memory.addr p) % 4 = 0
///@ requires h_init : Memory.is_initialized p
///@ level 10
///@ proof
///@   simp_all
unsafe fn test_read_success(p: *const u32) -> u32 {
    unsafe { std::ptr::read(p) }
}

fn main() {}
