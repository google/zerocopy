///@ lean model check_pos(x : U32)
///@ requires h : x > 0
///@ ensures |ret| ret = x
pub unsafe fn check_pos(x: u32) -> u32 {
    unsafe {
        if x == 0 {
            std::hint::unreachable_unchecked()
        }
        x
    }
}

///@ lean spec wrapper_fail (x : U32)
///@ ensures |ret| ret.val = 0
///@ proof
///@   intros
///@   simp [wrapper_fail]
pub fn wrapper_fail(x: u32) -> u32 {
    // VIOLATION: Calling check_pos(0) when it requires x > 0
    // This should fail to prove because the shim panics (Result.fail)
    // while the spec expects a return value.
    unsafe { check_pos(0) }
}

fn main() {}
