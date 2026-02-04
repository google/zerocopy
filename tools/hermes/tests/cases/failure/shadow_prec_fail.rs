///@ lean model must_be_ten(x : U32)
///@ requires h : x == 10
///@ ensures |ret| ret.val = 10
pub unsafe fn must_be_ten(x: u32) -> u32 {
    x
}

///@ lean spec prec_trap (x : U32)
///@ requires x.val > 10
///@ ensures |ret| ret.val = 10
///@ proof
///@   intros
///@   simp [prec_trap]
pub fn prec_trap(x: u32) -> u32 {
    // TRAP: x > 10 does not imply x = 10
    // We satisfy *a* condition (x > 10), but not the *required* one (x = 10)
    // Verification should fail.
    unsafe { must_be_ten(x) }
}

fn main() {}
