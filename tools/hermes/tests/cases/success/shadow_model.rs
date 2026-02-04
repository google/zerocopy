///@ lean model safe_div(a b : U32)
///@ requires h : b > 0
///@ ensures |ret| ret.val = a.val / b.val
pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
    unsafe { a / b }
}

///@ lean spec wrapper (a : U32)
///@ ensures |ret| ret.val = a.val
///@ proof
///@   rw [wrapper]
///@   have ⟨ ret, h ⟩ := safe_div_spec a 1#u32 (by simp) (by simp) (by native_decide)
///@   simp [h.1]
///@   simp_all [Nat.div_one, h.2]
pub fn wrapper(a: u32) -> u32 {
    // Calling safe_div with valid input
    // The unsafe block should be removed/shimmed in shadow crate
    unsafe { safe_div(a, 1) }
}

fn main() {}
