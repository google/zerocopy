///@ lean model safe_div(a b : U32)
///@ requires h : b > 0
///@ ensures |ret| ret.val = a.val / b.val
pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
    unsafe { a / b }
}

///@ lean spec wrapper (a : U32)
///@ ensures |ret| ret.val = a.val
///@ proof
///@   simp [wrapper]
///@   -- The "correct" precondition for safe_div is met: 1 > 0
///@   have h : 1 > 0 := by native_decide
///@   have h_one : 1#u32 = 1 := by simp [OfNat.ofNat, U32.ofNat, UScalar.ofNat, UScalar.ofNatCore]; try rfl
///@   rw [h_one]
///@   have ⟨ ret, h_call ⟩ := safe_div_spec a 1 h
///@   simp [h_call.1]
///@   have h_val := h_call.2
///@   have h_one_bv : (1 : U32).bv.toNat = 1 := by native_decide
///@   dsimp [UScalar.val, UScalar.ofNat, UScalar.ofNatCore, UScalar.mk] at h_val
///@   rw [h_one_bv] at h_val
///@   rw [Nat.div_one] at h_val
///@   cases ret; cases a
///@   congr
///@   apply BitVec.eq_of_toNat_eq
///@   rw [h_val]
pub fn wrapper(a: u32) -> u32 {
    // Calling safe_div with valid input
    // The unsafe block should be removed/shimmed in shadow crate
    unsafe { safe_div(a, 1) }
}

fn main() {}
