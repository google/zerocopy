/// ```lean, anneal, unsafe(axiom)
/// requires: b.val > 0
/// ensures: ret.val = a.val / b.val
/// ```
#[allow(unused_unsafe)]
pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
    unsafe { a / b }
}

/// ```lean, anneal, spec
/// ensures: ret.val = a.val
/// proof:
///   unfold wrapper at h_returns
///   have h := safe_div.spec a 1#u32 { h_anon := by decide }
///   unfold Aeneas.Std.WP.spec at h
///   rw [h_returns] at h
///   change safe_div.Post a 1#u32 ret at h
///   rcases h with ⟨_, h_div⟩
///   change ret.val = a.val / 1 at h_div
///   simp_all [Nat.div_one]
/// proof (h_progress):
///   unfold wrapper
///   have ⟨y, hy⟩ := Aeneas.Std.WP.spec_imp_exists (safe_div.spec a 1#u32 { h_anon := by decide })
///   simp_all
/// ```
pub fn wrapper(a: u32) -> u32 {
    unsafe { safe_div(a, 1) }
}

/// ```lean, anneal
/// isValid self := self.x.val % 2 = 0
/// ```
pub struct Even {
    #[allow(dead_code)]
    x: usize,
}

/// ```lean, anneal
/// isSafe : True
/// ```
pub unsafe trait FromBytes {}

/// ```lean, anneal, spec
/// ensures: ret.val = x.val
/// proof:
///   unfold read_val at h_returns
///   simp_all
/// proof (h_progress):
///   unfold read_val
///   simp_all
/// ```
pub fn read_val(x: &u32) -> u32 {
    *x
}

/// ```lean, anneal, spec
/// requires: x.val + add.val <= 4294967295
/// ensures: x'.val = x.val + add.val
/// proof:
///   unfold add_in_place at h_returns
///   have h := Aeneas.Std.U32.add_bv_spec (x := x) (y := add) (by scalar_tac)
///   unfold Aeneas.Std.WP.spec at h
///   try unfold Aeneas.Std.WP.theta at h
///   try unfold Aeneas.Std.WP.wp_return at h
///   simp_all
/// proof (h_progress):
///   unfold add_in_place
///   try rcases h_req with ⟨_, _, _⟩
///   have h := Aeneas.Std.U32.add_bv_spec (x := x) (y := add) (by scalar_tac)
///   have ⟨y, hy⟩ := Aeneas.Std.WP.spec_imp_exists h
///   simp_all
/// ```
pub unsafe fn add_in_place(x: &mut u32, add: u32) {
    *x += add;
}

/// ```lean, anneal
/// context:
///   open alloc.vec
/// requires: stack.length > 0#usize
/// ensures(h_len): stack'.length = stack.length - 1#usize
/// ensures(h_ret): ret = stack.index _ (stack.length - 1#usize)
/// proof (h_len):
///   unfold pop at h_returns
///   have ho := Vec.pop_spec Global stack
///   simp_all
/// proof (h_ret):
///   simp_all
/// proof (h_progress):
///   unfold pop
///   have ho := Vec.pop_spec Global stack
///   sorry
/// ```
pub unsafe fn pop(stack: &mut Vec<u32>) -> u32 {
    stack.pop().unwrap()
}

fn main() {}
