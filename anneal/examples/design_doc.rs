/// ```lean, anneal, unsafe(axiom)
/// axiom spec (a b : Std.U32) (h_req : b.val > 0) :
///   Aeneas.Std.WP.spec (safe_div a b) (fun ret_ => ret_.val = a.val / b.val)
/// ```
#[allow(unused_unsafe)]
pub unsafe fn safe_div(a: u32, b: u32) -> u32 {
    unsafe { a / b }
}

/// ```lean, anneal, spec
/// theorem spec (a : Std.U32) :
///   Aeneas.Std.WP.spec (wrapper a) (fun ret_ => ret_.val = a.val) := by
///   sorry
/// ```
pub fn wrapper(a: u32) -> u32 {
    unsafe { safe_div(a, 1) }
}

/// ```lean, anneal
/// def isValid (self : Even) : Prop := self.x.val % 2 = 0
/// ```
pub struct Even {
    #[allow(dead_code)]
    x: usize,
}

/// ```lean, anneal
/// def isSafe {Self : Type} : Prop := True
/// ```
pub unsafe trait FromBytes {}

/// ```lean, anneal, spec
/// theorem spec (x : Std.U32) :
///   Aeneas.Std.WP.spec (read_val x) (fun ret_ => ret_.val = x.val) := by
///   unfold read_val
///   simp_all
/// ```
pub fn read_val(x: &u32) -> u32 {
    *x
}

/// ```lean, anneal, spec
/// theorem spec (x : Std.U32) (add : Std.U32) (h_req : x.val + add.val ≤ 4294967295) :
///   Aeneas.Std.WP.spec (add_in_place x add) (fun ret_ => ret_.val = x.val + add.val) := by
///   sorry
/// ```
pub unsafe fn add_in_place(x: &mut u32, add: u32) {
    *x += add;
}

/// ```lean, anneal, spec
/// theorem spec (stack : alloc.vec.Vec Std.U32) (h_req : stack.length > 0#usize) :
///   Aeneas.Std.WP.spec (pop stack) (fun ret_ =>
///     let (ret, stack') := ret_
///     stack'.length = stack.length - 1#usize) := by
///   sorry
/// ```
pub unsafe fn pop(stack: &mut Vec<u32>) -> u32 {
    stack.pop().unwrap()
}

fn main() {}
