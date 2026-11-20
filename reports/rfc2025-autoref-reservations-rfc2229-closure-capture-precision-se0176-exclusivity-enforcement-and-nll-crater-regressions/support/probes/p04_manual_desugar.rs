// Expect: rejected (an explicit `&mut` bound by `let` is not a two-phase borrow).
pub fn f() {
    let mut vec: Vec<usize> = vec![1];
    let tmp0 = &mut vec;
    let tmp1 = vec.len();
    Vec::push(tmp0, tmp1);
}
