// Index projections are not captured precisely: the closure captures all of `s.arr`.
// Expect: rejected in edition 2021 (E0502), while disjoint *fields* would be accepted.
pub struct S { arr: [u32; 2] }
pub fn f(mut s: S) {
    let a = &mut s.arr[0];
    let c = || s.arr[1] + 1;
    let _ = c();
    *a += 1;
}
