// Same as p13 but the loan is used after the assignment. Expect: rejected (E0506).
pub fn f() -> i32 {
    let mut x = 1;
    let r = &x;
    x = *r + 1;
    *r
}
