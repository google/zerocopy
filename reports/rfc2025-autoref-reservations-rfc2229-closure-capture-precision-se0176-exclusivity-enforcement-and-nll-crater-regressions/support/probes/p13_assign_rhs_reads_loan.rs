// Assignment whose right-hand side reads through the last loan of the assigned place.
// Expect: accepted. The RHS is evaluated into a temporary before the write, and the loan is dead at the write.
pub fn shared() -> i32 {
    let mut x = 1;
    let r = &x;
    x = *r + 1;
    x
}
pub fn unique() -> i32 {
    let mut x = 1;
    let r = &mut x;
    x = *r + 1;
    x
}
