// Borrowing a field of a repr(packed) struct inside a closure truncates the capture at the struct.
// Expect: rejected in edition 2021 for P (packed), accepted for Q (not packed).
#[repr(packed)]
pub struct P { a: u8, b: u8 }
pub struct Q { a: u8, b: u8 }
pub fn packed(mut p: P) {
    let r = &mut p.a;
    let c = || { let x = &p.b; *x };
    let _ = c();
    *r = 1;
}
pub fn not_packed(mut q: Q) {
    let r = &mut q.a;
    let c = || { let x = &q.b; *x };
    let _ = c();
    *r = 1;
}
