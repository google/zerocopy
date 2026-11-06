#[inline(never)] fn identity(x: *const [u8]) -> *const [u8] { x }
fn main() {
 let bytes=[11u8,22,33]; let p: *const [u8]=&bytes;
 let q=identity(p); assert!(q.len() == 3); assert!(unsafe { (&*q)[2] } == 33);
}
