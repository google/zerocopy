#![no_std]
#![allow(dead_code)]
pub const BIAS: u8 = 3;
pub trait Step { const SHIFT: u8; fn step(self) -> u8; }
impl Step for u8 {
    const SHIFT: u8 = BIAS;
    fn step(self) -> u8 { self ^ Self::SHIFT }
}
pub fn generic<T: Step>(x: T) -> u8 { x.step() }
macro_rules! make { ($name:ident, $mask:expr) => { pub fn $name(x:u8)->u8 { x ^ $mask } }; }
make!(generated, 5u8);
#[cfg(feature="flip")]
pub fn selected(x:u8)->u8 { x ^ 1 }
#[cfg(not(feature="flip"))]
pub fn selected(x:u8)->u8 { x ^ 2 }
struct Guard(u8);
impl Drop for Guard { fn drop(&mut self) { self.0 = 0; } }
pub fn root(x:u8)->u8 {
    let _guard = Guard(x);
    let mask = generated(x);
    let closure = |y:u8| y ^ mask;
    closure(generic::<u8>(selected(x)))
}
pub fn decoy(x:u8)->u8 { x ^ 9 }
