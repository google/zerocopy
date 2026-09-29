#![allow(dead_code)]
#[derive(Clone, Copy)]
pub struct Wrap(pub u32);
pub trait Bump { fn bump(self) -> u32; }
impl Bump for Wrap { fn bump(self) -> u32 { self.0.wrapping_add(1) } }
pub fn step(x: u32) -> u32 { x.wrapping_add(2) }
pub fn use_step(x: u32) -> u32 { step(x) }
pub fn use_bump(x: Wrap) -> u32 { x.bump() }
pub fn even(n: u32) -> bool { if n == 0 { true } else { odd(n - 1) } }
pub fn odd(n: u32) -> bool { if n == 0 { false } else { even(n - 1) } }
