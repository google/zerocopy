#!/usr/bin/env cargo
//! ```cargo
//! [package]
//! name = "struct_method"
//! version = "0.1.0"
//! edition = "2021"
//! 
//! [dependencies]
//! ```

pub struct Point {
    pub x: u32,
    pub y: u32,
}

/*@ lean
<<<<<<< Updated upstream
spec move_pt (self : Point) (dx dy : U32)
: ∃ self_final, move_pt self dx dy = ok ((), self_final) ∧
  self_final.x.val = self.x.val + dx.val ∧
  self_final.y.val = self.y.val + dy.val
@*/
/*@ proof
  sorry
=======
spec move_pt (self : Point) (dx dy : u32)
ensures |ret, self_final|
  ret = () /\ self_final.x.val = self.x.val + dx.val /\ self_final.y.val = self.y.val + dy.val
@*/
/*@ proof
:= by
  simp [move_pt]
  simp [nop_div_pt] -- Aeneas might generate different names?
  linarith
>>>>>>> Stashed changes
@*/
impl Point {
    pub fn move_pt(&mut self, dx: u32, dy: u32) {
        self.x += dx;
        self.y += dy;
    }
}
fn main() {}
