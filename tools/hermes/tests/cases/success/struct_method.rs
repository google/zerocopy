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

impl Point {
    ///@ lean spec move_pt (self : Point) (dx dy : u32)
    ///@ ensures |ret, self_final|
    ///@   ret = () /\ self_final.x.val = self.x.val + dx.val /\ self_final.y.val = self.y.val + dy.val
    ///@ proof
    ///@   simp [move_pt]
    ///@   linarith
    pub fn move_pt(&mut self, dx: u32, dy: u32) {
        self.x += dx;
        self.y += dy;
    }
}

fn main() {}
