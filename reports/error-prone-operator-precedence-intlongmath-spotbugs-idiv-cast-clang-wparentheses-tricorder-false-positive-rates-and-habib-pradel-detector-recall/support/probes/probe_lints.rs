// Precedence and arithmetic-kind probe for rustc + Clippy (well-typed cases only).
// Build as a library crate:  src/lib.rs = this file.
#![allow(dead_code)]

pub fn c01_bitand_vs_eq(a: u32, b: u32, c: u32) -> bool { a & b == c }
pub fn c02_shl_vs_add_const_left(x: u32, y: u32) -> u32 { x << 16 + y }
pub fn c03_shl_vs_add_const_right(x: u32, y: u32) -> u32 { x << y + 16 }
pub fn c04_land_in_lor(a: bool, b: bool, c: bool) -> bool { a && b || c }
pub fn c05_bitand_in_bitor(a: u32, b: u32, c: u32) -> u32 { a & b | c }
pub fn c06_bitxor_in_bitor(a: u32, b: u32, c: u32) -> u32 { a ^ b | c }
pub fn c08_bitand_vs_shl(a: u32, b: u32, c: u32) -> u32 { a & b << c }
pub fn c09_bitand_vs_add(a: u32, b: u32, c: u32) -> u32 { a & b + c }
pub fn c10_mul_vs_add_control(a: u32, b: u32, c: u32) -> u32 { a * b + c }
pub fn c11_rem_vs_shl(a: u32, b: u32) -> u32 { a % b << 2 }
pub fn c17_idiv_cast_to_f64(i: i32, j: i32) -> f64 { (i / j) as f64 }
pub fn c17b_idiv_from_to_f64(i: i32, j: i32) -> f64 { f64::from(i / j) }
pub fn c19_imul_cast_to_i64(i: i32, j: i32) -> i64 { (i * j) as i64 }
pub fn c22_shr_vs_sub(x: u32, y: u32) -> u32 { x >> y - 1 }
pub fn c07_bitand_in_bitxor(a: u32, b: u32, c: u32) -> u32 { a & b ^ c }
pub fn c02b_shl_vs_add_const8(x: u32, y: u32) -> u32 { x << 8 + y }
