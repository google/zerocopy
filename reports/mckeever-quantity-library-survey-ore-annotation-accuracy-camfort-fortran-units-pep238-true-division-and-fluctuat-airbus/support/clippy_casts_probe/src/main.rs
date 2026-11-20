// Each function exercises one numeric-cast lint family from clippy_lints/src/casts/.
#![warn(
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_lossless,
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap
)]

fn truncation(x: u64) -> u8 { x as u8 }                 // cast_possible_truncation
fn float_to_int(x: f64) -> i32 { x as i32 }             // cast_possible_truncation (float -> int)
fn f64_to_f32(x: f64) -> f32 { x as f32 }               // cast_possible_truncation (f64 -> f32)
fn precision_i32_f32(x: i32) -> f32 { x as f32 }        // cast_precision_loss (32 >= 32)
fn precision_i64_f64(x: i64) -> f64 { x as f64 }        // cast_precision_loss (64 >= 64)
fn exact_i32_f64(x: i32) -> f64 { x as f64 }          // cast_lossless (exact; From exists)
fn lossless(x: u8) -> u64 { x as u64 }                  // cast_lossless
fn sign_loss(x: i32) -> u32 { x as u32 }                // cast_sign_loss
fn wrap(x: u32) -> i32 { x as i32 }                     // cast_possible_wrap
fn masked(x: u64) -> u8 { (x & 0xff) as u8 }            // reduced by apply_reductions: no truncation lint
fn int_div_then_float(sum: i32, n: i32) -> f64 { f64::from(sum / n) } // integer division: no lint at all

fn main() {
    println!("{} {} {} {} {} {} {} {} {} {} {}",
        truncation(300), float_to_int(1e10), f64_to_f32(1e300), precision_i32_f32(16_777_217),
        precision_i64_f64(i64::MAX), exact_i32_f64(7), lossless(7), sign_loss(-1), wrap(u32::MAX),
        masked(0x1234), int_div_then_float(7, 2));
}
