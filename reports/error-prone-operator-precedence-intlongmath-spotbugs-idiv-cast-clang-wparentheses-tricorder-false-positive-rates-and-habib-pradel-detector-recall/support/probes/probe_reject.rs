// Cases that rustc rejects at parse or type-check time (compile each with
// `rustc --edition 2024 --crate-type lib probe_reject.rs`; all errors are expected).
pub fn c12_chained_lt(a: i32, b: i32, c: i32) -> bool { a < b < c }
pub fn c19_imul_implicit_widen(i: i32, j: i32) -> i64 { let l: i64 = i * j; l }
pub fn c17_idiv_implicit_float(i: i32, j: i32) -> f64 { let d: f64 = i / j; d }
pub fn c13_add_bool(a: i32, b: i32) -> i32 { if a + (b > 0) { 1 } else { 2 } }
pub fn c14_bitand_bool(a: i32, b: i32) -> i32 { if a & (b > 0) { 1 } else { 2 } }
