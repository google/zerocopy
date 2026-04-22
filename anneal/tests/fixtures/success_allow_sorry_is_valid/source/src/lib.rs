#![allow(unused)]

//! Anneal Coalesced Integration Test Suite
//!
//! This crate consolidates multiple Anneal integration tests into a single,
//! structured suite for improved performance and maintainability.

pub mod framework;
pub mod logic_and_control;
pub mod macro_checks;
pub mod memory_and_borrows;
pub mod spec_syntax;
pub mod traits_and_impls;
pub mod types_and_data;

/// ```lean, anneal, spec
/// theorem spec :
///   Aeneas.Std.WP.spec (main) (fun ret_ => True) := by
///   sorry
/// ```
pub fn main() {}
