#![allow(clippy::bool_assert_comparison, clippy::new_without_default)]

#[macro_use]
extern crate serde_json;

#[macro_use]
pub mod common;
pub mod json_dsl;
pub mod json_schema;

pub use crate::common::error::ValicoErrors;
