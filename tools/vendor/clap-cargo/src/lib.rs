//! **clap-cargo**: Re-usable CLI flags for `cargo` plugins
//!
//! ## Examples
//!
//! ```rust,no_run
//! # #[cfg(feature = "clap")] {
//! # #[cfg(feature = "cargo_metadata")] {
//! use clap::Parser;
//!
//! // ...
//! #[derive(Debug, Parser)]
//! #[command(styles = clap_cargo::style::CLAP_STYLING)]
//! struct Cli {
//!     #[command(flatten)]
//!     manifest: clap_cargo::Manifest,
//!     #[command(flatten)]
//!     workspace: clap_cargo::Workspace,
//!     #[command(flatten)]
//!     features: clap_cargo::Features,
//! }
//!
//! let cli = // ...
//! # Cli::parse_from(["app"]);
//! let mut metadata = cli.manifest.metadata();
//! cli.features.forward_metadata(&mut metadata);
//! let metadata = metadata.exec().unwrap();
//! let (selected, excluded) = cli.workspace.partition_packages(&metadata);
//! # }
//! # }
//! ```
//!
//! ## Relevant crates
//!
//! Other crates that might be useful for cargo plugins:
//! * [escargot][escargot] for wrapping `cargo-build`, `carg-run`, `cargo-test`, etc.
//! * [cargo_metadata][cargo_metadata] for getting crate information.
//! * [clap-verbosity][clap-verbosity] for adding logging to your CLI.
//!
//! [escargot]: https://crates.io/crates/escargot
//! [cargo_metadata]: https://crates.io/crates/cargo_metadata
//! [clap-verbosity]: https://crates.io/crates/clap-verbosity-flag

#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(clippy::print_stderr)]
#![warn(clippy::print_stdout)]

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
#[cfg(feature = "clap")]
pub struct ReadmeDoctests;

mod features;
mod manifest;
mod workspace;

pub mod style;

pub use features::*;
pub use manifest::*;
pub use workspace::*;
