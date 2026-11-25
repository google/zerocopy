// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure, OS-I/O-free verification core shared across `cargo-anneal` and
//! `anneal-audit`.
//!
//! Modules under [`core`](self) must never access the filesystem, processes,
//! network, clock, or host environment variables, allowing them to compile and
//! execute cleanly on both host platforms and `wasm32-unknown-unknown`.

#![forbid(unsafe_code)]

pub mod digest;
pub mod elf;
pub mod error;
pub mod identifiers;
pub mod sanitize;

pub use digest::{digest_to_hex, is_sha256_hex, sha256_bytes};
pub use elf::{
    Elf64PhdrTable, FORBIDDEN_LOADER_ENV_PREFIXES, decode_pt_interp_cstr, find_elf64_pt_interp,
    parse_elf64_ehdr, reject_forbidden_loader_env,
};
pub use error::Failure;
pub use identifiers::{
    IR_PARTS, ImportEdge, MAX_OLEAN_BYTES, ModuleArtifacts, OLEAN_PARTS, OLEAN_V2_MAGIC, PARTS,
    is_clean_relative_path, is_lean_ident, topo_sort_modules, validate_olean_v2_header,
};
pub use sanitize::{
    SanitizedBlock, SanitizedInline, escape_gfm_cell, format_fenced_code_block,
    format_gfm_code_cell, is_dangerous_unicode, sanitize_inline_string,
};
