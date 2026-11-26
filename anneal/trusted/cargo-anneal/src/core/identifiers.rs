// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure Lean artifact schemas, identifier validators, relative-path checks,
//! and iterative topological module sorting.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Component, Path},
};

use serde::{Deserialize, Serialize};

use crate::core::error::Failure;

/// Lists the `.olean` artifact companion suffixes passed in the first array of
/// `Lean.ImportArtifacts`.
pub const OLEAN_PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

/// Lists the `.ir` artifact companion suffixes passed in the second array of
/// `Lean.ImportArtifacts`.
pub const IR_PARTS: [&str; 2] = ["ir.sig", "ir"];

/// Lists all five compiled Lean artifact companion suffixes tracked by
/// `foundation-lock.json`, `library-lock.json`, and module compilation.
pub const PARTS: [&str; 5] = ["olean", "olean.server", "olean.private", "ir.sig", "ir"];

/// Door 1 size cap for a single compiled `.olean` output (256 MiB).
pub const MAX_OLEAN_BYTES: u64 = 256 * 1024 * 1024;

/// Required 6-byte magic prefix for standard Lean 4 module `.olean` artifacts
/// (`v2` compacted region without closure relocation).
///
/// Lean 4's extended `v3` format (`b"olean\x03"`) carries relocated function
/// pointers (`allowClosures := true`) intended only for identical-process
/// serialization, never for standard `.olean` compilation outputs. Rejecting
/// non-`v2` headers at Door 1 fails closed before any promoted `.olean` can
/// reach downstream artifact inspection.
pub const OLEAN_V2_MAGIC: &[u8; 6] = b"olean\x02";

/// Validate a compiled `.olean` file's 6-byte magic header as standard `v2`
/// (rejecting truncated files and extended closure-relocating `v3` files).
pub fn validate_olean_v2_header(prefix: &[u8], label: &str, phase: &str) -> Result<(), Failure> {
    if prefix.len() < OLEAN_V2_MAGIC.len() {
        return Err(Failure::operational(
            phase,
            format!(
                "malformed .olean artifact {label}: truncated header ({} bytes, expected v2 magic)",
                prefix.len()
            ),
        ));
    }
    if &prefix[..OLEAN_V2_MAGIC.len()] != OLEAN_V2_MAGIC {
        return Err(Failure::operational(
            phase,
            format!(
                "unsupported or malformed .olean header in {label}: expected v2 magic {:02x?}, got {:02x?}",
                OLEAN_V2_MAGIC,
                &prefix[..OLEAN_V2_MAGIC.len()]
            ),
        ));
    }
    Ok(())
}

/// Holds the validated artifact companion paths for a single compiled Lean
/// module.
///
/// `Lean.ImportArtifacts` expects two path arrays per module:
///
/// 1. `olean_parts`: `[.olean, .olean.server?, .olean.private?]` (always
///    non-empty; `.olean` is mandatory).
/// 2. `ir_parts`: `[.ir.sig?, .ir?]`.
///
/// Representing these two groups as named fields rather than `Vec<Vec<String>>`
/// makes malformed artifact-group counts unrepresentable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleArtifacts {
    /// Holds the non-empty `.olean` companion group (`OLEAN_PARTS`).
    pub olean_parts: Vec<String>,
    /// Holds the optional `.ir` companion group (`IR_PARTS`).
    pub ir_parts: Vec<String>,
}

impl ModuleArtifacts {
    /// Construct [`ModuleArtifacts`] from a map of available part suffixes
    /// (`"olean"` -> path, etc.), failing if the primary `"olean"` part is
    /// absent.
    pub fn from_available(
        available: &BTreeMap<&str, String>,
        phase: &str,
        err_msg: impl FnOnce() -> String,
    ) -> Result<Self, Failure> {
        if !available.contains_key("olean") {
            return Err(Failure::new(2, phase, err_msg()));
        }
        let olean_parts = OLEAN_PARTS.iter().filter_map(|p| available.get(*p).cloned()).collect();
        let ir_parts = IR_PARTS.iter().filter_map(|p| available.get(*p).cloned()).collect();
        Ok(Self { olean_parts, ir_parts })
    }

    /// Convert to the two-element array representation expected by
    /// `Lean.ImportArtifacts` in `--setup` and `TrustedBoundary.lean`.
    pub fn to_wire(&self) -> [&[String]; 2] {
        [&self.olean_parts, &self.ir_parts]
    }
}

/// Represents a single `import` edge in a Lean module header, matching Lean's
/// `Import` JSON encoding (`Lean.Import`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ImportEdge {
    /// Names the imported module (for example `"Init.Core"` or
    /// `"Trusted.MirAst"`).
    pub module: String,
    /// Indicates whether `import all` was used (always `false` in admitted
    /// modules).
    pub import_all: bool,
    /// Indicates whether the import is exported (`true` for standard `import`).
    pub is_exported: bool,
    /// Indicates whether `meta import` was used (always `false` in admitted
    /// modules).
    pub is_meta: bool,
}

/// Return `true` if `s` is a valid ASCII Lean module identifier component.
pub fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|first| first.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Return `true` if `s` is a `#![feature(...)]` gate name of the form
/// `[a-z][a-z0-9_]*` (no wildcards, separators, or `-Zallow-features`
/// delimiters).
pub fn is_feature_name(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|c| c.is_ascii_lowercase())
        && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

/// Return `true` if `rel` consists exclusively of normal path components (no
/// `/`, `.`, or `..`).
pub fn is_clean_relative_path(rel: &str) -> bool {
    let mut comps = Path::new(rel).components();
    comps.clone().next().is_some() && comps.all(|c| matches!(c, Component::Normal(_)))
}

/// Topologically sort the module set `pending` according to `imports_map`,
/// returning a policy rejection (`code == 1`) with `cycle_msg` if `pending`
/// contains an import cycle.
///
/// Emit each ready layer in sorted order. Imports outside `pending` are assumed
/// to be available. Use iteration so deep import chains do not consume one Rust
/// stack frame per module.
pub fn topo_sort_modules(
    mut pending: BTreeSet<String>,
    imports_map: &BTreeMap<String, Vec<ImportEdge>>,
    cycle_msg: &str,
) -> Result<Vec<String>, Failure> {
    let mut order = Vec::with_capacity(pending.len());
    while !pending.is_empty() {
        // Snapshot the whole ready layer before removing modules so newly
        // unlocked modules cannot interleave with its sorted order.
        let ready: Vec<_> = pending
            .iter()
            .filter(|module| {
                imports_map[*module].iter().all(|edge| !pending.contains(&edge.module))
            })
            .cloned()
            .collect();
        if ready.is_empty() {
            return Err(Failure::policy("preflight", cycle_msg));
        }
        for module in ready {
            pending.remove(&module);
            order.push(module);
        }
    }
    Ok(order)
}
