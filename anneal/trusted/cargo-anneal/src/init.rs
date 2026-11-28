// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Safe starter-proof scaffolding for `cargo anneal init`.

use std::path::PathBuf;

use clap::{Args, ValueEnum};

mod files;
#[cfg(test)]
mod tests;

use self::files::{validate_manifest, write_create_new_files};

/// MIR profile whose specification bundle the Cargo-mode starter uses.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum InitProfile {
    /// Profile v1 scalar MIR (`Trusted.MirSemantics.Specs`)
    #[default]
    V1,
    /// Profile v2 references, raw pointers, and slices (`SpecsV2`)
    V2,
}

/// Arguments for `cargo anneal init`.
#[derive(Args)]
pub struct InitArgs {
    /// Package Cargo.toml to attach starter proof files to (defaults to ./Cargo.toml)
    #[arg(long, conflicts_with = "standalone")]
    pub manifest_path: Option<PathBuf>,
    /// Output directory for Spec.lean and Proof.lean (defaults to <crate>/proof, or . with --standalone)
    #[arg(long)]
    pub proof_dir: Option<PathBuf>,
    /// Optional function path to note in the generated --select command
    #[arg(long, conflicts_with = "standalone")]
    pub select: Option<String>,
    /// Create a self-contained runnable example (lib.rs, request.json, Spec.lean, Proof.lean)
    #[arg(long)]
    pub standalone: bool,
    /// Starter Spec.lean MIR profile (v2: references, raw pointers, slices)
    #[arg(long, value_enum, default_value_t = InitProfile::V1, conflicts_with = "standalone")]
    pub profile: InitProfile,
}

struct ScaffoldFile {
    name: &'static str,
    contents: String,
}

const STANDALONE_LIB_RS: &str = include_str!("../assets/scalar/lib.rs");
const STANDALONE_REQUEST_JSON: &str = include_str!("../assets/scalar/request.json");
const STANDALONE_SPEC_LEAN: &str = include_str!("../assets/scalar/Spec.lean");
const STANDALONE_PROOF_LEAN: &str = include_str!("../assets/scalar/Proof.lean");

/// Strip a leading `<comment_prefix> Copyright ...` license header block and
/// its immediately following blank line, returning `contents` unchanged when no
/// matching header is present.
fn strip_license_header<'a>(contents: &'a str, comment_prefix: &str) -> &'a str {
    let Some(after_prefix) = contents.strip_prefix(comment_prefix) else {
        return contents;
    };
    if comment_prefix.is_empty() || !after_prefix.starts_with(" Copyright ") {
        return contents;
    }
    let mut rest = contents;
    while rest.starts_with(comment_prefix) {
        match rest.find('\n') {
            Some(idx) => rest = &rest[idx + 1..],
            None => return "",
        }
    }
    rest.strip_prefix("\r\n").or_else(|| rest.strip_prefix('\n')).unwrap_or(rest)
}

fn cargo_spec_lean() -> String {
    "\
module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-- Crate-level safety and functional specification.
Replace `property` (and any `unsafe` caller preconditions in `safety`) with
the behavior your crate must satisfy. -/
def specs : Specs where
  safety := fun _ _ => True
  property := fun _ => True

end Spec

end
"
    .into()
}

fn cargo_proof_lean() -> String {
    "\
module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

-- Replace the placeholder hole below with `bodyVerified_of_safe` / `Anneal.MirWp`
-- proofs for each captured body in `Captured.program.bodies`.
-- Run `cargo anneal skill --example` or `cargo anneal init --standalone`
-- to inspect a complete worked proof.
public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, True.intro⟩
  exact ?_

end Proof
"
    .into()
}

fn cargo_spec_lean_v2() -> String {
    "\
module
prelude
public import Trusted.MirSemantics

@[expose] public section

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-- Crate-level MIR Profile v2 safety and functional specification.
`safety identity q` constrains each `Query` (arguments and `callerMem`)
passed to the `unsafe` function with canonical path `identity`. Replace
`property` (and any `unsafe` caller preconditions in `safety`) with the
behavior your crate must satisfy. -/
def specs : SpecsV2 where
  safety := fun _ _ => True
  property := fun _ => True

end Spec

end
"
    .into()
}

fn cargo_proof_lean_v2() -> String {
    "\
module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

-- `Expected.claim` is `UnitTheoremV2` or `CrateTheoremV2`. Replace the
-- placeholder hole below with a `BodyVerifiedV2` proof (static admission
-- and `WellFormedV2` for every valid `Query`) for each captured body in
-- `Captured.program.bodies`, for example by evaluating `execProgV2`.
public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, True.intro⟩
  exact ?_

end Proof
"
    .into()
}

/// Scaffold starter Anneal files and return a printable summary message.
pub fn run(args: InitArgs) -> Result<String, String> {
    if let Some(select) = &args.select
        && (select.trim().is_empty() || select.contains(['\n', '\r']))
    {
        return Err("--select function path cannot be empty or multiline".into());
    }

    if args.standalone {
        let dir = args.proof_dir.unwrap_or_else(|| PathBuf::from("."));
        let files = [
            ScaffoldFile {
                name: "lib.rs",
                contents: strip_license_header(STANDALONE_LIB_RS, "//").to_owned(),
            },
            ScaffoldFile { name: "request.json", contents: STANDALONE_REQUEST_JSON.to_owned() },
            ScaffoldFile {
                name: "Spec.lean",
                contents: strip_license_header(STANDALONE_SPEC_LEAN, "--").to_owned(),
            },
            ScaffoldFile {
                name: "Proof.lean",
                contents: strip_license_header(STANDALONE_PROOF_LEAN, "--").to_owned(),
            },
        ];
        let created = write_create_new_files(&dir, &files)?;
        let req = dir.join("request.json");
        let list =
            created.iter().map(|p| format!("  {}", p.display())).collect::<Vec<_>>().join("\n");
        return Ok(format!(
            "Initialized standalone Anneal example:\n{list}\n\nNext step:\n  cargo anneal verify --request {}\n",
            req.display()
        ));
    }

    let manifest = args.manifest_path.unwrap_or_else(|| PathBuf::from("Cargo.toml"));
    validate_manifest(&manifest)?;
    let proof_dir = args.proof_dir.unwrap_or_else(|| {
        manifest
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .map(|parent| parent.join("proof"))
            .unwrap_or_else(|| PathBuf::from("proof"))
    });
    let (spec, proof, profile_note) = match args.profile {
        InitProfile::V1 => (cargo_spec_lean(), cargo_proof_lean(), ""),
        InitProfile::V2 => (
            cargo_spec_lean_v2(),
            cargo_proof_lean_v2(),
            "\nThe v2 starter checks only if capture emits MIR Profile v2\n(`program.mir_profile_version = 2`); scalar-only crates need the default\n`--profile v1` starter.\n",
        ),
    };
    let files = [
        ScaffoldFile { name: "Spec.lean", contents: spec },
        ScaffoldFile { name: "Proof.lean", contents: proof },
    ];
    let created = write_create_new_files(&proof_dir, &files)?;
    let select_flag = args.select.as_deref().map(|s| format!(" --select {s}")).unwrap_or_default();
    let list = created.iter().map(|p| format!("  {}", p.display())).collect::<Vec<_>>().join("\n");
    Ok(format!(
        "Initialized Anneal proof files:\n{list}\n\nNext step:\n  Edit Spec.lean and Proof.lean, then run:\n  cargo anneal verify --manifest-path {} --proof-dir {}{select_flag}\n{profile_note}",
        manifest.display(),
        proof_dir.display()
    ))
}
