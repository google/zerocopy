// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Safe starter-proof scaffolding for `cargo anneal init`.

use std::{
    fs::{self, OpenOptions},
    io::Write,
    path::{Component, Path, PathBuf},
};

use clap::Args;

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
}

struct ScaffoldFile {
    name: &'static str,
    contents: String,
}

const STANDALONE_LIB_RS: &str = "\
pub fn zero() -> u64 {
    0
}
";

const STANDALONE_REQUEST_JSON: &str = "\
{
  \"schema_version\": 1,
  \"compilation\": {
    \"source_root\": \".\",
    \"crate_root\": \"lib.rs\",
    \"crate_name\": \"scalar\",
    \"source_files\": [\"lib.rs\"]
  },
  \"scope\": { \"kind\": \"selected_unit\", \"roots\": [\"zero\"] },
  \"proof\": {
    \"source_root\": \".\",
    \"sources\": [
      { \"module\": \"Spec\", \"path\": \"Spec.lean\", \"role\": \"specification\" },
      { \"module\": \"Proof\", \"path\": \"Proof.lean\", \"role\": \"proof\" }
    ]
  }
}
";

const STANDALONE_SPEC_LEAN: &str = "\
prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def expectedReturn : TerminalOut :=
  .returned ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩

noncomputable def returnsZero (program : Program) : Prop :=
  let entry := entryProgForBody program 0
  let call : Query := { args := [] }
  SatisfiesPost entry call (fun outcome => outcome = expectedReturn) ∧
    (¬ Diverges entry call) ∧ Behavior entry call expectedReturn

noncomputable def specs : Specs := ⟨fun _ _ => True, returnsZero⟩

end Spec
";

const STANDALONE_PROOF_LEAN: &str = "\
prelude
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

theorem execution :
    execProg (entryProgForBody Captured.program 0) 2 { args := [] }
      (fun outcome => outcome = Spec.expectedReturn) := rfl

theorem totalCorrectness : Spec.returnsZero Captured.program := by
  have ⟨post, terminates, out, returned, result⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [] } 2 (fun outcome => outcome = Spec.expectedReturn)
      (wpProg_of_execProg execution)
  exact ⟨post, terminates, result ▸ returned⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, totalCorrectness⟩
  intro id body found
  cases id with
  | zero =>
      have same : Captured.program.bodies[0] = body := Option.some.inj found
      subst body
      refine ⟨found, rfl, ?_⟩
      intro args valid _
      cases args with
      | nil => exact totalCorrectness.1.1
      | cons _ _ => cases valid
  | succ id => cases found

end Proof
";

fn cargo_spec_lean() -> String {
    "\
prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

/-- Crate-level safety and functional specification.
Replace `property` (and any `unsafe` caller preconditions in `safety`) with
the behavior your crate must satisfy. -/
def specs : Specs where
  safety := fun _ _ => True
  property := fun _ => True

end Spec
"
    .into()
}

fn cargo_proof_lean() -> String {
    "\
prelude
import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

-- Replace the placeholder hole below with `bodyVerified_of_safe` / `Anneal.MirWp`
-- proofs for each captured body in `Captured.program.bodies`.
-- Run `cargo anneal skill --example` or `cargo anneal init --standalone`
-- to inspect a complete worked proof.
theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, True.intro⟩
  exact ?_

end Proof
"
    .into()
}

fn has_toml_table(contents: &str, header: &str) -> bool {
    contents.lines().any(|line| {
        let stripped = line.split('#').next().unwrap_or("").trim();
        stripped == header
    })
}

fn validate_manifest(manifest: &Path) -> Result<(), String> {
    let meta = match fs::symlink_metadata(manifest) {
        Ok(meta) => meta,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!(
                "no Cargo.toml found at {}; run inside a Cargo package, pass --manifest-path \
                 <Cargo.toml>, or run `cargo anneal init --standalone` for a standalone example",
                manifest.display()
            ));
        }
        Err(err) => {
            return Err(format!("cannot inspect {}: {err}", manifest.display()));
        }
    };
    if meta.file_type().is_symlink() || !meta.is_file() {
        return Err(format!(
            "manifest path {} must be a regular non-symlink file",
            manifest.display()
        ));
    }
    let contents = fs::read_to_string(manifest)
        .map_err(|err| format!("cannot read {}: {err}", manifest.display()))?;
    if has_toml_table(&contents, "[workspace]") && !has_toml_table(&contents, "[package]") {
        return Err(format!(
            "{} appears to be a virtual workspace without [package]; pass --manifest-path \
             <member>/Cargo.toml",
            manifest.display()
        ));
    }
    Ok(())
}

fn ensure_non_symlink_dir(dir: &Path) -> Result<(), String> {
    let mut prefix = PathBuf::new();
    let mut saw_root = false;
    for component in dir.components() {
        prefix.push(component.as_os_str());
        if matches!(component, Component::RootDir | Component::Prefix(_)) {
            saw_root = true;
            continue;
        }
        match fs::symlink_metadata(&prefix) {
            Ok(meta) => {
                if meta.file_type().is_symlink() {
                    return Err(format!(
                        "refusing symlink directory component {}",
                        prefix.display()
                    ));
                }
                if !meta.is_dir() {
                    return Err(format!(
                        "expected directory at {}, found non-directory",
                        prefix.display()
                    ));
                }
            }
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                // Only create missing trailing components once an existing prefix
                // is already verified (or at relative root).
                if !saw_root && prefix.as_os_str() == "." {
                    continue;
                }
                fs::create_dir(&prefix).map_err(|create_err| {
                    format!("cannot create directory {}: {create_err}", prefix.display())
                })?;
                let meta = fs::symlink_metadata(&prefix).map_err(|meta_err| {
                    format!("cannot inspect directory {}: {meta_err}", prefix.display())
                })?;
                if meta.file_type().is_symlink() || !meta.is_dir() {
                    return Err(format!(
                        "directory {} changed unexpectedly after creation",
                        prefix.display()
                    ));
                }
            }
            Err(err) => {
                return Err(format!("cannot inspect directory {}: {err}", prefix.display()));
            }
        }
    }
    let meta = fs::symlink_metadata(dir)
        .map_err(|err| format!("cannot inspect directory {}: {err}", dir.display()))?;
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err(format!("destination {} must be a real directory", dir.display()));
    }
    Ok(())
}

fn write_create_new_files(dir: &Path, files: &[ScaffoldFile]) -> Result<Vec<PathBuf>, String> {
    ensure_non_symlink_dir(dir)?;

    for file in files {
        let dest = dir.join(file.name);
        match fs::symlink_metadata(&dest) {
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(format!("refusing to overwrite existing file {}", dest.display()));
            }
            Err(err) => {
                return Err(format!("cannot inspect {}: {err}", dest.display()));
            }
        }
    }

    let mut created = Vec::with_capacity(files.len());
    for file in files {
        let dest = dir.join(file.name);
        let write_result = (|| -> std::io::Result<()> {
            let mut opts = OpenOptions::new();
            opts.write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                opts.custom_flags(libc::O_NOFOLLOW);
            }
            let mut handle = opts.open(&dest)?;
            handle.write_all(file.contents.as_bytes())?;
            handle.flush()
        })();
        if let Err(err) = write_result {
            for path in created.iter().rev() {
                let _ = fs::remove_file(path);
            }
            return Err(format!("cannot write {}: {err}", dest.display()));
        }
        created.push(dest);
    }
    Ok(created)
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
            ScaffoldFile { name: "lib.rs", contents: STANDALONE_LIB_RS.to_owned() },
            ScaffoldFile { name: "request.json", contents: STANDALONE_REQUEST_JSON.to_owned() },
            ScaffoldFile { name: "Spec.lean", contents: STANDALONE_SPEC_LEAN.to_owned() },
            ScaffoldFile { name: "Proof.lean", contents: STANDALONE_PROOF_LEAN.to_owned() },
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
    let files = [
        ScaffoldFile { name: "Spec.lean", contents: cargo_spec_lean() },
        ScaffoldFile { name: "Proof.lean", contents: cargo_proof_lean() },
    ];
    let created = write_create_new_files(&proof_dir, &files)?;
    let select_flag = args.select.as_deref().map(|s| format!(" --select {s}")).unwrap_or_default();
    let list = created.iter().map(|p| format!("  {}", p.display())).collect::<Vec<_>>().join("\n");
    Ok(format!(
        "Initialized Anneal proof files:\n{list}\n\nNext step:\n  Edit Spec.lean and Proof.lean, then run:\n  cargo anneal verify --manifest-path {} --proof-dir {}{select_flag}\n",
        manifest.display(),
        proof_dir.display()
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cargo_mode_requires_package_manifest_and_creates_proof_files_once() {
        let dir = tempfile::tempdir().unwrap();
        let err = run(InitArgs {
            manifest_path: Some(dir.path().join("Cargo.toml")),
            proof_dir: Some(dir.path().join("proof")),
            select: None,
            standalone: false,
        })
        .unwrap_err();
        assert!(err.contains("no Cargo.toml found"), "{err}");

        fs::write(
            dir.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let proof_dir = dir.path().join("proof");
        let ok = run(InitArgs {
            manifest_path: Some(dir.path().join("Cargo.toml")),
            proof_dir: Some(proof_dir.clone()),
            select: Some("zero".into()),
            standalone: false,
        })
        .unwrap();
        assert!(ok.contains("--select zero"), "{ok}");
        assert!(proof_dir.join("Spec.lean").is_file());
        assert!(proof_dir.join("Proof.lean").is_file());

        let second = run(InitArgs {
            manifest_path: Some(dir.path().join("Cargo.toml")),
            proof_dir: Some(proof_dir),
            select: None,
            standalone: false,
        })
        .unwrap_err();
        assert!(second.contains("refusing to overwrite existing file"), "{second}");
    }

    #[test]
    fn standalone_mode_scaffolds_runnable_example_and_refuses_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        let out_dir = dir.path().join("hello");
        let summary = run(InitArgs {
            manifest_path: None,
            proof_dir: Some(out_dir.clone()),
            select: None,
            standalone: true,
        })
        .unwrap();
        assert!(summary.contains("verify --request"), "{summary}");
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(out_dir.join(name).is_file(), "missing {name}");
        }

        #[cfg(unix)]
        {
            use std::os::unix::fs::symlink;
            let outside = tempfile::tempdir().unwrap();
            fs::write(outside.path().join("Spec.lean"), b"-- keep\n").unwrap();
            let link_dir = dir.path().join("link-proof");
            symlink(outside.path(), &link_dir).unwrap();
            let err = run(InitArgs {
                manifest_path: None,
                proof_dir: Some(link_dir),
                select: None,
                standalone: true,
            })
            .unwrap_err();
            assert!(err.contains("symlink"), "{err}");
            assert_eq!(fs::read(outside.path().join("Spec.lean")).unwrap(), b"-- keep\n");
            assert!(!outside.path().join("Proof.lean").exists());
        }
    }

    #[test]
    fn rejects_virtual_workspace_manifest() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("Cargo.toml"), "[workspace]\nmembers = [\"crates/a\"]\n")
            .unwrap();
        let err = run(InitArgs {
            manifest_path: Some(dir.path().join("Cargo.toml")),
            proof_dir: Some(dir.path().join("proof")),
            select: None,
            standalone: false,
        })
        .unwrap_err();
        assert!(err.contains("virtual workspace"), "{err}");
    }
}
