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

/// Validate an existing directory component or create a missing one,
/// returning `Ok(true)` if `create_dir` created this component.
///
/// When `allow_symlink_ancestor` is `true`, an existing symlink is resolved
/// with `fs::metadata` (matching OS resolution of caller-chosen ancestor
/// directories such as macOS `/tmp -> private/tmp` or symlinked `$TMPDIR`).
/// Otherwise, symlinks are rejected via `fs::symlink_metadata`.
fn ensure_dir_component(prefix: &Path, allow_symlink_ancestor: bool) -> Result<bool, String> {
    match fs::symlink_metadata(prefix) {
        Ok(lmeta) if allow_symlink_ancestor && lmeta.file_type().is_symlink() => {
            let meta = fs::metadata(prefix).map_err(|err| {
                format!("cannot inspect symlink directory ancestor {}: {err}", prefix.display())
            })?;
            if !meta.is_dir() {
                return Err(format!(
                    "expected directory at {}, found non-directory",
                    prefix.display()
                ));
            }
            Ok(false)
        }
        Ok(lmeta) => {
            if lmeta.file_type().is_symlink() {
                return Err(format!("refusing symlink directory {}", prefix.display()));
            }
            if !lmeta.is_dir() {
                return Err(format!(
                    "expected directory at {}, found non-directory",
                    prefix.display()
                ));
            }
            Ok(false)
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            fs::create_dir(prefix).map_err(|create_err| {
                format!("cannot create directory {}: {create_err}", prefix.display())
            })?;
            let meta = fs::symlink_metadata(prefix).map_err(|meta_err| {
                format!("cannot inspect directory {}: {meta_err}", prefix.display())
            })?;
            if meta.file_type().is_symlink() || !meta.is_dir() {
                return Err(format!(
                    "directory {} changed unexpectedly after creation",
                    prefix.display()
                ));
            }
            Ok(true)
        }
        Err(err) => Err(format!("cannot inspect directory {}: {err}", prefix.display())),
    }
}

fn ensure_non_symlink_dir(dir: &Path) -> Result<(), String> {
    if dir.as_os_str().is_empty() {
        return Err("directory path cannot be empty".into());
    }
    // Rebuild from `components()` to trim trailing separators (and trailing
    // `/.`) while preserving root `/` and `.`, so `symlink_metadata` inspects
    // a final symlink entry itself rather than following a trailing slash.
    let trimmed: PathBuf = dir.components().collect();
    if trimmed.as_os_str().is_empty() {
        return Err("directory path cannot be empty".into());
    }
    if matches!(trimmed.components().next_back(), Some(Component::ParentDir)) {
        return Err(format!("refusing directory path ending in '..': {}", dir.display()));
    }

    let mut prefix = PathBuf::new();
    let mut created_missing = false;
    let mut components = trimmed.components().peekable();
    while let Some(component) = components.next() {
        prefix.push(component.as_os_str());
        if matches!(component, Component::RootDir | Component::Prefix(_)) {
            continue;
        }
        let is_last = components.peek().is_none();
        if ensure_dir_component(&prefix, !created_missing && !is_last)? {
            created_missing = true;
        }
    }

    let meta = fs::symlink_metadata(&trimmed)
        .map_err(|err| format!("cannot inspect directory {}: {err}", trimmed.display()))?;
    if meta.file_type().is_symlink() {
        return Err(format!("refusing symlink directory {}", trimmed.display()));
    }
    if !meta.is_dir() {
        return Err(format!("expected directory at {}, found non-directory", trimmed.display()));
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
            for spelling in [
                link_dir.clone(),
                PathBuf::from(format!("{}/", link_dir.display())),
                link_dir.join("."),
            ] {
                let err = run(InitArgs {
                    manifest_path: None,
                    proof_dir: Some(spelling),
                    select: None,
                    standalone: true,
                })
                .unwrap_err();
                assert!(err.contains("symlink"), "{err}");
            }
            assert_eq!(fs::read(outside.path().join("Spec.lean")).unwrap(), b"-- keep\n");
            assert!(!outside.path().join("Proof.lean").exists());
        }
    }

    #[test]
    fn strip_license_header_handles_comment_blocks_and_preserves_unheaded_text() {
        assert_eq!(
            strip_license_header("// Copyright 2026 Author\n//\n// body\n\npub fn f() {}\n", "//"),
            "pub fn f() {}\n"
        );
        assert_eq!(
            strip_license_header("-- Copyright 2026 Author\n--\n\nmodule\n", "--"),
            "module\n"
        );
        assert_eq!(
            strip_license_header("// Copyright 2026 Author\n\n\npub fn f() {}\n", "//"),
            "\npub fn f() {}\n"
        );
        assert_eq!(
            strip_license_header("// Copyright 2026 Author\r\n// line\r\n\r\nbody\r\n", "//"),
            "body\r\n"
        );
        assert_eq!(
            strip_license_header("// Copyright 2026 Author\npub fn f() {}\n", "//"),
            "pub fn f() {}\n"
        );
        assert_eq!(strip_license_header("// Copyright 2026 Author", "//"), "");
        assert_eq!(strip_license_header(STANDALONE_REQUEST_JSON, "//"), STANDALONE_REQUEST_JSON);
        assert_eq!(
            strip_license_header("// Licensed only\n\ncode\n", "//"),
            "// Licensed only\n\ncode\n"
        );
        assert_eq!(
            strip_license_header("// Copyrighted\n\ncode\n", "//"),
            "// Copyrighted\n\ncode\n"
        );
        assert_eq!(strip_license_header("// Copyright\n\ncode\n", "//"), "// Copyright\n\ncode\n");
        assert_eq!(strip_license_header("", "//"), "");
        assert_eq!(
            strip_license_header(" Copyright 2026\n\ncode\n", ""),
            " Copyright 2026\n\ncode\n"
        );
    }

    #[test]
    fn standalone_scaffolds_match_assets_without_license_headers() {
        let dir = tempfile::tempdir().unwrap();
        let out_dir = dir.path().join("scalar");
        run(InitArgs {
            manifest_path: None,
            proof_dir: Some(out_dir.clone()),
            select: None,
            standalone: true,
        })
        .unwrap();

        let lib_rs = fs::read_to_string(out_dir.join("lib.rs")).unwrap();
        let request_json = fs::read_to_string(out_dir.join("request.json")).unwrap();
        let spec_lean = fs::read_to_string(out_dir.join("Spec.lean")).unwrap();
        let proof_lean = fs::read_to_string(out_dir.join("Proof.lean")).unwrap();

        assert!(lib_rs.starts_with("pub fn zero()"), "{lib_rs}");
        assert!(request_json.starts_with('{'), "{request_json}");
        assert!(spec_lean.starts_with("module\n"), "{spec_lean}");
        assert!(proof_lean.starts_with("module\n"), "{proof_lean}");

        for (name, generated) in
            [("lib.rs", &lib_rs), ("Spec.lean", &spec_lean), ("Proof.lean", &proof_lean)]
        {
            assert!(!generated.contains("Copyright"), "{name} retained copyright header");
            assert!(!generated.contains("Licensed under"), "{name} retained license header");
        }

        let (lib_header, lib_body) =
            include_str!("../assets/scalar/lib.rs").split_once("\n\n").unwrap();
        assert!(lib_header.starts_with("// Copyright "));
        assert_eq!(lib_rs, lib_body);

        assert_eq!(request_json, include_str!("../assets/scalar/request.json"));

        let (spec_header, spec_body) =
            include_str!("../assets/scalar/Spec.lean").split_once("\n\n").unwrap();
        assert!(spec_header.starts_with("-- Copyright "));
        assert_eq!(spec_lean, spec_body);

        let (proof_header, proof_body) =
            include_str!("../assets/scalar/Proof.lean").split_once("\n\n").unwrap();
        assert!(proof_header.starts_with("-- Copyright "));
        assert_eq!(proof_lean, proof_body);
    }

    #[test]
    fn ensure_non_symlink_dir_handles_existing_root_dot_and_empty_paths() {
        let dir = tempfile::tempdir().unwrap();
        let existing = dir.path().join("existing");
        fs::create_dir(&existing).unwrap();
        ensure_non_symlink_dir(&existing).unwrap();
        ensure_non_symlink_dir(Path::new(&format!("{}/", existing.display()))).unwrap();

        ensure_non_symlink_dir(Path::new(".")).unwrap();
        ensure_non_symlink_dir(Path::new("./")).unwrap();
        ensure_non_symlink_dir(Path::new("/")).unwrap();

        let empty_err = ensure_non_symlink_dir(Path::new("")).unwrap_err();
        assert!(empty_err.contains("empty"), "{empty_err}");

        for parent_ref in [Path::new(".."), Path::new("../"), Path::new("../.")] {
            let err = ensure_non_symlink_dir(parent_ref).unwrap_err();
            assert!(err.contains("'..'"), "{err}");
        }
        let missing_parent_ref = dir.path().join("missing-before-parent/..");
        let missing_parent_err = ensure_non_symlink_dir(&missing_parent_ref).unwrap_err();
        assert!(missing_parent_err.contains("'..'"), "{missing_parent_err}");
        assert!(!dir.path().join("missing-before-parent").exists());

        let regular_file = dir.path().join("regular");
        fs::write(&regular_file, b"file").unwrap();
        let file_err = ensure_non_symlink_dir(&regular_file).unwrap_err();
        assert!(file_err.contains("non-directory"), "{file_err}");
        let under_file_err = ensure_non_symlink_dir(&regular_file.join("proof")).unwrap_err();
        assert!(under_file_err.contains("non-directory"), "{under_file_err}");
        assert!(!dir.path().join("regular/proof").exists());
    }

    #[cfg(unix)]
    #[test]
    fn allows_symlinked_ancestors_while_rejecting_symlink_destinations_and_broken_ancestors() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let real_root = dir.path().join("private-tmp");
        fs::create_dir(&real_root).unwrap();
        let symlink_parent = dir.path().join("tmp-link");
        symlink(&real_root, &symlink_parent).unwrap();

        // Pre-existing symlinked ancestor (like macOS `/tmp -> private/tmp`)
        // succeeds for nested new directories and existing real subdirectories.
        let nested = symlink_parent.join("nested").join("proof");
        run(InitArgs {
            manifest_path: None,
            proof_dir: Some(nested),
            select: None,
            standalone: true,
        })
        .unwrap();
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(real_root.join("nested/proof").join(name).is_file(), "missing {name}");
        }

        let existing_sub = real_root.join("existing-dir");
        fs::create_dir(&existing_sub).unwrap();
        run(InitArgs {
            manifest_path: None,
            proof_dir: Some(symlink_parent.join("existing-dir")),
            select: None,
            standalone: true,
        })
        .unwrap();
        assert!(existing_sub.join("Proof.lean").is_file());

        // Cargo mode under a pre-existing symlinked ancestor also succeeds.
        let crate_real = real_root.join("crate-demo");
        fs::create_dir(&crate_real).unwrap();
        fs::write(
            crate_real.join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        run(InitArgs {
            manifest_path: Some(symlink_parent.join("crate-demo/Cargo.toml")),
            proof_dir: None,
            select: None,
            standalone: false,
        })
        .unwrap();
        assert!(crate_real.join("proof/Spec.lean").is_file());
        assert!(crate_real.join("proof/Proof.lean").is_file());

        // Dangling symlink destination (with and without trailing `/`) is
        // refused.
        let dangling = dir.path().join("dangling");
        symlink(dir.path().join("absent-target"), &dangling).unwrap();
        for spelling in [dangling.clone(), PathBuf::from(format!("{}/", dangling.display()))] {
            let err = ensure_non_symlink_dir(&spelling).unwrap_err();
            assert!(err.contains("symlink"), "{err}");
        }

        // Dangling symlink ancestor is refused cleanly without creating
        // anything.
        let dangling_child = dangling.join("proof");
        let dangling_err = run(InitArgs {
            manifest_path: None,
            proof_dir: Some(dangling_child),
            select: None,
            standalone: true,
        })
        .unwrap_err();
        assert!(
            dangling_err.contains("cannot inspect symlink directory ancestor"),
            "{dangling_err}"
        );
        assert!(!dir.path().join("absent-target").exists());

        // Symlinked ancestor targeting a regular file is refused cleanly.
        let regular_file = dir.path().join("file");
        fs::write(&regular_file, b"data").unwrap();
        let file_link = dir.path().join("file-link");
        symlink(&regular_file, &file_link).unwrap();
        let file_link_err = ensure_non_symlink_dir(&file_link.join("proof")).unwrap_err();
        assert!(file_link_err.contains("non-directory"), "{file_link_err}");

        // Symlink loop ancestor is refused cleanly.
        let loop_a = dir.path().join("loop-a");
        let loop_b = dir.path().join("loop-b");
        symlink(&loop_b, &loop_a).unwrap();
        symlink(&loop_a, &loop_b).unwrap();
        let loop_err = ensure_non_symlink_dir(&loop_a.join("proof")).unwrap_err();
        assert!(loop_err.contains("cannot inspect symlink directory ancestor"), "{loop_err}");

        // Paths whose final non-`.` component is `..` are refused, including
        // through symlinked ancestors or trailing separators.
        for parent_spelling in [
            symlink_parent.join(".."),
            PathBuf::from(format!("{}/../", symlink_parent.display())),
            symlink_parent.join("../."),
            real_root.join(".."),
        ] {
            let err = run(InitArgs {
                manifest_path: None,
                proof_dir: Some(parent_spelling),
                select: None,
                standalone: true,
            })
            .unwrap_err();
            assert!(err.contains("'..'"), "{err}");
        }
    }

    #[test]
    fn relative_paths_subprocess_helper() {
        let Some(expected_dir) = std::env::var_os("ANNEAL_INIT_SUBPROCESS_DIR") else {
            return;
        };
        assert_eq!(
            fs::canonicalize(std::env::current_dir().unwrap()).unwrap(),
            fs::canonicalize(expected_dir).unwrap()
        );

        let dot_out =
            run(InitArgs { manifest_path: None, proof_dir: None, select: None, standalone: true })
                .unwrap();
        assert!(dot_out.contains("verify --request ./request.json"), "{dot_out}");
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(Path::new(name).is_file(), "missing {name} in '.'");
        }

        let nested_out = run(InitArgs {
            manifest_path: None,
            proof_dir: Some(PathBuf::from("a/b/c")),
            select: None,
            standalone: true,
        })
        .unwrap();
        assert!(nested_out.contains("verify --request a/b/c/request.json"), "{nested_out}");
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(Path::new("a/b/c").join(name).is_file(), "missing {name} in a/b/c");
        }

        let parent_sibling_out = run(InitArgs {
            manifest_path: None,
            proof_dir: Some(PathBuf::from("../proof")),
            select: None,
            standalone: true,
        })
        .unwrap();
        assert!(
            parent_sibling_out.contains("verify --request ../proof/request.json"),
            "{parent_sibling_out}"
        );
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(Path::new("../proof").join(name).is_file(), "missing {name} in ../proof");
        }
    }

    #[test]
    fn standalone_accepts_dot_and_relative_nested_paths_in_isolated_cwd() {
        let dir = tempfile::tempdir().unwrap();
        let subdir = dir.path().join("sub");
        fs::create_dir(&subdir).unwrap();
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "init::tests::relative_paths_subprocess_helper"])
            .env("ANNEAL_INIT_SUBPROCESS_DIR", &subdir)
            .current_dir(&subdir)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "subprocess failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(subdir.join(name).is_file(), "missing {name} in '.'");
            assert!(subdir.join("a/b/c").join(name).is_file(), "missing {name} in a/b/c");
            assert!(dir.path().join("proof").join(name).is_file(), "missing {name} in ../proof");
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
