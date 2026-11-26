// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Checks canonical bundle parity and optionally stages
//! `trusted/cargo-anneal/packaged/{bundled_resources.rs,bundled_theory.json}`
//! for standalone `.crate` packaging.
//!
//! Ordinary workspace builds compile `trusted/cargo-anneal/build.rs` directly
//! from canonical sources into `$OUT_DIR/bundled_resources.rs` and
//! `$OUT_DIR/bundled_theory.json` without checking generated monoliths into
//! git. Standalone packaging (`cargo package` / `cargo publish`) passes
//! `--stage-package` to write the transient `trusted/cargo-anneal/packaged/`
//! snapshots.

use cargo_anneal::bundle::{
    LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION, PACKAGED_BUNDLE_DESTINATION,
    PACKAGED_THEORY_BUNDLE_DESTINATION, prepare_packaged_bundle_destination,
    prepare_packaged_theory_destination, render_bundled_resources, render_bundled_theory,
    validate_destination_path,
};
use clap::Parser;
use std::error::Error;
use std::fs;
use std::io::{self, Write as _};
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(about = "Check or stage the verifier's embedded source resources")]
struct Args {
    /// Names the repository root containing the canonical sources and output.
    #[arg(long)]
    root: PathBuf,
    /// Explicitly request check-only mode (now the default behavior; retained
    /// for backwards CLI compatibility).
    #[arg(long, conflicts_with = "stage_package")]
    check: bool,
    /// Stage `trusted/cargo-anneal/packaged/` snapshots for standalone
    /// `cargo package` / `cargo publish`.
    #[arg(long)]
    stage_package: bool,
}

fn write_atomic(
    destination: &Path,
    permissions: Option<fs::Permissions>,
    expected: &str,
) -> Result<(), Box<dyn Error>> {
    // Replacing the named file keeps every other hard link to its old inode
    // unchanged. Preserve the destination's permissions on the new file before
    // the same-directory rename makes the update visible.
    let mut temporary = tempfile::NamedTempFile::new_in(
        destination
            .parent()
            .expect("the fixed output path has a parent"),
    )?;
    temporary.write_all(expected.as_bytes())?;
    if let Some(permissions) = permissions {
        temporary.as_file().set_permissions(permissions)?;
    }
    temporary.persist(destination)?;
    Ok(())
}

fn reject_legacy_bundle(root: &Path, rel: &str) -> Result<(), Box<dyn Error>> {
    let legacy_path = root.join(rel);
    match fs::symlink_metadata(&legacy_path) {
        Ok(_) => Err(io::Error::other(format!(
            "legacy checked-in bundle must be absent: {}",
            legacy_path.display()
        ))
        .into()),
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err.into()),
    }
}

fn check_packaged_snapshot(
    root: &Path,
    rel: &str,
    expected: &str,
) -> Result<(), Box<dyn Error>> {
    let (pkg_dest, pkg_perms) = validate_destination_path(root, rel)?;
    if pkg_perms.is_none() {
        return Err(io::Error::other(format!(
            "missing staged packaged bundle: {}",
            pkg_dest.display()
        ))
        .into());
    }
    if fs::read(&pkg_dest)? != expected.as_bytes() {
        return Err(io::Error::other(format!(
            "{} is stale relative to its canonical sources; remove \
             trusted/cargo-anneal/packaged first, then re-stage with \
             --stage-package if publishing",
            pkg_dest.display()
        ))
        .into());
    }
    Ok(())
}

fn run(args: Args) -> Result<(), Box<dyn Error>> {
    let root = fs::canonicalize(args.root)?;
    reject_legacy_bundle(&root, LEGACY_BUNDLE_DESTINATION)?;
    reject_legacy_bundle(&root, LEGACY_THEORY_BUNDLE_DESTINATION)?;

    let expected_trusted = render_bundled_resources(&root)?;
    let expected_theory = render_bundled_theory(&root)?;

    if args.stage_package {
        let (pkg_trusted_dest, pkg_trusted_perms) = prepare_packaged_bundle_destination(&root)?;
        let (pkg_theory_dest, pkg_theory_perms) = prepare_packaged_theory_destination(&root)?;
        write_atomic(&pkg_trusted_dest, pkg_trusted_perms, &expected_trusted)?;
        write_atomic(&pkg_theory_dest, pkg_theory_perms, &expected_theory)?;
        return Ok(());
    }

    // Default invocation is now check-only; `--check` is retained as a
    // backwards-compatible CLI alias that verifies canonical sources and, if
    // `packaged/` is present, ensures both staged snapshots match.
    let _ = args.check;
    let packaged_dir = root.join("trusted/cargo-anneal/packaged");
    if fs::symlink_metadata(&packaged_dir).is_ok() {
        check_packaged_snapshot(&root, PACKAGED_BUNDLE_DESTINATION, &expected_trusted)?;
        check_packaged_snapshot(&root, PACKAGED_THEORY_BUNDLE_DESTINATION, &expected_theory)?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    run(Args::parse())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use cargo_anneal::bundle::{
        PROVENANCE_SOURCES, THEORY_BUNDLE_MANIFEST, TRUSTED_BUNDLE_SOURCES, TheoryBundleEntry,
        TheoryBundleManifest,
    };
    use cargo_anneal::sha256_bytes;
    use std::os::unix::fs::{PermissionsExt, symlink};
    use std::path::Path;

    fn repository(root: &Path) {
        for source in TRUSTED_BUNDLE_SOURCES {
            let path = root.join(source);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, format!("canonical bytes for {source}\n")).unwrap();
        }
        let theory_sources = [
            "theory/Anneal/MirWp.lean",
            "theory/Anneal/NatBitwise.lean",
        ];
        let mut entries = Vec::new();
        for source in theory_sources {
            let path = root.join(source);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            let bytes = format!("canonical bytes for {source}\n");
            fs::write(&path, &bytes).unwrap();
            entries.push(TheoryBundleEntry {
                path: source.to_owned(),
                sha256: sha256_bytes(bytes.as_bytes()),
            });
        }
        let manifest = TheoryBundleManifest {
            schema_version: 1,
            lean_toolchain: None,
            compatible_trusted_merkle_roots: None,
            min_mir_ast_wire_version: None,
            theory_merkle_root: None,
            modules: entries,
        };
        let manifest_path = root.join(THEORY_BUNDLE_MANIFEST);
        fs::create_dir_all(manifest_path.parent().unwrap()).unwrap();
        fs::write(
            manifest_path,
            format!("{}\n", serde_json::to_string_pretty(&manifest).unwrap()),
        )
        .unwrap();
        for source in PROVENANCE_SOURCES {
            let path = root.join(source);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            if *source == "vendor/lean-miri/UPSTREAM_PIN.json" {
                let sample_pin = r#"{
  "repository": "https://github.com/proofs-rs/lean-miri.git",
  "commit": "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a",
  "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
  "build_lean_toolchain": "leanprover/lean4:v4.34.1",
  "patched_files": [
    {
      "path": "Miri/Interpreter/Call.lean",
      "upstream_sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
      "patched_sha256": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
    }
  ]
}"#;
                fs::write(path, sample_pin).unwrap();
            } else {
                fs::write(path, format!("canonical bytes for {source}\n")).unwrap();
            }
        }
        fs::create_dir_all(root.join("trusted/cargo-anneal/src")).unwrap();
    }

    #[test]
    fn regeneration_preserves_outside_hard_link_and_output_permissions() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);
        let outside = fixture.path().join("outside.rs");
        let original = b"outside file must remain unchanged\n";
        fs::write(&outside, original).unwrap();
        fs::set_permissions(&outside, fs::Permissions::from_mode(0o640)).unwrap();
        let pkg_dir = root.join(PACKAGED_BUNDLE_DESTINATION).parent().unwrap().to_path_buf();
        fs::create_dir_all(&pkg_dir).unwrap();
        let pkg_destination = root.join(PACKAGED_BUNDLE_DESTINATION);
        fs::hard_link(&outside, &pkg_destination).unwrap();

        let outside_theory = fixture.path().join("outside.json");
        fs::write(&outside_theory, original).unwrap();
        fs::set_permissions(&outside_theory, fs::Permissions::from_mode(0o640)).unwrap();
        let theory_dest = root.join(PACKAGED_THEORY_BUNDLE_DESTINATION);
        fs::hard_link(&outside_theory, &theory_dest).unwrap();

        run(Args {
            root: root.clone(),
            check: false,
            stage_package: true,
        })
        .unwrap();
        run(Args {
            root: root.clone(),
            check: true,
            stage_package: false,
        })
        .unwrap();
        run(Args {
            root: root.clone(),
            check: false,
            stage_package: false,
        })
        .unwrap();

        assert_eq!(fs::read(&outside).unwrap(), original);
        assert_eq!(fs::read(&outside_theory).unwrap(), original);
        assert_eq!(
            fs::read(&pkg_destination).unwrap(),
            render_bundled_resources(&root).unwrap().as_bytes()
        );
        assert_eq!(
            fs::read(&theory_dest).unwrap(),
            render_bundled_theory(&root).unwrap().as_bytes()
        );
        assert_eq!(
            fs::metadata(pkg_destination).unwrap().permissions().mode() & 0o777,
            0o640
        );
        assert_eq!(
            fs::metadata(theory_dest).unwrap().permissions().mode() & 0o777,
            0o640
        );
    }

    #[test]
    fn all_modes_reject_legacy_checked_in_bundles() {
        for legacy_rel in [LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION] {
            let fixture = tempfile::tempdir().unwrap();
            let root = fixture.path().join("repository");
            repository(&root);
            fs::write(root.join(legacy_rel), b"legacy\n").unwrap();
            for (check, stage_package) in [(false, false), (true, false), (false, true)] {
                let error = run(Args {
                    root: root.clone(),
                    check,
                    stage_package,
                })
                .unwrap_err();
                assert!(error.to_string().contains("legacy checked-in bundle"), "{error}");
            }
        }
    }

    #[test]
    fn both_modes_reject_symlinked_output_without_changing_its_target() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);

        let outside = fixture.path().join("outside.rs");
        fs::write(&outside, b"outside sentinel\n").unwrap();
        let pkg_dest = root.join(PACKAGED_BUNDLE_DESTINATION);
        fs::create_dir_all(pkg_dest.parent().unwrap()).unwrap();
        symlink(&outside, &pkg_dest).unwrap();

        for (check, stage_package) in [(false, false), (true, false), (false, true)] {
            let error = run(Args {
                root: root.clone(),
                check,
                stage_package,
            })
            .unwrap_err();
            assert!(error.to_string().contains("regular file"), "{error}");
            assert_eq!(fs::read(&outside).unwrap(), b"outside sentinel\n");
        }
        fs::remove_file(&pkg_dest).unwrap();
        fs::write(&pkg_dest, render_bundled_resources(&root).unwrap().as_bytes()).unwrap();

        let outside_theory = fixture.path().join("outside.json");
        fs::write(&outside_theory, b"outside sentinel\n").unwrap();
        let theory_dest = root.join(PACKAGED_THEORY_BUNDLE_DESTINATION);
        symlink(&outside_theory, &theory_dest).unwrap();
        for (check, stage_package) in [(false, false), (true, false), (false, true)] {
            let error = run(Args {
                root: root.clone(),
                check,
                stage_package,
            })
            .unwrap_err();
            assert!(error.to_string().contains("regular file"), "{error}");
            assert_eq!(fs::read(&outside_theory).unwrap(), b"outside sentinel\n");
        }
    }

    #[test]
    fn both_modes_reject_symlinked_output_parent() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);
        let outside = fixture.path().join("outside");
        fs::create_dir(&outside).unwrap();
        let pkg_dir = root.join("trusted/cargo-anneal/packaged");
        symlink(&outside, &pkg_dir).unwrap();

        for (check, stage_package) in [(false, false), (true, false), (false, true)] {
            let error = run(Args {
                root: root.clone(),
                check,
                stage_package,
            })
            .unwrap_err();
            assert!(error.to_string().contains("regular directory"), "{error}");
            assert_eq!(fs::read_dir(&outside).unwrap().count(), 0);
        }
    }

    #[test]
    fn both_modes_reject_symlinked_bundle_source_and_parent() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);
        let outside_file = fixture.path().join("outside.lean");
        fs::write(&outside_file, b"-- outside\n").unwrap();

        // 1. Symlinked leaf source file listed in `THEORY_BUNDLE_MANIFEST` is rejected.
        let leaf = root.join("theory/Anneal/MirWp.lean");
        fs::remove_file(&leaf).unwrap();
        symlink(&outside_file, &leaf).unwrap();
        for (check, stage_package) in [(false, false), (true, false), (false, true)] {
            let error = run(Args {
                root: root.clone(),
                check,
                stage_package,
            })
            .unwrap_err();
            assert!(error.to_string().contains("regular file"), "{error}");
        }
        fs::remove_file(&leaf).unwrap();
        fs::write(&leaf, b"canonical bytes for theory/Anneal/MirWp.lean\n").unwrap();

        // 2. Symlinked parent directory of a theory source file is rejected.
        let outside_dir = fixture.path().join("outside-theory");
        fs::create_dir_all(&outside_dir).unwrap();
        fs::write(
            outside_dir.join("MirWp.lean"),
            b"canonical bytes for theory/Anneal/MirWp.lean\n",
        )
        .unwrap();
        let parent_dir = root.join("theory/Anneal");
        fs::remove_dir_all(&parent_dir).unwrap();
        symlink(&outside_dir, &parent_dir).unwrap();
        for (check, stage_package) in [(false, false), (true, false), (false, true)] {
            let error = run(Args {
                root: root.clone(),
                check,
                stage_package,
            })
            .unwrap_err();
            assert!(error.to_string().contains("regular directory"), "{error}");
        }
    }

    #[test]
    fn stage_package_leaves_no_packaged_dir_on_theory_bundle_failure() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);
        fs::write(root.join("theory/Anneal/MirWp.lean"), b"-- tampered\n").unwrap();

        let error = run(Args {
            root: root.clone(),
            check: false,
            stage_package: true,
        })
        .unwrap_err();
        assert!(error.to_string().contains("SHA-256 mismatch"), "{error}");
        assert!(
            !root.join("trusted/cargo-anneal/packaged").exists(),
            "theory validation failure must not leave empty packaged/ dir behind"
        );
    }

    #[test]
    fn check_reports_stage_package_remediation_for_stale_packaged_snapshot() {
        let fixture = tempfile::tempdir().unwrap();
        let root = fixture.path().join("repository");
        repository(&root);
        let pkg_dest = root.join(PACKAGED_BUNDLE_DESTINATION);
        let theory_pkg_dest = root.join(PACKAGED_THEORY_BUNDLE_DESTINATION);
        fs::create_dir_all(pkg_dest.parent().unwrap()).unwrap();
        fs::write(&pkg_dest, b"// stale packaged snapshot\n").unwrap();
        fs::write(&theory_pkg_dest, render_bundled_theory(&root).unwrap().as_bytes()).unwrap();

        let error = run(Args {
            root: root.clone(),
            check: true,
            stage_package: false,
        })
        .unwrap_err();
        let message = error.to_string();
        assert!(
            message.contains("remove trusted/cargo-anneal/packaged first")
                && message.contains("--stage-package")
                && !message.contains("without --check"),
            "{message}"
        );

        fs::write(&pkg_dest, render_bundled_resources(&root).unwrap().as_bytes()).unwrap();
        fs::write(&theory_pkg_dest, b"{}\n").unwrap();
        let error = run(Args {
            root: root.clone(),
            check: true,
            stage_package: false,
        })
        .unwrap_err();
        let message = error.to_string();
        assert!(
            message.contains("remove trusted/cargo-anneal/packaged first")
                && message.contains("--stage-package"),
            "{message}"
        );

        fs::remove_file(&theory_pkg_dest).unwrap();
        let error = run(Args {
            root,
            check: true,
            stage_package: false,
        })
        .unwrap_err();
        assert!(error.to_string().contains("missing staged packaged bundle"), "{error}");
    }
}
