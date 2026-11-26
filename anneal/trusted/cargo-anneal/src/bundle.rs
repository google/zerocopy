// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical source inventory, deterministic rendering of audited
//! resources, and fail-closed runtime loading of external `--theory-dir` /
//! `--theory-archive` (`0`-TCB `Anneal.*` proof libraries).

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt as _;
use std::{
    fs,
    io::{self, Read as _},
    path::{Component, Path},
    process::{Command, Stdio},
};

use walkdir::WalkDir;

pub use crate::{
    theory_bundle::{
        BundledTheory, BundledTheoryModule, EXTERNAL_THEORY_MANIFEST_FILENAME,
        LEGACY_THEORY_BUNDLE_DESTINATION, PACKAGED_THEORY_BUNDLE_CRATE_REL,
        PACKAGED_THEORY_BUNDLE_DESTINATION, THEORY_BUNDLE_MANIFEST, TheoryBundleEntry,
        TheoryBundleManifest, compute_theory_merkle_root, load_theory_bundle_manifest,
        parse_bundled_theory, parse_theory_bundle_manifest_bytes,
        prepare_packaged_theory_destination, render_bundled_theory, validate_theory_compatibility,
    },
    trusted_bundle::{
        BUNDLE_HEADER, BundleError, CORRESPONDENCE_ADAPTER_DIR, CORRESPONDENCE_ADAPTER_PATHS,
        CORRESPONDENCE_PROOF_DIR, CORRESPONDENCE_PROOF_PATHS, CORRESPONDENCE_PROVENANCE_NOTE,
        CURRENT_MIR_AST_WIRE_VERSION, DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
        LEGACY_BUNDLE_DESTINATION, LOCKED_LEAN_TOOLCHAIN, PACKAGED_BUNDLE_CRATE_REL,
        PACKAGED_BUNDLE_DESTINATION, PROVENANCE_SOURCES, RenderedBundleParts,
        TRUSTED_BUNDLE_SOURCES, UPSTREAM_PIN_PATH, compute_trusted_merkle_root,
        prepare_packaged_bundle_destination, render_bundled_resources,
        render_bundled_resources_parts, render_correspondence_provenance,
        render_correspondence_provenance_from_checkout, validate_bundle_source,
        validate_destination_path, validate_parent_directories,
    },
};

const MAX_THEORY_FILE_BYTES: u64 = 16 * 1024 * 1024;
const MAX_THEORY_ARCHIVE_TOTAL_BYTES: u64 = 128 * 1024 * 1024;

/// Provenance tag identifying how the Pass 1 `theory/` bundle was resolved at
/// runtime (`Receipt v3` `theory_source`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalTheorySource {
    /// Loaded from an explicit `--theory-dir` or `ANNEAL_THEORY_DIR` directory.
    ExternalDir,
    /// Unpacked and validated from `--theory-archive`.
    ExternalArchive,
    /// Loaded from `<toolchain_root>/share/anneal/theory/`.
    ToolchainShare,
    /// Loaded from compile-time `bundled-theory` fallback.
    Embedded,
}

impl ExternalTheorySource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ExternalDir => "external_dir",
            Self::ExternalArchive => "external_archive",
            Self::ToolchainShare => "toolchain_share",
            Self::Embedded => "embedded",
        }
    }
}

/// Validated runtime `theory/` bundle ready for Pass 1 `TargetRole::Proof`
/// staging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedTheoryBundle {
    pub source: ExternalTheorySource,
    pub theory_merkle_root: String,
    pub bundle: BundledTheory,
}

#[cfg(feature = "bundled-theory")]
pub(crate) const EMBEDDED_THEORY_BUNDLE_JSON: &str =
    include_str!(concat!(env!("OUT_DIR"), "/bundled_theory.json"));

/// Return the parsed, self-verified [`BundledTheory`] generated into
/// `$OUT_DIR/bundled_theory.json` by `build.rs` when `bundled-theory` is on.
#[cfg(feature = "bundled-theory")]
pub fn embedded_theory_bundle() -> Result<BundledTheory, BundleError> {
    parse_bundled_theory(EMBEDDED_THEORY_BUNDLE_JSON)
}

fn read_regular_nofollow_bytes(path: &Path, max_bytes: u64) -> Result<Vec<u8>, BundleError> {
    let mut opts = fs::OpenOptions::new();
    opts.read(true);
    #[cfg(unix)]
    opts.custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC);
    let file = opts.open(path).map_err(|err| {
        #[cfg(unix)]
        if err.raw_os_error() == Some(libc::ELOOP) {
            return BundleError::Policy(format!(
                "symlink forbidden in external theory bundle: {}",
                path.display()
            ));
        }
        if err.kind() == io::ErrorKind::NotFound {
            BundleError::Policy(format!(
                "missing file in external theory bundle: {}",
                path.display()
            ))
        } else {
            BundleError::Io(err)
        }
    })?;
    let meta = file.metadata().map_err(BundleError::Io)?;
    if !meta.is_file() {
        return Err(BundleError::Policy(format!(
            "expected regular file in external theory bundle: {}",
            path.display()
        )));
    }
    if meta.len() > max_bytes {
        return Err(BundleError::Policy(format!(
            "theory file {} exceeds {} byte cap ({} bytes)",
            path.display(),
            max_bytes,
            meta.len()
        )));
    }
    let mut buf = Vec::with_capacity(meta.len() as usize);
    file.take(max_bytes + 1).read_to_end(&mut buf).map_err(BundleError::Io)?;
    if buf.len() as u64 > max_bytes {
        return Err(BundleError::Policy(format!(
            "theory file {} grew past {} byte cap while reading",
            path.display(),
            max_bytes
        )));
    }
    Ok(buf)
}

/// Load and fail-closed validate an external `--theory-dir <theory_dir>`
/// containing `bundle-manifest.json` and `Anneal/**/*.lean`.
///
/// Enforces:
/// 1. `theory_dir` and every ancestor under `Anneal/` are regular non-symlink
///    directories;
/// 2. `bundle-manifest.json` is `schema_version = 2` and passes fast-fail
///    compatibility checks against `expected_lean_toolchain`,
///    `expected_trusted_merkle_root`, and `current_mir_ast_wire_version`;
/// 3. Every listed `theory/Anneal/**/*.lean` file is opened via `O_NOFOLLOW`,
///    verified as `S_ISREG`, UTF-8 decoded, and SHA-256 matched against the
///    manifest; and
/// 4. No symlinks or unlisted `.lean` files exist anywhere inside `theory_dir`.
pub fn load_external_theory_dir(
    theory_dir: &Path,
    expected_lean_toolchain: &str,
    expected_trusted_merkle_root: &str,
    current_mir_ast_wire_version: u32,
    source_kind: ExternalTheorySource,
) -> Result<ResolvedTheoryBundle, BundleError> {
    let dir_meta = fs::symlink_metadata(theory_dir).map_err(|err| {
        if err.kind() == io::ErrorKind::NotFound {
            BundleError::Policy(format!(
                "external theory directory does not exist: {}",
                theory_dir.display()
            ))
        } else {
            BundleError::Io(err)
        }
    })?;
    if dir_meta.file_type().is_symlink() || !dir_meta.file_type().is_dir() {
        return Err(BundleError::Policy(format!(
            "external theory directory must be a regular non-symlink directory: {}",
            theory_dir.display()
        )));
    }

    let manifest_path = theory_dir.join(EXTERNAL_THEORY_MANIFEST_FILENAME);
    let label = manifest_path.display().to_string();
    let manifest_bytes = read_regular_nofollow_bytes(&manifest_path, MAX_THEORY_FILE_BYTES)?;
    let (manifest_sha256, manifest) = parse_theory_bundle_manifest_bytes(&manifest_bytes, &label)?;
    validate_theory_compatibility(
        &manifest,
        &label,
        expected_lean_toolchain,
        expected_trusted_merkle_root,
        current_mir_ast_wire_version,
        /*require_v2=*/ true,
    )?;

    // Walk `theory_dir` without following symlinks to reject any symlink or
    // special file (FIFOs, sockets, device nodes) anywhere in the tree.
    // Regular `.lean` files outside `bundle-manifest.json` (such as repository
    // `Canaries.lean` modules in `anneal/theory/`) are ignored and never
    // staged; only manifest-listed files enter the verified bundle below.
    for entry in WalkDir::new(theory_dir).follow_links(false).min_depth(1) {
        let entry = entry.map_err(|err| {
            let msg = err.to_string();
            err.into_io_error().map_or(BundleError::Policy(msg), BundleError::Io)
        })?;
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(BundleError::Policy(format!(
                "symlink forbidden inside external theory directory: {}",
                entry.path().display()
            )));
        }
        if !ft.is_dir() && !ft.is_file() {
            return Err(BundleError::Policy(format!(
                "non-regular file forbidden inside external theory directory: {}",
                entry.path().display()
            )));
        }
    }

    let theory_merkle_root = compute_theory_merkle_root(&manifest.modules);
    let mut modules = Vec::with_capacity(manifest.modules.len());
    for entry in &manifest.modules {
        let rel_inside_theory = entry.path.strip_prefix("theory/").ok_or_else(|| {
            BundleError::Policy(format!(
                "theory bundle path must start with theory/: {}",
                entry.path
            ))
        })?;
        validate_parent_directories(
            theory_dir,
            Path::new(rel_inside_theory),
            "external theory module parent",
        )?;
        let file_path = theory_dir.join(rel_inside_theory);
        let raw_bytes = read_regular_nofollow_bytes(&file_path, MAX_THEORY_FILE_BYTES)?;
        let content = String::from_utf8(raw_bytes).map_err(|err| {
            BundleError::Policy(format!(
                "non-UTF-8 source in external theory module {}: {err}",
                file_path.display()
            ))
        })?;
        let actual_sha = crate::trusted_bundle::sha256_bytes(content.as_bytes());
        if actual_sha != entry.sha256 {
            return Err(BundleError::Policy(format!(
                "external theory SHA-256 mismatch for {}: expected {}, got {actual_sha}",
                entry.path, entry.sha256
            )));
        }
        modules.push(BundledTheoryModule { path: entry.path.clone(), sha256: actual_sha, content });
    }

    Ok(ResolvedTheoryBundle {
        source: source_kind,
        theory_merkle_root: theory_merkle_root.clone(),
        bundle: BundledTheory {
            schema_version: manifest.schema_version,
            manifest_sha256,
            theory_merkle_root: Some(theory_merkle_root),
            lean_toolchain: manifest.lean_toolchain,
            compatible_trusted_merkle_roots: manifest.compatible_trusted_merkle_roots,
            min_mir_ast_wire_version: manifest.min_mir_ast_wire_version,
            modules,
        },
    })
}

fn unpack_validated_tar<R: io::Read>(reader: R, dest: &Path) -> Result<(), BundleError> {
    let mut archive = tar::Archive::new(reader);
    archive.set_preserve_permissions(false);
    archive.set_preserve_mtime(false);
    archive.set_unpack_xattrs(false);
    let mut total_bytes: u64 = 0;
    let entries = archive.entries().map_err(BundleError::Io)?;
    for entry_res in entries {
        let mut entry = entry_res.map_err(BundleError::Io)?;
        let entry_type = entry.header().entry_type();
        if !matches!(entry_type, tar::EntryType::Regular | tar::EntryType::Directory) {
            return Err(BundleError::Policy(format!(
                "disallowed non-regular tar entry type {entry_type:?} in theory archive"
            )));
        }
        let raw_path = entry.path().map_err(BundleError::Io)?.into_owned();
        if raw_path.is_absolute()
            || raw_path.components().any(|c| !matches!(c, Component::Normal(_) | Component::CurDir))
        {
            return Err(BundleError::Policy(format!(
                "unsafe path in theory archive: {}",
                raw_path.display()
            )));
        }
        let clean_comps: Vec<_> = raw_path
            .components()
            .filter_map(|c| match c {
                Component::Normal(seg) => Some(seg.to_os_string()),
                _ => None,
            })
            .collect();
        if clean_comps.is_empty() {
            continue;
        }
        // Strip an optional leading `theory/` prefix so archives created from
        // either `-C anneal theory` or `-C anneal/theory .` unpack identically.
        let rel_comps =
            if clean_comps[0] == "theory" { &clean_comps[1..] } else { &clean_comps[..] };
        if rel_comps.is_empty() {
            continue;
        }
        let mut out_path = dest.to_path_buf();
        for seg in rel_comps {
            out_path.push(seg);
        }
        if entry_type == tar::EntryType::Directory {
            fs::create_dir_all(&out_path).map_err(BundleError::Io)?;
            continue;
        }
        let size = entry.header().size().map_err(BundleError::Io)?;
        if size > MAX_THEORY_FILE_BYTES {
            return Err(BundleError::Policy(format!(
                "theory archive entry {} exceeds {} byte cap",
                raw_path.display(),
                MAX_THEORY_FILE_BYTES
            )));
        }
        total_bytes = total_bytes.saturating_add(size);
        if total_bytes > MAX_THEORY_ARCHIVE_TOTAL_BYTES {
            return Err(BundleError::Policy(format!(
                "theory archive exceeds {} byte total cap",
                MAX_THEORY_ARCHIVE_TOTAL_BYTES
            )));
        }
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent).map_err(BundleError::Io)?;
        }
        let mut out_file =
            fs::OpenOptions::new().write(true).create_new(true).open(&out_path).map_err(|e| {
                BundleError::Policy(format!(
                    "duplicate or colliding path in theory archive ({}): {e}",
                    raw_path.display()
                ))
            })?;
        io::copy(&mut entry, &mut out_file).map_err(BundleError::Io)?;
    }
    Ok(())
}

/// Unpack a CAS-safe `.tar` or `.tar.zst` `--theory-archive` into a private
/// temporary directory with strict regular-file validation and validate it via
/// [`load_external_theory_dir`].
///
/// Unlike `--theory-dir`, `archive_path` itself may be a Bazel runfiles symlink
/// pointing to a regular CAS blob (`fs::metadata` dereference), while every
/// member *inside* the archive must be a regular file or directory.
pub fn load_external_theory_archive(
    archive_path: &Path,
    expected_lean_toolchain: &str,
    expected_trusted_merkle_root: &str,
    current_mir_ast_wire_version: u32,
) -> Result<ResolvedTheoryBundle, BundleError> {
    let meta = fs::metadata(archive_path).map_err(|err| {
        if err.kind() == io::ErrorKind::NotFound {
            BundleError::Policy(format!(
                "external theory archive does not exist: {}",
                archive_path.display()
            ))
        } else {
            BundleError::Io(err)
        }
    })?;
    if !meta.is_file() {
        return Err(BundleError::Policy(format!(
            "external theory archive must resolve to a regular file: {}",
            archive_path.display()
        )));
    }

    let mut stage_builder = tempfile::Builder::new();
    stage_builder.prefix("anneal-theory-archive-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        stage_builder.permissions(fs::Permissions::from_mode(0o700));
    }
    let temp = stage_builder.tempdir().map_err(BundleError::Io)?;
    let name_lower =
        archive_path.file_name().and_then(|n| n.to_str()).unwrap_or("").to_ascii_lowercase();

    if name_lower.ends_with(".tar.zst") || name_lower.ends_with(".tzst") {
        // POSIX/GNU `tar` and Python `tarfile` pad archives past the two 512B
        // zero EOF blocks up to a record boundary (10 KiB by default, up to
        // 1 MiB with `-b 2048`). Drain bounded trailing padding before closing
        // the pipe so `zstd -dc` does not die with `SIGPIPE` on archives
        // larger than the OS pipe buffer.
        const MAX_TAR_TRAILING_PADDING_BYTES: u64 = 1024 * 1024;
        let in_file = fs::File::open(archive_path).map_err(BundleError::Io)?;
        let mut child = Command::new("zstd")
            .arg("-dc")
            .stdin(Stdio::from(in_file))
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| {
                BundleError::Policy(format!(
                    "cannot spawn zstd to decompress {}: {e}",
                    archive_path.display()
                ))
            })?;
        let mut stdout = child.stdout.take().expect("piped stdout");
        let unpack_res = unpack_validated_tar(&mut stdout, temp.path());
        let drain_res = if unpack_res.is_ok() {
            io::copy(&mut (&mut stdout).take(MAX_TAR_TRAILING_PADDING_BYTES + 1), &mut io::sink())
        } else {
            Ok(0)
        };
        drop(stdout);
        let output = child.wait_with_output().map_err(BundleError::Io)?;
        unpack_res?;
        let drained = drain_res.map_err(BundleError::Io)?;
        if drained > MAX_TAR_TRAILING_PADDING_BYTES {
            return Err(BundleError::Policy(format!(
                "theory archive {} exceeds {} bytes of trailing data after tar EOF",
                archive_path.display(),
                MAX_TAR_TRAILING_PADDING_BYTES
            )));
        }
        if !output.status.success() {
            return Err(BundleError::Policy(format!(
                "zstd decompression failed for {}: {}",
                archive_path.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
    } else if name_lower.ends_with(".tar") {
        let file = fs::File::open(archive_path).map_err(BundleError::Io)?;
        unpack_validated_tar(file, temp.path())?;
    } else {
        return Err(BundleError::Policy(format!(
            "unsupported theory archive extension for {} (expected .tar or .tar.zst)",
            archive_path.display()
        )));
    }

    load_external_theory_dir(
        temp.path(),
        expected_lean_toolchain,
        expected_trusted_merkle_root,
        current_mir_ast_wire_version,
        ExternalTheorySource::ExternalArchive,
    )
}

/// Resolve the runtime Pass 1 `theory/` bundle following Tier-1 precedence:
/// 1. Explicit `--theory-dir <dir>`
/// 2. Explicit `--theory-archive <path>`
/// 3. `ANNEAL_THEORY_DIR` environment variable
/// 4. Sibling `<toolchain_root>/share/anneal/theory/` (when present)
/// 5. Compile-time `bundled-theory` fallback (when feature-enabled)
pub fn resolve_runtime_theory_bundle(
    theory_dir: Option<&Path>,
    theory_archive: Option<&Path>,
    env_theory_dir: Option<&Path>,
    toolchain_share_theory_dir: Option<&Path>,
    expected_lean_toolchain: &str,
    expected_trusted_merkle_root: &str,
    current_mir_ast_wire_version: u32,
) -> Result<ResolvedTheoryBundle, BundleError> {
    if let Some(dir) = theory_dir {
        return load_external_theory_dir(
            dir,
            expected_lean_toolchain,
            expected_trusted_merkle_root,
            current_mir_ast_wire_version,
            ExternalTheorySource::ExternalDir,
        );
    }
    if let Some(archive) = theory_archive {
        return load_external_theory_archive(
            archive,
            expected_lean_toolchain,
            expected_trusted_merkle_root,
            current_mir_ast_wire_version,
        );
    }
    if let Some(env_dir) = env_theory_dir {
        return load_external_theory_dir(
            env_dir,
            expected_lean_toolchain,
            expected_trusted_merkle_root,
            current_mir_ast_wire_version,
            ExternalTheorySource::ExternalDir,
        );
    }
    if let Some(share_dir) = toolchain_share_theory_dir {
        let share_present = match fs::symlink_metadata(share_dir) {
            Ok(meta) => {
                meta.file_type().is_symlink()
                    || !meta.file_type().is_dir()
                    || fs::symlink_metadata(share_dir.join(EXTERNAL_THEORY_MANIFEST_FILENAME))
                        .is_ok()
            }
            Err(err) if err.kind() == io::ErrorKind::NotFound => false,
            Err(err) => return Err(BundleError::Io(err)),
        };
        if share_present {
            return load_external_theory_dir(
                share_dir,
                expected_lean_toolchain,
                expected_trusted_merkle_root,
                current_mir_ast_wire_version,
                ExternalTheorySource::ToolchainShare,
            );
        }
    }
    #[cfg(feature = "bundled-theory")]
    {
        let bundled = embedded_theory_bundle()?;
        let entries: Vec<TheoryBundleEntry> = bundled
            .modules
            .iter()
            .map(|m| TheoryBundleEntry { path: m.path.clone(), sha256: m.sha256.clone() })
            .collect();
        let merkle = bundled
            .theory_merkle_root
            .clone()
            .unwrap_or_else(|| compute_theory_merkle_root(&entries));
        if bundled.schema_version == 2 {
            let manifest = TheoryBundleManifest {
                schema_version: 2,
                lean_toolchain: bundled.lean_toolchain.clone(),
                compatible_trusted_merkle_roots: bundled.compatible_trusted_merkle_roots.clone(),
                min_mir_ast_wire_version: bundled.min_mir_ast_wire_version,
                theory_merkle_root: Some(merkle.clone()),
                modules: entries,
            };
            validate_theory_compatibility(
                &manifest,
                "embedded bundled_theory.json",
                expected_lean_toolchain,
                expected_trusted_merkle_root,
                current_mir_ast_wire_version,
                /*require_v2=*/ true,
            )?;
        }
        Ok(ResolvedTheoryBundle {
            source: ExternalTheorySource::Embedded,
            theory_merkle_root: merkle,
            bundle: bundled,
        })
    }
    #[cfg(not(feature = "bundled-theory"))]
    {
        Err(BundleError::Policy(
            "no external theory bundle configured: pass --theory-dir <DIR>, \
             --theory-archive <ARCHIVE>, or set ANNEAL_THEORY_DIR \
             (cargo-anneal was built without the `bundled-theory` feature)"
                .to_owned(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::theory_bundle::REQUIRED_THEORY_BUNDLE_PATH;

    #[test]
    fn provenance_sources_match_component_lists() {
        let expected: Vec<&str> = std::iter::once(UPSTREAM_PIN_PATH)
            .chain(CORRESPONDENCE_ADAPTER_PATHS.iter().copied())
            .chain(CORRESPONDENCE_PROOF_PATHS.iter().copied())
            .collect();
        assert_eq!(PROVENANCE_SOURCES, expected.as_slice());
        assert_eq!(
            DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
            crate::core::inspect::schema::DECOUPLED_CORRESPONDENCE_PROVENANCE_REASON,
        );
    }

    #[cfg(feature = "bundled-theory")]
    #[test]
    fn embedded_theory_bundle_is_self_consistent() {
        let bundled = embedded_theory_bundle().expect("embedded theory bundle must verify");
        assert!(matches!(bundled.schema_version, 1 | 2));
        assert!(bundled.modules.iter().any(|m| m.path == REQUIRED_THEORY_BUNDLE_PATH));
    }

    #[test]
    fn parse_bundled_theory_rejects_tampered_and_invalid_payloads() {
        let m0_src = "-- synthetic MirWp\n".to_owned();
        let m1_src = "-- synthetic NatBitwise\n".to_owned();
        let m0_sha = crate::trusted_bundle::sha256_bytes(m0_src.as_bytes());
        let m1_sha = crate::trusted_bundle::sha256_bytes(m1_src.as_bytes());
        let valid = BundledTheory {
            schema_version: 1,
            manifest_sha256: "a".repeat(64),
            theory_merkle_root: None,
            lean_toolchain: None,
            compatible_trusted_merkle_roots: None,
            min_mir_ast_wire_version: None,
            modules: vec![
                BundledTheoryModule {
                    path: REQUIRED_THEORY_BUNDLE_PATH.to_owned(),
                    sha256: m0_sha,
                    content: m0_src,
                },
                BundledTheoryModule {
                    path: "theory/Anneal/NatBitwise.lean".to_owned(),
                    sha256: m1_sha,
                    content: m1_src,
                },
            ],
        };
        parse_bundled_theory(&serde_json::to_string(&valid).unwrap()).unwrap();

        let mut tampered = valid.clone();
        tampered.modules[0].content.push_str("\n-- tampered\n");
        let err = parse_bundled_theory(&serde_json::to_string(&tampered).unwrap()).unwrap_err();
        assert!(err.to_string().contains("SHA-256 mismatch"), "{err}");

        let mut dup = valid.clone();
        let first = dup.modules[0].clone();
        dup.modules.push(first);
        let err = parse_bundled_theory(&serde_json::to_string(&dup).unwrap()).unwrap_err();
        assert!(err.to_string().contains("duplicate theory bundle path"), "{err}");

        let mut unsorted = valid.clone();
        unsorted.modules.swap(0, 1);
        let err = parse_bundled_theory(&serde_json::to_string(&unsorted).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsorted theory bundle entry"), "{err}");

        let mut escaped = valid.clone();
        escaped.modules[0].path = "trusted/lean/Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&escaped).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must reside under theory/Anneal/"), "{err}");

        let mut traversal = valid.clone();
        traversal.modules[0].path = "theory/Anneal/../Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&traversal).unwrap()).unwrap_err();
        assert!(err.to_string().contains("invalid relative theory bundle path"), "{err}");

        let mut umbrella = valid.clone();
        umbrella.modules[0].path = "theory/Anneal.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&umbrella).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must name a module under theory/Anneal/"), "{err}");

        let mut missing_required = valid;
        missing_required.modules.retain(|m| m.path != REQUIRED_THEORY_BUNDLE_PATH);
        let err =
            parse_bundled_theory(&serde_json::to_string(&missing_required).unwrap()).unwrap_err();
        assert!(err.to_string().contains("missing required theory module"), "{err}");
    }

    #[test]
    fn external_theory_dir_and_archive_enforce_fail_closed_manifest_and_merkle_checks() {
        let tmp = tempfile::tempdir().unwrap();
        let theory_dir = tmp.path().join("theory");
        let anneal_sub = theory_dir.join("Anneal");
        fs::create_dir_all(&anneal_sub).unwrap();

        let mir_wp_src = "module\nprelude\n";
        let nat_bw_src = "module\nprelude\n-- helper\n";
        fs::write(anneal_sub.join("MirWp.lean"), mir_wp_src.as_bytes()).unwrap();
        fs::write(anneal_sub.join("NatBitwise.lean"), nat_bw_src.as_bytes()).unwrap();

        let entries = vec![
            TheoryBundleEntry {
                path: "theory/Anneal/MirWp.lean".to_owned(),
                sha256: crate::trusted_bundle::sha256_bytes(mir_wp_src.as_bytes()),
            },
            TheoryBundleEntry {
                path: "theory/Anneal/NatBitwise.lean".to_owned(),
                sha256: crate::trusted_bundle::sha256_bytes(nat_bw_src.as_bytes()),
            },
        ];
        let merkle = compute_theory_merkle_root(&entries);
        let trusted_root = "7".repeat(64);
        let manifest = TheoryBundleManifest {
            schema_version: 2,
            lean_toolchain: Some(LOCKED_LEAN_TOOLCHAIN.to_owned()),
            compatible_trusted_merkle_roots: Some(vec![trusted_root.clone()]),
            min_mir_ast_wire_version: Some(CURRENT_MIR_AST_WIRE_VERSION),
            theory_merkle_root: Some(merkle.clone()),
            modules: entries,
        };
        let manifest_path = theory_dir.join(EXTERNAL_THEORY_MANIFEST_FILENAME);
        fs::write(
            &manifest_path,
            format!("{}\n", serde_json::to_string_pretty(&manifest).unwrap()),
        )
        .unwrap();

        // 1. Valid external `--theory-dir` succeeds.
        let loaded = load_external_theory_dir(
            &theory_dir,
            LOCKED_LEAN_TOOLCHAIN,
            &trusted_root,
            CURRENT_MIR_AST_WIRE_VERSION,
            ExternalTheorySource::ExternalDir,
        )
        .expect("valid external theory dir must load");
        assert_eq!(loaded.source, ExternalTheorySource::ExternalDir);
        assert_eq!(loaded.theory_merkle_root, merkle);
        assert_eq!(loaded.bundle.modules.len(), 2);

        // 2. Incompatible Ring-0 Trusted/ Merkle root fails closed immediately.
        let wrong_trusted = "8".repeat(64);
        let err = load_external_theory_dir(
            &theory_dir,
            LOCKED_LEAN_TOOLCHAIN,
            &wrong_trusted,
            CURRENT_MIR_AST_WIRE_VERSION,
            ExternalTheorySource::ExternalDir,
        )
        .unwrap_err();
        assert!(
            err.to_string().contains("incompatible with embedded Ring-0 Trusted/ Merkle root"),
            "{err}"
        );

        // 3. Incompatible Lean toolchain fails closed immediately.
        let err = load_external_theory_dir(
            &theory_dir,
            "leanprover/lean4:v4.35.0",
            &trusted_root,
            CURRENT_MIR_AST_WIRE_VERSION,
            ExternalTheorySource::ExternalDir,
        )
        .unwrap_err();
        assert!(err.to_string().contains("lean_toolchain"), "{err}");

        // 4. Higher required MirAst wire version fails closed immediately.
        let err = load_external_theory_dir(
            &theory_dir,
            LOCKED_LEAN_TOOLCHAIN,
            &trusted_root,
            CURRENT_MIR_AST_WIRE_VERSION - 1,
            ExternalTheorySource::ExternalDir,
        )
        .unwrap_err();
        assert!(err.to_string().contains("min_mir_ast_wire_version"), "{err}");

        // 5. Unlisted repo-only `.lean` file (e.g. `Canaries.lean`) inside
        //    `--theory-dir` is ignored and never staged into the bundle.
        let canary_only = anneal_sub.join("Canaries.lean");
        fs::write(&canary_only, b"module\nprelude\n").unwrap();
        let loaded_with_canary = load_external_theory_dir(
            &theory_dir,
            LOCKED_LEAN_TOOLCHAIN,
            &trusted_root,
            CURRENT_MIR_AST_WIRE_VERSION,
            ExternalTheorySource::ExternalDir,
        )
        .expect("unlisted repo-only Canaries.lean must be ignored, not staged");
        assert_eq!(loaded_with_canary.bundle.modules.len(), 2);
        assert!(
            loaded_with_canary.bundle.modules.iter().all(|m| !m.path.ends_with("Canaries.lean"))
        );
        fs::remove_file(&canary_only).unwrap();

        // 6. Symlink inside `--theory-dir` fails closed (`O_NOFOLLOW` + walk).
        #[cfg(unix)]
        {
            let outside = tmp.path().join("outside.lean");
            fs::write(&outside, mir_wp_src.as_bytes()).unwrap();
            let sym = anneal_sub.join("Sym.lean");
            std::os::unix::fs::symlink(&outside, &sym).unwrap();
            let err = load_external_theory_dir(
                &theory_dir,
                LOCKED_LEAN_TOOLCHAIN,
                &trusted_root,
                CURRENT_MIR_AST_WIRE_VERSION,
                ExternalTheorySource::ExternalDir,
            )
            .unwrap_err();
            assert!(err.to_string().contains("symlink forbidden"), "{err}");
            fs::remove_file(&sym).unwrap();
        }

        // 7. Valid `.tar` and `.tar.zst` `--theory-archive` (including via a
        //    Bazel-style runfiles symlink!) succeed.
        // Include an unstaged >256 KiB repo-only `Canaries.lean` file plus
        // 9,216 bytes of GNU-tar 10 KiB record padding after the two 512B EOF
        // blocks so the uncompressed stream exceeds the 64 KiB OS pipe buffer
        // and drains trailing padding without `zstd -dc` hitting `SIGPIPE`.
        let big_canary = format!("module\nprelude\n-- {}\n", "x".repeat(300 * 1024));
        fs::write(anneal_sub.join("Canaries.lean"), big_canary.as_bytes()).unwrap();
        let tar_path = tmp.path().join("theory.tar");
        {
            let tar_file = fs::File::create(&tar_path).unwrap();
            let mut builder = tar::Builder::new(tar_file);
            builder.append_dir_all("theory", &theory_dir).unwrap();
            builder.finish().unwrap();
        }
        let zst_path = tmp.path().join("theory.tar.zst");
        {
            let mut raw_tar = fs::read(&tar_path).unwrap();
            raw_tar.extend(std::iter::repeat_n(0u8, 9216));
            let compressed = zstd::encode_all(raw_tar.as_slice(), 1).unwrap();
            fs::write(&zst_path, compressed).unwrap();
        }
        #[cfg(unix)]
        {
            let runfiles_link = tmp.path().join("bazel-runfiles-theory.tar.zst");
            std::os::unix::fs::symlink(&zst_path, &runfiles_link).unwrap();
            let from_archive = load_external_theory_archive(
                &runfiles_link,
                LOCKED_LEAN_TOOLCHAIN,
                &trusted_root,
                CURRENT_MIR_AST_WIRE_VERSION,
            )
            .expect("CAS symlink to regular .tar.zst archive must load");
            assert_eq!(from_archive.source, ExternalTheorySource::ExternalArchive);
            assert_eq!(from_archive.theory_merkle_root, merkle);
            assert_eq!(from_archive.bundle, loaded.bundle);
        }

        // 8. Source tampering inside `--theory-dir` fails closed on SHA-256
        //    mismatch.
        fs::write(anneal_sub.join("NatBitwise.lean"), b"module\nprelude\n-- tampered!\n").unwrap();
        let err = load_external_theory_dir(
            &theory_dir,
            LOCKED_LEAN_TOOLCHAIN,
            &trusted_root,
            CURRENT_MIR_AST_WIRE_VERSION,
            ExternalTheorySource::ExternalDir,
        )
        .unwrap_err();
        assert!(err.to_string().contains("SHA-256 mismatch"), "{err}");

        // 9. Broken `share/anneal/theory` symlink must fail closed rather than
        //    silently falling back to `bundled-theory`.
        #[cfg(unix)]
        {
            let broken_share = tmp.path().join("broken-share-theory");
            std::os::unix::fs::symlink(tmp.path().join("nonexistent-target"), &broken_share)
                .unwrap();
            let err = resolve_runtime_theory_bundle(
                None,
                None,
                None,
                Some(&broken_share),
                LOCKED_LEAN_TOOLCHAIN,
                &trusted_root,
                CURRENT_MIR_AST_WIRE_VERSION,
            )
            .unwrap_err();
            assert!(err.to_string().contains("regular non-symlink directory"), "{err}");
        }
    }

    #[cfg(not(feature = "bundled-theory"))]
    #[test]
    fn resolve_without_external_theory_fails_closed_without_bundled_theory() {
        let tmp = tempfile::tempdir().unwrap();
        let missing_share = tmp.path().join("absent/share/anneal/theory");
        for share in [None, Some(missing_share.as_path())] {
            let err = resolve_runtime_theory_bundle(
                None,
                None,
                None,
                share,
                LOCKED_LEAN_TOOLCHAIN,
                &"7".repeat(64),
                CURRENT_MIR_AST_WIRE_VERSION,
            )
            .unwrap_err();
            assert!(
                err.to_string().contains("built without the `bundled-theory` feature"),
                "{err}"
            );
        }
    }

    #[test]
    fn theory_bundle_identifier_helpers_match_core() {
        for ident in [
            "",
            "A",
            "MirWp",
            "Step_Wp2",
            "_leading_underscore",
            "2leading_digit",
            "with-hyphen",
            "with.dot",
            "with space",
            "αβγ",
        ] {
            assert_eq!(
                crate::theory_bundle::is_lean_ident(ident),
                crate::core::is_lean_ident(ident),
                "is_lean_ident mismatch on {ident:?}"
            );
        }
        for path in [
            "",
            "a",
            "theory/Anneal/MirWp.lean",
            "/abs/path",
            "./dot",
            "a/./b",
            "a/../b",
            "..",
            ".",
            "a//b",
            "a/b/",
        ] {
            assert_eq!(
                crate::theory_bundle::is_clean_relative_path(path),
                crate::core::is_clean_relative_path(path),
                "is_clean_relative_path mismatch on {path:?}"
            );
        }
    }
}
