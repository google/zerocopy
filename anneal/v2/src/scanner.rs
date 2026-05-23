// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use sha2::Digest as _;

/// Controls target scanning scope.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ScanMode {
    /// Scan local workspace member crates only.
    WorkspaceOnly,
    /// Walk all source code crates in the dependency graph and emit LLBC.
    FollowDependencies,
}

/// Represents a compilation target (artifact) that needs to be processed.
///
/// In this rewrite, we no longer directly parse Rust files to extract annotations
/// or entry points. Instead, Charon compiles the entire target to generate LLBC
/// files, and annotations will be processed from LLBC directly at a later stage.
#[derive(Clone, Debug)]
pub struct AnnealArtifact {
    pub name: crate::resolve::AnnealTargetName,
    pub target_kind: crate::resolve::AnnealTargetKind,
    /// The path to the crate's `Cargo.toml`.
    pub manifest_path: std::path::PathBuf,
}

impl AnnealArtifact {
    /// Returns a unique, Lean-compatible "slug" for this artifact that matches
    /// the name that Aeneas will expect for the corresponding Lean module.
    ///
    /// Guarantees uniqueness based on manifest path even if multiple packages
    /// have the same name. The slug is guaranteed to be a valid Lean
    /// identifier (no hyphens).
    pub fn artifact_slug(&self) -> String {
        fn hash(data: &[u8]) -> u64 {
            let mut hasher = sha2::Sha256::new();
            hasher.update(data);
            let result = hasher.finalize();
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&result[0..8]);
            u64::from_le_bytes(bytes)
        }

        // Double-hash to make sure we can distinguish between e.g.
        // (manifest_path, target_name) = ("abc", "def") and ("ab", "cdef"),
        // which would hash identically if we just hashed their concatenation.
        //
        // Use SHA-256 not for security but rather stability – Rust's
        // `DefaultHasher` doesn't guarantee stability even across runs of the
        // same binary.
        //
        // `ANNEAL_HASH_WITH_REMOVED_PREFIX` allows our integration test
        // framework to strip the randomized sandbox prefix from the manifest
        // path before hashing, ensuring deterministic hashes even when running
        // in a sandboxed environment.
        let mut manifest_path_to_hash = self.manifest_path.as_path();
        if let Ok(prefix) = std::env::var("ANNEAL_HASH_WITH_REMOVED_PREFIX") {
            if let Ok(stripped) = self.manifest_path.strip_prefix(&prefix) {
                manifest_path_to_hash = stripped;
            }
        }
        let h0 = hash(manifest_path_to_hash.as_os_str().as_encoded_bytes());
        let h1 = hash(self.name.target_name.as_bytes());
        let h2 = hash(&[self.target_kind as u8]);
        let hashes = [h0, h1, h2];
        let h = hash(&hashes.map(u64::to_ne_bytes).concat());

        // Converts kebab-case -> PascalCase.
        // We convert both package and target names to PascalCase to ensure
        // the generated Lean module name is a valid and idiomatic Lean
        // identifier, matching Aeneas's output format.
        let to_pascal = |s: &str| {
            s.split(['-', '_'])
                .map(|segment| {
                    let mut chars = segment.chars();
                    match chars.next() {
                        None => String::new(),
                        Some(f) => f.to_uppercase().collect::<String>() + chars.as_str(),
                    }
                })
                .collect::<String>()
        };

        let pkg = to_pascal(self.name.package_name.as_str());
        let target = to_pascal(&self.name.target_name);

        // We use the hash to ensure uniqueness.
        format!("{}{}{:08x}", pkg, target, h)
    }

    /// Returns the name of the `.llbc` file to use for this artifact.
    pub fn llbc_file_name(&self) -> String {
        format!("{}.llbc", self.artifact_slug())
    }

    /// Returns the name of the `.lean` spec file to use for this artifact.
    #[allow(dead_code)]
    pub fn lean_spec_file_name(&self) -> String {
        format!("{}.lean", self.artifact_slug())
    }

    /// Returns the absolute path to the .llbc file.
    ///
    /// This method requires [`crate::resolve::LockedRoots`] to ensure that the caller holds the
    /// build lock before accessing the build artifact path.
    pub fn llbc_path(&self, roots: &crate::resolve::LockedRoots) -> std::path::PathBuf {
        roots.llbc_root().join(self.llbc_file_name())
    }
}

/// Scans the resolved workspace roots to identify the targets that need to be passed
/// to Charon. No Rust source code parsing is performed during this step.
pub fn scan_workspace(
    roots: &crate::resolve::Roots,
    mode: ScanMode,
) -> anyhow::Result<Vec<AnnealArtifact>> {
    let mut artifacts = Vec::new();
    for target in &roots.roots {
        artifacts.push(AnnealArtifact {
            name: target.name.clone(),
            target_kind: target.kind,
            manifest_path: target.manifest_path.clone(),
        });
    }

    if mode == ScanMode::FollowDependencies {
        for pkg in &roots.metadata.packages {
            // Skip workspace members to prevent duplication.
            if roots.metadata.workspace_members.contains(&pkg.id) {
                continue;
            }
            artifacts.push(AnnealArtifact {
                name: crate::resolve::AnnealTargetName {
                    package_name: pkg.name.clone(),
                    target_name: pkg.name.to_string(),
                    kind: crate::resolve::AnnealTargetKind::Lib,
                },
                target_kind: crate::resolve::AnnealTargetKind::Lib,
                manifest_path: pkg.manifest_path.as_std_path().to_owned(),
            });
        }
    }

    Ok(artifacts)
}
