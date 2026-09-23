// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use sha2::Digest as _;

/// Represents a compilation target (artifact) that needs to be processed.
///
/// Charon compiles the entire target to generate LLBC files. The generated
/// LLBC is the source of truth for processing Anneal annotations that affect
/// Aeneas code generation.
#[derive(Clone, Debug)]
pub struct AnnealArtifact {
    pub name: crate::resolve::AnnealTargetName,
    pub target_kind: crate::resolve::AnnealTargetKind,
    /// The path to the crate's `Cargo.toml`.
    pub manifest_path: std::path::PathBuf,
}

impl From<&crate::resolve::AnnealTarget> for AnnealArtifact {
    fn from(target: &crate::resolve::AnnealTarget) -> Self {
        Self {
            name: target.name.clone(),
            target_kind: target.kind,
            manifest_path: target.manifest_path.clone(),
        }
    }
}

impl AnnealArtifact {
    /// Returns a unique, Lean-compatible artifact slug.
    ///
    /// Charon uses the slug as the file stem for the target's emitted LLBC
    /// file. Later Aeneas/Lean stages can reuse the same Lean-compatible stem
    /// when associating generated Lean code with this artifact. The slug is
    /// guaranteed to be a valid Lean identifier (no hyphens), and is unique
    /// based on the manifest path, target name, and target kind.
    pub fn artifact_slug(&self) -> String {
        fn hash(data: &[u8]) -> u64 {
            // Use SHA-256 not for security but rather stability; Rust's
            // `DefaultHasher` doesn't guarantee stability even across runs of
            // the same binary.
            let mut hasher = sha2::Sha256::new();
            hasher.update(data);
            let result = hasher.finalize();
            let mut bytes = [0u8; 8];
            bytes.copy_from_slice(&result[0..8]);
            u64::from_le_bytes(bytes)
        }

        // Compute `hash([hash(manifest_path), hash(target_name), hash(target_kind)])` to
        // distinguish between e.g. (manifest_path, target_name) = ("abc", "def") and
        // ("ab", "cdef"), which would hash identically if we just hashed their
        // concatenation.
        let h0 = hash(self.manifest_path.as_os_str().as_encoded_bytes());
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

        // We use the hash to ensure uniqueness even if our prior `to_pascal`
        // mapping caused a collision.
        format!("{}{}{:08x}", pkg, target, h)
    }

    /// Returns the name of the `.llbc` file to use for this artifact.
    pub fn llbc_file_name(&self) -> String {
        format!("{}.llbc", self.artifact_slug())
    }

    /// Returns the absolute path to the .llbc file.
    ///
    /// This method requires [`crate::resolve::LockedRoots`] to ensure that the caller holds the
    /// build lock before accessing the build artifact path.
    pub fn llbc_path(&self, roots: &crate::resolve::LockedRoots) -> std::path::PathBuf {
        roots.llbc_root().join(self.llbc_file_name())
    }
}
