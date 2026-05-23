// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Cargo package and target resolution for Anneal.
//!
//! Cargo selectors can identify several logical targets depending on package
//! layout: a library, named binaries, examples, and integration tests. Cargo
//! metadata also describes the output artifact kinds for each target, so one
//! library target can expose several crate types such as `rlib` and `cdylib`.
//!
//! This module resolves that metadata into one explicit Anneal artifact per
//! logical Cargo target and records the selector Charon must pass back to
//! Cargo. Downstream stages assign each selection its own LLBC path and Charon
//! configuration. This prevents distinct selected targets from sharing a
//! `--dest-file`, while avoiding duplicate translations of one library target
//! that happens to emit multiple crate types.

use anyhow::Context as _;
use sha2::Digest as _;

#[derive(clap::Parser, Debug)]
pub struct Args {
    #[command(flatten)]
    pub manifest: clap_cargo::Manifest,

    #[command(flatten)]
    pub workspace: clap_cargo::Workspace,

    #[command(flatten)]
    pub features: clap_cargo::Features,

    /// Verify the library target.
    #[arg(long)]
    pub lib: bool,

    /// Verify specific binary targets.
    #[arg(long)]
    pub bin: Vec<String>,

    /// Verify all binary targets.
    #[arg(long)]
    pub bins: bool,

    /// Verify specific example targets.
    #[arg(long)]
    pub example: Vec<String>,

    /// Verify all example targets.
    #[arg(long)]
    pub examples: bool,

    /// Verify specific test targets.
    #[arg(long)]
    pub test: Vec<String>,

    /// Verify all test targets.
    #[arg(long)]
    pub tests: bool,

    /// Permit Lean proof admissions (`sorry`, `admit`, or `sorryAx`).
    ///
    /// Without this explicit opt-in, generated Lean treats warnings as errors
    /// so every declaration which semantically depends on an admission fails.
    #[arg(long)]
    pub allow_sorry: bool,
}

/// A logical Cargo target selector that Charon can invoke.
///
/// Cargo metadata describes the artifact kinds emitted by a target. In
/// particular, one library target may list several crate types such as `rlib`
/// and `cdylib`. Charon's Cargo frontend selects that target with one Cargo
/// flag (`--lib`), not one flag per emitted crate type. Anneal therefore
/// normalizes every library-like artifact kind to [`Self::Lib`]. Named binary,
/// example, and test targets remain distinct because Charon selects them with
/// `--bin`, `--example`, and `--test`, respectively.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum AnnealTargetSelector {
    /// Select the package's library target with Cargo's `--lib` flag.
    Lib,
    /// Select a named binary target with Cargo's `--bin` flag.
    Bin,
    /// Select a named example target with Cargo's `--example` flag.
    Example,
    /// Select a named integration-test target with Cargo's `--test` flag.
    Test,
}

impl AnnealTargetSelector {
    /// Maps one Cargo metadata target to the selector Charon can use for it.
    fn for_cargo_target(
        target: &cargo_metadata::Target,
    ) -> anyhow::Result<Option<AnnealTargetSelector>> {
        let mut selector = None;

        for kind in &target.kind {
            use cargo_metadata::TargetKind::*;
            let candidate = match kind {
                // These are distinct rustc output artifact kinds, but Cargo and
                // Charon select their shared logical library target with
                // `--lib`. Cargo passes all configured crate types to one rustc
                // invocation, so returning one `Lib` prevents duplicate LLBC.
                Lib | RLib | ProcMacro | CDyLib | DyLib | StaticLib => Self::Lib,
                Bin => Self::Bin,
                Example => Self::Example,
                Test => Self::Test,
                // Need `_` because `TargetKind` is `#[non_exhaustive]`.
                Bench | CustomBuild | _ => continue,
            };

            match selector {
                None => selector = Some(candidate),
                Some(existing) if existing == candidate => {}
                Some(existing) => {
                    anyhow::bail!(
                        "Cargo target '{}' maps to incompatible Charon selectors {:?} and {:?}",
                        target.name,
                        existing,
                        candidate
                    );
                }
            }
        }

        Ok(selector)
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct AnnealTargetName {
    /// The Cargo package that owns this artifact.
    pub package_name: cargo_metadata::PackageName,
    /// The Cargo target name.
    pub target_name: String,
    /// The logical Cargo selector used to compile this artifact.
    ///
    /// This remains part of the identity so, for example, a library and binary
    /// with the same target name receive distinct Charon and Lean outputs.
    pub selector: AnnealTargetSelector,
}

/// A fully resolved target ready for verification.
///
/// This struct bridges the gap between `cargo_metadata`'s view of the world
/// and Anneal's verification pipeline. It contains absolute paths to critical
/// files, ensuring that downstream tools (Scanner, Charon) don't need to resolve
/// paths relative to the CWD or workspace root again.
#[derive(Debug)]
pub struct AnnealTarget {
    pub name: AnnealTargetName,
    pub selector: AnnealTargetSelector,

    /// Path to the `Cargo.toml` for this target.
    pub manifest_path: std::path::PathBuf,
}

#[derive(Debug)]
pub struct Roots {
    // E.g., `target/anneal`.
    anneal_global_root: std::path::PathBuf,
    // E.g., `target/anneal/<hash>`.
    anneal_run_root: std::path::PathBuf,
    pub roots: Vec<AnnealTarget>,
    pub metadata: cargo_metadata::Metadata,
}

impl Roots {
    pub fn lock_run_root(&self) -> anyhow::Result<LockedRoots<'_>> {
        let lock = crate::util::DirLock::lock_exclusive(self.anneal_run_root.clone())?;
        Ok(LockedRoots { roots: self, anneal_run_root: lock, llbc_override: None })
    }

    pub fn cargo_target_dir(&self) -> std::path::PathBuf {
        self.anneal_global_root.join("cargo_target")
    }
}

/// A wrapper around [`crate::resolve::Roots`] that proves the build lock is held.
///
/// This struct is the *only* way to access paths within the Anneal build
/// directory (e.g., LLBC output, Lean generation). This enforces that all
/// filesystem operations are guarded by the `BuildLock`.
pub struct LockedRoots<'a> {
    roots: &'a Roots,
    anneal_run_root: crate::util::DirLock,
    pub llbc_override: Option<std::path::PathBuf>,
}

impl<'a> LockedRoots<'a> {
    pub fn llbc_root(&self) -> std::path::PathBuf {
        if let Some(ref over) = self.llbc_override {
            over.clone()
        } else {
            self.anneal_run_root.path.join("llbc")
        }
    }

    // We expose the Cargo target directory for convenience, as it is used
    // by downstream tools like Charon to coordinate dependency artifacts.
    pub fn cargo_target_dir(&self) -> std::path::PathBuf {
        self.roots.cargo_target_dir()
    }
}

/// Resolves all verification roots.
///
/// Each entry represents a distinct logical Cargo target selection to verify.
/// Keeping this selection list explicit is deliberate: later Charon invocation
/// code should not have to rediscover which target a Cargo flag selects for a
/// particular workspace shape.
pub fn resolve_roots(args: &Args, toolchain: &crate::setup::Toolchain) -> anyhow::Result<Roots> {
    log::trace!("resolve_roots({:?})", args);
    let mut cmd = cargo_metadata::MetadataCommand::new();
    cmd.cargo_path(crate::setup::Tool::Cargo.path(toolchain))
        .env("RUSTC", crate::setup::Tool::Rustc.path(toolchain))
        .env(crate::setup::rust_library_path_env_var(), toolchain.rust_lib());

    if let Some(path) = &args.manifest.manifest_path {
        cmd.manifest_path(path);
    }

    // Forward features to ensure dependency resolution matches the user's
    // request. This is critical because conditional compilation
    // (via `#[cfg(feature = "...")]`) can completely change the shape of
    // the dependency graph and the source code itself. If we resolved
    // metadata without these flags, we might miss dependencies or include
    // dependencies that are not actually used in the build.
    args.features.forward_metadata(&mut cmd);

    let metadata = cmd.exec().context("Failed to run 'cargo metadata'")?;
    // We enforce that all local dependencies are contained within the workspace
    // root. This is a temporary limitation to simplify the verification model
    // and ensure a "hermetic-like" boundary for analysis. It prevents issues
    // where experimental or local forks of dependencies might be picked up
    // unpredictably, or where Charon might struggle to locate source files
    // outside the standard project structure.
    check_for_external_deps(&metadata)?;

    let selected_packages =
        resolve_packages(&metadata, &args.workspace, args.manifest.manifest_path.as_deref())?;

    let (anneal_global_root, anneal_run_root) = resolve_run_roots(&metadata);
    let mut roots = Roots {
        anneal_global_root,
        anneal_run_root,
        roots: Vec::new(),
        metadata: metadata.clone(), // `metadata` must outlive `selected_packages`.
    };

    for package in selected_packages {
        log::trace!("Scanning package: {}", package.name);

        let targets = resolve_targets(package, args)?;

        if targets.is_empty() {
            log::warn!("No matching targets found for package '{}'", package.name);
            continue;
        }

        roots.roots.extend(targets.into_iter().map(|(target, selector)| AnnealTarget {
            name: AnnealTargetName {
                package_name: package.name.clone(),
                target_name: target.name.clone(),
                selector,
            },
            selector,
            // We convert to absolute paths here to establish a canonical
            // reference for the rest of the pipeline. This avoids ambiguity
            // if the CWD changes or if we're working with complex workspace
            // structures.
            manifest_path: package.manifest_path.as_std_path().to_owned(),
        }));
    }

    Ok(roots)
}

fn resolve_run_roots(
    metadata: &cargo_metadata::Metadata,
) -> (std::path::PathBuf, std::path::PathBuf) {
    log::trace!("resolve_run_root");
    log::debug!("workspace_root: {:?}", metadata.workspace_root.as_std_path());
    // NOTE: Automatically handles `CARGO_TARGET_DIR` env var.
    let target_dir = metadata.target_directory.as_std_path();
    let anneal_global = target_dir.join("anneal");

    // Hash the path to the workspace root to avoid collisions between different
    // workspaces using the same target directory. We use SHA-256 (truncated to
    // 64 bits) for stable hashing across Rust versions. This ensures that the
    // build directory name remains consistent for the same workspace root,
    // avoiding unnecessary cache invalidation.
    let workspace_root_hash = {
        let mut hasher = sha2::Sha256::new();
        hasher.update(b"anneal_build_salt");
        hasher.update(metadata.workspace_root.as_str().as_bytes());
        let result = hasher.finalize();
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&result[0..8]);
        u64::from_le_bytes(bytes)
    };

    let run_root = anneal_global.join(format!("{workspace_root_hash:x}"));
    (anneal_global, run_root)
}

/// Resolves which packages to process based on workspace flags and CWD.
fn resolve_packages<'a>(
    metadata: &'a cargo_metadata::Metadata,
    args: &clap_cargo::Workspace,
    manifest_path: Option<&std::path::Path>,
) -> anyhow::Result<Vec<&'a cargo_metadata::Package>> {
    log::trace!("resolve_packages(workspace: {}, all: {})", args.workspace, args.all);
    let mut packages = if !args.package.is_empty() {
        // Resolve explicitly selected packages (-p / --package).
        args.package
            .iter()
            .map(|name| {
                metadata
                    .packages
                    .iter()
                    .find(|p| p.name == *name)
                    .ok_or_else(|| anyhow::anyhow!("Package '{}' not found in workspace", name))
            })
            .collect::<anyhow::Result<Vec<_>>>()?
    } else if args.workspace || args.all {
        // Resolve entire workspace (--workspace / --all). This explicitly
        // selects all workspace members, ignoring any packages that might be
        // in the graph but are not members (e.g. dependencies).
        metadata
            .workspace_members
            .iter()
            .filter_map(|id| metadata.packages.iter().find(|p| &p.id == id))
            .collect()
    } else {
        // Resolve Cargo's default package selection for the effective current
        // directory. At the workspace root Cargo selects `default-members`;
        // within an individual member it selects that package.
        let cwd = {
            let cwd_candidate = manifest_path
                .map(|p| p.to_path_buf())
                .unwrap_or_else(|| std::env::current_dir().unwrap_or_default())
                .canonicalize()
                .context("Failed to canonicalize CWD")?;

            // If the user explicitly provided `--manifest-path`, Cargo treats
            // its parent directory as the effective CWD.
            if manifest_path.is_some() {
                cwd_candidate.parent().unwrap_or(&cwd_candidate).to_path_buf()
            } else {
                cwd_candidate
            }
        };

        // Check the workspace root first. A non-virtual workspace root can
        // itself be a package, but Cargo still honors `default-members` there.
        if cwd == metadata.workspace_root.as_std_path() {
            metadata
                .workspace_default_members
                .iter()
                .filter_map(|id| metadata.packages.iter().find(|p| &p.id == id))
                .collect()
        } else {
            // Find the package whose manifest directory is an ancestor of CWD.
            metadata
                .packages
                .iter()
                .find(|p| {
                    let manifest_dir = p.manifest_path.parent().unwrap();
                    cwd.starts_with(manifest_dir)
                })
                .map(|package| vec![package])
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "Could not determine package from current directory. Please use -p <NAME> or --workspace."
                    )
                })?
        }
    };

    // Filter out excluded packages (--exclude).
    if !args.exclude.is_empty() {
        packages.retain(|p| !args.exclude.contains(&p.name));
    }

    Ok(packages)
}

/// Resolves the Cargo targets selected from one package.
///
/// Returns one `(Target, Selector)` pair per selected logical Cargo target.
/// A library target is returned once even when it emits multiple crate types,
/// because all of those artifacts are produced by the same `--lib` selection.
fn resolve_targets<'a>(
    package: &'a cargo_metadata::Package,
    args: &Args,
) -> anyhow::Result<Vec<(&'a cargo_metadata::Target, AnnealTargetSelector)>> {
    log::trace!("resolve_targets({})", package.name);
    let default_mode = !args.lib
        && args.bin.is_empty()
        && !args.bins
        && args.example.is_empty()
        && !args.examples
        && args.test.is_empty()
        && !args.tests;

    // Filter targets based on the requested verification mode.
    // Unlike Cargo, which might build everything by default, we try to be
    // selectively inclusive to avoid overwhelming the user with verification
    // tasks they didn't ask for.
    let mut selected_artifacts = Vec::new();
    for target in &package.targets {
        let Some(selector) = AnnealTargetSelector::for_cargo_target(target)? else {
            continue;
        };

        let include = if default_mode {
            matches!(selector, AnnealTargetSelector::Lib | AnnealTargetSelector::Bin)
        } else {
            (args.lib && selector == AnnealTargetSelector::Lib)
                || (args.bins && selector == AnnealTargetSelector::Bin)
                || (args.bin.contains(&target.name) && selector == AnnealTargetSelector::Bin)
                || (args.examples && selector == AnnealTargetSelector::Example)
                || (args.example.contains(&target.name)
                    && selector == AnnealTargetSelector::Example)
                || (args.tests && selector == AnnealTargetSelector::Test)
                || (args.test.contains(&target.name) && selector == AnnealTargetSelector::Test)
        };

        if include {
            selected_artifacts.push((target, selector));
        }
    }

    Ok(selected_artifacts)
}

/// Scans the package graph to ensure all local dependencies are contained
/// within the workspace root. Returns an error if an external path dependency
/// is found.
pub fn check_for_external_deps(metadata: &cargo_metadata::Metadata) -> anyhow::Result<()> {
    log::trace!("check_for_external_deps");
    // Canonicalize workspace root to handle symlinks correctly.
    let workspace_root = std::fs::canonicalize(&metadata.workspace_root)
        .context("Failed to canonicalize workspace root")?;

    for pkg in &metadata.packages {
        // We only care about packages that are "local" (source is None).
        // If source is Some(...), it's from crates.io or git, which is fine
        // (handled by Cargo).
        if pkg.source.is_none() {
            let pkg_path = pkg.manifest_path.as_std_path();

            // Canonicalize the package path for comparison.
            let canonical_pkg_path = std::fs::canonicalize(pkg_path)
                .with_context(|| format!("Failed to canonicalize path for package {}", pkg.name))?;

            // Check if the package lives outside the workspace tree.
            if !canonical_pkg_path.starts_with(&workspace_root) {
                anyhow::bail!(
                    "Unsupported external dependency: '{}' at {:?}.\n\
                     Anneal currently only supports verifying workspaces where all local \
                     dependencies are contained within the workspace root.",
                    pkg.name,
                    pkg_path
                );
            }
        }
    }

    Ok(())
}
