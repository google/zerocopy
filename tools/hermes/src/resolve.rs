use std::{
    env, fs,
    hash::{Hash as _, Hasher as _},
    path::PathBuf,
};

use anyhow::{anyhow, Context, Result};
use cargo_metadata::{Metadata, MetadataCommand, Package, PackageName, Target, TargetKind};
use clap::Parser;

#[derive(Parser, Debug)]
pub struct Args {
    #[command(flatten)]
    pub manifest: clap_cargo::Manifest,

    #[command(flatten)]
    pub workspace: clap_cargo::Workspace,

    #[command(flatten)]
    pub features: clap_cargo::Features,

    /// Verify the library target
    #[arg(long)]
    pub lib: bool,

    /// Verify specific binary targets
    #[arg(long)]
    pub bin: Vec<String>,

    /// Verify all binary targets
    #[arg(long)]
    pub bins: bool,

    /// Verify specific example targets
    #[arg(long)]
    pub example: Vec<String>,

    /// Verify all example targets
    #[arg(long)]
    pub examples: bool,

    /// Verify specific test targets
    #[arg(long)]
    pub test: Vec<String>,

    /// Verify all test targets
    #[arg(long)]
    pub tests: bool,

    /// Allow `sorry` in proofs and inject `sorry` for missing proofs
    #[arg(long)]
    pub allow_sorry: bool,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum HermesTargetKind {
    /// A library target (generic).
    Lib,
    /// A Rust library.
    RLib,
    /// A procedural macro library.
    ProcMacro,
    /// A C-compatible dynamic library.
    CDyLib,
    /// A dynamic Rust library.
    DyLib,
    /// A static system library.
    StaticLib,
    /// A binary executable.
    Bin,
    /// A documentation example.
    Example,
    /// An integration test.
    Test,
}

impl HermesTargetKind {
    pub fn is_lib(&self) -> bool {
        use HermesTargetKind::*;
        matches!(self, Lib | RLib | ProcMacro | CDyLib | DyLib | StaticLib)
    }
}

impl TryFrom<&TargetKind> for HermesTargetKind {
    type Error = ();

    fn try_from(kind: &TargetKind) -> Result<Self, Self::Error> {
        use TargetKind::*;
        match kind {
            Lib => Ok(Self::Lib),
            RLib => Ok(Self::RLib),
            ProcMacro => Ok(Self::ProcMacro),
            CDyLib => Ok(Self::CDyLib),
            DyLib => Ok(Self::DyLib),
            StaticLib => Ok(Self::StaticLib),
            Bin => Ok(Self::Bin),
            Example => Ok(Self::Example),
            Test => Ok(Self::Test),
            // Need `_` because `TargetKind` is `#[non_exhaustive]`.
            Bench | CustomBuild | _ => Err(()),
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct HermesTargetName {
    pub package_name: PackageName,
    pub target_name: String,
    pub kind: HermesTargetKind,
}

#[derive(Debug)]
pub struct HermesTarget {
    pub name: HermesTargetName,
    pub kind: HermesTargetKind,
    /// Path to the main source file for this target.
    pub src_path: PathBuf,
    /// Path to the `Cargo.toml` for this target.
    pub manifest_path: PathBuf,
}

#[derive(Debug)]
pub struct Roots {
    pub workspace: PathBuf,
    // E.g., `target/hermes`.
    hermes_global_root: PathBuf,
    // E.g., `target/hermes/<hash>`.
    hermes_run_root: PathBuf,
    pub roots: Vec<HermesTarget>,
}

impl Roots {
    pub fn llbc_root(&self) -> PathBuf {
        self.hermes_run_root.join("llbc")
    }

    pub fn lean_generated_root(&self) -> PathBuf {
        self.hermes_run_root.join("lean").join("generated")
    }

    pub fn cargo_target_dir(&self) -> PathBuf {
        self.hermes_global_root.join("cargo_target")
    }
}

/// Resolves all verification roots.
///
/// Each entry represents a distinct compilation artifact to be verified.
pub fn resolve_roots(args: &Args) -> Result<Roots> {
    log::trace!("resolve_roots({:?})", args);
    let mut cmd = MetadataCommand::new();

    if let Some(path) = &args.manifest.manifest_path {
        cmd.manifest_path(path);
    }

    // Forward features to ensure dependency resolution matches the user's
    // request.
    args.features.forward_metadata(&mut cmd);

    let metadata = cmd.exec().context("Failed to run 'cargo metadata'")?;
    check_for_external_deps(&metadata)?;

    let selected_packages = resolve_packages(&metadata, &args.workspace)?;

    let (hermes_global_root, hermes_run_root) = resolve_run_roots(&metadata);
    let mut roots = Roots {
        workspace: metadata.workspace_root.as_std_path().to_owned(),
        // cargo_target_dir: metadata.target_directory.as_std_path().to_owned(),
        hermes_global_root,
        hermes_run_root,
        roots: Vec::new(),
    };

    for package in selected_packages {
        log::trace!("Scanning package: {}", package.name);

        let targets = resolve_targets(package, args)?;

        if targets.is_empty() {
            log::warn!("No matching targets found for package '{}'", package.name);
            continue;
        }

        roots.roots.extend(targets.into_iter().map(|(target, kind)| HermesTarget {
            name: HermesTargetName {
                package_name: package.name.clone(),
                target_name: target.name.clone(),
                kind,
            },
            kind,
            src_path: target.src_path.as_std_path().to_owned(),
            manifest_path: package.manifest_path.as_std_path().to_owned(),
        }));
    }

    Ok(roots)
}

fn resolve_run_roots(metadata: &Metadata) -> (PathBuf, PathBuf) {
    log::trace!("resolve_run_root");
    log::debug!("workspace_root: {:?}", metadata.workspace_root.as_std_path());
    // NOTE: Automatically handles `CARGO_TARGET_DIR` env var.
    let target_dir = metadata.target_directory.as_std_path();
    let hermes_global = target_dir.join("hermes");

    // Used by integration tests to ensure deterministic shadow dir names.
    if let Ok(name) = std::env::var("HERMES_TEST_DIR_NAME") {
        let run_root = hermes_global.join(name);
        return (hermes_global, run_root);
    }

    // Hash the path to the workspace root to avoid collisions between different
    // workspaces using the same target directory.
    let workspace_root_hash = {
        let mut hasher = std::hash::DefaultHasher::new();
        hasher.write(b"hermes_build_salt");
        metadata.workspace_root.hash(&mut hasher);
        hasher.finish()
    };

    let run_root = hermes_global.join(format!("{workspace_root_hash:x}"));
    (hermes_global, run_root)
}

/// Resolves which packages to process based on workspace flags and CWD.
fn resolve_packages<'a>(
    metadata: &'a Metadata,
    args: &clap_cargo::Workspace,
) -> Result<Vec<&'a Package>> {
    log::trace!("resolve_packages(workspace: {}, all: {})", args.workspace, args.all);
    let mut packages = if !args.package.is_empty() {
        // Resolve explicitly selected packages (-p / --package)
        args.package
            .iter()
            .map(|name| {
                metadata
                    .packages
                    .iter()
                    .find(|p| p.name == *name)
                    .ok_or_else(|| anyhow!("Package '{}' not found in workspace", name))
            })
            .collect::<Result<Vec<_>>>()?
    } else if args.workspace || args.all {
        // Resolve entire workspace (--workspace / --all)
        metadata
            .workspace_members
            .iter()
            .filter_map(|id| metadata.packages.iter().find(|p| &p.id == id))
            .collect()
    } else {
        // Resolve default (Current Working Directory)
        let cwd = env::current_dir()
            .context("Failed to get CWD")?
            .canonicalize()
            .context("Failed to canonicalize CWD")?;

        // Find the package whose manifest directory is an ancestor of CWD
        let current_pkg = metadata.packages.iter().find(|p| {
            let manifest_dir = p.manifest_path.parent().unwrap();
            cwd.starts_with(manifest_dir)
        });

        if let Some(pkg) = current_pkg {
            vec![pkg]
        } else {
            // Fallback: If we are at the workspace root (virtual manifest),
            // behave like --workspace.
            if cwd == metadata.workspace_root.as_std_path() {
                metadata
                    .workspace_members
                    .iter()
                    .filter_map(|id| metadata.packages.iter().find(|p| &p.id == id))
                    .collect()
            } else {
                return Err(anyhow!(
                    "Could not determine package from current directory. Please use -p <NAME> or --workspace."
                ));
            }
        }
    };

    // Filter out excluded packages (--exclude)
    if !args.exclude.is_empty() {
        packages.retain(|p| !args.exclude.contains(&p.name));
    }

    Ok(packages)
}

/// Flattening Resolver:
/// Returns a list of (Target, TargetKind) pairs.
/// If a target is defined as `crate-type = ["rlib", "cdylib"]`, and both are requested,
/// this returns two entries, allowing them to be verified independently.
fn resolve_targets<'a>(
    package: &'a Package,
    args: &Args,
) -> Result<Vec<(&'a Target, HermesTargetKind)>> {
    log::trace!("resolve_targets({})", package.name);
    let default_mode = !args.lib
        && args.bin.is_empty()
        && !args.bins
        && args.example.is_empty()
        && !args.examples
        && args.test.is_empty()
        && !args.tests;

    let selected_artifacts: Vec<_> = package
        .targets
        .iter()
        .flat_map(|target| {
            target.kind.iter().filter_map(move |raw_kind| {
                let kind = HermesTargetKind::try_from(raw_kind).ok()?;

                let include = if default_mode {
                    kind.is_lib() || kind == HermesTargetKind::Bin
                } else {
                    (args.lib && kind.is_lib())
                        || (args.bins && kind == HermesTargetKind::Bin)
                        || (args.bin.contains(&target.name) && kind == HermesTargetKind::Bin)
                        || (args.examples && kind == HermesTargetKind::Example)
                        || (args.example.contains(&target.name)
                            && kind == HermesTargetKind::Example)
                        || (args.tests && kind == HermesTargetKind::Test)
                        || (args.test.contains(&target.name) && kind == HermesTargetKind::Test)
                };

                include.then_some((target, kind))
            })
        })
        .collect();

    Ok(selected_artifacts)
}

// TODO: Eventually, we'll want to support external path dependencies by
// analyzing them in-place or ensuring they are accessible to Charon.

/// Scans the package graph to ensure all local dependencies are contained
/// within the workspace root. Returns an error if an external path dependency
/// is found.
pub fn check_for_external_deps(metadata: &Metadata) -> Result<()> {
    log::trace!("check_for_external_deps");
    // Canonicalize workspace root to handle symlinks correctly
    let workspace_root = fs::canonicalize(&metadata.workspace_root)
        .context("Failed to canonicalize workspace root")?;

    for pkg in &metadata.packages {
        // We only care about packages that are "local" (source is None).
        // If source is Some(...), it's from crates.io or git, which is fine
        // (handled by Cargo).
        if pkg.source.is_none() {
            let pkg_path = pkg.manifest_path.as_std_path();

            // Canonicalize the package path for comparison
            let canonical_pkg_path = fs::canonicalize(pkg_path)
                .with_context(|| format!("Failed to canonicalize path for package {}", pkg.name))?;

            // Check if the package lives outside the workspace tree
            if !canonical_pkg_path.starts_with(&workspace_root) {
                anyhow::bail!(
                    "Unsupported external dependency: '{}' at {:?}.\n\
                     Hermes currently only supports verifying workspaces where all local \
                     dependencies are contained within the workspace root.",
                    pkg.name,
                    pkg_path
                );
            }
        }
    }

    Ok(())
}
