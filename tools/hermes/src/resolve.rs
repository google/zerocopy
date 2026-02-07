use std::env;

use anyhow::{anyhow, Context, Result};
use cargo_metadata::{
    camino::Utf8PathBuf, Metadata, MetadataCommand, Package, PackageName, Target, TargetKind,
};
use clap::Parser;

#[derive(Parser, Debug)]
pub struct Args {
    #[command(flatten)]
    manifest: clap_cargo::Manifest,

    #[command(flatten)]
    workspace: clap_cargo::Workspace,

    #[command(flatten)]
    features: clap_cargo::Features,

    /// Verify the library target
    #[arg(long)]
    lib: bool,

    /// Verify specific binary targets
    #[arg(long)]
    bin: Vec<String>,

    /// Verify all binary targets
    #[arg(long)]
    bins: bool,

    /// Verify specific example targets
    #[arg(long)]
    example: Vec<String>,

    /// Verify all example targets
    #[arg(long)]
    examples: bool,

    /// Verify specific test targets
    #[arg(long)]
    test: Vec<String>,

    /// Verify all test targets
    #[arg(long)]
    tests: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// Resolves all verification roots.
///
/// Each entry represents a distinct compilation artifact to be verified.
pub fn resolve_roots(args: &Args) -> Result<Vec<(PackageName, HermesTargetKind, Utf8PathBuf)>> {
    let mut cmd = MetadataCommand::new();

    if let Some(path) = &args.manifest.manifest_path {
        cmd.manifest_path(path);
    }

    // Forward features to ensure dependency resolution matches the user's
    // request.
    args.features.forward_metadata(&mut cmd);

    let metadata = cmd.exec().context("Failed to run 'cargo metadata'")?;

    let selected_packages = resolve_packages(&metadata, &args.workspace)?;

    let mut roots = Vec::new();
    for package in selected_packages {
        log::trace!("Scanning package: {}", package.name);

        let targets = resolve_targets(package, args)?;

        if targets.is_empty() {
            log::warn!("No matching targets found for package '{}'", package.name);
            continue;
        }

        for (target, kind) in targets {
            roots.push((package.name.clone(), kind.clone(), target.src_path.clone()));
        }
    }

    Ok(roots)
}

/// Resolves which packages to process based on workspace flags and CWD.
fn resolve_packages<'a>(
    metadata: &'a Metadata,
    args: &clap_cargo::Workspace,
) -> Result<Vec<&'a Package>> {
    let mut packages = Vec::new();

    if !args.package.is_empty() {
        // Resolve explicitly selected packages (-p / --package)
        for name in &args.package {
            let pkg = metadata
                .packages
                .iter()
                .find(|p| p.name == name)
                .ok_or_else(|| anyhow!("Package '{}' not found in workspace", name))?;
            packages.push(pkg);
        }
    } else if args.workspace || args.all {
        // Resolve entire workspace (--workspace / --all)
        for id in &metadata.workspace_members {
            if let Some(pkg) = metadata.packages.iter().find(|p| &p.id == id) {
                packages.push(pkg);
            }
        }
    } else {
        // Resolve default (Current Working Directory)
        let cwd = env::current_dir().context("Failed to get CWD")?;

        // Find the package whose manifest directory is an ancestor of CWD
        let current_pkg = metadata.packages.iter().find(|p| {
            let manifest_dir = p.manifest_path.parent().unwrap();
            cwd.starts_with(manifest_dir)
        });

        if let Some(pkg) = current_pkg {
            packages.push(pkg);
        } else {
            // Fallback: If we are at the workspace root (virtual manifest),
            // behave like --workspace.
            if cwd == metadata.workspace_root.as_std_path() {
                for id in &metadata.workspace_members {
                    if let Some(pkg) = metadata.packages.iter().find(|p| &p.id == id) {
                        packages.push(pkg);
                    }
                }
            } else {
                return Err(anyhow!("Could not determine package from current directory. Please use -p <NAME> or --workspace."));
            }
        }
    }

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
    let mut selected_artifacts = Vec::new();

    // If no specific target flags are set, default to libs + bins.
    let default_mode = !args.lib
        && args.bin.is_empty()
        && !args.bins
        && args.example.is_empty()
        && !args.examples
        && args.test.is_empty()
        && !args.tests;

    for target in &package.targets {
        for raw_kind in &target.kind {
            // 1. Try to convert to our supported internal kind.
            // If it fails (e.g., Bench, CustomBuild), we skip it immediately.
            let Ok(kind) = HermesTargetKind::try_from(raw_kind) else {
                continue;
            };

            // 2. Check against user flags using the helper and clean matches.
            let include = if default_mode {
                kind.is_lib() || kind == HermesTargetKind::Bin
            } else {
                let explicitly_lib = args.lib && kind.is_lib();

                let explicitly_all_bins = args.bins && kind == HermesTargetKind::Bin;
                let explicitly_named_bin =
                    args.bin.contains(&target.name) && kind == HermesTargetKind::Bin;

                let explicitly_all_examples = args.examples && kind == HermesTargetKind::Example;
                let explicitly_named_example =
                    args.example.contains(&target.name) && kind == HermesTargetKind::Example;

                let explicitly_all_tests = args.tests && kind == HermesTargetKind::Test;
                let explicitly_named_test =
                    args.test.contains(&target.name) && kind == HermesTargetKind::Test;

                explicitly_lib
                    || explicitly_all_bins
                    || explicitly_named_bin
                    || explicitly_all_examples
                    || explicitly_named_example
                    || explicitly_all_tests
                    || explicitly_named_test
            };

            if include {
                selected_artifacts.push((target, kind));
            }
        }
    }

    Ok(selected_artifacts)
}
