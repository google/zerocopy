// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Run the pinned compiler or explicitly capture one configured compilation.
//! Typed capture does not verify a crate; the host must check the generated
//! subject against its authored specifications and exact root.

// RUSTC-WORKAROUND(#4368): Path::normalize_lexically is still unstable.
#![feature(normalize_lexically, rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_expand;
extern crate rustc_feature;
extern crate rustc_hir;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

mod capture;
mod driver;
mod extract;
mod identity;
mod ir;
mod lean;
mod mono;
mod publication;
mod shard;

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;

use clap::{ArgGroup, Parser, ValueEnum};
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliCrateType {
    Lib,
    Bin,
}

impl From<CliCrateType> for ir::CrateType {
    fn from(value: CliCrateType) -> Self {
        match value {
            CliCrateType::Lib => Self::Lib,
            CliCrateType::Bin => Self::Bin,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliPanicStrategy {
    Unwind,
    Abort,
}

impl From<CliPanicStrategy> for ir::PanicStrategy {
    fn from(value: CliPanicStrategy) -> Self {
        match value {
            CliPanicStrategy::Unwind => Self::Unwind,
            CliPanicStrategy::Abort => Self::Abort,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum CliStdlibCrate {
    Core,
}

impl From<CliStdlibCrate> for ir::StdlibCrate {
    fn from(value: CliStdlibCrate) -> Self {
        match value {
            CliStdlibCrate::Core => Self::Core,
        }
    }
}

#[derive(Debug, Parser)]
#[command(
    name = "anneal-rustc-capture capture",
    version,
    about = "Capture pinned Runtime(PostCleanup) MIR",
    group(ArgGroup::new("selection").required(true).multiple(true).args(["select", "instantiate", "scope"]))
)]
pub struct Args {
    #[arg(long)]
    crate_root: PathBuf,
    #[arg(long)]
    crate_name: String,
    #[arg(long, value_enum, default_value_t = CliCrateType::Lib)]
    crate_type: CliCrateType,
    #[arg(long, value_enum, default_value_t = CliPanicStrategy::Unwind)]
    panic: CliPanicStrategy,
    /// Enable runtime integer overflow checks (`-Coverflow-checks=yes`) during
    /// capture instead of `-Coverflow-checks=no`.
    #[arg(long)]
    overflow_checks: bool,
    #[arg(long, default_value = "2024", value_parser = ["2015", "2018", "2021", "2024"])]
    edition: String,
    #[arg(long)]
    target: String,
    /// Publish into a new directory with a UTF-8 resolved path.
    /// An existing destination is refused.
    #[arg(long)]
    out_dir: PathBuf,
    // Capture these callable roots without claiming coverage of other items.
    #[arg(long, action = clap::ArgAction::Append, conflicts_with = "scope")]
    select: Vec<String>,
    /// Capture concrete generic instantiations as JSON
    /// (`{"path":...,"args":[...]}`).
    #[arg(
        long,
        action = clap::ArgAction::Append,
        value_name = "JSON",
        conflicts_with = "scope",
        value_parser = parse_instantiation
    )]
    instantiate: Vec<ir::Instantiation>,
    // Require admission of every required item in the compiler census.
    #[arg(long, value_parser = ["crate"])]
    scope: Option<String>,
    /// Exclude local impls of an allowlisted diagnostic trait
    /// (`core::error::Error`, `core::fmt::Debug`, `core::fmt::Display`) from
    /// `--scope crate` capture once proven unreachable from verified bodies.
    #[arg(long, action = clap::ArgAction::Append, value_name = "TRAIT")]
    exclude_trait: Vec<String>,
    #[arg(long, action = clap::ArgAction::Append)]
    cfg: Vec<String>,
    /// Declare a compile-time environment variable (`KEY=VALUE`) for `env!`
    /// and `option_env!`. Undeclared environment reads still fail closed.
    #[arg(
        long,
        action = clap::ArgAction::Append,
        value_name = "KEY=VALUE",
        value_parser = parse_env_binding
    )]
    env: Vec<(String, String)>,
    /// Override the sysroot resolved from the pinned compiler distribution.
    #[arg(long)]
    sysroot: Option<PathBuf>,
    /// Declare an allowed compiler input; repeat for every staged source file.
    /// An explicit allowlist prevents omitted declarations from authorizing
    /// ambient module or include-file reads.
    #[arg(long, required = true, action = clap::ArgAction::Append)]
    source_file: Vec<PathBuf>,
    /// Optional logical source root directory. When supplied, `--crate-root`
    /// and every `--source-file` must canonically reside inside this directory,
    /// and path metadata in `capture.json` (`configuration.crate_root`,
    /// `configuration.declared_source_files`, and `source_files[].path`) is
    /// normalized to source-root-relative POSIX paths. Only those path fields
    /// are normalized; crates that embed path-dependent values (for example via
    /// `file!()`) may still vary across staging directories.
    #[arg(long)]
    source_root: Option<PathBuf>,
    /// Capture the named standard-library crate from its unmodified sources.
    /// This capability admits the crate's own language items and version-pinned
    /// `#![feature(...)]` gates and skips object emission. It requires a
    /// library crate whose `--crate-name` matches, selected roots, a
    /// compilation that loads no other crate, no `miri` cfg (forbidden for all
    /// captures), and any crate-local `Ordering` language item to have the
    /// modeled shape. The capability is recorded in `capture.json`.
    #[arg(long, value_enum)]
    stdlib_crate: Option<CliStdlibCrate>,
    /// Minimum body count above which `.olean` sharding activates (`N > min`).
    /// Captures with `<= shard_min_bodies` keep the single-file `Captured.lean`
    /// layout.
    #[arg(long, default_value_t = shard::DEFAULT_SHARD_MIN_BODIES)]
    shard_min_bodies: usize,
    /// Maximum bodies packed into a single coarsened shard (`>= 1`; any
    /// oversized single SCC receives a dedicated isolated shard).
    #[arg(
        long,
        default_value_t = shard::DEFAULT_SHARD_MAX_BODIES,
        value_parser = parse_nonzero_usize
    )]
    shard_max_bodies: usize,
    /// Maximum AST nodes packed into a single coarsened shard (`>= 1`).
    #[arg(
        long,
        default_value_t = shard::DEFAULT_SHARD_MAX_AST_NODES,
        value_parser = parse_nonzero_usize
    )]
    shard_max_ast_nodes: usize,
    /// Verify that the captured shard topology matches a checked-in
    /// `anneal-shards.json` plan before publishing any artifacts.
    #[arg(long)]
    verify_shard_plan: Option<PathBuf>,
    /// Admit an unstable `#![feature(...)]` gate on a normal crate; repeat
    /// or comma-separate for several. Compiler-internal features (and
    /// `ergonomic_clones` and `rustc_private`) stay refused. Each admitted
    /// and enabled feature is recorded in `capture.json`.
    #[arg(
        long,
        action = clap::ArgAction::Append,
        value_delimiter = ',',
        value_name = "FEATURE",
        value_parser = parse_feature_name,
        conflicts_with = "stdlib_crate"
    )]
    allow_unstable_feature: Vec<String>,
}

fn parse_nonzero_usize(raw: &str) -> Result<usize, String> {
    let n: usize =
        raw.parse().map_err(|e| format!("expected positive integer, got {raw:?}: {e}"))?;
    if n == 0 {
        return Err("value must be at least 1".to_owned());
    }
    Ok(n)
}

/// Accept a `#![feature(...)]` gate name of the form `[a-z][a-z0-9_]*`, which
/// also keeps `-Zallow-features=` free of comma and wildcard injection.
fn parse_feature_name(raw: &str) -> Result<String, String> {
    let mut chars = raw.chars();
    let valid = chars.next().is_some_and(|c| c.is_ascii_lowercase())
        && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
    if !valid {
        return Err(format!("invalid feature name {raw:?}: expected [a-z][a-z0-9_]*"));
    }
    Ok(raw.to_owned())
}

fn parse_instantiation(raw: &str) -> Result<ir::Instantiation, String> {
    serde_json::from_str::<ir::Instantiation>(raw)
        .map_err(|e| format!("invalid --instantiate JSON {raw:?}: {e}"))
}

fn parse_env_binding(raw: &str) -> Result<(String, String), String> {
    let Some((key, value)) = raw.split_once('=') else {
        return Err(format!("expected KEY=VALUE environment binding, got {raw:?}"));
    };
    if key.is_empty() {
        return Err("environment variable name must not be empty".to_owned());
    }
    if key.contains('\0') || value.contains('\0') {
        return Err("environment binding must not contain NUL bytes".to_owned());
    }
    Ok((key.to_owned(), value.to_owned()))
}

impl Args {
    pub(crate) fn resolved_scope(&self) -> Result<ir::Scope, Failure> {
        if self.scope.is_some() {
            let mut excluded_traits = BTreeSet::new();
            for raw in &self.exclude_trait {
                let trait_kind =
                    ir::ExcludedTrait::parse_canonical(raw).map_err(Failure::unsupported)?;
                excluded_traits.insert(trait_kind);
            }
            return Ok(ir::Scope::Crate { excluded_traits });
        }
        if !self.exclude_trait.is_empty() {
            return Err(Failure::unsupported(
                "--exclude-trait is valid only with --scope crate; \
                 cannot be combined with --select or --instantiate",
            ));
        }
        let roots: BTreeSet<String> = self.select.iter().cloned().collect();
        let instantiations: BTreeSet<ir::Instantiation> =
            self.instantiate.iter().cloned().collect();
        if roots.is_empty() && instantiations.is_empty() {
            return Err(Failure::unsupported("empty selected scope"));
        }
        Ok(ir::Scope::SelectedUnit { roots, instantiations })
    }

    pub(crate) fn resolved_env(&self) -> Result<BTreeMap<String, String>, Failure> {
        let mut declared = BTreeMap::new();
        for (key, value) in &self.env {
            if declared.insert(key.clone(), value.clone()).is_some() {
                return Err(Failure::tool(format!(
                    "duplicate --env binding for {key}"
                )));
            }
        }
        Ok(declared)
    }
}

#[derive(Debug, Serialize)]
pub struct Failure {
    status: &'static str,
    diagnostics: Vec<String>,
    unsupported: Vec<ir::Unsupported>,
}

impl Failure {
    fn tool(message: impl Into<String>) -> Self {
        Self {
            status: "tool_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn io(error: std::io::Error) -> Self {
        Self::tool(error.to_string())
    }
    fn compiler(message: impl Into<String>) -> Self {
        Self {
            status: "compiler_failed",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported(message: impl Into<String>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![message.into()],
            unsupported: Vec::new(),
        }
    }
    fn unsupported_items(items: Vec<ir::Unsupported>) -> Self {
        Self {
            status: "unsupported",
            diagnostics: vec![format!(
                "{} required obligations are unsupported",
                items.len()
            )],
            unsupported: items,
        }
    }
}

/// Format a canonical input path for `capture.json` emission.
///
/// When `source_root` is `Some`, returns a clean source-root-relative POSIX
/// path (`/`-separated `Normal` UTF-8 components) and fails closed if
/// `canonical_path` escapes or equals `source_root`. When `source_root` is
/// `None`, preserves `canonical_path` verbatim for standalone callers.
pub(crate) fn manifest_path(
    canonical_path: &Path,
    source_root: Option<&Path>,
) -> Result<PathBuf, Failure> {
    let Some(root) = source_root else {
        return Ok(canonical_path.to_path_buf());
    };
    let rel = canonical_path.strip_prefix(root).map_err(|_| {
        Failure::unsupported(format!(
            "source input escapes --source-root: {}",
            canonical_path.display()
        ))
    })?;
    let mut parts = Vec::new();
    for component in rel.components() {
        match component {
            Component::Normal(part) => {
                let s = part.to_str().ok_or_else(|| {
                    Failure::unsupported("non-UTF-8 source path cannot be normalized for manifest")
                })?;
                parts.push(s);
            }
            _ => {
                return Err(Failure::unsupported(format!(
                    "source input does not normalize cleanly under --source-root: {}",
                    canonical_path.display()
                )));
            }
        }
    }
    if parts.is_empty() {
        return Err(Failure::unsupported(format!(
            "source input must be a file inside --source-root: {}",
            canonical_path.display()
        )));
    }
    Ok(PathBuf::from(parts.join("/")))
}

/// Canonicalizes the command-line input paths against one view of the
/// filesystem, so that inputs reached through the same moving symlink
/// (for example a `current -> snap_v1` link that is atomically retargeted
/// to `snap_v2`) all resolve into the same snapshot.
///
/// Calling `std::fs::canonicalize` once per argument resolves a shared
/// prefix once per argument. If the link moves between two of those calls,
/// `--crate-root` and a `--source-file` that name the same file can resolve
/// into different snapshots; rustc then reads a name that is not declared,
/// and capture fails closed with a spurious undeclared-read refusal.
///
/// Instead, each path is made absolute and canonicalized one component at a
/// time by calling `std::fs::canonicalize` on each `(canonical_prefix,
/// next_component)` step and memoizing the result under the raw prefix. This
/// is an Anneal cross-argument snapshot consistency mechanism rather than a
/// compiler or standard-library workaround (neither POSIX `realpath` nor
/// `std::fs::canonicalize` resolves multiple independent CLI arguments against
/// a shared moving-symlink snapshot): inputs whose raw spellings share a
/// prefix observe one resolution of it. On ordinary static paths, this
/// preserves `std::fs::canonicalize` semantics—including physical `..`,
/// trailing `/` and `/.` directory checks, and fail-closed errors for missing,
/// dangling, or non-directory components—differing only on exotic cases such
/// as chains exceeding Linux's cumulative symlink hop limit across cached
/// prefixes, `.` under an unsearchable ancestor, or exact errno distinctions
/// on missing spellings.
///
/// Once resolved, only canonical names reach rustc, the `RecordingLoader`
/// namespace, and the manifest, so later movement of the link cannot change
/// what is read. This does not make the snapshot itself immutable: as
/// `RecordingLoader::lookup` states, direct callers must keep the declared
/// canonical files and their ancestors unchanged for the compiler session.
/// Distinct raw spellings of moving links (`a/current` and `b/current`) are
/// resolved independently and can still disagree; that failure is also
/// closed.
#[derive(Default)]
struct InputResolver {
    resolved: BTreeMap<PathBuf, PathBuf>,
}

impl InputResolver {
    fn canonicalize(&mut self, path: &Path) -> std::io::Result<PathBuf> {
        if path.as_os_str().is_empty() {
            return path.canonicalize();
        }
        let absolute = std::path::absolute(path)?;
        let mut raw = PathBuf::new();
        let mut canonical = PathBuf::new();
        for component in absolute.components() {
            raw.push(component);
            match component {
                Component::RootDir => canonical.push(component),
                Component::Normal(_) | Component::ParentDir => {
                    canonical = match self.resolved.get(&raw) {
                        Some(resolved) => resolved.clone(),
                        None => {
                            let resolved = canonical.join(component).canonicalize()?;
                            self.resolved.insert(raw.clone(), resolved.clone());
                            resolved
                        }
                    };
                }
                // `std::path::absolute` removes `.` components on Unix, and
                // capture runs only on Linux, where paths have no prefix.
                Component::CurDir | Component::Prefix(_) => {
                    return Err(std::io::Error::other(format!(
                        "unexpected component in absolute input path: {}",
                        absolute.display()
                    )));
                }
            }
        }
        // `Path::components` drops a trailing `/` or `/.`, either of which
        // requires the path to name a directory. Check that requirement as
        // `canonicalize` does, so that `file.rs/` fails rather than naming
        // `file.rs`.
        let spelling = path.as_os_str().as_encoded_bytes();
        if spelling.ends_with(b"/") || spelling.ends_with(b"/.") {
            canonical = canonical.join(".").canonicalize()?;
        }
        Ok(canonical)
    }
}

/// Canonicalize all command-line input paths through one shared `InputResolver`
/// so inputs reached through the same moving symlink resolve into one snapshot.
fn resolve_input_paths(args: &mut Args, resolver: &mut InputResolver) -> Result<(), Failure> {
    args.crate_root = resolver.canonicalize(&args.crate_root).map_err(Failure::io)?;
    for path in &mut args.source_file {
        *path = resolver.canonicalize(path).map_err(Failure::io)?;
    }
    if let Some(source_root) = args.source_root.as_mut() {
        *source_root = resolver.canonicalize(source_root).map_err(Failure::io)?;
        if !source_root.is_dir() {
            return Err(Failure::unsupported(format!(
                "--source-root is not a directory: {}",
                source_root.display()
            )));
        }
        manifest_path(&args.crate_root, Some(source_root))?;
        for path in &args.source_file {
            manifest_path(path, Some(source_root))?;
        }
    }
    Ok(())
}

fn resolve_verify_shard_plan(
    verify_shard_plan: Option<PathBuf>,
    resolver: &mut InputResolver,
) -> Result<Option<PathBuf>, Failure> {
    match verify_shard_plan {
        Some(path) => Ok(Some(resolver.canonicalize(&path).map_err(|e| {
            Failure::tool(format!("cannot resolve --verify-shard-plan {}: {e}", path.display()))
        })?)),
        None => Ok(None),
    }
}

fn run(mut args: Args) -> Result<serde_json::Value, Failure> {
    if args.target != "x86_64-unknown-linux-gnu" {
        return Err(Failure::unsupported(
            "the initial adapter supports only x86_64-unknown-linux-gnu",
        ));
    }
    // Declarations, selectors, and cfgs are sets. A declared alias selects its
    // canonical filename; it does not expose other ambient aliases to rustc.
    // The recording loader uses those names and their ancestor directories as
    // its source namespace, independently checking the exact bytes read.
    // Sorting keeps manifests stable; normalization alone proves no read.
    // One resolver canonicalizes every input path (including
    // `--verify-shard-plan` below), so inputs reached through the same moving
    // symlink resolve into one snapshot.
    let mut resolver = InputResolver::default();
    resolve_input_paths(&mut args, &mut resolver)?;
    args.source_file.sort();
    args.source_file.dedup();
    // rustc reads the crate root through the recording loader, which refuses
    // any undeclared name. Check that here, before the compiler runs, so
    // that a crate root resolved outside the declared files fails with a
    // diagnostic that names the crate root.
    if args.source_file.binary_search(&args.crate_root).is_err() {
        return Err(Failure::unsupported(format!(
            "--crate-root is not a declared --source-file: {}",
            args.crate_root.display()
        )));
    }
    args.cfg.sort();
    args.cfg.dedup();
    args.allow_unstable_feature.sort();
    args.allow_unstable_feature.dedup();
    let declared_env = args.resolved_env()?;
    // Resolve explicit or packaged sysroot lexically (preserving virtual
    // symlink-forest layouts such as `<sysroot>/bin/rustc` beside
    // `<sysroot>/lib/rustlib`) and verify compiler identity and Linux driver
    // residency via open-FD `(st_dev, st_ino)` + SHA-256 before creating
    // publication directories or entering rustc's fatal-error handler.
    let raw_sysroot = match args.sysroot.take() {
        Some(sysroot) => sysroot,
        None => driver::resolve_packaged_sysroot().map_err(Failure::tool)?,
    };
    let sysroot = identity::normalize_logical_sysroot(&raw_sysroot)?;
    args.sysroot = Some(sysroot.clone());
    let verified = identity::verify_compiler(&sysroot, &args.target)?;
    // Keep compiler side effects outside the public artifact pair. The
    // publication owner cleans up staging on every error and unwind; only its
    // completed directory rename permits a captured status below.
    let publication = publication::Publication::new(&args.out_dir).map_err(Failure::io)?;
    args.out_dir = publication.compiler_dir();
    let shard_config = shard::ShardConfig {
        shard_min_bodies: args.shard_min_bodies,
        shard_max_bodies: args.shard_max_bodies,
        shard_max_ast_nodes: args.shard_max_ast_nodes,
    };
    shard_config.validate().map_err(Failure::tool)?;
    let verify_shard_plan =
        resolve_verify_shard_plan(args.verify_shard_plan.take(), &mut resolver)?;
    let mut manifest = capture::run(&args, &declared_env, &sysroot, &verified)?;
    let prepared_shards =
        shard::maybe_shard_manifest(&mut manifest, shard_config).map_err(Failure::tool)?;
    if let Some(ref plan_path) = verify_shard_plan {
        let actual_plan = match &prepared_shards {
            Some(prepared) => shard::ShardPlan::from_sharded(&prepared.manifest, shard_config),
            None => shard::ShardPlan::from_unsharded(
                manifest.program.scope(),
                manifest.program.bodies().len(),
                shard_config,
            ),
        };
        shard::verify_shard_plan_file(plan_path, &actual_plan).map_err(Failure::tool)?;
    }
    let json =
        serde_json::to_vec_pretty(&manifest).map_err(|error| Failure::tool(error.to_string()))?;
    let (destination, shard_count) = match prepared_shards {
        None => {
            let lean = lean::render(&manifest.program);
            let destination = publication.publish(&json, lean.as_bytes()).map_err(Failure::io)?;
            (destination, 0usize)
        }
        Some(prepared) => {
            let destination = publication
                .publish_with_shards(
                    &json,
                    prepared.root_lean.as_bytes(),
                    Some(publication::ShardedPublication {
                        shards_json: &prepared.manifest_json,
                        shard_sources: &prepared.shard_sources,
                    }),
                )
                .map_err(Failure::io)?;
            (destination, prepared.manifest.total_shards)
        }
    };
    let json_path = destination.join("capture.json");
    let lean_path = destination.join("Captured.lean");
    let mut response = serde_json::json!({
        "status": "captured", "capture": json_path, "lean": lean_path,
        "selected_count": manifest.selected.len(),
        "census_count": manifest.census.len(),
        "source_count": manifest.source_files.len(),
    });
    if shard_count > 0 {
        let obj = response.as_object_mut().expect("object literal");
        obj.insert(
            "capture_shards".to_owned(),
            serde_json::json!(destination.join("capture_shards.json")),
        );
        obj.insert("shard_count".to_owned(), serde_json::json!(shard_count));
    }
    Ok(response)
}

fn run_capture(args: Vec<OsString>) -> ExitCode {
    let args = match Args::try_parse_from(
        std::iter::once(OsString::from("anneal-rustc-capture capture")).chain(args),
    ) {
        Ok(args) => args,
        Err(error)
            if matches!(
                error.kind(),
                clap::error::ErrorKind::DisplayHelp | clap::error::ErrorKind::DisplayVersion
            ) =>
        {
            print!("{error}");
            return ExitCode::SUCCESS;
        }
        Err(error) => {
            println!(
                "{}",
                serde_json::to_string(&Failure::tool(error.to_string()))
                    .expect("serializable failure")
            );
            return ExitCode::from(2);
        }
    };
    // A callback or adapter panic must become an explicit failed capture,
    // never an apparently successful receipt for an incomplete compiler run.
    // rustc's own ICE hook still supplies the detailed stderr diagnostic.
    let result = std::panic::catch_unwind(|| run(args)).unwrap_or_else(|_| {
        Err(Failure::tool(
            "capture or compiler panicked; see stderr diagnostics",
        ))
    });
    match result {
        Ok(success) => {
            println!("{success}");
            ExitCode::SUCCESS
        }
        Err(failure) => {
            println!(
                "{}",
                serde_json::to_string(&failure).expect("serializable failure")
            );
            ExitCode::from(1)
        }
    }
}

/// Entrypoint for the `anneal-rustc-capture` driver binary.
pub fn cli_main() -> ExitCode {
    let mut args: Vec<_> = env::args_os().skip(1).collect();
    if args.is_empty() || (args.len() == 1 && matches!(args[0].to_str(), Some("--help" | "-h"))) {
        println!(
            "Usage: anneal-rustc-capture [--] <rustc arguments>\n\
             \n\
             Run the pinned compiler and report a successful analysis callback on stderr.\n\
             Verification is not performed.\n\
             \n\
             Pass compiler options unchanged, including --sysroot for an unbundled\n\
             development binary. Installed binaries use the adjacent rust/ sysroot.\n\
             Use -- before compiler --help, --version, or an input named capture.\n\
             \n\
             Use anneal-rustc-capture capture --help for typed MIR capture."
        );
        return ExitCode::SUCCESS;
    }
    if args.len() == 1 && matches!(args[0].to_str(), Some("--version" | "-V")) {
        println!("anneal-rustc-capture {}", env!("CARGO_PKG_VERSION"));
        return ExitCode::SUCCESS;
    }
    // Only the explicit command selects typed capture. Inspect it before
    // removing the raw compiler escape, so `-- capture` remains a rustc input.
    if args.first().is_some_and(|arg| arg == "capture") {
        args.remove(0);
        return run_capture(args);
    }
    if args.first().is_some_and(|arg| arg == "--") {
        args.remove(0);
    }
    driver::run(args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_env_binding_validates_syntax_and_nul_bytes() {
        assert_eq!(
            parse_env_binding("CARGO_PKG_VERSION=0.8.64").unwrap(),
            ("CARGO_PKG_VERSION".to_owned(), "0.8.64".to_owned())
        );
        assert_eq!(
            parse_env_binding("EMPTY=").unwrap(),
            ("EMPTY".to_owned(), String::new())
        );
        assert_eq!(
            parse_env_binding("NESTED=a=b=c").unwrap(),
            ("NESTED".to_owned(), "a=b=c".to_owned())
        );
        assert_eq!(
            parse_env_binding("AT=@literal").unwrap(),
            ("AT".to_owned(), "@literal".to_owned())
        );

        assert!(parse_env_binding("NO_EQUALS").is_err());
        assert!(parse_env_binding("=value").is_err());
        assert!(parse_env_binding("BAD\0KEY=value").is_err());
        assert!(parse_env_binding("KEY=bad\0value").is_err());
    }

    #[test]
    fn resolved_env_sorts_deterministically_and_rejects_duplicates() {
        let base = [
            "anneal-rustc-capture capture",
            "--crate-root=lib.rs",
            "--crate-name=demo",
            "--target=x86_64-unknown-linux-gnu",
            "--out-dir=out",
            "--select=f",
            "--source-file=lib.rs",
        ];

        let args = Args::try_parse_from(
            base.into_iter()
                .chain(["--env=Z_KEY=last", "--env=A_KEY=first"]),
        )
        .unwrap();
        let resolved = args.resolved_env().unwrap();
        let keys: Vec<&str> = resolved.keys().map(String::as_str).collect();
        assert_eq!(keys, vec!["A_KEY", "Z_KEY"]);
        assert_eq!(resolved["A_KEY"], "first");
        assert_eq!(resolved["Z_KEY"], "last");

        for dup in [
            ["--env=FOO=one", "--env=FOO=two"],
            ["--env=FOO=one", "--env=FOO=one"],
        ] {
            let args = Args::try_parse_from(base.into_iter().chain(dup)).unwrap();
            let err = args.resolved_env().unwrap_err();
            assert_eq!(err.status, "tool_failed");
            assert!(
                err.diagnostics[0].contains("duplicate --env binding for FOO"),
                "{err:?}"
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn input_resolver_matches_canonicalize_without_concurrent_changes() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        std::fs::create_dir_all(base.join("real/inner")).unwrap();
        std::fs::write(base.join("real/inner/lib.rs"), "").unwrap();
        std::fs::write(base.join("real/top.rs"), "").unwrap();
        symlink(base.join("real"), base.join("abs-dir")).unwrap();
        symlink("real/inner", base.join("rel-dir")).unwrap();
        symlink("inner/lib.rs", base.join("real/file-link.rs")).unwrap();
        symlink("rel-dir", base.join("chain")).unwrap();
        symlink("missing", base.join("dangling")).unwrap();
        let cases = [
            "real/inner/lib.rs",
            "abs-dir/inner/lib.rs",
            "rel-dir/lib.rs",
            "chain/lib.rs",
            "real/file-link.rs",
            "abs-dir/file-link.rs",
            "abs-dir",
            // `..` is physical: `rel-dir/..` is `real`, not `base`.
            "rel-dir/../top.rs",
            "chain/../top.rs",
            "real/inner/../top.rs",
            // A trailing `/` or `/.` requires a directory.
            "abs-dir/",
            "rel-dir/.",
            "chain/./",
            "real/top.rs/",
            "real/top.rs/.",
            "real/file-link.rs/",
            // Errors: a missing component, a dangling link, and `..` after a
            // regular file.
            "real/missing.rs",
            "real/missing/../top.rs",
            "dangling",
            "real/top.rs/../top.rs",
        ];
        let mut shared = InputResolver::default();
        for case in cases {
            let path = base.join(case);
            let expected = path.canonicalize().ok();
            assert_eq!(InputResolver::default().canonicalize(&path).ok(), expected, "{case}");
            assert_eq!(shared.canonicalize(&path).ok(), expected, "{case} (shared)");
        }
        assert_eq!(
            shared.canonicalize(&base.join("rel-dir/../top.rs")).unwrap(),
            base.join("real/top.rs")
        );
        assert!(shared.canonicalize(&base.join("real/top.rs/")).is_err());
        assert!(shared.canonicalize(&base.join("real/top.rs/.")).is_err());
        assert_eq!(shared.canonicalize(&base.join("rel-dir/.")).unwrap(), base.join("real/inner"));
    }

    #[cfg(unix)]
    #[test]
    fn input_resolver_resolves_a_shared_moving_symlink_once() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        for snapshot in ["snap_v1", "snap_v2"] {
            std::fs::create_dir_all(base.join(snapshot).join("src")).unwrap();
            std::fs::write(base.join(snapshot).join("src/lib.rs"), "mod sub;\n").unwrap();
            std::fs::write(base.join(snapshot).join("src/sub.rs"), "").unwrap();
        }
        let current = base.join("current");
        symlink("snap_v1", &current).unwrap();
        let mut resolver = InputResolver::default();
        let crate_root = resolver.canonicalize(&current.join("src/lib.rs")).unwrap();
        assert_eq!(crate_root, base.join("snap_v1/src/lib.rs"));

        // Retarget the link atomically, as a snapshot publisher would, between
        // resolving `--crate-root` and resolving the remaining inputs.
        symlink("snap_v2", base.join("next")).unwrap();
        std::fs::rename(base.join("next"), &current).unwrap();
        assert_eq!(
            current.join("src/sub.rs").canonicalize().unwrap(),
            base.join("snap_v2/src/sub.rs"),
            "the link must really have moved"
        );

        // Every later input that shares the raw `current` prefix stays in the
        // snapshot that the first input observed.
        assert_eq!(resolver.canonicalize(&current.join("src/lib.rs")).unwrap(), crate_root);
        assert_eq!(
            resolver.canonicalize(&current.join("src/sub.rs")).unwrap(),
            base.join("snap_v1/src/sub.rs")
        );
        assert_eq!(
            resolver.canonicalize(&current.join("src/../src/sub.rs")).unwrap(),
            base.join("snap_v1/src/sub.rs")
        );
        assert_eq!(resolver.canonicalize(&current).unwrap(), base.join("snap_v1"));
        // A fresh resolver is a fresh view of the filesystem.
        assert_eq!(
            InputResolver::default().canonicalize(&current.join("src/sub.rs")).unwrap(),
            base.join("snap_v2/src/sub.rs")
        );
    }

    #[cfg(unix)]
    #[test]
    fn resolve_input_paths_and_shard_plan_share_one_snapshot_resolver() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        for snapshot in ["snap_v1", "snap_v2"] {
            std::fs::create_dir_all(base.join(snapshot).join("src")).unwrap();
            std::fs::write(base.join(snapshot).join("src/lib.rs"), "mod sub;\n").unwrap();
            std::fs::write(base.join(snapshot).join("src/sub.rs"), "").unwrap();
            std::fs::write(base.join(snapshot).join("anneal-shards.json"), "{}").unwrap();
        }
        let current = base.join("current");
        symlink("snap_v1", &current).unwrap();
        let mut args = Args::try_parse_from([
            "anneal-rustc-capture",
            "--crate-name",
            "demo",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--scope",
            "crate",
            "--crate-root",
            current.join("src/lib.rs").to_str().unwrap(),
            "--source-file",
            current.join("src/lib.rs").to_str().unwrap(),
            "--source-file",
            current.join("src/sub.rs").to_str().unwrap(),
            "--source-root",
            current.to_str().unwrap(),
            "--verify-shard-plan",
            current.join("anneal-shards.json").to_str().unwrap(),
            "--out-dir",
            base.join("out").to_str().unwrap(),
        ])
        .unwrap();

        let mut resolver = InputResolver::default();
        resolve_input_paths(&mut args, &mut resolver).unwrap();
        assert_eq!(args.crate_root, base.join("snap_v1/src/lib.rs"));
        assert_eq!(
            args.source_file,
            vec![base.join("snap_v1/src/lib.rs"), base.join("snap_v1/src/sub.rs")]
        );
        assert_eq!(args.source_root, Some(base.join("snap_v1")));

        // Retarget `current` to `snap_v2` before `--verify-shard-plan` is
        // resolved (the exact window in `run()` around `verify_compiler`).
        symlink("snap_v2", base.join("next")).unwrap();
        std::fs::rename(base.join("next"), &current).unwrap();
        let plan_path =
            resolve_verify_shard_plan(args.verify_shard_plan.take(), &mut resolver).unwrap();
        assert_eq!(plan_path, Some(base.join("snap_v1/anneal-shards.json")));
    }

    #[test]
    fn manifest_path_normalizes_under_source_root_and_rejects_escapes() {
        let root = Path::new("/tmp/stage-a/rust");
        assert_eq!(
            manifest_path(Path::new("/tmp/stage-a/rust/lib.rs"), Some(root)).unwrap(),
            PathBuf::from("lib.rs")
        );
        assert_eq!(
            manifest_path(Path::new("/tmp/stage-a/rust/src/sub/mod.rs"), Some(root)).unwrap(),
            PathBuf::from("src/sub/mod.rs")
        );
        assert_eq!(
            manifest_path(Path::new("/tmp/stage-a/rust/lib.rs"), None).unwrap(),
            PathBuf::from("/tmp/stage-a/rust/lib.rs")
        );

        // Paths equal to or outside `--source-root` fail closed.
        let escape = manifest_path(Path::new("/tmp/stage-b/rust/lib.rs"), Some(root)).unwrap_err();
        assert_eq!(escape.status, "unsupported");
        assert!(escape.diagnostics[0].contains("escapes --source-root"), "{escape:?}");

        let same = manifest_path(root, Some(root)).unwrap_err();
        assert_eq!(same.status, "unsupported");
        assert!(same.diagnostics[0].contains("must be a file inside --source-root"), "{same:?}");
    }

    #[test]
    fn resolved_scope_validates_exclude_trait_allowlist_and_crate_scope() {
        let base = [
            "anneal-rustc-capture capture",
            "--crate-root=lib.rs",
            "--crate-name=demo",
            "--target=x86_64-unknown-linux-gnu",
            "--out-dir=out",
            "--source-file=lib.rs",
        ];

        // Default crate scope keeps `excluded_traits` empty.
        let args = Args::try_parse_from(base.into_iter().chain(["--scope=crate"])).unwrap();
        assert_eq!(
            args.resolved_scope().unwrap(),
            ir::Scope::Crate { excluded_traits: BTreeSet::new() }
        );

        // Repeatable `--exclude-trait` deduplicates and sorts canonically.
        let args = Args::try_parse_from(base.into_iter().chain([
            "--scope=crate",
            "--exclude-trait=core::fmt::Display",
            "--exclude-trait=core::fmt::Debug",
            "--exclude-trait=core::error::Error",
            "--exclude-trait=core::fmt::Debug",
        ]))
        .unwrap();
        assert_eq!(
            args.resolved_scope().unwrap(),
            ir::Scope::Crate {
                excluded_traits: BTreeSet::from([
                    ir::ExcludedTrait::Error,
                    ir::ExcludedTrait::Debug,
                    ir::ExcludedTrait::Display,
                ]),
            }
        );

        // Non-allowlisted traits fail closed.
        for bad in ["core::ops::Drop", "core::clone::Clone", "std::fmt::Debug", "Debug"] {
            let args = Args::try_parse_from(
                base.into_iter()
                    .chain(["--scope=crate", "--exclude-trait", bad]),
            )
            .unwrap();
            let err = args.resolved_scope().unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert!(
                err.diagnostics[0].contains("not in the closed --exclude-trait allowlist"),
                "{bad}: {err:?}"
            );
        }

        // Combining `--exclude-trait` with `--select` or `--instantiate` fails
        // closed.
        for sel in [
            "--select=f",
            "--instantiate={\"path\":\"f\",\"args\":[\"u64\"]}",
        ] {
            let args = Args::try_parse_from(
                base.into_iter()
                    .chain([sel, "--exclude-trait=core::fmt::Debug"]),
            )
            .unwrap();
            let err = args.resolved_scope().unwrap_err();
            assert_eq!(err.status, "unsupported");
            assert!(
                err.diagnostics[0].contains("--exclude-trait is valid only with --scope crate"),
                "{sel}: {err:?}"
            );
        }
    }
}
