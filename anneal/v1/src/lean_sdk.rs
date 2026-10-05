// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Admitted Lean installations and workspaces pinned to them for their lifetime.
//!
//! The publisher validates bytes, artifact families, sources, and compatibility.
//! Consumers trust that admission and continued installation immutability. This
//! module checks the small descriptor and workspace ownership, never repairs the
//! installation or hashes shared compiled modules on invocation. Ownership files
//! are cooperative provenance records, not authentication of arbitrary OLeans.
//! Local-source freshness still requires a Lake build and fresh consuming workers.

use std::{
    borrow::Cow,
    collections::BTreeSet,
    fs::{self, OpenOptions},
    io::{Read, Write},
    path::{Component, Path, PathBuf},
    process::Command,
};

use anyhow::{Context as _, Result, bail, ensure};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

const SCHEMA: u32 = 1;
const BINDING: &str = ".anneal-sdk.json";
const OUTPUT_OWNER: &str = ".lake/.anneal-owner.json";
const PRIVATE_RUNTIME: &str = ".runtime";
const LAKE_CONFIGURATION: &str = ".anneal-lake.json";
const MAX_DESCRIPTOR_SIZE: u64 = 64 * 1024;
const MAX_MODULES_SIZE: u64 = 32 * 1024 * 1024;

/// The local saved-input snapshot changed while it was being observed. This
/// makes that observation obsolete; admission and permanent I/O errors are
/// deliberately not classified as changes.
#[derive(Debug)]
pub(crate) struct SourceStampChanged(String);

impl SourceStampChanged {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl std::fmt::Display for SourceStampChanged {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for SourceStampChanged {}

/// A coherent observation of saved inputs, with enough private provenance to
/// validate the owner's controlled root rename without weakening live stamps.
#[derive(Debug)]
pub(crate) struct SavedInputSnapshot {
    stamp: [u8; 32],
    relocation_stamp: [u8; 32],
    root_identity: Vec<u8>,
}

impl SavedInputSnapshot {
    pub(crate) fn stamp(&self) -> [u8; 32] {
        self.stamp
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Descriptor {
    schema: u32,
    id: String,
    lean_toolchain: String,
    compiler_hash: String,
    platform: String,
    runtime: PathBuf,
    source_roots: Vec<PathBuf>,
    import_roots: Vec<PathBuf>,
    loader_roots: Vec<PathBuf>,
    plugins: Vec<Plugin>,
    modules: PathBuf,
    modules_sha256: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Plugin {
    /// The resolved immutable native library, suitable for `inputFile`.
    pub path: PathBuf,
    /// Lean's native-library name, independent of its platform suffix.
    pub name: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ModuleManifest {
    schema: u32,
    modules: Vec<String>,
}

/// One publisher-admitted installation, including its immutable module map.
#[derive(Clone, Debug)]
pub struct LeanSdk {
    root: PathBuf,
    installation: PathBuf,
    descriptor_sha256: String,
    descriptor: Descriptor,
    modules: BTreeSet<String>,
    folded_modules: BTreeSet<String>,
    imports: Vec<PathBuf>,
    sources: Vec<PathBuf>,
    loaders: Vec<PathBuf>,
    plugins: Vec<Plugin>,
}

impl LeanSdk {
    /// Resolve a published `lean-sdk` directory. No compiler is run or input
    /// modified. The module manifest is read once per admitted SDK object.
    pub fn load(root: &Path) -> Result<Self> {
        let root = fs::canonicalize(root)
            .with_context(|| format!("Lean SDK is not installed at {}", root.display()))?;
        ensure!(root.to_str().is_some(), "Lean SDK root must be UTF-8");
        ensure!(root.is_dir(), "Lean SDK root is not a directory");
        let installation =
            root.parent().context("Lean SDK has no installation parent")?.to_path_buf();
        let raw = read_small(&root.join("sdk.json"), MAX_DESCRIPTOR_SIZE)?;
        let descriptor: Descriptor =
            serde_json::from_slice(&raw).context("Invalid SDK descriptor")?;
        ensure!(descriptor.schema == SCHEMA, "Unsupported SDK descriptor schema");
        ensure!(is_sha256(&descriptor.id), "Invalid SDK identity");
        ensure!(is_lower_hex(&descriptor.compiler_hash, 40), "Invalid Lean compiler commit hash");
        ensure!(is_sha256(&descriptor.modules_sha256), "Invalid module manifest hash");
        ensure!(
            descriptor.platform == host_platform()?,
            "SDK platform {} does not match this host",
            descriptor.platform
        );
        ensure!(
            !descriptor.lean_toolchain.is_empty()
                && !descriptor.lean_toolchain.contains(['\n', '\r', '\0']),
            "Invalid SDK Lean toolchain"
        );
        let runtime = resolve_shared(&root, &installation, &descriptor.runtime, true)?;
        ensure!(runtime != root, "SDK runtime must name the publisher's compiler closure");
        for launcher in ["lean", "lake"] {
            check_launcher(&root.join("bin").join(launcher), &installation)?;
        }
        let imports = resolve_roots(&root, &installation, &descriptor.import_roots)?;
        let sources = resolve_roots(&root, &installation, &descriptor.source_roots)?;
        let loaders = resolve_roots(&root, &installation, &descriptor.loader_roots)?;
        ensure!(
            !imports.is_empty() && !sources.is_empty() && !loaders.is_empty(),
            "Incomplete SDK search paths"
        );
        // The published view, rather than arbitrary extra import roots, is the
        // compiler installation. Lake also uses its standard sysroot search path.
        ensure!(
            descriptor.import_roots == [PathBuf::from("lib/lean")],
            "SDK must expose its unified lib/lean import view"
        );
        let mut names = BTreeSet::new();
        let mut plugins = Vec::new();
        for plugin in &descriptor.plugins {
            ensure!(valid_component(&plugin.name), "Invalid native plugin name");
            ensure!(names.insert(plugin.name.clone()), "Duplicate native plugin name");
            plugins.push(Plugin {
                path: resolve_shared(&root, &installation, &plugin.path, false)?,
                name: plugin.name.clone(),
            });
        }
        ensure!(
            descriptor.modules == Path::new("modules.json"),
            "Unsupported module manifest location"
        );
        let modules_raw = read_small(&root.join(&descriptor.modules), MAX_MODULES_SIZE)?;
        ensure!(
            sha256(&modules_raw) == descriptor.modules_sha256,
            "SDK module manifest hash mismatch"
        );
        let manifest: ModuleManifest =
            serde_json::from_slice(&modules_raw).context("Invalid module manifest")?;
        ensure!(manifest.schema == SCHEMA, "Unsupported module manifest schema");
        ensure!(!manifest.modules.is_empty(), "SDK exports no modules");
        let mut modules = BTreeSet::new();
        let mut folded_modules = BTreeSet::new();
        let folds_case = filesystem_folds_ascii_case(&root.join("modules.json"))?;
        for name in manifest.modules {
            ensure!(valid_module(&name), "Invalid SDK module identity: {name}");
            ensure!(modules.insert(name.clone()), "Duplicate exact SDK module: {name}");
            let unique_folded = folded_modules.insert(name.to_ascii_lowercase());
            ensure!(unique_folded || !folds_case, "Case-equivalent SDK module providers: {name}");
        }
        let sdk = Self {
            root,
            installation,
            descriptor_sha256: sha256(&raw),
            descriptor,
            modules,
            folded_modules,
            imports,
            sources,
            loaders,
            plugins,
        };
        command_search_paths(&sdk, None)?;
        Ok(sdk)
    }

    pub fn id(&self) -> &str {
        &self.descriptor.id
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn lean_toolchain(&self) -> &str {
        &self.descriptor.lean_toolchain
    }

    pub fn plugins(&self) -> &[Plugin] {
        &self.plugins
    }

    fn check_descriptor(&self) -> Result<()> {
        ensure!(
            sha256(&read_small(&self.root.join("sdk.json"), MAX_DESCRIPTOR_SIZE)?)
                == self.descriptor_sha256,
            "SDK descriptor changed after admission"
        );
        for launcher in ["lean", "lake"] {
            check_launcher(&self.root.join("bin").join(launcher), &self.installation)?;
        }
        for plugin in &self.plugins {
            ensure!(
                plugin.path.is_file(),
                "Missing admitted native plugin: {}",
                plugin.path.display()
            );
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Binding {
    schema: u32,
    sdk_id: String,
    sdk_root: PathBuf,
    descriptor_sha256: String,
    workspace: PathBuf,
    owner: String,
    source_roots: Vec<PathBuf>,
}

/// The supported generated Lake library uses exact module globs and a bound
/// source root. Arbitrary executable Lake configuration is outside this API.
pub struct LakeLibrary<'a> {
    pub name: &'a str,
    pub source_root: &'a str,
    pub modules: &'a [String],
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LakeConfiguration {
    libraries: Vec<LibraryConfiguration>,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct LibraryConfiguration {
    name: String,
    source_root: PathBuf,
    modules: Vec<String>,
}

/// A workspace's shared SDK and private outputs have one fixed owner.
pub struct Workspace<'a> {
    sdk: Cow<'a, LeanSdk>,
    root: PathBuf,
    binding: Binding,
}

pub enum LakeOperation<'a> {
    /// Build ordinary local targets; supported explicit facet is `:olean`.
    Build(&'a [String]),
    SetupFile(&'a Path),
    /// Stock Lake server startup, with the workspace's setup/plugin metadata.
    Serve,
    Version,
}

pub enum LeanOperation<'a> {
    /// Inspect a local source. Callers must first build its saved local imports
    /// before treating this inspection as verification of current sources.
    Check {
        file: &'a Path,
        json: bool,
    },
    Server,
    Version,
    PrintPrefix,
    GitHash,
}

impl<'a> Workspace<'a> {
    /// Write the known generated Lake configuration and its declarative spec.
    /// Admission compares the entire Lakefile against this same renderer; it
    /// does not infer effective roots by parsing arbitrary Lean programs. The
    /// spec is local configuration, subordinate to the fixed SDK/root binding.
    pub fn write_lakefile(sdk: &LeanSdk, root: &Path, libraries: &[LakeLibrary<'_>]) -> Result<()> {
        sdk.check_descriptor()?;
        reject_links(root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        ensure!(
            binding.schema == SCHEMA
                && binding.sdk_id == sdk.id()
                && binding.sdk_root == sdk.root()
                && binding.descriptor_sha256 == sdk.descriptor_sha256,
            "Lake configuration SDK binding mismatch"
        );
        let configuration = LakeConfiguration {
            libraries: libraries
                .iter()
                .map(|library| LibraryConfiguration {
                    name: library.name.to_owned(),
                    source_root: PathBuf::from(library.source_root),
                    modules: library.modules.to_vec(),
                })
                .collect(),
        };
        validate_lake_configuration(&configuration, &binding.source_roots)?;
        reject_reserved_source_aliases(
            &binding.source_roots,
            filesystem_folds_ascii_case(&root.join(BINDING))?,
        )?;
        let lakefile = render_lakefile(sdk, &configuration)?;
        for filename in [LAKE_CONFIGURATION, "lakefile.lean"] {
            reject_links(&root.join(filename))?;
        }
        ensure!(!root.join("lakefile.toml").try_exists()?, "Unsupported alternate Lakefile");
        fs::write(root.join(LAKE_CONFIGURATION), serde_json::to_vec_pretty(&configuration)?)?;
        fs::write(root.join("lakefile.lean"), lakefile)?;
        Ok(())
    }

    pub fn create(sdk: &'a LeanSdk, root: &Path, source_roots: &[&str]) -> Result<Self> {
        Self::stage(sdk, root, root, None, source_roots)?;
        Self::open(sdk, root)
    }

    /// Bind a fresh source-generation stage to its eventual physical root.
    /// When preserving an existing workspace this writes only the binding;
    /// the owner must admit `existing` and transfer its complete `.lake` and
    /// `.runtime` trees before installing the stage at the same final root.
    /// No newly generated or externally supplied output tree is adopted.
    pub fn stage(
        sdk: &'a LeanSdk,
        staging_root: &Path,
        final_root: &Path,
        existing: Option<&Self>,
        source_roots: &[&str],
    ) -> Result<()> {
        sdk.check_descriptor()?;
        let staging_root = new_physical_path(staging_root)?;
        let final_root = new_physical_path(final_root)?;
        ensure!(
            !staging_root.starts_with(&sdk.installation),
            "Workspace stage is inside the immutable installation"
        );
        ensure!(
            !final_root.starts_with(&sdk.installation),
            "Workspace is inside the immutable installation"
        );
        let source_roots = validate_source_roots(source_roots)?;
        command_search_paths(sdk, Some((&final_root, &source_roots)))?;
        let binding = if let Some(existing) = existing {
            existing.admit()?;
            ensure!(existing.root == final_root, "Cannot move an existing workspace binding");
            ensure!(
                existing.binding.sdk_id == sdk.id(),
                "Cannot upgrade an existing workspace SDK"
            );
            ensure!(
                existing.binding.descriptor_sha256 == sdk.descriptor_sha256,
                "Cannot change an existing workspace descriptor"
            );
            ensure!(
                existing.binding.source_roots == source_roots,
                "Cannot change bound source-root mapping"
            );
            existing.binding.clone()
        } else {
            ensure!(!final_root.try_exists()?, "Workspace creation requires a fresh final path");
            let owner = tempfile::Builder::new()
                .prefix(".anneal-owner-")
                .tempfile_in(final_root.parent().unwrap())?;
            reject_reserved_source_aliases(
                &source_roots,
                filesystem_folds_ascii_case(owner.path())?,
            )?;
            Binding {
                schema: SCHEMA,
                sdk_id: sdk.id().to_owned(),
                sdk_root: sdk.root().to_path_buf(),
                descriptor_sha256: sdk.descriptor_sha256.clone(),
                workspace: final_root,
                owner: owner.path().file_name().unwrap().to_string_lossy().into_owned(),
                source_roots,
            }
        };
        fs::create_dir(&staging_root).context("Workspace stage must be a nonexistent directory")?;
        write_new_json(&staging_root.join(BINDING), &binding)?;
        if existing.is_none() {
            fs::create_dir(staging_root.join(".lake"))?;
            write_new_json(&staging_root.join(OUTPUT_OWNER), &binding)?;
            fs::create_dir(staging_root.join(PRIVATE_RUNTIME))?;
            for dir in ["home", "cache", "config", "data", "tmp"] {
                fs::create_dir(staging_root.join(PRIVATE_RUNTIME).join(dir))?;
            }
        }
        Ok(())
    }

    pub fn admit_stage(sdk: &LeanSdk, stage: &Path, final_root: &Path) -> Result<()> {
        sdk.check_descriptor()?;
        reject_links(stage)?;
        let binding: Binding = read_json(&stage.join(BINDING))?;
        ensure!(binding.schema == SCHEMA && !binding.owner.is_empty(), "Invalid stage owner");
        ensure!(
            binding.sdk_id == sdk.id()
                && binding.sdk_root == sdk.root()
                && binding.descriptor_sha256 == sdk.descriptor_sha256
                && binding.workspace == new_physical_path(final_root)?,
            "Stage binding changed"
        );
        validate_bound_source_roots(&binding.source_roots)?;
        command_search_paths(sdk, Some((&binding.workspace, &binding.source_roots)))?;
        check_lake_configuration(sdk, stage, &binding.source_roots, false)?;
        let folds_case = filesystem_folds_ascii_case(&stage.join(BINDING))?;
        reject_reserved_source_aliases(&binding.source_roots, folds_case)?;
        let mut local_modules = BTreeSet::new();
        for source in &binding.source_roots {
            let source = stage.join(source);
            if source.try_exists()? {
                check_local_sources(&source, &source, stage, sdk, folds_case, &mut local_modules)?;
            }
        }
        // Also establish that every saved input will be tracked on invocation.
        saved_inputs(stage)?;
        Ok(())
    }

    pub fn open(sdk: &'a LeanSdk, root: &Path) -> Result<Self> {
        let root = fs::canonicalize(root).context("Unknown Lean workspace")?;
        ensure!(root.to_str().is_some(), "Lean workspace path must be UTF-8");
        reject_links(&root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        let workspace = Self { sdk: Cow::Borrowed(sdk), root, binding };
        workspace.admit()?;
        Ok(workspace)
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Resolve the fixed SDK selected when this workspace was created. This
    /// gateway never resolves the current global toolchain or ambient Elan.
    pub fn from_root(root: &Path) -> Result<Workspace<'static>> {
        let root = fs::canonicalize(root).context("Unknown Lean workspace")?;
        ensure!(root.to_str().is_some(), "Lean workspace path must be UTF-8");
        reject_links(&root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        ensure!(binding.schema == SCHEMA, "Unsupported workspace binding schema");
        ensure!(binding.sdk_root.is_absolute(), "Workspace SDK path must be absolute");
        let sdk = LeanSdk::load(&binding.sdk_root)?;
        let workspace = Workspace { sdk: Cow::Owned(sdk), root, binding };
        workspace.admit()?;
        Ok(workspace)
    }

    /// The lock is a sibling of the replaceable workspace directory. All Anneal
    /// source/output writers use it; locks do not control direct user edits.
    pub fn lock_root(root: &Path) -> Result<fs::File> {
        let file = open_workspace_lock(root, false)?;
        fs2::FileExt::lock_exclusive(&file)?;
        Ok(file)
    }

    pub fn writer_lock(&self) -> Result<fs::File> {
        let file = Self::lock_root(&self.root)?;
        self.admit()?;
        Ok(file)
    }

    pub fn try_writer_lock(&self) -> Result<Option<fs::File>> {
        self.try_lock(false)
    }

    pub fn try_shared_lock(&self) -> Result<Option<fs::File>> {
        self.try_lock(true)
    }

    /// One mutable-document coordinator per workspace. This separate lease
    /// leaves batch writers free to build while the editor is open.
    pub fn server_lock(&self) -> Result<fs::File> {
        self.admit()?;
        let file = open_workspace_lock(&self.root, true)?;
        fs2::FileExt::try_lock_exclusive(&file).context(
            "An editor coordinator already owns this workspace; close it before starting another",
        )?;
        Ok(file)
    }

    fn try_lock(&self, shared: bool) -> Result<Option<fs::File>> {
        let file = open_workspace_lock(&self.root, false)?;
        let result = if shared {
            fs2::FileExt::try_lock_shared(&file)
        } else {
            fs2::FileExt::try_lock_exclusive(&file)
        };
        match result {
            Ok(()) => {
                self.admit()?;
                Ok(Some(file))
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => Ok(None),
            Err(error) => Err(error.into()),
        }
    }

    /// Local sources and the exact published SDK source providers may be opened
    /// by the editor. A canonical source reached through a definition link is
    /// checked against its module in the published view, without walking Mathlib.
    pub fn contains_source(&self, path: &Path) -> Result<bool> {
        self.admit()?;
        if path.starts_with(&self.root) {
            return self.local_source(path).map(|_| true);
        }
        self.contains_sdk_source(path)
    }

    pub fn contains_sdk_source(&self, path: &Path) -> Result<bool> {
        self.admit()?;
        if path.extension().is_none_or(|s| s != "lean") {
            return Ok(false);
        }
        let physical = fs::canonicalize(path)?;
        let parts = physical
            .components()
            .map(|c| c.as_os_str().to_str().context("Non-UTF8 SDK source path"))
            .collect::<Result<Vec<_>>>()?;
        for start in 0..parts.len() {
            let relative: PathBuf = parts[start..].iter().collect();
            let module = relative
                .with_extension("")
                .iter()
                .map(|c| c.to_str().context("Non-UTF8 SDK module"))
                .collect::<Result<Vec<_>>>()?
                .join(".");
            if self.sdk.modules.contains(&module) {
                for source in &self.sdk.sources {
                    if fs::canonicalize(source.join(&relative)).ok().as_ref() == Some(&physical) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    /// Stock editor project detection follows the original SDK source markers.
    /// Admit that root only as a source-only route back to this bound consumer;
    /// it never becomes Lake's cwd or an output location. Cache this admission
    /// for the source client's lifetime under the immutable-installation premise.
    pub fn admit_sdk_source_project(&self, root: &Path) -> Result<bool> {
        self.admit()?;
        let Ok(root) = fs::canonicalize(root) else { return Ok(false) };
        if !root.is_dir() || !root.starts_with(&self.sdk.installation) {
            return Ok(false);
        }
        for source in &self.sdk.sources {
            if root == *source {
                return Ok(true);
            }
            for module in &self.sdk.modules {
                let file = source.join(module.replace('.', "/")).with_extension("lean");
                if let Ok(file) = fs::canonicalize(file) {
                    if file.starts_with(&root) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    pub fn source_roots(&self) -> Vec<PathBuf> {
        self.binding.source_roots.iter().map(|p| self.root.join(p)).collect()
    }

    pub fn sdk(&self) -> &LeanSdk {
        &self.sdk
    }

    /// Observe case equivalence on this already-admitted workspace filesystem.
    pub(crate) fn folds_ascii_case(&self) -> Result<bool> {
        filesystem_folds_ascii_case(&self.root.join(BINDING))
    }

    /// Fingerprint the saved local Lean inputs and Lake configuration. Compare
    /// stamps around builds and checks before accepting their results as current.
    /// Private incremental outputs and caches are deliberately excluded. File
    /// and directory modification identities catch ordinary edit-and-restore
    /// races, including replacement of an entire saved-source tree.
    pub fn source_stamp(&self) -> Result<[u8; 32]> {
        Ok(self.source_snapshot()?.stamp())
    }

    pub(crate) fn source_snapshot(&self) -> Result<SavedInputSnapshot> {
        self.admit()?;
        snapshot_saved_inputs(&self.root, |_| {})
    }

    /// Observe an already-admitted workspace after its owner has renamed it to
    /// a sibling backup. This cannot open commands, adopt outputs, or retarget
    /// its binding; it only rechecks the saved-input snapshot before a swap.
    /// The caller must compare the full live stamp to `original` immediately
    /// before its isolation rename, and call this before transferring outputs.
    pub(crate) fn source_stamp_at(
        &self,
        relocated_root: &Path,
        original: &SavedInputSnapshot,
    ) -> Result<[u8; 32]> {
        let relocated_root = new_physical_path(relocated_root)?;
        ensure!(
            relocated_root.parent() == self.root.parent() && relocated_root.is_dir(),
            "Saved-input backup must be a physical sibling of its bound workspace"
        );
        let binding: Binding = read_json(&relocated_root.join(BINDING))?;
        ensure!(binding == self.binding, "Saved-input backup binding changed");
        ensure!(
            physical_directory_identity(&fs::metadata(&relocated_root)?)? == original.root_identity,
            "Saved-input backup has a different physical root"
        );
        let relocated = snapshot_saved_inputs(&relocated_root, |_| {})?;
        ensure!(
            relocated.root_identity == original.root_identity,
            "Saved-input backup has a different physical root"
        );
        ensure!(
            relocated.relocation_stamp == original.relocation_stamp,
            SourceStampChanged::new("Saved Lean inputs changed while isolating their state")
        );
        Ok(original.stamp())
    }

    /// Recheck ownership at an invocation or private-output transfer boundary.
    pub fn admit(&self) -> Result<()> {
        self.sdk.check_descriptor()?;
        reject_links(&self.root)?;
        ensure!(self.root.is_dir(), "Workspace disappeared");
        let binding: Binding = read_json(&self.root.join(BINDING))?;
        ensure!(binding == self.binding, "Workspace binding changed after opening");
        reject_workspace_lock_name(&self.root, Some(&self.root.join(BINDING)))?;
        ensure!(binding.schema == SCHEMA, "Unsupported workspace binding schema");
        ensure!(binding.sdk_id == self.sdk.id(), "Workspace SDK identity mismatch");
        ensure!(binding.sdk_root == self.sdk.root(), "Workspace SDK location mismatch");
        ensure!(
            binding.descriptor_sha256 == self.sdk.descriptor_sha256,
            "Workspace SDK descriptor mismatch"
        );
        ensure!(
            binding.workspace == self.root && !binding.owner.is_empty(),
            "Workspace location or owner mismatch"
        );
        validate_bound_source_roots(&binding.source_roots)?;
        command_search_paths(&self.sdk, Some((&self.root, &binding.source_roots)))?;
        check_lake_configuration(&self.sdk, &self.root, &binding.source_roots, false)?;
        for private in [".lake", PRIVATE_RUNTIME] {
            check_private_tree(&self.root.join(private))?;
        }
        let owner: Binding = read_json(&self.root.join(OUTPUT_OWNER))?;
        ensure!(owner == binding, "Private output ownership mismatch");
        for private in ["home", "cache", "config", "data", "tmp"] {
            ensure!(
                self.root.join(PRIVATE_RUNTIME).join(private).is_dir(),
                "Missing private runtime directory: {private}"
            );
        }
        let mut local_modules = BTreeSet::new();
        let folds_case = filesystem_folds_ascii_case(&self.root.join(OUTPUT_OWNER))?;
        reject_reserved_source_aliases(
            &binding.source_roots,
            filesystem_folds_ascii_case(&self.root.join(BINDING))?,
        )?;
        for source in &binding.source_roots {
            let source = self.root.join(source);
            if source.try_exists()? {
                check_local_sources(
                    &source,
                    &source,
                    &self.root,
                    &self.sdk,
                    folds_case,
                    &mut local_modules,
                )?;
            }
        }
        Ok(())
    }

    pub fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
        let mut command = self.command("lake")?;
        // RC2 recognizes --version before its ordinary option parser; it must
        // be the first argument. Version inspection cannot schedule builds.
        if !matches!(operation, LakeOperation::Version) {
            check_lake_configuration(&self.sdk, &self.root, &self.binding.source_roots, true)?;
            command.args(["--keep-toolchain", "--no-cache", "--reconfigure"]);
        }
        match operation {
            LakeOperation::Build(targets) => {
                command.arg("build");
                for target in targets {
                    ensure!(valid_build_target(target), "Unsupported Lake build target: {target}");
                    command.arg(target);
                }
            }
            LakeOperation::SetupFile(file) => {
                command.arg("setup-file").arg(self.local_source(file)?);
            }
            LakeOperation::Serve => {
                command.arg("serve");
            }
            LakeOperation::Version => {
                command.arg("--version");
            }
        }
        Ok(command)
    }

    pub fn lean_command(&self, operation: LeanOperation<'_>) -> Result<Command> {
        let mut command = self.command("lean")?;
        command.arg(format!("--root={}", self.root.display()));
        for plugin in &self.sdk.plugins {
            command.arg(format!("--plugin={}", plugin.path.display()));
        }
        match operation {
            LeanOperation::Check { file, json } => {
                if json {
                    command.arg("--json");
                }
                // Preserve relative diagnostic filenames under the fixed cwd.
                let source = self.local_source(file)?;
                let relative = source.strip_prefix(&self.root)?;
                if relative.as_os_str().as_encoded_bytes().starts_with(b"-") {
                    command.arg(Path::new(".").join(relative));
                } else {
                    command.arg(relative);
                }
            }
            LeanOperation::Server => {
                command.arg("--server");
            }
            LeanOperation::Version => {
                command.arg("--version");
            }
            LeanOperation::PrintPrefix => {
                command.arg("--print-prefix");
            }
            LeanOperation::GitHash => {
                command.arg("--githash");
            }
        }
        Ok(command)
    }

    fn local_source(&self, file: &Path) -> Result<PathBuf> {
        ensure!(
            !file.components().any(|c| matches!(c, Component::ParentDir)),
            "Lean source path cannot traverse parent directories"
        );
        let file = if file.is_absolute() { file.to_path_buf() } else { self.root.join(file) };
        ensure!(file.starts_with(&self.root), "Lean source is outside its workspace");
        reject_links(&file)?;
        let folds_case = filesystem_folds_ascii_case(&self.root.join(BINDING))?;
        ensure!(
            file.is_file()
                && file.extension().and_then(|s| s.to_str()).is_some_and(|s| {
                    s == "lean" || (folds_case && s.eq_ignore_ascii_case("lean"))
                }),
            "Expected an existing local Lean source"
        );
        ensure!(
            file.strip_prefix(&self.root)?.components().all(|part| {
                !matches!(part, Component::Normal(name) if reserved_private_name(name, folds_case))
            }),
            "Source must not come from ignored private output/cache trees"
        );
        Ok(file)
    }

    fn command(&self, tool: &str) -> Result<Command> {
        self.admit()?;
        let mut command = Command::new(self.sdk.root.join("bin").join(tool));
        command.current_dir(&self.root).env_clear();
        // An allowlist excludes all ambient tool selectors, imports, dynamic
        // loader injections, native compiler overrides, and external caches.
        for key in ["LANG", "LC_ALL", "LC_CTYPE", "TZ", "TERM"] {
            if let Some(value) = std::env::var_os(key) {
                command.env(key, value);
            }
        }
        let private = self.root.join(PRIVATE_RUNTIME);
        let search_paths =
            command_search_paths(&self.sdk, Some((&self.root, &self.binding.source_roots)))?;
        command.env("PATH", search_paths.path);
        command.env("HOME", private.join("home"));
        command.env("XDG_CACHE_HOME", private.join("cache"));
        command.env("XDG_CONFIG_HOME", private.join("config"));
        command.env("XDG_DATA_HOME", private.join("data"));
        for key in ["TMPDIR", "TMP", "TEMP"] {
            command.env(key, private.join("tmp"));
        }
        command.env("LEAN", self.sdk.root.join("bin/lean"));
        command.env("LAKE", self.sdk.root.join("bin/lake"));
        command.env("LEAN_SYSROOT", &self.sdk.root);
        command.env("LAKE_HOME", &self.sdk.root);
        command.env("LAKE_OVERRIDE_LEAN", "true");
        command.env("LEAN_NUM_THREADS", "1");
        command.env("LAKE_ARTIFACT_CACHE", "false");
        command.env("LAKE_RESTORE_ARTIFACTS", "false");
        command.env("LAKE_CACHE_DIR", private.join("cache"));
        command.env("MATHLIB_NO_CACHE_ON_UPDATE", "1");
        command.env("LEAN_PATH", search_paths.imports);
        command.env("LEAN_SRC_PATH", search_paths.sources);
        command.env("LD_LIBRARY_PATH", &search_paths.loaders);
        command.env("DYLD_LIBRARY_PATH", search_paths.loaders);
        Ok(command)
    }
}

struct CommandSearchPaths {
    path: std::ffi::OsString,
    imports: std::ffi::OsString,
    sources: std::ffi::OsString,
    loaders: std::ffi::OsString,
}

/// Validate and serialize the exact command input closure before it can be
/// persisted as an SDK/workspace binding. Do not substitute lossy strings or
/// blacklist a platform-specific separator instead of using `join_paths`.
fn command_search_paths(
    sdk: &LeanSdk,
    workspace: Option<(&Path, &[PathBuf])>,
) -> Result<CommandSearchPaths> {
    let mut paths = vec![sdk.root.join("bin")];
    paths.extend(["/usr/bin", "/bin", "/usr/sbin", "/sbin"].map(PathBuf::from));
    let mut imports = Vec::new();
    let mut sources = Vec::new();
    if let Some((root, source_roots)) = workspace {
        imports.push(root.join(".lake/build/lib/lean"));
        sources.extend(source_roots.iter().map(|source| root.join(source)));
    }
    imports.extend(sdk.imports.iter().cloned());
    sources.extend(sdk.sources.iter().cloned());
    Ok(CommandSearchPaths {
        path: std::env::join_paths(paths).context("SDK PATH cannot represent its input paths")?,
        imports: std::env::join_paths(imports)
            .context("LEAN_PATH cannot represent its input paths")?,
        sources: std::env::join_paths(sources)
            .context("LEAN_SRC_PATH cannot represent its input paths")?,
        loaders: std::env::join_paths(&sdk.loaders)
            .context("Native loader search list cannot represent its input paths")?,
    })
}

#[cfg(test)]
fn stamp_saved_inputs(root: &Path, mut after_recording: impl FnMut(&Path)) -> Result<[u8; 32]> {
    Ok(snapshot_saved_inputs(root, &mut after_recording)?.stamp())
}

fn snapshot_saved_inputs(
    root: &Path,
    mut after_recording: impl FnMut(&Path),
) -> Result<SavedInputSnapshot> {
    let inputs = saved_inputs_with_change_detection(root, true)?;
    let mut hasher = Sha256::new();
    let mut identities = Vec::new();
    let mut directories = Vec::new();
    let mut root_state = None;
    for path in &inputs.directories {
        reject_links(path)?;
        let metadata = saved_input_io(fs::metadata(path), true)?;
        let before = directory_modification_identity(&metadata)?;
        if path == root {
            root_state = Some((before.clone(), physical_directory_identity(&metadata)?));
        } else {
            let relative = path.strip_prefix(root)?.as_os_str().as_encoded_bytes();
            hasher.update(b"directory");
            hasher.update((relative.len() as u64).to_le_bytes());
            hasher.update(relative);
            hasher.update((before.len() as u64).to_le_bytes());
            hasher.update(&before);
        }
        directories.push((path, before));
    }
    for path in &inputs.files {
        reject_links(path)?;
        let relative = path.strip_prefix(root)?.as_os_str().as_encoded_bytes();
        hasher.update(b"file");
        hasher.update((relative.len() as u64).to_le_bytes());
        hasher.update(relative);
        let mut file = saved_input_io(fs::File::open(path), true)
            .with_context(|| format!("Saved input disappeared: {}", path.display()))?;
        let before = modification_identity(&saved_input_io(file.metadata(), true)?)?;
        hasher.update((before.len() as u64).to_le_bytes());
        hasher.update(&before);
        let mut buffer = [0u8; 64 * 1024];
        loop {
            let count = saved_input_io(file.read(&mut buffer), true)?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
        }
        ensure!(
            before == modification_identity(&saved_input_io(file.metadata(), true)?)?
                && before == modification_identity(&saved_input_io(fs::metadata(path), true)?)?,
            SourceStampChanged::new(format!(
                "Saved Lean input changed while recording its state: {}",
                path.display()
            ))
        );
        identities.push((path, before));
        after_recording(path);
    }
    ensure!(
        inputs == saved_inputs_with_change_detection(root, true)?,
        SourceStampChanged::new("Saved Lean input set changed while recording its state")
    );
    // Revalidate every earlier input after the entire content traversal,
    // not only while that individual file was being read.
    for (path, before) in identities {
        reject_links(path)?;
        ensure!(
            before == modification_identity(&saved_input_io(fs::metadata(path), true)?)?,
            SourceStampChanged::new(format!(
                "Saved Lean input changed while recording its state: {}",
                path.display()
            ))
        );
    }
    for (path, before) in directories {
        reject_links(path)?;
        ensure!(
            before == directory_modification_identity(&saved_input_io(fs::metadata(path), true)?)?,
            SourceStampChanged::new(format!(
                "Saved Lean source directory changed while recording its state: {}",
                path.display()
            ))
        );
    }
    let content_stamp: [u8; 32] = hasher.finalize().into();
    let (root_state, root_identity) = root_state.context("Saved-input snapshot has no root")?;
    let digest = |identity: &[u8]| {
        let mut hasher = Sha256::new();
        hasher.update((identity.len() as u64).to_le_bytes());
        hasher.update(identity);
        hasher.update(content_stamp);
        <[u8; 32]>::from(hasher.finalize())
    };
    Ok(SavedInputSnapshot {
        stamp: digest(&root_state),
        relocation_stamp: digest(&root_identity),
        root_identity,
    })
}

fn saved_input_io<T>(result: std::io::Result<T>, detect_changes: bool) -> Result<T> {
    result.map_err(|error| {
        if detect_changes && error.kind() == std::io::ErrorKind::NotFound {
            SourceStampChanged::new(error.to_string()).into()
        } else {
            error.into()
        }
    })
}

fn host_platform() -> Result<&'static str> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => Ok("aarch64-darwin"),
        ("macos", "x86_64") => Ok("x86_64-darwin"),
        ("linux", "aarch64") => Ok("aarch64-linux"),
        ("linux", "x86_64") => Ok("x86_64-linux"),
        _ => bail!("Unsupported Lean SDK host platform"),
    }
}

fn read_small(path: &Path, limit: u64) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    fs::File::open(path)
        .with_context(|| format!("Missing or unreadable {}", path.display()))?
        .take(limit + 1)
        .read_to_end(&mut bytes)?;
    ensure!(
        bytes.len() as u64 <= limit,
        "Oversized descriptor or ownership file: {}",
        path.display()
    );
    Ok(bytes)
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    reject_links(path)?;
    serde_json::from_slice(&read_small(path, MAX_DESCRIPTOR_SIZE)?)
        .with_context(|| format!("Invalid ownership or binding: {}", path.display()))
}

fn write_new_json(path: &Path, value: &impl Serialize) -> Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    serde_json::to_writer_pretty(&mut file, value)?;
    file.write_all(b"\n")?;
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn is_sha256(text: &str) -> bool {
    is_lower_hex(text, 64)
}

fn is_lower_hex(text: &str, length: usize) -> bool {
    text.len() == length && text.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

fn resolve_shared(
    root: &Path,
    installation: &Path,
    relative: &Path,
    directory: bool,
) -> Result<PathBuf> {
    ensure!(
        !relative.is_absolute() && !relative.as_os_str().is_empty(),
        "SDK path must be relative"
    );
    let resolved = fs::canonicalize(root.join(relative))
        .with_context(|| format!("Missing SDK input: {}", relative.display()))?;
    ensure!(resolved.to_str().is_some(), "Resolved SDK input path must be UTF-8");
    ensure!(
        resolved.starts_with(installation),
        "SDK input escapes the admitted installation: {}",
        relative.display()
    );
    ensure!(
        if directory { resolved.is_dir() } else { resolved.is_file() },
        "Wrong SDK input type: {}",
        relative.display()
    );
    Ok(resolved)
}

fn resolve_roots(root: &Path, installation: &Path, relatives: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut roots = Vec::new();
    for relative in relatives {
        let path = resolve_shared(root, installation, relative, true)?;
        ensure!(!roots.contains(&path), "Duplicate SDK search root");
        roots.push(path);
    }
    Ok(roots)
}

fn check_launcher(path: &Path, installation: &Path) -> Result<()> {
    let metadata = fs::symlink_metadata(path).context("Missing SDK launcher")?;
    ensure!(metadata.file_type().is_file(), "SDK launchers must be real copied files");
    ensure!(fs::canonicalize(path)?.starts_with(installation), "SDK launcher escapes installation");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        ensure!(metadata.permissions().mode() & 0o111 != 0, "SDK launcher is not executable");
    }
    Ok(())
}

fn open_workspace_lock(root: &Path, server: bool) -> Result<fs::File> {
    let root = new_physical_path(root)?;
    let mut leaf = root.file_name().context("Workspace has no leaf")?.to_os_string();
    // Writer filenames end in `.lock`; server leases never do. Appending
    // `.server.lock` would alias the writer lock of a `foo.server` sibling.
    leaf.push(if server { ".server-lease" } else { ".lock" });
    let path = root.with_file_name(leaf);
    reject_links(&path)?;
    let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path)?;
    ensure!(file.metadata()?.is_file(), "Workspace lock is not a regular file");
    Ok(file)
}

fn new_physical_path(path: &Path) -> Result<PathBuf> {
    ensure!(
        !path.components().any(|c| matches!(c, Component::ParentDir)),
        "Workspace path must not traverse parent directories"
    );
    let path =
        if path.is_absolute() { path.to_path_buf() } else { std::env::current_dir()?.join(path) };
    let parent = fs::canonicalize(path.parent().context("Workspace has no parent")?)
        .context("Workspace parent must already exist")?;
    let path = parent.join(path.file_name().context("Workspace must have a directory name")?);
    ensure!(path.to_str().is_some(), "Lean workspace path must be UTF-8");
    reject_links(&path)?;
    reject_workspace_lock_name(&path, None)?;
    Ok(path)
}

fn reject_workspace_lock_name(root: &Path, reference: Option<&Path>) -> Result<()> {
    let leaf = root
        .file_name()
        .and_then(|leaf| leaf.to_str())
        .context("Lean workspace name must be UTF-8")?;
    let reserved =
        |name: &str| [".lock", ".server-lease"].iter().any(|suffix| name.ends_with(suffix));
    ensure!(!reserved(leaf), "Workspace name uses a reserved lock suffix");
    if reserved(&leaf.to_ascii_lowercase()) {
        let folds_case = if let Some(reference) = reference {
            filesystem_folds_ascii_case(reference)?
        } else {
            let probe = tempfile::Builder::new()
                .prefix(".anneal-name-probe-")
                .tempfile_in(root.parent().context("Workspace has no parent")?)?;
            filesystem_folds_ascii_case(probe.path())?
        };
        ensure!(!folds_case, "Workspace name uses a case-equivalent reserved lock suffix");
    }
    Ok(())
}

fn reject_links(path: &Path) -> Result<()> {
    for ancestor in path.ancestors() {
        match fs::symlink_metadata(ancestor) {
            Ok(metadata) => ensure!(
                !metadata.file_type().is_symlink(),
                "Writable path traverses a symlink: {}",
                ancestor.display()
            ),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.into()),
        }
    }
    Ok(())
}

fn validate_source_roots(raw: &[&str]) -> Result<Vec<PathBuf>> {
    let roots: Vec<_> = raw.iter().map(PathBuf::from).collect();
    validate_bound_source_roots(&roots)?;
    Ok(roots)
}

fn validate_bound_source_roots(roots: &[PathBuf]) -> Result<()> {
    ensure!(!roots.is_empty(), "Workspace needs source roots");
    let mut unique = BTreeSet::new();
    for root in roots {
        ensure!(
            !root.as_os_str().is_empty()
                && root.is_relative()
                && root.components().all(|c| matches!(c, Component::CurDir | Component::Normal(_))),
            "Workspace source roots must stay local"
        );
        ensure!(
            root.components().all(|part| !matches!(part, Component::Normal(name)
                if [".lake", PRIVATE_RUNTIME, ".git"].iter().any(|s| name == *s))),
            "Source roots cannot include private output/cache trees"
        );
        ensure!(unique.insert(root), "Duplicate workspace source root");
    }
    Ok(())
}

fn reserved_private_name(name: &std::ffi::OsStr, folds_case: bool) -> bool {
    [".lake", PRIVATE_RUNTIME, ".git"].iter().any(|reserved| {
        name == *reserved
            || (folds_case && name.to_str().is_some_and(|name| name.eq_ignore_ascii_case(reserved)))
    })
}

fn reject_reserved_source_aliases(roots: &[PathBuf], folds_case: bool) -> Result<()> {
    for root in roots {
        ensure!(
            root.components().all(|part| !matches!(part, Component::Normal(name)
                if reserved_private_name(name, folds_case))),
            "Source roots cannot include private output/cache trees or their filesystem aliases"
        );
    }
    Ok(())
}

fn validate_lake_configuration(configuration: &LakeConfiguration, roots: &[PathBuf]) -> Result<()> {
    validate_bound_source_roots(roots)?;
    let mut names = BTreeSet::new();
    let mut configured_roots = BTreeSet::new();
    for library in &configuration.libraries {
        ensure!(valid_component(&library.name), "Unsupported Lake library name");
        ensure!(names.insert(&library.name), "Duplicate Lake library name");
        ensure!(
            configured_roots.insert(&library.source_root),
            "Duplicate Lake library source root"
        );
        for module in &library.modules {
            ensure!(valid_module(module), "Unsupported local Lean module name: {module}");
        }
    }
    ensure!(
        configured_roots == roots.iter().collect(),
        "Lake source roots do not match the workspace binding"
    );
    Ok(())
}

fn render_lakefile(sdk: &LeanSdk, configuration: &LakeConfiguration) -> Result<String> {
    render_lakefile_with_library_escape(sdk, configuration, true)
}

fn render_lakefile_with_library_escape(
    sdk: &LeanSdk,
    configuration: &LakeConfiguration,
    escape_libraries: bool,
) -> Result<String> {
    use std::fmt::Write as _;
    let mut plugins = String::new();
    let mut targets = Vec::new();
    for (index, plugin) in sdk.plugins().iter().enumerate() {
        let target = format!("annealPlugin{index}");
        targets.push(format!("Target.mk (.mk (.packageTarget .anonymous `{target}))"));
        let path =
            serde_json::to_string(plugin.path.to_str().context("Plugin path is not UTF-8")?)?;
        let name = serde_json::to_string(&plugin.name)?;
        writeln!(
            plugins,
            "target {target} : Dynlib := do\n  let artifact : System.FilePath := {path}\n  return (← inputFile artifact false).map fun path =>\n    {{ path := path, name := {name}, plugin := true }}"
        )?;
    }
    let targets = targets.join(", ");
    let mut lakefile = format!(
        "import Lake\nopen Lake DSL\npackage anneal_verification where\n  plugins := #[{targets}]\n{plugins}"
    );
    for library in &configuration.libraries {
        // The validated ASCII grammar excludes guillemets. Escaping every
        // library identifier avoids relying on a fixed list of Lean/Lake
        // keywords, which depends on the imported syntax extensions.
        let name =
            if escape_libraries { format!("«{}»", library.name) } else { library.name.clone() };
        let root =
            serde_json::to_string(library.source_root.to_str().context("Non-UTF8 source root")?)?;
        let globs = library
            .modules
            .iter()
            .map(|module| format!(".one `{module}"))
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            lakefile,
            "@[default_target] lean_lib {} where\n  srcDir := {root}\n  roots := #[]\n  globs := #[{globs}]",
            name
        )?;
    }
    Ok(lakefile)
}

fn check_lake_configuration(
    sdk: &LeanSdk,
    root: &Path,
    source_roots: &[PathBuf],
    required: bool,
) -> Result<()> {
    ensure!(!root.join("lakefile.toml").try_exists()?, "Unsupported alternate Lakefile");
    let spec = root.join(LAKE_CONFIGURATION);
    let lakefile = root.join("lakefile.lean");
    if !required && !spec.try_exists()? && !lakefile.try_exists()? {
        // Fresh stages can be bound before source/configuration generation.
        return Ok(());
    }
    reject_links(&spec)?;
    reject_links(&lakefile)?;
    let configuration: LakeConfiguration =
        serde_json::from_slice(&read_small(&spec, MAX_MODULES_SIZE)?)
            .context("Invalid generated Lake configuration")?;
    validate_lake_configuration(&configuration, source_roots)?;
    let lakefile = read_small(&lakefile, MAX_MODULES_SIZE)?;
    // Existing generated stock workspaces keep their private outputs. Only
    // their exact previous canonical spelling is admitted as compatibility;
    // custom or keyword library identifiers must use the escaped renderer.
    let stock_names = configuration.libraries.iter().all(|library| {
        matches!(library.name.as_str(), "Generated" | "Anneal" | "User")
            || library.name.strip_prefix("Source").is_some_and(|number| {
                !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
            })
    });
    ensure!(
        lakefile == render_lakefile(sdk, &configuration)?.as_bytes()
            || (stock_names
                && lakefile
                    == render_lakefile_with_library_escape(sdk, &configuration, false)?.as_bytes()),
        "Lakefile differs from its bound generated configuration"
    );
    Ok(())
}

fn check_private_tree(path: &Path) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).context("Missing private output/runtime directory")?;
    ensure!(metadata.is_dir(), "Private output/runtime path is not a real directory");
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        ensure!(
            kind.is_dir() || kind.is_file(),
            "Private tree contains a link or special file: {}",
            entry.path().display()
        );
        if kind.is_dir() {
            check_private_tree(&entry.path())?;
        }
    }
    Ok(())
}

fn check_local_sources(
    path: &Path,
    source_root: &Path,
    workspace_root: &Path,
    sdk: &LeanSdk,
    folds_case: bool,
    local_modules: &mut BTreeSet<String>,
) -> Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    ensure!(metadata.is_dir(), "Local source root is not a real directory");
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let name = entry.file_name();
        if reserved_private_name(&name, folds_case) {
            ensure!(
                path == workspace_root,
                "Reserved output/cache directory inside a source root: {}",
                entry.path().display()
            );
            continue;
        }
        let kind = entry.file_type()?;
        ensure!(!kind.is_symlink(), "Local source contains a symlink: {}", entry.path().display());
        ensure!(
            kind.is_dir() || kind.is_file(),
            "Local source contains a special file: {}",
            entry.path().display()
        );
        if kind.is_dir() {
            check_local_sources(
                &entry.path(),
                source_root,
                workspace_root,
                sdk,
                folds_case,
                local_modules,
            )?;
        } else if kind.is_file() {
            let path = entry.path();
            let filename = name.to_string_lossy();
            let filename =
                if folds_case { filename.to_ascii_lowercase() } else { filename.into_owned() };
            ensure!(
                ![".olean", ".olean.private", ".olean.server", ".ilean", ".ir"]
                    .iter()
                    .any(|suffix| filename.ends_with(suffix)),
                "Compiled input outside owned .lake outputs: {}",
                path.display()
            );
            if path
                .extension()
                .and_then(|s| s.to_str())
                .is_some_and(|s| s == "lean" || (folds_case && s.eq_ignore_ascii_case("lean")))
            {
                let relative = path.strip_prefix(source_root)?.with_extension("");
                let name = relative
                    .iter()
                    .map(|s| s.to_str().context("Non-UTF8 Lean module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                // The generator's module grammar is ASCII; retaining other
                // ASCII direct-check filenames is safe, but a Unicode alias
                // would require the filesystem's Unicode normalization rules.
                ensure!(name.is_ascii(), "Unsupported non-ASCII local module path: {name}");
                ensure!(!sdk.modules.contains(&name), "Local/SDK exact module collision: {name}");
                let provider = if folds_case { name.to_ascii_lowercase() } else { name.clone() };
                ensure!(
                    !folds_case || !sdk.folded_modules.contains(&provider),
                    "Local/SDK case-equivalent module collision: {name}"
                );
                ensure!(local_modules.insert(provider), "Duplicate local module provider: {name}");
            }
        }
    }
    Ok(())
}

/// All supported generated module names are ASCII. Probe an existing ownership
/// or manifest file on the relevant filesystem, without creating scratch files
/// or assuming that every macOS volume folds case. Output provider aliases are
/// decided by the private output filesystem, even when sources live elsewhere.
pub(crate) fn filesystem_folds_ascii_case(reference: &Path) -> Result<bool> {
    let leaf = reference
        .file_name()
        .context("Case probe has no filename")?
        .to_str()
        .context("Case probe filename is not UTF-8")?;
    let alternate =
        leaf.chars()
            .map(|c| {
                if c.is_ascii_lowercase() { c.to_ascii_uppercase() } else { c.to_ascii_lowercase() }
            })
            .collect::<String>();
    ensure!(alternate != leaf, "Case probe needs an ASCII letter");
    let original = fs::metadata(reference)?;
    let alternate = match fs::metadata(reference.with_file_name(alternate)) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error.into()),
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        Ok(original.dev() == alternate.dev() && original.ino() == alternate.ino())
    }
    #[cfg(not(unix))]
    {
        bail!("Unsupported filesystem module equivalence probe")
    }
}

fn valid_component(name: &str) -> bool {
    let mut chars = name.bytes();
    chars.next().is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, b'_' | b'\''))
}

fn valid_module(name: &str) -> bool {
    !name.is_empty() && name.split('.').all(valid_component)
}

fn valid_build_target(target: &str) -> bool {
    let target = target.strip_prefix('+').unwrap_or(target);
    let target = target.strip_suffix(":olean").unwrap_or(target);
    valid_module(target)
}

fn saved_inputs(root: &Path) -> Result<BTreeSet<PathBuf>> {
    Ok(saved_inputs_with_change_detection(root, false)?.files)
}

#[derive(PartialEq, Eq)]
struct SavedInputPaths {
    files: BTreeSet<PathBuf>,
    directories: BTreeSet<PathBuf>,
}

fn saved_inputs_with_change_detection(
    root: &Path,
    detect_changes: bool,
) -> Result<SavedInputPaths> {
    fn collect(
        path: &Path,
        root: &Path,
        folds_case: bool,
        detect_changes: bool,
        inputs: &mut SavedInputPaths,
    ) -> Result<()> {
        inputs.directories.insert(path.to_path_buf());
        for entry in saved_input_io(fs::read_dir(path), detect_changes)? {
            let entry = saved_input_io(entry, detect_changes)?;
            let name = entry.file_name();
            if reserved_private_name(&name, folds_case) {
                continue;
            }
            let kind = saved_input_io(entry.file_type(), detect_changes)?;
            ensure!(
                !kind.is_symlink(),
                "Saved source tree contains a symlink: {}",
                entry.path().display()
            );
            ensure!(
                kind.is_dir() || kind.is_file(),
                "Saved source tree contains a special file: {}",
                entry.path().display()
            );
            if kind.is_dir() {
                collect(&entry.path(), root, folds_case, detect_changes, inputs)?;
            } else if kind.is_file()
                && (entry
                    .path()
                    .extension()
                    .and_then(|s| s.to_str())
                    .is_some_and(|s| s == "lean" || (folds_case && s.eq_ignore_ascii_case("lean")))
                    || (path == root
                        && [
                            "lakefile.toml",
                            "lake-manifest.json",
                            "lean-toolchain",
                            LAKE_CONFIGURATION,
                        ]
                        .iter()
                        .any(|s| name == *s)))
            {
                inputs.files.insert(entry.path());
            }
        }
        Ok(())
    }
    let mut inputs = SavedInputPaths { files: BTreeSet::new(), directories: BTreeSet::new() };
    let folds_case = filesystem_folds_ascii_case(&root.join(BINDING))?;
    collect(root, root, folds_case, detect_changes, &mut inputs)?;
    Ok(inputs)
}

fn physical_directory_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    ensure!(metadata.is_dir(), "Saved source tree path is not a directory");
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let mut identity = metadata.dev().to_le_bytes().to_vec();
        identity.extend_from_slice(&metadata.ino().to_le_bytes());
        Ok(identity)
    }
    #[cfg(not(unix))]
    {
        bail!("Unsupported saved-input directory identity")
    }
}

fn directory_modification_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    let mut identity = physical_directory_identity(metadata)?;
    let modified = metadata.modified()?.duration_since(std::time::UNIX_EPOCH)?;
    identity.extend_from_slice(&modified.as_secs().to_le_bytes());
    identity.extend_from_slice(&modified.subsec_nanos().to_le_bytes());
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        identity.extend_from_slice(&metadata.ctime().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime_nsec().to_le_bytes());
    }
    Ok(identity)
}

fn modification_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    ensure!(metadata.is_file(), "Saved Lean input is not a regular file");
    let modified = metadata.modified()?.duration_since(std::time::UNIX_EPOCH)?;
    let mut identity = Vec::new();
    identity.extend_from_slice(&metadata.len().to_le_bytes());
    identity.extend_from_slice(&modified.as_secs().to_le_bytes());
    identity.extend_from_slice(&modified.subsec_nanos().to_le_bytes());
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        identity.extend_from_slice(&metadata.dev().to_le_bytes());
        identity.extend_from_slice(&metadata.ino().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime_nsec().to_le_bytes());
    }
    Ok(identity)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    struct Fixture {
        _temp: tempfile::TempDir,
        base: PathBuf,
        sdk: LeanSdk,
    }

    impl Fixture {
        fn new(modules: &[&str]) -> Self {
            let temp = tempfile::tempdir().unwrap();
            let base = fs::canonicalize(temp.path()).unwrap();
            let installation = base.join("toolchain");
            let root = installation.join("lean-sdk");
            for path in ["bin", "lib/lean", "src/lean/lake"] {
                fs::create_dir_all(root.join(path)).unwrap();
            }
            fs::create_dir(installation.join("lean")).unwrap();
            for tool in ["lean", "lake"] {
                fs::write(root.join("bin").join(tool), "#!/bin/sh\nexit 0\n").unwrap();
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt as _;
                    fs::set_permissions(
                        root.join("bin").join(tool),
                        fs::Permissions::from_mode(0o755),
                    )
                    .unwrap();
                }
            }
            let manifest = serde_json::to_vec(&json!({"schema": 1, "modules": modules})).unwrap();
            fs::write(root.join("modules.json"), &manifest).unwrap();
            let descriptor = json!({
                "schema": 1,
                "id": "a".repeat(64),
                "lean_toolchain": "leanprover/lean4:v4.30.0-rc2",
                "compiler_hash": "b".repeat(40),
                "platform": host_platform().unwrap(),
                "runtime": "../lean",
                "source_roots": ["src/lean", "src/lean/lake"],
                "import_roots": ["lib/lean"],
                "loader_roots": ["lib", "lib/lean"],
                "plugins": [],
                "modules": "modules.json",
                "modules_sha256": sha256(&manifest),
            });
            fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
            let sdk = LeanSdk::load(&root).unwrap();
            Self { _temp: temp, base, sdk }
        }

        fn workspace(&self) -> Workspace<'_> {
            let workspace =
                Workspace::create(&self.sdk, &self.base.join("workspace"), &[".", "src"]).unwrap();
            configure_test_workspace(&workspace);
            workspace
        }

        fn mapped_workspace_with_sentinels(&self) -> (Workspace<'_>, Vec<(PathBuf, Vec<u8>)>) {
            let workspace = Workspace::create(
                &self.sdk,
                &self.base.join("mapped-workspace"),
                &["anneal", "generated", "user"],
            )
            .unwrap();
            configure_test_workspace(&workspace);
            let mut sentinels = Vec::new();
            for (relative, bytes) in [
                ("anneal/Existing.lean", b"def existing := 10\n".as_slice()),
                (".lake/build/lib/lean/Existing.olean", b"owned compiled output".as_slice()),
                (".runtime/cache/entry", b"owned cache".as_slice()),
            ] {
                let path = workspace.root().join(relative);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(&path, bytes).unwrap();
                sentinels.push((path, bytes.to_vec()));
            }
            for relative in [BINDING, OUTPUT_OWNER] {
                let path = workspace.root().join(relative);
                sentinels.push((path.clone(), fs::read(path).unwrap()));
            }
            workspace.admit().unwrap();
            (workspace, sentinels)
        }
    }

    fn configure_test_workspace(workspace: &Workspace<'_>) {
        let names = workspace
            .binding
            .source_roots
            .iter()
            .enumerate()
            .map(|(i, _)| format!("Source{i}"))
            .collect::<Vec<_>>();
        let libraries = workspace
            .binding
            .source_roots
            .iter()
            .zip(&names)
            .map(|(root, name)| LakeLibrary {
                name,
                source_root: root.to_str().unwrap(),
                modules: &[],
            })
            .collect::<Vec<_>>();
        Workspace::write_lakefile(workspace.sdk(), workspace.root(), &libraries).unwrap();
    }

    #[test]
    fn workspace_names_cannot_alias_sibling_lock_files() {
        let f = Fixture::new(&["Shared.A"]);
        for suffix in [".lock", ".server-lease"] {
            let root = f.base.join(format!("reserved{suffix}"));
            let error = Workspace::create(&f.sdk, &root, &["src"]).err().unwrap();
            assert!(error.to_string().contains("reserved lock suffix"));
            assert!(!root.exists());
            let stage = f.base.join(format!("stage{suffix}"));
            assert!(
                Workspace::stage(&f.sdk, &stage, &f.base.join("valid-final"), None, &["src"])
                    .is_err()
            );
            assert!(!stage.exists());
        }
        let folds_case = filesystem_folds_ascii_case(&f.sdk.root().join("modules.json")).unwrap();
        for suffix in [".LOCK", ".SERVER-LEASE"] {
            let root = f.base.join(format!("case-alias{suffix}"));
            let result = Workspace::create(&f.sdk, &root, &["src"]);
            assert_eq!(result.is_err(), folds_case);
            assert_eq!(root.exists(), !folds_case);
        }

        // A preexisting or manually relabeled binding cannot bypass the new
        // creation rule and occupy a sibling's reserved lock pathname.
        let workspace = f.workspace();
        let legacy = f.base.join("legacy.lock");
        fs::rename(workspace.root(), &legacy).unwrap();
        let mut binding = workspace.binding.clone();
        binding.workspace = legacy.clone();
        for record in [BINDING, OUTPUT_OWNER] {
            fs::write(legacy.join(record), serde_json::to_vec(&binding).unwrap()).unwrap();
        }
        let error = Workspace::open(&f.sdk, &legacy).err().unwrap();
        assert!(error.to_string().contains("reserved lock suffix"));
    }

    #[cfg(unix)]
    #[test]
    fn search_list_inputs_are_rejected_before_sdk_or_workspace_binding() {
        let f = Fixture::new(&["Shared.A"]);
        let root = f.base.join("workspace:separator");
        let error = Workspace::create(&f.sdk, &root, &["src"]).err().unwrap();
        assert_eq!(error.to_string(), "LEAN_PATH cannot represent its input paths");
        assert!(!root.exists());
        let root = f.base.join("local-source-separator");
        let error = Workspace::create(&f.sdk, &root, &["src:separator"]).err().unwrap();
        assert_eq!(error.to_string(), "LEAN_SRC_PATH cannot represent its input paths");
        assert!(!root.exists());

        let workspace = f.workspace();
        let mut binding = workspace.binding.clone();
        binding.source_roots = vec!["src:separator".into()];
        for record in [BINDING, OUTPUT_OWNER] {
            fs::write(workspace.root().join(record), serde_json::to_vec(&binding).unwrap())
                .unwrap();
        }
        let legacy = Workspace::open(&f.sdk, workspace.root()).err().unwrap();
        assert_eq!(legacy.to_string(), "LEAN_SRC_PATH cannot represent its input paths");

        let descriptor_path = f.sdk.root().join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        let loader = f.sdk.installation.join("loader:separator");
        fs::create_dir(&loader).unwrap();
        descriptor["loader_roots"] = json!(["../loader:separator"]);
        fs::write(&descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        let loader_error = LeanSdk::load(f.sdk.root()).unwrap_err();
        assert_eq!(
            loader_error.to_string(),
            "Native loader search list cannot represent its input paths"
        );
        descriptor["loader_roots"] = json!(["lib"]);
        fs::write(&descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        let moved = f.sdk.root().with_file_name("lean-sdk:separator");
        fs::rename(f.sdk.root(), &moved).unwrap();
        let sdk_error = LeanSdk::load(&moved).unwrap_err();
        assert_eq!(sdk_error.to_string(), "SDK PATH cannot represent its input paths");
    }

    #[cfg(unix)]
    #[test]
    fn special_source_files_are_rejected_before_command_creation() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let fifo = workspace.root().join("Proof.lean");
        assert!(Command::new("mkfifo").arg(&fifo).status().unwrap().success());
        let admission = workspace.admit().unwrap_err();
        assert!(admission.to_string().contains("Local source contains a special file"));
        assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());
        assert!(workspace.lean_command(LeanOperation::Check { file: &fifo, json: false }).is_err());
        let stamp = stamp_saved_inputs(workspace.root(), |_| {}).unwrap_err();
        assert!(stamp.to_string().contains("Saved source tree contains a special file"));
        assert!(stamp.downcast_ref::<SourceStampChanged>().is_none());
        // No process opens or supplies source bytes to this FIFO.
        fs::remove_file(fifo).unwrap();
        workspace.admit().unwrap();
    }

    #[test]
    fn direct_source_checks_use_the_filesystems_lean_suffix_equivalence() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let uppercase = workspace.root().join("Proof.LEAN");
        fs::write(&uppercase, "example : True := by trivial\n").unwrap();
        let folds_case = workspace.folds_ascii_case().unwrap();
        workspace.admit().unwrap();
        let check = workspace.lean_command(LeanOperation::Check { file: &uppercase, json: true });
        let setup = workspace.lake_command(LakeOperation::SetupFile(&uppercase));
        assert_eq!(check.is_ok(), folds_case);
        assert_eq!(setup.is_ok(), folds_case);
        if folds_case {
            assert!(check.unwrap().get_args().any(|arg| arg == "Proof.LEAN"));
            assert!(setup.unwrap().get_args().any(|arg| arg == uppercase.as_os_str()));
        }
    }

    #[test]
    fn rejected_stage_sdk_collision_preserves_existing_sources_and_outputs() {
        let f = Fixture::new(&["Config"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let stage = f.base.join("colliding-stage");
        Workspace::stage(
            &f.sdk,
            &stage,
            workspace.root(),
            Some(&workspace),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        fs::create_dir(stage.join("generated")).unwrap();
        fs::write(stage.join("generated/Config.lean"), "def value := 20\n").unwrap();
        let error = Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap_err();
        assert!(error.to_string().contains("Local/SDK exact module collision: Config"));
        for (path, expected) in sentinels {
            assert_eq!(fs::read(path).unwrap(), expected);
        }
        Workspace::from_root(workspace.root()).unwrap().admit().unwrap();
    }

    #[test]
    fn rejected_stage_duplicate_local_provider_preserves_existing_sources_and_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let stage = f.base.join("duplicate-stage");
        Workspace::stage(
            &f.sdk,
            &stage,
            workspace.root(),
            Some(&workspace),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        for root in ["anneal", "user"] {
            fs::create_dir(stage.join(root)).unwrap();
            fs::write(stage.join(root).join("Config.lean"), "def value := 20\n").unwrap();
        }
        let error = Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap_err();
        assert!(error.to_string().contains("Duplicate local module provider: Config"));
        for (path, expected) in sentinels {
            assert_eq!(fs::read(path).unwrap(), expected);
        }
        Workspace::from_root(workspace.root()).unwrap().admit().unwrap();
    }

    #[test]
    fn direct_check_and_setup_reject_nested_reserved_source_directories() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = Workspace::create(&f.sdk, &f.base.join("workspace"), &["user"]).unwrap();
        configure_test_workspace(&workspace);
        fs::create_dir(workspace.root().join("user")).unwrap();
        let regular = workspace.root().join("user/Proof.lean");
        fs::write(&regular, "example : True := by trivial\n").unwrap();
        for reserved in [".lake", ".runtime", ".git"] {
            let path = workspace.root().join("user/nested").join(reserved).join("Proof.lean");
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, "example : True := by trivial\n").unwrap();
            for file in [path.as_path(), path.strip_prefix(workspace.root()).unwrap()] {
                assert!(
                    workspace.lean_command(LeanOperation::Check { file, json: true }).is_err(),
                    "direct Lean accepted reserved input {}",
                    file.display()
                );
                assert!(
                    workspace.lake_command(LakeOperation::SetupFile(file)).is_err(),
                    "Lake setup accepted reserved input {}",
                    file.display()
                );
            }
            assert!(workspace.admit().is_err());
            fs::remove_dir_all(path.parent().unwrap()).unwrap();
        }
        workspace.admit().unwrap();
        workspace.lean_command(LeanOperation::Check { file: &regular, json: true }).unwrap();
        workspace.lake_command(LakeOperation::SetupFile(&regular)).unwrap();
    }

    #[test]
    fn independent_workspace_handles_serialize_writers_and_allow_shared_readers() {
        let f = Fixture::new(&["Shared.A"]);
        let first = f.workspace();
        let second = Workspace::from_root(first.root()).unwrap();
        let writer = first.writer_lock().unwrap();
        assert!(second.try_writer_lock().unwrap().is_none());
        assert!(second.try_shared_lock().unwrap().is_none());
        drop(writer);

        let first_reader = first.try_shared_lock().unwrap().unwrap();
        let second_reader = second.try_shared_lock().unwrap().unwrap();
        assert!(first.try_writer_lock().unwrap().is_none());
        drop(first_reader);
        assert!(first.try_writer_lock().unwrap().is_none());
        drop(second_reader);
        let second_writer = second.try_writer_lock().unwrap().unwrap();
        assert!(first.try_writer_lock().unwrap().is_none());
        assert!(first.try_shared_lock().unwrap().is_none());
        drop(second_writer);
        assert!(first.try_writer_lock().unwrap().is_some());
    }

    #[test]
    fn held_writer_lock_survives_workspace_replacement_at_the_bound_path() {
        let f = Fixture::new(&["Shared.A"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let writer = workspace.writer_lock().unwrap();
        let stage = f.base.join("replacement-stage");
        Workspace::stage(
            &f.sdk,
            &stage,
            workspace.root(),
            Some(&workspace),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        fs::create_dir(stage.join("anneal")).unwrap();
        fs::copy(workspace.root().join("anneal/Existing.lean"), stage.join("anneal/Existing.lean"))
            .unwrap();
        Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap();
        workspace.admit().unwrap();
        let retired = f.base.join("retired-workspace");
        fs::rename(workspace.root(), &retired).unwrap();
        for private in [".lake", PRIVATE_RUNTIME] {
            fs::rename(retired.join(private), stage.join(private)).unwrap();
        }
        fs::rename(&stage, workspace.root()).unwrap();

        let replacement = Workspace::from_root(workspace.root()).unwrap();
        assert!(replacement.try_writer_lock().unwrap().is_none());
        assert!(replacement.try_shared_lock().unwrap().is_none());
        for (path, expected) in sentinels {
            assert_eq!(fs::read(path).unwrap(), expected);
        }
        drop(writer);
        assert!(replacement.try_writer_lock().unwrap().is_some());
    }

    #[test]
    fn identical_sdk_metadata_in_another_archive_cannot_retarget_a_bound_workspace() {
        let f = Fixture::new(&["Shared.A"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let second_installation = f.base.join("second-archive");
        let second_root = second_installation.join("lean-sdk");
        for directory in ["bin", "lib/lean", "src/lean/lake"] {
            fs::create_dir_all(second_root.join(directory)).unwrap();
        }
        fs::create_dir(second_installation.join("lean")).unwrap();
        for relative in ["sdk.json", "modules.json", "bin/lean", "bin/lake"] {
            fs::copy(f.sdk.root().join(relative), second_root.join(relative)).unwrap();
        }
        let second_sdk = LeanSdk::load(&second_root).unwrap();
        assert_eq!(second_sdk.id(), f.sdk.id());
        assert_ne!(second_sdk.root(), f.sdk.root());
        for relative in ["sdk.json", "modules.json"] {
            assert_eq!(
                fs::read(second_sdk.root().join(relative)).unwrap(),
                fs::read(f.sdk.root().join(relative)).unwrap()
            );
        }
        assert!(Workspace::open(&second_sdk, workspace.root()).is_err());
        let original = Workspace::from_root(workspace.root()).unwrap();
        assert_eq!(original.sdk().root(), f.sdk.root());
        assert_eq!(
            original.lean_command(LeanOperation::Version).unwrap().get_program(),
            f.sdk.root().join("bin/lean")
        );
        for (path, expected) in sentinels {
            assert_eq!(fs::read(path).unwrap(), expected);
        }
        Workspace::create(
            &second_sdk,
            &f.base.join("second-workspace"),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        Workspace::from_root(workspace.root()).unwrap().admit().unwrap();
    }

    #[test]
    fn one_editor_session_does_not_block_batch_writers_or_another_workspace() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let editor = workspace.server_lock().unwrap();
        let reopened = Workspace::from_root(workspace.root()).unwrap();
        assert!(reopened.server_lock().is_err());
        assert!(workspace.try_writer_lock().unwrap().is_some());
        let other = Workspace::create(&f.sdk, &f.base.join("other"), &["src"]).unwrap();
        assert!(other.server_lock().is_ok());
        drop(editor);
        assert!(reopened.server_lock().is_ok());
    }

    #[test]
    fn editor_lease_is_disjoint_from_a_server_named_siblings_writer_lock() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let sibling =
            Workspace::create(&f.sdk, &f.base.join("workspace.server"), &["src"]).unwrap();
        let editor = workspace.server_lock().unwrap();
        let writer = sibling.try_writer_lock().unwrap().expect("unrelated sibling writer blocked");
        assert!(sibling.server_lock().is_ok());
        assert!(workspace.try_writer_lock().unwrap().is_some());
        drop(editor);
        assert!(workspace.server_lock().is_ok(), "sibling writer blocked editor restart");
        drop(writer);
    }

    #[test]
    fn nested_reserved_directories_cannot_hide_bound_sources_from_freshness() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::create_dir_all(workspace.root().join("src/.runtime")).unwrap();
        fs::write(workspace.root().join("src/.runtime/Hidden.lean"), "def hidden := 1").unwrap();
        assert!(workspace.admit().is_err());
    }

    #[test]
    fn rejects_unowned_and_copied_outputs_before_command_creation() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::create_dir_all(workspace.root().join(".lake/build/lib/lean")).unwrap();
        fs::write(workspace.root().join(".lake/build/lib/lean/Local.olean"), "owned").unwrap();
        workspace.admit().unwrap();
        let mut foreign = workspace.binding.clone();
        foreign.owner.push_str("-foreign");
        fs::write(workspace.root().join(OUTPUT_OWNER), serde_json::to_vec(&foreign).unwrap())
            .unwrap();
        assert!(workspace.lean_command(LeanOperation::Server).is_err());
        assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());

        let unowned = f.base.join("unowned");
        fs::create_dir_all(unowned.join(".lake/build")).unwrap();
        fs::write(unowned.join(".lake/build/Foreign.olean"), "foreign").unwrap();
        assert!(Workspace::create(&f.sdk, &unowned, &["."]).is_err());
        assert_eq!(fs::read(unowned.join(".lake/build/Foreign.olean")).unwrap(), b"foreign");
    }

    #[test]
    fn exact_module_collisions_reject_but_shared_namespaces_work() {
        let f = Fixture::new(&["Shared.A", "Other.B"]);
        let workspace = f.workspace();
        fs::create_dir_all(workspace.root().join("src/Shared")).unwrap();
        fs::write(workspace.root().join("src/Shared/B.lean"), "def b := 1").unwrap();
        workspace.admit().unwrap();
        fs::write(workspace.root().join("src/Shared/A.lean"), "def a := 1").unwrap();
        assert!(workspace.lean_command(LeanOperation::Server).is_err());
        assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());
    }

    #[test]
    fn rejects_descriptor_mutation_and_forged_same_label_rebinding() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let path = f.sdk.root().join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        descriptor["compiler_hash"] = json!("c".repeat(40));
        fs::write(&path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(workspace.lean_command(LeanOperation::Server).is_err());
        let relabeled_sdk = LeanSdk::load(f.sdk.root()).unwrap();
        assert_eq!(relabeled_sdk.id(), f.sdk.id());
        assert!(Workspace::open(&relabeled_sdk, workspace.root()).is_err());
    }

    #[test]
    fn regeneration_preserves_only_the_same_workspace_owner() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let stage = f.base.join("stage");
        Workspace::stage(&f.sdk, &stage, workspace.root(), Some(&workspace), &[".", "src"])
            .unwrap();
        let binding: Binding = read_json(&stage.join(BINDING)).unwrap();
        assert_eq!(binding, workspace.binding);
        assert!(!stage.join(".lake").exists());
        assert!(!stage.join(PRIVATE_RUNTIME).exists());
        assert!(
            Workspace::stage(
                &f.sdk,
                &f.base.join("moved-stage"),
                &f.base.join("moved"),
                Some(&workspace),
                &[".", "src"]
            )
            .is_err()
        );
        assert!(
            Workspace::stage(
                &f.sdk,
                &f.base.join("remapped-stage"),
                workspace.root(),
                Some(&workspace),
                &["."]
            )
            .is_err()
        );
    }

    #[test]
    fn saved_input_stamps_detect_source_and_config_changes_but_ignore_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::create_dir(workspace.root().join("src")).unwrap();
        let source = workspace.root().join("src/Local.lean");
        fs::write(&source, "def value := 10\n").unwrap();
        let initial = workspace.source_stamp().unwrap();
        fs::create_dir_all(workspace.root().join(".lake/build/lib/lean")).unwrap();
        fs::write(workspace.root().join(".lake/build/lib/lean/Local.olean"), "private build")
            .unwrap();
        fs::write(workspace.root().join(".runtime/cache/cache-entry"), "private cache").unwrap();
        assert_eq!(initial, workspace.source_stamp().unwrap());
        fs::write(&source, "def value := 20\n").unwrap();
        assert_ne!(initial, workspace.source_stamp().unwrap());
        let edited = workspace.source_stamp().unwrap();
        fs::write(workspace.root().join("lean-toolchain"), "changed\n").unwrap();
        assert_ne!(edited, workspace.source_stamp().unwrap());
    }

    #[test]
    fn source_directory_swap_and_restore_changes_live_and_in_progress_stamps() {
        for whole_root in [false, true] {
            let f = Fixture::new(&["Shared.A"]);
            let workspace = f.workspace();
            let source = workspace.root().join("src");
            fs::create_dir(&source).unwrap();
            fs::write(source.join("Proof.lean"), "def value := 10\n").unwrap();
            let later = workspace.root().join("z.lean");
            fs::write(&later, "def other := 10\n").unwrap();
            let before = workspace.source_stamp().unwrap();
            let target = if whole_root { workspace.root() } else { source.as_path() };
            let retired = f.base.join("retired-source-directory");
            let error = stamp_saved_inputs(workspace.root(), |recorded| {
                if recorded == later {
                    fs::rename(target, &retired).unwrap();
                    fs::create_dir(target).unwrap();
                    let transient = target.join("Transient.lean");
                    fs::write(&transient, "def temporary := 20\n").unwrap();
                    fs::remove_file(transient).unwrap();
                    fs::remove_dir(target).unwrap();
                    fs::rename(&retired, target).unwrap();
                }
            })
            .unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_some());
            assert!(error.to_string().contains("source directory changed"));
            assert_ne!(before, workspace.source_stamp().unwrap());
            assert_eq!(fs::read_to_string(source.join("Proof.lean")).unwrap(), "def value := 10\n");
        }
    }

    #[test]
    fn source_stamp_rechecks_earlier_files_after_reading_later_inputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let earlier = workspace.root().join("A.lean");
        let later = workspace.root().join("B.lean");
        fs::write(&earlier, "def value := 10\n").unwrap();
        fs::write(&later, "def other := 10\n").unwrap();
        let original = workspace.source_stamp().unwrap();
        let error = stamp_saved_inputs(workspace.root(), |recorded| {
            if recorded == later {
                fs::write(&earlier, "def value := 20\n").unwrap();
            }
        })
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_some());
        assert!(error.to_string().contains("changed while recording its state"));
        assert!(error.to_string().contains("A.lean"));
        assert_ne!(original, workspace.source_stamp().unwrap());
    }

    #[test]
    fn source_stamp_classifies_deletions_before_read_and_after_later_inputs() {
        for delete_before_read in [true, false] {
            let f = Fixture::new(&["Shared.A"]);
            let workspace = f.workspace();
            let earlier = workspace.root().join("A.lean");
            let later = workspace.root().join("B.lean");
            fs::write(&earlier, "def value := 10\n").unwrap();
            fs::write(&later, "def other := 10\n").unwrap();
            let error = stamp_saved_inputs(workspace.root(), |recorded| {
                if delete_before_read && recorded == earlier {
                    fs::remove_file(&later).unwrap();
                } else if !delete_before_read && recorded == later {
                    fs::remove_file(&earlier).unwrap();
                }
            })
            .unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_some());
            if delete_before_read {
                assert!(error.to_string().contains("Saved input disappeared:"));
                assert!(error.to_string().contains("B.lean"));
            } else {
                assert_eq!(
                    error.to_string(),
                    "Saved Lean input set changed while recording its state"
                );
            }
        }
    }

    #[test]
    fn source_stamp_keeps_binding_ownership_and_sdk_admission_failures_fatal() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        for record in [BINDING, OUTPUT_OWNER] {
            let path = workspace.root().join(record);
            let original = fs::read(&path).unwrap();
            let mut binding: Binding = serde_json::from_slice(&original).unwrap();
            binding.owner.push_str("-foreign");
            fs::write(&path, serde_json::to_vec(&binding).unwrap()).unwrap();
            let error = workspace.source_stamp().unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            fs::remove_file(&path).unwrap();
            let missing = workspace.source_stamp().unwrap_err();
            assert!(missing.downcast_ref::<SourceStampChanged>().is_none());
            fs::write(&path, original).unwrap();
        }
        let descriptor = f.sdk.root().join("sdk.json");
        let original = fs::read(&descriptor).unwrap();
        fs::write(&descriptor, b"{}").unwrap();
        let error = workspace.source_stamp().unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        assert_eq!(error.to_string(), "SDK descriptor changed after admission");
        fs::write(descriptor, original).unwrap();
        workspace.source_stamp().unwrap();
    }

    #[test]
    fn source_stamp_keeps_nonregular_inputs_and_permanent_io_errors_fatal() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let earlier = workspace.root().join("A.lean");
        let later = workspace.root().join("B.lean");
        fs::write(&earlier, "def value := 10\n").unwrap();
        fs::write(&later, "def other := 10\n").unwrap();
        let error = stamp_saved_inputs(workspace.root(), |recorded| {
            if recorded == earlier {
                fs::remove_file(&later).unwrap();
                fs::create_dir(&later).unwrap();
            }
        })
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());

        // Permission and permanent device failures must not become a retry
        // signal merely because they arose during local snapshot recording.
        for kind in [std::io::ErrorKind::PermissionDenied, std::io::ErrorKind::Other] {
            let error = saved_input_io::<()>(Err(std::io::Error::new(kind, "permanent I/O")), true)
                .unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            assert_eq!(error.downcast_ref::<std::io::Error>().unwrap().kind(), kind);
        }
        // Missing input outside the stamp observation is still an admission
        // failure, rather than a blanket classification of all NotFound I/O.
        let error = saved_input_io::<()>(
            Err(std::io::Error::new(std::io::ErrorKind::NotFound, "missing admission input")),
            false,
        )
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
    }

    #[cfg(unix)]
    #[test]
    fn source_stamp_keeps_escaping_links_fatal_even_during_observation() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let earlier = workspace.root().join("A.lean");
        let later = workspace.root().join("B.lean");
        let outside = f.base.join("Outside.lean");
        fs::write(&earlier, "def value := 10\n").unwrap();
        fs::write(&later, "def other := 10\n").unwrap();
        fs::write(&outside, "def foreign := 10\n").unwrap();
        let error = stamp_saved_inputs(workspace.root(), |recorded| {
            if recorded == later {
                fs::remove_file(&earlier).unwrap();
                symlink(&outside, &earlier).unwrap();
            }
        })
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        assert!(error.to_string().contains("symlink"));
        let admission = workspace.source_stamp().unwrap_err();
        assert!(admission.downcast_ref::<SourceStampChanged>().is_none());
        assert!(admission.to_string().contains("symlink"));
    }

    #[test]
    fn lakefile_is_stamped_and_edit_restore_during_traversal_is_obsolete() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let lakefile = workspace.root().join("lakefile.lean");
        let later = workspace.root().join("z.lean");
        fs::write(&later, "def value := 10\n").unwrap();
        assert!(saved_inputs(workspace.root()).unwrap().contains(&lakefile));
        let bytes = fs::read(&lakefile).unwrap();
        let modified = fs::metadata(&lakefile).unwrap().modified().unwrap();
        let before = workspace.source_stamp().unwrap();
        let retired = workspace.root().join("retired-lakefile");
        let error = stamp_saved_inputs(workspace.root(), |recorded| {
            if recorded == later {
                // Restore both bytes and mtime, as an editor's atomic file
                // replacement can do. The replacement identity still changed.
                fs::rename(&lakefile, &retired).unwrap();
                fs::write(&lakefile, "import Lake\n-- transient different configuration\n")
                    .unwrap();
                fs::write(&lakefile, &bytes).unwrap();
                fs::File::options()
                    .write(true)
                    .open(&lakefile)
                    .unwrap()
                    .set_times(fs::FileTimes::new().set_modified(modified))
                    .unwrap();
                fs::remove_file(&retired).unwrap();
            }
        })
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_some());
        assert!(error.to_string().contains("lakefile.lean"));
        assert!(error.to_string().contains("changed while recording its state"));
        assert_eq!(fs::read(&lakefile).unwrap(), bytes);
        assert_ne!(workspace.source_stamp().unwrap(), before);
    }

    #[test]
    fn private_source_root_aliases_follow_the_workspace_filesystem() {
        let f = Fixture::new(&["Shared.A"]);
        let folds_case = filesystem_folds_ascii_case(&f.sdk.root().join("modules.json")).unwrap();
        for (index, alias) in
            [".RUNTIME", ".LAKE", ".GIT", "user/.RuNtImE", "user/.LaKe", "user/.GiT"]
                .iter()
                .enumerate()
        {
            let root = f.base.join(format!("alias-{index}"));
            let result = Workspace::create(&f.sdk, &root, &[alias]);
            assert_eq!(result.is_err(), folds_case, "source root {alias}");
            if folds_case {
                assert!(!root.exists(), "reserved alias left a partial workspace");
            }
        }
    }

    #[test]
    fn private_aliases_cannot_hide_sources_in_existing_bindings_or_direct_checks() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("private-alias"), &["user"]).unwrap();
        configure_test_workspace(&workspace);
        let folds_case = filesystem_folds_ascii_case(&workspace.root().join(OUTPUT_OWNER)).unwrap();
        if !folds_case {
            return;
        }
        fs::write(workspace.root().join(".runtime/Proof.lean"), "example : True := by trivial\n")
            .unwrap();
        assert!(
            workspace
                .lean_command(LeanOperation::Check {
                    file: Path::new(".RUNTIME/Proof.lean"),
                    json: true
                })
                .is_err()
        );
        let mut forged = workspace.binding.clone();
        forged.source_roots = vec![PathBuf::from(".RUNTIME")];
        for file in [BINDING, OUTPUT_OWNER] {
            fs::write(workspace.root().join(file), serde_json::to_vec(&forged).unwrap()).unwrap();
        }
        let configuration = LakeConfiguration {
            libraries: vec![LibraryConfiguration {
                name: "Hidden".into(),
                source_root: ".RUNTIME".into(),
                modules: vec!["Proof".into()],
            }],
        };
        fs::write(
            workspace.root().join(LAKE_CONFIGURATION),
            serde_json::to_vec(&configuration).unwrap(),
        )
        .unwrap();
        fs::write(
            workspace.root().join("lakefile.lean"),
            render_lakefile(&f.sdk, &configuration).unwrap(),
        )
        .unwrap();
        let result = Workspace::from_root(workspace.root());
        assert!(result.err().unwrap().to_string().contains("filesystem aliases"));
        assert!(
            Workspace::write_lakefile(
                &f.sdk,
                workspace.root(),
                &[LakeLibrary {
                    name: "Hidden",
                    source_root: ".RUNTIME",
                    modules: &["Proof".into()]
                }]
            )
            .is_err()
        );
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_workspace_roots_fail_explicitly_before_binding() {
        use std::os::unix::ffi::OsStringExt as _;
        let f = Fixture::new(&["Shared.A"]);
        let workspace_root = f.base.join(std::ffi::OsString::from_vec(b"workspace-\xff".to_vec()));
        let error = Workspace::create(&f.sdk, &workspace_root, &["src"]).err().unwrap();
        assert_eq!(error.to_string(), "Lean workspace path must be UTF-8");
        assert!(!workspace_root.exists());
    }

    // Physical malformed UTF-8 filenames are supported on Linux; the tested
    // macOS filesystem rejects creating them before SDK admission is reached.
    #[cfg(target_os = "linux")]
    #[test]
    fn non_utf8_sdk_roots_fail_explicitly_before_binding() {
        use std::os::unix::ffi::OsStringExt as _;
        let f = Fixture::new(&["Shared.A"]);
        let installation = f.base.join(std::ffi::OsString::from_vec(b"toolchain-\xff".to_vec()));
        fs::rename(&f.sdk.installation, &installation).unwrap();
        let error = LeanSdk::load(&installation.join("lean-sdk")).unwrap_err();
        assert_eq!(error.to_string(), "Lean SDK root must be UTF-8");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sdk_admission_rejects_a_plugin_resolving_to_non_utf8_bytes() {
        use std::os::unix::{ffi::OsStringExt as _, fs::symlink};
        let f = Fixture::new(&["Shared.A"]);
        let plugin =
            f.sdk.installation.join(std::ffi::OsString::from_vec(b"plugin-\xff.so".to_vec()));
        fs::write(&plugin, "immutable fixture plugin").unwrap();
        symlink(&plugin, f.sdk.root().join("lib/plugin.so")).unwrap();
        let descriptor_path = f.sdk.root().join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        descriptor["plugins"] = json!([{"path": "lib/plugin.so", "name": "nativePlugin"}]);
        fs::write(descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        let error = LeanSdk::load(f.sdk.root()).unwrap_err();
        assert_eq!(error.to_string(), "Resolved SDK input path must be UTF-8");
    }

    #[test]
    fn relocated_source_stamp_observes_backup_without_retargeting_ownership() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::write(workspace.root().join("A.lean"), "def value := 10\n").unwrap();
        let original = workspace.source_snapshot().unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), original.stamp());
        let clone = f.base.join("cloned-backup");
        fs::create_dir(&clone).unwrap();
        fs::write(clone.join(BINDING), fs::read(workspace.root().join(BINDING)).unwrap()).unwrap();
        fs::copy(workspace.root().join("A.lean"), clone.join("A.lean")).unwrap();
        let cloned = workspace.source_stamp_at(&clone, &original).unwrap_err();
        assert_eq!(cloned.to_string(), "Saved-input backup has a different physical root");
        let backup = f.base.join("backup");
        fs::rename(workspace.root(), &backup).unwrap();
        assert_eq!(workspace.source_stamp_at(&backup, &original).unwrap(), original.stamp());
        assert!(Workspace::from_root(&backup).is_err());
        fs::write(backup.join("A.lean"), "def value := 20\n").unwrap();
        let changed = workspace.source_stamp_at(&backup, &original).unwrap_err();
        assert!(changed.downcast_ref::<SourceStampChanged>().is_some());
        let mut binding = workspace.binding.clone();
        binding.owner.push_str("-foreign");
        fs::write(backup.join(BINDING), serde_json::to_vec(&binding).unwrap()).unwrap();
        assert!(workspace.source_stamp_at(&backup, &original).is_err());
        assert!(workspace.source_stamp_at(f.sdk.root(), &original).is_err());
    }

    #[test]
    fn generated_lake_configuration_rejects_unbound_roots_and_executable_changes() {
        let f = Fixture::new(&["Config"]);
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("mapped"), &["anneal", "generated", "user"])
                .unwrap();
        configure_test_workspace(&workspace);
        let original = fs::read(workspace.root().join("lakefile.lean")).unwrap();
        fs::create_dir(workspace.root().join("other")).unwrap();
        fs::write(workspace.root().join("other/Config.lean"), "def value := 20\n").unwrap();
        let modified = String::from_utf8(original.clone())
            .unwrap()
            .replace("srcDir := \"user\"", "srcDir := \"other\"");
        fs::write(workspace.root().join("lakefile.lean"), modified).unwrap();
        assert!(
            workspace
                .lake_command(LakeOperation::Build(&[]))
                .unwrap_err()
                .to_string()
                .contains("Lakefile differs")
        );
        // Mutating both the script and its declarative spec cannot bless roots
        // excluded from the immutable workspace binding.
        let spec_path = workspace.root().join(LAKE_CONFIGURATION);
        let spec_bytes = fs::read(&spec_path).unwrap();
        let mut spec: serde_json::Value = serde_json::from_slice(&spec_bytes).unwrap();
        spec["libraries"][2]["source_root"] = json!("other");
        fs::write(&spec_path, serde_json::to_vec(&spec).unwrap()).unwrap();
        assert!(workspace.admit().unwrap_err().to_string().contains("source roots do not match"));
        fs::write(&spec_path, spec_bytes).unwrap();
        let mut executable = original.clone();
        executable.extend_from_slice(b"\nlean_lib Other where\n  srcDir := \"other\"\n");
        fs::write(workspace.root().join("lakefile.lean"), executable).unwrap();
        assert!(workspace.lake_command(LakeOperation::Serve).is_err());
        fs::write(workspace.root().join("lakefile.lean"), &original).unwrap();
        workspace.admit().unwrap();
        fs::write(workspace.root().join("lakefile.toml"), "name = 'other'\n").unwrap();
        assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());
    }

    #[test]
    fn generated_configuration_uses_exact_globs_and_bound_plugin_inputs() {
        let mut f = Fixture::new(&["Shared.A"]);
        f.sdk.plugins.push(Plugin {
            path: f.sdk.root().join("lib/native plugin.so"),
            name: "nativePlugin".into(),
        });
        fs::write(&f.sdk.plugins[0].path, "immutable fixture native plugin").unwrap();
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("generated"), &["generated", "user"]).unwrap();
        let modules = ["Shared.B".into(), "Proof".into()];
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[
                LakeLibrary { name: "Generated", source_root: "generated", modules: &modules },
                LakeLibrary { name: "User", source_root: "user", modules: &[] },
            ],
        )
        .unwrap();
        let lakefile = fs::read_to_string(workspace.root().join("lakefile.lean")).unwrap();
        assert!(lakefile.contains("globs := #[.one `Shared.B, .one `Proof]"));
        assert!(lakefile.contains("roots := #[]"));
        assert!(lakefile.contains("target annealPlugin0 : Dynlib := do"));
        assert!(lakefile.contains("inputFile artifact false"));
        assert!(lakefile.contains("name := \"nativePlugin\", plugin := true"));
        workspace.lake_command(LakeOperation::Build(&["Generated".into()])).unwrap();
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let next_modules = ["OtherProof".into()];
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[
                LakeLibrary { name: "Generated", source_root: "generated", modules: &next_modules },
                LakeLibrary { name: "User", source_root: "user", modules: &[] },
            ],
        )
        .unwrap();
        workspace.admit().unwrap();
        assert_eq!(fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap(), owner);
    }

    #[test]
    fn library_keywords_are_escaped_with_exact_stock_configuration_compatibility() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let configuration: LakeConfiguration =
            serde_json::from_slice(&fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap())
                .unwrap();
        let legacy = render_lakefile_with_library_escape(&f.sdk, &configuration, false).unwrap();
        assert!(legacy.contains("lean_lib Source0 where"));
        fs::write(workspace.root().join("lakefile.lean"), legacy).unwrap();
        workspace.admit().unwrap();

        // Backtick module Name literals already use Lean's raw-name parser;
        // keyword components retain their names and exact-glob semantics.
        let modules = ["where.def".into(), "Proof'.by".into()];
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[
                LakeLibrary { name: "where", source_root: ".", modules: &modules },
                LakeLibrary { name: "_", source_root: "src", modules: &[] },
            ],
        )
        .unwrap();
        let lakefile = fs::read_to_string(workspace.root().join("lakefile.lean")).unwrap();
        assert!(lakefile.contains("lean_lib «where» where"));
        assert!(lakefile.contains("lean_lib «_» where"));
        assert!(lakefile.contains("globs := #[.one `where.def, .one `Proof'.by]"));
        workspace.admit().unwrap();
        assert_eq!(fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap(), owner);

        let configuration: LakeConfiguration =
            serde_json::from_slice(&fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap())
                .unwrap();
        fs::write(
            workspace.root().join("lakefile.lean"),
            render_lakefile_with_library_escape(&f.sdk, &configuration, false).unwrap(),
        )
        .unwrap();
        assert!(
            workspace
                .lake_command(LakeOperation::Build(&[]))
                .unwrap_err()
                .to_string()
                .contains("Lakefile differs")
        );
    }

    #[test]
    fn case_aliases_follow_the_private_output_filesystem() {
        let f = Fixture::new(&["Config"]);
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("case-workspace"), &["left", "right"]).unwrap();
        configure_test_workspace(&workspace);
        let folds_case = filesystem_folds_ascii_case(&workspace.root().join(OUTPUT_OWNER)).unwrap();
        for root in ["left", "right"] {
            fs::create_dir(workspace.root().join(root)).unwrap();
        }
        fs::write(workspace.root().join("left/config.lean"), "def value := 10\n").unwrap();
        assert_eq!(workspace.admit().is_err(), folds_case);
        fs::remove_file(workspace.root().join("left/config.lean")).unwrap();
        fs::write(workspace.root().join("left/Local.lean"), "def value := 10\n").unwrap();
        fs::write(workspace.root().join("right/local.lean"), "def value := 20\n").unwrap();
        assert_eq!(workspace.admit().is_err(), folds_case);
        fs::remove_file(workspace.root().join("right/local.lean")).unwrap();
        fs::write(workspace.root().join("right/config.LEAN"), "def value := 20\n").unwrap();
        assert_eq!(workspace.admit().is_err(), folds_case);
    }

    #[test]
    fn sdk_case_alias_exports_reject_only_when_the_filesystem_aliases_them() {
        let f = Fixture::new(&["Shared.A"]);
        let folds_case = filesystem_folds_ascii_case(&f.sdk.root().join("modules.json")).unwrap();
        let modules =
            serde_json::to_vec(&json!({"schema": 1, "modules": ["Config", "config"]})).unwrap();
        fs::write(f.sdk.root().join("modules.json"), &modules).unwrap();
        let path = f.sdk.root().join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        descriptor["modules_sha256"] = json!(sha256(&modules));
        fs::write(&path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert_eq!(LeanSdk::load(f.sdk.root()).is_err(), folds_case);
    }

    #[test]
    fn bound_gateway_loads_the_original_sdk_and_lake_serves_with_owned_context() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let bound = Workspace::from_root(workspace.root()).unwrap();
        assert_eq!(bound.sdk().root(), f.sdk.root());
        assert_eq!(bound.sdk().id(), f.sdk.id());
        let command = bound.lake_command(LakeOperation::Serve).unwrap();
        assert_eq!(command.get_program(), f.sdk.root().join("bin/lake"));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            ["--keep-toolchain", "--no-cache", "--reconfigure", "serve"]
        );
    }

    #[test]
    fn module_collision_names_follow_each_librarys_source_directory() {
        let f = Fixture::new(&["Config"]);
        let workspace = Workspace::create(
            &f.sdk,
            &f.base.join("mapped-workspace"),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        fs::create_dir(workspace.root().join("anneal")).unwrap();
        fs::write(workspace.root().join("anneal/Config.lean"), "def value := 1\n").unwrap();
        assert!(workspace.admit().is_err());
    }

    #[test]
    fn commands_use_owned_context_and_reject_option_or_path_overrides() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::create_dir(workspace.root().join("src")).unwrap();
        fs::write(workspace.root().join("src/Proof.lean"), "example : True := by trivial").unwrap();
        fs::write(f.base.join("Outside.lean"), "example : True := by trivial").unwrap();
        assert!(workspace.lake_command(LakeOperation::Build(&["--cache=foreign".into()])).is_err());
        assert!(workspace.lake_command(LakeOperation::Build(&["Proof:exe".into()])).is_err());
        assert!(
            workspace
                .lean_command(LeanOperation::Check {
                    file: &f.base.join("Outside.lean"),
                    json: true
                })
                .is_err()
        );
        assert!(
            workspace
                .lean_command(LeanOperation::Check {
                    file: Path::new("../Outside.lean"),
                    json: true
                })
                .is_err()
        );
        let command =
            workspace.lake_command(LakeOperation::Build(&["+Proof:olean".into()])).unwrap();
        let env: std::collections::BTreeMap<_, _> = command.get_envs().collect();
        assert_eq!(
            env.get(std::ffi::OsStr::new("LAKE_RESTORE_ARTIFACTS")).copied().flatten(),
            Some(std::ffi::OsStr::new("false"))
        );
        let imports = env.get(std::ffi::OsStr::new("LEAN_PATH")).copied().flatten().unwrap();
        assert_eq!(
            std::env::split_paths(imports).collect::<Vec<_>>(),
            [workspace.root().join(".lake/build/lib/lean"), f.sdk.root().join("lib/lean")]
        );
        for key in [
            "HOME",
            "XDG_CACHE_HOME",
            "XDG_CONFIG_HOME",
            "XDG_DATA_HOME",
            "TMPDIR",
            "LAKE_CACHE_DIR",
        ] {
            assert!(
                Path::new(env.get(std::ffi::OsStr::new(key)).copied().flatten().unwrap())
                    .starts_with(workspace.root().join(PRIVATE_RUNTIME))
            );
        }
        assert_eq!(command.get_program(), f.sdk.root().join("bin/lake"));
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            ["--keep-toolchain", "--no-cache", "--reconfigure", "build", "+Proof:olean"]
        );
        // RC2 handles this flag before its ordinary option parser. Placing
        // keep-toolchain/no-cache before it turns a real version probe into a
        // failed command, preventing stock editor startup.
        let version = workspace.lake_command(LakeOperation::Version).unwrap();
        assert_eq!(version.get_args().collect::<Vec<_>>(), ["--version"]);
        // Admission is physical/absolute, while the invocation remains
        // relative to the fixed cwd so V1 diagnostics retain their file names.
        let check = workspace
            .lean_command(LeanOperation::Check {
                file: &workspace.root().join("src/Proof.lean"),
                json: true,
            })
            .unwrap();
        assert_eq!(check.get_current_dir(), Some(workspace.root()));
        assert!(check.get_args().any(|arg| arg == "src/Proof.lean"));
        let dash_source = workspace.root().join("-Proof.lean");
        fs::write(&dash_source, "example : True := by trivial\n").unwrap();
        let check = workspace
            .lean_command(LeanOperation::Check { file: &dash_source, json: false })
            .unwrap();
        assert!(check.get_args().any(|arg| arg == "./-Proof.lean"));
        assert!(!check.get_args().any(|arg| arg == "-Proof.lean"));
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlinked_private_outputs_and_launchers() {
        use std::os::unix::fs::symlink;
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        symlink(f.sdk.root().join("lib/lean"), workspace.root().join(".lake/foreign")).unwrap();
        assert!(workspace.lean_command(LeanOperation::Server).is_err());
        let fake = f.sdk.root().join("bin/other-lean");
        fs::rename(f.sdk.root().join("bin/lean"), &fake).unwrap();
        symlink(&fake, f.sdk.root().join("bin/lean")).unwrap();
        assert!(LeanSdk::load(f.sdk.root()).is_err());
    }

    #[test]
    fn duplicate_exact_export_and_bad_manifest_hash_reject_admission() {
        let f = Fixture::new(&["Shared.A"]);
        let raw =
            serde_json::to_vec(&json!({"schema": 1, "modules": ["Shared.A", "Shared.A"]})).unwrap();
        fs::write(f.sdk.root().join("modules.json"), &raw).unwrap();
        assert!(LeanSdk::load(f.sdk.root()).is_err());
        let descriptor_path = f.sdk.root().join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        descriptor["modules_sha256"] = json!(sha256(&raw));
        fs::write(&descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(f.sdk.root()).is_err());
    }
}
