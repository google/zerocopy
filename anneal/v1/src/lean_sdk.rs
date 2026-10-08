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
    sync::Arc,
};

use anyhow::{Context as _, Result, bail, ensure};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

const SCHEMA: u32 = 1;
const BINDING: &str = ".anneal-sdk.json";
const OUTPUT_OWNER: &str = ".lake/.anneal-owner.json";
const PRIVATE_RUNTIME: &str = ".runtime";
const LAKE_CONFIGURATION: &str = ".anneal-lake.json";
const LOCAL_INPUT_PROVENANCE: &str = ".lake/.anneal-local-inputs";
const MAX_DESCRIPTOR_SIZE: u64 = 64 * 1024;
const MAX_MODULES_SIZE: u64 = 32 * 1024 * 1024;

// Native open flags for the supported Darwin/Linux host tuples. Keep these
// local rather than introducing another dependency for two descriptor checks.
#[cfg(target_os = "macos")]
const NONBLOCK_OPEN_FLAG: i32 = 0x0004;
#[cfg(all(target_os = "linux", any(target_arch = "aarch64", target_arch = "x86_64")))]
const NONBLOCK_OPEN_FLAG: i32 = 0x0800;
#[cfg(target_os = "macos")]
const NOFOLLOW_OPEN_FLAG: i32 = 0x0100;
// Linux arm64 overrides asm-generic O_NOFOLLOW; 0x20000 is its O_LARGEFILE.
#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const NOFOLLOW_OPEN_FLAG: i32 = 0x8000;
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const NOFOLLOW_OPEN_FLAG: i32 = 0x20000;

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
pub struct SavedInputSnapshot {
    stamp: [u8; 32],
    relocation_stamp: [u8; 32],
    root_identity: Vec<u8>,
    auxiliary_stamp: [u8; 32],
}

#[derive(Clone, Copy)]
enum PrivateAdmission {
    SavedObservation,
    Complete,
}

/// An owned, coherent preparation for local compilation. The caller must hold
/// the workspace writer lease until all compilation ends and this is finished.
/// Dropping an unfinished preparation leaves persistent provenance absent.
#[derive(Debug)]
pub struct LocalOutputPreparation {
    binding: Binding,
    stamp: [u8; 32],
    auxiliary_stamp: [u8; 32],
}

impl LocalOutputPreparation {
    pub fn stamp(&self) -> [u8; 32] {
        self.stamp
    }
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
    #[serde(default)]
    finite_lake: Option<FiniteLake>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct FiniteLake {
    path: PathBuf,
    sha256: String,
    protocol: u32,
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

/// A shared handle to one publisher-admitted installation. Cloning does not
/// reload or copy the immutable module map; command and workspace admission
/// still check the descriptor and physical installation on every invocation.
#[derive(Clone, Debug)]
pub struct LeanSdk {
    inner: Arc<LeanSdkInner>,
}

#[derive(Debug)]
struct LeanSdkInner {
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
    /// modified. The module manifest is read once per admission and shared by
    /// clones.
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
        ensure!(matches!(descriptor.schema, 1 | 2), "Unsupported SDK descriptor schema");
        ensure!(
            (descriptor.schema == 2) == descriptor.finite_lake.is_some(),
            "SDK descriptor finite helper does not match its schema"
        );
        if descriptor.schema == 1 {
            let fields: serde_json::Value = serde_json::from_slice(&raw)?;
            ensure!(fields.get("finite_lake").is_none(), "Schema 1 cannot declare a finite helper");
        }
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
        if let Some(helper) = &descriptor.finite_lake {
            check_finite_helper(&root, &installation, helper)?;
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
            inner: Arc::new(LeanSdkInner {
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
            }),
        };
        command_search_paths(&sdk, None)?;
        Ok(sdk)
    }

    pub fn id(&self) -> &str {
        &self.inner.descriptor.id
    }

    pub fn root(&self) -> &Path {
        &self.inner.root
    }

    pub fn lean_toolchain(&self) -> &str {
        &self.inner.descriptor.lean_toolchain
    }

    pub(crate) fn has_module(&self, name: &str) -> bool {
        self.inner.modules.contains(name)
    }

    pub fn plugins(&self) -> &[Plugin] {
        &self.inner.plugins
    }

    fn check_descriptor(&self) -> Result<()> {
        ensure!(
            sha256(&read_small(&self.inner.root.join("sdk.json"), MAX_DESCRIPTOR_SIZE)?)
                == self.inner.descriptor_sha256,
            "SDK descriptor changed after admission"
        );
        for launcher in ["lean", "lake"] {
            check_launcher(&self.inner.root.join("bin").join(launcher), &self.inner.installation)?;
        }
        if let Some(helper) = &self.inner.descriptor.finite_lake {
            check_launcher(&self.inner.root.join(&helper.path), &self.inner.installation)?;
        }
        for plugin in &self.inner.plugins {
            ensure!(
                plugin.path.is_file(),
                "Missing admitted native plugin: {}",
                plugin.path.display()
            );
        }
        Ok(())
    }

    pub(crate) fn check_finite_integrity(&self) -> Result<()> {
        self.check_descriptor()?;
        let helper =
            self.inner.descriptor.finite_lake.as_ref().context("SDK has no finite helper")?;
        check_finite_helper(&self.inner.root, &self.inner.installation, helper)
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

/// An exclusive observation fence waiting for inherited producers to stop.
/// It is not output mutation capability until `try_admit` completes. Retain it
/// across bounded polls so live source peers can observe sustained contention.
pub(crate) struct WriterReservation {
    root: PathBuf,
    file: Option<fs::File>,
    workspace: Option<Workspace<'static>>,
    producer_create: bool,
}

impl WriterReservation {
    fn try_root(root: &Path, create: bool) -> Result<Option<Self>> {
        let root = physical_workspace_path(root)?;
        check_workspace_parent_namespace(&root)?;
        let (file, path) = open_workspace_lock_path(workspace_lock_path(&root, false)?, create)?;
        match fs2::FileExt::try_lock_exclusive(&file) {
            Ok(()) => {
                check_workspace_lock_entry(&file, &path)?;
                Ok(Some(Self { root, file: Some(file), workspace: None, producer_create: create }))
            }
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => Ok(None),
            Err(error) => Err(error.into()),
        }
    }

    pub(crate) fn fence(&self) -> &fs::File {
        self.file.as_ref().expect("Admitted writer reservation has no fence")
    }

    pub(crate) fn try_admit(&mut self) -> Result<Option<fs::File>> {
        let file = self.fence();
        let path = workspace_lock_path(&self.root, false)?;
        check_workspace_lock_entry(file, &path)?;
        if !try_native_producer_barrier(&self.root, self.producer_create)? {
            return Ok(None);
        }
        advance_writer_witness(file).context("Recording reserved workspace writer acquisition")?;
        check_workspace_lock_entry(file, &path)?;
        if let Some(workspace) = &self.workspace {
            workspace.admit()?;
        }
        check_workspace_lock_entry(file, &path)?;
        Ok(self.file.take())
    }

    pub(crate) fn into_workspace(self) -> Result<Workspace<'static>> {
        ensure!(self.file.is_none(), "Writer reservation has not been admitted");
        self.workspace.context("Unbound writer reservation has no workspace")
    }
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
    /// Each file is replaced through a fresh regular inode. The two renames
    /// are not pair-atomic: a later rename failure can leave only the spec
    /// replaced. Admission still checks the complete pair before invocation.
    pub fn write_lakefile(sdk: &LeanSdk, root: &Path, libraries: &[LakeLibrary<'_>]) -> Result<()> {
        sdk.check_descriptor()?;
        let root = physical_workspace_path(root).context("Unknown Lean workspace stage")?;
        ensure!(root.is_dir(), "Lean workspace stage is not a directory");
        check_workspace_namespace(&root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        ensure!(
            binding.schema == SCHEMA
                && binding.sdk_id == sdk.id()
                && binding.sdk_root == sdk.root()
                && binding.descriptor_sha256 == sdk.inner.descriptor_sha256,
            "Lake configuration SDK binding mismatch"
        );
        let requested_roots =
            libraries.iter().map(|library| PathBuf::from(library.source_root)).collect::<Vec<_>>();
        let folds_case = filesystem_folds_ascii_case(&root.join(BINDING))?;
        let configured_roots = normalize_source_roots(&requested_roots, folds_case)?;
        let configuration = LakeConfiguration {
            libraries: libraries
                .iter()
                .zip(configured_roots)
                .map(|(library, source_root)| LibraryConfiguration {
                    name: library.name.to_owned(),
                    source_root,
                    modules: library.modules.to_vec(),
                })
                .collect(),
        };
        validate_lake_configuration(&configuration, &binding.source_roots)?;
        validate_persisted_source_roots(&binding.source_roots, folds_case)?;
        reject_reserved_source_aliases(&binding.source_roots, folds_case)?;
        let configuration_bytes = serde_json::to_vec_pretty(&configuration)?;
        ensure!(
            configuration_bytes.len() as u64 <= MAX_MODULES_SIZE,
            "Generated Lake configuration exceeds size limit"
        );
        let lakefile = render_lakefile(sdk, &configuration)?;
        ensure!(lakefile.len() as u64 <= MAX_MODULES_SIZE, "Generated Lakefile exceeds size limit");
        for filename in [LAKE_CONFIGURATION, "lakefile.lean"] {
            reject_links(&root.join(filename))?;
        }
        ensure!(!root.join("lakefile.toml").try_exists()?, "Unsupported alternate Lakefile");
        // Seed an absent manifest when rendering dependency-free configuration. Existing
        // manifests must pass the same gate; never let Lake repair them first.
        let manifest_path = root.join("lake-manifest.json");
        reject_links(&manifest_path)?;
        if manifest_path.try_exists()? {
            check_dependency_free_manifest(&read_small(&manifest_path, MAX_MODULES_SIZE)?)?;
        } else {
            let mut manifest =
                OpenOptions::new().write(true).create_new(true).open(&manifest_path)?;
            manifest.write_all(b"{\"version\":\"1.2.0\",\"packagesDir\":\".lake/packages\",\"packages\":[],\"name\":\"anneal_verification\",\"lakeDir\":\".lake\"}\n")?;
        }
        let mut spec = tempfile::Builder::new().prefix(".anneal-lake-").tempfile_in(&root)?;
        spec.write_all(&configuration_bytes)?;
        let mut script = tempfile::Builder::new().prefix(".anneal-lake-").tempfile_in(&root)?;
        script.write_all(lakefile.as_bytes())?;
        spec.persist(root.join(LAKE_CONFIGURATION)).map_err(|error| error.error)?;
        script.persist(root.join("lakefile.lean")).map_err(|error| error.error)?;
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
        let staging_root = physical_workspace_path(staging_root)?;
        check_workspace_parent_namespace(&staging_root)?;
        let final_root = physical_workspace_path(final_root)?;
        // Check destination ancestors before any disposable policy/owner probe
        // or stage directory can be created. The prospective leaf need not exist.
        check_workspace_parent_namespace(&final_root)?;
        ensure!(
            existing.is_none_or(|existing| {
                !staging_root.starts_with(&final_root) && !staging_root.starts_with(&existing.root)
            }),
            "Existing workspace stage must be outside the live workspace"
        );
        reject_stage_ancestry(&staging_root, &final_root)?;
        if let Some(existing) = existing {
            ensure!(existing.root == final_root, "Cannot move an existing workspace binding");
        }
        ensure!(
            !staging_root.starts_with(&sdk.inner.installation),
            "Workspace stage is inside the immutable installation"
        );
        ensure!(
            !final_root.starts_with(&sdk.inner.installation),
            "Workspace is inside the immutable installation"
        );
        reject_workspace_lock_name(&final_root, None)?;
        reject_workspace_lock_name(&staging_root, None)?;
        let requested_roots = source_roots.iter().map(PathBuf::from).collect::<Vec<_>>();
        validate_bound_source_roots(&requested_roots)?;
        let stage_parent = staging_root.parent().context("Workspace stage has no parent")?;
        let final_parent = final_root.parent().context("Workspace has no parent")?;
        let final_device = filesystem_device(&fs::metadata(final_parent)?)?;
        if existing.is_some() {
            ensure!(
                filesystem_device(&fs::metadata(&final_root)?)? == final_device,
                "Workspace final root must share its parent filesystem for replacement"
            );
        }
        ensure_stage_destination_policy(
            filesystem_device(&fs::metadata(stage_parent)?)?,
            final_device,
            filesystem_case_of_new_child(stage_parent)?,
            if let Some(existing) = existing {
                filesystem_folds_ascii_case(&existing.root.join(BINDING))?
            } else {
                filesystem_case_of_new_child(final_parent)?
            },
        )?;
        let owner = if existing.is_none() {
            Some(
                tempfile::Builder::new()
                    .prefix(".anneal-owner-")
                    .tempfile_in(final_root.parent().unwrap())?,
            )
        } else {
            None
        };
        let folds_case = if let Some(owner) = &owner {
            filesystem_folds_ascii_case(owner.path())?
        } else {
            filesystem_folds_ascii_case(&existing.unwrap().root.join(BINDING))?
        };
        let source_roots = normalize_source_roots(&requested_roots, folds_case)?;
        reject_physical_source_root_aliases(stage_parent, &source_roots)?;
        if final_parent != stage_parent {
            reject_physical_source_root_aliases(final_parent, &source_roots)?;
        }
        command_search_paths(sdk, Some((&final_root, &source_roots)))?;
        let binding = if let Some(existing) = existing {
            existing.admit()?;
            ensure!(existing.root == final_root, "Cannot move an existing workspace binding");
            ensure!(
                existing.binding.sdk_id == sdk.id(),
                "Cannot upgrade an existing workspace SDK"
            );
            ensure!(
                existing.binding.sdk_root == sdk.root(),
                "Cannot relocate an existing workspace SDK"
            );
            ensure!(
                existing.binding.descriptor_sha256 == sdk.inner.descriptor_sha256,
                "Cannot change an existing workspace descriptor"
            );
            ensure!(
                existing.binding.source_roots == source_roots,
                "Cannot change bound source-root mapping"
            );
            existing.binding.clone()
        } else {
            ensure!(!final_root.try_exists()?, "Workspace creation requires a fresh final path");
            let owner = owner.as_ref().unwrap();
            reject_reserved_source_aliases(&source_roots, folds_case)?;
            Binding {
                schema: SCHEMA,
                sdk_id: sdk.id().to_owned(),
                sdk_root: sdk.root().to_path_buf(),
                descriptor_sha256: sdk.inner.descriptor_sha256.clone(),
                workspace: final_root,
                owner: owner.path().file_name().unwrap().to_string_lossy().into_owned(),
                source_roots,
            }
        };
        let mut binding_bytes = serde_json::to_vec_pretty(&binding)?;
        binding_bytes.push(b'\n');
        ensure!(
            binding_bytes.len() as u64 <= MAX_DESCRIPTOR_SIZE,
            "Workspace binding exceeds descriptor size limit"
        );
        let mut stage_directory = fs::DirBuilder::new();
        #[cfg(unix)]
        {
            use std::os::unix::fs::DirBuilderExt as _;
            // The staged root becomes the editor workspace after installation.
            // Give it a protected mode at creation, independent of umask.
            stage_directory.mode(0o700);
        }
        stage_directory
            .create(&staging_root)
            .context("Workspace stage must be a nonexistent directory")?;
        write_new_bytes(&staging_root.join(BINDING), &binding_bytes)?;
        if existing.is_none() {
            fs::create_dir(staging_root.join(".lake"))?;
            write_new_bytes(&staging_root.join(OUTPUT_OWNER), &binding_bytes)?;
            fs::create_dir(staging_root.join(PRIVATE_RUNTIME))?;
            for dir in ["home", "cache", "config", "data", "tmp"] {
                fs::create_dir(staging_root.join(PRIVATE_RUNTIME).join(dir))?;
            }
        }
        Ok(())
    }

    pub fn admit_stage(sdk: &LeanSdk, stage: &Path, final_root: &Path) -> Result<()> {
        sdk.check_descriptor()?;
        // Resolve parent aliases, but retain and check the leaf that the owner
        // will rename. Canonicalizing the whole stage would erase a leaf link.
        let stage = physical_workspace_path(stage).context("Unknown Lean workspace stage")?;
        ensure!(stage.is_dir(), "Lean workspace stage is not a directory");
        check_workspace_namespace(&stage)?;
        let final_root = physical_workspace_path(final_root)?;
        // Check destination ancestors before any disposable policy/owner probe
        // or stage directory can be created. The prospective leaf need not exist.
        check_workspace_parent_namespace(&final_root)?;
        // The stage may have moved since creation. Resolve existing ancestors
        // and reject nesting before any name-policy probe can touch live inputs.
        reject_stage_ancestry(&stage, &final_root)?;
        reject_workspace_lock_name(&stage, Some(&stage.join(BINDING)))?;
        reject_workspace_lock_name(
            &final_root,
            final_root.try_exists()?.then(|| final_root.join(BINDING)).as_deref(),
        )?;
        let final_parent = final_root.parent().context("Workspace has no parent")?;
        let destination_device = filesystem_device(&fs::metadata(final_parent)?)?;
        let stage_device = filesystem_device(&fs::metadata(&stage)?)?;
        let stage_parent_device = filesystem_device(&fs::metadata(
            stage.parent().context("Workspace stage has no parent")?,
        )?)?;
        ensure!(
            stage_device == stage_parent_device,
            "Workspace stage root must share its parent filesystem for replacement"
        );
        let existing = match fs::metadata(&final_root) {
            Ok(metadata) => {
                ensure!(
                    filesystem_device(&metadata)? == destination_device,
                    "Workspace final root must share its parent filesystem for replacement"
                );
                // The owner already holds the writer fence. Admit the complete
                // live workspace without acquiring that fence a second time.
                Some(Workspace::open(sdk, &final_root)?)
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error.into()),
        };
        let final_exists = existing.is_some();
        let final_folds_case = if final_exists {
            filesystem_folds_ascii_case(&final_root.join(BINDING))?
        } else {
            filesystem_case_of_new_child(final_parent)?
        };
        ensure_stage_destination_policy(
            stage_device,
            destination_device,
            filesystem_folds_ascii_case(&stage.join(BINDING))?,
            final_folds_case,
        )?;
        if final_exists {
            // These destinations must be absent before the owner isolates the
            // live tree and transfers its complete private outputs and runtime.
            // Even empty directories, links, or special files are unsupported.
            for private in [".lake", PRIVATE_RUNTIME] {
                match fs::symlink_metadata(stage.join(private)) {
                    Ok(_) => {
                        bail!(
                            "Replacement stage contains a private output/runtime entry: {private}"
                        )
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
            }
        }
        let binding: Binding = read_json(&stage.join(BINDING))?;
        ensure!(binding.schema == SCHEMA && !binding.owner.is_empty(), "Invalid stage owner");
        ensure!(
            binding.sdk_id == sdk.id()
                && binding.sdk_root == sdk.root()
                && binding.descriptor_sha256 == sdk.inner.descriptor_sha256
                && binding.workspace == new_physical_path(&final_root)?,
            "Stage binding changed"
        );
        if let Some(existing) = &existing {
            ensure!(
                binding == existing.binding,
                "Replacement stage binding differs from live workspace"
            );
        } else {
            check_workspace_private_layout(&stage, &binding, &LocalFilesystemPolicy::at(&stage)?)?;
        }
        validate_bound_source_roots(&binding.source_roots)?;
        validate_persisted_source_roots(
            &binding.source_roots,
            filesystem_folds_ascii_case(&stage.join(BINDING))?,
        )?;
        let stage_parent = stage.parent().context("Workspace stage has no parent")?;
        reject_physical_source_root_aliases(stage_parent, &binding.source_roots)?;
        if final_parent != stage_parent {
            reject_physical_source_root_aliases(final_parent, &binding.source_roots)?;
        }
        reject_existing_source_root_aliases(&stage, &binding.source_roots)?;
        if final_exists {
            reject_existing_source_root_aliases(&final_root, &binding.source_roots)?;
        }
        command_search_paths(sdk, Some((&binding.workspace, &binding.source_roots)))?;
        check_lake_configuration(sdk, &stage, &binding.source_roots, false)?;
        let folds_case = filesystem_folds_ascii_case(&stage.join(BINDING))?;
        reject_reserved_source_aliases(&binding.source_roots, folds_case)?;
        let mut local_modules = BTreeSet::new();
        for source in &binding.source_roots {
            let source = stage.join(source);
            if source.try_exists()? {
                check_local_sources(&source, &source, &stage, sdk, folds_case, &mut local_modules)?;
            }
        }
        // Also establish that every saved input will be tracked on invocation.
        saved_inputs(&stage)?;
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

    /// Reuse the selected installation when it is this workspace's physical
    /// binding. A Rust-only archive move can retain the same Lean identity at
    /// another path; in that case admit the original bound installation once,
    /// rather than retargeting its outputs to the newly selected installation.
    /// A different Lean identity never takes this preservation route.
    pub(crate) fn open_bound(sdk: &'a LeanSdk, root: &Path) -> Result<Self> {
        let root = fs::canonicalize(root).context("Unknown Lean workspace")?;
        ensure!(root.to_str().is_some(), "Lean workspace path must be UTF-8");
        reject_links(&root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        ensure!(binding.schema == SCHEMA, "Unsupported workspace binding schema");
        ensure!(binding.sdk_root.is_absolute(), "Workspace SDK path must be absolute");
        ensure!(binding.sdk_id == sdk.id(), "Workspace SDK identity changed");
        let workspace = if binding.sdk_root == sdk.root() {
            Self::open(sdk, &root)?
        } else {
            Self::from_root(&root)?
        };
        // Constructors read and admit the binding again. A changed identity
        // between the preliminary observation and admission must also fail.
        ensure!(workspace.sdk().id() == sdk.id(), "Workspace SDK identity changed");
        Ok(workspace)
    }

    /// Resolve the fixed SDK selected when this workspace was created. This
    /// gateway never resolves the current global toolchain or ambient Elan.
    pub fn from_root(root: &Path) -> Result<Workspace<'static>> {
        Self::from_root_with_private(root, PrivateAdmission::Complete)
    }

    fn from_root_with_private(
        root: &Path,
        private: PrivateAdmission,
    ) -> Result<Workspace<'static>> {
        let root = fs::canonicalize(root).context("Unknown Lean workspace")?;
        ensure!(root.to_str().is_some(), "Lean workspace path must be UTF-8");
        reject_links(&root)?;
        let binding: Binding = read_json(&root.join(BINDING))?;
        ensure!(binding.schema == SCHEMA, "Unsupported workspace binding schema");
        ensure!(binding.sdk_root.is_absolute(), "Workspace SDK path must be absolute");
        let sdk = LeanSdk::load(&binding.sdk_root)?;
        let workspace = Workspace { sdk: Cow::Owned(sdk), root, binding };
        workspace.admit_with_private_contents(private)?;
        Ok(workspace)
    }

    /// The lock is a sibling of the replaceable workspace directory. All Anneal
    /// source/output writers use it; locks do not control direct user edits.
    pub fn lock_root(root: &Path) -> Result<fs::File> {
        let (file, path) = open_workspace_lock(root, false)?;
        fs2::FileExt::lock_exclusive(&file)?;
        check_workspace_lock_entry(&file, &path)?;
        // Holding the main writer fence signals the coordinator to suspend.
        // Return mutation capability only after every inherited native holder
        // has released the separate producer lease.
        wait_native_producers(root)?;
        check_workspace_lock_entry(&file, &path)?;
        advance_writer_witness(&file).context("Recording workspace writer acquisition")?;
        check_workspace_lock_entry(&file, &path)?;
        Ok(file)
    }

    pub fn writer_lock(&self) -> Result<fs::File> {
        let file = Self::lock_root(&self.root)?;
        self.admit()?;
        Ok(file)
    }

    pub(crate) fn startup_writer_until(
        root: &Path,
        deadline: std::time::Instant,
        mut cancelled: impl FnMut() -> bool,
    ) -> Result<(Workspace<'static>, fs::File)> {
        let mut pending: Option<WriterReservation> = None;
        loop {
            ensure!(!cancelled(), "Workspace operation interrupted");
            if pending.is_none() {
                pending = Self::try_reserve_root_for_startup(root)?;
            }
            if let Some(reservation) = pending.as_mut() {
                if let Some(writer) = reservation.try_admit()? {
                    let workspace = pending.take().unwrap().into_workspace()?;
                    return Ok((workspace, writer));
                }
            }
            ensure!(
                std::time::Instant::now() < deadline,
                "Workspace writer is busy; retry startup after it completes"
            );
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
    }

    pub(crate) fn try_reserve_root_for_startup(root: &Path) -> Result<Option<WriterReservation>> {
        let Some(mut reservation) = WriterReservation::try_root(root, false).context(
            "Startup requires an existing stable workspace writer lock; generate the workspace first",
        )? else {
            return Ok(None);
        };
        let resolved = fs::canonicalize(&reservation.root).context("Unknown Lean workspace")?;
        check_workspace_lock_entry(reservation.fence(), &workspace_lock_path(&resolved, false)?)?;
        let workspace =
            Self::from_root_with_private(&resolved, PrivateAdmission::SavedObservation)?;
        check_workspace_lock_entry(
            reservation.fence(),
            &workspace_lock_path(workspace.root(), false)?,
        )?;
        reservation.root = resolved;
        reservation.workspace = Some(workspace);
        Ok(Some(reservation))
    }

    pub fn try_writer_lock(&self) -> Result<Option<fs::File>> {
        self.try_lock(false)
    }

    /// Fence saved observations against cooperative external writers. This does
    /// not certify outputs produced by our own still-running native processes.
    /// Artifact consumers must separately perform complete admission.
    pub fn try_shared_lock(&self) -> Result<Option<fs::File>> {
        self.try_lock(true)
    }

    /// Finite groups start under an admitted main writer. Their inherited
    /// shared holder also fences successor writers if cancellation releases it.
    pub(crate) fn finite_producer_lease(&self) -> Result<FiniteProducerLease> {
        self.admit_saved_observation()?;
        FiniteProducerLease::acquire(&self.root)
    }

    /// One mutable-document coordinator per workspace. This separate lease
    /// leaves batch writers free to build while the editor is open.
    pub fn server_lock(&self) -> Result<fs::File> {
        // This reserves coordinator identity before acquiring a startup writer;
        // it consumes no private artifacts produced by the incumbent server.
        self.admit_saved_observation()?;
        let (file, path) = open_workspace_lock(&self.root, true)?;
        fs2::FileExt::try_lock_exclusive(&file).context(
            "An editor coordinator already owns this workspace; close it before starting another",
        )?;
        check_workspace_lock_entry(&file, &path)?;
        Ok(file)
    }

    fn try_lock(&self, shared: bool) -> Result<Option<fs::File>> {
        let (file, path) = open_workspace_lock(&self.root, false)?;
        let result = if shared {
            fs2::FileExt::try_lock_shared(&file)
        } else {
            fs2::FileExt::try_lock_exclusive(&file)
        };
        match result {
            Ok(()) => {
                check_workspace_lock_entry(&file, &path)?;
                if !shared {
                    if !try_native_producer_barrier(&self.root, true)? {
                        return Ok(None);
                    }
                    advance_writer_witness(&file)
                        .context("Recording workspace writer acquisition")?;
                    check_workspace_lock_entry(&file, &path)?;
                }
                if shared {
                    // Our own native server can still be producing private
                    // configuration/cache files under this shared fence.
                    self.admit_saved_observation()?;
                } else {
                    self.admit()?;
                }
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
        self.admit_saved_observation()?;
        if self.local_source_relative(path)?.is_some() {
            return self.local_source(path).map(|_| true);
        }
        self.contains_sdk_source(path)
    }

    pub fn contains_sdk_source(&self, path: &Path) -> Result<bool> {
        self.admit_saved_observation()?;
        self.contains_immutable_sdk_source(path)
    }

    /// Look up only the fixed immutable SDK's admitted source providers. This
    /// checks the SDK descriptor, not workspace admission, and remains usable
    /// while an external writer temporarily replaces the writable tree.
    /// A filesystem case alias must still resolve to the exact exported
    /// `.lean` provider, rather than a distinct file with the same stem.
    pub fn contains_immutable_sdk_source(&self, path: &Path) -> Result<bool> {
        self.sdk.check_descriptor()?;
        if path.extension().and_then(|s| s.to_str()).is_none_or(|s| !s.eq_ignore_ascii_case("lean"))
        {
            return Ok(false);
        }
        let physical = match fs::canonicalize(path) {
            Ok(path) => path,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(false),
            Err(error) => return Err(error.into()),
        };
        if physical
            .extension()
            .and_then(|s| s.to_str())
            .is_none_or(|s| !s.eq_ignore_ascii_case("lean"))
        {
            return Ok(false);
        }
        let physical_metadata = fs::metadata(&physical)?;
        if !physical_metadata.is_file() {
            return Ok(false);
        }
        // Published source views may link a complete subtree, or individual
        // files in a merged namespace, to distinct physical provider roots.
        // Derive only module-shaped suffix candidates from the physical path,
        // then resolve that exact module through each admitted source view.
        let components = physical.components().map(|part| part.as_os_str()).collect::<Vec<_>>();
        for start in 0..components.len() {
            let relative = components[start..].iter().copied().collect::<PathBuf>();
            let components = relative.with_extension("");
            let parts = components
                .iter()
                .map(|c| c.to_str().context("Non-UTF8 SDK module component"))
                .collect::<Result<Vec<_>>>()?;
            if !parts.iter().all(|part| valid_component(part)) {
                continue;
            }
            let module = parts.join(".");
            if !self.sdk.inner.modules.contains(&module) {
                continue;
            }
            // A dotted filename may spell the same module text as a nested
            // provider, but only the manifest module's component path is real.
            for source in &self.sdk.inner.sources {
                let provider = source.join(module.replace('.', "/")).with_extension("lean");
                let provider = match fs::canonicalize(&provider) {
                    Ok(provider) => provider,
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                    Err(error) => return Err(error.into()),
                };
                if provider == physical {
                    return Ok(true);
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
        self.admit_saved_observation()?;
        let Ok(root) = fs::canonicalize(root) else { return Ok(false) };
        if !root.is_dir() || !root.starts_with(&self.sdk.inner.installation) {
            return Ok(false);
        }
        for source in &self.sdk.inner.sources {
            if root == *source {
                return Ok(true);
            }
            for module in &self.sdk.inner.modules {
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
    pub fn folds_ascii_case(&self) -> Result<bool> {
        filesystem_folds_ascii_case(&self.root.join(BINDING))
    }

    /// Fingerprint all nonprivate regular saved local inputs. Compare
    /// stamps around builds and checks before accepting their results as current.
    /// Private incremental outputs and caches are deliberately excluded. File
    /// and directory modification identities catch ordinary edit-and-restore
    /// races, including replacement of an entire saved-source tree.
    pub fn source_stamp(&self) -> Result<[u8; 32]> {
        Ok(self.source_snapshot()?.stamp())
    }

    pub(crate) fn source_snapshot(&self) -> Result<SavedInputSnapshot> {
        self.admit_saved_observation()?;
        let snapshot = snapshot_saved_inputs(&self.root, |_| {})?;
        let binding: Binding = read_json(&self.root.join(BINDING))?;
        ensure!(binding == self.binding, "Workspace binding changed after opening");
        Ok(snapshot)
    }

    /// Prepare owned local outputs under the caller's writer lease. Supported
    /// dependencies are the contents of all permitted nonprivate files and the
    /// paths/types of their directory entries, including declared Lean sources
    /// read as data. Any changed saved content conservatively invalidates local
    /// build outputs; unchanged inputs retain warm outputs. Filesystem metadata
    /// dependencies, external I/O, and observing private namespaces (even through
    /// directory enumeration) are outside this contract, not sandboxed here.
    /// For example, a source-relative `include_str "../policy.txt"` outside the
    /// workspace is not stamped; changing it does not invalidate a warm OLean.
    /// Copy needed mutable data into the preserved `user/` subtree and read it
    /// there before relying on reusable local results.
    pub fn prepare_local_outputs(&self) -> Result<LocalOutputPreparation> {
        self.admit()?;
        check_lake_configuration(&self.sdk, &self.root, &self.binding.source_roots, true)?;
        let snapshot = self.source_snapshot()?;
        let marker = self.root.join(LOCAL_INPUT_PROVENANCE);
        let expected = format!("{}\n", hex_digest(snapshot.auxiliary_stamp));
        let previous = match fs::File::open(&marker) {
            Ok(file) => {
                let mut bytes = Vec::with_capacity(66);
                file.take(66).read_to_end(&mut bytes)?;
                Some(bytes)
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(error.into()),
        };
        // Remove the marker before any output mutation or compilation. A
        // rejected/interrupted build must never certify partially new outputs.
        if previous.is_some() {
            fs::remove_file(&marker)?;
        }
        if previous.as_deref() != Some(expected.as_bytes()) {
            let build = self.root.join(".lake/build");
            if build.try_exists()? {
                fs::remove_dir_all(build)?;
            }
        }
        prune_undeclared_outputs(&self.root)?;
        ensure!(
            self.source_stamp()? == snapshot.stamp(),
            SourceStampChanged::new("Saved Lean inputs changed while preparing local outputs")
        );
        Ok(LocalOutputPreparation {
            binding: self.binding.clone(),
            stamp: snapshot.stamp(),
            auxiliary_stamp: snapshot.auxiliary_stamp,
        })
    }

    /// Commit provenance only after successful compilation of the unchanged
    /// prepared inputs, still under the same caller-owned writer lease.
    pub fn finish_local_outputs(&self, prepared: &LocalOutputPreparation) -> Result<()> {
        self.admit()?;
        ensure!(prepared.binding == self.binding, "Local output preparation owner changed");
        ensure!(
            self.source_stamp()? == prepared.stamp,
            SourceStampChanged::new("Saved Lean inputs changed while compiling local outputs")
        );
        let marker = self.root.join(LOCAL_INPUT_PROVENANCE);
        reject_links(&marker)?;
        let content = format!("{}\n", hex_digest(prepared.auxiliary_stamp));
        let mut file = OpenOptions::new().write(true).create_new(true).open(marker)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }

    /// Observe an already-admitted workspace after its owner has renamed it to
    /// a sibling backup. This cannot open commands, adopt outputs, or retarget
    /// its binding; it only rechecks the saved-input snapshot before a swap.
    /// The caller must compare the full live stamp to `original` immediately
    /// before its isolation rename, and call this before transferring outputs.
    pub fn source_stamp_at(
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
        let binding: Binding = read_json(&relocated_root.join(BINDING))?;
        ensure!(binding == self.binding, "Saved-input backup binding changed");
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
        self.admit_with_private_contents(PrivateAdmission::Complete)
    }

    /// Saved observations do not consume or certify private artifacts. An owned
    /// Lake/Lean producer can create, rename, and remove ordinary entries there
    /// even while this coordinator holds its writer fence. Check the stable
    /// namespace/ownership boundaries without enumerating producer descendants;
    /// Output-consuming commands and completed producers still require full private admission.
    pub(crate) fn admit_saved_observation(&self) -> Result<()> {
        self.admit_with_private_contents(PrivateAdmission::SavedObservation)
    }

    fn admit_with_private_contents(&self, private: PrivateAdmission) -> Result<()> {
        check_workspace_namespace(&self.root)?;
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
            binding.descriptor_sha256 == self.sdk.inner.descriptor_sha256,
            "Workspace SDK descriptor mismatch"
        );
        ensure!(
            binding.workspace == self.root && !binding.owner.is_empty(),
            "Workspace location or owner mismatch"
        );
        validate_bound_source_roots(&binding.source_roots)?;
        command_search_paths(&self.sdk, Some((&self.root, &binding.source_roots)))?;
        check_lake_configuration(&self.sdk, &self.root, &binding.source_roots, false)?;
        let policy = LocalFilesystemPolicy::at(&self.root)?;
        validate_persisted_source_roots(&binding.source_roots, policy.folds_case)?;
        reject_existing_source_root_aliases(&self.root, &binding.source_roots)?;
        if matches!(private, PrivateAdmission::Complete) {
            check_workspace_private_layout(&self.root, &binding, &policy)?;
        } else {
            check_workspace_private_roots(&self.root, &binding, &policy)?;
        }
        let mut local_modules = BTreeSet::new();
        let folds_case = policy.folds_case;
        reject_reserved_source_aliases(&binding.source_roots, folds_case)?;
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
        // Include local data outside module roots in the same filesystem/input
        // contract before any command is constructed.
        saved_inputs(&self.root)?;
        Ok(())
    }

    pub fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
        let private = if matches!(operation, LakeOperation::Version) {
            PrivateAdmission::SavedObservation
        } else {
            PrivateAdmission::Complete
        };
        self.lake_command_with_private(operation, private)
    }

    fn lake_command_with_private(
        &self,
        operation: LakeOperation<'_>,
        private: PrivateAdmission,
    ) -> Result<Command> {
        let mut command = self.command_with_private("lake", private)?;
        // RC2 recognizes --version before its ordinary option parser; it must
        // be the first argument. Version inspection cannot schedule builds.
        if !matches!(operation, LakeOperation::Version) {
            check_lake_configuration(&self.sdk, &self.root, &self.binding.source_roots, true)?;
            // Lake consumes its manifest independently of the generated config.
            // Recheck it before every operation that can load the workspace;
            // generation-time admission cannot certify a later edited manifest.
            let manifest = self.root.join("lake-manifest.json");
            reject_links(&manifest)?;
            check_dependency_free_manifest(&read_small(&manifest, MAX_MODULES_SIZE)?)?;
            // Let Lake reuse an unchanged configuration. The exact generated
            // configuration is still admitted above on every invocation; Lake
            // tracks changes to it without forcing recompilation on warm calls.
            command.args(["--keep-toolchain", "--no-cache"]);
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

    /// Inspect the exact known generated configuration without acquiring a
    /// writer lease. The operation owner already holds that lease. A legacy
    /// descriptor or absent legacy manifest selects incumbent stock commands.
    pub(crate) fn finite_inputs(&self) -> Result<Option<(String, String)>> {
        self.admit()?;
        check_lake_configuration(&self.sdk, &self.root, &self.binding.source_roots, true)?;
        let manifest = self.root.join("lake-manifest.json");
        reject_links(&manifest)?;
        if !manifest.try_exists()? {
            ensure!(
                self.sdk.inner.descriptor.finite_lake.is_none(),
                "Finite SDK requires an existing empty Lake manifest"
            );
            return Ok(None);
        }
        let manifest = read_small(&manifest, MAX_MODULES_SIZE)?;
        check_dependency_free_manifest(&manifest)?;
        if self.sdk.inner.descriptor.finite_lake.is_none() {
            return Ok(None);
        }
        let config = read_small(&self.root.join("lakefile.lean"), MAX_MODULES_SIZE)?;
        Ok(Some((String::from_utf8(config)?, String::from_utf8(manifest)?)))
    }

    pub(crate) fn finite_command(&self) -> Result<Option<Command>> {
        self.admit()?;
        let Some(helper) = &self.sdk.inner.descriptor.finite_lake else { return Ok(None) };
        self.sdk.check_finite_integrity()?;
        check_lake_configuration(&self.sdk, &self.root, &self.binding.source_roots, true)?;
        check_dependency_free_manifest(&read_small(
            &self.root.join("lake-manifest.json"),
            MAX_MODULES_SIZE,
        )?)?;
        let mut command = self.command("anneal-finite-lake")?;
        ensure!(
            helper.path == Path::new("bin/anneal-finite-lake"),
            "Unsupported finite helper path"
        );
        command.arg(&self.root);
        Ok(Some(command))
    }

    pub(crate) fn validate_preparation_request(
        &self,
        targets: &[String],
        setup: Option<(&str, &Path)>,
    ) -> Result<()> {
        for target in targets {
            ensure!(valid_build_target(target), "Unsupported Lake build target: {target}");
        }
        if let Some((file_name, path)) = setup {
            self.local_source(path)?;
            ensure!(!file_name.is_empty() && !file_name.contains('\0'), "Invalid setup filename");
        }
        Ok(())
    }

    pub fn lean_command(&self, operation: LeanOperation<'_>) -> Result<Command> {
        let mut command = if matches!(
            operation,
            LeanOperation::Version | LeanOperation::PrintPrefix | LeanOperation::GitHash
        ) {
            self.command_with_private("lean", PrivateAdmission::SavedObservation)?
        } else {
            self.command("lean")?
        };
        command.arg(format!("--root={}", self.root.display()));
        for plugin in &self.sdk.inner.plugins {
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

    // Canonicalization does not necessarily normalize filesystem-equivalent
    // spellings. Find the bound directory among the named path's ancestors by
    // identity, retaining the suffix for link and private-alias validation.
    fn local_source_relative(&self, file: &Path) -> Result<Option<PathBuf>> {
        let file = if file.is_absolute() { file.to_path_buf() } else { self.root.join(file) };
        let root_identity = physical_directory_identity(&fs::metadata(&self.root)?)?;
        for ancestor in file.ancestors() {
            let metadata = match fs::metadata(ancestor) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                Err(error) => return Err(error.into()),
            };
            if metadata.is_dir() && physical_directory_identity(&metadata)? == root_identity {
                return Ok(Some(file.strip_prefix(ancestor)?.to_path_buf()));
            }
        }
        Ok(None)
    }

    fn local_source(&self, file: &Path) -> Result<PathBuf> {
        ensure!(
            !file.components().any(|c| matches!(c, Component::ParentDir)),
            "Lean source path cannot traverse parent directories"
        );
        let file = if file.is_absolute() { file.to_path_buf() } else { self.root.join(file) };
        // Check the original name before any physical resolution can erase a
        // symlink. SDK source providers use their separate immutable route.
        reject_links(&file)?;
        let relative =
            self.local_source_relative(&file)?.context("Lean source is outside its workspace")?;
        let file = self.root.join(&relative);
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
            relative.components().all(|part| {
                !matches!(part, Component::Normal(name) if reserved_private_name(name, folds_case))
            }),
            "Source must not come from ignored private output/cache trees"
        );
        let parent = relative.parent().context("Local source has no parent")?.to_path_buf();
        reject_existing_source_root_aliases(&self.root, &[parent])?;
        Ok(file)
    }

    fn command(&self, tool: &str) -> Result<Command> {
        self.command_with_private(tool, PrivateAdmission::Complete)
    }

    fn command_with_private(&self, tool: &str, private: PrivateAdmission) -> Result<Command> {
        self.admit_with_private_contents(private)?;
        let mut command = Command::new(self.sdk.inner.root.join("bin").join(tool));
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
        command.env("LEAN", self.sdk.inner.root.join("bin/lean"));
        command.env("LAKE", self.sdk.inner.root.join("bin/lake"));
        command.env("LEAN_SYSROOT", &self.sdk.inner.root);
        command.env("LAKE_HOME", &self.sdk.inner.root);
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

fn hex_digest(digest: [u8; 32]) -> String {
    digest.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn prune_undeclared_outputs(root: &Path) -> Result<()> {
    let configuration: LakeConfiguration =
        serde_json::from_slice(&read_small(&root.join(LAKE_CONFIGURATION), MAX_MODULES_SIZE)?)?;
    let folds_case = filesystem_folds_ascii_case(&root.join(OUTPUT_OWNER))?;
    let provider_key = |module: String| {
        if folds_case { module.to_ascii_lowercase() } else { module }
    };
    let mut providers = BTreeSet::new();
    for library in configuration.libraries {
        for module in library.modules {
            let source = root
                .join(&library.source_root)
                .join(module.replace('.', "/"))
                .with_extension("lean");
            reject_links(&source)?;
            match fs::metadata(&source) {
                Ok(metadata) => {
                    ensure!(metadata.is_file(), "Local module provider is not a regular file");
                    providers.insert(provider_key(module));
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.into()),
            }
        }
    }
    for relative_root in [".lake/build/lib/lean", ".lake/build/ir"] {
        let output_root = root.join(relative_root);
        if !output_root.try_exists()? {
            continue;
        }
        for entry in walkdir::WalkDir::new(&output_root).follow_links(false) {
            let entry = entry?;
            ensure!(
                entry.file_type().is_dir() || entry.file_type().is_file(),
                "Private output contains a link or special file"
            );
            if !entry.file_type().is_file() {
                continue;
            }
            let relative = entry.path().strip_prefix(&output_root)?;
            let leaf =
                relative.file_name().and_then(|s| s.to_str()).context("Non-UTF8 output path")?;
            let Some((module_leaf, _)) = leaf.split_once('.') else { continue };
            let module = relative
                .with_file_name(module_leaf)
                .iter()
                .map(|part| part.to_str().context("Non-UTF8 output path"))
                .collect::<Result<Vec<_>>>()?
                .join(".");
            if !providers.contains(&provider_key(module)) {
                fs::remove_file(entry.path())?;
            }
        }
    }
    Ok(())
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
    let mut paths = vec![sdk.inner.root.join("bin")];
    paths.extend(["/usr/bin", "/bin", "/usr/sbin", "/sbin"].map(PathBuf::from));
    let mut imports = Vec::new();
    let mut sources = Vec::new();
    if let Some((root, source_roots)) = workspace {
        imports.push(root.join(".lake/build/lib/lean"));
        sources.extend(source_roots.iter().map(|source| root.join(source)));
    }
    imports.extend(sdk.inner.imports.iter().cloned());
    sources.extend(sdk.inner.sources.iter().cloned());
    Ok(CommandSearchPaths {
        path: std::env::join_paths(paths).context("SDK PATH cannot represent its input paths")?,
        imports: std::env::join_paths(imports)
            .context("LEAN_PATH cannot represent its input paths")?,
        sources: std::env::join_paths(sources)
            .context("LEAN_SRC_PATH cannot represent its input paths")?,
        loaders: std::env::join_paths(&sdk.inner.loaders)
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
    let mut auxiliary_hasher = Sha256::new();
    let mut identities = Vec::new();
    let mut directories = Vec::new();
    let mut root_state = None;
    for path in &inputs.directories {
        reject_links(path)?;
        let metadata = saved_input_io(fs::metadata(path), true)?;
        let before = directory_modification_identity(&metadata)?;
        let relative = path.strip_prefix(root)?.as_os_str().as_encoded_bytes();
        // Persistent provenance tracks observable nonprivate membership/type,
        // not inode or timestamp churn across the owner's regeneration.
        auxiliary_hasher.update(b"directory");
        auxiliary_hasher.update((relative.len() as u64).to_le_bytes());
        auxiliary_hasher.update(relative);
        if path == root {
            root_state = Some((before.clone(), physical_directory_identity(&metadata)?));
        } else {
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
        let metadata = saved_input_io(file.metadata(), true)?;
        let before = modification_identity(&metadata)?;
        hasher.update((before.len() as u64).to_le_bytes());
        hasher.update(&before);
        // Lean providers can also be read as data without an import edge.
        // Every permitted file's contents therefore participate in provenance.
        auxiliary_hasher.update(b"file");
        auxiliary_hasher.update((relative.len() as u64).to_le_bytes());
        auxiliary_hasher.update(relative);
        auxiliary_hasher.update(metadata.len().to_le_bytes());
        let mut buffer = [0u8; 64 * 1024];
        loop {
            let count = saved_input_io(file.read(&mut buffer), true)?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
            auxiliary_hasher.update(&buffer[..count]);
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
        auxiliary_stamp: auxiliary_hasher.finalize().into(),
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
    ensure!(
        fs::metadata(path)
            .with_context(|| format!("Missing or unreadable {}", path.display()))?
            .is_file(),
        "Bounded input is not a regular file: {}",
        path.display()
    );
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", any(target_arch = "aarch64", target_arch = "x86_64"))
    ))]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        // A regular input replaced by a FIFO between inspection and open must
        // also fail promptly. Verify the opened descriptor before reading it.
        options.custom_flags(NONBLOCK_OPEN_FLAG);
    }
    let file =
        options.open(path).with_context(|| format!("Missing or unreadable {}", path.display()))?;
    ensure!(file.metadata()?.is_file(), "Bounded input is not a regular file: {}", path.display());
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes)?;
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

fn write_new_bytes(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        // Only fresh binding and output-owner records use this helper.
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    file.write_all(bytes)?;
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

fn check_finite_helper(root: &Path, installation: &Path, helper: &FiniteLake) -> Result<()> {
    ensure!(
        helper.protocol == 1
            && helper.path == Path::new("bin/anneal-finite-lake")
            && is_sha256(&helper.sha256),
        "Invalid finite Lake helper descriptor"
    );
    let path = root.join(&helper.path);
    check_launcher(&path, installation)?;
    // Stream the executable; admission does not allocate its complete body.
    let mut file = fs::File::open(&path)?;
    let mut digest = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    ensure!(
        hex_digest(digest.finalize().into()) == helper.sha256,
        "Finite Lake helper changed after admission"
    );
    check_launcher(&path, installation)?;
    Ok(())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LakeManifest {
    version: String,
    packages_dir: String,
    packages: Vec<serde_json::Value>,
    name: String,
    lake_dir: String,
    // Stock Lake writes this optional field; the generated package uses its
    // default false value. An absent field retains the same Lake semantics.
    #[serde(default)]
    fixed_toolchain: bool,
}

fn check_dependency_free_manifest(bytes: &[u8]) -> Result<()> {
    let manifest: LakeManifest = serde_json::from_slice(bytes).context("Invalid Lake manifest")?;
    ensure!(manifest.version == "1.2.0", "Unsupported Lake manifest version");
    ensure!(manifest.packages.is_empty(), "Lake manifest must contain an empty packages array");
    ensure!(
        manifest.lake_dir == ".lake" && manifest.packages_dir == ".lake/packages",
        "Lake manifest paths differ from the private workspace layout"
    );
    ensure!(manifest.name == "anneal_verification", "Lake manifest package name changed");
    ensure!(!manifest.fixed_toolchain, "Lake manifest overrides the generated toolchain policy");
    Ok(())
}

fn open_workspace_lock(root: &Path, server: bool) -> Result<(fs::File, PathBuf)> {
    let root = new_physical_path(root)?;
    open_workspace_lock_path(workspace_lock_path(&root, server)?, true)
}

/// A finite operation holds the main writer while this shared lease runs.
/// Only successful completion waits for its separate exclusive probe. On
/// error/cancellation, inherited holders continue fencing successor writers.
pub(crate) struct FiniteProducerLease {
    holder: Option<fs::File>,
    barrier: fs::File,
    path: PathBuf,
}

impl FiniteProducerLease {
    pub(crate) fn acquire(root: &Path) -> Result<Self> {
        let (holder, path) = open_native_producer_lease(root, false)?;
        fs2::FileExt::lock_shared(&holder)?;
        check_workspace_lock_entry(&holder, &path)?;
        // A new open is required: dup/try_clone would share the inherited
        // lock description and could upgrade it while descendants still run.
        let (barrier, barrier_path) = open_native_producer_lease(root, false)?;
        ensure!(path == barrier_path, "Finite producer lease path changed");
        check_workspace_lock_entry(&holder, &path)?;
        check_workspace_lock_entry(&barrier, &path)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            let held = holder.metadata()?;
            let probe = barrier.metadata()?;
            ensure!(
                held.dev() == probe.dev() && held.ino() == probe.ino(),
                "Finite producer lease changed between opens"
            );
        }
        Ok(Self { holder: Some(holder), barrier, path })
    }

    pub(crate) fn holder(&self) -> &fs::File {
        self.holder.as_ref().expect("Finite producer parent holder already released")
    }

    pub(crate) fn release_parent(&mut self) {
        // Drop, never explicitly unlock: child descriptors share this holder.
        self.holder.take();
    }

    pub(crate) fn poll_released(&self) -> Result<bool> {
        ensure!(self.holder.is_none(), "Finite producer parent holder is still retained");
        check_workspace_lock_entry(&self.barrier, &self.path)?;
        let released = match fs2::FileExt::try_lock_exclusive(&self.barrier) {
            Ok(()) => true,
            Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => false,
            Err(error) => return Err(error.into()),
        };
        // Replacing the protected pathname must not hide an older holder.
        check_workspace_lock_entry(&self.barrier, &self.path)?;
        Ok(released)
    }
}

pub(crate) fn open_native_producer_lease(root: &Path, create: bool) -> Result<(fs::File, PathBuf)> {
    let root = if create { new_physical_path(root)? } else { physical_workspace_path(root)? };
    let mut leaf = root.file_name().context("Workspace has no leaf")?.to_os_string();
    // Distinct from both `.lock` writer names and `.server-lease` coordinator
    // names, including when another workspace leaf ends in either suffix.
    leaf.push(".producer-lease");
    open_workspace_lock_path(root.with_file_name(leaf), create).context(
        "Native startup requires an existing protected producer lease; regenerate or adopt the workspace under its normal writer first",
    )
}

// The caller retains the exclusive main fence throughout this barrier. A new
// producer can start only under that same fence, so the exclusive producer
// handle may be released before returning the main writer to its owner.
fn wait_native_producers(root: &Path) -> Result<()> {
    let (file, path) = open_native_producer_lease(root, true)?;
    fs2::FileExt::lock_exclusive(&file)?;
    check_workspace_lock_entry(&file, &path)
}

fn try_native_producer_barrier(root: &Path, create: bool) -> Result<bool> {
    let (file, path) = open_native_producer_lease(root, create)?;
    match fs2::FileExt::try_lock_exclusive(&file) {
        Ok(()) => {
            check_workspace_lock_entry(&file, &path)?;
            Ok(true)
        }
        Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => Ok(false),
        Err(error) => Err(error.into()),
    }
}

fn open_workspace_lock_path(path: PathBuf, create: bool) -> Result<(fs::File, PathBuf)> {
    reject_links(&path)?;
    let mut options = OpenOptions::new();
    options.read(true).write(true).create(create).truncate(false);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.mode(0o600);
    }
    #[cfg(any(
        target_os = "macos",
        all(target_os = "linux", any(target_arch = "aarch64", target_arch = "x86_64"))
    ))]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.custom_flags(NONBLOCK_OPEN_FLAG | NOFOLLOW_OPEN_FLAG);
    }
    let file = options.open(&path)?;
    check_workspace_lock_entry(&file, &path)?;
    Ok((file, path))
}

// The caller supplies a physical parent. Computing a sibling name must not
// perform the name-policy probes needed only by lock-creating producers.
pub(crate) fn workspace_lock_path(root: &Path, server: bool) -> Result<PathBuf> {
    let mut leaf = root.file_name().context("Workspace has no leaf")?.to_os_string();
    // Writer filenames end in `.lock`; server leases never do. Appending
    // `.server.lock` would alias the writer lock of a `foo.server` sibling.
    leaf.push(if server { ".server-lease" } else { ".lock" });
    Ok(root.with_file_name(leaf))
}

// The stable sibling lock is never truncated or replaced. A legacy empty
// lock means zero; every writer stores a positive checked sequence and its
// complement, then syncs before returning any mutation capability. A failed
// acquisition can conservatively change history without changing outputs.
// Interrupted prefix writes are either the old/new valid witness or malformed;
// no writer effects precede the complete synced record. This is cooperative
// synchronization, not authentication or a guarantee about older binaries.
pub(crate) fn read_writer_witness(file: &fs::File) -> Result<u64> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt as _;
        match file.metadata()?.len() {
            0 => Ok(0),
            16 => {
                let mut bytes = [0; 16];
                file.read_exact_at(&mut bytes, 0).context("Reading workspace writer witness")?;
                ensure!(file.metadata()?.len() == 16, "Workspace writer witness length changed");
                let sequence = u64::from_le_bytes(bytes[..8].try_into().unwrap());
                let complement = u64::from_le_bytes(bytes[8..].try_into().unwrap());
                ensure!(sequence == !complement, "Malformed workspace writer witness");
                Ok(sequence)
            }
            _ => bail!("Malformed workspace writer witness length"),
        }
    }
    #[cfg(not(unix))]
    {
        let _ = file;
        bail!("Unsupported positional workspace writer witness")
    }
}

pub(crate) fn advance_writer_witness(file: &fs::File) -> Result<u64> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt as _;
        let sequence = read_writer_witness(file)?
            .checked_add(1)
            .context("Workspace writer witness exhausted")?;
        let mut bytes = [0; 16];
        bytes[..8].copy_from_slice(&sequence.to_le_bytes());
        bytes[8..].copy_from_slice(&(!sequence).to_le_bytes());
        file.write_all_at(&bytes, 0).context("Writing workspace writer witness")?;
        file.sync_all().context("Syncing workspace writer witness before writer effects")?;
        ensure!(read_writer_witness(file)? == sequence, "Workspace writer witness changed");
        Ok(sequence)
    }
    #[cfg(not(unix))]
    {
        let _ = file;
        bail!("Unsupported positional workspace writer witness")
    }
}

fn check_workspace_lock_entry(file: &fs::File, path: &Path) -> Result<()> {
    let opened = file.metadata()?;
    let entry = fs::symlink_metadata(path)?;
    ensure!(opened.is_file() && entry.is_file(), "Workspace lock is not a regular file");
    #[cfg(unix)]
    {
        let owner = workspace_lock_owner();
        check_workspace_lock_metadata(&opened, owner)?;
        check_workspace_lock_metadata(&entry, owner)?;
    }
    ensure!(
        physical_input_identity(&opened)? == physical_input_identity(&entry)?,
        "Workspace lock entry changed during acquisition"
    );
    Ok(())
}

/// Path-based commands require a namespace that another local UID cannot
/// replace. Check from the filesystem root down, including grandparents:
/// after a parent is admitted, its next entry must also have a trusted owner.
/// The invoking UID and root remain trusted through later command spawning;
/// privileged mounts and changes by those owners are not an OS sandbox claim.
// Private-root admission excludes traversal through this namespace. It does
// not revoke preexisting descriptors or prevent writes through outside hardlink
// aliases; the trusted invoking UID/root and cooperative-writer premises remain.
fn check_workspace_namespace(root: &Path) -> Result<()> {
    check_workspace_namespace_chain(root, true)
}

// The caller resolves this prospective workspace path physically first. Check
// only its existing parent chain, without reading workspace/config/private data.
// A root-owned parent is an ancestor, not an invoking-UID-owned workspace root.
fn check_workspace_parent_namespace(root: &Path) -> Result<()> {
    check_workspace_namespace_chain(root.parent().context("Workspace has no parent")?, false)
}

fn check_workspace_namespace_chain(root: &Path, workspace_root: bool) -> Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;

        ensure!(root.is_absolute(), "Workspace namespace must be physical and absolute");
        let invoking_uid = workspace_lock_owner();
        let ancestors = root.ancestors().collect::<Vec<_>>();
        for directory in ancestors.into_iter().rev() {
            let metadata = fs::symlink_metadata(directory).with_context(|| {
                format!("Cannot inspect workspace namespace {}", directory.display())
            })?;
            ensure!(metadata.is_dir(), "Workspace namespace contains a link or non-directory");
            check_workspace_namespace_identity(
                metadata.uid(),
                metadata.mode(),
                invoking_uid,
                workspace_root && directory == root,
            )
            .with_context(|| format!("Unsupported workspace namespace {}", directory.display()))?;
            check_workspace_namespace_acl(directory, workspace_root && directory == root)?;
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = (root, workspace_root);
        bail!("Unsupported workspace namespace permission admission")
    }
}

#[cfg(unix)]
fn check_workspace_namespace_identity(
    owner: u32,
    mode: u32,
    invoking_uid: u32,
    workspace_root: bool,
) -> Result<()> {
    if workspace_root {
        ensure!(owner == invoking_uid, "Workspace root is owned by another user");
        // Descendant modes may be ordinary source/output modes. Keep their
        // namespace private rather than accepting a traversable workspace root.
        ensure!(mode & 0o077 == 0, "Workspace root permits group or other access");
    } else {
        ensure!(
            owner == invoking_uid || owner == 0,
            "Workspace ancestor is owned by an untrusted user"
        );
        ensure!(
            mode & 0o022 == 0 || mode & 0o1000 != 0,
            "Writable workspace ancestor must have the sticky bit"
        );
    }
    Ok(())
}

fn check_workspace_namespace_acl(directory: &Path, workspace_root: bool) -> Result<()> {
    #[cfg(target_os = "macos")]
    {
        darwin_namespace_acl::check(directory, workspace_root)
    }
    #[cfg(target_os = "linux")]
    {
        // Linux POSIX ACL named-user/group write rights are bounded by the
        // group-class mask represented in mode bits. This does not admit
        // additional non-POSIX ACL or privileged namespace semantics.
        let _ = (directory, workspace_root);
        Ok(())
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (directory, workspace_root);
        bail!("Unsupported workspace namespace ACL admission")
    }
}

#[cfg(target_os = "macos")]
mod darwin_namespace_acl {
    use std::{
        ffi::{CString, c_char, c_void},
        os::unix::ffi::OsStrExt as _,
    };

    use super::*;

    // Darwin sys/acl.h and acl_get_entry(3), not the Linux POSIX return ABI.
    #[cfg(test)]
    const TYPE_EXTENDED: i32 = 0x100;
    const ALLOW: i32 = 1;
    const DENY: i32 = 2;
    const MAX_ENTRIES: i32 = 128;
    const EINVAL: i32 = 22;
    const READ_ONLY: u64 = (1 << 1) | (1 << 3) | (1 << 7) | (1 << 9) | (1 << 11) | (1 << 20);

    unsafe extern "C" {
        fn filesec_init() -> *mut c_void;
        fn filesec_free(filesec: *mut c_void);
        #[cfg_attr(target_arch = "x86_64", link_name = "lstatx_np$INODE64")]
        fn lstatx_np(path: *const c_char, stat: *mut libc::stat, filesec: *mut c_void) -> i32;
        fn filesec_query_property(filesec: *mut c_void, property: i32, present: *mut i32) -> i32;
        fn filesec_get_property(filesec: *mut c_void, property: i32, value: *mut c_void) -> i32;
        fn acl_valid(acl: *mut c_void) -> i32;
        fn acl_get_entry(acl: *mut c_void, index: i32, entry: *mut *mut c_void) -> i32;
        fn acl_get_tag_type(entry: *mut c_void, tag: *mut i32) -> i32;
        fn acl_get_permset_mask_np(entry: *mut c_void, mask: *mut u64) -> i32;
        fn acl_free(acl: *mut c_void) -> i32;
    }

    const FILESEC_ACL: i32 = 5;
    // Public sys/fcntl.h sentinel; it is not allocated ACL storage.
    const REMOVE_ACL: *mut c_void = 1usize as *mut c_void;

    struct OwnedFilesec(*mut c_void);
    impl Drop for OwnedFilesec {
        fn drop(&mut self) {
            // SAFETY: owned non-null storage from filesec_init, freed once.
            unsafe { filesec_free(self.0) };
        }
    }

    struct OwnedAcl(*mut c_void);
    impl Drop for OwnedAcl {
        fn drop(&mut self) {
            // SAFETY: owned non-null storage from the native ACL API, freed once.
            unsafe {
                acl_free(self.0);
            }
        }
    }

    fn check_entry(tag: i32, mask: u64, workspace_root: bool) -> Result<()> {
        match tag {
            DENY => Ok(()),
            ALLOW => {
                // Reject every mutating grant, even to a trusted principal,
                // without relying on deny ordering, UUID mapping, or inheritance.
                // The allowlist also rejects any future unrecognized right.
                ensure!(mask & !READ_ONLY == 0, "Workspace namespace ACL grants mutating access");
                // ACL_SEARCH/ACL_EXECUTE can bypass mode-bit traversal
                // exclusion. Ancestors need search; the private root must not
                // grant it, even to a trusted principal under this policy.
                ensure!(
                    !workspace_root || mask & (1 << 3) == 0,
                    "Workspace root ACL grants traversal access"
                );
                Ok(())
            }
            _ => bail!("Unsupported workspace namespace ACL entry type"),
        }
    }

    fn read_acl(directory: &Path) -> Result<Option<OwnedAcl>> {
        let path = CString::new(directory.as_os_str().as_bytes())?;
        // SAFETY: filesec_init has no arguments and returns separately owned
        // storage. No property is read before lstatx_np successfully fills it.
        let raw = unsafe { filesec_init() };
        ensure!(
            !raw.is_null(),
            "Cannot allocate workspace namespace security metadata: {}",
            std::io::Error::last_os_error()
        );
        let filesec = OwnedFilesec(raw);
        let mut metadata = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: NUL-terminated path, typed writable Darwin stat storage, and
        // live filesec. Intel uses the header-defined 64-bit inode symbol.
        ensure!(
            unsafe { lstatx_np(path.as_ptr(), metadata.as_mut_ptr(), filesec.0) } == 0,
            "Cannot stat workspace namespace {}: {}",
            directory.display(),
            std::io::Error::last_os_error()
        );
        let mut present = 0;
        // SAFETY: filesec was successfully populated and present is writable.
        ensure!(
            unsafe { filesec_query_property(filesec.0, FILESEC_ACL, &mut present) } == 0,
            "Cannot query workspace namespace ACL {}: {}",
            directory.display(),
            std::io::Error::last_os_error()
        );
        if present == 0 {
            // Successful native property query establishes absence. In
            // particular, no errno from a failed getter is treated as absence.
            return Ok(None);
        }
        let mut raw_acl: *mut c_void = std::ptr::null_mut();
        // SAFETY: this populated property returns independent allocated ACL
        // storage through a writable acl_t output pointer, not an opaque buffer.
        let result = unsafe {
            filesec_get_property(filesec.0, FILESEC_ACL, (&mut raw_acl as *mut *mut c_void).cast())
        };
        let error = std::io::Error::last_os_error();
        // Own any real returned storage even on an unexpected getter failure;
        // neither null nor the public removal sentinel is allocated storage.
        let acl = (!raw_acl.is_null() && raw_acl != REMOVE_ACL).then(|| OwnedAcl(raw_acl));
        ensure!(
            result == 0,
            "Cannot read workspace namespace ACL {}: {error}",
            directory.display()
        );
        Ok(Some(acl.context("Invalid workspace namespace ACL storage")?))
    }

    pub(super) fn check(directory: &Path, workspace_root: bool) -> Result<()> {
        let Some(acl) = read_acl(directory)? else { return Ok(()) };
        // SAFETY: this ACL is live, privately owned native storage.
        ensure!(unsafe { acl_valid(acl.0) } == 0, "Invalid workspace namespace ACL");
        for index in 0..=MAX_ENTRIES {
            let mut entry = std::ptr::null_mut();
            // SAFETY: valid ACL and writable pointer to an entry descriptor.
            let result = unsafe { acl_get_entry(acl.0, index, &mut entry) };
            if result != 0 {
                let error = std::io::Error::last_os_error();
                // On a validated, unmodified ACL, an indexed EINVAL means this
                // index is out of range, including index 0 for an empty ACL.
                // Darwin returns 0 for an entry and -1 for end/error.
                ensure!(
                    result == -1 && error.raw_os_error() == Some(EINVAL),
                    "Cannot enumerate workspace namespace ACL: {error}"
                );
                return Ok(());
            }
            ensure!(index < MAX_ENTRIES, "Unsupported workspace namespace ACL size");
            ensure!(!entry.is_null(), "Invalid workspace namespace ACL entry");
            let mut tag = 0;
            let mut mask = 0;
            // SAFETY: entry belongs to the live ACL; output pointers are valid.
            ensure!(
                unsafe { acl_get_tag_type(entry, &mut tag) } == 0,
                "Cannot read workspace namespace ACL entry type"
            );
            ensure!(
                unsafe { acl_get_permset_mask_np(entry, &mut mask) } == 0,
                "Cannot read workspace namespace ACL permissions"
            );
            check_entry(tag, mask, workspace_root)?;
        }
        unreachable!("ACL enumeration either ends or rejects an excessive size")
    }

    #[cfg(test)]
    pub(super) fn install_test_entry(directory: &Path, tag: i32, mask: u64) {
        unsafe extern "C" {
            fn acl_init(count: i32) -> *mut c_void;
            fn acl_create_entry(acl: *mut *mut c_void, entry: *mut *mut c_void) -> i32;
            fn acl_set_tag_type(entry: *mut c_void, tag: i32) -> i32;
            fn acl_set_qualifier(entry: *mut c_void, qualifier: *const c_void) -> i32;
            fn acl_set_permset_mask_np(entry: *mut c_void, mask: u64) -> i32;
            fn acl_set_link_np(path: *const c_char, acl_type: i32, acl: *mut c_void) -> i32;
            fn mbr_uid_to_uuid(uid: u32, uuid: *mut u8) -> i32;
        }
        let path = CString::new(directory.as_os_str().as_bytes()).unwrap();
        // Only callers' fresh private fixtures are changed. No process is
        // spawned and no other UID, shared directory, or namespace is modified.
        // SAFETY: header-defined scalar ABI and initialized output/storage
        // pointers; the qualifier is the invoking account's 128-bit UUID.
        unsafe {
            let mut acl = OwnedAcl(acl_init(1));
            assert!(!acl.0.is_null());
            if mask != 0 {
                let mut entry = std::ptr::null_mut();
                assert_eq!(acl_create_entry(&mut acl.0, &mut entry), 0);
                assert_eq!(acl_set_tag_type(entry, tag), 0);
                let mut uuid = [0u8; 16];
                assert_eq!(mbr_uid_to_uuid(workspace_lock_owner(), uuid.as_mut_ptr()), 0);
                assert_eq!(acl_set_qualifier(entry, uuid.as_ptr().cast()), 0);
                assert_eq!(acl_set_permset_mask_np(entry, mask), 0);
            }
            assert_eq!(acl_valid(acl.0), 0);
            assert_eq!(acl_set_link_np(path.as_ptr(), TYPE_EXTENDED, acl.0), 0);
        }
    }

    #[cfg(test)]
    #[test]
    fn filesec_distinguishes_absent_acl_from_missing_directory() {
        let fixture = tempfile::tempdir().unwrap();
        let directory = fixture.path().join("no-acl");
        fs::create_dir(&directory).unwrap();
        // A fresh private directory has no installed ACL. Require the native
        // successful query's absent branch before admitting it; no ACL getter
        // ENOENT or other operational error can satisfy this positive control.
        assert!(read_acl(&directory).unwrap().is_none());
        check(&directory, false).unwrap();
        let missing = directory.join("missing");
        assert!(!missing.exists());
        let error = check(&missing, false).unwrap_err();
        assert!(error.to_string().contains("Cannot stat workspace namespace"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
    }

    #[cfg(test)]
    #[test]
    fn acl_permissions_reject_mutating_and_unknown_allow_rights() {
        check_entry(ALLOW, READ_ONLY, false).unwrap();
        check_entry(ALLOW, READ_ONLY & !(1 << 3), true).unwrap();
        assert!(check_entry(ALLOW, 1 << 3, true).is_err());
        check_entry(DENY, 1 << 3, true).unwrap();
        for bit in [2, 4, 5, 6, 8, 10, 12, 13, 63] {
            for workspace_root in [false, true] {
                assert!(check_entry(ALLOW, READ_ONLY | (1 << bit), workspace_root).is_err());
                check_entry(DENY, 1 << bit, workspace_root).unwrap();
            }
        }
        assert!(check_entry(0, READ_ONLY, false).is_err());
    }
}

#[cfg(unix)]
fn workspace_lock_owner() -> u32 {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    // SAFETY: geteuid has no arguments or memory effects and returns this UID.
    unsafe { geteuid() }
}

#[cfg(unix)]
fn check_workspace_lock_metadata(metadata: &fs::Metadata, owner: u32) -> Result<()> {
    use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};
    ensure!(metadata.uid() == owner, "Workspace lock is owned by another user");
    ensure!(
        metadata.permissions().mode() & 0o077 == 0,
        "Workspace lock must exclude group and other access"
    );
    Ok(())
}

fn new_physical_path(path: &Path) -> Result<PathBuf> {
    let path = physical_workspace_path(path)?;
    let reference = match fs::symlink_metadata(&path) {
        Ok(metadata) if metadata.is_dir() => Some(path.as_path()),
        Ok(_) => None,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(error.into()),
    };
    reject_workspace_lock_name(&path, reference)?;
    Ok(path)
}

/// Resolve a prospective or replaceable workspace path by canonicalizing its
/// parent and appending the final component. The leaf may be missing or name
/// the old object being replaced; do not resolve it as the stable object.
// Resolve without the optional name-policy tempfile probe, so stage ancestry
// can be rejected before even a temporary entry touches the live workspace.
fn physical_workspace_path(path: &Path) -> Result<PathBuf> {
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
    Ok(path)
}

fn reject_stage_ancestry(stage: &Path, final_root: &Path) -> Result<()> {
    let final_root = match fs::symlink_metadata(final_root) {
        Ok(metadata) => physical_directory_identity(&metadata)?,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    // Directory identities also cover case/normalization aliases whose path
    // spellings need not compare equal after lexical or symlink resolution.
    for ancestor in stage.ancestors() {
        let metadata = match fs::symlink_metadata(ancestor) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error.into()),
        };
        if metadata.is_dir() {
            ensure!(
                physical_directory_identity(&metadata)? != final_root,
                "Existing workspace stage must be outside the live workspace"
            );
        }
    }
    Ok(())
}

fn reject_workspace_lock_name(root: &Path, reference: Option<&Path>) -> Result<()> {
    let leaf = root
        .file_name()
        .and_then(|leaf| leaf.to_str())
        .context("Lean workspace name must be UTF-8")?;
    let reserved = |name: &str| {
        [".lock", ".server-lease", ".producer-lease"].iter().any(|suffix| name.ends_with(suffix))
    };
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
    if !leaf.is_ascii() {
        // Compare complete candidate names, so Unicode normalization/case
        // equivalence comes from this filesystem rather than a string fold.
        // Existing admission stays read-only, including read-only parents.
        let probe = if reference.is_none() {
            let mut builder = tempfile::Builder::new();
            builder.prefix(".anneal-lock-names-");
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt as _;
                builder.permissions(fs::Permissions::from_mode(0o700));
            }
            Some(builder.tempdir_in(root.parent().context("Workspace has no parent")?)?)
        } else {
            None
        };
        let candidate =
            probe.as_ref().map_or_else(|| root.to_path_buf(), |probe| probe.path().join(leaf));
        if probe.is_some() {
            fs::create_dir(&candidate)?;
        }
        let identity = physical_directory_identity(&fs::symlink_metadata(&candidate)?)?;
        for (index, _) in leaf.char_indices() {
            for suffix in [".lock", ".server-lease", ".producer-lease"] {
                let alternate = candidate.with_file_name(format!("{}{suffix}", &leaf[..index]));
                if probe.is_some() {
                    match fs::create_dir_all(&alternate) {
                        Ok(()) => {}
                        Err(error) if error.kind() == std::io::ErrorKind::InvalidFilename => {
                            continue;
                        }
                        Err(error) => return Err(error.into()),
                    }
                }
                let metadata = match fs::symlink_metadata(alternate) {
                    Ok(metadata) => metadata,
                    // An impossible alternate cannot name a usable lock path.
                    Err(error)
                        if matches!(
                            error.kind(),
                            std::io::ErrorKind::NotFound | std::io::ErrorKind::InvalidFilename
                        ) =>
                    {
                        continue;
                    }
                    Err(error) => return Err(error.into()),
                };
                ensure!(
                    identity != physical_input_identity(&metadata)?,
                    "Workspace name uses a filesystem-equivalent reserved lock suffix"
                );
            }
        }
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

fn normalize_source_roots(roots: &[PathBuf], folds_case: bool) -> Result<Vec<PathBuf>> {
    validate_bound_source_roots(roots)?;
    let mut unique = BTreeSet::new();
    let mut normalized = Vec::with_capacity(roots.len());
    for root in roots {
        let mut path = PathBuf::new();
        for component in root.components() {
            if let Component::Normal(name) = component {
                path.push(name);
            }
        }
        if path.as_os_str().is_empty() {
            path.push(".");
        }
        let mut key = path.as_os_str().as_encoded_bytes().to_vec();
        if folds_case {
            key.make_ascii_lowercase();
        }
        ensure!(unique.insert(key), "Duplicate workspace source root or filesystem alias");
        normalized.push(path);
    }
    Ok(normalized)
}

fn filesystem_case_of_new_child(parent: &Path) -> Result<bool> {
    let probe = tempfile::Builder::new().prefix(".anneal-stage-policy-").tempfile_in(parent)?;
    filesystem_folds_ascii_case(probe.path())
}

fn ensure_stage_destination_policy(
    stage_device: u64,
    final_device: u64,
    stage_folds_case: bool,
    final_folds_case: bool,
) -> Result<()> {
    ensure!(
        stage_device == final_device,
        "Workspace stage and final destination must share one filesystem"
    );
    ensure!(
        stage_folds_case == final_folds_case,
        "Workspace stage and final destination have different case policies"
    );
    Ok(())
}

// A disposable private tree observes the destination filesystem's own name
// equivalence, including Unicode normalization, without rejecting otherwise
// supported non-ASCII or control-character source-root names.
fn reject_physical_source_root_aliases(parent: &Path, roots: &[PathBuf]) -> Result<()> {
    if roots.iter().all(|root| root.as_os_str().as_encoded_bytes().is_ascii()) {
        return Ok(());
    }
    let mut builder = tempfile::Builder::new();
    builder.prefix(".anneal-source-roots-");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    let probe = builder.tempdir_in(parent)?;
    let mut identities = BTreeSet::new();
    for root in roots {
        let path = probe.path().join(root);
        fs::create_dir_all(&path)?;
        let identity = physical_directory_identity(&fs::symlink_metadata(&path)?)?;
        ensure!(identities.insert(identity), "Duplicate workspace source root or filesystem alias");
    }
    // A Unicode component can also be an alias for a private name that the
    // ASCII-only saved-input exclusion would otherwise fail to recognize.
    // Observe each component beside all three reserved names on this same
    // filesystem, without creating any entry in a live workspace.
    let component_probe = builder.tempdir_in(parent)?;
    let mut private_identities = BTreeSet::new();
    for reserved in [".lake", PRIVATE_RUNTIME, ".git"] {
        let path = component_probe.path().join(reserved);
        fs::create_dir(&path)?;
        private_identities.insert(physical_directory_identity(&fs::symlink_metadata(path)?)?);
    }
    for root in roots {
        for component in root.components() {
            if let Component::Normal(name) = component {
                let path = component_probe.path().join(name);
                fs::create_dir_all(&path)?;
                let identity = physical_directory_identity(&fs::symlink_metadata(path)?)?;
                ensure!(
                    !private_identities.contains(&identity),
                    "Source root aliases a private output/cache name"
                );
            }
        }
    }
    Ok(())
}

// Admission also checks the directories that actually exist. This is read-only
// on a live workspace, where a disposable probe would disturb saved inputs.
fn reject_existing_source_root_aliases(root: &Path, roots: &[PathBuf]) -> Result<()> {
    if roots.iter().all(|source| source.as_os_str().as_encoded_bytes().is_ascii()) {
        return Ok(());
    }
    let mut identities = BTreeSet::new();
    for source in roots {
        let mut current = root.to_path_buf();
        for component in source.components() {
            let Component::Normal(name) = component else { continue };
            current.push(name);
            let metadata = match fs::symlink_metadata(&current) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
                Err(error) => return Err(error.into()),
            };
            let identity = physical_directory_identity(&metadata)?;
            for reserved in [".lake", PRIVATE_RUNTIME, ".git"] {
                let private = current.with_file_name(reserved);
                match fs::symlink_metadata(private) {
                    Ok(metadata) if metadata.is_dir() => ensure!(
                        identity != physical_directory_identity(&metadata)?,
                        "Source root aliases a private output/cache name"
                    ),
                    Ok(_) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => return Err(error.into()),
                }
            }
        }
        let metadata = match fs::symlink_metadata(root.join(source)) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error.into()),
        };
        let identity = physical_directory_identity(&metadata)?;
        ensure!(identities.insert(identity), "Duplicate workspace source root or filesystem alias");
    }
    Ok(())
}

fn validate_persisted_source_roots(roots: &[PathBuf], folds_case: bool) -> Result<()> {
    ensure!(
        normalize_source_roots(roots, folds_case)?.as_slice() == roots,
        "Workspace source roots are not normalized"
    );
    Ok(())
}

fn validate_bound_source_roots(roots: &[PathBuf]) -> Result<()> {
    ensure!(!roots.is_empty(), "Workspace needs source roots");
    let mut unique = BTreeSet::new();
    for root in roots {
        ensure!(
            !root.as_os_str().as_encoded_bytes().contains(&0),
            "Workspace source roots cannot contain NUL bytes"
        );
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
        ensure!(
            !library.name.strip_prefix("annealPlugin").is_some_and(|index| {
                !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit())
            }),
            "Lake library name is reserved for generated plugin targets"
        );
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

/// Lean RC2 supports JSON's ordinary escapes and four-digit Unicode escapes,
/// except for JSON's backspace/form-feed shortcuts. Rewrite only those escape
/// tokens, preserving literal backslash-b/f and all other valid characters.
fn lean_string_literal(value: &str) -> Result<String> {
    let quoted = serde_json::to_string(value)?;
    let mut literal = String::with_capacity(quoted.len());
    let mut chars = quoted.chars();
    while let Some(c) = chars.next() {
        literal.push(c);
        if c == '\\' {
            match chars.next().context("Incomplete JSON string escape")? {
                'b' => literal.push_str("u0008"),
                'f' => literal.push_str("u000c"),
                c => literal.push(c),
            }
        }
    }
    Ok(literal)
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
        let path = lean_string_literal(plugin.path.to_str().context("Plugin path is not UTF-8")?)?;
        let name = lean_string_literal(&plugin.name)?;
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
            lean_string_literal(library.source_root.to_str().context("Non-UTF8 source root")?)?;
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

fn check_workspace_private_layout(
    root: &Path,
    binding: &Binding,
    policy: &LocalFilesystemPolicy,
) -> Result<()> {
    for private in [".lake", PRIVATE_RUNTIME] {
        check_private_tree(&root.join(private), policy)?;
    }
    let owner: Binding = read_json(&root.join(OUTPUT_OWNER))?;
    ensure!(&owner == binding, "Private output ownership mismatch");
    for private in ["home", "cache", "config", "data", "tmp"] {
        ensure!(
            root.join(PRIVATE_RUNTIME).join(private).is_dir(),
            "Missing private runtime directory: {private}"
        );
    }
    Ok(())
}

// Do not call check_directory here: its case-policy probe also enumerates
// children, which may disappear during ordinary private producer activity.
// The namespace, devices, owner record and fixed runtime roots remain checked.
fn check_workspace_private_roots(
    root: &Path,
    binding: &Binding,
    policy: &LocalFilesystemPolicy,
) -> Result<()> {
    for relative in [
        ".lake",
        PRIVATE_RUNTIME,
        ".runtime/home",
        ".runtime/cache",
        ".runtime/config",
        ".runtime/data",
        ".runtime/tmp",
    ] {
        let path = root.join(relative);
        let metadata =
            fs::symlink_metadata(&path).context("Missing private output/runtime directory")?;
        ensure!(metadata.is_dir(), "Private output/runtime path is not a real directory");
        policy.check_device(&metadata)?;
    }
    let owner_path = root.join(OUTPUT_OWNER);
    let owner: Binding = read_json(&owner_path)?;
    policy.check_device(&fs::symlink_metadata(&owner_path)?)?;
    ensure!(&owner == binding, "Private output ownership mismatch");
    Ok(())
}

// read_dir preserves spelling even when fixed private-name lookups resolve a
// Unicode/case alias. Compare real directory identities at the root boundary;
// unrelated non-ASCII local data remains an ordinary saved input.
fn private_directory_identities(root: &Path, detect_changes: bool) -> Result<BTreeSet<Vec<u8>>> {
    let mut identities = BTreeSet::new();
    for private in [".lake", PRIVATE_RUNTIME, ".git"] {
        match fs::symlink_metadata(root.join(private)) {
            Ok(metadata) if metadata.is_dir() => {
                identities.insert(physical_directory_identity(&metadata)?);
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return saved_input_io(Err(error), detect_changes),
        }
    }
    Ok(identities)
}

fn check_private_tree(path: &Path, policy: &LocalFilesystemPolicy) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).context("Missing private output/runtime directory")?;
    ensure!(metadata.is_dir(), "Private output/runtime path is not a real directory");
    policy.check_directory(path, false)?;
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let kind = entry.file_type()?;
        ensure!(
            kind.is_dir() || kind.is_file(),
            "Private tree contains a link or special file: {}",
            entry.path().display()
        );
        policy.check_device(&fs::symlink_metadata(entry.path())?)?;
        if kind.is_dir() {
            check_private_tree(&entry.path(), policy)?;
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
    let policy = LocalFilesystemPolicy::at(workspace_root)?;
    policy.check_directory(path, true)?;
    let private_identities = if path == workspace_root {
        private_directory_identities(workspace_root, false)?
    } else {
        BTreeSet::new()
    };
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
        if path == workspace_root
            && kind.is_dir()
            && private_identities
                .contains(&physical_directory_identity(&fs::symlink_metadata(entry.path())?)?)
        {
            continue;
        }
        ensure!(!kind.is_symlink(), "Local source contains a symlink: {}", entry.path().display());
        ensure!(
            kind.is_dir() || kind.is_file(),
            "Local source contains a special file: {}",
            entry.path().display()
        );
        policy.check_device(&fs::symlink_metadata(entry.path())?)?;
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
                let parts = relative
                    .iter()
                    .map(|s| s.to_str().context("Non-UTF8 Lean module path"))
                    .collect::<Result<Vec<_>>>()?;
                let name = parts.join(".");
                // The generator's module grammar is ASCII; retaining other
                // ASCII direct-check filenames is safe, but a Unicode alias
                // would require the filesystem's Unicode normalization rules.
                ensure!(name.is_ascii(), "Unsupported non-ASCII local module path: {name}");
                // A flat Foo.Bar.lean is a saved input, not the provider for
                // the imported module Foo.Bar, which lives at Foo/Bar.lean.
                if !parts.iter().all(|part| valid_component(part)) {
                    continue;
                }
                ensure!(
                    !sdk.inner.modules.contains(&name),
                    "Local/SDK exact module collision: {name}"
                );
                let provider = if folds_case { name.to_ascii_lowercase() } else { name.clone() };
                ensure!(
                    !folds_case || !sdk.inner.folded_modules.contains(&provider),
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
/// or assuming that every macOS volume folds case. The workspace rejects local
/// cross-device mounts or observable per-directory policies that differ from its root.
pub(crate) fn filesystem_folds_ascii_case(reference: &Path) -> Result<bool> {
    filesystem_folds_ascii_case_with_change_detection(reference, false)
}

fn filesystem_folds_ascii_case_with_change_detection(
    reference: &Path,
    detect_changes: bool,
) -> Result<bool> {
    filesystem_case_probe(reference, detect_changes, |path| fs::metadata(path))
}

fn filesystem_case_probe(
    reference: &Path,
    detect_changes: bool,
    mut metadata: impl FnMut(&Path) -> std::io::Result<fs::Metadata>,
) -> Result<bool> {
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
    let original = saved_input_io(metadata(reference), detect_changes)?;
    let alternate_metadata = match metadata(&reference.with_file_name(&alternate)) {
        Ok(metadata) => Some(metadata),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(error.into()),
    };
    let same_input = match &alternate_metadata {
        Some(alternate) => {
            physical_input_identity(&original)? == physical_input_identity(alternate)?
        }
        None => false,
    };
    // Equal inode identities can also describe two distinct hard-linked entries
    // on a case-sensitive filesystem. Inspect exact directory names without
    // creating a probe in the saved source tree.
    let distinct_entries = if same_input {
        let mut original_entry = false;
        let mut alternate_entry = false;
        for entry in saved_input_io(
            fs::read_dir(reference.parent().context("Case probe has no parent")?),
            detect_changes,
        )? {
            let name = saved_input_io(entry, detect_changes)?.file_name();
            original_entry |= name == leaf;
            alternate_entry |= name == alternate.as_str();
            if original_entry && alternate_entry {
                break;
            }
        }
        original_entry && alternate_entry
    } else {
        false
    };
    let after = saved_input_io(metadata(reference), detect_changes)?;
    let probe_identity = |metadata: &fs::Metadata| {
        if metadata.is_dir() {
            directory_modification_identity(metadata)
        } else {
            modification_identity(metadata)
        }
    };
    if probe_identity(&original)? != probe_identity(&after)? {
        let message = format!("Local case probe changed while observing {}", reference.display());
        if detect_changes {
            return Err(SourceStampChanged::new(message).into());
        }
        bail!(message);
    }
    Ok(same_input && !distinct_entries)
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
        policy: &LocalFilesystemPolicy,
        detect_changes: bool,
        inputs: &mut SavedInputPaths,
    ) -> Result<()> {
        policy.check_directory(path, true)?;
        inputs.directories.insert(path.to_path_buf());
        let private_identities = if path == root {
            private_directory_identities(root, detect_changes)?
        } else {
            BTreeSet::new()
        };
        for entry in saved_input_io(fs::read_dir(path), detect_changes)? {
            let entry = saved_input_io(entry, detect_changes)?;
            let name = entry.file_name();
            if reserved_private_name(&name, policy.folds_case) {
                continue;
            }
            let kind = saved_input_io(entry.file_type(), detect_changes)?;
            if path == root
                && kind.is_dir()
                && private_identities.contains(&physical_directory_identity(&saved_input_io(
                    fs::symlink_metadata(entry.path()),
                    detect_changes,
                )?)?)
            {
                continue;
            }
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
            policy.check_device(&saved_input_io(fs::metadata(entry.path()), detect_changes)?)?;
            if kind.is_dir() {
                collect(&entry.path(), root, policy, detect_changes, inputs)?;
            } else if kind.is_file() {
                inputs.files.insert(entry.path());
            }
        }
        Ok(())
    }
    let mut inputs = SavedInputPaths { files: BTreeSet::new(), directories: BTreeSet::new() };
    let policy = LocalFilesystemPolicy::at(root)?;
    collect(root, root, &policy, detect_changes, &mut inputs)?;
    Ok(inputs)
}

/// One measured policy for the admitted writable tree. Cross-device mounts
/// and observable per-directory case-policy changes are explicitly unsupported.
/// Device IDs do not prevent same-device bind mounts or privileged namespace
/// changes. Cooperative writer leases and the trusted invoking UID/root remain
/// premises; these checks do not provide an operating-system sandbox.
/// An empty directory without an ASCII-letter entry has no observable provider
/// policy yet; its first named input is checked on the next admission.
struct LocalFilesystemPolicy {
    device: u64,
    folds_case: bool,
}

impl LocalFilesystemPolicy {
    fn at(root: &Path) -> Result<Self> {
        Ok(Self {
            device: filesystem_device(&fs::metadata(root)?)?,
            folds_case: filesystem_folds_ascii_case(&root.join(BINDING))?,
        })
    }

    fn check_device(&self, metadata: &fs::Metadata) -> Result<()> {
        ensure!(
            filesystem_device(metadata)? == self.device,
            "Unsupported local filesystem mount: inputs and private outputs must share the workspace device"
        );
        Ok(())
    }

    fn check_directory(&self, path: &Path, detect_changes: bool) -> Result<()> {
        let metadata = saved_input_io(fs::symlink_metadata(path), detect_changes)?;
        ensure!(metadata.is_dir(), "Local workspace path is not a real directory");
        self.check_device(&metadata)?;
        for entry in saved_input_io(fs::read_dir(path), detect_changes)? {
            let entry = saved_input_io(entry, detect_changes)?;
            let kind = saved_input_io(entry.file_type(), detect_changes)?;
            if !entry
                .file_name()
                .to_str()
                .is_some_and(|name| name.bytes().any(|byte| byte.is_ascii_alphabetic()))
                || !(kind.is_file() || kind.is_dir())
            {
                continue;
            }
            ensure!(
                filesystem_folds_ascii_case_with_change_detection(
                    &entry.path(),
                    detect_changes
                        && !matches!(
                            entry.file_name().to_str(),
                            Some(BINDING | ".anneal-owner.json")
                        ),
                )? == self.folds_case,
                "Unsupported local directory case policy: {} differs from the workspace root",
                path.display()
            );
            break;
        }
        Ok(())
    }
}

fn filesystem_device(metadata: &fs::Metadata) -> Result<u64> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        Ok(metadata.dev())
    }
    #[cfg(not(unix))]
    {
        let _ = metadata;
        bail!("Unsupported local filesystem device admission")
    }
}

fn physical_directory_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    ensure!(metadata.is_dir(), "Saved source tree path is not a directory");
    physical_input_identity(metadata)
}

fn physical_input_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let mut identity = metadata.dev().to_le_bytes().to_vec();
        identity.extend_from_slice(&metadata.ino().to_le_bytes());
        Ok(identity)
    }
    #[cfg(not(unix))]
    {
        let _ = metadata;
        bail!("Unsupported saved-input physical identity")
    }
}

fn directory_modification_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    let mut identity = physical_directory_identity(metadata)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        // Signed platform timestamps also represent valid pre-epoch inputs.
        identity.extend_from_slice(&metadata.mtime().to_le_bytes());
        identity.extend_from_slice(&metadata.mtime_nsec().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime_nsec().to_le_bytes());
    }
    Ok(identity)
}

fn modification_identity(metadata: &fs::Metadata) -> Result<Vec<u8>> {
    ensure!(metadata.is_file(), "Saved Lean input is not a regular file");
    let mut identity = Vec::new();
    identity.extend_from_slice(&metadata.len().to_le_bytes());
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        identity.extend_from_slice(&metadata.mtime().to_le_bytes());
        identity.extend_from_slice(&metadata.mtime_nsec().to_le_bytes());
        identity.extend_from_slice(&metadata.dev().to_le_bytes());
        identity.extend_from_slice(&metadata.ino().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime().to_le_bytes());
        identity.extend_from_slice(&metadata.ctime_nsec().to_le_bytes());
    }
    Ok(identity)
}

#[cfg(test)]
pub(crate) mod tests {
    use serde_json::json;

    use super::*;

    // Concurrent process tests can fork while another test's fence is open.
    // Retry only a busy acquisition; errors remain immediate, and a timeout
    // panics so corruption fixtures cannot mistake contention for rejection.
    fn wait_for_test_attempt<T>(mut attempt: impl FnMut() -> Result<Option<T>>) -> Result<T> {
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            if let Some(lock) = attempt()? {
                return Ok(lock);
            }
            assert!(std::time::Instant::now() < deadline, "Test lock contention did not clear");
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }

    pub(crate) fn wait_for_test_lock<T>(attempt: impl FnMut() -> Result<Option<T>>) -> T {
        wait_for_test_attempt(attempt).unwrap()
    }

    pub(crate) struct Fixture {
        _temp: tempfile::TempDir,
        base: PathBuf,
        pub(crate) sdk: LeanSdk,
    }

    impl Fixture {
        pub(crate) fn new(modules: &[&str]) -> Self {
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

    #[cfg(unix)]
    #[test]
    fn stage_root_and_binding_stay_private_under_group_umask() {
        use std::os::unix::fs::PermissionsExt;

        const CHILD: &str = "ANNEAL_SDK_STAGE_GROUP_UMASK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .arg("stage_root_and_binding_stay_private_under_group_umask")
                .arg("--test-threads=1")
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }

        let f = Fixture::new(&["Shared.A"]);
        unsafe extern "C" {
            fn umask(mode: u32) -> u32;
        }
        // SAFETY: the filtered test runs alone in this child process.
        let previous = unsafe { umask(0o002) };
        #[cfg(target_os = "macos")]
        let stage_parent = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let stage_parent = tempfile::tempdir().unwrap();
        // Keep the fixture parent admitted while testing the child's group umask.
        fs::set_permissions(stage_parent.path(), fs::Permissions::from_mode(0o700)).unwrap();
        let stage = stage_parent.path().join("stage");
        let final_root = f.base.join("final-root");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &[".", "src"]).unwrap();
        assert_eq!(fs::metadata(&stage).unwrap().permissions().mode() & 0o777, 0o700);
        for relative in [BINDING, OUTPUT_OWNER] {
            assert_eq!(
                fs::metadata(stage.join(relative)).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
        // SAFETY: restore this child's prior process-wide umask.
        unsafe { umask(previous) };
    }

    #[test]
    fn generated_configuration_replaces_hardlinked_inodes_without_changing_saved_sources() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let source = workspace.root().join("SourceSaved.lean");
        let bytes = b"def saved := 10\n";
        fs::write(&source, bytes).unwrap();
        for name in [LAKE_CONFIGURATION, "lakefile.lean"] {
            let destination = workspace.root().join(name);
            fs::remove_file(&destination).unwrap();
            fs::hard_link(&source, &destination).unwrap();
            let identity = physical_input_identity(&fs::metadata(&source).unwrap()).unwrap();
            configure_test_workspace(&workspace);
            assert_eq!(fs::read(&source).unwrap(), bytes);
            assert_ne!(
                physical_input_identity(&fs::metadata(&destination).unwrap()).unwrap(),
                identity
            );
            workspace.admit().unwrap();
            assert!(!fs::read_dir(workspace.root()).unwrap().any(|entry| {
                entry.unwrap().file_name().to_string_lossy().starts_with(".anneal-lake-")
            }));
        }
    }

    #[cfg(unix)]
    #[test]
    fn generated_configuration_replaces_fifo_entries_without_opening_them() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        for name in [LAKE_CONFIGURATION, "lakefile.lean"] {
            let destination = workspace.root().join(name);
            fs::remove_file(&destination).unwrap();
            assert!(Command::new("mkfifo").arg(&destination).status().unwrap().success());
            // No FIFO reader or source payload is supplied. Replacement must
            // finish without ever opening the old stream for writing.
            configure_test_workspace(&workspace);
            assert!(fs::symlink_metadata(&destination).unwrap().file_type().is_file());
            workspace.admit().unwrap();
        }
    }

    #[test]
    fn later_generated_file_rename_failure_leaves_no_tempfiles_and_requires_regeneration() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let lakefile = workspace.root().join("lakefile.lean");
        fs::remove_file(&lakefile).unwrap();
        fs::create_dir(&lakefile).unwrap();
        let result = Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[
                LakeLibrary { name: "Changed", source_root: ".", modules: &[] },
                LakeLibrary { name: "Source1", source_root: "src", modules: &[] },
            ],
        );
        assert!(result.is_err());
        let spec: LakeConfiguration =
            serde_json::from_slice(&fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap())
                .unwrap();
        assert_eq!(spec.libraries[0].name, "Changed");
        assert!(!fs::read_dir(workspace.root()).unwrap().any(|entry| {
            entry.unwrap().file_name().to_string_lossy().starts_with(".anneal-lake-")
        }));
        assert!(workspace.admit().is_err());
        fs::remove_dir(lakefile).unwrap();
        configure_test_workspace(&workspace);
        workspace.admit().unwrap();
    }

    #[test]
    fn nul_source_roots_are_rejected_before_creating_any_binding_or_owner() {
        let f = Fixture::new(&["Shared.A"]);
        let before = fs::read_dir(&f.base)
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect::<BTreeSet<_>>();
        let root = f.base.join("nul-workspace");
        let stage = f.base.join("nul-stage");
        let final_root = f.base.join("nul-final");
        let error = Workspace::create(&f.sdk, &root, &["src\0other"]).err().unwrap();
        assert_eq!(error.to_string(), "Workspace source roots cannot contain NUL bytes");
        let error =
            Workspace::stage(&f.sdk, &stage, &final_root, None, &["src\0other"]).unwrap_err();
        assert_eq!(error.to_string(), "Workspace source roots cannot contain NUL bytes");
        assert!(!root.exists() && !stage.exists() && !final_root.exists());
        assert_eq!(
            before,
            fs::read_dir(&f.base)
                .unwrap()
                .map(|entry| entry.unwrap().file_name())
                .collect::<BTreeSet<_>>()
        );

        let workspace = f.workspace();
        let binding = fs::read(workspace.root().join(BINDING)).unwrap();
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let stamp = workspace.source_stamp().unwrap();
        let error =
            Workspace::stage(&f.sdk, &stage, workspace.root(), Some(&workspace), &["src\0other"])
                .unwrap_err();
        assert_eq!(error.to_string(), "Workspace source roots cannot contain NUL bytes");
        assert!(!stage.exists());
        assert_eq!(fs::read(workspace.root().join(BINDING)).unwrap(), binding);
        assert_eq!(fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap(), owner);
        assert_eq!(workspace.source_stamp().unwrap(), stamp);
    }

    #[test]
    fn source_root_aliases_are_normalized_before_binding() {
        let f = Fixture::new(&["Shared.A"]);
        let root = f.base.join("root-aliases");
        for roots in [&["src", "./src"][..], &["src/./lean", "src/lean"][..]] {
            let error = Workspace::create(&f.sdk, &root, roots).err().unwrap();
            assert!(error.to_string().contains("Duplicate workspace source root"));
            assert!(!root.exists());
        }
        assert!(normalize_source_roots(&["src".into(), "SRC".into()], true).is_err());
        assert!(normalize_source_roots(&["src".into(), "SRC".into()], false).is_ok());

        let workspace = Workspace::create(&f.sdk, &root, &["./src"]).unwrap();
        assert_eq!(workspace.binding.source_roots, vec![PathBuf::from("src")]);
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[LakeLibrary { name: "Source", source_root: "./src", modules: &[] }],
        )
        .unwrap();
        let spec: LakeConfiguration =
            serde_json::from_slice(&fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap())
                .unwrap();
        assert_eq!(spec.libraries[0].source_root, PathBuf::from("src"));
        workspace.admit().unwrap();
    }

    #[test]
    fn unicode_source_root_aliases_follow_the_destination_filesystem() {
        let f = Fixture::new(&["Shared.A"]);
        for (index, roots) in
            [["src/é", "src/e\u{301}"], ["src/K", "src/K"]].into_iter().enumerate()
        {
            let probe = tempfile::tempdir_in(&f.base).unwrap();
            for root in roots {
                fs::create_dir_all(probe.path().join(root)).unwrap();
            }
            let aliases =
                physical_directory_identity(&fs::metadata(probe.path().join(roots[0])).unwrap())
                    .unwrap()
                    == physical_directory_identity(
                        &fs::metadata(probe.path().join(roots[1])).unwrap(),
                    )
                    .unwrap();
            let final_root = f.base.join(format!("unicode-source-roots-{index}"));
            let result = Workspace::create(&f.sdk, &final_root, &roots);
            assert_eq!(result.is_err(), aliases);
            if aliases {
                assert!(!final_root.exists());
            } else {
                let workspace = result.unwrap();
                assert_eq!(workspace.binding.source_roots.len(), 2);
                workspace.admit().unwrap();
            }
        }
    }

    #[test]
    fn unicode_private_source_root_aliases_follow_physical_component_names() {
        let f = Fixture::new(&["Shared.A"]);
        for (index, (reserved, candidate)) in
            [(".lake", ".laKe"), (".runtime", ".runtİme"), (".git", ".gİt")].into_iter().enumerate()
        {
            let probe = tempfile::tempdir_in(&f.base).unwrap();
            fs::create_dir(probe.path().join(reserved)).unwrap();
            fs::create_dir_all(probe.path().join(candidate)).unwrap();
            let aliases =
                physical_directory_identity(&fs::metadata(probe.path().join(reserved)).unwrap())
                    .unwrap()
                    == physical_directory_identity(
                        &fs::metadata(probe.path().join(candidate)).unwrap(),
                    )
                    .unwrap();
            assert_eq!(
                reject_existing_source_root_aliases(probe.path(), &[candidate.into()]).is_err(),
                aliases
            );
            let final_root = f.base.join(format!("unicode-private-{index}"));
            let result = Workspace::create(&f.sdk, &final_root, &[candidate]);
            assert_eq!(result.is_err(), aliases, "{candidate} versus {reserved}");
            if aliases {
                assert!(!final_root.exists());
            } else {
                result.unwrap().admit().unwrap();
            }
        }
    }

    #[test]
    fn existing_unicode_stage_admission_does_not_touch_live_or_staged_inputs() {
        let f = Fixture::new(&["Shared.A"]);
        let escaped = "source space \"quoted\" \\f é\u{8}\u{c}";
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("unicode-live"), &[".", escaped]).unwrap();
        configure_test_workspace(&workspace);
        let live_stamp = workspace.source_stamp().unwrap();
        let stage = f.base.join("unicode-stage");
        Workspace::stage(&f.sdk, &stage, workspace.root(), Some(&workspace), &[".", escaped])
            .unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), live_stamp);
        Workspace::write_lakefile(
            &f.sdk,
            &stage,
            &[
                LakeLibrary { name: "Source0", source_root: ".", modules: &[] },
                LakeLibrary { name: "Source1", source_root: escaped, modules: &[] },
            ],
        )
        .unwrap();
        let stage_stamp = stamp_saved_inputs(&stage, |_| {}).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), live_stamp);
        assert_eq!(stamp_saved_inputs(&stage, |_| {}).unwrap(), stage_stamp);
    }

    #[test]
    fn stage_policy_requires_matching_device_and_case_before_adoption() {
        ensure_stage_destination_policy(7, 7, true, true).unwrap();
        let different_device = ensure_stage_destination_policy(7, 8, true, true).unwrap_err();
        assert!(different_device.to_string().contains("share one filesystem"));
        let different_case = ensure_stage_destination_policy(7, 7, true, false).unwrap_err();
        assert!(different_case.to_string().contains("different case policies"));
    }

    #[cfg(unix)]
    #[test]
    fn nested_existing_stages_are_rejected_without_touching_live_inputs_or_provenance() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        workspace.finish_local_outputs(&prepared).unwrap();
        let alias = f.base.join("live-parent-alias");
        symlink(workspace.root(), &alias).unwrap();
        let stamp = workspace.source_stamp().unwrap();
        let provenance = fs::read(workspace.root().join(LOCAL_INPUT_PROVENANCE)).unwrap();
        let source = fs::read(workspace.root().join("Proof.lean")).unwrap();
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let identity = modification_identity(&fs::metadata(&output).unwrap()).unwrap();
        let mut stages = vec![
            (workspace.root().join(".stage"), workspace.root().to_path_buf()),
            (workspace.root().join(".stage.LOCK"), workspace.root().to_path_buf()),
            (alias.join(".stage"), workspace.root().to_path_buf()),
        ];
        if workspace.folds_ascii_case().unwrap() {
            stages.push((
                workspace.root().join(".case-stage.LOCK"),
                workspace.root().with_file_name("WORKSPACE"),
            ));
        }
        for (stage, final_root) in stages {
            let error =
                Workspace::stage(&f.sdk, &stage, &final_root, Some(&workspace), &[".", "src"])
                    .unwrap_err();
            assert_eq!(
                error.to_string(),
                "Existing workspace stage must be outside the live workspace"
            );
            assert!(!stage.exists());
            assert_eq!(workspace.source_stamp().unwrap(), stamp);
            assert_eq!(
                fs::read(workspace.root().join(LOCAL_INPUT_PROVENANCE)).unwrap(),
                provenance
            );
            assert_eq!(fs::read(workspace.root().join("Proof.lean")).unwrap(), source);
            assert_eq!(fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap(), owner);
            assert_eq!(modification_identity(&fs::metadata(&output).unwrap()).unwrap(), identity);
        }
    }

    #[cfg(unix)]
    #[test]
    fn stage_admission_rechecks_moved_and_equal_live_roots_without_touching_inputs() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let workspace = Workspace::create(&f.sdk, &f.base.join("workspace"), &["src/é"]).unwrap();
        configure_test_workspace(&workspace);
        fs::create_dir_all(workspace.root().join("src/é")).unwrap();
        fs::write(workspace.root().join("src/é/Proof.lean"), "def proof := 1\n").unwrap();
        let external = f.base.join("external-stage");
        Workspace::stage(&f.sdk, &external, workspace.root(), Some(&workspace), &["src/é"])
            .unwrap();
        Workspace::write_lakefile(
            &f.sdk,
            &external,
            &[LakeLibrary { name: "Source0", source_root: "src/é", modules: &[] }],
        )
        .unwrap();
        fs::create_dir_all(external.join("src/é")).unwrap();
        fs::write(external.join("src/é/Proof.lean"), "def proof := 2\n").unwrap();
        // Establish that this was a valid external stage before relocation.
        Workspace::admit_stage(&f.sdk, &external, workspace.root()).unwrap();
        let nested = workspace.root().join(".moved-stage.locK");
        fs::rename(&external, &nested).unwrap();
        let alias = f.base.join("live-alias");
        symlink(workspace.root(), &alias).unwrap();
        let live_stamp = workspace.source_stamp().unwrap();
        let staged_stamp = stamp_saved_inputs(&nested, |_| {}).unwrap();
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let binding = fs::read(nested.join(BINDING)).unwrap();
        let mut paths = vec![
            (nested.clone(), workspace.root().to_path_buf()),
            (alias.join(nested.file_name().unwrap()), workspace.root().to_path_buf()),
            (workspace.root().to_path_buf(), workspace.root().to_path_buf()),
        ];
        if workspace.folds_ascii_case().unwrap() {
            paths.push((nested.clone(), workspace.root().with_file_name("WORKSPACE")));
            paths.push((
                workspace.root().with_file_name("WORKSPACE"),
                workspace.root().to_path_buf(),
            ));
        }
        for (stage, final_root) in paths {
            let error = Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap_err();
            assert_eq!(
                error.to_string(),
                "Existing workspace stage must be outside the live workspace"
            );
            assert_eq!(workspace.source_stamp().unwrap(), live_stamp);
            assert_eq!(stamp_saved_inputs(&nested, |_| {}).unwrap(), staged_stamp);
            assert_eq!(fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap(), owner);
            assert_eq!(fs::read(nested.join(BINDING)).unwrap(), binding);
            assert_eq!(
                fs::read_to_string(workspace.root().join("src/é/Proof.lean")).unwrap(),
                "def proof := 1\n"
            );
        }
    }

    #[test]
    fn sdk_source_aliases_require_the_exported_lean_provider_and_its_case_policy() {
        let f = Fixture::new(&["Shared.A"]);
        let source = f.sdk.root().join("src/lean/Shared/A.lean");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        fs::write(&source, "def shared := 10\n").unwrap();
        let folds_case = filesystem_folds_ascii_case(&source).unwrap();
        let suffix_alias = source.with_extension("LEAN");
        let component_alias = source.with_file_name("a.lean");
        let full_alias = source.parent().unwrap().with_file_name("shared").join("a.LEAN");
        if !folds_case {
            fs::write(&suffix_alias, "distinct suffix file\n").unwrap();
            fs::write(&component_alias, "distinct basename file\n").unwrap();
            fs::create_dir_all(full_alias.parent().unwrap()).unwrap();
            fs::write(&full_alias, "distinct directory file\n").unwrap();
        }
        let unexported = source.with_file_name("Unexported.lean");
        fs::write(&unexported, "def unexported := 20\n").unwrap();
        let non_lean = source.with_extension("txt");
        fs::hard_link(&source, &non_lean).unwrap();
        let workspace = f.workspace();
        for path in [&source, &suffix_alias, &component_alias, &full_alias] {
            let expected = path == &source || folds_case;
            assert_eq!(workspace.contains_source(path).unwrap(), expected);
            assert_eq!(workspace.contains_sdk_source(path).unwrap(), expected);
            assert_eq!(workspace.contains_immutable_sdk_source(path).unwrap(), expected);
        }
        for path in [&unexported, &non_lean] {
            assert!(!workspace.contains_sdk_source(path).unwrap());
            assert!(!workspace.contains_immutable_sdk_source(path).unwrap());
        }
        if !folds_case {
            fs::remove_file(&suffix_alias).unwrap();
            fs::hard_link(&source, &suffix_alias).unwrap();
            assert!(!workspace.contains_immutable_sdk_source(&suffix_alias).unwrap());
        }
        let backup = f.base.join("writer-backup");
        fs::rename(workspace.root(), &backup).unwrap();
        assert_eq!(workspace.contains_immutable_sdk_source(&suffix_alias).unwrap(), folds_case);
        assert!(workspace.contains_sdk_source(&source).is_err());
        fs::rename(backup, workspace.root()).unwrap();
        workspace.admit().unwrap();
    }

    #[test]
    fn dotted_sdk_filename_is_not_the_exported_nested_module_provider() {
        let f = Fixture::new(&["Foo.Bar"]);
        let canonical = f.sdk.root().join("src/lean/Foo/Bar.lean");
        let dotted = f.sdk.root().join("src/lean/Foo.Bar.lean");
        fs::create_dir_all(canonical.parent().unwrap()).unwrap();
        fs::write(&canonical, "def nested := 1\n").unwrap();
        fs::write(&dotted, "def dotted := 2\n").unwrap();
        let workspace = f.workspace();
        assert!(workspace.contains_immutable_sdk_source(&canonical).unwrap());
        assert!(!workspace.contains_immutable_sdk_source(&dotted).unwrap());
        assert!(!workspace.contains_sdk_source(&dotted).unwrap());
    }

    #[test]
    fn dotted_local_lean_file_is_stamped_without_claiming_module_provider() {
        let f = Fixture::new(&["Foo.Bar"]);
        let workspace = Workspace::create(&f.sdk, &f.base.join("dotted-local"), &["src"]).unwrap();
        configure_test_workspace(&workspace);
        fs::create_dir(workspace.root().join("src")).unwrap();
        let dotted = workspace.root().join("src/Foo.Bar.lean");
        fs::write(&dotted, "def data := 1\n").unwrap();
        workspace.admit().unwrap();
        let before = workspace.source_stamp().unwrap();
        fs::write(&dotted, "def data := 2\n").unwrap();
        assert_ne!(workspace.source_stamp().unwrap(), before);
        let nested = workspace.root().join("src/Foo/Bar.lean");
        fs::create_dir(nested.parent().unwrap()).unwrap();
        fs::write(&nested, "def provider := 1\n").unwrap();
        assert!(
            workspace.admit().unwrap_err().to_string().contains("Local/SDK exact module collision")
        );
    }

    #[cfg(unix)]
    #[test]
    fn merged_sdk_source_view_routes_distinct_physical_providers() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A", "Other.B"]);
        let source_view = f.sdk.root().join("src/lean");
        let first_origin = f.base.join("toolchain/aeneas/Shared");
        let second_origin = f.base.join("toolchain/lean/Other");
        fs::create_dir_all(&first_origin).unwrap();
        fs::create_dir_all(&second_origin).unwrap();
        let first = first_origin.join("A.lean");
        let second = second_origin.join("B.lean");
        fs::write(&first, "def first := 1\n").unwrap();
        fs::write(&second, "def second := 2\n").unwrap();
        // The publisher compacts complete namespaces but links individual
        // files when two providers contribute to a merged source view.
        symlink(&first_origin, source_view.join("Shared")).unwrap();
        fs::create_dir(source_view.join("Other")).unwrap();
        symlink(&second, source_view.join("Other/B.lean")).unwrap();
        let workspace = f.workspace();
        for (view, origin) in
            [(source_view.join("Shared/A.lean"), first), (source_view.join("Other/B.lean"), second)]
        {
            assert!(workspace.contains_immutable_sdk_source(&view).unwrap());
            assert!(workspace.contains_immutable_sdk_source(&origin).unwrap());
        }
        let dotted = source_view.join("Other.B.lean");
        fs::write(&dotted, "def unrelated := 3\n").unwrap();
        assert!(!workspace.contains_immutable_sdk_source(&dotted).unwrap());
    }

    #[test]
    fn outside_same_suffix_hardlinks_cannot_be_sdk_source_routes() {
        let f = Fixture::new(&["Shared.A"]);
        let source = f.sdk.root().join("src/lean/Shared/A.lean");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        fs::write(&source, "def shared := 10\n").unwrap();
        let outside = f.base.join("outside/Shared/A.lean");
        fs::create_dir_all(outside.parent().unwrap()).unwrap();
        fs::hard_link(&source, &outside).unwrap();
        assert_eq!(
            physical_input_identity(&fs::metadata(&source).unwrap()).unwrap(),
            physical_input_identity(&fs::metadata(&outside).unwrap()).unwrap()
        );
        assert_ne!(source.canonicalize().unwrap(), outside.canonicalize().unwrap());
        let workspace = f.workspace();
        assert!(workspace.contains_sdk_source(&source).unwrap());
        assert!(!workspace.contains_source(&outside).unwrap());
        assert!(!workspace.contains_sdk_source(&outside).unwrap());
        assert!(!workspace.contains_immutable_sdk_source(&outside).unwrap());
        let backup = f.base.join("writer-hardlink-backup");
        fs::rename(workspace.root(), &backup).unwrap();
        assert!(workspace.contains_immutable_sdk_source(&source).unwrap());
        assert!(!workspace.contains_immutable_sdk_source(&outside).unwrap());
        fs::rename(backup, workspace.root()).unwrap();
        workspace.admit().unwrap();
    }

    #[test]
    fn immutable_sdk_source_lookup_does_not_admit_a_transitional_workspace() {
        let f = Fixture::new(&["Shared.A"]);
        let source = f.sdk.root().join("src/lean/Shared/A.lean");
        let unexported = source.with_file_name("Unexported.lean");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        fs::write(&source, "def shared := 10\n").unwrap();
        fs::write(&unexported, "def unexported := 20\n").unwrap();
        let workspace = f.workspace();
        assert!(workspace.contains_sdk_source(&source).unwrap());
        assert!(!workspace.contains_immutable_sdk_source(&unexported).unwrap());
        let binding = fs::read(workspace.root().join(BINDING)).unwrap();
        fs::write(workspace.root().join(BINDING), "{}\n").unwrap();
        assert!(workspace.contains_immutable_sdk_source(&source).unwrap());
        assert!(workspace.contains_sdk_source(&source).is_err());
        assert!(workspace.lake_command(LakeOperation::Version).is_err());
        fs::write(workspace.root().join(BINDING), binding).unwrap();
        let backup = f.base.join("writer-isolation-backup");
        fs::rename(workspace.root(), &backup).unwrap();
        assert!(workspace.contains_immutable_sdk_source(&source).unwrap());
        assert!(workspace.contains_sdk_source(&source).is_err());
        assert!(workspace.lake_command(LakeOperation::Version).is_err());
        let descriptor = f.sdk.root().join("sdk.json");
        let bytes = fs::read(&descriptor).unwrap();
        let mut changed = bytes.clone();
        changed.push(b'\n');
        fs::write(&descriptor, changed).unwrap();
        let error = workspace.contains_immutable_sdk_source(&source).unwrap_err();
        assert_eq!(error.to_string(), "SDK descriptor changed after admission");
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        fs::write(descriptor, bytes).unwrap();
        fs::rename(backup, workspace.root()).unwrap();
        workspace.admit().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn pre_epoch_file_and_directory_mtimes_remain_valid_saved_inputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let directory = workspace.root().join("Historical");
        fs::create_dir(&directory).unwrap();
        let source = directory.join("Proof.lean");
        fs::write(&source, "def value := 10\n").unwrap();
        let historical = std::time::UNIX_EPOCH - std::time::Duration::new(10, 123_456_789);
        for path in [&source, &directory] {
            fs::File::open(path)
                .unwrap()
                .set_times(fs::FileTimes::new().set_modified(historical))
                .unwrap();
            assert!(
                fs::metadata(path)
                    .unwrap()
                    .modified()
                    .unwrap()
                    .duration_since(std::time::UNIX_EPOCH)
                    .is_err()
            );
        }
        workspace.admit().unwrap();
        let original = workspace.source_stamp().unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), original);
        fs::File::open(&source)
            .unwrap()
            .set_times(
                fs::FileTimes::new()
                    .set_modified(std::time::UNIX_EPOCH - std::time::Duration::from_secs(20)),
            )
            .unwrap();
        let changed_source = workspace.source_stamp().unwrap();
        assert_ne!(changed_source, original);
        fs::File::open(&directory)
            .unwrap()
            .set_times(
                fs::FileTimes::new()
                    .set_modified(std::time::UNIX_EPOCH - std::time::Duration::from_secs(30)),
            )
            .unwrap();
        assert_ne!(workspace.source_stamp().unwrap(), changed_source);
    }

    #[test]
    fn identical_sdk_at_another_root_is_rejected_before_stage_creation() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let binding = fs::read(workspace.root().join(BINDING)).unwrap();
        let relocated_installation = f.base.join("relocated-toolchain");
        for entry in walkdir::WalkDir::new(&f.sdk.inner.installation).follow_links(false) {
            let entry = entry.unwrap();
            let destination = relocated_installation
                .join(entry.path().strip_prefix(&f.sdk.inner.installation).unwrap());
            if entry.file_type().is_dir() {
                fs::create_dir_all(destination).unwrap();
            } else {
                fs::copy(entry.path(), destination).unwrap();
            }
        }
        let relocated = LeanSdk::load(&relocated_installation.join("lean-sdk")).unwrap();
        assert_eq!(relocated.id(), f.sdk.id());
        assert_eq!(relocated.inner.descriptor_sha256, f.sdk.inner.descriptor_sha256);
        assert_ne!(relocated.root(), f.sdk.root());
        let stage = f.base.join("rejected-stage");
        let error =
            Workspace::stage(&relocated, &stage, workspace.root(), Some(&workspace), &[".", "src"])
                .unwrap_err();
        assert_eq!(error.to_string(), "Cannot relocate an existing workspace SDK");
        assert!(!stage.exists());
        assert!(!stage.join(BINDING).exists());
        assert_eq!(fs::read(workspace.root().join(BINDING)).unwrap(), binding);
        workspace.admit().unwrap();
    }

    #[test]
    fn oversized_binding_is_rejected_before_workspace_or_stage_creation() {
        let f = Fixture::new(&["Shared.A"]);
        let roots =
            (0..512).map(|index| format!("source_{index}_{}", "x".repeat(128))).collect::<Vec<_>>();
        let roots = roots.iter().map(String::as_str).collect::<Vec<_>>();
        let workspace = f.base.join("oversized-workspace");
        let error = Workspace::create(&f.sdk, &workspace, &roots).err().unwrap();
        assert_eq!(error.to_string(), "Workspace binding exceeds descriptor size limit");
        assert!(!workspace.exists());
        assert!(!workspace.join(BINDING).exists());
        let stage = f.base.join("oversized-stage");
        let final_root = f.base.join("oversized-final");
        let error = Workspace::stage(&f.sdk, &stage, &final_root, None, &roots).unwrap_err();
        assert_eq!(error.to_string(), "Workspace binding exceeds descriptor size limit");
        assert!(!stage.exists());
        assert!(!stage.join(BINDING).exists());
        assert!(!final_root.exists());
    }

    #[cfg(unix)]
    #[test]
    fn stage_write_and_admission_use_the_same_physical_parent_without_admitting_child_links() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("physical-parent");
        fs::create_dir(&parent).unwrap();
        // The raw parent alias models /tmp -> /private/tmp without changing
        // any global filesystem alias or following links inside the stage.
        let alias = f.base.join("parent-alias");
        symlink(&parent, &alias).unwrap();
        let stage = alias.join("stage");
        let final_root = alias.join("workspace");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        fs::create_dir(stage.join("src")).unwrap();
        fs::write(stage.join("src/Proof.lean"), "def value := 10\n").unwrap();
        let libraries =
            [LakeLibrary { name: "Generated", source_root: "src", modules: &["Proof".into()] }];
        Workspace::write_lakefile(&f.sdk, &stage, &libraries).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
        let binding: Binding = read_json(&stage.canonicalize().unwrap().join(BINDING)).unwrap();
        assert_eq!(binding.workspace, parent.join("workspace"));

        let external = f.base.join("External.lean");
        fs::write(&external, "def external := 20\n").unwrap();
        let link = stage.join("src/Linked.lean");
        symlink(&external, &link).unwrap();
        let error = Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap_err();
        assert!(error.to_string().contains("symlink"));
        fs::remove_file(link).unwrap();

        let lakefile = stage.join("lakefile.lean");
        let external_lakefile = f.base.join("external-lakefile.lean");
        fs::rename(&lakefile, &external_lakefile).unwrap();
        symlink(&external_lakefile, &lakefile).unwrap();
        let spec = fs::read(stage.join(LAKE_CONFIGURATION)).unwrap();
        let error = Workspace::write_lakefile(&f.sdk, &stage, &libraries).unwrap_err();
        assert!(error.to_string().contains("symlink"));
        assert_eq!(fs::read(stage.join(LAKE_CONFIGURATION)).unwrap(), spec);
        fs::remove_file(lakefile).unwrap();
        fs::rename(external_lakefile, stage.join("lakefile.lean")).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
    }

    #[test]
    fn oversized_generated_configuration_and_lakefile_are_rejected_before_either_write() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("bounded-workspace"), &["."]).unwrap();
        configure_test_workspace(&workspace);
        let preserved = [LAKE_CONFIGURATION, "lakefile.lean", BINDING, OUTPUT_OWNER]
            .map(|name| (name, fs::read(workspace.root().join(name)).unwrap()));
        let configuration = LakeConfiguration {
            libraries: vec![LibraryConfiguration {
                name: "Generated".into(),
                source_root: ".".into(),
                modules: vec!["M".into()],
            }],
        };
        let configuration_overhead = serde_json::to_vec_pretty(&configuration).unwrap().len() - 1;
        let lakefile_overhead = render_lakefile(&f.sdk, &configuration).unwrap().len() - 1;
        assert!(lakefile_overhead > configuration_overhead);
        // Use the actual reader bound. These valid ASCII module declarations
        // need no physical provider or subject execution, and are never written.
        for (extra, expected) in [
            (1, "Generated Lake configuration exceeds size limit"),
            (0, "Generated Lakefile exceeds size limit"),
        ] {
            let modules =
                vec!["M".repeat(MAX_MODULES_SIZE as usize - configuration_overhead + extra)];
            let error = Workspace::write_lakefile(
                &f.sdk,
                workspace.root(),
                &[LakeLibrary { name: "Generated", source_root: ".", modules: &modules }],
            )
            .unwrap_err();
            assert_eq!(error.to_string(), expected);
            for (name, bytes) in &preserved {
                assert_eq!(&fs::read(workspace.root().join(name)).unwrap(), bytes);
            }
            workspace.admit().unwrap();
        }

        let stage = f.base.join("bounded-stage");
        let final_root = f.base.join("bounded-final");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["."]).unwrap();
        let modules = vec!["M".repeat(MAX_MODULES_SIZE as usize)];
        assert!(
            Workspace::write_lakefile(
                &f.sdk,
                &stage,
                &[LakeLibrary { name: "Generated", source_root: ".", modules: &modules }],
            )
            .is_err()
        );
        assert!(!stage.join(LAKE_CONFIGURATION).exists());
        assert!(!stage.join("lakefile.lean").exists());
        assert!(!final_root.exists());
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
    }

    #[test]
    fn generated_plugin_target_names_cannot_be_lake_libraries() {
        let mut f = Fixture::new(&["Shared.A"]);
        let root = f.sdk.root().to_path_buf();
        fs::write(root.join("lib/plugin.so"), "immutable fixture plugin").unwrap();
        let descriptor_path = root.join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        descriptor["plugins"] = json!([{"path":"lib/plugin.so", "name":"nativePlugin"}]);
        fs::write(&descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        f.sdk = LeanSdk::load(&root).unwrap();
        let workspace = f.workspace();
        let spec = fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap();
        let lakefile = fs::read(workspace.root().join("lakefile.lean")).unwrap();
        for name in ["annealPlugin0", "annealPlugin1", "annealPlugin00"] {
            let error = Workspace::write_lakefile(
                &f.sdk,
                workspace.root(),
                &[
                    LakeLibrary { name, source_root: ".", modules: &[] },
                    LakeLibrary { name: "Source1", source_root: "src", modules: &[] },
                ],
            )
            .unwrap_err();
            assert!(error.to_string().contains("reserved for generated plugin targets"));
            assert_eq!(fs::read(workspace.root().join(LAKE_CONFIGURATION)).unwrap(), spec);
            assert_eq!(fs::read(workspace.root().join("lakefile.lean")).unwrap(), lakefile);
        }
        // Admission must reject a colliding spec even if its entire script is
        // otherwise the exact canonical rendering of that spec.
        let mut configuration: LakeConfiguration = serde_json::from_slice(&spec).unwrap();
        configuration.libraries[0].name = "annealPlugin0".into();
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
        assert!(
            workspace
                .admit()
                .unwrap_err()
                .to_string()
                .contains("reserved for generated plugin targets")
        );
        fs::write(workspace.root().join(LAKE_CONFIGURATION), spec).unwrap();
        fs::write(workspace.root().join("lakefile.lean"), lakefile).unwrap();
        workspace.admit().unwrap();
    }

    #[test]
    fn lean_literals_distinguish_control_escapes_from_literal_backslash_sequences() {
        let value = "space \"quote\" slash\\b\\f unicode é🙂\u{8}\u{c}\n\r\t\0";
        let literal = lean_string_literal(value).unwrap();
        assert_eq!(
            literal,
            "\"space \\\"quote\\\" slash\\\\b\\\\f unicode é🙂\\u0008\\u000c\\n\\r\\t\\u0000\""
        );
        assert_eq!(serde_json::from_str::<String>(&literal).unwrap(), value);
    }

    #[test]
    fn canonical_lake_paths_use_lean_control_escapes_without_excluding_valid_characters() {
        let mut f = Fixture::new(&["Shared.A"]);
        let root = f.sdk.root().to_path_buf();
        let plugin = "lib/native plugin \"quoted\" \\b é\u{8}\u{c}.so";
        fs::write(root.join(plugin), "immutable fixture native plugin").unwrap();
        let descriptor_path = root.join("sdk.json");
        let mut descriptor: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        descriptor["plugins"] = json!([{"path":plugin, "name":"nativePlugin"}]);
        fs::write(&descriptor_path, serde_json::to_vec(&descriptor).unwrap()).unwrap();
        f.sdk = LeanSdk::load(&root).unwrap();
        let source_root = "source space \"quoted\" \\f é\u{8}\u{c}";
        let workspace =
            Workspace::create(&f.sdk, &f.base.join("escaped-workspace"), &[source_root]).unwrap();
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[LakeLibrary { name: "Generated", source_root, modules: &[] }],
        )
        .unwrap();
        let lakefile = fs::read_to_string(workspace.root().join("lakefile.lean")).unwrap();
        assert!(
            lakefile.contains(&format!("srcDir := {}", lean_string_literal(source_root).unwrap()))
        );
        assert!(lakefile.contains(&format!(
            "System.FilePath := {}",
            lean_string_literal(f.sdk.plugins()[0].path.to_str().unwrap()).unwrap()
        )));
        assert!(lakefile.contains("\\u0008\\u000c"));
        workspace.admit().unwrap();
        workspace.lake_command(LakeOperation::Build(&[])).unwrap();
    }

    fn configure_compilation_fixture(workspace: &Workspace<'_>) {
        fs::write(workspace.root().join("Proof.lean"), "def value := 10\n").unwrap();
        Workspace::write_lakefile(
            workspace.sdk(),
            workspace.root(),
            &[
                LakeLibrary { name: "Source0", source_root: ".", modules: &["Proof".into()] },
                LakeLibrary { name: "Source1", source_root: "src", modules: &[] },
            ],
        )
        .unwrap();
    }

    fn local_output(workspace: &Workspace<'_>, relative: &str) -> PathBuf {
        let path = workspace.root().join(".lake/build").join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, b"owned local compilation sentinel").unwrap();
        path
    }

    #[test]
    fn saved_inputs_include_local_data_and_detect_later_changes() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let data = workspace.root().join("A.data");
        let later = workspace.root().join("Z.lean");
        fs::write(&data, "10").unwrap();
        fs::write(&later, "def value := 10\n").unwrap();
        assert!(saved_inputs(workspace.root()).unwrap().contains(&data));
        let before = workspace.source_stamp().unwrap();
        fs::write(&data, "20").unwrap();
        assert_ne!(workspace.source_stamp().unwrap(), before);
        for delete in [false, true] {
            fs::write(&data, "10").unwrap();
            let error = stamp_saved_inputs(workspace.root(), |recorded| {
                if recorded == later {
                    if delete {
                        fs::remove_file(&data).unwrap();
                    } else {
                        fs::write(&data, "20").unwrap();
                    }
                }
            })
            .unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_some());
        }
    }

    #[test]
    fn local_provenance_retains_unchanged_outputs_and_clears_changed_source_or_data() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let data = workspace.root().join("fixture-data.txt");
        fs::write(&data, "10").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        let identity = modification_identity(&fs::metadata(&output).unwrap()).unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        assert_eq!(prepared.stamp(), workspace.source_stamp().unwrap());
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert_eq!(modification_identity(&fs::metadata(&output).unwrap()).unwrap(), identity);
        assert!(!workspace.root().join(LOCAL_INPUT_PROVENANCE).exists());
        workspace.finish_local_outputs(&prepared).unwrap();
        fs::write(workspace.root().join("Proof.lean"), "def value := 20\n").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        workspace.finish_local_outputs(&prepared).unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        fs::write(&data, "20").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        assert!(workspace.root().join(OUTPUT_OWNER).exists());
        assert!(workspace.root().join(".runtime/cache").is_dir());
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn auxiliary_addition_removal_and_undeclared_lean_data_clear_owned_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let auxiliary = workspace.root().join("Auxiliary.lean");
        for change in [0, 1, 2] {
            let output = local_output(&workspace, "lib/lean/Proof.olean");
            match change {
                0 => fs::write(&auxiliary, "local undeclared data\n").unwrap(),
                1 => fs::write(&auxiliary, "changed local undeclared data\n").unwrap(),
                _ => fs::remove_file(&auxiliary).unwrap(),
            }
            let prepared = workspace.prepare_local_outputs().unwrap();
            assert!(!output.exists());
            workspace.finish_local_outputs(&prepared).unwrap();
        }
    }

    #[test]
    fn permitted_empty_directory_membership_and_entry_type_invalidate_local_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let enumerated = workspace.root().join("fixture-directory");
        fs::create_dir(&enumerated).unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let entry = enumerated.join("Entry");
        for change in [0, 1, 2, 3] {
            let output = local_output(&workspace, "lib/lean/Proof.olean");
            let before = workspace.source_snapshot().unwrap();
            match change {
                0 => fs::create_dir(&entry).unwrap(),
                1 => {
                    fs::remove_dir(&entry).unwrap();
                    fs::write(&entry, "local auxiliary entry").unwrap();
                }
                2 => {
                    fs::remove_file(&entry).unwrap();
                    fs::create_dir(&entry).unwrap();
                }
                _ => fs::remove_dir(&entry).unwrap(),
            }
            let after = workspace.source_snapshot().unwrap();
            assert_ne!(before.stamp(), after.stamp());
            assert_ne!(before.auxiliary_stamp, after.auxiliary_stamp);
            let prepared = workspace.prepare_local_outputs().unwrap();
            assert!(!output.exists());
            assert!(workspace.root().join(OUTPUT_OWNER).is_file());
            workspace.finish_local_outputs(&prepared).unwrap();
        }
    }

    #[test]
    fn declared_unimported_provider_content_and_membership_invalidate_other_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        Workspace::write_lakefile(
            &f.sdk,
            workspace.root(),
            &[
                LakeLibrary {
                    name: "Source0",
                    source_root: ".",
                    modules: &["Proof".into(), "Optional".into()],
                },
                LakeLibrary { name: "Source1", source_root: "src", modules: &[] },
            ],
        )
        .unwrap();
        // Missing declared providers remain admitted; the output pruner omits
        // them. Their subsequent names are still visible to local enumeration.
        let optional = workspace.root().join("Optional.lean");
        assert!(!optional.exists());
        let prepared = workspace.prepare_local_outputs().unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        fs::write(&optional, "def optional := 10\n").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        workspace.finish_local_outputs(&prepared).unwrap();

        let output = local_output(&workspace, "lib/lean/Proof.olean");
        let proof = fs::read(workspace.root().join("Proof.lean")).unwrap();
        // Proof has no import of Optional. Its unchanged output must still be
        // invalidated if elaboration reads that declared provider as local data.
        fs::write(&optional, "def optional := 20\n").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        assert_eq!(fs::read(workspace.root().join("Proof.lean")).unwrap(), proof);
        workspace.finish_local_outputs(&prepared).unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        fs::remove_file(optional).unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn saved_observations_and_shared_fences_ignore_owned_private_file_churn() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let source = workspace.root().join("src/Proof.lean");
        fs::create_dir_all(source.parent().unwrap()).unwrap();
        fs::write(&source, "def value := 10\n").unwrap();
        let writer = workspace.writer_lock().unwrap();
        let original = workspace.source_stamp().unwrap();
        let temporary = workspace.root().join(".runtime/tmp/producer-file");
        let renamed = temporary.with_extension("renamed");
        // Deterministically mutate ordinary producer files between recording
        // saved inputs. They do not become saved inputs or output receipts.
        let observed = stamp_saved_inputs(workspace.root(), |_| {
            fs::write(&temporary, b"partial native output").unwrap();
            fs::rename(&temporary, &renamed).unwrap();
            fs::remove_file(&renamed).unwrap();
        })
        .unwrap();
        assert_eq!(observed, original);
        fs::write(&temporary, b"still producing").unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), original);
        assert!(workspace.contains_source(&source).unwrap());
        drop(writer);
        // The native server remains our producer even without a batch writer.
        let shared = wait_for_test_lock(|| workspace.try_shared_lock());
        fs::remove_file(temporary).unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), original);
        drop(shared);
        workspace.admit().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn observations_do_not_certify_linked_producer_outputs() {
        use std::os::unix::fs::symlink;
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let writer = workspace.writer_lock().unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        let original = workspace.source_stamp().unwrap();
        let link = workspace.root().join(".lake/build/linked-producer-output");
        fs::create_dir_all(link.parent().unwrap()).unwrap();
        symlink(f.sdk.root().join("lib/lean"), &link).unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), original);
        drop(writer);
        let shared = wait_for_test_lock(|| workspace.try_shared_lock());
        assert_eq!(workspace.source_stamp().unwrap(), original);
        drop(shared);
        // Observations credit no artifacts. Every actual invocation/adoption
        // still rejects the link, including post-producer finalization.
        assert!(workspace.admit().is_err());
        assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());
        assert!(workspace.finish_local_outputs(&prepared).is_err());
        assert!(!workspace.root().join(LOCAL_INPUT_PROVENANCE).exists());
        fs::remove_file(link).unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn saved_observation_keeps_private_roots_owner_and_source_namespace_checks() {
        use std::os::unix::fs::symlink;
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let source = workspace.root().join("Proof.lean");
        fs::write(&source, "def value := 10\n").unwrap();
        let before = workspace.source_stamp().unwrap();
        fs::write(&source, "def value := 20\n").unwrap();
        assert_ne!(before, workspace.source_stamp().unwrap());
        let owner = fs::read(workspace.root().join(OUTPUT_OWNER)).unwrap();
        let mut foreign = workspace.binding.clone();
        foreign.owner.push_str("-foreign");
        fs::write(workspace.root().join(OUTPUT_OWNER), serde_json::to_vec(&foreign).unwrap())
            .unwrap();
        assert!(workspace.source_stamp().is_err());
        fs::write(workspace.root().join(OUTPUT_OWNER), owner).unwrap();
        let runtime = workspace.root().join(".runtime/tmp");
        fs::remove_dir(&runtime).unwrap();
        symlink(f.sdk.root(), &runtime).unwrap();
        assert!(workspace.source_stamp().is_err());
        fs::remove_file(&runtime).unwrap();
        fs::create_dir(&runtime).unwrap();
        fs::remove_file(&source).unwrap();
        symlink(f.sdk.root().join("src/lean"), &source).unwrap();
        assert!(workspace.source_stamp().is_err());
    }

    #[test]
    fn private_directory_churn_and_permitted_metadata_changes_preserve_content_provenance() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let enumerated = workspace.root().join("fixture-directory");
        fs::create_dir(&enumerated).unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        let identity = modification_identity(&fs::metadata(&output).unwrap()).unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let before = workspace.source_snapshot().unwrap();
        for private in [".lake/cache/editor/empty", ".runtime/cache/empty"] {
            fs::create_dir_all(workspace.root().join(private)).unwrap();
        }
        fs::write(workspace.root().join(".runtime/cache/private-data"), "private churn").unwrap();
        assert_eq!(workspace.source_snapshot().unwrap().auxiliary_stamp, before.auxiliary_stamp);
        let time = std::time::UNIX_EPOCH + std::time::Duration::from_secs(123_456);
        fs::File::open(&enumerated)
            .unwrap()
            .set_times(fs::FileTimes::new().set_modified(time))
            .unwrap();
        let after = workspace.source_snapshot().unwrap();
        assert_ne!(before.stamp(), after.stamp());
        assert_eq!(before.auxiliary_stamp, after.auxiliary_stamp);
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert_eq!(modification_identity(&fs::metadata(&output).unwrap()).unwrap(), identity);
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn interrupted_or_obsolete_compilation_cannot_certify_restored_inputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let data = workspace.root().join("fixture-data.txt");
        fs::write(&data, "10").unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        fs::write(&data, "20").unwrap();
        let interrupted = workspace.prepare_local_outputs().unwrap();
        let obsolete_output = local_output(&workspace, "lib/lean/Proof.olean");
        fs::write(&data, "10").unwrap();
        let error = workspace.finish_local_outputs(&interrupted).unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_some());
        assert!(!workspace.root().join(LOCAL_INPUT_PROVENANCE).exists());
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!obsolete_output.exists());
        workspace.finish_local_outputs(&prepared).unwrap();
        let unfinished = workspace.prepare_local_outputs().unwrap();
        let partial_output = local_output(&workspace, "lib/lean/Proof.olean");
        drop(unfinished);
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!partial_output.exists());
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn provider_pruning_removes_undeclared_missing_families_but_keeps_valid_aliases() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let declared = local_output(&workspace, "lib/lean/Proof.olean");
        let folds_case = workspace.folds_ascii_case().unwrap();
        let valid = if folds_case {
            let alias = declared.with_file_name("PROOF.olean");
            fs::rename(&declared, &alias).unwrap();
            alias
        } else {
            declared
        };
        let undeclared = [
            "lib/lean/Removed.olean",
            "lib/lean/Removed.olean.private",
            "lib/lean/Removed.olean.server",
            "lib/lean/Removed.ilean",
            "lib/lean/Removed.ir",
            "lib/lean/Removed.olean.trace",
            "ir/Removed.c",
            "ir/Removed.c.o",
            "ir/Removed.c.o.trace",
        ]
        .map(|relative| local_output(&workspace, relative));
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(valid.exists());
        assert!(undeclared.iter().all(|path| !path.exists()));
        workspace.finish_local_outputs(&prepared).unwrap();
        fs::remove_file(workspace.root().join("Proof.lean")).unwrap();
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!valid.exists());
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn generated_configuration_changes_invalidate_local_outputs_without_source_edits() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        workspace.finish_local_outputs(&prepared).unwrap();
        // The physical source remains, but is no longer a declared target.
        configure_test_workspace(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert!(!output.exists());
        assert!(workspace.root().join("Proof.lean").exists());
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn malformed_or_oversized_provenance_invalidates_only_owned_build_outputs() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        for malformed in [vec![b'x'; 65], vec![b'x'; MAX_DESCRIPTOR_SIZE as usize + 1]] {
            fs::write(workspace.root().join(LOCAL_INPUT_PROVENANCE), malformed).unwrap();
            let output = local_output(&workspace, "lib/lean/Proof.olean");
            let prepared = workspace.prepare_local_outputs().unwrap();
            assert!(!output.exists());
            assert!(workspace.root().join(OUTPUT_OWNER).exists());
            workspace.finish_local_outputs(&prepared).unwrap();
        }
    }

    #[test]
    fn content_provenance_survives_owner_root_rename_and_metadata_change() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        configure_compilation_fixture(&workspace);
        let prepared = workspace.prepare_local_outputs().unwrap();
        let output = local_output(&workspace, "lib/lean/Proof.olean");
        let output_identity = modification_identity(&fs::metadata(&output).unwrap()).unwrap();
        workspace.finish_local_outputs(&prepared).unwrap();
        let backup = f.base.join("controlled-backup");
        fs::rename(workspace.root(), &backup).unwrap();
        fs::rename(&backup, workspace.root()).unwrap();
        assert_ne!(workspace.source_stamp().unwrap(), prepared.stamp());
        let prepared = workspace.prepare_local_outputs().unwrap();
        assert_eq!(
            modification_identity(&fs::metadata(&output).unwrap()).unwrap(),
            output_identity
        );
        workspace.finish_local_outputs(&prepared).unwrap();
    }

    #[test]
    fn local_case_probe_replacement_is_obsolete_even_when_alias_disappears() {
        let f = Fixture::new(&["Shared.A"]);
        let original = f.base.join("original-observation");
        let replacement = f.base.join("replacement-observation");
        fs::write(&original, "original").unwrap();
        fs::write(&replacement, "replacement").unwrap();
        let original = fs::metadata(original).unwrap();
        let replacement = fs::metadata(replacement).unwrap();
        for alias_missing in [false, true] {
            let mut step = 0;
            let error = filesystem_case_probe(&f.base.join("Probe"), true, |_| {
                step += 1;
                match step {
                    1 => Ok(original.clone()),
                    2 if alias_missing => Err(std::io::ErrorKind::NotFound.into()),
                    _ => Ok(replacement.clone()),
                }
            })
            .unwrap_err();
            assert!(error.downcast_ref::<SourceStampChanged>().is_some());
        }
    }

    #[test]
    fn local_case_probe_permission_and_stable_policy_errors_remain_fatal() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let probe = workspace.root().join("Proof.lean");
        fs::write(&probe, "def value := 10\n").unwrap();
        let mut step = 0;
        let error = filesystem_case_probe(&probe, true, |path| {
            step += 1;
            if step == 2 {
                Err(std::io::ErrorKind::PermissionDenied.into())
            } else {
                fs::metadata(path)
            }
        })
        .unwrap_err();
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        let policy = LocalFilesystemPolicy::at(workspace.root()).unwrap();
        let mismatch =
            LocalFilesystemPolicy { device: policy.device, folds_case: !policy.folds_case };
        let error = mismatch.check_directory(workspace.root(), true).unwrap_err();
        assert!(error.to_string().contains("directory case policy"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        let wrong_device = LocalFilesystemPolicy {
            device: policy.device.wrapping_add(1),
            folds_case: policy.folds_case,
        };
        let error = wrong_device.check_device(&fs::metadata(&probe).unwrap()).unwrap_err();
        assert!(error.to_string().contains("filesystem mount"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
    }

    #[test]
    fn local_case_probe_distinguishes_hard_links_from_case_aliases() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let source = workspace.root().join("src");
        fs::create_dir(&source).unwrap();
        let reference = source.join("data");
        fs::write(&reference, "saved non-module input").unwrap();
        let folds_case = workspace.folds_ascii_case().unwrap();
        let alternate = source.join("DATA");
        if !folds_case {
            fs::hard_link(&reference, &alternate).unwrap();
        }
        assert_eq!(
            physical_input_identity(&fs::metadata(&reference).unwrap()).unwrap(),
            physical_input_identity(&fs::metadata(&alternate).unwrap()).unwrap(),
        );
        assert_eq!(filesystem_folds_ascii_case(&reference).unwrap(), folds_case);
        assert_eq!(filesystem_folds_ascii_case(&alternate).unwrap(), folds_case);
        LocalFilesystemPolicy::at(workspace.root())
            .unwrap()
            .check_directory(&source, true)
            .unwrap();
        workspace.admit().unwrap();
        let stamp = workspace.source_stamp().unwrap();
        assert_eq!(workspace.source_stamp().unwrap(), stamp);
    }

    #[test]
    fn workspace_names_cannot_alias_sibling_lock_files() {
        let f = Fixture::new(&["Shared.A"]);
        for suffix in [".lock", ".server-lease", ".producer-lease"] {
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
        for suffix in [".LOCK", ".SERVER-LEASE", ".PRODUCER-LEASE"] {
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

    #[test]
    fn unicode_workspace_lock_suffixes_follow_physical_name_equivalence() {
        let f = Fixture::new(&["Shared.A"]);
        for (index, (suffix, reserved)) in [
            (".locK", ".lock"),
            (".ſerver-lease", ".server-lease"),
            (".server-leaſe", ".server-lease"),
            (".producer-leaſe", ".producer-lease"),
            ("．lock", ".lock"),
        ]
        .into_iter()
        .enumerate()
        {
            let probe = tempfile::tempdir_in(&f.base).unwrap();
            let canonical = probe.path().join(format!("victim{reserved}"));
            let candidate = probe.path().join(format!("victim{suffix}"));
            fs::create_dir(&canonical).unwrap();
            fs::create_dir_all(&candidate).unwrap();
            let aliases = physical_directory_identity(&fs::metadata(&canonical).unwrap()).unwrap()
                == physical_directory_identity(&fs::metadata(&candidate).unwrap()).unwrap();
            assert_eq!(reject_workspace_lock_name(&candidate, Some(&candidate)).is_err(), aliases);

            let root = f.base.join(format!("victim-{index}{suffix}"));
            let result = Workspace::create(&f.sdk, &root, &["src"]);
            assert_eq!(result.is_err(), aliases);
            if aliases {
                assert!(!root.exists());
            } else {
                result.unwrap().admit().unwrap();
            }
            let stage = f.base.join(format!("stage-{index}{suffix}"));
            let final_root = f.base.join(format!("final-{index}"));
            let result = Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]);
            assert_eq!(result.is_err(), aliases);
            if aliases {
                assert!(!stage.exists() && !final_root.exists());
            } else {
                Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn unicode_workspace_admission_preserves_read_only_parent_and_source_stamps() {
        use std::os::unix::fs::PermissionsExt as _;

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("read-only-parent");
        fs::create_dir(&parent).unwrap();
        let workspace = Workspace::create(
            &f.sdk,
            &parent.join("workspace é \"quoted\" \\f \u{8}\u{c}"),
            &["."],
        )
        .unwrap();
        configure_test_workspace(&workspace);
        fs::write(workspace.root().join("Proof.lean"), "def proof := 1\n").unwrap();
        let stamp = workspace.source_stamp().unwrap();
        let permissions = fs::metadata(&parent).unwrap().permissions();
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o555)).unwrap();
        let parent_before =
            directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap();
        let admission = Workspace::open(&f.sdk, workspace.root());
        let observed = workspace.source_stamp();
        let parent_after =
            directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap();
        fs::set_permissions(&parent, permissions).unwrap();
        admission.unwrap();
        assert_eq!(observed.unwrap(), stamp);
        assert_eq!(parent_after, parent_before);
    }

    #[cfg(unix)]
    #[test]
    fn unicode_workspace_leases_reuse_precreated_locks_under_read_only_parent() {
        use std::os::unix::fs::{
            DirBuilderExt as _, MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _,
        };

        fn lock_snapshot(path: &Path, server: bool) -> (Vec<u8>, Vec<u8>, u64) {
            let file = fs::File::open(path).unwrap();
            fs2::FileExt::lock_shared(&file).unwrap();
            let metadata = file.metadata().unwrap();
            let mut identity = if server {
                modification_identity(&metadata).unwrap()
            } else {
                physical_input_identity(&metadata).unwrap()
            };
            identity.extend_from_slice(&metadata.uid().to_le_bytes());
            identity.extend_from_slice(&metadata.gid().to_le_bytes());
            identity.extend_from_slice(&metadata.mode().to_le_bytes());
            (identity, fs::read(path).unwrap(), read_writer_witness(&file).unwrap())
        }

        // Other unit tests launch subprocesses concurrently. Keep this immediate
        // lock-release oracle in a process with no unrelated descriptor owners.
        const CHILD: &str = "ANNEAL_SDK_READ_ONLY_LEASE_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .arg("lean_sdk::tests::unicode_workspace_leases_reuse_precreated_locks_under_read_only_parent")
                .arg("--exact")
                .arg("--test-threads=1")
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(
                String::from_utf8_lossy(&output.stdout)
                    .contains("test result: ok. 1 passed; 0 failed;"),
                "Isolated lease oracle did not run exactly one test: {}",
                String::from_utf8_lossy(&output.stdout)
            );
            return;
        }

        struct RestoreParent<'a> {
            path: &'a Path,
            permissions: fs::Permissions,
            armed: bool,
        }
        impl Drop for RestoreParent<'_> {
            fn drop(&mut self) {
                if self.armed {
                    let _ = fs::set_permissions(self.path, self.permissions.clone());
                }
            }
        }

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("lease-parent");
        fs::create_dir(&parent).unwrap();
        let workspace = Workspace::create(&f.sdk, &parent.join("workspace-é"), &["."]).unwrap();
        configure_test_workspace(&workspace);
        fs::write(workspace.root().join("Proof.lean"), "def proof := 1\n").unwrap();
        let unbound = parent.join("unbound-é");
        fs::DirBuilder::new().mode(0o700).create(&unbound).unwrap();
        let lock_path = |root: &Path, suffix: &str| {
            let mut leaf = root.file_name().unwrap().to_os_string();
            leaf.push(suffix);
            root.with_file_name(leaf)
        };
        let locks = [
            lock_path(workspace.root(), ".lock"),
            lock_path(workspace.root(), ".server-lease"),
            lock_path(&unbound, ".lock"),
            lock_path(workspace.root(), ".producer-lease"),
            lock_path(&unbound, ".producer-lease"),
        ];
        for path in &locks {
            OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .unwrap();
        }
        // A first writer must also support a root that has no directory yet.
        let missing = parent.join("missing-é");
        drop(Workspace::lock_root(&missing).unwrap());
        assert!(!missing.exists());

        let permissions = fs::metadata(&parent).unwrap().permissions();
        let mut restore =
            RestoreParent { path: &parent, permissions: permissions.clone(), armed: true };
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o555)).unwrap();
        let observations: Result<_> = (|| {
            let parent_before = directory_modification_identity(&fs::metadata(&parent)?)?;
            let root_before = directory_modification_identity(&fs::metadata(workspace.root())?)?;
            let stamp_before = workspace.source_stamp()?;
            let mut lock_before = Vec::new();
            for (index, path) in locks.iter().enumerate() {
                lock_before.push(lock_snapshot(path, index == 1 || index >= 3));
            }
            // Raw generation locks may precede binding/owner creation.
            drop(Workspace::lock_root(&unbound)?);
            let mut checks = Vec::new();
            let writer = workspace.writer_lock()?;
            checks.push((
                "held writer blocks another writer",
                workspace.try_writer_lock()?.is_none(),
            ));
            checks.push(("held writer blocks a reader", workspace.try_shared_lock()?.is_none()));
            drop(writer);
            let first_reader =
                workspace.try_shared_lock()?.context("Reader blocked after writer release")?;
            let second_reader =
                workspace.try_shared_lock()?.context("Second shared reader blocked")?;
            checks.push(("shared readers block a writer", workspace.try_writer_lock()?.is_none()));
            drop(first_reader);
            checks
                .push(("remaining reader blocks a writer", workspace.try_writer_lock()?.is_none()));
            drop(second_reader);
            drop(
                workspace
                    .try_writer_lock()?
                    .context("Writer blocked after all readers released")?,
            );

            let server = workspace.server_lock()?;
            let contended = match workspace.server_lock() {
                Err(error) => error
                    .downcast_ref::<std::io::Error>()
                    .is_some_and(|error| error.kind() == std::io::ErrorKind::WouldBlock),
                Ok(unexpected) => {
                    drop(unexpected);
                    false
                }
            };
            checks.push(("held server excludes another server", contended));
            drop(workspace.try_writer_lock()?.context("Server lease incorrectly blocks a writer")?);
            drop(server);
            drop(workspace.server_lock()?);

            let mut lock_after = Vec::new();
            for (index, path) in locks.iter().enumerate() {
                let metadata = fs::metadata(path)?;
                checks.push((
                    "precreated lock remains protected regular file",
                    metadata.is_file() && metadata.permissions().mode() & 0o777 == 0o600,
                ));
                lock_after.push(lock_snapshot(path, index == 1 || index >= 3));
            }
            Ok((
                checks,
                parent_before,
                directory_modification_identity(&fs::metadata(&parent)?)?,
                root_before,
                directory_modification_identity(&fs::metadata(workspace.root())?)?,
                stamp_before,
                workspace.source_stamp()?,
                lock_before,
                lock_after,
            ))
        })();
        // Restore before inspecting fallible observations; the guard also
        // restores permissions if a called operation unexpectedly panics.
        let restored = fs::set_permissions(&parent, permissions);
        if restored.is_ok() {
            restore.armed = false;
        }
        drop(restore);
        restored.unwrap();
        let (
            checks,
            parent_before,
            parent_after,
            root_before,
            root_after,
            stamp_before,
            stamp_after,
            lock_before,
            lock_after,
        ) = observations.unwrap();
        for (reason, passed) in checks {
            assert!(passed, "{reason}");
        }
        assert_eq!(parent_after, parent_before);
        assert_eq!(root_after, root_before);
        assert_eq!(stamp_after, stamp_before);
        // Only writer history intentionally changes: three successful bound
        // writer acquisitions and one raw unbound root acquisition above.
        // Physical inode/device/owner/mode remain exact; shared reads do not
        // advance history. The separate server lease keeps its original full
        // modification identity and byte equality.
        assert_eq!(lock_after[1], lock_before[1]);
        assert_eq!(lock_after[3], lock_before[3]);
        assert_eq!(lock_after[4], lock_before[4]);
        for (index, increment) in [(0, 3), (2, 1)] {
            assert_eq!(lock_after[index].0, lock_before[index].0);
            assert_eq!(lock_after[index].2, lock_before[index].2 + increment);
            assert_eq!(lock_after[index].1.len(), 16);
        }
        assert!(!missing.exists());
        assert!(!unbound.join(BINDING).exists());
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
        let loader = f.sdk.inner.installation.join("loader:separator");
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
    fn workspace_namespace_requires_trusted_root_and_ancestor_owners() {
        let invoking_uid = workspace_lock_owner();
        let foreign_uid = invoking_uid.wrapping_add(1).max(1);
        check_workspace_namespace_identity(invoking_uid, 0o700, invoking_uid, true).unwrap();
        check_workspace_namespace_identity(0, 0o755, invoking_uid, false).unwrap();
        check_workspace_namespace_identity(invoking_uid, 0o1777, invoking_uid, false).unwrap();
        assert!(
            check_workspace_namespace_identity(foreign_uid, 0o700, invoking_uid, true).is_err()
        );
        assert!(
            check_workspace_namespace_identity(foreign_uid, 0o1777, invoking_uid, false).is_err()
        );
        assert!(
            check_workspace_namespace_identity(invoking_uid, 0o1777, invoking_uid, true).is_err()
        );
        for mode in [0o775, 0o757, 0o777] {
            assert!(
                check_workspace_namespace_identity(invoking_uid, mode, invoking_uid, false)
                    .is_err()
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn command_admission_rechecks_private_root_parent_and_grandparent_modes() {
        use std::os::unix::fs::PermissionsExt as _;

        let f = Fixture::new(&["Shared.A"]);
        let grandparent = f.base.join("namespace");
        let parent = grandparent.join("parent");
        fs::create_dir_all(&parent).unwrap();
        for path in [&grandparent, &parent] {
            fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        let workspace = Workspace::create(&f.sdk, &parent.join("workspace"), &["."]).unwrap();
        configure_test_workspace(&workspace);
        let binding = fs::read(workspace.root().join(BINDING)).unwrap();
        workspace.lake_command(LakeOperation::Version).unwrap();
        workspace.lean_command(LeanOperation::Version).unwrap();
        // The Workspace is already open. Every command must reject a newly
        // unsupported namespace before any launcher or Lakefile is executed.
        for path in [grandparent.as_path(), parent.as_path(), workspace.root()] {
            assert!(path.starts_with(&f.base));
            for mode in [0o775, 0o757, 0o777] {
                fs::set_permissions(path, fs::Permissions::from_mode(mode)).unwrap();
                for error in [
                    workspace.lake_command(LakeOperation::Version).unwrap_err(),
                    workspace.lean_command(LeanOperation::Version).unwrap_err(),
                ] {
                    assert!(format!("{error:#}").contains("workspace namespace"));
                    assert!(error.downcast_ref::<SourceStampChanged>().is_none());
                }
            }
            let restored = if path == workspace.root() { 0o700 } else { 0o755 };
            fs::set_permissions(path, fs::Permissions::from_mode(restored)).unwrap();
            workspace.lake_command(LakeOperation::Version).unwrap();
            workspace.lean_command(LeanOperation::Version).unwrap();
        }
        // Sticky ancestors protect each trusted child entry, including a
        // trusted intermediate directory below a writable grandparent.
        for path in [&grandparent, &parent] {
            fs::set_permissions(path, fs::Permissions::from_mode(0o1777)).unwrap();
        }
        workspace.lake_command(LakeOperation::Version).unwrap();
        workspace.lean_command(LeanOperation::Version).unwrap();
        assert_eq!(fs::read(workspace.root().join(BINDING)).unwrap(), binding);
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn command_admission_rechecks_darwin_namespace_acl_grants() {
        use std::os::unix::fs::PermissionsExt as _;

        let f = Fixture::new(&["Shared.A"]);
        let grandparent = f.base.join("acl-namespace");
        let parent = grandparent.join("parent");
        fs::create_dir_all(&parent).unwrap();
        let workspace = Workspace::create(&f.sdk, &parent.join("workspace"), &["."]).unwrap();
        configure_test_workspace(&workspace);
        let binding = fs::read(workspace.root().join(BINDING)).unwrap();
        for path in [grandparent.as_path(), parent.as_path(), workspace.root()] {
            assert!(path.starts_with(&f.base));
            let mode = fs::metadata(path).unwrap().permissions().mode();
            // A successfully retrieved empty ACL and read-only ALLOW entry
            // remain usable; the latter exercises Darwin's success=0 ABI.
            darwin_namespace_acl::install_test_entry(path, 1, 0);
            workspace.lake_command(LakeOperation::Version).unwrap();
            darwin_namespace_acl::install_test_entry(path, 1, (1 << 1) | (1 << 11));
            workspace.lean_command(LeanOperation::Version).unwrap();
            for bit in [2, 4, 5, 6, 8, 10, 12, 13] {
                darwin_namespace_acl::install_test_entry(path, 1, 1 << bit);
                assert_eq!(fs::metadata(path).unwrap().permissions().mode(), mode);
                for error in [
                    workspace.lake_command(LakeOperation::Version).unwrap_err(),
                    workspace.lean_command(LeanOperation::Version).unwrap_err(),
                ] {
                    assert!(error.to_string().contains("namespace ACL grants mutating access"));
                    assert!(error.downcast_ref::<SourceStampChanged>().is_none());
                }
            }
            // A DENY entry adds no capability. Restore a fresh empty ACL on
            // each private fixture before proceeding to the next ancestor.
            darwin_namespace_acl::install_test_entry(path, 2, 1 << 2);
            workspace.lake_command(LakeOperation::Version).unwrap();
            darwin_namespace_acl::install_test_entry(path, 1, 0);
            workspace.lean_command(LeanOperation::Version).unwrap();
        }
        assert_eq!(fs::read(workspace.root().join(BINDING)).unwrap(), binding);
    }

    #[cfg(unix)]
    #[test]
    fn workspace_locks_require_private_owner_and_stable_entries() {
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _};

        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        for server in [false, true] {
            let (file, path) = open_workspace_lock(workspace.root(), server).unwrap();
            let metadata = file.metadata().unwrap();
            assert_eq!(metadata.uid(), workspace_lock_owner());
            assert_eq!(metadata.permissions().mode() & 0o777, 0o600);
            let foreign =
                check_workspace_lock_metadata(&metadata, workspace_lock_owner().wrapping_add(1))
                    .unwrap_err();
            assert!(foreign.to_string().contains("owned by another user"));
            fs2::FileExt::lock_exclusive(&file).unwrap();
            for mode in [0o640, 0o604, 0o620, 0o602, 0o610, 0o601] {
                fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
                let error = if server {
                    workspace.server_lock().unwrap_err()
                } else {
                    let error = workspace.writer_lock().unwrap_err();
                    assert!(workspace.try_writer_lock().is_err());
                    assert!(workspace.try_shared_lock().is_err());
                    error
                };
                assert!(error.to_string().contains("exclude group and other access"));
                assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            }
            fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
            let moved = path.with_extension("preserved-lock");
            fs::rename(&path, &moved).unwrap();
            OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&path)
                .unwrap();
            let error = check_workspace_lock_entry(&file, &path).unwrap_err();
            assert_eq!(error.to_string(), "Workspace lock entry changed during acquisition");
            drop(file);
            fs::remove_file(path).unwrap();
            fs::remove_file(moved).unwrap();
        }
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

    #[cfg(unix)]
    #[test]
    fn bounded_sdk_and_workspace_inputs_reject_unconnected_fifos() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let mut paths = [BINDING, OUTPUT_OWNER, LAKE_CONFIGURATION, "lakefile.lean"]
            .map(|name| workspace.root().join(name))
            .to_vec();
        paths.extend(["sdk.json", "modules.json"].map(|name| f.sdk.root().join(name)));
        for path in paths {
            let bytes = fs::read(&path).unwrap();
            fs::remove_file(&path).unwrap();
            assert!(Command::new("mkfifo").arg(&path).status().unwrap().success());
            // No peer opens the FIFO. Admission must reject it rather than wait
            // for descriptor/configuration bytes or mistake it for a source race.
            let error = read_small(&path, MAX_MODULES_SIZE).unwrap_err();
            assert!(error.to_string().contains("not a regular file"));
            assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            assert!(Workspace::from_root(workspace.root()).is_err());
            if path != f.sdk.root().join("modules.json") {
                assert!(Workspace::open(&f.sdk, workspace.root()).is_err());
                let admission = workspace.admit().unwrap_err();
                assert!(admission.downcast_ref::<SourceStampChanged>().is_none());
                assert!(workspace.source_stamp().is_err());
                assert!(workspace.lake_command(LakeOperation::Build(&[])).is_err());
                assert!(workspace.lean_command(LeanOperation::Version).is_err());
            } else {
                // Existing SDK objects cache the immutable provider manifest;
                // its bounded read belongs to new SDK admission, not invocation.
                assert!(LeanSdk::load(f.sdk.root()).is_err());
            }
            fs::remove_file(&path).unwrap();
            fs::write(&path, bytes).unwrap();
            workspace.admit().unwrap();
        }
        let error = read_small(workspace.root(), MAX_DESCRIPTOR_SIZE).unwrap_err();
        assert!(error.to_string().contains("not a regular file"));
    }

    #[test]
    fn direct_sources_reject_physical_unicode_private_aliases() {
        for (alias, reserved) in [
            (".laKe", ".lake"),
            (".runtıme", PRIVATE_RUNTIME),
            (".gİt", ".git"),
            ("．lake", ".lake"),
            ("．runtime", PRIVATE_RUNTIME),
            ("．git", ".git"),
        ] {
            let f = Fixture::new(&["Shared.A"]);
            let workspace =
                Workspace::create(&f.sdk, &f.base.join("workspace"), &["user"]).unwrap();
            configure_test_workspace(&workspace);
            let private = workspace.root().join(reserved);
            if reserved == ".git" {
                fs::create_dir(&private).unwrap();
            }
            let canonical = private.join("Proof.lean");
            fs::write(&canonical, "def proof := 1\n").unwrap();
            let candidate = workspace.root().join(alias);
            let aliases = match fs::metadata(&candidate) {
                Ok(metadata) => {
                    physical_directory_identity(&metadata).unwrap()
                        == physical_directory_identity(&fs::metadata(&private).unwrap()).unwrap()
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
                Err(error) => panic!("Could not observe private alias {alias}: {error}"),
            };
            if !aliases {
                fs::create_dir(&candidate).unwrap();
                fs::write(candidate.join("Proof.lean"), "def proof := 1\n").unwrap();
            }
            workspace.admit().unwrap();
            let stamp = workspace.source_stamp().unwrap();
            fs::write(&canonical, "def proof := 2\n").unwrap();
            assert_eq!(workspace.source_stamp().unwrap(), stamp);
            let file = candidate.join("Proof.lean");
            let contains = workspace.contains_source(&file);
            let check = workspace.lean_command(LeanOperation::Check { file: &file, json: true });
            let setup = workspace.lake_command(LakeOperation::SetupFile(&file));
            assert_eq!(contains.is_ok(), !aliases, "private spelling {alias}");
            assert_eq!(check.is_ok(), !aliases, "private spelling {alias}");
            assert_eq!(setup.is_ok(), !aliases, "private spelling {alias}");
            if aliases {
                let error = contains.unwrap_err();
                assert!(error.to_string().contains("private output/cache"));
                assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            } else {
                assert!(contains.unwrap());
            }
        }
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

        let first_reader = wait_for_test_lock(|| first.try_shared_lock());
        let second_reader = second.try_shared_lock().unwrap().unwrap();
        assert!(first.try_writer_lock().unwrap().is_none());
        drop(first_reader);
        assert!(first.try_writer_lock().unwrap().is_none());
        drop(second_reader);
        let second_writer = wait_for_test_lock(|| second.try_writer_lock());
        assert!(first.try_writer_lock().unwrap().is_none());
        assert!(first.try_shared_lock().unwrap().is_none());
        drop(second_writer);
        drop(wait_for_test_lock(|| first.try_writer_lock()));
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

    #[cfg(unix)]
    #[test]
    fn fresh_destinations_reject_unsafe_ancestors_before_any_creation() {
        use std::os::unix::fs::PermissionsExt as _;
        let f = Fixture::new(&["Shared.A"]);
        let grandparent = f.base.join("destination-namespace");
        let parent = grandparent.join("parent");
        let stage_parent = f.base.join("stage-parent");
        fs::create_dir_all(&parent).unwrap();
        fs::create_dir(&stage_parent).unwrap();
        let stage = stage_parent.join("stage");
        let final_root = parent.join("workspace");
        for unsafe_ancestor in [&grandparent, &parent] {
            fs::set_permissions(unsafe_ancestor, fs::Permissions::from_mode(0o775)).unwrap();
            let parent_before =
                directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap();
            let stage_before =
                directory_modification_identity(&fs::metadata(&stage_parent).unwrap()).unwrap();
            assert!(Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).is_err());
            assert!(Workspace::create(&f.sdk, &final_root, &["src"]).is_err());
            assert!(!stage.exists() && !final_root.exists());
            // Also catch disposable policy/owner probes, not just residual roots.
            assert_eq!(
                directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap(),
                parent_before
            );
            assert_eq!(
                directory_modification_identity(&fs::metadata(&stage_parent).unwrap()).unwrap(),
                stage_before
            );
            fs::set_permissions(unsafe_ancestor, fs::Permissions::from_mode(0o755)).unwrap();
        }
        fs::set_permissions(&stage_parent, fs::Permissions::from_mode(0o775)).unwrap();
        let before =
            directory_modification_identity(&fs::metadata(&stage_parent).unwrap()).unwrap();
        assert!(Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).is_err());
        assert!(!stage.exists() && !final_root.exists());
        assert_eq!(
            directory_modification_identity(&fs::metadata(&stage_parent).unwrap()).unwrap(),
            before
        );
        fs::set_permissions(&stage_parent, fs::Permissions::from_mode(0o755)).unwrap();
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        Workspace::write_lakefile(
            &f.sdk,
            &stage,
            &[LakeLibrary { name: "Source", source_root: "src", modules: &[] }],
        )
        .unwrap();
        let binding = fs::read(stage.join(BINDING)).unwrap();
        fs::set_permissions(&grandparent, fs::Permissions::from_mode(0o775)).unwrap();
        assert!(Workspace::admit_stage(&f.sdk, &stage, &final_root).is_err());
        assert!(!final_root.exists());
        assert_eq!(fs::read(stage.join(BINDING)).unwrap(), binding);
        fs::set_permissions(&grandparent, fs::Permissions::from_mode(0o1777)).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
        fs::rename(&stage, &final_root).unwrap();
        let workspace = Workspace::open(&f.sdk, &final_root).unwrap();
        workspace.lake_command(LakeOperation::Version).unwrap();
        workspace.lean_command(LeanOperation::Version).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn fresh_destinations_reject_mutating_ancestor_acls_before_creation() {
        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("acl-destination");
        fs::create_dir(&parent).unwrap();
        let final_root = parent.join("workspace");
        darwin_namespace_acl::install_test_entry(&parent, 1, 1 << 2);
        let before = directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap();
        assert!(Workspace::create(&f.sdk, &final_root, &["src"]).is_err());
        assert!(!final_root.exists());
        assert_eq!(
            directory_modification_identity(&fs::metadata(&parent).unwrap()).unwrap(),
            before
        );
        darwin_namespace_acl::install_test_entry(&parent, 1, 1 << 1);
        let workspace = Workspace::create(&f.sdk, &final_root, &["src"]).unwrap();
        workspace.admit().unwrap();
    }

    #[test]
    fn fresh_stage_admission_validates_private_layout_and_owner() {
        let f = Fixture::new(&["Shared.A"]);
        for (index, damage) in ["lake", "runtime", "cache", "owner"].into_iter().enumerate() {
            let stage = f.base.join(format!("fresh-stage-{index}"));
            let final_root = f.base.join(format!("fresh-final-{index}"));
            Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
            Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
            let binding = fs::read(stage.join(BINDING)).unwrap();
            match damage {
                "lake" => fs::remove_dir_all(stage.join(".lake")).unwrap(),
                "runtime" => fs::remove_dir_all(stage.join(PRIVATE_RUNTIME)).unwrap(),
                "cache" => fs::remove_dir(stage.join(".runtime/cache")).unwrap(),
                "owner" => {
                    let mut owner: Binding = read_json(&stage.join(OUTPUT_OWNER)).unwrap();
                    owner.owner.push_str("-foreign");
                    fs::write(stage.join(OUTPUT_OWNER), serde_json::to_vec(&owner).unwrap())
                        .unwrap();
                }
                _ => unreachable!(),
            }
            let error = Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap_err();
            assert!(error.to_string().contains(if damage == "owner" {
                "Private output ownership mismatch"
            } else {
                "private"
            }));
            assert!(!final_root.exists());
            assert_eq!(fs::read(stage.join(BINDING)).unwrap(), binding);
        }
        // A complete untouched stage can be installed and opened immediately.
        let stage = f.base.join("complete-stage");
        let final_root = f.base.join("complete-final");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
        fs::rename(&stage, &final_root).unwrap();
        Workspace::open(&f.sdk, &final_root).unwrap().admit().unwrap();
    }

    #[test]
    fn saved_inputs_follow_physical_private_directory_aliases() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        for (reserved, alias) in
            [(".lake", ".laKe"), (PRIVATE_RUNTIME, ".runtİme"), (".git", ".gİt")]
        {
            let probe = tempfile::tempdir_in(&f.base).unwrap();
            fs::create_dir(probe.path().join(reserved)).unwrap();
            fs::create_dir_all(probe.path().join(alias)).unwrap();
            let aliases =
                physical_directory_identity(&fs::metadata(probe.path().join(reserved)).unwrap())
                    .unwrap()
                    == physical_directory_identity(
                        &fs::metadata(probe.path().join(alias)).unwrap(),
                    )
                    .unwrap();
            let private = workspace.root().join(reserved);
            let aliased = workspace.root().join(alias);
            if reserved == ".git" {
                fs::create_dir(&private).unwrap();
            }
            if aliases {
                fs::rename(&private, &aliased).unwrap();
                assert!(
                    fs::read_dir(workspace.root())
                        .unwrap()
                        .any(|entry| entry.unwrap().file_name() == alias)
                );
                workspace.admit().unwrap();
                let stamp = workspace.source_stamp().unwrap();
                // Compiled private outputs must remain excluded even when
                // read_dir preserves the filesystem-equivalent Unicode name.
                fs::write(aliased.join("Output.olean"), b"private output").unwrap();
                workspace.admit().unwrap();
                assert_eq!(workspace.source_stamp().unwrap(), stamp);
            } else {
                // On filesystems where this spelling is distinct, ordinary
                // non-ASCII local data must not be hidden as private output.
                fs::create_dir(&aliased).unwrap();
                fs::write(aliased.join("data.txt"), "one").unwrap();
                workspace.admit().unwrap();
                let stamp = workspace.source_stamp().unwrap();
                fs::write(aliased.join("data.txt"), "two").unwrap();
                assert_ne!(workspace.source_stamp().unwrap(), stamp);
            }
        }
    }

    #[test]
    fn replacement_stage_rejects_occupied_private_destinations_before_live_isolation() {
        let f = Fixture::new(&["Shared.A"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let _writer = workspace.writer_lock().unwrap();
        let live_stamp = workspace.source_stamp().unwrap();
        for (index, private) in [".lake", PRIVATE_RUNTIME].into_iter().enumerate() {
            for kind in ["empty", "nonempty", "file", "link"] {
                #[cfg(not(unix))]
                if kind == "link" {
                    continue;
                }
                let stage = f.base.join(format!("occupied-stage-{index}-{kind}"));
                Workspace::stage(
                    &f.sdk,
                    &stage,
                    workspace.root(),
                    Some(&workspace),
                    &["anneal", "generated", "user"],
                )
                .unwrap();
                let destination = stage.join(private);
                match kind {
                    "empty" => fs::create_dir(&destination).unwrap(),
                    "nonempty" => {
                        fs::create_dir(&destination).unwrap();
                        fs::write(destination.join("foreign"), "unowned output").unwrap();
                    }
                    "file" => fs::write(&destination, "not a directory").unwrap(),
                    #[cfg(unix)]
                    "link" => {
                        std::os::unix::fs::symlink(f.base.join("missing"), &destination).unwrap()
                    }
                    _ => unreachable!(),
                }
                let binding = fs::read(stage.join(BINDING)).unwrap();
                let error = Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap_err();
                assert!(error.to_string().contains("Replacement stage contains a private"));
                assert!(error.downcast_ref::<SourceStampChanged>().is_none());
                assert!(workspace.root().is_dir());
                assert!(!workspace.root().with_extension("previous").exists());
                assert_eq!(workspace.source_stamp().unwrap(), live_stamp);
                assert_eq!(fs::read(stage.join(BINDING)).unwrap(), binding);
                assert!(fs::symlink_metadata(&destination).is_ok());
                for (path, expected) in &sentinels {
                    assert_eq!(&fs::read(path).unwrap(), expected);
                }
            }
        }
        // A fresh workspace stage owns the private trees created by this API;
        // it does not receive outputs transferred from an existing workspace.
        let fresh = f.base.join("fresh-owned-stage");
        let final_root = f.base.join("fresh-owned-final");
        Workspace::stage(&f.sdk, &fresh, &final_root, None, &["src"]).unwrap();
        Workspace::admit_stage(&f.sdk, &fresh, &final_root).unwrap();
        let binding: Binding = read_json(&fresh.join(BINDING)).unwrap();
        assert_eq!(read_json::<Binding>(&fresh.join(OUTPUT_OWNER)).unwrap(), binding);
        assert!(fresh.join(".runtime/cache").is_dir());
        assert!(!final_root.exists());
    }

    #[test]
    fn local_source_root_aliases_require_bound_directory_identity() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        fs::create_dir(workspace.root().join("src")).unwrap();
        let source = workspace.root().join("src/Proof.lean");
        fs::write(&source, "def proof := 1\n").unwrap();
        let root_identity =
            physical_directory_identity(&fs::metadata(workspace.root()).unwrap()).unwrap();
        for name in ["WORKSPACE", "worKspace", "workſpace", "workspace-extra"] {
            let alias = workspace.root().with_file_name(name);
            let aliases = match fs::metadata(&alias) {
                Ok(metadata) => physical_directory_identity(&metadata).unwrap() == root_identity,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
                Err(error) => panic!("Could not observe workspace alias {name}: {error}"),
            };
            if name == "WORKSPACE" {
                assert_eq!(aliases, workspace.folds_ascii_case().unwrap());
            }
            if !aliases {
                fs::create_dir(&alias).unwrap();
                fs::create_dir(alias.join("src")).unwrap();
                // Identical file identity outside the bound directory does not
                // establish local containment, even with a similar root name.
                fs::hard_link(&source, alias.join("src/Proof.lean")).unwrap();
            }
            let file = alias.join("src/Proof.lean");
            assert_eq!(workspace.contains_source(&file).unwrap(), aliases);
            let lean = workspace.lean_command(LeanOperation::Check { file: &file, json: true });
            let lake = workspace.lake_command(LakeOperation::SetupFile(&file));
            if aliases {
                let lean = lean.unwrap();
                let lake = lake.unwrap();
                assert_eq!(lean.get_current_dir(), Some(workspace.root()));
                assert_eq!(lake.get_current_dir(), Some(workspace.root()));
                assert!(lean.get_args().any(|arg| arg == std::ffi::OsStr::new("src/Proof.lean")));
                assert!(lake.get_args().any(|arg| arg == source.as_os_str()));
            } else {
                assert!(lean.unwrap_err().to_string().contains("outside its workspace"));
                assert!(lake.unwrap_err().to_string().contains("outside its workspace"));
            }
        }
        #[cfg(unix)]
        {
            let linked_root = f.base.join("linked-workspace");
            std::os::unix::fs::symlink(workspace.root(), &linked_root).unwrap();
            let file = linked_root.join("src/Proof.lean");
            assert!(workspace.contains_source(&file).unwrap_err().to_string().contains("symlink"));
            assert!(
                workspace.lean_command(LeanOperation::Check { file: &file, json: true }).is_err()
            );
            assert!(workspace.lake_command(LakeOperation::SetupFile(&file)).is_err());
        }
        assert!(workspace.contains_source(&source).unwrap());
        workspace.admit().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn stage_admission_rejects_leaf_links_but_accepts_physical_parent_aliases() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("stage-parent");
        fs::create_dir(&parent).unwrap();
        let parent_alias = f.base.join("stage-parent-alias");
        symlink(&parent, &parent_alias).unwrap();
        let stage = parent_alias.join("stage");
        let final_root = parent_alias.join("final");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        let binding = fs::read(stage.join(BINDING)).unwrap();
        let owner = fs::read(stage.join(OUTPUT_OWNER)).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
        let leaf_link = parent_alias.join("leaf-link");
        symlink(parent.join("stage"), &leaf_link).unwrap();
        let error = Workspace::admit_stage(&f.sdk, &leaf_link, &final_root).unwrap_err();
        assert!(format!("{error:#}").contains("symlink"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        assert!(fs::symlink_metadata(&leaf_link).unwrap().file_type().is_symlink());
        assert_eq!(fs::read(stage.join(BINDING)).unwrap(), binding);
        assert_eq!(fs::read(stage.join(OUTPUT_OWNER)).unwrap(), owner);
        assert!(!final_root.exists());
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn lakefile_writer_rejects_leaf_links_but_accepts_parent_aliases() {
        use std::os::unix::fs::symlink;

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("configuration-parent");
        fs::create_dir(&parent).unwrap();
        let alias = f.base.join("configuration-parent-alias");
        symlink(&parent, &alias).unwrap();
        let stage = alias.join("stage");
        let final_root = alias.join("final");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        let libraries = [LakeLibrary { name: "Source", source_root: "src", modules: &[] }];
        Workspace::write_lakefile(&f.sdk, &stage, &libraries).unwrap();
        let preserved = [BINDING, OUTPUT_OWNER, LAKE_CONFIGURATION, "lakefile.lean"]
            .map(|relative| (relative, fs::read(stage.join(relative)).unwrap()));
        let before = directory_modification_identity(&fs::metadata(&stage).unwrap()).unwrap();
        let leaf = alias.join("stage-link");
        symlink(parent.join("stage"), &leaf).unwrap();
        let error = Workspace::write_lakefile(&f.sdk, &leaf, &libraries).unwrap_err();
        assert!(format!("{error:#}").contains("symlink"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        assert!(fs::symlink_metadata(&leaf).unwrap().file_type().is_symlink());
        assert_eq!(
            directory_modification_identity(&fs::metadata(&stage).unwrap()).unwrap(),
            before
        );
        for (relative, bytes) in preserved {
            assert_eq!(fs::read(stage.join(relative)).unwrap(), bytes);
        }
        // The stage binding names the final leaf, so this positive control also
        // ensures generation does not incorrectly use live Workspace::open.
        assert!(!final_root.exists());
        Workspace::write_lakefile(&f.sdk, &parent.join("stage"), &libraries).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
        let file = parent.join("not-a-directory");
        fs::write(&file, "ordinary data").unwrap();
        assert!(Workspace::write_lakefile(&f.sdk, &file, &libraries).is_err());
        assert_eq!(fs::read(&file).unwrap(), b"ordinary data");
    }

    #[test]
    fn replacement_stage_requires_complete_admitted_live_binding() {
        let f = Fixture::new(&["Shared.A"]);
        let (workspace, sentinels) = f.mapped_workspace_with_sentinels();
        let _writer = workspace.writer_lock().unwrap();
        let live_stamp = workspace.source_stamp().unwrap();
        for damage in ["owner", "source-roots"] {
            let stage = f.base.join(format!("binding-stage-{damage}"));
            Workspace::stage(
                &f.sdk,
                &stage,
                workspace.root(),
                Some(&workspace),
                &["anneal", "generated", "user"],
            )
            .unwrap();
            let mut binding: Binding = read_json(&stage.join(BINDING)).unwrap();
            if damage == "owner" {
                binding.owner.push_str("-different");
            } else {
                binding.source_roots.push(PathBuf::from("extra"));
            }
            fs::write(stage.join(BINDING), serde_json::to_vec(&binding).unwrap()).unwrap();
            let names = binding
                .source_roots
                .iter()
                .enumerate()
                .map(|(i, _)| format!("Stage{i}"))
                .collect::<Vec<_>>();
            let libraries = binding
                .source_roots
                .iter()
                .zip(&names)
                .map(|(root, name)| LakeLibrary {
                    name,
                    source_root: root.to_str().unwrap(),
                    modules: &[],
                })
                .collect::<Vec<_>>();
            // Keep configuration internally consistent, so only the missing
            // stage/live identity comparison could accept this replacement.
            Workspace::write_lakefile(&f.sdk, &stage, &libraries).unwrap();
            let stage_binding = fs::read(stage.join(BINDING)).unwrap();
            let error = Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap_err();
            assert!(error.to_string().contains("Replacement stage binding differs"));
            assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            assert_eq!(fs::read(stage.join(BINDING)).unwrap(), stage_binding);
            assert!(!stage.join(".lake").exists());
            assert!(!stage.join(PRIVATE_RUNTIME).exists());
            assert!(!workspace.root().with_extension("previous").exists());
            assert_eq!(workspace.source_stamp().unwrap(), live_stamp);
            for (path, bytes) in &sentinels {
                assert_eq!(&fs::read(path).unwrap(), bytes);
            }
        }
        let stage = f.base.join("live-admission-stage");
        Workspace::stage(
            &f.sdk,
            &stage,
            workspace.root(),
            Some(&workspace),
            &["anneal", "generated", "user"],
        )
        .unwrap();
        Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap();
        let owner_path = workspace.root().join(OUTPUT_OWNER);
        let owner_bytes = fs::read(&owner_path).unwrap();
        let mut owner = workspace.binding.clone();
        owner.owner.push_str("-foreign");
        let corrupt = serde_json::to_vec(&owner).unwrap();
        fs::write(&owner_path, &corrupt).unwrap();
        let error = Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap_err();
        assert!(error.to_string().contains("Private output ownership mismatch"));
        assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        assert_eq!(fs::read(&owner_path).unwrap(), corrupt);
        assert!(!stage.join(".lake").exists());
        assert!(!stage.join(PRIVATE_RUNTIME).exists());
        fs::write(&owner_path, owner_bytes).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, workspace.root()).unwrap();
        for (path, bytes) in sentinels {
            assert_eq!(fs::read(path).unwrap(), bytes);
        }
    }

    #[cfg(unix)]
    #[test]
    fn private_roots_reject_traversal_before_commands_configuration_or_stage_admission() {
        use std::os::unix::fs::PermissionsExt as _;

        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let preserved = [BINDING, OUTPUT_OWNER, LAKE_CONFIGURATION, "lakefile.lean"]
            .map(|relative| (relative, fs::read(workspace.root().join(relative)).unwrap()));
        let libraries = [
            LakeLibrary { name: "Source0", source_root: ".", modules: &[] },
            LakeLibrary { name: "Source1", source_root: "src", modules: &[] },
        ];
        let stage = f.base.join("traversal-stage");
        let final_root = f.base.join("traversal-final");
        Workspace::stage(&f.sdk, &stage, &final_root, None, &["src"]).unwrap();
        let stage_binding = fs::read(stage.join(BINDING)).unwrap();
        for mode in [0o755, 0o750, 0o711] {
            fs::set_permissions(workspace.root(), fs::Permissions::from_mode(mode)).unwrap();
            let before =
                directory_modification_identity(&fs::metadata(workspace.root()).unwrap()).unwrap();
            for error in [
                workspace.lake_command(LakeOperation::Version).unwrap_err(),
                workspace.lean_command(LeanOperation::Version).unwrap_err(),
                Workspace::write_lakefile(&f.sdk, workspace.root(), &libraries).unwrap_err(),
                Workspace::open(&f.sdk, workspace.root()).err().expect("traversable root admitted"),
            ] {
                assert!(
                    format!("{error:#}").contains("Workspace root permits group or other access")
                );
                assert!(error.downcast_ref::<SourceStampChanged>().is_none());
            }
            assert_eq!(
                directory_modification_identity(&fs::metadata(workspace.root()).unwrap()).unwrap(),
                before
            );
            assert_eq!(fs::metadata(workspace.root()).unwrap().permissions().mode() & 0o777, mode);
            for (relative, bytes) in &preserved {
                assert_eq!(&fs::read(workspace.root().join(relative)).unwrap(), bytes);
            }
            fs::set_permissions(&stage, fs::Permissions::from_mode(mode)).unwrap();
            let error = Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap_err();
            assert!(format!("{error:#}").contains("Workspace root permits group or other access"));
            assert!(!final_root.exists());
            assert_eq!(fs::read(stage.join(BINDING)).unwrap(), stage_binding);
        }
        fs::set_permissions(workspace.root(), fs::Permissions::from_mode(0o700)).unwrap();
        fs::set_permissions(&stage, fs::Permissions::from_mode(0o700)).unwrap();
        workspace.lake_command(LakeOperation::Version).unwrap();
        workspace.lean_command(LeanOperation::Version).unwrap();
        Workspace::write_lakefile(&f.sdk, workspace.root(), &libraries).unwrap();
        Workspace::admit_stage(&f.sdk, &stage, &final_root).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn darwin_search_acl_is_allowed_on_ancestors_but_not_private_roots() {
        use std::os::unix::fs::PermissionsExt as _;

        let f = Fixture::new(&["Shared.A"]);
        let parent = f.base.join("search-acl-parent");
        fs::create_dir(&parent).unwrap();
        let workspace = Workspace::create(&f.sdk, &parent.join("workspace"), &["src"]).unwrap();
        configure_test_workspace(&workspace);
        let preserved = [BINDING, OUTPUT_OWNER, LAKE_CONFIGURATION, "lakefile.lean"]
            .map(|relative| (relative, fs::read(workspace.root().join(relative)).unwrap()));
        // Only the invoking UID's fixture ACL is installed. Conservative policy
        // rejects root traversal grants without principal/deny-order reasoning.
        darwin_namespace_acl::install_test_entry(&parent, 1, 1 << 3);
        workspace.lake_command(LakeOperation::Version).unwrap();
        workspace.lean_command(LeanOperation::Version).unwrap();
        darwin_namespace_acl::install_test_entry(workspace.root(), 1, 1 << 3);
        assert_eq!(fs::metadata(workspace.root()).unwrap().permissions().mode() & 0o777, 0o700);
        let libraries = [LakeLibrary { name: "Source0", source_root: "src", modules: &[] }];
        for error in [
            workspace.lake_command(LakeOperation::Version).unwrap_err(),
            workspace.lean_command(LeanOperation::Version).unwrap_err(),
            Workspace::write_lakefile(&f.sdk, workspace.root(), &libraries).unwrap_err(),
        ] {
            assert!(error.to_string().contains("Workspace root ACL grants traversal access"));
            assert!(error.downcast_ref::<SourceStampChanged>().is_none());
        }
        for (relative, bytes) in preserved {
            assert_eq!(fs::read(workspace.root().join(relative)).unwrap(), bytes);
        }
        darwin_namespace_acl::install_test_entry(workspace.root(), 2, 1 << 3);
        // DENY is permitted by policy, but denying our own search can block
        // later command I/O. Check the native ACL policy before replacing it.
        darwin_namespace_acl::check(workspace.root(), true).unwrap();
        darwin_namespace_acl::install_test_entry(workspace.root(), 1, (1 << 1) | (1 << 11));
        workspace.lean_command(LeanOperation::Version).unwrap();
        darwin_namespace_acl::install_test_entry(workspace.root(), 1, 0);
        workspace.lake_command(LakeOperation::Version).unwrap();
    }

    #[test]
    fn cloned_sdk_shares_admitted_metadata_and_retains_descriptor_fences() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let selected = f.sdk.clone();
        assert!(Arc::ptr_eq(&selected.inner, &f.sdk.inner));
        let reopened = Workspace::open_bound(&selected, workspace.root()).unwrap();
        assert!(Arc::ptr_eq(&reopened.sdk().inner, &selected.inner));
        assert!(matches!(&reopened.sdk, Cow::Borrowed(_)));
        assert_eq!(reopened.sdk().root(), f.sdk.root());

        let descriptor = f.sdk.root().join("sdk.json");
        let mut changed: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor).unwrap()).unwrap();
        changed["compiler_hash"] = json!("c".repeat(40));
        fs::write(&descriptor, serde_json::to_vec(&changed).unwrap()).unwrap();
        assert!(reopened.lake_command(LakeOperation::Build(&[])).is_err());
        assert!(Workspace::open_bound(&selected, workspace.root()).is_err());
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
        let preserved = Workspace::open_bound(&second_sdk, workspace.root()).unwrap();
        assert_eq!(preserved.sdk().root(), f.sdk.root());
        assert_eq!(preserved.sdk().id(), second_sdk.id());
        assert!(matches!(&preserved.sdk, Cow::Owned(_)));
        assert_eq!(
            preserved.lean_command(LeanOperation::Version).unwrap().get_program(),
            f.sdk.root().join("bin/lean")
        );
        let descriptor = second_root.join("sdk.json");
        let mut changed: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor).unwrap()).unwrap();
        changed["id"] = json!("c".repeat(64));
        fs::write(&descriptor, serde_json::to_vec(&changed).unwrap()).unwrap();
        let upgraded = LeanSdk::load(&second_root).unwrap();
        assert_eq!(
            Workspace::open_bound(&upgraded, workspace.root()).err().unwrap().to_string(),
            "Workspace SDK identity changed"
        );
        // Restore the fixture's selected descriptor for the separate workspace
        // creation below; the original bound installation was never modified.
        fs::copy(f.sdk.root().join("sdk.json"), &descriptor).unwrap();
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
        fs::rename(&f.sdk.inner.installation, &installation).unwrap();
        let error = LeanSdk::load(&installation.join("lean-sdk")).unwrap_err();
        assert_eq!(error.to_string(), "Lean SDK root must be UTF-8");
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn sdk_admission_rejects_a_plugin_resolving_to_non_utf8_bytes() {
        use std::os::unix::{ffi::OsStringExt as _, fs::symlink};
        let f = Fixture::new(&["Shared.A"]);
        let plugin =
            f.sdk.inner.installation.join(std::ffi::OsString::from_vec(b"plugin-\xff.so".to_vec()));
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
        let plugin_path = f.sdk.root().join("lib/native plugin.so");
        Arc::get_mut(&mut f.sdk.inner)
            .unwrap()
            .plugins
            .push(Plugin { path: plugin_path, name: "nativePlugin".into() });
        fs::write(&f.sdk.inner.plugins[0].path, "immutable fixture native plugin").unwrap();
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
            ["--keep-toolchain", "--no-cache", "serve"]
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
            ["--keep-toolchain", "--no-cache", "build", "+Proof:olean"]
        );
        let setup =
            workspace.lake_command(LakeOperation::SetupFile(Path::new("src/Proof.lean"))).unwrap();
        assert_eq!(
            setup.get_args().collect::<Vec<_>>(),
            [
                std::ffi::OsStr::new("--keep-toolchain"),
                std::ffi::OsStr::new("--no-cache"),
                std::ffi::OsStr::new("setup-file"),
                workspace.root().join("src/Proof.lean").as_os_str(),
            ]
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

    #[test]
    fn stock_lake_operations_recheck_the_complete_manifest_after_admission() {
        let f = Fixture::new(&["Shared.A"]);
        let workspace = f.workspace();
        let proof = workspace.root().join("Proof.lean");
        fs::write(&proof, "example : True := by trivial\n").unwrap();
        workspace.admit().unwrap();
        let manifest_path = workspace.root().join("lake-manifest.json");
        let original = fs::read(&manifest_path).unwrap();
        let baseline: serde_json::Value = serde_json::from_slice(&original).unwrap();
        let command = |operation| match operation {
            0 => workspace.lake_command(LakeOperation::Build(&[])),
            1 => workspace.lake_command(LakeOperation::SetupFile(&proof)),
            2 => workspace.lake_command(LakeOperation::Serve),
            _ => unreachable!(),
        };
        for operation in 0..3 {
            command(operation).unwrap();
        }

        // Stock Lake emits the same manifest with an explicit default policy
        // field and different formatting. Both forms preserve the fixed layout.
        let mut stock = baseline.clone();
        stock["fixedToolchain"] = json!(false);
        fs::write(&manifest_path, serde_json::to_vec_pretty(&stock).unwrap()).unwrap();
        for operation in 0..3 {
            command(operation).unwrap();
        }

        let mut rejected = Vec::new();
        for (field, value) in [
            ("version", json!("1.3.0")),
            ("packages", json!([{"name": "foreign", "type": "path", "dir": "../foreign"}])),
            ("lakeDir", json!("../foreign-output")),
            ("packagesDir", json!("../foreign-packages")),
            ("packagesDir", serde_json::Value::Null),
            ("name", json!("foreign-package")),
            ("fixedToolchain", json!(true)),
            ("fixedToolchain", serde_json::Value::Null),
            ("unknownField", json!("unsupported policy")),
        ] {
            let mut changed = baseline.clone();
            changed[field] = value;
            rejected.push((field.to_owned(), serde_json::to_vec(&changed).unwrap()));
        }
        for field in ["version", "packages", "lakeDir", "packagesDir", "name"] {
            let mut changed = baseline.clone();
            changed.as_object_mut().unwrap().remove(field);
            rejected.push((format!("missing {field}"), serde_json::to_vec(&changed).unwrap()));
        }
        rejected.push(("malformed JSON".into(), b"not a manifest".to_vec()));
        rejected.push((
            "duplicate field".into(),
            br#"{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"anneal_verification","lakeDir":"../foreign","lakeDir":".lake"}"#.to_vec(),
        ));
        for (case, bytes) in rejected {
            fs::write(&manifest_path, &bytes).unwrap();
            for operation in 0..3 {
                assert!(command(operation).is_err(), "Accepted {case} in operation {operation}");
            }
            assert_eq!(fs::read(&manifest_path).unwrap(), bytes, "Repaired {case}");
            // RC2 handles --version before loading workspace configuration.
            // Keep this inspection route available without consuming a manifest.
            let version = workspace.lake_command(LakeOperation::Version).unwrap();
            assert_eq!(version.get_args().collect::<Vec<_>>(), ["--version"]);
        }
        fs::remove_file(&manifest_path).unwrap();
        for operation in 0..3 {
            assert!(
                command(operation).is_err(),
                "Accepted absent manifest in operation {operation}"
            );
        }
        assert!(!manifest_path.exists(), "Lake admission recreated a missing manifest");
        workspace.lake_command(LakeOperation::Version).unwrap();
        fs::write(&manifest_path, &original).unwrap();
        for operation in 0..3 {
            command(operation).unwrap();
        }
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

    #[cfg(unix)]
    #[test]
    fn finite_descriptor_admission_preserves_stock_routes() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let f = Fixture::new(&["Shared.A"]);
        let root = f.sdk.root();
        let descriptor_path = root.join("sdk.json");
        let legacy: serde_json::Value =
            serde_json::from_slice(&fs::read(&descriptor_path).unwrap()).unwrap();
        // Legacy admission requires no optional helper or manifest.
        assert!(LeanSdk::load(root).is_ok());
        let helper_path = root.join("bin/anneal-finite-lake");
        assert!(!helper_path.exists());
        let bytes = b"#!/bin/sh\nexit 2\n";
        fs::write(&helper_path, bytes).unwrap();
        fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o755)).unwrap();
        let mut valid = legacy.clone();
        valid["schema"] = json!(2);
        valid["finite_lake"] = json!({"path":"bin/anneal-finite-lake",
            "sha256":sha256(bytes),"protocol":1});
        let write = |descriptor: &serde_json::Value| {
            fs::write(&descriptor_path, serde_json::to_vec(descriptor).unwrap()).unwrap();
        };
        write(&valid);
        let sdk = LeanSdk::load(root).unwrap();
        // SDK2 is usable through stock commands before protocol integration.
        let workspace = Workspace::create(&sdk, &f.base.join("sdk2-stock"), &["."]).unwrap();
        configure_test_workspace(&workspace);
        let command = workspace.lake_command(LakeOperation::Build(&["Source0".into()])).unwrap();
        assert_eq!(command.get_program(), root.join("bin/lake").as_os_str());
        assert_eq!(
            command.get_args().collect::<Vec<_>>(),
            ["--keep-toolchain", "--no-cache", "build", "Source0"]
        );

        let mut unknown_schema = valid.clone();
        unknown_schema["schema"] = json!(3);
        let mut missing = valid.clone();
        missing.as_object_mut().unwrap().remove("finite_lake");
        let mut null = valid.clone();
        null["finite_lake"] = serde_json::Value::Null;
        let mut legacy_helper = valid.clone();
        legacy_helper["schema"] = json!(1);
        let mut legacy_null = legacy.clone();
        legacy_null["finite_lake"] = serde_json::Value::Null;
        let mut bad_protocol = valid.clone();
        bad_protocol["finite_lake"]["protocol"] = json!(2);
        let mut bad_path = valid.clone();
        bad_path["finite_lake"]["path"] = json!("../lean/bin/anneal-finite-lake");
        let mut malformed_hash = valid.clone();
        malformed_hash["finite_lake"]["sha256"] = json!("A".repeat(64));
        let mut wrong_hash = valid.clone();
        wrong_hash["finite_lake"]["sha256"] = json!("a".repeat(64));
        let mut unknown_field = valid.clone();
        unknown_field["finite_lake"]["extra"] = json!(true);
        for (label, descriptor) in [
            ("schema", unknown_schema),
            ("missing", missing),
            ("null", null),
            ("legacy helper", legacy_helper),
            ("legacy null", legacy_null),
            ("protocol", bad_protocol),
            ("path", bad_path),
            ("malformed hash", malformed_hash),
            ("wrong hash", wrong_hash),
            ("unknown field", unknown_field),
        ] {
            write(&descriptor);
            assert!(LeanSdk::load(root).is_err(), "Accepted {label}");
        }
        write(&valid);
        fs::write(&helper_path, b"#!/bin/sh\nexit 0\n").unwrap();
        assert!(LeanSdk::load(root).is_err(), "Accepted changed helper bytes");
        fs::write(&helper_path, bytes).unwrap();
        fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(LeanSdk::load(root).is_err(), "Accepted non-executable helper");
        fs::remove_file(&helper_path).unwrap();
        assert!(LeanSdk::load(root).is_err(), "Accepted missing helper");
        let alternate = root.join("bin/retained-helper");
        fs::write(&alternate, bytes).unwrap();
        fs::set_permissions(&alternate, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&alternate, &helper_path).unwrap();
        assert!(LeanSdk::load(root).is_err(), "Accepted linked helper");
        assert!(sdk.check_descriptor().is_err(), "Missed admitted launcher retarget");
        fs::remove_file(&helper_path).unwrap();
        symlink(root.join("missing-helper"), &helper_path).unwrap();
        assert!(LeanSdk::load(root).is_err(), "Accepted dangling helper");
        fs::remove_file(&helper_path).unwrap();
        fs::write(&helper_path, bytes).unwrap();
        fs::set_permissions(&helper_path, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(LeanSdk::load(root).is_ok());
        write(&legacy);
        assert!(LeanSdk::load(root).is_ok());
    }
}
