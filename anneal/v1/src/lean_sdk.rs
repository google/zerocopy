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
const MAX_DESCRIPTOR_SIZE: u64 = 64 * 1024;
const MAX_MODULES_SIZE: u64 = 32 * 1024 * 1024;

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
        for name in manifest.modules {
            ensure!(valid_module(&name), "Invalid SDK module identity: {name}");
            ensure!(modules.insert(name.clone()), "Duplicate exact SDK module: {name}");
        }
        Ok(Self {
            root,
            installation,
            descriptor_sha256: sha256(&raw),
            descriptor,
            modules,
            imports,
            sources,
            loaders,
            plugins,
        })
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
        let mut local_modules = BTreeSet::new();
        for source in &binding.source_roots {
            let source = stage.join(source);
            if source.try_exists()? {
                check_local_sources(&source, &source, stage, &sdk.modules, &mut local_modules)?;
            }
        }
        // Also establish that every saved input will be tracked on invocation.
        saved_inputs(stage)?;
        Ok(())
    }

    pub fn open(sdk: &'a LeanSdk, root: &Path) -> Result<Self> {
        let root = fs::canonicalize(root).context("Unknown Lean workspace")?;
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
        let file = open_workspace_lock(root)?;
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
        let mut leaf = self.root.file_name().context("Workspace has no leaf")?.to_os_string();
        leaf.push(".server");
        let file = open_workspace_lock(&self.root.with_file_name(leaf))?;
        fs2::FileExt::try_lock_exclusive(&file)
            .context("An editor coordinator already owns this workspace; close it before starting another")?;
        Ok(file)
    }

    fn try_lock(&self, shared: bool) -> Result<Option<fs::File>> {
        let file = open_workspace_lock(&self.root)?;
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
            if root == *source { return Ok(true); }
            for module in &self.sdk.modules {
                let file = source.join(module.replace('.', "/")).with_extension("lean");
                if let Ok(file) = fs::canonicalize(file) {
                    if file.starts_with(&root) { return Ok(true); }
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

    /// Fingerprint the saved local Lean inputs and Lake configuration. Compare
    /// stamps around builds and checks before accepting their results as current.
    /// Private incremental outputs and caches are deliberately excluded. File
    /// modification identities also catch ordinary edit-and-restore races.
    pub fn source_stamp(&self) -> Result<[u8; 32]> {
        self.admit()?;
        let inputs = saved_inputs(&self.root)?;
        let mut hasher = Sha256::new();
        for path in &inputs {
            reject_links(path)?;
            let relative = path.strip_prefix(&self.root)?.as_os_str().as_encoded_bytes();
            hasher.update((relative.len() as u64).to_le_bytes());
            hasher.update(relative);
            let mut file = fs::File::open(path)
                .with_context(|| format!("Saved input disappeared: {}", path.display()))?;
            let before = modification_identity(&file.metadata()?)?;
            hasher.update((before.len() as u64).to_le_bytes());
            hasher.update(&before);
            let mut buffer = [0u8; 64 * 1024];
            loop {
                let count = file.read(&mut buffer)?;
                if count == 0 {
                    break;
                }
                hasher.update(&buffer[..count]);
            }
            ensure!(
                before == modification_identity(&file.metadata()?)?
                    && before == modification_identity(&fs::metadata(path)?)?,
                "Saved Lean input changed while recording its state: {}",
                path.display()
            );
        }
        ensure!(
            inputs == saved_inputs(&self.root)?,
            "Saved Lean input set changed while recording its state"
        );
        Ok(hasher.finalize().into())
    }

    /// Recheck ownership at an invocation or private-output transfer boundary.
    pub fn admit(&self) -> Result<()> {
        self.sdk.check_descriptor()?;
        reject_links(&self.root)?;
        ensure!(self.root.is_dir(), "Workspace disappeared");
        let binding: Binding = read_json(&self.root.join(BINDING))?;
        ensure!(binding == self.binding, "Workspace binding changed after opening");
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
        for source in &binding.source_roots {
            let source = self.root.join(source);
            if source.try_exists()? {
                check_local_sources(&source, &source, &self.root, &self.sdk.modules, &mut local_modules)?;
            }
        }
        Ok(())
    }

    pub fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
        let mut command = self.command("lake")?;
        command.args(["--keep-toolchain", "--no-cache"]);
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
                command.arg(self.local_source(file)?);
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
        ensure!(
            file.is_file() && file.extension().is_some_and(|s| s == "lean"),
            "Expected an existing local Lean source"
        );
        ensure!(file.strip_prefix(&self.root)?.components().all(|part| {
            !matches!(part, Component::Normal(name) if [".lake", PRIVATE_RUNTIME, ".git"].iter().any(|s| name == *s))
        }), "Source must not come from ignored private output/cache trees");
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
        let mut paths = vec![self.sdk.root.join("bin")];
        paths.extend(["/usr/bin", "/bin", "/usr/sbin", "/sbin"].map(PathBuf::from));
        command.env("PATH", std::env::join_paths(paths)?);
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
        let imports = std::iter::once(self.root.join(".lake/build/lib/lean"))
            .chain(self.sdk.imports.iter().cloned());
        command.env("LEAN_PATH", std::env::join_paths(imports)?);
        let sources = self
            .binding
            .source_roots
            .iter()
            .map(|p| self.root.join(p))
            .chain(self.sdk.sources.iter().cloned());
        command.env("LEAN_SRC_PATH", std::env::join_paths(sources)?);
        let loaders = std::env::join_paths(&self.sdk.loaders)?;
        command.env("LD_LIBRARY_PATH", &loaders);
        command.env("DYLD_LIBRARY_PATH", loaders);
        Ok(command)
    }
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

fn open_workspace_lock(root: &Path) -> Result<fs::File> {
    let root = new_physical_path(root)?;
    let mut leaf = root.file_name().context("Workspace has no leaf")?.to_os_string();
    leaf.push(".lock");
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
    reject_links(&path)?;
    Ok(path)
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
    modules: &BTreeSet<String>,
    local_modules: &mut BTreeSet<String>,
) -> Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    ensure!(metadata.is_dir(), "Local source root is not a real directory");
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let name = entry.file_name();
        if [".lake", PRIVATE_RUNTIME, ".git"].iter().any(|s| name == *s) {
            ensure!(path == workspace_root, "Reserved output/cache directory inside a source root: {}", entry.path().display());
            continue;
        }
        let kind = entry.file_type()?;
        ensure!(!kind.is_symlink(), "Local source contains a symlink: {}", entry.path().display());
        if kind.is_dir() {
            check_local_sources(&entry.path(), source_root, workspace_root, modules, local_modules)?;
        } else if kind.is_file() {
            let path = entry.path();
            let filename = name.to_string_lossy();
            ensure!(
                ![".olean", ".olean.private", ".olean.server", ".ilean", ".ir"]
                    .iter()
                    .any(|suffix| filename.ends_with(suffix)),
                "Compiled input outside owned .lake outputs: {}",
                path.display()
            );
            if path.extension().is_some_and(|s| s == "lean") {
                let relative = path.strip_prefix(source_root)?.with_extension("");
                let name = relative
                    .iter()
                    .map(|s| s.to_str().context("Non-UTF8 Lean module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                ensure!(!modules.contains(&name), "Local/SDK exact module collision: {name}");
                ensure!(
                    local_modules.insert(name.clone()),
                    "Duplicate local module provider: {name}"
                );
            }
        }
    }
    Ok(())
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
    fn collect(path: &Path, root: &Path, inputs: &mut BTreeSet<PathBuf>) -> Result<()> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let name = entry.file_name();
            if [".lake", PRIVATE_RUNTIME, ".git"].iter().any(|s| name == *s) {
                continue;
            }
            let kind = entry.file_type()?;
            ensure!(
                !kind.is_symlink(),
                "Saved source tree contains a symlink: {}",
                entry.path().display()
            );
            if kind.is_dir() {
                collect(&entry.path(), root, inputs)?;
            } else if kind.is_file()
                && (entry.path().extension().is_some_and(|s| s == "lean")
                    || (path == root
                        && ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]
                            .iter()
                            .any(|s| name == *s)))
            {
                inputs.insert(entry.path());
            }
        }
        Ok(())
    }
    let mut inputs = BTreeSet::new();
    collect(root, root, &mut inputs)?;
    Ok(inputs)
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
    use super::*;
    use serde_json::json;

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
            Workspace::create(&self.sdk, &self.base.join("workspace"), &[".", "src"]).unwrap()
        }

        fn mapped_workspace_with_sentinels(&self) -> (Workspace<'_>, Vec<(PathBuf, Vec<u8>)>) {
            let workspace = Workspace::create(
                &self.sdk,
                &self.base.join("mapped-workspace"),
                &["anneal", "generated", "user"],
            )
            .unwrap();
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
        fs::write(workspace.root().join("lakefile.toml"), "name = 'changed'\n").unwrap();
        assert_ne!(edited, workspace.source_stamp().unwrap());
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
