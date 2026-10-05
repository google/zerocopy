// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Finite private VS Code commands. The caller executes and records each command,
//! checks installation success, then launches. This module does not run subjects.

use std::{
    cell::Cell,
    ffi::OsString,
    fs::{self, File, OpenOptions},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output, Stdio},
};

use anyhow::{Context, Result, ensure};
use serde_json::json;
use sha2::{Digest as _, Sha256};

use crate::lean_sdk::Workspace;

// Include the temporary root and every intermediate/leaf directory whose
// paths are passed to Code, so preparation and invocation share one inventory.
const PROFILE_DIRECTORIES: [&str; 13] = [
    "",
    "home",
    "elan",
    "config",
    "cache",
    "xdg-data",
    "tmp",
    "data",
    "data/user-data",
    "data/user-data/User",
    "data/extensions",
    "data/tmp",
    "vsix",
];

// These are the generated controls the stock editor or its wrappers can read
// after the launch-time validation has finished. Optional generated Lake and
// toolchain inputs are protected when present; the protected workspace root
// prevents another account from creating absent entries during the session.
const REQUIRED_WORKSPACE_CONTROLS: [&str; 4] =
    [".anneal-sdk.json", ".anneal-bin/lean", ".anneal-bin/lake", ".vscode/settings.json"];
const OPTIONAL_WORKSPACE_CONTROLS: [&str; 3] =
    ["lean-toolchain", ".anneal-lake.json", "lakefile.lean"];

/// A fresh editor instance bound to exactly one production workspace. Its state
/// persists after the CLI exits; it must not be removed while Code is running.
pub struct EditorHost<'w, 'sdk> {
    workspace: &'w Workspace<'sdk>,
    profile: Profile,
    version_accepted: Cell<bool>,
}

impl<'w, 'sdk> EditorHost<'w, 'sdk> {
    /// `code` is the absolute trusted desktop Code CLI, and every extension is an
    /// explicit local VSIX, including dependencies. No Gallery identifiers.
    pub fn prepare(
        workspace: &'w Workspace<'sdk>,
        code: &Path,
        extensions: &[PathBuf],
        state_dir: Option<&Path>,
    ) -> Result<Self> {
        ensure!(
            cfg!(target_os = "macos"),
            "The private editor launcher currently supports macOS only"
        );
        workspace.admit()?;
        let profile = Profile::prepare_at(
            workspace.root(),
            workspace.sdk().root(),
            code,
            extensions,
            state_dir,
        )?;
        Ok(Self { workspace, profile, version_accepted: Cell::new(false) })
    }

    pub fn profile_root(&self) -> &Path {
        &self.profile.root
    }

    /// Recheck after command construction and immediately before the caller
    /// invokes Code, including each previously constructed installation command.
    pub(crate) fn validate_before_command(&self) -> Result<()> {
        self.workspace.admit()?;
        self.profile.check_owner(self.workspace.root(), self.workspace.sdk().root())
    }

    /// Record the actual selected editor version before using its CLI contract.
    pub fn version_command(&self) -> Result<Command> {
        self.workspace.admit()?;
        let mut command = self.profile.command()?;
        command.arg("--version");
        Ok(command)
    }

    /// Admit the observed version response before any extension or GUI command.
    pub(crate) fn accept_version_output(&self, output: &Output) -> Result<()> {
        admit_code_version(&self.version_accepted, output)
    }

    fn require_version(&self) -> Result<()> {
        require_code_version(&self.version_accepted)
    }

    /// Execute sequentially, retaining nonzero failures. Every dependency must
    /// have been supplied explicitly; automatic pack/dependency fetching is off.
    pub fn install_commands(&self) -> Result<Vec<Command>> {
        self.require_version()?;
        self.workspace.admit()?;
        (0..self.profile.extensions.len())
            .map(|index| self.profile.install_command(index))
            .collect()
    }

    /// The caller must first complete all installation commands. An empty or
    /// incomplete extension profile cannot silently fall back to global state.
    pub fn launch_command(&self) -> Result<Command> {
        self.require_version()?;
        self.workspace.admit()?;
        self.profile.check_required_extensions()?;
        // The macOS shell CLI dispatches through LaunchServices and can detach
        // the GUI from its caller. Start the bundle executable directly so the
        // caller owns the editor process and can wait for or terminate it.
        let mut command = self.profile.command_for(&self.profile.gui.path)?;
        command
            .args([
                "--new-window",
                "--sync",
                "off",
                "--skip-add-to-recently-opened",
                "--use-inmemory-secretstorage",
            ])
            .args([
                "--disable-extension",
                "vscode.git",
                "--disable-extension",
                "vscode.github",
                "--disable-extension",
                "vscode.github-authentication",
                "--disable-extension",
                "vscode.microsoft-authentication",
            ])
            .arg(self.workspace.root());
        Ok(command)
    }
}

struct Profile {
    root: PathBuf,
    parent_directories: Vec<(PathBuf, DirectoryIdentity)>,
    root_identity: DirectoryIdentity,
    workspace: PathBuf,
    workspace_directories: Vec<(PathBuf, DirectoryIdentity)>,
    workspace_controls: Vec<ProtectedFile>,
    sdk: PathBuf,
    gateway: ProtectedFile,
    code: ProtectedFile,
    gui: ProtectedFile,
    bundle: Option<ProtectedBundle>,
    extensions: Vec<ExtensionSnapshot>,
    path: OsString,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct DirectoryIdentity {
    device: u64,
    inode: u64,
    owner: u32,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct FileIdentity {
    device: u64,
    inode: u64,
    owner: u32,
}

struct ExtensionSnapshot {
    source: PathBuf,
    private_path: PathBuf,
    identity: FileIdentity,
    sha256: [u8; 32],
}

struct ProtectedFile {
    path: PathBuf,
    identity: FileIdentity,
    directories: Vec<(PathBuf, DirectoryIdentity)>,
    executable: bool,
}

struct ProtectedBundle {
    root: PathBuf,
    parent_directories: Vec<(PathBuf, DirectoryIdentity)>,
    entries: Vec<BundleEntry>,
}

#[derive(Eq, PartialEq)]
struct BundleEntry {
    relative: PathBuf,
    identity: FileIdentity,
    kind: BundleEntryKind,
    target: Option<PathBuf>,
}

#[derive(Eq, PartialEq)]
enum BundleEntryKind {
    Directory,
    File,
    Symlink,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum DirectoryPurpose {
    PrivateState,
    ProtectedControl,
}

#[cfg(unix)]
fn effective_uid() -> u32 {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    // SAFETY: geteuid takes no arguments and returns the process's effective UID.
    unsafe { geteuid() }
}

#[cfg(unix)]
fn require_effective_execute(path: &Path) -> Result<()> {
    // The stock launcher is macOS-only; Linux keeps the inert Unix fixtures
    // useful. These constants are the platforms' fcntl.h AT_* values.
    #[cfg(target_os = "macos")]
    const AT_FDCWD: i32 = -2;
    #[cfg(target_os = "linux")]
    const AT_FDCWD: i32 = -100;
    #[cfg(target_os = "macos")]
    const AT_EACCESS: i32 = 0x0010;
    #[cfg(target_os = "linux")]
    const AT_EACCESS: i32 = 0x0200;
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = path;
        anyhow::bail!("Editor executable access checks are unsupported on this Unix platform");
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    {
        use std::{ffi::CString, os::unix::ffi::OsStrExt};

        unsafe extern "C" {
            fn faccessat(fd: i32, path: *const std::ffi::c_char, mode: i32, flags: i32) -> i32;
        }
        let path_bytes = CString::new(path.as_os_str().as_bytes())
            .context("Editor executable path contains a NUL byte")?;
        // SAFETY: path_bytes is a valid NUL-terminated path and remains alive
        // across this non-mutating access check. X_OK is 1 on both platforms.
        let status = unsafe { faccessat(AT_FDCWD, path_bytes.as_ptr(), 1, AT_EACCESS) };
        ensure!(
            status == 0,
            "Editor executable is inaccessible to the invoking user: {}: {}",
            path.display(),
            std::io::Error::last_os_error()
        );
        Ok(())
    }
}

#[cfg(unix)]
fn directory_identity(path: &Path) -> Result<DirectoryIdentity> {
    use std::os::unix::fs::MetadataExt;

    let metadata = fs::symlink_metadata(path)?;
    ensure!(
        metadata.is_dir(),
        "Private editor profile directory is not physical: {}",
        path.display()
    );
    Ok(DirectoryIdentity { device: metadata.dev(), inode: metadata.ino(), owner: metadata.uid() })
}

fn open_regular_no_follow(path: &Path) -> Result<File> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        // O_NOFOLLOW | O_NONBLOCK: the former rejects a replaced symlink,
        // while the latter prevents a replaced FIFO from blocking at open.
        #[cfg(target_os = "macos")]
        options.custom_flags(0x00000100 | 0x00000004);
        #[cfg(target_os = "linux")]
        options.custom_flags(0x00020000 | 0x00000800);
    }
    let file =
        options.open(path).with_context(|| format!("Open editor artifact {}", path.display()))?;
    regular_file_identity(&file, path)?;
    Ok(file)
}

#[cfg(unix)]
fn regular_file_identity(file: &File, path: &Path) -> Result<FileIdentity> {
    use std::os::unix::fs::MetadataExt;

    let opened = file.metadata()?;
    let named = fs::symlink_metadata(path)?;
    ensure!(
        opened.is_file()
            && named.is_file()
            && opened.dev() == named.dev()
            && opened.ino() == named.ino(),
        "Editor artifact must remain a physical regular file: {}",
        path.display()
    );
    Ok(FileIdentity { device: opened.dev(), inode: opened.ino(), owner: opened.uid() })
}

#[cfg(not(unix))]
fn regular_file_identity(_file: &File, _path: &Path) -> Result<FileIdentity> {
    anyhow::bail!("Private VSIX snapshots currently require Unix")
}

impl ExtensionSnapshot {
    fn capture(root: &Path, index: usize, source: PathBuf) -> Result<Self> {
        Self::capture_with_observer(root, index, source, || {})
    }

    fn capture_with_observer(
        root: &Path,
        index: usize,
        source: PathBuf,
        after_open: impl FnOnce(),
    ) -> Result<Self> {
        // A stable inode is insufficient during a streamed copy: an account
        // with write authority can change the same file between read calls.
        // Admit that authority before opening, then recheck after the copy.
        let protected_source = ProtectedFile::prepare(source.clone(), false)?;
        let mut input = open_regular_no_follow(&source)?;
        let input_identity = regular_file_identity(&input, &source)?;
        ensure!(
            input_identity == protected_source.identity,
            "Local VSIX changed before capture: {}",
            source.display()
        );
        let private_path = root.join("vsix").join(format!("extension-{index}.vsix"));
        let mut options = OpenOptions::new();
        options.write(true).create_new(true);
        #[cfg(unix)]
        {
            use std::os::unix::fs::OpenOptionsExt;
            options.mode(0o600);
        }
        let mut output = options.open(&private_path)?;
        let mut hasher = Sha256::new();
        let mut buffer = [0u8; 65536];
        after_open();
        loop {
            let count = input.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            output.write_all(&buffer[..count])?;
            hasher.update(&buffer[..count]);
        }
        ensure!(
            regular_file_identity(&input, &source)? == input_identity,
            "Local VSIX changed while being captured: {}",
            source.display()
        );
        protected_source.check()?;
        let identity = regular_file_identity(&output, &private_path)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            ensure!(
                identity.owner == effective_uid()
                    && output.metadata()?.permissions().mode() & 0o077 == 0,
                "Private VSIX copy is not owner-private: {}",
                private_path.display()
            );
        }
        Ok(Self { source, private_path, identity, sha256: hasher.finalize().into() })
    }

    fn check(&self) -> Result<()> {
        let mut input = open_regular_no_follow(&self.private_path)?;
        ensure!(
            regular_file_identity(&input, &self.private_path)? == self.identity,
            "Private VSIX copy identity changed: {}",
            self.private_path.display()
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            ensure!(
                self.identity.owner == effective_uid()
                    && input.metadata()?.permissions().mode() & 0o077 == 0,
                "Private VSIX copy is not owner-private: {}",
                self.private_path.display()
            );
        }
        let mut hasher = Sha256::new();
        let mut buffer = [0u8; 65536];
        loop {
            let count = input.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            hasher.update(&buffer[..count]);
        }
        let digest: [u8; 32] = hasher.finalize().into();
        ensure!(
            digest == self.sha256,
            "Private VSIX copy content changed: {}",
            self.private_path.display()
        );
        ensure!(
            regular_file_identity(&input, &self.private_path)? == self.identity,
            "Private VSIX copy identity changed: {}",
            self.private_path.display()
        );
        Ok(())
    }
}

#[cfg(unix)]
impl ProtectedFile {
    fn prepare(path: PathBuf, executable: bool) -> Result<Self> {
        let parent = path.parent().context("Protected editor file has no parent")?;
        let directories = checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?;
        let file = open_regular_no_follow(&path)?;
        let identity = regular_file_identity(&file, &path)?;
        let protected = Self { path, identity, directories, executable };
        protected.check()?;
        Ok(protected)
    }

    fn check(&self) -> Result<()> {
        use std::os::unix::fs::PermissionsExt;

        let parent = self.path.parent().context("Protected editor file has no parent")?;
        ensure!(
            checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?
                == self.directories,
            "Protected editor file ancestor changed: {}",
            self.path.display()
        );
        let file = open_regular_no_follow(&self.path)?;
        ensure!(
            regular_file_identity(&file, &self.path)? == self.identity,
            "Protected editor file identity changed: {}",
            self.path.display()
        );
        let mode = file.metadata()?.permissions().mode();
        ensure!(
            (self.identity.owner == effective_uid() || self.identity.owner == 0)
                && mode & 0o022 == 0,
            "Editor file is writable by another account: {}",
            self.path.display()
        );
        #[cfg(target_os = "macos")]
        check_non_granting_acl(&self.path)?;
        if self.executable {
            require_effective_execute(&self.path)?;
        }
        ensure!(
            regular_file_identity(&file, &self.path)? == self.identity,
            "Protected editor file identity changed: {}",
            self.path.display()
        );
        Ok(())
    }
}

#[cfg(unix)]
impl ProtectedBundle {
    #[cfg_attr(not(target_os = "macos"), allow(dead_code))]
    fn prepare(root: PathBuf) -> Result<Self> {
        ensure!(
            root.is_absolute() && root.canonicalize()? == root,
            "Code application bundle must have a canonical physical root"
        );
        let parent = root.parent().context("Code application bundle has no parent")?;
        let parent_directories =
            checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?;
        let entries = Self::scan(&root)?;
        ensure!(
            checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?
                == parent_directories,
            "Code application bundle ancestor changed: {}",
            root.display()
        );
        Ok(Self { root, parent_directories, entries })
    }

    fn check(&self) -> Result<()> {
        let parent = self.root.parent().context("Code application bundle has no parent")?;
        ensure!(
            checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?
                == self.parent_directories,
            "Code application bundle ancestor changed: {}",
            self.root.display()
        );
        ensure!(
            Self::scan(&self.root)? == self.entries,
            "Code application bundle contents changed: {}",
            self.root.display()
        );
        ensure!(
            checked_parent_directories(parent, DirectoryPurpose::ProtectedControl)?
                == self.parent_directories,
            "Code application bundle ancestor changed: {}",
            self.root.display()
        );
        Ok(())
    }

    fn scan(root: &Path) -> Result<Vec<BundleEntry>> {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        const MAX_ENTRIES: usize = 100_000;
        let mut pending = vec![root.to_owned()];
        let mut entries = Vec::new();
        while let Some(path) = pending.pop() {
            ensure!(
                entries.len() < MAX_ENTRIES,
                "Code application bundle exceeds {MAX_ENTRIES} entries"
            );
            let relative = path.strip_prefix(root)?.to_owned();
            let metadata = fs::symlink_metadata(&path)?;
            let kind = if metadata.is_dir() {
                BundleEntryKind::Directory
            } else if metadata.is_file() {
                BundleEntryKind::File
            } else if metadata.file_type().is_symlink() {
                BundleEntryKind::Symlink
            } else {
                anyhow::bail!(
                    "Code application bundle has an unsupported node: {}",
                    path.display()
                );
            };
            ensure!(
                metadata.uid() == effective_uid() || metadata.uid() == 0,
                "Code application bundle has an untrusted owner: {}",
                path.display()
            );
            let target = if kind == BundleEntryKind::Symlink {
                let link = fs::read_link(&path)?;
                Self::check_lexical_link(root, &path, &link)?;
                let physical = path.canonicalize()?;
                ensure!(
                    physical.starts_with(root),
                    "Code application bundle link escapes its root: {}",
                    path.display()
                );
                Some(link)
            } else {
                ensure!(
                    metadata.permissions().mode() & 0o022 == 0,
                    "Code application bundle is writable by another account: {}",
                    path.display()
                );
                #[cfg(target_os = "macos")]
                check_non_granting_acl(&path)?;
                None
            };
            let after = fs::symlink_metadata(&path)?;
            ensure!(
                after.dev() == metadata.dev()
                    && after.ino() == metadata.ino()
                    && after.uid() == metadata.uid()
                    && after.is_dir() == metadata.is_dir()
                    && after.is_file() == metadata.is_file()
                    && after.file_type().is_symlink() == metadata.file_type().is_symlink(),
                "Code application bundle entry changed during inspection: {}",
                path.display()
            );
            if kind == BundleEntryKind::Directory {
                for child in fs::read_dir(&path)? {
                    pending.push(child?.path());
                }
            }
            entries.push(BundleEntry {
                relative,
                identity: FileIdentity {
                    device: metadata.dev(),
                    inode: metadata.ino(),
                    owner: metadata.uid(),
                },
                kind,
                target,
            });
        }
        entries.sort_by(|left, right| left.relative.cmp(&right.relative));
        Ok(entries)
    }

    fn check_lexical_link(root: &Path, path: &Path, link: &Path) -> Result<()> {
        use std::path::Component;

        let (mut parts, target) = if link.is_absolute() {
            (Vec::new(), link.strip_prefix(root)?)
        } else {
            let parent = path.parent().context("Code application link has no parent")?;
            (
                parent
                    .strip_prefix(root)?
                    .components()
                    .map(|part| part.as_os_str().to_owned())
                    .collect::<Vec<_>>(),
                link,
            )
        };
        for part in target.components() {
            match part {
                Component::Normal(name) => parts.push(name.to_owned()),
                Component::CurDir => {}
                Component::ParentDir => {
                    ensure!(
                        parts.pop().is_some(),
                        "Code application bundle link traverses outside its root: {}",
                        path.display()
                    );
                }
                _ => anyhow::bail!(
                    "Code application bundle link is not confined: {}",
                    path.display()
                ),
            }
        }
        Ok(())
    }
}

#[cfg(not(unix))]
impl ProtectedBundle {
    fn prepare(_root: PathBuf) -> Result<Self> {
        anyhow::bail!("Protected Code bundles currently require Unix")
    }

    fn check(&self) -> Result<()> {
        anyhow::bail!("Protected Code bundles currently require Unix")
    }
}

#[cfg(not(unix))]
impl ProtectedFile {
    fn prepare(_path: PathBuf, _executable: bool) -> Result<Self> {
        anyhow::bail!("Protected editor files currently require Unix")
    }

    fn check(&self) -> Result<()> {
        anyhow::bail!("Protected editor files currently require Unix")
    }
}

#[cfg(target_os = "macos")]
fn check_non_granting_acl(path: &Path) -> Result<()> {
    use std::{
        ffi::{CString, c_void},
        os::unix::ffi::OsStrExt,
    };

    unsafe extern "C" {
        fn acl_get_file(path: *const std::ffi::c_char, kind: i32) -> *mut c_void;
        fn acl_valid(acl: *mut c_void) -> i32;
        fn acl_get_entry(acl: *mut c_void, selector: i32, entry: *mut *mut c_void) -> i32;
        fn acl_get_tag_type(entry: *mut c_void, tag: *mut i32) -> i32;
        fn acl_free(acl: *mut c_void) -> i32;
    }
    let before = fs::symlink_metadata(path)?;
    ensure!(before.is_dir() || before.is_file(), "ACL path is not physical: {}", path.display());
    let path_bytes = CString::new(path.as_os_str().as_bytes())?;
    // SAFETY: path_bytes is NUL-terminated and remains live until the call returns.
    let acl = unsafe { acl_get_file(path_bytes.as_ptr(), 0x100) };
    if acl.is_null() {
        let error = std::io::Error::last_os_error();
        // On Darwin, a physical directory without an extended ACL returns
        // ENOENT here. Accept it only if the same directory still occupies
        // the path; an actual disappearance or replacement must fail.
        ensure!(
            error.raw_os_error() == Some(2) && same_physical_file(path, &before)?,
            "Inspect editor state ACL: {}: {error}",
            path.display()
        );
        return Ok(());
    }
    let result = (|| -> Result<()> {
        // SAFETY: acl is the live result of acl_get_file and remains allocated
        // throughout validation and entry traversal below.
        ensure!(unsafe { acl_valid(acl) } == 0, "Invalid editor state ACL: {}", path.display());
        let mut entry = std::ptr::null_mut();
        // SAFETY: entry is writable storage for an opaque descriptor owned by
        // acl. ACL_FIRST_ENTRY is 0 in the installed Darwin SDK header.
        ensure!(
            unsafe { acl_get_entry(acl, 0, &mut entry) } == 0 && !entry.is_null(),
            "Editor state ACL has no readable first entry: {}",
            path.display()
        );
        for index in 0..128 {
            let mut tag = 0;
            // SAFETY: entry came from this live acl; tag is writable storage.
            ensure!(
                unsafe { acl_get_tag_type(entry, &mut tag) } == 0 && tag == 2,
                "Editor state ACL has a granting or unknown entry: {}",
                path.display()
            );
            entry = std::ptr::null_mut();
            // SAFETY: acl remains live and ACL_NEXT_ENTRY is -1. The entry
            // output is used only after a successful call.
            let status = unsafe { acl_get_entry(acl, -1, &mut entry) };
            if status == -1 {
                // The documented end condition after a successful entry is
                // EINVAL. Other failures must not appear as a complete ACL.
                ensure!(
                    std::io::Error::last_os_error().raw_os_error() == Some(22),
                    "Incomplete editor state ACL traversal: {}",
                    path.display()
                );
                return Ok(());
            }
            ensure!(
                status == 0 && !entry.is_null() && index + 1 < 128,
                "Editor state ACL exceeds the supported 128 entries: {}",
                path.display()
            );
        }
        unreachable!("the ACL traversal either ends or rejects an extra entry")
    })();
    // SAFETY: the non-null acl returned by acl_get_file is freed exactly once,
    // after all borrowed entry descriptors have gone out of use.
    let acl_freed = unsafe { acl_free(acl) };
    ensure!(acl_freed == 0, "Inspect editor state ACL: {}", path.display());
    result?;
    ensure!(
        same_physical_file(path, &before)?,
        "Editor state directory changed during ACL inspection: {}",
        path.display()
    );
    Ok(())
}

#[cfg(target_os = "macos")]
fn same_physical_file(path: &Path, before: &fs::Metadata) -> Result<bool> {
    use std::os::unix::fs::MetadataExt;

    let after = fs::symlink_metadata(path)?;
    Ok(after.dev() == before.dev()
        && after.ino() == before.ino()
        && after.is_dir() == before.is_dir()
        && after.is_file() == before.is_file())
}

#[cfg(unix)]
fn checked_parent_directories(
    parent: &Path,
    purpose: DirectoryPurpose,
) -> Result<Vec<(PathBuf, DirectoryIdentity)>> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let current_uid = effective_uid();
    let mut ancestors = parent.ancestors().map(Path::to_owned).collect::<Vec<_>>();
    ancestors.reverse();
    let mut checked: Vec<(PathBuf, DirectoryIdentity)> = Vec::with_capacity(ancestors.len());
    for (index, path) in ancestors.iter().enumerate() {
        let identity = directory_identity(&path)?;
        let metadata = fs::symlink_metadata(&path)?;
        ensure!(
            identity.owner == current_uid || identity.owner == 0,
            "Editor state ancestor has an untrusted owner: {}",
            path.display()
        );
        #[cfg(target_os = "macos")]
        check_non_granting_acl(&path)?;
        let mode = metadata.permissions().mode();
        let writable_by_others = mode & 0o022 != 0;
        if path == parent {
            ensure!(
                !writable_by_others
                    && (purpose == DirectoryPurpose::ProtectedControl
                        || identity.owner == current_uid),
                "Editor parent is not protected against another account: {}",
                path.display()
            );
        } else if writable_by_others {
            // A sticky ancestor can contain an owned child without allowing a
            // different unprivileged account to rename that child.
            let child_owner = directory_identity(&ancestors[index + 1])?.owner;
            ensure!(
                mode & 0o1000 != 0
                    && (child_owner == current_uid
                        || (purpose == DirectoryPurpose::ProtectedControl && child_owner == 0)),
                "Editor state ancestor permits replacement: {}",
                path.display()
            );
        }
        ensure!(
            metadata.dev() == identity.device && metadata.ino() == identity.inode,
            "Editor state ancestor changed: {}",
            path.display()
        );
        checked.push((path.to_owned(), identity));
    }
    Ok(checked)
}

fn regular_absolute(path: &Path) -> Result<PathBuf> {
    ensure!(
        path.is_absolute(),
        "An absolute local editor artifact path is required: {}",
        path.display()
    );
    let path = path
        .canonicalize()
        .with_context(|| format!("Resolve editor artifact {}", path.display()))?;
    ensure!(
        fs::metadata(&path)?.is_file(),
        "Editor artifact is not a regular file: {}",
        path.display()
    );
    Ok(path)
}

fn editor_program(code: &Path) -> Result<PathBuf> {
    #[cfg(target_os = "macos")]
    {
        ensure!(
            code.ends_with("Contents/Resources/app/bin/code"),
            "On macOS, select the Code CLI inside its application bundle"
        );
        let contents = code.ancestors().nth(4).context("Code application bundle is incomplete")?;
        let program = regular_absolute(&contents.join("MacOS/Electron"))?;
        ensure!(
            program.starts_with(contents),
            "Code GUI executable escapes its application bundle"
        );
        require_effective_execute(&program)?;
        Ok(program)
    }
    #[cfg(not(target_os = "macos"))]
    {
        regular_absolute(code)
    }
}

fn check_code_version(stdout: &[u8]) -> Result<()> {
    let output = std::str::from_utf8(stdout).context("Code returned a non-UTF8 version")?;
    let lines = output.lines().collect::<Vec<_>>();
    ensure!(
        matches!(
            lines.as_slice(),
            ["1.100.3", "258e40fedc6cb8edf399a463ce3a9d32e7e1f6f3", "arm64"]
        ),
        "The supported Code build is 1.100.3/258e40fedc6cb8edf399a463ce3a9d32e7e1f6f3 on macOS arm64; other builds need editor acceptance"
    );
    Ok(())
}

fn admit_code_version(admitted: &Cell<bool>, output: &Output) -> Result<()> {
    admitted.set(false);
    ensure!(output.status.success(), "Code version probe failed ({})", output.status);
    check_code_version(&output.stdout)?;
    admitted.set(true);
    Ok(())
}

fn require_code_version(admitted: &Cell<bool>) -> Result<()> {
    ensure!(admitted.get(), "Check the selected Code 1.100.3 version first");
    Ok(())
}

fn check_ipc_path(profile: &Path) -> Result<()> {
    #[cfg(target_os = "macos")]
    ensure!(
        profile.join("data/user-data/xxxx-xxxxxx.sock").as_os_str().as_encoded_bytes().len() <= 103,
        "macOS editor IPC path is too long (profile {}); use --state-dir with a shorter existing absolute directory",
        profile.display()
    );
    #[cfg(not(target_os = "macos"))]
    let _ = profile;
    Ok(())
}

fn protected_workspace_controls(workspace: &Path) -> Result<Vec<ProtectedFile>> {
    let mut controls = Vec::new();
    for relative in REQUIRED_WORKSPACE_CONTROLS {
        controls.push(ProtectedFile::prepare(
            workspace.join(relative),
            relative.starts_with(".anneal-bin/"),
        )?);
    }
    for relative in OPTIONAL_WORKSPACE_CONTROLS {
        let path = workspace.join(relative);
        match fs::symlink_metadata(&path) {
            Ok(_) => controls.push(ProtectedFile::prepare(path, false)?),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(error.into()),
        }
    }
    Ok(controls)
}

impl Profile {
    #[cfg(test)]
    fn prepare(workspace: &Path, sdk: &Path, code: &Path, extensions: &[PathBuf]) -> Result<Self> {
        Self::prepare_at(workspace, sdk, code, extensions, None)
    }

    fn prepare_at(
        workspace: &Path,
        sdk: &Path,
        code: &Path,
        extensions: &[PathBuf],
        state_dir: Option<&Path>,
    ) -> Result<Self> {
        ensure!(
            workspace.is_absolute() && sdk.is_absolute(),
            "Editor binding paths must be absolute"
        );
        ensure!(!extensions.is_empty(), "Supply pinned local Lean and dependency VSIX files");
        ensure!(
            workspace.canonicalize()?.as_path() == workspace,
            "Editor workspace must use its canonical physical path"
        );
        #[cfg(unix)]
        let workspace_directories =
            checked_parent_directories(workspace, DirectoryPurpose::ProtectedControl)?;
        #[cfg(not(unix))]
        let workspace_directories = Vec::new();
        let workspace_controls = protected_workspace_controls(workspace)?;
        let gateway = ProtectedFile::prepare(regular_absolute(&std::env::current_exe()?)?, true)?;
        let code = ProtectedFile::prepare(regular_absolute(code)?, true)?;
        let gui = ProtectedFile::prepare(editor_program(&code.path)?, true)?;
        #[cfg(target_os = "macos")]
        let bundle = Some(ProtectedBundle::prepare(
            code.path
                .ancestors()
                .nth(5)
                .context("Code application bundle is incomplete")?
                .to_owned(),
        )?);
        #[cfg(not(target_os = "macos"))]
        let bundle = None;
        let extension_paths = extensions
            .iter()
            .map(|path| {
                let path = regular_absolute(path)?;
                ensure!(
                    path.extension()
                        .and_then(|ext| ext.to_str())
                        .is_some_and(|ext| ext.eq_ignore_ascii_case("vsix")),
                    "Only explicit local VSIX files may be installed"
                );
                Ok(path)
            })
            .collect::<Result<Vec<_>>>()?;
        let parent =
            state_dir.unwrap_or(workspace.parent().context("Editor workspace has no parent")?);
        ensure!(parent.is_absolute(), "Editor state directory must be absolute");
        let parent = parent.canonicalize().context("Editor state directory must already exist")?;
        ensure!(
            parent.is_dir()
                && !parent.starts_with(workspace)
                && !parent.starts_with(sdk.parent().context("SDK installation has no parent")?),
            "Editor state must live outside the workspace and SDK"
        );
        #[cfg(unix)]
        let parent_directories =
            checked_parent_directories(&parent, DirectoryPurpose::PrivateState)?;
        #[cfg(not(unix))]
        let parent_directories = Vec::new();
        crate::lean_gateway::validate_editor_gateway(workspace)?;
        let path = std::env::join_paths([
            workspace.join(".anneal-bin"),
            PathBuf::from("/usr/bin"),
            PathBuf::from("/bin"),
            PathBuf::from("/usr/sbin"),
            PathBuf::from("/sbin"),
        ])?;
        // Chromium's singleton/socket symlinks must not enter .runtime, whose
        // compiler-output admission deliberately rejects links recursively.
        let mut builder = tempfile::Builder::new();
        builder.prefix("ae-").rand_bytes(6);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            // The default directory mode is 0777 before umask, which need not
            // satisfy the owner-private profile invariant. Set it at creation.
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let temporary = builder.tempdir_in(&parent)?;
        let root = temporary.path().to_owned();
        #[cfg(unix)]
        let root_identity = directory_identity(&root)?;
        #[cfg(not(unix))]
        let root_identity = DirectoryIdentity { device: 0, inode: 0, owner: 0 };
        let mut profile = Self {
            root,
            parent_directories,
            root_identity,
            workspace: workspace.to_owned(),
            workspace_directories,
            workspace_controls,
            sdk: sdk.to_owned(),
            gateway,
            code,
            gui,
            bundle,
            extensions: Vec::new(),
            path,
        };
        for dir in PROFILE_DIRECTORIES {
            fs::create_dir_all(profile.root.join(dir))?;
        }
        for (index, source) in extension_paths.into_iter().enumerate() {
            profile.extensions.push(ExtensionSnapshot::capture(&profile.root, index, source)?);
        }
        fs::write(profile.root.join("binding.json"), serde_json::to_vec_pretty(&profile.owner())?)?;
        fs::write(
            profile.root.join("data/user-data/User/settings.json"),
            serde_json::to_vec_pretty(&profile.settings())?,
        )?;
        check_ipc_path(&profile.root)?;
        profile.check_parent_and_root()?;
        let _ = temporary.keep();
        Ok(profile)
    }

    fn owner(&self) -> serde_json::Value {
        json!({"schema": 3, "workspace": self.workspace, "sdk_root": self.sdk,
            "gateway": self.gateway.path,
            "gateway_identity": [self.gateway.identity.device, self.gateway.identity.inode],
            "code": self.code.path,
            "code_identity": [self.code.identity.device, self.code.identity.inode],
            "gui": self.gui.path,
            "gui_identity": [self.gui.identity.device, self.gui.identity.inode],
            "workspace_controls": self.workspace_controls.iter().map(|control| json!({
                "path": control.path,
                "device": control.identity.device,
                "inode": control.identity.inode,
                "owner": control.identity.owner
            })).collect::<Vec<_>>(),
            "extensions": self.extensions.iter().map(|extension| json!({
                "source": extension.source,
                "private_path": extension.private_path,
                "sha256": extension.sha256,
                "device": extension.identity.device,
                "inode": extension.identity.inode,
                "owner": extension.identity.owner
            })).collect::<Vec<_>>(),
            "profile": self.root})
    }

    fn settings(&self) -> serde_json::Value {
        json!({
            "lean4.envPathExtensions": [self.workspace.join(".anneal-bin")],
            "lean4.automaticallyBuildDependencies": false,
            "lean4.logging.enabled": false,
            "lean4.showSetupWarnings": false,
            "lean4.serverArgs": [],
            "extensions.autoUpdate": false,
            "extensions.autoCheckUpdates": false,
            "update.mode": "none",
            "telemetry.telemetryLevel": "off",
            "terminal.integrated.inheritEnv": false,
            "git.enabled": false
        })
    }

    fn check_owner(&self, workspace: &Path, sdk: &Path) -> Result<()> {
        ensure!(workspace == self.workspace && sdk == self.sdk, "Editor workspace binding changed");
        #[cfg(unix)]
        ensure!(
            checked_parent_directories(workspace, DirectoryPurpose::ProtectedControl)?
                == self.workspace_directories,
            "Editor workspace or ancestor changed"
        );
        for control in &self.workspace_controls {
            control.check()?;
        }
        self.gateway.check()?;
        if let Some(bundle) = &self.bundle {
            bundle.check()?;
        }
        self.code.check()?;
        self.gui.check()?;
        self.check_parent_and_root()?;
        for relative in PROFILE_DIRECTORIES {
            // Do not append an empty component: a trailing separator can make
            // symlink_metadata follow a redirected root on Unix.
            let directory =
                if relative.is_empty() { self.root.clone() } else { self.root.join(relative) };
            ensure!(
                fs::symlink_metadata(&directory)?.is_dir(),
                "Private editor profile directory is not physical: {}",
                directory.display()
            );
        }
        for extension in &self.extensions {
            extension.check()?;
        }
        ensure!(
            fs::symlink_metadata(self.root.join("binding.json"))?.is_file(),
            "Private editor profile binding is not a physical regular file"
        );
        let owner: serde_json::Value =
            serde_json::from_slice(&fs::read(self.root.join("binding.json"))?)?;
        ensure!(owner == self.owner(), "Private editor profile ownership changed");
        crate::lean_gateway::validate_editor_gateway(workspace)?;
        let settings = self.root.join("data/user-data/User/settings.json");
        ensure!(
            fs::symlink_metadata(&settings)?.is_file(),
            "Private editor settings are not a physical regular file"
        );
        ensure!(
            fs::read(settings)? == serde_json::to_vec_pretty(&self.settings())?,
            "Private editor settings changed"
        );
        self.check_parent_and_root()?;
        #[cfg(unix)]
        ensure!(
            checked_parent_directories(workspace, DirectoryPurpose::ProtectedControl)?
                == self.workspace_directories,
            "Editor workspace or ancestor changed"
        );
        Ok(())
    }

    fn check_parent_and_root(&self) -> Result<()> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let parent = self.root.parent().context("Private editor profile has no parent")?;
            ensure!(
                checked_parent_directories(parent, DirectoryPurpose::PrivateState)?
                    == self.parent_directories,
                "Editor state parent or ancestor changed"
            );
            ensure!(
                directory_identity(&self.root)? == self.root_identity,
                "Private editor profile root identity changed"
            );
            ensure!(
                self.root_identity.owner == effective_uid()
                    && fs::symlink_metadata(&self.root)?.permissions().mode() & 0o077 == 0,
                "Private editor profile root is not private to this user"
            );
            #[cfg(target_os = "macos")]
            check_non_granting_acl(&self.root)?;
        }
        Ok(())
    }

    fn command(&self) -> Result<Command> {
        self.command_for(&self.code.path)
    }

    fn install_command(&self, index: usize) -> Result<Command> {
        let extension = self.extensions.get(index).context("Missing private VSIX snapshot")?;
        let mut command = self.command()?;
        command
            .args(["--do-not-sync", "--do-not-include-pack-dependencies"])
            .arg("--install-extension")
            .arg(&extension.private_path);
        Ok(command)
    }

    fn command_for(&self, program: &Path) -> Result<Command> {
        self.check_owner(&self.workspace, &self.sdk)?;
        let mut command = Command::new(program);
        command
            .env_clear()
            .current_dir(&self.workspace)
            .stdin(Stdio::null())
            .env("PATH", &self.path)
            .env("HOME", self.root.join("home"))
            .env("XDG_CONFIG_HOME", self.root.join("config"))
            .env("XDG_CACHE_HOME", self.root.join("cache"))
            .env("XDG_DATA_HOME", self.root.join("xdg-data"))
            .env("TMPDIR", self.root.join("tmp"))
            .env("ELAN_HOME", self.root.join("elan"))
            .env("ELAN_TOOLCHAIN", &self.sdk)
            .env("SHELL", "/bin/sh")
            .env("LANG", "en_US.UTF-8")
            // Override installation-adjacent portable data with an owned path.
            // Its effective directories match the explicit CLI flags below.
            .env("VSCODE_PORTABLE", self.root.join("data"))
            .args(["--force-disable-user-env", "--disable-updates", "--disable-telemetry"])
            .arg("--user-data-dir")
            .arg(self.root.join("data/user-data"))
            .arg("--extensions-dir")
            .arg(self.root.join("data/extensions"));
        Ok(command)
    }

    fn check_required_extensions(&self) -> Result<()> {
        let mut lean = false;
        let mut toml = false;
        for entry in fs::read_dir(self.root.join("data/extensions"))? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                continue;
            }
            let manifest = entry.path().join("package.json");
            if !manifest.is_file() {
                continue;
            }
            let manifest: serde_json::Value = serde_json::from_slice(&fs::read(manifest)?)?;
            let id = format!(
                "{}.{}",
                manifest["publisher"].as_str().unwrap_or(""),
                manifest["name"].as_str().unwrap_or("")
            );
            if id == "leanprover.lean4" {
                ensure!(
                    manifest["version"] == "0.0.240",
                    "The researched Lean extension version is 0.0.240; other versions need a new editor contract review"
                );
                lean = true;
            }
            if id == "tamasfe.even-better-toml" {
                ensure!(
                    manifest["version"] == "0.21.2",
                    "The researched TOML extension version is 0.21.2; other versions need a new editor contract review"
                );
                toml = true;
            }
        }
        ensure!(
            lean && toml,
            "Private profile requires explicit local leanprover.lean4 and tamasfe.even-better-toml installations"
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, ffi::OsString};

    use super::*;

    #[cfg(unix)]
    #[test]
    fn code_version_admission_requires_reviewed_release_platform_and_success() {
        use std::os::unix::process::ExitStatusExt;

        let accepted = Cell::new(false);
        assert!(require_code_version(&accepted).is_err());
        let response = |status, text: &[u8]| Output {
            status: std::process::ExitStatus::from_raw(status),
            stdout: text.to_owned(),
            stderr: Vec::new(),
        };
        let commit = "258e40fedc6cb8edf399a463ce3a9d32e7e1f6f3";
        for text in [
            "1.99.0\n0123456789abcdef0123456789abcdef01234567\narm64\n",
            "1.100.3-insiders\n0123456789abcdef0123456789abcdef01234567\narm64\n",
            "1.100.3\nmissing-commit\narm64\n",
            "1.100.3\n0123456789abcdef0123456789abcdef01234567\nx64\n",
            "1.100.3\n0123456789abcdef0123456789abcdef01234567\n",
            "1.100.3\n0123456789abcdef0123456789abcdef01234567\narm64\n",
        ] {
            assert!(admit_code_version(&accepted, &response(0, text.as_bytes())).is_err());
            assert!(!accepted.get());
        }
        assert!(admit_code_version(&accepted, &response(0, &[0xff])).is_err());
        assert!(!accepted.get());
        let valid = format!("1.100.3\n{commit}\narm64\n");
        assert!(admit_code_version(&accepted, &response(1 << 8, valid.as_bytes())).is_err());
        assert!(!accepted.get());
        admit_code_version(&accepted, &response(0, valid.as_bytes())).unwrap();
        assert!(accepted.get());
        require_code_version(&accepted).unwrap();
        assert!(admit_code_version(&accepted, &response(0, b"1.101.0\n")).is_err());
        assert!(!accepted.get());
        assert!(require_code_version(&accepted).is_err());
    }

    fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        #[cfg(target_os = "macos")]
        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let temp = tempfile::tempdir().unwrap();
        let workspace = temp.path().join("consumer");
        fs::create_dir(&workspace).unwrap();
        crate::lean_gateway::write_editor_gateway(&workspace, &workspace).unwrap();
        // Inert generated control files. They are never used as SDK commands.
        for relative in [".anneal-sdk.json", "lean-toolchain", ".anneal-lake.json", "lakefile.lean"]
        {
            fs::write(workspace.join(relative), "fixture control\n").unwrap();
        }
        #[cfg(target_os = "macos")]
        let code = temp.path().join("Code.app/Contents/Resources/app/bin/code");
        #[cfg(not(target_os = "macos"))]
        let code = temp.path().join("code");
        fs::create_dir_all(code.parent().unwrap()).unwrap();
        fs::write(&code, "unused fixture").unwrap();
        #[cfg(target_os = "macos")]
        {
            let gui = temp.path().join("Code.app/Contents/MacOS/Electron");
            fs::create_dir_all(gui.parent().unwrap()).unwrap();
            fs::write(&gui, "unused fixture").unwrap();
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(gui, fs::Permissions::from_mode(0o700)).unwrap();
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&code, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let vsix = temp.path().join("lean.vsix");
        fs::write(&vsix, "unused fixture").unwrap();
        (temp, workspace, code, vsix)
    }

    #[cfg(unix)]
    #[test]
    fn generated_workspace_is_admitted_under_group_writable_umask() {
        use std::os::unix::fs::PermissionsExt;

        const CHILD: &str = "ANNEAL_EDITOR_FULL_GROUP_UMASK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .arg("generated_workspace_is_admitted_under_group_writable_umask")
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

        let sdk_fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let (_code_fixture, _, code, vsix) = fixture();
        #[cfg(target_os = "macos")]
        let generation = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let generation = tempfile::tempdir().unwrap();
        unsafe extern "C" {
            fn umask(mode: u32) -> u32;
        }
        // SAFETY: this filtered fixture runs alone in its child process.
        let previous = unsafe { umask(0o002) };
        let run = generation.path().join("target/anneal/run");
        crate::resolve::create_missing_private_run_directories(&run).unwrap();
        let lean = run.join("lean");
        crate::aeneas::create_missing_private_lean_directory(&lean).unwrap();
        let final_root = lean.join(sdk_fixture.sdk.id());
        let stage = tempfile::Builder::new().prefix(".anneal-stage-").tempdir_in(&lean).unwrap();
        let stage_root = stage.path().join("workspace");
        crate::lean_sdk::Workspace::stage(
            &sdk_fixture.sdk,
            &stage_root,
            &final_root,
            None,
            &["anneal", "generated", "user"],
        )
        .unwrap();
        crate::aeneas::write_generated_toolchain(
            &stage_root.join("lean-toolchain"),
            &format!("{}\n", sdk_fixture.sdk.root().display()),
        )
        .unwrap();
        for relative in ["anneal", "generated", "user"] {
            fs::create_dir(stage_root.join(relative)).unwrap();
        }
        let libraries = [
            crate::lean_sdk::LakeLibrary { name: "Anneal", source_root: "anneal", modules: &[] },
            crate::lean_sdk::LakeLibrary {
                name: "Generated",
                source_root: "generated",
                modules: &[],
            },
            crate::lean_sdk::LakeLibrary { name: "User", source_root: "user", modules: &[] },
        ];
        crate::lean_sdk::Workspace::write_lakefile(&sdk_fixture.sdk, &stage_root, &libraries)
            .unwrap();
        crate::lean_gateway::write_editor_gateway(&stage_root, &final_root).unwrap();
        crate::lean_sdk::Workspace::admit_stage(&sdk_fixture.sdk, &stage_root, &final_root)
            .unwrap();
        fs::rename(&stage_root, &final_root).unwrap();
        let workspace = crate::lean_sdk::Workspace::open(&sdk_fixture.sdk, &final_root).unwrap();
        workspace.admit().unwrap();

        for path in [
            generation.path().join("target"),
            generation.path().join("target/anneal"),
            run,
            lean,
            final_root.clone(),
            final_root.join(".anneal-bin"),
            final_root.join(".vscode"),
        ] {
            assert_eq!(fs::metadata(path).unwrap().permissions().mode() & 0o777, 0o700);
        }
        for relative in [".anneal-sdk.json", "lean-toolchain", ".vscode/settings.json"] {
            assert_eq!(
                fs::metadata(final_root.join(relative)).unwrap().permissions().mode() & 0o777,
                0o600
            );
        }
        let profile =
            Profile::prepare(&final_root, sdk_fixture.sdk.root(), &code, &[vsix]).unwrap();
        profile.check_owner(&final_root, sdk_fixture.sdk.root()).unwrap();
        // SAFETY: restore this child's prior process-wide umask.
        unsafe { umask(previous) };
    }

    #[cfg(unix)]
    fn inert_bundle_fixture() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        use std::os::unix::fs::{PermissionsExt, symlink};

        #[cfg(target_os = "macos")]
        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("Code.app");
        let script = root.join("Contents/Resources/app/out/main.js");
        let framework = root.join("Contents/Frameworks/Test.framework/Versions/A/Test");
        fs::create_dir_all(script.parent().unwrap()).unwrap();
        fs::create_dir_all(framework.parent().unwrap()).unwrap();
        fs::write(&script, b"inert resource").unwrap();
        fs::write(&framework, b"inert framework").unwrap();
        for path in [
            root.clone(),
            root.join("Contents"),
            root.join("Contents/Resources"),
            root.join("Contents/Resources/app"),
            root.join("Contents/Resources/app/out"),
            root.join("Contents/Frameworks"),
            root.join("Contents/Frameworks/Test.framework"),
            root.join("Contents/Frameworks/Test.framework/Versions"),
            root.join("Contents/Frameworks/Test.framework/Versions/A"),
        ] {
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        }
        for path in [&script, &framework] {
            fs::set_permissions(path, fs::Permissions::from_mode(0o600)).unwrap();
        }
        symlink("A", root.join("Contents/Frameworks/Test.framework/Versions/Current")).unwrap();
        (temp, root, script, framework)
    }

    #[cfg(unix)]
    #[test]
    fn vsix_capture_requires_protected_source_and_rechecks_copy_fence() {
        use std::os::unix::fs::PermissionsExt;

        #[cfg(target_os = "macos")]
        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("profile");
        fs::create_dir_all(root.join("vsix")).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let source_dir = temp.path().join("source");
        fs::create_dir(&source_dir).unwrap();
        let source = source_dir.join("lean.vsix");
        fs::write(&source, b"inert original archive").unwrap();
        fs::set_permissions(&source, fs::Permissions::from_mode(0o600)).unwrap();
        let snapshot = ExtensionSnapshot::capture(&root, 0, source.clone()).unwrap();
        fs::remove_file(&source).unwrap();
        snapshot.check().unwrap();

        fs::write(&source, b"inert original archive").unwrap();
        fs::set_permissions(&source, fs::Permissions::from_mode(0o666)).unwrap();
        assert!(ExtensionSnapshot::capture(&root, 1, source.clone()).is_err());
        fs::set_permissions(&source, fs::Permissions::from_mode(0o600)).unwrap();
        fs::set_permissions(&source_dir, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(ExtensionSnapshot::capture(&root, 2, source.clone()).is_err());
        fs::set_permissions(&source_dir, fs::Permissions::from_mode(0o700)).unwrap();

        let original_inode =
            regular_file_identity(&open_regular_no_follow(&source).unwrap(), &source)
                .unwrap()
                .inode;
        assert!(
            ExtensionSnapshot::capture_with_observer(&root, 3, source.clone(), || {
                fs::set_permissions(&source, fs::Permissions::from_mode(0o666)).unwrap();
                fs::write(&source, b"changed inert bytes").unwrap();
            })
            .is_err()
        );
        assert_eq!(
            regular_file_identity(&open_regular_no_follow(&source).unwrap(), &source)
                .unwrap()
                .inode,
            original_inode
        );
        fs::set_permissions(&source, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(
            ExtensionSnapshot::capture_with_observer(&root, 4, source.clone(), || {
                fs::set_permissions(&source_dir, fs::Permissions::from_mode(0o777)).unwrap();
            })
            .is_err()
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn vsix_capture_rejects_granting_source_acl() {
        use std::os::unix::fs::PermissionsExt;

        for parent_acl in [false, true] {
            let temp = tempfile::tempdir_in("/private/tmp").unwrap();
            let root = temp.path().join("profile");
            fs::create_dir_all(root.join("vsix")).unwrap();
            fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
            let source_dir = temp.path().join("source");
            fs::create_dir(&source_dir).unwrap();
            let source = source_dir.join("lean.vsix");
            fs::write(&source, b"inert archive").unwrap();
            fs::set_permissions(&source, fs::Permissions::from_mode(0o600)).unwrap();
            let path = if parent_acl { &source_dir } else { &source };
            let status = std::process::Command::new("/bin/chmod")
                .args(["+a", "everyone allow write"])
                .arg(path)
                .status()
                .unwrap();
            assert!(status.success());
            assert!(ExtensionSnapshot::capture(&root, 0, source).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn protected_code_bundle_rejects_mutable_resources_and_replacement() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, root, script, framework) = inert_bundle_fixture();
        let bundle = ProtectedBundle::prepare(root.clone()).unwrap();
        bundle.check().unwrap();
        for path in [script.clone(), framework.clone(), root.join("Contents/Frameworks")] {
            let original = fs::metadata(&path).unwrap().permissions();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o770)).unwrap();
            assert!(bundle.check().is_err(), "accepted mutable {}", path.display());
            fs::set_permissions(&path, original).unwrap();
            bundle.check().unwrap();
        }
        fs::set_permissions(&script, fs::Permissions::from_mode(0o660)).unwrap();
        assert!(ProtectedBundle::prepare(root.clone()).is_err());
        fs::set_permissions(&script, fs::Permissions::from_mode(0o600)).unwrap();
        bundle.check().unwrap();
        let added = root.join("Contents/Resources/app/out/new.js");
        fs::write(&added, b"new inert resource").unwrap();
        assert!(bundle.check().is_err(), "accepted added bundle resource");
        fs::remove_file(added).unwrap();
        bundle.check().unwrap();
        let moved = temp.path().join("original-main.js");
        fs::rename(&script, &moved).unwrap();
        fs::copy(&moved, &script).unwrap();
        fs::set_permissions(&script, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(bundle.check().is_err(), "accepted physical resource replacement");
    }

    #[cfg(unix)]
    #[test]
    fn protected_code_bundle_rejects_physical_directory_replacement() {
        let (temp, root, _script, _framework) = inert_bundle_fixture();
        let bundle = ProtectedBundle::prepare(root.clone()).unwrap();
        let directory = root.join("Contents/Frameworks");
        fs::rename(&directory, temp.path().join("old-frameworks")).unwrap();
        fs::create_dir(&directory).unwrap();
        assert!(bundle.check().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn code_bundle_accepts_confined_links_and_rejects_escape_or_dangling_links() {
        use std::os::unix::fs::symlink;

        let (temp, root, _script, _framework) = inert_bundle_fixture();
        let link = root.join("Contents/Frameworks/Test.framework/Versions/Current");
        let bundle = ProtectedBundle::prepare(root.clone()).unwrap();
        bundle.check().unwrap();
        fs::remove_file(&link).unwrap();
        let outside = temp.path().join("outside");
        fs::write(&outside, b"inert outside fixture").unwrap();
        symlink(&outside, &link).unwrap();
        assert!(bundle.check().is_err());
        assert!(ProtectedBundle::prepare(root.clone()).is_err());
        fs::remove_file(&link).unwrap();
        // Its final physical target is inside the bundle, but resolving this
        // spelling crosses the unprotected parent before coming back inside.
        symlink("../../../../../Code.app/Contents/Frameworks/Test.framework/Versions/A", &link)
            .unwrap();
        assert_eq!(
            link.canonicalize().unwrap(),
            root.join("Contents/Frameworks/Test.framework/Versions/A")
        );
        assert!(ProtectedBundle::prepare(root.clone()).is_err());
        fs::remove_file(&link).unwrap();
        symlink("missing", &link).unwrap();
        assert!(ProtectedBundle::prepare(root).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn code_bundle_rejects_granting_resource_and_directory_acls() {
        for directory in [false, true] {
            let (_temp, root, script, _framework) = inert_bundle_fixture();
            let bundle = ProtectedBundle::prepare(root.clone()).unwrap();
            let path = if directory { root.join("Contents/Frameworks") } else { script };
            let status = std::process::Command::new("/bin/chmod")
                .args(["+a", "everyone allow write"])
                .arg(&path)
                .status()
                .unwrap();
            assert!(status.success());
            assert!(bundle.check().is_err());
        }
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn prepared_code_commands_recheck_bundle_resources() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let script = temp.path().join("Code.app/Contents/Resources/app/out/main.js");
        fs::create_dir_all(script.parent().unwrap()).unwrap();
        fs::write(&script, b"inert JS").unwrap();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let prepared_install = profile.install_command(0).unwrap();
        let prepared_launch = profile.command_for(&profile.gui.path).unwrap();
        fs::set_permissions(&script, fs::Permissions::from_mode(0o660)).unwrap();
        assert_eq!(prepared_install.get_program(), code.as_os_str());
        assert_eq!(prepared_launch.get_program(), profile.gui.path.as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.install_command(0).is_err());
        assert!(profile.command_for(&profile.gui.path).is_err());
    }

    #[test]
    fn private_commands_have_only_owned_environment_and_finite_arguments() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let command = profile.command().unwrap();
        let env: BTreeMap<OsString, OsString> = command
            .get_envs()
            .map(|(key, value)| (key.to_owned(), value.unwrap().to_owned()))
            .collect();
        assert_eq!(env.len(), 11);
        assert_eq!(env.get(&OsString::from("ELAN_TOOLCHAIN")), Some(&sdk.into_os_string()));
        for forbidden in [
            "DYLD_INSERT_LIBRARIES",
            "NODE_OPTIONS",
            "LEAN_PATH",
            "LAKE",
            "ELECTRON_RUN_AS_NODE",
            "VSCODE_IPC_HOOK_CLI",
        ] {
            assert!(!env.contains_key(&OsString::from(forbidden)));
        }
        assert!(command.get_args().any(|arg| arg == "--force-disable-user-env"));
        assert_eq!(command.get_program(), code.canonicalize().unwrap().as_os_str());
    }

    #[test]
    fn each_profile_is_fresh_outside_compiler_private_tree_and_logging_is_off() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let first = Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).unwrap();
        let second = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        assert_ne!(first.root, second.root);
        assert!(!first.root.starts_with(&workspace));
        first.check_owner(&workspace, &sdk).unwrap();
        let settings: serde_json::Value = serde_json::from_slice(
            &fs::read(first.root.join("data/user-data/User/settings.json")).unwrap(),
        )
        .unwrap();
        assert_eq!(settings["lean4.logging.enabled"], false);
        assert_eq!(settings["lean4.envPathExtensions"][0], json!(workspace.join(".anneal-bin")));
        fs::write(first.root.join("binding.json"), "{}").unwrap();
        assert!(first.check_owner(&workspace, &sdk).is_err());
    }

    #[test]
    fn every_code_command_rechecks_tools_and_effective_settings() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        profile.command().unwrap();
        profile.command_for(&code).unwrap();
        for tool in ["lean", "lake"] {
            let wrapper = workspace.join(".anneal-bin").join(tool);
            let original = fs::read(&wrapper).unwrap();
            // Admission fails before constructing any command; no modified
            // wrapper or foreign toolchain fixture is executed.
            fs::write(&wrapper, "changed fixture").unwrap();
            assert!(profile.command().is_err());
            assert!(profile.command_for(&code).is_err());
            fs::write(wrapper, original).unwrap();
        }
        for settings in [
            workspace.join(".vscode/settings.json"),
            profile.root.join("data/user-data/User/settings.json"),
        ] {
            let original = fs::read(&settings).unwrap();
            let mut changed: serde_json::Value = serde_json::from_slice(&original).unwrap();
            changed["lean4.executablePath"] = json!("/unused/fixture");
            fs::write(&settings, serde_json::to_vec_pretty(&changed).unwrap()).unwrap();
            assert!(profile.command().is_err());
            assert!(profile.command_for(&code).is_err());
            fs::write(settings, original).unwrap();
        }
        profile.command().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn selected_code_cli_and_gui_reject_same_path_physical_replacement() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        for (index, replace_gui) in [false, true].into_iter().enumerate() {
            let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).unwrap();
            let prepared = if replace_gui {
                profile.command_for(&profile.gui.path).unwrap()
            } else {
                profile.command().unwrap()
            };
            let selected = if replace_gui { &profile.gui.path } else { &profile.code.path };
            let relocated = temp.path().join(format!("original-code-{index}"));
            fs::rename(selected, &relocated).unwrap();
            fs::copy(&relocated, selected).unwrap();
            fs::set_permissions(selected, fs::Permissions::from_mode(0o700)).unwrap();
            assert_eq!(prepared.get_program(), selected.as_os_str());
            assert!(profile.check_owner(&workspace, &sdk).is_err());
            assert!(profile.command().is_err());
            assert!(profile.command_for(&profile.gui.path).is_err());
            fs::remove_file(selected).unwrap();
            fs::rename(relocated, selected).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn selected_code_requires_protected_file_and_ancestor_modes() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();
        let original_mode = fs::metadata(&code).unwrap().permissions().mode();
        fs::set_permissions(&code, fs::Permissions::from_mode(0o770)).unwrap();
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        fs::set_permissions(&code, fs::Permissions::from_mode(original_mode)).unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();

        let ancestor = code.parent().unwrap();
        let original_mode = fs::metadata(ancestor).unwrap().permissions().mode();
        fs::set_permissions(ancestor, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        fs::set_permissions(ancestor, fs::Permissions::from_mode(original_mode)).unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn selected_code_rejects_a_physical_ancestor_replacement() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let prepared = profile.command().unwrap();
        let ancestor = code.parent().unwrap();
        let relocated = temp.path().join("original-code-bin");
        fs::rename(ancestor, &relocated).unwrap();
        fs::create_dir(ancestor).unwrap();
        fs::copy(relocated.join("code"), &code).unwrap();
        fs::set_permissions(&code, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(prepared.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.command().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn selected_code_rejects_a_symlink_replacement() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let relocated = temp.path().join("selected-code-original");
        fs::rename(&code, &relocated).unwrap();
        std::os::unix::fs::symlink(&relocated, &code).unwrap();
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.command().is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn selected_code_rejects_a_granting_file_acl() {
        let (temp, workspace, code, vsix) = fixture();
        let profile =
            Profile::prepare(&workspace, &temp.path().join("archive/lean-sdk"), &code, &[vsix])
                .unwrap();
        let status = std::process::Command::new("/bin/chmod")
            .args(["+a", "everyone allow write"])
            .arg(&code)
            .status()
            .unwrap();
        assert!(status.success());
        assert!(profile.check_owner(&workspace, &temp.path().join("archive/lean-sdk")).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn executable_requires_the_invoking_users_permission_class() {
        use std::os::unix::fs::PermissionsExt;

        #[cfg(target_os = "macos")]
        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("inert-code");
        fs::write(&path, "inert executable fixture").unwrap();
        // Group and other have execute, but the file's owner does not.
        fs::set_permissions(&path, fs::Permissions::from_mode(0o611)).unwrap();
        assert!(ProtectedFile::prepare(path.clone(), true).is_err());

        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        let protected = ProtectedFile::prepare(path.clone(), true).unwrap();
        protected.check().unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o611)).unwrap();
        assert!(protected.check().is_err());
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        protected.check().unwrap();
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn executable_rejects_an_applicable_deny_execute_acl() {
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        let path = temp.path().join("inert-code");
        fs::write(&path, "inert executable fixture").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        let protected = ProtectedFile::prepare(path.clone(), true).unwrap();
        let status = std::process::Command::new("/bin/chmod")
            .args(["+a", "everyone deny execute"])
            .arg(&path)
            .status()
            .unwrap();
        assert!(status.success());
        assert!(protected.check().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn gateway_executable_uses_the_same_protected_path_and_identity_rule() {
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir().unwrap();
        let bin = temp.path().join("bin");
        fs::create_dir(&bin).unwrap();
        let path = bin.join("cargo-anneal");
        fs::write(&path, "inert executable fixture").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        let protected = ProtectedFile::prepare(path.clone(), true).unwrap();
        protected.check().unwrap();

        fs::set_permissions(&path, fs::Permissions::from_mode(0o770)).unwrap();
        assert!(protected.check().is_err());
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        protected.check().unwrap();

        fs::set_permissions(&bin, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(protected.check().is_err());
        fs::set_permissions(&bin, fs::Permissions::from_mode(0o755)).unwrap();
        protected.check().unwrap();

        let old = temp.path().join("old-bin");
        fs::rename(&bin, &old).unwrap();
        fs::create_dir(&bin).unwrap();
        fs::copy(old.join("cargo-anneal"), &path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        assert!(protected.check().is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn gateway_executable_rejects_a_granting_acl() {
        use std::os::unix::fs::PermissionsExt;

        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        let path = temp.path().join("cargo-anneal");
        fs::write(&path, "inert executable fixture").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        let protected = ProtectedFile::prepare(path.clone(), true).unwrap();
        let status = std::process::Command::new("/bin/chmod")
            .args(["+a", "everyone allow write"])
            .arg(&path)
            .status()
            .unwrap();
        assert!(status.success());
        assert!(protected.check().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn stock_profile_pins_gateway_and_generated_workspace_controls() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let mut profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let constructed = profile.command().unwrap();
        let expected_gateway = regular_absolute(&std::env::current_exe().unwrap()).unwrap();
        assert_eq!(profile.gateway.path, expected_gateway);
        assert_eq!(profile.workspace_controls.len(), 7);
        profile.check_owner(&workspace, &sdk).unwrap();

        // The same check guards an already constructed Code command.
        profile.gateway.identity.inode ^= 1;
        assert_eq!(constructed.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        profile.gateway.identity.inode ^= 1;
        profile.check_owner(&workspace, &sdk).unwrap();

        for relative in REQUIRED_WORKSPACE_CONTROLS.into_iter().chain(OPTIONAL_WORKSPACE_CONTROLS) {
            let path = workspace.join(relative);
            let mode = fs::metadata(&path).unwrap().permissions().mode();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o666)).unwrap();
            assert!(profile.check_owner(&workspace, &sdk).is_err(), "accepted {relative}");
            fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
            profile.check_owner(&workspace, &sdk).unwrap();
        }
        let directories =
            [workspace.clone(), workspace.join(".anneal-bin"), workspace.join(".vscode")];
        for directory in &directories {
            let mode = fs::metadata(directory).unwrap().permissions().mode();
            fs::set_permissions(directory, fs::Permissions::from_mode(0o777)).unwrap();
            assert!(profile.check_owner(&workspace, &sdk).is_err());
            fs::set_permissions(directory, fs::Permissions::from_mode(mode)).unwrap();
            profile.check_owner(&workspace, &sdk).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn stock_profile_rejects_mutable_workspace_controls_at_preparation() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let binding = workspace.join(".anneal-sdk.json");
        let mode = fs::metadata(&binding).unwrap().permissions().mode();
        fs::set_permissions(&binding, fs::Permissions::from_mode(0o666)).unwrap();
        assert!(Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).is_err());
        fs::set_permissions(&binding, fs::Permissions::from_mode(mode)).unwrap();

        let mode = fs::metadata(&workspace).unwrap().permissions().mode();
        fs::set_permissions(&workspace, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).is_err());
        fs::set_permissions(&workspace, fs::Permissions::from_mode(mode)).unwrap();
        Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn stock_profile_rejects_replaced_workspace_control_and_parent() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let command = profile.command().unwrap();
        let lean = workspace.join(".anneal-bin/lean");
        let old = workspace.join("old-lean");
        fs::rename(&lean, &old).unwrap();
        fs::copy(&old, &lean).unwrap();
        assert_eq!(command.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let settings_dir = workspace.join(".vscode");
        let old = workspace.join("old-vscode");
        fs::rename(&settings_dir, &old).unwrap();
        fs::create_dir(&settings_dir).unwrap();
        fs::copy(old.join("settings.json"), settings_dir.join("settings.json")).unwrap();
        assert!(profile.check_owner(&workspace, &sdk).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn stock_profile_rejects_granting_workspace_control_acls() {
        for relative in [".vscode/settings.json", ".anneal-bin/lean", ".anneal-sdk.json", ""] {
            let (temp, workspace, code, vsix) = fixture();
            let sdk = temp.path().join("archive/lean-sdk");
            let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
            let path = workspace.join(relative);
            let status = std::process::Command::new("/bin/chmod")
                .args(["+a", "everyone allow write"])
                .arg(&path)
                .status()
                .unwrap();
            assert!(status.success());
            assert!(profile.check_owner(&workspace, &sdk).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn profile_settings_cannot_be_redirected_through_symlinks() {
        let (temp, workspace, code, vsix) = fixture();
        let profile =
            Profile::prepare(&workspace, &temp.path().join("archive/lean-sdk"), &code, &[vsix])
                .unwrap();
        let settings = profile.root.join("data/user-data/User/settings.json");
        let copy = temp.path().join("settings-copy");
        fs::rename(&settings, &copy).unwrap();
        std::os::unix::fs::symlink(copy, settings).unwrap();
        assert!(profile.command().is_err());
        assert!(profile.command_for(&code).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn every_private_profile_directory_rejects_redirection_before_code_commands() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        // This independent inventory covers all effective environment/CLI
        // paths, portable data and the settings ancestors, including data/tmp.
        for (index, relative) in [
            "",
            "data",
            "data/user-data",
            "data/user-data/User",
            "data/extensions",
            "data/tmp",
            "home",
            "elan",
            "config",
            "cache",
            "xdg-data",
            "tmp",
            "vsix",
        ]
        .iter()
        .enumerate()
        {
            let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).unwrap();
            let prepared_command = profile.command().unwrap();
            let directory = if relative.is_empty() {
                profile.root.clone()
            } else {
                profile.root.join(relative)
            };
            let redirected = temp.path().join(format!("redirected-{index}"));
            fs::rename(&directory, &redirected).unwrap();
            let marker = redirected.join("untouched-fixture");
            fs::write(&marker, "inert owned fixture").unwrap();
            std::os::unix::fs::symlink(&redirected, &directory).unwrap();

            // Revalidate a previously constructed command at the same fence
            // used by EditorHost::validate_before_command. No Code executes.
            assert_eq!(prepared_command.get_program(), code.canonicalize().unwrap().as_os_str());
            let error = profile.check_owner(&workspace, &sdk).unwrap_err();
            assert!(error.to_string().contains("profile directory is not physical"));
            assert!(profile.command().is_err(), "Code CLI accepted {relative}");
            assert!(profile.command_for(&code).is_err(), "Code GUI accepted {relative}");
            assert_eq!(fs::read_to_string(&marker).unwrap(), "inert owned fixture");

            fs::remove_file(&directory).unwrap();
            fs::rename(&redirected, &directory).unwrap();
            profile.check_owner(&workspace, &sdk).unwrap();
        }
    }

    #[test]
    fn missing_relative_or_gallery_artifacts_are_rejected() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        assert!(Profile::prepare(&workspace, &sdk, Path::new("code"), &[vsix.clone()]).is_err());
        assert!(Profile::prepare(&workspace, &sdk, &code, &[]).is_err());
        assert!(
            Profile::prepare(&workspace, &sdk, &code, &[PathBuf::from("leanprover.lean4")])
                .is_err()
        );
        assert!(Profile::prepare(&workspace, &sdk, &code, &[code.clone()]).is_err());
    }

    #[test]
    fn install_commands_use_private_snapshots_when_original_vsix_files_change() {
        let (temp, workspace, code, vsix) = fixture();
        let second = temp.path().join("toml.vsix");
        fs::write(&vsix, "original lean fixture").unwrap();
        fs::write(&second, "original toml fixture").unwrap();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile =
            Profile::prepare(&workspace, &sdk, &code, &[vsix.clone(), second.clone()]).unwrap();
        assert_eq!(profile.extensions.len(), 2);
        let prepared = [profile.install_command(0).unwrap(), profile.install_command(1).unwrap()];
        for (index, expected) in
            ["original lean fixture", "original toml fixture"].iter().enumerate()
        {
            let snapshot = &profile.extensions[index];
            assert_eq!(fs::read_to_string(&snapshot.private_path).unwrap(), *expected);
            let args = prepared[index].get_args().collect::<Vec<_>>();
            assert!(args.iter().any(|arg| *arg == "--do-not-include-pack-dependencies"));
            assert!(args.iter().any(|arg| *arg == snapshot.private_path.as_os_str()));
        }
        fs::write(&vsix, "changed original lean").unwrap();
        fs::remove_file(&second).unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();
        for index in 0..2 {
            profile.install_command(index).unwrap();
        }
    }

    #[cfg(unix)]
    #[test]
    fn private_vsix_content_and_physical_replacement_fail_before_commands() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let private = &profile.extensions[0].private_path;
        let prepared = profile.install_command(0).unwrap();
        let original = fs::read(private).unwrap();
        fs::write(private, "changed fixture").unwrap();
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.install_command(0).is_err());
        fs::write(private, &original).unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();

        let relocated = temp.path().join("relocated-vsix");
        fs::rename(private, &relocated).unwrap();
        fs::copy(&relocated, private).unwrap();
        fs::set_permissions(private, fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(prepared.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.install_command(0).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn private_vsix_symlink_and_fifo_replacement_fail_without_opening_them() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        for fifo in [false, true] {
            let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix.clone()]).unwrap();
            let private = &profile.extensions[0].private_path;
            let relocated = temp.path().join(if fifo { "fifo-original" } else { "link-original" });
            fs::rename(private, &relocated).unwrap();
            if fifo {
                let status =
                    std::process::Command::new("/usr/bin/mkfifo").arg(private).status().unwrap();
                assert!(status.success());
            } else {
                std::os::unix::fs::symlink(&relocated, private).unwrap();
            }
            assert!(profile.check_owner(&workspace, &sdk).is_err());
            assert!(profile.install_command(0).is_err());
        }
    }

    #[test]
    fn empty_profile_cannot_fall_back_to_global_extensions() {
        let (temp, workspace, code, vsix) = fixture();
        let profile =
            Profile::prepare(&workspace, &temp.path().join("archive/lean-sdk"), &code, &[vsix])
                .unwrap();
        assert!(profile.check_required_extensions().is_err());
        for (publisher, name, version) in
            [("leanprover", "lean4", "0.0.240"), ("tamasfe", "even-better-toml", "0.21.2")]
        {
            let dir = profile.root.join("data/extensions").join(format!("{publisher}.{name}"));
            fs::create_dir(&dir).unwrap();
            fs::write(
                dir.join("package.json"),
                serde_json::to_vec(
                    &json!({"publisher": publisher, "name": name, "version": version}),
                )
                .unwrap(),
            )
            .unwrap();
        }
        profile.check_required_extensions().unwrap();
    }

    #[test]
    fn private_profile_requires_the_reviewed_toml_extension_version() {
        let (temp, workspace, code, vsix) = fixture();
        let profile =
            Profile::prepare(&workspace, &temp.path().join("archive/lean-sdk"), &code, &[vsix])
                .unwrap();
        let extensions = profile.root.join("data/extensions");
        let lean = extensions.join("leanprover.lean4");
        let toml = extensions.join("tamasfe.even-better-toml");
        fs::create_dir(&lean).unwrap();
        fs::create_dir(&toml).unwrap();
        fs::write(
            lean.join("package.json"),
            serde_json::to_vec(
                &json!({"publisher":"leanprover","name":"lean4","version":"0.0.240"}),
            )
            .unwrap(),
        )
        .unwrap();
        for version in
            [json!("0.0.240"), json!("0.21.1"), json!("0.21.3"), json!(""), json!(null), json!(21)]
        {
            fs::write(
                toml.join("package.json"),
                serde_json::to_vec(
                    &json!({"publisher":"tamasfe","name":"even-better-toml","version":version}),
                )
                .unwrap(),
            )
            .unwrap();
            assert!(
                profile
                    .check_required_extensions()
                    .unwrap_err()
                    .to_string()
                    .contains("TOML extension version is 0.21.2")
            );
        }
        fs::write(
            toml.join("package.json"),
            serde_json::to_vec(
                &json!({"publisher":"tamasfe","name":"even-better-toml","version":"0.21.2"}),
            )
            .unwrap(),
        )
        .unwrap();
        profile.check_required_extensions().unwrap();
    }

    #[test]
    fn explicit_state_parent_must_be_existing_and_outside_bound_inputs() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        fs::create_dir_all(&sdk).unwrap();
        let state = temp.path().join("editor-state");
        fs::create_dir(&state).unwrap();
        let profile =
            Profile::prepare_at(&workspace, &sdk, &code, &[vsix.clone()], Some(&state)).unwrap();
        assert!(profile.root.starts_with(state.canonicalize().unwrap()));
        for rejected in [
            PathBuf::from("relative"),
            temp.path().join("missing"),
            workspace,
            sdk.clone(),
            sdk.parent().unwrap().to_owned(),
        ] {
            assert!(
                Profile::prepare_at(
                    &temp.path().join("consumer"),
                    &sdk,
                    &code,
                    &[vsix.clone()],
                    Some(&rejected)
                )
                .is_err()
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn state_parent_rejects_permissions_granting_other_accounts_write_access() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let parent = temp.path().join("editor-state");
        fs::create_dir(&parent).unwrap();
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o770)).unwrap();
        assert!(
            Profile::prepare_at(&workspace, &sdk, &code, &[vsix.clone()], Some(&parent)).is_err()
        );
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o707)).unwrap();
        assert!(Profile::prepare_at(&workspace, &sdk, &code, &[vsix], Some(&parent)).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn state_parent_security_is_rechecked_for_existing_commands() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let parent = temp.path().join("editor-state");
        fs::create_dir(&parent).unwrap();
        let profile = Profile::prepare_at(&workspace, &sdk, &code, &[vsix], Some(&parent)).unwrap();
        let prepared = profile.command().unwrap();
        fs::set_permissions(&parent, fs::Permissions::from_mode(0o777)).unwrap();
        assert_eq!(prepared.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.command().is_err());
        assert!(profile.command_for(&code).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn fresh_profile_root_is_private_and_permission_changes_are_rejected() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let metadata = fs::symlink_metadata(&profile.root).unwrap();
        assert_eq!(metadata.uid(), effective_uid());
        assert_eq!(metadata.permissions().mode() & 0o077, 0);
        profile.check_owner(&workspace, &sdk).unwrap();

        let prepared = profile.command().unwrap();
        fs::set_permissions(&profile.root, fs::Permissions::from_mode(0o770)).unwrap();
        assert_eq!(prepared.get_program(), code.canonicalize().unwrap().as_os_str());
        assert!(profile.check_owner(&workspace, &sdk).is_err());
        assert!(profile.command().is_err());
        assert!(profile.command_for(&code).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn physical_profile_root_replacement_rejects_prepared_and_new_commands() {
        use std::os::unix::fs::PermissionsExt;

        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let prepared = profile.command().unwrap();
        profile.check_owner(&workspace, &sdk).unwrap();

        let original = temp.path().join("original-profile");
        fs::rename(&profile.root, &original).unwrap();
        fs::create_dir(&profile.root).unwrap();
        fs::set_permissions(&profile.root, fs::Permissions::from_mode(0o700)).unwrap();
        for relative in PROFILE_DIRECTORIES.into_iter().filter(|path| !path.is_empty()) {
            fs::create_dir_all(profile.root.join(relative)).unwrap();
        }
        for relative in ["binding.json", "data/user-data/User/settings.json"] {
            fs::copy(original.join(relative), profile.root.join(relative)).unwrap();
        }
        assert_eq!(prepared.get_program(), code.canonicalize().unwrap().as_os_str());
        let error = profile.check_owner(&workspace, &sdk).unwrap_err();
        assert!(error.to_string().contains("root identity changed"));
        assert!(profile.command().is_err());
        assert!(profile.command_for(&code).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn physical_directory_acls_admit_only_denials() {
        fn add_acl(path: &Path, entry: &str) {
            let status = std::process::Command::new("/bin/chmod")
                .args(["+a", entry])
                .arg(path)
                .status()
                .unwrap();
            assert!(status.success());
        }

        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        let no_acl = temp.path().join("no-acl");
        let deny = temp.path().join("deny");
        let allow = temp.path().join("allow");
        let mixed = temp.path().join("mixed");
        for path in [&no_acl, &deny, &allow, &mixed] {
            fs::create_dir(path).unwrap();
        }
        check_non_granting_acl(&no_acl).unwrap();
        add_acl(&deny, "everyone deny add_file");
        check_non_granting_acl(&deny).unwrap();
        add_acl(&allow, "everyone allow add_file");
        assert!(check_non_granting_acl(&allow).is_err());
        add_acl(&mixed, "everyone deny add_file");
        add_acl(&mixed, "everyone allow delete_child");
        assert!(check_non_granting_acl(&mixed).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn editor_ipc_path_limit_counts_bytes_including_socket_suffix() {
        let suffix = Path::new("data/user-data/xxxx-xxxxxx.sock");
        // One byte for the profile's leading slash and one for the join.
        let available = 103 - 2 - suffix.as_os_str().as_encoded_bytes().len();
        let longest = PathBuf::from(format!("/{}", "a".repeat(available)));
        assert_eq!(longest.join(suffix).as_os_str().as_encoded_bytes().len(), 103);
        check_ipc_path(&longest).unwrap();
        assert!(check_ipc_path(&PathBuf::from(format!("/{}", "a".repeat(available + 1)))).is_err());
        assert!(check_ipc_path(&PathBuf::from(format!("/{}", "é".repeat(available)))).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn failed_ipc_admission_removes_unreported_profile() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let state = temp.path().join("long-editor-state-".repeat(5));
        fs::create_dir(&state).unwrap();
        let error = Profile::prepare_at(&workspace, &sdk, &code, &[vsix], Some(&state))
            .err()
            .expect("long IPC path must be rejected");
        assert!(error.to_string().contains("IPC path is too long"));
        assert_eq!(fs::read_dir(state).unwrap().count(), 0);
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn gui_launch_requires_an_executable_inside_the_selected_bundle() {
        let (temp, _, code, _) = fixture();
        let plain = temp.path().join("plain-code");
        fs::write(&plain, "plain fixture").unwrap();
        assert!(editor_program(&plain).is_err());
        let contents = temp.path().join("Other.app/Contents");
        let cli = contents.join("Resources/app/bin/code");
        fs::create_dir_all(cli.parent().unwrap()).unwrap();
        fs::write(&cli, "cli").unwrap();
        let gui = contents.join("MacOS/Electron");
        assert!(editor_program(&cli).is_err());
        fs::create_dir_all(gui.parent().unwrap()).unwrap();
        fs::write(&gui, "gui").unwrap();
        assert!(editor_program(&cli).is_err());
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&gui, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(editor_program(&cli).unwrap(), gui.canonicalize().unwrap());
        fs::remove_file(&gui).unwrap();
        std::os::unix::fs::symlink(&code, &gui).unwrap();
        assert!(editor_program(&cli).is_err());
    }
}
