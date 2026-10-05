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
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use anyhow::{Context, Result, ensure};
use serde_json::json;

use crate::lean_sdk::Workspace;

/// A fresh editor instance bound to exactly one production workspace. Its state
/// persists after the CLI exits; it must not be removed while Code is running.
pub struct EditorHost<'w, 'sdk> {
    workspace: &'w Workspace<'sdk>,
    profile: Profile,
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
        check_ipc_path(&profile.root)?;
        Ok(Self { workspace, profile })
    }

    pub fn profile_root(&self) -> &Path {
        &self.profile.root
    }

    /// Record the actual selected editor version before using its CLI contract.
    pub fn version_command(&self) -> Result<Command> {
        self.workspace.admit()?;
        self.profile.check_owner(self.workspace.root(), self.workspace.sdk().root())?;
        let mut command = self.profile.command();
        command.arg("--version");
        Ok(command)
    }

    /// Execute sequentially, retaining nonzero failures. Every dependency must
    /// have been supplied explicitly; automatic pack/dependency fetching is off.
    pub fn install_commands(&self) -> Result<Vec<Command>> {
        self.workspace.admit()?;
        self.profile.check_owner(self.workspace.root(), self.workspace.sdk().root())?;
        self.profile
            .extensions
            .iter()
            .map(|extension| {
                ensure!(
                    regular_absolute(extension)? == *extension,
                    "Local extension artifact path changed"
                );
                let mut command = self.profile.command();
                command
                    .args(["--do-not-sync", "--do-not-include-pack-dependencies"])
                    .arg("--install-extension")
                    .arg(extension);
                Ok(command)
            })
            .collect()
    }

    /// The caller must first complete all installation commands. An empty or
    /// incomplete extension profile cannot silently fall back to global state.
    pub fn launch_command(&self) -> Result<Command> {
        self.workspace.admit()?;
        self.profile.check_owner(self.workspace.root(), self.workspace.sdk().root())?;
        self.profile.check_required_extensions()?;
        // The macOS shell CLI dispatches through LaunchServices and can detach
        // the GUI from its caller. Start the bundle executable directly so the
        // caller owns the editor process and can wait for or terminate it.
        let mut command = self.profile.command_for(&editor_program(&self.profile.code)?);
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
    workspace: PathBuf,
    sdk: PathBuf,
    code: PathBuf,
    extensions: Vec<PathBuf>,
    path: OsString,
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
        use std::os::unix::fs::PermissionsExt;
        ensure!(
            fs::metadata(&program)?.permissions().mode() & 0o111 != 0,
            "Code GUI executable is not executable"
        );
        Ok(program)
    }
    #[cfg(not(target_os = "macos"))]
    {
        regular_absolute(code)
    }
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
        let code = regular_absolute(code)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            ensure!(
                fs::metadata(&code)?.permissions().mode() & 0o111 != 0,
                "Code CLI is not executable"
            );
        }
        let extensions = extensions
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
        let path = std::env::join_paths([
            workspace.join(".anneal-bin"),
            PathBuf::from("/usr/bin"),
            PathBuf::from("/bin"),
            PathBuf::from("/usr/sbin"),
            PathBuf::from("/sbin"),
        ])?;
        // Chromium's singleton/socket symlinks must not enter .runtime, whose
        // compiler-output admission deliberately rejects links recursively.
        let root = tempfile::Builder::new().prefix("ae-").rand_bytes(6).tempdir_in(parent)?.keep();
        let profile = Self {
            root,
            workspace: workspace.to_owned(),
            sdk: sdk.to_owned(),
            code,
            extensions,
            path,
        };
        for dir in [
            "home",
            "elan",
            "config",
            "cache",
            "xdg-data",
            "tmp",
            "data/user-data/User",
            "data/extensions",
            "data/tmp",
        ] {
            fs::create_dir_all(profile.root.join(dir))?;
        }
        fs::write(profile.root.join("binding.json"), serde_json::to_vec_pretty(&profile.owner())?)?;
        let settings = json!({
            "lean4.envPathExtensions": [workspace.join(".anneal-bin")],
            "lean4.automaticallyBuildDependencies": false,
            "lean4.logging.enabled": false,
            "lean4.showSetupWarnings": false,
            "lean4.serverArgs": [],
            "extensions.autoUpdate": false,
            "extensions.autoCheckUpdates": false,
            "update.mode": "none",
            "telemetry.telemetryLevel": "off",
            "terminal.integrated.inheritEnv": false
            ,"git.enabled": false
        });
        fs::write(
            profile.root.join("data/user-data/User/settings.json"),
            serde_json::to_vec_pretty(&settings)?,
        )?;
        Ok(profile)
    }

    fn owner(&self) -> serde_json::Value {
        json!({"schema": 1, "workspace": self.workspace, "sdk_root": self.sdk,
            "code": self.code, "extensions": self.extensions, "profile": self.root})
    }

    fn check_owner(&self, workspace: &Path, sdk: &Path) -> Result<()> {
        ensure!(workspace == self.workspace && sdk == self.sdk, "Editor workspace binding changed");
        let owner: serde_json::Value =
            serde_json::from_slice(&fs::read(self.root.join("binding.json"))?)?;
        ensure!(owner == self.owner(), "Private editor profile ownership changed");
        ensure!(
            regular_absolute(&self.code)? == self.code,
            "Selected Code executable path changed"
        );
        Ok(())
    }

    fn command(&self) -> Command {
        self.command_for(&self.code)
    }

    fn command_for(&self, program: &Path) -> Command {
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
        command
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
            toml |= id == "tamasfe.even-better-toml";
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

    fn fixture() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        let temp = tempfile::tempdir().unwrap();
        let workspace = temp.path().join("consumer");
        fs::create_dir(&workspace).unwrap();
        let code = temp.path().join("code");
        fs::write(&code, "unused fixture").unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&code, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let vsix = temp.path().join("lean.vsix");
        fs::write(&vsix, "unused fixture").unwrap();
        (temp, workspace, code, vsix)
    }

    #[test]
    fn private_commands_have_only_owned_environment_and_finite_arguments() {
        let (temp, workspace, code, vsix) = fixture();
        let sdk = temp.path().join("archive/lean-sdk");
        let profile = Profile::prepare(&workspace, &sdk, &code, &[vsix]).unwrap();
        let command = profile.command();
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
    fn empty_profile_cannot_fall_back_to_global_extensions() {
        let (temp, workspace, code, vsix) = fixture();
        let profile =
            Profile::prepare(&workspace, &temp.path().join("archive/lean-sdk"), &code, &[vsix])
                .unwrap();
        assert!(profile.check_required_extensions().is_err());
        for (publisher, name) in [("leanprover", "lean4"), ("tamasfe", "even-better-toml")] {
            let dir = profile.root.join("data/extensions").join(format!("{publisher}.{name}"));
            fs::create_dir(&dir).unwrap();
            fs::write(
                dir.join("package.json"),
                serde_json::to_vec(
                    &json!({"publisher": publisher, "name": name, "version": "0.0.240"}),
                )
                .unwrap(),
            )
            .unwrap();
        }
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
    fn gui_launch_requires_an_executable_inside_the_selected_bundle() {
        let (temp, _, code, _) = fixture();
        assert!(editor_program(&code).is_err());
        let contents = temp.path().join("Code.app/Contents");
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
