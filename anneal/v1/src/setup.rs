//! Subcommand for installing Anneal dependencies.

use std::{
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::Context as _;

pub struct SetupArgs {
    pub local_archive: Option<PathBuf>,
}

pub const CONFIG: exocrate::Config =
    exocrate::Config::new(&["anneal", "toolchain"], env!("ANNEAL_EXOCRATE_VERSION_SLUG"));

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tool {
    Charon,
    #[allow(dead_code)]
    CharonDriver,
    Aeneas,
}

impl Tool {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Charon => "charon",
            Self::CharonDriver => "charon-driver",
            Self::Aeneas => "aeneas",
        }
    }

    pub fn path(&self, toolchain: &Toolchain) -> PathBuf {
        match self {
            Self::Charon | Self::CharonDriver | Self::Aeneas => {
                toolchain.aeneas_bin_dir().join(self.name())
            }
        }
    }
}

const AENEAS_DIR: &str = "aeneas";
const BIN_DIR: &str = "bin";
const LIB_DIR: &str = "lib";
const RUST_SYSROOT: &str = "rust";

pub struct Toolchain {
    pub root: PathBuf,
}

impl Toolchain {
    pub fn resolve() -> anyhow::Result<Self> {
        let root = CONFIG
            .resolve_installation_dir(location())
            .context("Toolchain not installed. Please run 'cargo anneal setup' first.")?;
        Ok(Self { root })
    }

    /// Select managed generator tools from the installation captured during SDK
    /// admission, rather than resolving a mutable configured alias again.
    pub fn from_admitted_sdk(sdk: &crate::lean_sdk::LeanSdk) -> Self {
        Self {
            root: sdk
                .root()
                .parent()
                .expect("Admitted SDK has an installation parent")
                .to_path_buf(),
        }
    }

    /// Resolve the publisher-admitted Lean installation without modifying an
    /// existing archive or falling back to ambient Elan/Lean executables.
    pub fn lean_sdk(&self) -> anyhow::Result<crate::lean_sdk::LeanSdk> {
        let sdk = crate::lean_sdk::LeanSdk::load(&self.root.join("lean-sdk")).context(
            "Toolchain has no admitted Lean SDK; install a matching published toolchain",
        )?;
        anyhow::ensure!(
            sdk.lean_toolchain() == env!("ANNEAL_LEAN_TOOLCHAIN"),
            "Published SDK Lean toolchain does not match this Anneal version"
        );
        Ok(sdk)
    }

    pub fn bin_dir(&self) -> PathBuf {
        self.aeneas_bin_dir()
    }

    pub fn aeneas_root(&self) -> PathBuf {
        self.root.join(AENEAS_DIR)
    }

    pub fn aeneas_bin_dir(&self) -> PathBuf {
        self.aeneas_root().join(BIN_DIR)
    }

    pub fn rust_sysroot(&self) -> PathBuf {
        self.root.join(RUST_SYSROOT)
    }

    pub fn rust_bin(&self) -> PathBuf {
        self.rust_sysroot().join(BIN_DIR)
    }

    pub fn rust_lib(&self) -> PathBuf {
        self.rust_sysroot().join(LIB_DIR)
    }

    pub fn command(&self, tool: Tool) -> Command {
        if std::env::var("ANNEAL_USE_PATH_FOR_TOOLS").is_ok() {
            Command::new(tool.name())
        } else {
            Command::new(tool.path(self))
        }
    }
}

pub fn run_setup(args: SetupArgs) -> anyhow::Result<()> {
    let local_archive = args
        .local_archive
        .or_else(|| std::env::var_os("ANNEAL_SETUP_LOCAL_ARCHIVE").map(PathBuf::from));
    let source = match local_archive {
        Some(local_archive) => exocrate::Source::Local(local_archive),
        None => exocrate::Source::Remote(remote_archive()),
    };

    let (installation_dir, status) = CONFIG
        .resolve_installation_dir_or_install_with_validation(
            location(),
            source,
            validate_toolchain_installation,
        )
        .context("failed to resolve-or-install admitted dependencies")?;
    // Staging admission is read-only and its SDK object is discarded. Reload
    // the published path rather than retaining paths into the renamed stage.
    Toolchain { root: installation_dir.clone() }.lean_sdk()?;
    log::info!("anneal toolchain {:?} at {:?}", status, installation_dir);
    Ok(())
}

fn validate_toolchain_installation(root: &Path) -> std::io::Result<()> {
    Toolchain { root: root.to_path_buf() }.lean_sdk().map(|_| ()).map_err(|error| {
        std::io::Error::other(format!(
            "Toolchain SDK admission failed at {} (existing installations are preserved): {error:#}",
            root.display(),
        ))
    })
}

fn location() -> exocrate::Location {
    if let Some(dir) = std::env::var_os("ANNEAL_TOOLCHAIN_DIR") {
        exocrate::Location::Custom(PathBuf::from(dir))
    } else if std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok()
        || std::env::var("__ANNEAL_LOCAL_DEV").is_ok()
    {
        exocrate::Location::LocalDev
    } else {
        exocrate::Location::UserGlobal
    }
}

fn remote_archive() -> exocrate::RemoteArchive {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("linux", "x86_64") => remote_archive_for(
            env!("ANNEAL_EXOCRATE_LINUX_X86_64_URL"),
            env!("ANNEAL_EXOCRATE_LINUX_X86_64_SHA256"),
        ),
        ("macos", "x86_64") => remote_archive_for(
            env!("ANNEAL_EXOCRATE_MACOS_X86_64_URL"),
            env!("ANNEAL_EXOCRATE_MACOS_X86_64_SHA256"),
        ),
        ("linux", "aarch64") => remote_archive_for(
            env!("ANNEAL_EXOCRATE_LINUX_AARCH64_URL"),
            env!("ANNEAL_EXOCRATE_LINUX_AARCH64_SHA256"),
        ),
        ("macos", "aarch64") => remote_archive_for(
            env!("ANNEAL_EXOCRATE_MACOS_AARCH64_URL"),
            env!("ANNEAL_EXOCRATE_MACOS_AARCH64_SHA256"),
        ),
        (os, arch) => panic!("unsupported platform: {os}-{arch}"),
    }
}

fn remote_archive_for(url: &'static str, sha256: &'static str) -> exocrate::RemoteArchive {
    exocrate::RemoteArchive {
        url,
        sha256: decode_hex(sha256).expect("package.metadata.exocrate sha256 must be valid hex"),
    }
}

fn decode_hex(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut res = [0u8; 32];
    for i in 0..32 {
        let h_nib = decode_nibble(bytes[i * 2])?;
        let l_nib = decode_nibble(bytes[i * 2 + 1])?;
        res[i] = (h_nib << 4) | l_nib;
    }
    Some(res)
}

fn decode_nibble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn managed_tools_keep_the_admitted_installation_after_alias_retarget() {
        use std::os::unix::fs::symlink;

        use crate::lean_sdk::{LakeLibrary, LeanSdk, Workspace, tests::Fixture};

        const CHILD: &str = "ANNEAL_TEST_ADMITTED_TOOLCHAIN_CHILD";
        let Some(mode) = std::env::var_os(CHILD) else {
            for mode in ["managed", "path"] {
                let mut child = Command::new(std::env::current_exe().unwrap());
                child.arg("setup::tests::managed_tools_keep_the_admitted_installation_after_alias_retarget")
                    .arg("--exact").arg("--test-threads=1")
                    .env(CHILD, mode).env_remove("ANNEAL_USE_PATH_FOR_TOOLS");
                if mode == "path" {
                    child.env("ANNEAL_USE_PATH_FOR_TOOLS", "1");
                }
                let output = child.output().unwrap();
                assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
                assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed"));
            }
            return;
        };
        assert!(mode == "managed" || mode == "path");
        for different_id in [false, true] {
            let first = Fixture::new(&["Shared.A"]);
            let second = Fixture::new(&["Shared.A"]);
            if different_id {
                let descriptor = second.sdk.root().join("sdk.json");
                let mut value: serde_json::Value =
                    serde_json::from_slice(&std::fs::read(&descriptor).unwrap()).unwrap();
                value["id"] = serde_json::json!("c".repeat(64));
                std::fs::write(descriptor, serde_json::to_vec(&value).unwrap()).unwrap();
            }
            let temp = tempfile::tempdir().unwrap();
            let alias = temp.path().join("installation");
            symlink(first.sdk.root().parent().unwrap(), &alias).unwrap();
            let admitted = LeanSdk::load(&alias.join("lean-sdk")).unwrap();
            let workspace =
                Workspace::create(&admitted, &temp.path().join("workspace"), &["user"]).unwrap();
            Workspace::write_lakefile(
                &admitted,
                workspace.root(),
                &[LakeLibrary { name: "User", source_root: "user", modules: &[] }],
            )
            .unwrap();
            std::fs::create_dir(workspace.root().join("user")).unwrap();
            std::fs::write(workspace.root().join("user/Proof.lean"), "def proof := 1\n").unwrap();
            let binding = std::fs::read(workspace.root().join(".anneal-sdk.json")).unwrap();
            let _writer = workspace.writer_lock().unwrap();
            std::fs::remove_file(&alias).unwrap();
            symlink(second.sdk.root().parent().unwrap(), &alias).unwrap();
            let newly_resolved = LeanSdk::load(&alias.join("lean-sdk")).unwrap();
            assert_eq!(newly_resolved.id() != admitted.id(), different_id);
            assert_ne!(newly_resolved.root(), admitted.root());
            let toolchain = Toolchain::from_admitted_sdk(&admitted);
            let installation = first.sdk.root().parent().unwrap();
            assert_eq!(toolchain.root, installation);
            assert_eq!(toolchain.rust_sysroot(), installation.join("rust"));
            assert_eq!(toolchain.rust_bin(), installation.join("rust/bin"));
            assert_eq!(toolchain.rust_lib(), installation.join("rust/lib"));
            for tool in [Tool::Aeneas, Tool::Charon, Tool::CharonDriver] {
                assert_eq!(
                    tool.path(&toolchain),
                    installation.join("aeneas/bin").join(tool.name())
                );
                let command = toolchain.command(tool);
                let expected =
                    if mode == "path" { PathBuf::from(tool.name()) } else { tool.path(&toolchain) };
                assert_eq!(command.get_program(), expected.as_os_str());
            }
            workspace.admit().unwrap();
            assert_eq!(workspace.sdk().root(), first.sdk.root());
            assert_eq!(std::fs::read(workspace.root().join(".anneal-sdk.json")).unwrap(), binding);
            assert_eq!(
                std::fs::read_to_string(workspace.root().join("user/Proof.lean")).unwrap(),
                "def proof := 1\n"
            );
            assert!(workspace.try_shared_lock().unwrap().is_none());
        }
    }

    #[cfg(unix)]
    fn copy_fixture_installation(source: &Path, target: &Path) {
        std::fs::create_dir(target).unwrap();
        for entry in walkdir::WalkDir::new(source).min_depth(1) {
            let entry = entry.unwrap();
            let to = target.join(entry.path().strip_prefix(source).unwrap());
            if entry.file_type().is_dir() {
                std::fs::create_dir(&to).unwrap();
            } else {
                assert!(entry.file_type().is_file());
                std::fs::copy(entry.path(), &to).unwrap();
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn staging_sdk_validation_rejects_damage_and_reloads_after_relocation() {
        use crate::lean_sdk::tests::Fixture;
        let fixture = Fixture::new(&["Shared.A"]);
        for damage in ["missing", "malformed", "manifest", "tuple"] {
            let temp = tempfile::tempdir().unwrap();
            let stage = temp.path().join("installation.staging");
            copy_fixture_installation(fixture.sdk.root().parent().unwrap(), &stage);
            let descriptor_path = stage.join("lean-sdk/sdk.json");
            let manifest_path = stage.join("lean-sdk/modules.json");
            let descriptor = std::fs::read(&descriptor_path).unwrap();
            let manifest = std::fs::read(&manifest_path).unwrap();
            match damage {
                "missing" => std::fs::remove_file(&descriptor_path).unwrap(),
                "malformed" => std::fs::write(&descriptor_path, b"{").unwrap(),
                "manifest" => {
                    std::fs::write(&manifest_path, br#"{"schema":1,"modules":["Changed.A"]}"#)
                        .unwrap()
                }
                "tuple" => {
                    let mut value: serde_json::Value = serde_json::from_slice(&descriptor).unwrap();
                    value["lean_toolchain"] = serde_json::json!("leanprover/lean4:v0.0.0");
                    std::fs::write(&descriptor_path, serde_json::to_vec(&value).unwrap()).unwrap();
                }
                _ => unreachable!(),
            }
            let before = std::fs::read(&descriptor_path).ok();
            let error = validate_toolchain_installation(&stage).unwrap_err();
            assert!(error.to_string().contains("Toolchain SDK admission failed"));
            assert_eq!(std::fs::read(&descriptor_path).ok(), before);
            // A corrected tree at the same staging path is admissible. The
            // exocrate tests exercise rejection and retry of actual archives.
            std::fs::write(&descriptor_path, descriptor).unwrap();
            std::fs::write(&manifest_path, manifest).unwrap();
            validate_toolchain_installation(&stage).unwrap();
            let final_root = temp.path().join("installation");
            std::fs::rename(&stage, &final_root).unwrap();
            let reloaded = Toolchain { root: final_root.clone() }.lean_sdk().unwrap();
            assert_eq!(
                reloaded.root(),
                std::fs::canonicalize(final_root.join("lean-sdk")).unwrap()
            );
            assert_eq!(
                Toolchain::from_admitted_sdk(&reloaded).root,
                std::fs::canonicalize(&final_root).unwrap()
            );
            assert!(!stage.exists());
            validate_toolchain_installation(&final_root).unwrap();
        }
    }

    #[test]
    fn tool_paths_use_omnibus_layout() {
        let toolchain = Toolchain { root: PathBuf::from("/tmp/toolchain") };

        assert_eq!(toolchain.bin_dir(), PathBuf::from("/tmp/toolchain/aeneas/bin"));
        assert_eq!(
            Tool::Charon.path(&toolchain),
            PathBuf::from("/tmp/toolchain/aeneas/bin/charon")
        );
        assert_eq!(
            Tool::Aeneas.path(&toolchain),
            PathBuf::from("/tmp/toolchain/aeneas/bin/aeneas")
        );
    }
}
