//! Subcommand for installing Anneal dependencies.

use std::{path::PathBuf, process::Command};

use anyhow::Context as _;

pub struct SetupArgs {
    pub local_archive: Option<PathBuf>,
}

pub const CONFIG: exocrate::Config = exocrate::Config {
    rel_dir_path: &["anneal", "toolchain"],
    version_slug: env!("ANNEAL_EXOCRATE_VERSION_SLUG"),
};

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
const AENEAS_BACKENDS_DIR: &str = "backends";
const AENEAS_LEAN_DIR: &str = "lean";
const BIN_DIR: &str = "bin";
const LIB_DIR: &str = "lib";
const LEAN_SYSROOT: &str = "lean";
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

    pub fn bin_dir(&self) -> PathBuf {
        self.aeneas_bin_dir()
    }

    pub fn cache_dir(&self) -> PathBuf {
        self.root.join("lake-cache")
    }

    pub fn aeneas_root(&self) -> PathBuf {
        self.root.join(AENEAS_DIR)
    }

    pub fn aeneas_bin_dir(&self) -> PathBuf {
        self.aeneas_root().join(BIN_DIR)
    }

    pub fn aeneas_lean_dir(&self) -> PathBuf {
        self.aeneas_root().join(AENEAS_BACKENDS_DIR).join(AENEAS_LEAN_DIR)
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

    pub fn lean_sysroot(&self) -> PathBuf {
        self.root.join(LEAN_SYSROOT)
    }

    pub fn lean_bin(&self) -> PathBuf {
        self.lean_sysroot().join(BIN_DIR)
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

    let installation_dir = CONFIG
        .resolve_installation_dir_or_install(location(), source)
        .context("failed to resolve-or-install dependencies")?;
    log::info!("anneal toolchain is installed at {:?}", installation_dir);
    Ok(())
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

    #[test]
    fn tool_paths_use_omnibus_layout() {
        let toolchain = Toolchain { root: PathBuf::from("/tmp/toolchain") };

        assert_eq!(toolchain.bin_dir(), PathBuf::from("/tmp/toolchain/aeneas/bin"));
        assert_eq!(
            toolchain.aeneas_lean_dir(),
            PathBuf::from("/tmp/toolchain/aeneas/backends/lean")
        );
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
