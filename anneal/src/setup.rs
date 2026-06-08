//! Subcommand for installing Anneal dependencies.

use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    time::SystemTime,
};

use anyhow::{Context as _, Result};
use walkdir::WalkDir;

pub struct SetupArgs {
    pub local_archive: Option<PathBuf>,
}

pub const CONFIG: exocrate::Config = exocrate::Config {
    rel_dir_path: &[".anneal", "toolchain"],
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
        let toolchain = Self { root };
        toolchain.prepare_lake_packages()?;
        Ok(toolchain)
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

    fn prepare_lake_packages(&self) -> Result<()> {
        let aeneas_root = self.aeneas_root();
        make_lake_config_dirs_writable(&aeneas_root)?;
        normalize_lake_input_mtimes(&aeneas_root)
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
    Toolchain { root: installation_dir.clone() }
        .prepare_lake_packages()
        .context("failed to prepare Lake package directories")?;
    log::info!("anneal toolchain is installed at {:?}", installation_dir);
    Ok(())
}

fn make_lake_config_dirs_writable(root: &Path) -> Result<()> {
    if !root.exists() {
        return Ok(());
    }

    let mut entries = WalkDir::new(root).into_iter();
    while let Some(entry) = entries.next() {
        let entry = entry.with_context(|| format!("Failed to walk {}", root.display()))?;
        let path = entry.path();

        if entry.file_type().is_dir() && is_lake_dir(path) {
            ensure_lake_config_dir_writable(path)?;
            entries.skip_current_dir();
        }
    }

    Ok(())
}

fn ensure_lake_config_dir_writable(lake_dir: &Path) -> Result<()> {
    let config_dir = lake_dir.join("config");
    if !config_dir.exists() {
        let original_permissions = fs::symlink_metadata(lake_dir)
            .with_context(|| format!("Failed to stat {}", lake_dir.display()))?
            .permissions();
        make_writable(lake_dir)?;
        fs::create_dir_all(&config_dir)
            .with_context(|| format!("Failed to create {}", config_dir.display()))?;
        fs::set_permissions(lake_dir, original_permissions)
            .with_context(|| format!("Failed to restore permissions on {}", lake_dir.display()))?;
    }
    make_tree_writable(&config_dir)
}

fn make_tree_writable(root: &Path) -> Result<()> {
    for entry in WalkDir::new(root) {
        let entry = entry.with_context(|| format!("Failed to walk {}", root.display()))?;
        make_writable(entry.path())?;
    }
    Ok(())
}

fn make_writable(path: &Path) -> Result<()> {
    let metadata =
        fs::symlink_metadata(path).with_context(|| format!("Failed to stat {}", path.display()))?;
    if metadata.file_type().is_symlink() {
        return Ok(());
    }
    let mut perms = metadata.permissions();
    if perms.readonly() {
        #[allow(clippy::permissions_set_readonly_false)]
        perms.set_readonly(false);
        fs::set_permissions(path, perms)
            .with_context(|| format!("Failed to make {} writable", path.display()))?;
    }
    Ok(())
}

fn is_lake_dir(path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == ".lake")
}

fn normalize_lake_input_mtimes(root: &Path) -> Result<()> {
    let mut entries = WalkDir::new(root).into_iter();
    while let Some(entry) = entries.next() {
        let entry = entry.with_context(|| format!("Failed to walk {}", root.display()))?;
        let path = entry.path();

        if entry.file_type().is_dir() && is_lake_build_dir(path) {
            entries.skip_current_dir();
            continue;
        }

        if !entry.file_type().is_file() || !is_lake_input_file(path) {
            continue;
        }

        let file = fs::File::open(path)
            .with_context(|| format!("Failed to open {} to normalize mtime", path.display()))?;
        file.set_times(fs::FileTimes::new().set_modified(SystemTime::UNIX_EPOCH))
            .with_context(|| format!("Failed to normalize mtime for {}", path.display()))?;
    }

    Ok(())
}

fn is_lake_build_dir(path: &Path) -> bool {
    path.file_name().is_some_and(|name| name == "build")
        && path.parent().and_then(Path::file_name).is_some_and(|name| name == ".lake")
}

fn is_lake_input_file(path: &Path) -> bool {
    if path.extension().and_then(|ext| ext.to_str()) == Some("lean") {
        return true;
    }

    matches!(
        path.file_name().and_then(|name| name.to_str()),
        Some("lakefile.lean" | "lakefile.toml" | "lake-manifest.json" | "lean-toolchain")
    )
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

    #[test]
    fn lake_config_fixup_leaves_build_cache_readonly() {
        let temp = tempfile::tempdir().unwrap();
        let aeneas_root = temp.path().join("aeneas");
        let source_file = aeneas_root.join("backends/lean/Aeneas.lean");
        let config_file = aeneas_root.join("backends/lean/.lake/config/aeneas/lakefile.olean");
        let build_file = aeneas_root.join("backends/lean/.lake/build/lib/lean/Aeneas.olean");
        let package_lake_dir = aeneas_root.join("packages/MiniDep/.lake");

        std::fs::create_dir_all(source_file.parent().unwrap()).unwrap();
        std::fs::create_dir_all(config_file.parent().unwrap()).unwrap();
        std::fs::create_dir_all(build_file.parent().unwrap()).unwrap();
        std::fs::create_dir_all(package_lake_dir.join("build")).unwrap();
        std::fs::write(&source_file, "import Aeneas").unwrap();
        std::fs::write(&config_file, "config").unwrap();
        std::fs::write(&build_file, "build").unwrap();

        make_tree_readonly(&aeneas_root);
        Toolchain { root: temp.path().to_path_buf() }.prepare_lake_packages().unwrap();

        let package_config_dir = package_lake_dir.join("config");
        assert!(package_config_dir.is_dir());
        assert!(!std::fs::metadata(&package_config_dir).unwrap().permissions().readonly());
        assert!(
            !std::fs::metadata(config_file.parent().unwrap()).unwrap().permissions().readonly()
        );
        assert!(!std::fs::metadata(&config_file).unwrap().permissions().readonly());
        assert!(std::fs::metadata(&build_file).unwrap().permissions().readonly());
        assert_eq!(modified_secs(&source_file), 0);
        assert_ne!(modified_secs(&build_file), 0);

        make_tree_writable(&aeneas_root).unwrap();
    }

    fn modified_secs(path: &Path) -> u64 {
        std::fs::metadata(path)
            .unwrap()
            .modified()
            .unwrap()
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap()
            .as_secs()
    }

    fn make_tree_readonly(root: &Path) {
        for entry in WalkDir::new(root).contents_first(true) {
            let entry = entry.unwrap();
            let mut perms = std::fs::metadata(entry.path()).unwrap().permissions();
            perms.set_readonly(true);
            std::fs::set_permissions(entry.path(), perms).unwrap();
        }
    }
}
