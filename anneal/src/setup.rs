//! Subcommand for installing Anneal dependencies.
//!
//! This module handles the automated download, verification, and installation
//! of `charon`, `charon-driver`, and `aeneas`.

use std::{fs, io::Read, path::Path, process::Command};

use anyhow::{Context, Result, bail};
use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};
use tar::Archive;
use tempfile;
use walkdir::WalkDir;

use crate::util::DirLock;

const MOCK_RUSTC_HASH: [u8; 32] = const {
    decode_hex("0d98244543ccb295295e0e9b335fbace9e06e8121bbdad6135773bca27f507f5")
        .expect("valid hex")
};
const MOCK_RUST_STD_HASH: [u8; 32] = const {
    decode_hex("31d62a14beb156f010188c39cb5e6069fa6f4f0d48e06f961a9888cf9263d8c6")
        .expect("valid hex")
};
const MOCK_RUSTC_DEV_HASH: [u8; 32] = const {
    decode_hex("7680c83ea3ab6bae514155ee3924d9b452e6f6c852552a266943142806653a8c")
        .expect("valid hex")
};
const MOCK_LLVM_TOOLS_HASH: [u8; 32] = const {
    decode_hex("c44c8e08c9e1411589402262a960226918d5051f77bd76912a3cb09c3393f198")
        .expect("valid hex")
};
const MOCK_MIRI_HASH: [u8; 32] = const {
    decode_hex("c093bdc1b9749b19ae3f93e3a6d58c901b5d94d09b80690f24e060d1a121a4d7")
        .expect("valid hex")
};
const MOCK_RUST_SRC_HASH: [u8; 32] = const {
    decode_hex("c2aa19f097efaa4d789911e3b1b4c1bb8379e4ac4ce66c47d60d0144f0307482")
        .expect("valid hex")
};

macro_rules! decode_hex_env {
    ($key:expr) => {
        const { decode_hex(env!($key)).expect("valid hex") }
    };
}

/// Supported platforms for Anneal dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Platform {
    LinuxX86_64,
    LinuxAArch64,
    MacosAArch64,
    MacosX86_64,
}

/// A specific tool or component within an Anneal dependency.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Tool {
    Charon,
    CharonDriver,
    Aeneas,
    Lake,
    Rustc,
    Miri,
    RustStd,
    RustcDev,
    LlvmTools,
    RustSrc,
}

impl Tool {
    /// Returns the name of the binary or component for this tool.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Charon => "charon",
            Self::CharonDriver => "charon-driver",
            Self::Aeneas => "aeneas",
            Self::Lake => "lake",
            Self::Rustc => "rustc",
            Self::Miri => "miri",
            Self::RustStd => "rust-std",
            Self::RustcDev => "rustc-dev",
            Self::LlvmTools => "llvm-tools",
            Self::RustSrc => "rust-src",
        }
    }
}

impl Platform {
    /// Returns the target triple for this platform.
    pub fn triple(&self) -> &'static str {
        match self {
            Self::LinuxX86_64 => "x86_64-unknown-linux-gnu",
            Self::LinuxAArch64 => "aarch64-unknown-linux-gnu",
            Self::MacosAArch64 => "aarch64-apple-darwin",
            Self::MacosX86_64 => "x86_64-apple-darwin",
        }
    }

    /// Detects the current host platform.
    pub fn detect() -> Result<Self> {
        let os = std::env::consts::OS;
        let arch = std::env::consts::ARCH;

        match (os, arch) {
            ("linux", "x86_64") => Ok(Self::LinuxX86_64),
            ("linux", "aarch64") => Ok(Self::LinuxAArch64),
            ("macos", "aarch64") => Ok(Self::MacosAArch64),
            ("macos", "x86_64") => Ok(Self::MacosX86_64),
            _ => bail!("Unsupported platform: {}-{}", os, arch),
        }
    }

    /// Returns the expected SHA-256 checksum for the specified archive on this
    /// platform.
    ///
    /// These hashes are baked into the binary at compile time from values
    /// provided by `build.rs` from the project's `Cargo.toml`. This ensures
    /// that we always download and verify the exact versions of dependencies
    /// that this version of Anneal was built to work with.
    pub fn expected_archive_hash(&self) -> [u8; 32] {
        use Platform::*;
        match self {
            LinuxX86_64 => decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_X86_64"),
            LinuxAArch64 => decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_AARCH64"),
            MacosAArch64 => decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_AARCH64"),
            MacosX86_64 => decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_X86_64"),
        }
    }

    /// Returns the expected SHA-256 checksum for a specific binary on this
    /// platform.
    ///
    /// This is used for verifying individual binaries within a toolchain,
    /// allowing the `setup` command to detect and repair corruption of any
    /// of the toolchain components.
    pub fn expected_bin_hash(&self, tool: Tool) -> [u8; 32] {
        if std::env::var("__ANNEAL_USE_MOCK_RUST_HASHES").is_ok() {
            // When testing with mock Rust hashes, we intercept requests for Rust
            // components and return the hardcoded mock hashes. For non-Rust
            // tools, we fall through to the normal logic that reads hashes from
            // environment variables.
            //
            // This approach is acceptable from a security perspective because:
            // 1. The mock hashes are hardcoded in the binary and cannot be
            //    overridden by an attacker via environment variables.
            // 2. The mock archives only contain inert, empty files. Even if an
            //    attacker forces the use of these mocks, they can only cause
            //    the tool to fail to run, but cannot inject malicious behavior.
            use Tool::*;
            match tool {
                Rustc => return MOCK_RUSTC_HASH,
                RustStd => return MOCK_RUST_STD_HASH,
                RustcDev => return MOCK_RUSTC_DEV_HASH,
                LlvmTools => return MOCK_LLVM_TOOLS_HASH,
                Miri => return MOCK_MIRI_HASH,
                RustSrc => return MOCK_RUST_SRC_HASH,
                Charon | CharonDriver | Aeneas | Lake => {}
            }
        }

        use Platform::*;
        match (self, tool) {
            // Rust components
            (LinuxX86_64, Tool::Rustc) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_X86_64_RUSTC")
            }
            (LinuxX86_64, Tool::RustStd) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_X86_64_RUST_STD")
            }
            (LinuxX86_64, Tool::RustcDev) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_X86_64_RUSTC_DEV")
            }
            (LinuxX86_64, Tool::LlvmTools) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_X86_64_LLVM_TOOLS_PREVIEW")
            }
            (LinuxX86_64, Tool::Miri) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_X86_64_MIRI_PREVIEW")
            }

            (LinuxAArch64, Tool::Rustc) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_AARCH64_RUSTC")
            }
            (LinuxAArch64, Tool::RustStd) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_AARCH64_RUST_STD")
            }
            (LinuxAArch64, Tool::RustcDev) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_AARCH64_RUSTC_DEV")
            }
            (LinuxAArch64, Tool::LlvmTools) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_AARCH64_LLVM_TOOLS_PREVIEW")
            }
            (LinuxAArch64, Tool::Miri) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_LINUX_AARCH64_MIRI_PREVIEW")
            }

            (MacosX86_64, Tool::Rustc) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_X86_64_RUSTC")
            }
            (MacosX86_64, Tool::RustStd) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_X86_64_RUST_STD")
            }
            (MacosX86_64, Tool::RustcDev) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_X86_64_RUSTC_DEV")
            }
            (MacosX86_64, Tool::LlvmTools) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_X86_64_LLVM_TOOLS_PREVIEW")
            }
            (MacosX86_64, Tool::Miri) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_X86_64_MIRI_PREVIEW")
            }

            (MacosAArch64, Tool::Rustc) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_AARCH64_RUSTC")
            }
            (MacosAArch64, Tool::RustStd) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_AARCH64_RUST_STD")
            }
            (MacosAArch64, Tool::RustcDev) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_AARCH64_RUSTC_DEV")
            }
            (MacosAArch64, Tool::LlvmTools) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_AARCH64_LLVM_TOOLS_PREVIEW")
            }
            (MacosAArch64, Tool::Miri) => {
                decode_hex_env!("ANNEAL_RUST_CHECKSUM_MACOS_AARCH64_MIRI_PREVIEW")
            }

            (_, Tool::RustSrc) => decode_hex_env!("ANNEAL_RUST_CHECKSUM_RUST_SRC"),

            _ => {
                unreachable!("unsupported tool combination for individual verification")
            }
        }
    }
}

pub struct Toolchain {
    pub root: std::path::PathBuf,
    // Holds the shared lock for the lifetime of the Toolchain object.
    _lock: Option<DirLock>,
}

impl Toolchain {
    /// Resolves the toolchain manager and acquires a shared lock.
    pub fn resolve() -> Result<Self> {
        let home = if let Ok(dir) = std::env::var("ANNEAL_TOOLCHAIN_DIR") {
            std::path::PathBuf::from(dir)
        } else if std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok() {
            let base = std::env::var("CARGO_MANIFEST_DIR")
                .map(std::path::PathBuf::from)
                // Fall back to current directory if CARGO_MANIFEST_DIR is not set,
                // which can happen if the binary is executed directly rather than
                // via `cargo run`.
                .unwrap_or_else(|_| std::env::current_dir().unwrap());
            base.join("target").join("anneal-home")
        } else {
            dirs::home_dir().ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?
        };
        let platform = Platform::detect()?;
        let aeneas_hash = platform.expected_archive_hash();

        // We produce a unique hash of the toolchain component versions to
        // ensure that each combination of versions is installed into its own
        // isolated directory. This allows multiple versions of Anneal to
        // coexist on the same machine without colliding, and ensures that
        // switching branches or updating Anneal will automatically point to
        // the correct toolchain version.
        //
        // We hash the expected archive checksum rather than version tags.
        // Checksums provide a stable, data-anchored identity for the toolchain
        // components that cannot drift from the underlying binaries.
        let mut hasher = Sha256::new();
        hasher.update(aeneas_hash);
        // Hash the Rust toolchain tag to ensure that updating the Rust version
        // results in a new, isolated toolchain directory.
        hasher.update(env!("ANNEAL_RUST_TAG"));
        let hash = format!("{:x}", hasher.finalize());
        let short_hash = &hash[..12];

        // We include the host platform's target triple in the directory name.
        // This ensures that toolchains for different architectures remain isolated
        // if they are stored in a shared filesystem (e.g., a networked home directory).
        let root = home.join(".anneal").join("toolchain").join(format!(
            "{}-{}",
            platform.triple(),
            short_hash
        ));

        // Acquire a shared lock to ensure the toolchain isn't modified while
        // we use it. If the directory doesn't exist yet, we still acquire the
        // lock on the path (which setup will also use).
        let lock = DirLock::lock_shared(root.clone())
            .with_context(|| format!("Failed to acquire shared lock on {:?}", root))?;

        Ok(Self { root, _lock: Some(lock) })
    }

    /// Returns the bin directory for this toolchain.
    pub fn bin_dir(&self) -> std::path::PathBuf {
        self.root.clone()
    }

    /// Returns the cache directory for this toolchain.
    pub fn cache_dir(&self) -> std::path::PathBuf {
        self.root.join("lake-cache")
    }

    /// Acquires an exclusive lock on the toolchain directory.
    pub fn lock_exclusive(&self) -> Result<DirLock> {
        DirLock::lock_exclusive(self.root.clone())
    }

    /// Returns a Command for the specified tool, prioritizing the managed
    /// toolchain.
    pub fn command(&self, tool: Tool) -> Command {
        let bin_name = tool.name();
        let managed_path = self.bin_dir().join(bin_name);

        // If ANNEAL_USE_PATH_FOR_TOOLS is set, we ignore the managed toolchain
        // and look for the tool in the system PATH. This is useful in tests
        // to allow mocking tools via PATH shims, which would otherwise be
        // bypassed by the managed toolchain's absolute paths.
        if std::env::var("ANNEAL_USE_PATH_FOR_TOOLS").is_ok() {
            Command::new(bin_name)
        } else if tool == Tool::Lake {
            // Lake is not part of the managed toolchain; it is assumed to be
            // installed on the system (e.g., via elan).
            Command::new(bin_name)
        } else {
            Command::new(managed_path)
        }
    }

    /// Takes the shared lock from the toolchain, if it exists.
    ///
    /// This is used when we need to upgrade from a shared lock (held during
    /// normal operation) to an exclusive lock (needed during `setup` or
    /// repair). Because file locks cannot be atomically upgraded, we must
    /// drop the shared lock before acquiring the exclusive one.
    pub fn take_lock(&mut self) -> Option<DirLock> {
        self._lock.take()
    }
}

/// Calculates the SHA-256 hash of a file on disk.
fn calculate_file_hash(path: &Path) -> Result<[u8; 32]> {
    let mut file = fs::File::open(path).context("Failed to open file for hashing")?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 8192];
    loop {
        let n = file.read(&mut buffer).context("Failed to read file for hashing")?;
        if n == 0 {
            break;
        }
        hasher.update(&buffer[..n]);
    }
    Ok(hasher.finalize().into())
}

/// Ensures that the file at the specified path is writable.
/// Some archives (like Nix-built ones) may contain read-only files,
/// which prevents us from repairing or corrupting them in tests.
fn make_writable(path: &Path) -> Result<()> {
    if path.exists() {
        let mut perms = fs::metadata(path)?.permissions();
        if perms.readonly() {
            #[allow(clippy::permissions_set_readonly_false)]
            perms.set_readonly(false);
            fs::set_permissions(path, perms).context("Failed to set toolchain permissions")?;
        }
    }
    Ok(())
}

/// Decodes a hexadecimal string into its byte representation.
const fn decode_hex(s: &str) -> Option<[u8; 32]> {
    let bytes = s.as_bytes();
    if bytes.len() != 64 {
        return None;
    }
    let mut res = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        let (h, l) = (bytes[i * 2], bytes[i * 2 + 1]);
        let h_nib = match decode_nibble(h) {
            Some(n) => n,
            None => return None,
        };
        let l_nib = match decode_nibble(l) {
            Some(n) => n,
            None => return None,
        };
        res[i] = (h_nib << 4) | l_nib;
        i += 1;
    }
    Some(res)
}

const fn decode_nibble(c: u8) -> Option<u8> {
    match c {
        b'0'..=b'9' => Some(c - b'0'),
        b'a'..=b'f' => Some(c - b'a' + 10),
        b'A'..=b'F' => Some(c - b'A' + 10),
        _ => None,
    }
}

const AENEAS_TOOLS: &[Tool] = &[Tool::Aeneas, Tool::Charon, Tool::CharonDriver];
const RUST_TOOLS: &[Tool] =
    &[Tool::Rustc, Tool::RustStd, Tool::RustcDev, Tool::LlvmTools, Tool::Miri, Tool::RustSrc];

/// A generic function to extract a tar.gz archive, using a closure to map
/// paths from the archive to paths on disk.
fn extract_tar_gz<F>(data: &[u8], target_dir: &Path, mut map_path: F) -> Result<()>
where
    F: FnMut(&Path) -> Option<std::path::PathBuf>,
{
    let tar = GzDecoder::new(data);
    let mut archive = Archive::new(tar);

    fs::create_dir_all(target_dir).context("Failed to create target directory")?;

    for entry in archive.entries().context("Failed to read archive entries")? {
        let mut entry = entry.context("Failed to get archive entry")?;
        let path = entry.path().context("Failed to get entry path")?;

        if let Some(target) = map_path(&path) {
            if let Some(parent) = target.parent() {
                fs::create_dir_all(parent).context("Failed to create parent directory")?;
            }
            entry.unpack(&target).context("Failed to unpack archive entry")?;
            make_writable(&target)?;
        }
    }

    Ok(())
}

/// Extracts a tar.gz archive to the target directory.
fn extract_artifact(data: &[u8], target_dir: &Path) -> Result<()> {
    log::info!("Extracting to {:?}...", target_dir);
    extract_tar_gz(data, target_dir, |path| Some(target_dir.join(path)))
}

/// Performs a strict string replacement in a file.
///
/// This function reads the file at the specified path, ensures that the target
/// string appears exactly once in the file, and replaces it with the
/// replacement string.
///
/// We are strict about expecting exactly one occurrence to prevent accidental
/// mis-replacements or corrupted states when modifying files that we do not
/// fully parse (like Lean source files acting as configuration).
///
/// # Errors
///
/// Bails with an error if the target string is not found, or if it is found
/// more than once.
fn strict_replace_file_content(path: &Path, target: &str, replacement: &str) -> Result<()> {
    let content = fs::read_to_string(path).context("Failed to read file for rewriting")?;
    let count = content.matches(target).count();
    if count == 0 {
        bail!("Target string not found in {:?}", path);
    }
    if count > 1 {
        bail!("Multiple instances of target string found in {:?}", path);
    }
    let new_content = content.replace(target, replacement);
    fs::write(path, new_content).context("Failed to write rewritten file")?;
    Ok(())
}

/// Reads a Lake manifest file and extracts resolved package commits.
///
/// This function parses the JSON manifest generated by Lake and returns a map
/// from package names to their resolved Git commit hashes. This allows us to
/// know the exact versions of dependencies resolved by Lake, even if we
/// subsequently override the repository URLs to be local.
fn read_manifest_revs(manifest_path: &Path) -> Result<std::collections::HashMap<String, String>> {
    let content = fs::read_to_string(manifest_path).context("Failed to read manifest")?;
    let json: serde_json::Value =
        serde_json::from_str(&content).context("Failed to parse manifest JSON")?;
    let mut map = std::collections::HashMap::new();

    if let Some(packages) = json.get("packages").and_then(|p| p.as_array()) {
        for pkg in packages {
            if let (Some(name), Some(rev)) =
                (pkg.get("name").and_then(|n| n.as_str()), pkg.get("rev").and_then(|r| r.as_str()))
            {
                map.insert(name.to_string(), rev.to_string());
            }
        }
    }
    Ok(map)
}

/// Updates package URLs and requested revisions in a Lake manifest file.
///
/// This function reads the generated manifest, iterates through all resolved
/// packages, and updates their URLs to point to the local `packages/`
/// directory using `file://` URLs based on the provided `base_path`.
///
/// We update the manifest in addition to the `lakefile`s to prevent Lake from
/// detecting that the manifest is out of date and falling back to cloning the
/// dependencies from GitHub again.
///
/// It also updates the `inputRev` field to match the resolved `rev` (commit
/// hash) to suppress warnings from Lake about the requested revision changing.
fn update_manifest_urls(manifest_path: &Path, base_path: &Path) -> Result<()> {
    let content = fs::read_to_string(manifest_path).context("Failed to read manifest")?;
    let mut json: serde_json::Value =
        serde_json::from_str(&content).context("Failed to parse manifest JSON")?;

    if let Some(packages) = json.get_mut("packages").and_then(|p| p.as_array_mut()) {
        for pkg in packages {
            if let Some(name) = pkg.get("name").and_then(|n| n.as_str()) {
                let local_url = format!("file://{}/packages/{}", base_path.display(), name);
                pkg["url"] = serde_json::Value::String(local_url);

                // Also update inputRev to match the resolved rev to avoid warnings
                if let Some(rev) = pkg.get("rev").cloned() {
                    pkg["inputRev"] = rev;
                }
            }
        }
    }

    let new_content =
        serde_json::to_string_pretty(&json).context("Failed to serialize manifest")?;
    fs::write(manifest_path, new_content).context("Failed to write manifest")?;
    Ok(())
}

fn extract_rust_component(data: &[u8], target_dir: &Path, component_name: &str) -> Result<()> {
    log::info!("Extracting component {} to {:?}...", component_name, target_dir);
    extract_tar_gz(data, target_dir, |path| {
        let mut components = path.components();
        components.next(); // skip top level (e.g. rustc-nightly-x86_64-unknown-linux-gnu)
        components.next(); // skip component name (e.g. rustc)

        let rest = components.as_path();
        if rest.as_os_str().is_empty() { None } else { Some(target_dir.join(rest)) }
    })
}

fn setup_rust_toolchain(toolchain: &Toolchain, platform: Platform, tmp_root: &Path) -> Result<()> {
    let sysroot = tmp_root.join("rust");
    println!("Setting up Rust toolchain at {:?}...", sysroot);

    let base_url = std::env::var("ANNEAL_SETUP_RUST_BASE_URL").unwrap_or_else(|_| {
        format!("https://static.rust-lang.org/dist/{}", env!("ANNEAL_RUST_DATE"))
    });

    let components = [
        ("rustc", Tool::Rustc),
        ("rust-std", Tool::RustStd),
        ("rustc-dev", Tool::RustcDev),
        ("llvm-tools", Tool::LlvmTools),
        ("miri", Tool::Miri),
    ];

    for (name, tool) in components {
        let url = format!("{}/{}-nightly-{}.tar.gz", base_url, name, platform.triple());
        let expected_hash = platform.expected_bin_hash(tool);

        println!("Downloading and extracting {}...", name);
        let data = download_artifact(&url, &expected_hash)?;
        extract_rust_component(&data, &sysroot, name)?;
    }

    // Handle rust-src separately as it is target-independent
    let url = format!("{}/rust-src-nightly.tar.gz", base_url);
    let expected_hash = platform.expected_bin_hash(Tool::RustSrc);
    println!("Downloading and extracting rust-src...");
    let data = download_artifact(&url, &expected_hash)?;
    extract_rust_component(&data, &sysroot, "rust-src")?;

    Ok(())
}

/// Ensures that `elan` (the Lean toolchain manager) is installed on the
/// system. If it is not found in the system `PATH`, it downloads the latest
/// release from GitHub and runs `elan-init` to install it for the current
/// user. It also attempts to add the `elan` bin directory to the current
/// process's `PATH` to ensure subsequent commands can find it immediately.
fn ensure_elan_installed() -> Result<()> {
    println!("Checking for elan...");
    let status = Command::new("elan")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    if status.is_ok() && status.unwrap().success() {
        println!("elan is already installed.");
        return Ok(());
    }

    println!("elan not found. Installing elan...");
    let platform = Platform::detect()?;
    let arch = platform.triple();

    let url =
        format!("https://github.com/leanprover/elan/releases/latest/download/elan-{}.tar.gz", arch);

    println!("Downloading elan from {}...", url);
    let response = reqwest::blocking::get(&url).context("Failed to download elan")?;
    if !response.status().is_success() {
        bail!("Failed to download elan: HTTP {}", response.status());
    }
    let data = response.bytes().context("Failed to read elan response")?;

    let temp_dir = std::env::temp_dir();
    let elan_extract_dir = temp_dir.join("elan-extract-anneal");
    fs::create_dir_all(&elan_extract_dir).context("Failed to create elan extract dir")?;

    extract_artifact(&data, &elan_extract_dir)?;

    let elan_init_path = elan_extract_dir.join("elan-init");

    let status = Command::new(&elan_init_path)
        .args(["-y", "--default-toolchain", "none"])
        .status()
        .context("Failed to run elan-init")?;

    let _ = fs::remove_dir_all(&elan_extract_dir);

    if !status.success() {
        bail!("elan-init failed");
    }

    // Add elan to PATH for current process
    let home = dirs::home_dir().ok_or_else(|| anyhow::anyhow!("Could not find home directory"))?;
    let elan_bin = home.join(".elan").join("bin");
    if elan_bin.exists() {
        let path = std::env::var_os("PATH").unwrap_or_default();
        let mut paths = std::env::split_paths(&path).collect::<Vec<_>>();
        if !paths.contains(&elan_bin) {
            paths.insert(0, elan_bin);
            let new_path = std::env::join_paths(paths)?;
            // SAFETY: This is a single-threaded setup context.
            unsafe {
                std::env::set_var("PATH", new_path);
            }
        }
    }

    println!("elan installed successfully.");
    Ok(())
}

/// Installs the pinned Lean toolchain required by Anneal using `elan`.
/// It checks the environment variable `ANNEAL_LEAN_TOOLCHAIN` to determine
/// which version to install. If the version is already listed in `elan
/// toolchain list`, it skips installation to save time.
fn install_lean_toolchain() -> Result<()> {
    let version = env!("ANNEAL_LEAN_TOOLCHAIN");
    println!("Installing Lean toolchain {}...", version);

    // Check if already installed
    let output = Command::new("elan")
        .args(["toolchain", "list"])
        .output()
        .context("Failed to run elan toolchain list")?;

    if output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        if stdout.lines().any(|line| line.contains(version)) {
            println!("Lean toolchain {} is already installed.", version);
            return Ok(());
        }
    }

    let status = Command::new("elan")
        .args(["toolchain", "install", version])
        .status()
        .context("Failed to run elan toolchain install")?;

    if !status.success() {
        bail!("Failed to install Lean toolchain");
    }

    println!("Lean toolchain {} installed successfully.", version);
    Ok(())
}

/// Pre-builds the Aeneas Lean library in the extracted toolchain directory.
/// This prevents compiling the library from source when users verify their
/// projects, which is slow and disk-heavy. It first attempts to fetch
/// pre-compiled Mathlib artifacts using `lake exe cache get` to avoid
/// compiling Mathlib from source, and then runs `lake build`.
fn prebuild_lean_library(lean_dir: &Path, cache_dir: &Path) -> Result<()> {
    println!("Pre-building Aeneas Lean library at {:?}...", lean_dir);

    // Fetch Mathlib cache
    println!("Fetching Mathlib cache...");
    let status = Command::new("lake")
        .args(["exe", "cache", "get"])
        .env("LAKE_CACHE_DIR", cache_dir)
        .env("LAKE_ARTIFACT_CACHE", "1")
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake exe cache get`")?;

    if !status.success() {
        bail!("Failed to fetch Mathlib cache; refusing to build from scratch");
    }

    // Build the library
    println!("Building Aeneas Lean library...");
    let status = Command::new("lake")
        .arg("build")
        .env("LAKE_CACHE_DIR", cache_dir)
        .env("LAKE_ARTIFACT_CACHE", "1")
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake build`")?;

    if !status.success() {
        bail!("Failed to build Aeneas Lean library");
    }

    println!("Successfully pre-built Aeneas Lean library.");
    Ok(())
}

/// Checks whether the specified tools are installed and have valid hashes.
/// Returns `true` if all are valid, or `false` if any are missing or corrupt.

/// Sets up the Anneal toolchain by downloading and extracting dependencies.
pub fn run_setup() -> Result<()> {
    ensure_elan_installed()?;
    install_lean_toolchain()?;

    let mut toolchain = Toolchain::resolve()?;
    // Drop the shared lock acquired by resolve() so we can acquire an
    // exclusive one.
    drop(toolchain.take_lock());

    // Acquire global lock to prevent concurrent installations or repairs.
    // This ensures that two instances of Anneal don't try to download or
    // modify the toolchain at the same time.
    let _lock = toolchain.lock_exclusive()?;
    let platform = Platform::detect()?;

    let parent_dir = toolchain.root.parent().unwrap();
    fs::create_dir_all(parent_dir).context("Failed to create toolchain parent directory")?;
    // To ensure atomic installation, we perform all extraction and setup steps
    // in a temporary directory within the same parent folder. This prevents
    // leaving the toolchain in a partially-installed state if the process is
    // interrupted.
    let temp_dir = tempfile::Builder::new()
        .prefix("anneal-toolchain-tmp-")
        .tempdir_in(parent_dir)
        .context("Failed to create temporary directory for setup")?;
    let tmp_root = temp_dir.path();

    setup_rust_toolchain(&toolchain, platform, tmp_root)?;

    let tag = env!("ANNEAL_AENEAS_TAG");

    // Perform installation. Note that, because we validate SHA-256
    // checksums against values baked into the binary, allowing the user to
    // override the download URL does not represent a security risk.
    let base_url = std::env::var("ANNEAL_SETUP_AENEAS_BASE_URL")
        .unwrap_or_else(|_| "https://github.com/AeneasVerif/aeneas/releases/download".to_string());

    let url = format!(
        "{}/{}/aeneas-{}.tar.gz",
        base_url,
        tag,
        match platform {
            Platform::LinuxX86_64 => "linux-x86_64",
            Platform::LinuxAArch64 => "linux-aarch64",
            Platform::MacosAArch64 => "macos-aarch64",
            Platform::MacosX86_64 => "macos-x86_64",
        }
    );

    let expected_archive_hash = platform.expected_archive_hash();

    let data = download_artifact(&url, &expected_archive_hash)?;

    extract_artifact(&data, &tmp_root)?;

    let lean_dir = tmp_root.join("backends").join("lean");

    // Initialize git repo in the extracted Lean directory
    println!("Initializing git repository in {:?}...", lean_dir);
    let status = Command::new("git")
        .args(["init", "-b", "main", "-q"])
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `git init -b main`")?;
    if !status.success() {
        bail!("`git init -b main` failed");
    }

    let status = Command::new("git")
        .args(["add", "."])
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `git add`")?;
    if !status.success() {
        bail!("`git add` failed");
    }

    let status = Command::new("git")
        .args(["commit", "-m", "Initial commit from Anneal setup", "-q"])
        .env("GIT_AUTHOR_NAME", "Anneal")
        .env("GIT_AUTHOR_EMAIL", "anneal@example.com")
        .env("GIT_COMMITTER_NAME", "Anneal")
        .env("GIT_COMMITTER_EMAIL", "anneal@example.com")
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `git commit`")?;
    if !status.success() {
        bail!("`git commit` failed");
    }

    // Run `lake update` to resolve dependencies and generate the manifest.
    // We do this initially with remote URLs to let Lake resolve conflicts and
    // record the specific commit hashes in `lake-manifest.json`. This also
    // fetches the sources into `.lake/packages`.
    println!("Resolving dependencies with `lake update` in {:?}...", lean_dir);
    let status = Command::new("lake")
        .arg("update")
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `lake update`")?;
    if !status.success() {
        bail!("`lake update` failed");
    }

    // Move the resolved dependency directories to a centralized `packages`
    // folder in the toolchain root. This acts as our local registry and
    // ensures that they are preserved across builds and not treated as
    // transient build artifacts by Lake in `backends/lean`.
    let packages_dir = tmp_root.join("packages");
    fs::create_dir_all(&packages_dir).context("Failed to create packages directory")?;

    let lake_packages_dir = lean_dir.join(".lake").join("packages");
    if lake_packages_dir.exists() {
        for entry in fs::read_dir(&lake_packages_dir).context("Failed to read .lake/packages")? {
            let entry = entry.context("Failed to read directory entry")?;
            let path = entry.path();
            if path.is_dir() {
                let name = path.file_name().unwrap();
                let dest = packages_dir.join(name);
                fs::rename(&path, &dest).context("Failed to move package")?;
            }
        }
    }

    // We now perform the core rewriting of dependency configurations to point
    // to the filesystem-local paths we just created.
    //
    // We first read the manifest to know the exact resolved commit hashes,
    // ensuring we preserve the versions resolved by Lake in step 2.
    let manifest_path = lean_dir.join("lake-manifest.json");
    let revs = read_manifest_revs(&manifest_path)?;

    // Helper to get rev or fallback
    let get_rev = |name: &str| -> &str { revs.get(name).map(|s| s.as_str()).unwrap_or("main") };

    // We hardcode the target strings for replacement because parsing arbitrary
    // Lean configuration files in Rust is fragile. Since this toolchain pins
    // specific versions of dependencies, these target strings are stable for
    // this version of Anneal.
    //
    // Rewrite URLs in Aeneas lakefile.lean
    let aeneas_lakefile = lean_dir.join("lakefile.lean");
    let mathlib_rev = get_rev("mathlib");
    let target = "require mathlib from git\n  \"https://github.com/leanprover-community/mathlib4.git\" @ \"v4.28.0-rc1\"";
    let replacement = format!(
        "require mathlib from git\n  \"file://{}/packages/mathlib\" @ \"{}\"",
        tmp_root.display(),
        mathlib_rev
    );
    strict_replace_file_content(&aeneas_lakefile, target, &replacement)?;

    // Rewrite URLs in Mathlib lakefile.lean
    let mathlib_lakefile = packages_dir.join("mathlib").join("lakefile.lean");
    let batteries_rev = get_rev("batteries");
    let qq_rev = get_rev("Qq");
    let aesop_rev = get_rev("aesop");
    let proofwidgets_rev = get_rev("proofwidgets");
    let import_graph_rev = get_rev("importGraph");
    let lean_search_client_rev = get_rev("LeanSearchClient");
    let plausible_rev = get_rev("plausible");

    let mathlib_replacements = [
        (
            "require \"leanprover-community\" / \"batteries\" @ git \"main\"",
            format!(
                "require batteries from git \"file://{}/packages/batteries\" @ \"{}\"",
                tmp_root.display(),
                batteries_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"Qq\" @ git \"master\"",
            format!(
                "require Qq from git \"file://{}/packages/Qq\" @ \"{}\"",
                tmp_root.display(),
                qq_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"aesop\" @ git \"master\"",
            format!(
                "require aesop from git \"file://{}/packages/aesop\" @ \"{}\"",
                tmp_root.display(),
                aesop_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"proofwidgets\" @ git \"v0.0.86\"",
            format!(
                "require proofwidgets from git \"file://{}/packages/proofwidgets\" @ \"{}\"",
                tmp_root.display(),
                proofwidgets_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"importGraph\" @ git \"main\"",
            format!(
                "require importGraph from git \"file://{}/packages/importGraph\" @ \"{}\"",
                tmp_root.display(),
                import_graph_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"LeanSearchClient\" @ git \"main\"",
            format!(
                "require LeanSearchClient from git \"file://{}/packages/LeanSearchClient\" @ \"{}\"",
                tmp_root.display(),
                lean_search_client_rev
            ),
        ),
        (
            "require \"leanprover-community\" / \"plausible\" @ git \"main\"",
            format!(
                "require plausible from git \"file://{}/packages/plausible\" @ \"{}\"",
                tmp_root.display(),
                plausible_rev
            ),
        ),
    ];

    for (target, replacement) in &mathlib_replacements {
        strict_replace_file_content(&mathlib_lakefile, target, &replacement)?;
    }

    // Rewrite URLs in Aesop lakefile.toml
    let aesop_lakefile = packages_dir.join("aesop").join("lakefile.toml");
    let target = "[[require]]\nname = \"batteries\"\ngit = \"https://github.com/leanprover-community/batteries\"\nrev = \"v4.28.0-rc1\"";
    let replacement = format!(
        "[[require]]\nname = \"batteries\"\ngit = \"file://{}/packages/batteries\"\nrev = \"v4.28.0-rc1\"",
        tmp_root.display()
    );
    strict_replace_file_content(&aesop_lakefile, target, &replacement)?;

    // Rewrite URLs in ImportGraph lakefile.toml
    let import_graph_lakefile = packages_dir.join("importGraph").join("lakefile.toml");
    let target = "[[require]]\nname = \"Cli\"\nscope = \"leanprover\"\nrev = \"v4.28.0-rc1\"";
    let replacement = format!(
        "[[require]]\nname = \"Cli\"\ngit = \"file://{}/packages/Cli\"\nrev = \"v4.28.0-rc1\"",
        tmp_root.display()
    );
    strict_replace_file_content(&import_graph_lakefile, target, &replacement)?;

    // We must also update the manifest file itself. If we only update the
    // `lakefile`s, Lake will see that the manifest is out of date and attempt
    // to re-resolve or re-clone from GitHub.
    //
    // Rewrite URLs in lake-manifest.json
    update_manifest_urls(&manifest_path, tmp_root)?;

    prebuild_lean_library(&lean_dir, &toolchain.cache_dir())?;

    // Phase 2: Rewrite URLs to point to final toolchain root
    println!("Rewriting URLs to final toolchain root...");

    let target_aeneas = format!(
        "require mathlib from git\n  \"file://{}/packages/mathlib\" @ \"{}\"",
        tmp_root.display(),
        mathlib_rev
    );
    let replacement_aeneas = format!(
        "require mathlib from git\n  \"file://{}/packages/mathlib\" @ \"{}\"",
        toolchain.root.display(),
        mathlib_rev
    );
    strict_replace_file_content(&aeneas_lakefile, &target_aeneas, &replacement_aeneas)?;

    for (orig_target, phase1_rep) in &mathlib_replacements {
        let phase2_rep = phase1_rep
            .replace(&tmp_root.display().to_string(), &toolchain.root.display().to_string());
        strict_replace_file_content(&mathlib_lakefile, &phase1_rep, &phase2_rep)?;
    }

    let target_aesop = format!(
        "[[require]]\nname = \"batteries\"\ngit = \"file://{}/packages/batteries\"\nrev = \"v4.28.0-rc1\"",
        tmp_root.display()
    );
    let replacement_aesop = format!(
        "[[require]]\nname = \"batteries\"\ngit = \"file://{}/packages/batteries\"\nrev = \"v4.28.0-rc1\"",
        toolchain.root.display()
    );
    strict_replace_file_content(&aesop_lakefile, &target_aesop, &replacement_aesop)?;

    let target_import_graph = format!(
        "[[require]]\nname = \"Cli\"\ngit = \"file://{}/packages/Cli\"\nrev = \"v4.28.0-rc1\"",
        tmp_root.display()
    );
    let replacement_import_graph = format!(
        "[[require]]\nname = \"Cli\"\ngit = \"file://{}/packages/Cli\"\nrev = \"v4.28.0-rc1\"",
        toolchain.root.display()
    );
    strict_replace_file_content(
        &import_graph_lakefile,
        &target_import_graph,
        &replacement_import_graph,
    )?;

    // Also update manifest for Phase 2
    update_manifest_urls(&manifest_path, &toolchain.root)?;

    // Commit changes in local repositories so that Git clone operations
    // performed by Lake in user projects will see the rewritten URLs.
    println!("Committing changes in local repositories...");

    // Commit in Aeneas
    let status = Command::new("git")
        .args(["add", "."])
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `git add` in Aeneas")?;
    if !status.success() {
        bail!("`git add` failed in Aeneas");
    }

    let status = Command::new("git")
        .args(["commit", "-m", "Anneal: rewrite dependencies to local paths", "-q"])
        .env("GIT_AUTHOR_NAME", "Anneal")
        .env("GIT_AUTHOR_EMAIL", "anneal@example.com")
        .env("GIT_COMMITTER_NAME", "Anneal")
        .env("GIT_COMMITTER_EMAIL", "anneal@example.com")
        .current_dir(&lean_dir)
        .status()
        .context("Failed to run `git commit` in Aeneas")?;
    if !status.success() {
        bail!("`git commit` failed in Aeneas");
    }

    // Commit in dependencies
    if packages_dir.exists() {
        for entry in fs::read_dir(&packages_dir).context("Failed to read packages directory")? {
            let entry = entry.context("Failed to read directory entry")?;
            let path = entry.path();
            if path.is_dir() {
                if path.join(".git").exists() {
                    let output = Command::new("git")
                        .args(["status", "--porcelain"])
                        .current_dir(&path)
                        .output()
                        .context("Failed to run `git status` in dependency")?;

                    if !output.stdout.is_empty() {
                        println!(
                            "Committing changes in dependency: {:?}",
                            path.file_name().unwrap()
                        );
                        let status = Command::new("git")
                            .args(["add", "."])
                            .current_dir(&path)
                            .status()
                            .context("Failed to run `git add` in dependency")?;
                        if !status.success() {
                            bail!("`git add` failed in dependency {:?}", path);
                        }

                        let status = Command::new("git")
                            .args([
                                "commit",
                                "-m",
                                "Anneal: rewrite dependencies to local paths",
                                "-q",
                            ])
                            .env("GIT_AUTHOR_NAME", "Anneal")
                            .env("GIT_AUTHOR_EMAIL", "anneal@example.com")
                            .env("GIT_COMMITTER_NAME", "Anneal")
                            .env("GIT_COMMITTER_EMAIL", "anneal@example.com")
                            .current_dir(&path)
                            .status()
                            .context("Failed to run `git commit` in dependency")?;
                        if !status.success() {
                            bail!("`git commit` failed in dependency {:?}", path);
                        }
                    }
                }
            }
        }
    }

    // Post-process trace files to fix absolute paths
    println!("Post-processing trace files to fix absolute paths...");
    let tmp_path_str = temp_dir.path().to_str().unwrap();
    let final_path_str = toolchain.root.to_str().unwrap();

    // Helper closure to process a build directory
    let mut process_build_dir = |dir: &Path| -> Result<()> {
        if dir.exists() {
            let walker = WalkDir::new(dir).into_iter();
            for entry in walker {
                let entry = entry.context("Failed to walk build directory")?;
                let path = entry.path();
                if path.is_file() && path.extension().map_or(false, |ext| ext == "trace") {
                    let content = fs::read_to_string(path).context("Failed to read trace file")?;
                    if content.contains(tmp_path_str) {
                        let new_content = content.replace(tmp_path_str, final_path_str);
                        fs::write(path, new_content).context("Failed to write trace file")?;
                    }
                }
            }
        }
        Ok(())
    };

    // Process Aeneas build dir
    process_build_dir(&lean_dir.join(".lake").join("build"))?;

    // Process dependencies build dirs
    if packages_dir.exists() {
        for entry in fs::read_dir(&packages_dir).context("Failed to read packages directory")? {
            let entry = entry.context("Failed to read directory entry")?;
            let path = entry.path();
            if path.is_dir() {
                process_build_dir(&path.join(".lake").join("build"))?;
            }
        }
    }

    println!("Successfully installed toolchain v{tag}");

    // Once installation is successful, we atomically swap the temporary
    // directory into the final target location. If the target directory
    // already exists (e.g., a re-installation attempt), we delete it first to
    // allow the rename to succeed on Unix systems.
    let tmp_path = temp_dir.into_path();
    if toolchain.root.exists() {
        fs::remove_dir_all(&toolchain.root).context("Failed to remove old toolchain directory")?;
    }
    fs::rename(&tmp_path, &toolchain.root)
        .context("Failed to rename temporary toolchain directory to target")?;

    Ok(())
}

/// Downloads an artifact from the specified URL and verifies its SHA-256 hash.
fn download_artifact(url: &str, expected_hash: &[u8; 32]) -> Result<Vec<u8>> {
    println!("Downloading: {}", url);
    let mut response = reqwest::blocking::get(url).context("Failed to download artifact")?;
    if !response.status().is_success() {
        bail!("Failed to download artifact: HTTP {}", response.status());
    }

    let mut data = Vec::new();
    response.read_to_end(&mut data).context("Failed to read artifact data")?;

    let mut hasher = Sha256::new();
    hasher.update(&data);
    let actual_hash: [u8; 32] = hasher.finalize().into();

    if actual_hash != *expected_hash {
        bail!(
            "Checksum mismatch for artifact! Expected {}, got {}",
            format_hex(expected_hash),
            format_hex(&actual_hash)
        );
    }

    Ok(data)
}

fn format_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        use std::fmt::Write;
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_platform_detection() {
        let platform = Platform::detect().expect("Should detect current platform");
        // Verify that the detected platform triple matches the Rust target triple
        // used to compile this test (roughly).
        let triple = platform.triple();
        if cfg!(target_os = "linux") {
            assert!(triple.contains("linux"));
        } else if cfg!(target_os = "macos") {
            assert!(triple.contains("apple-darwin"));
        }
    }

    #[test]
    fn test_toolchain_resolve() {
        let temp_dir = tempfile::tempdir().unwrap();
        // We must use an unsafe block because `set_var` is unsafe in recent Rust
        // versions due to potential data races. We use it here to point the
        // toolchain directory to our temporary directory, preventing the test
        // from mutating the user's real home directory.
        unsafe {
            std::env::set_var("ANNEAL_TOOLCHAIN_DIR", temp_dir.path());
        }

        let toolchain = Toolchain::resolve().expect("Should resolve toolchain");

        // Verify that the resolved toolchain root is located within the
        // isolated temporary directory we specified.
        assert!(toolchain.root.starts_with(temp_dir.path()));

        // Verify that the resolved path includes the platform target triple,
        // ensuring platform-specific isolation.
        let path_str = toolchain.root.to_str().unwrap();
        let platform = Platform::detect().unwrap();
        assert!(path_str.contains(platform.triple()));
    }

    #[test]
    fn test_locking() {
        let temp = tempfile::tempdir().unwrap();
        let lock_path = temp.path().join(".lock");

        // First lock
        let lock1 =
            DirLock::lock_exclusive(temp.path().to_path_buf()).expect("First lock should succeed");

        // Try second lock in another thread (should block/fail if we used try_lock, but DirLock::lock blocks)
        // To test non-blocking, we'd need another helper, but we can verify that the second lock
        // succeeds after the first one is dropped.
        let lock_path_clone = lock_path.clone();
        let handle = std::thread::spawn(move || {
            let _lock2 = DirLock::lock_exclusive(lock_path_clone.parent().unwrap().to_path_buf())
                .expect("Second lock should succeed after first is dropped");
        });

        std::thread::sleep(std::time::Duration::from_millis(100));
        drop(lock1);
        handle.join().expect("Thread should finish");
    }

    #[test]
    fn test_extraction() {
        let temp = tempfile::tempdir().unwrap();
        let target = temp.path().join("extracted");

        // Create a dummy tar.gz in memory
        let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        {
            let mut tar = tar::Builder::new(&mut enc);
            let mut header = tar::Header::new_gnu();
            header.set_path("hello.txt").unwrap();
            header.set_size(5);
            #[cfg(unix)]
            {
                header.set_mode(0o755);
            }
            header.set_cksum();
            tar.append(&header, b"world" as &[u8]).unwrap();
            tar.finish().unwrap();
        }
        let data = enc.finish().unwrap();

        // Test normal extraction
        extract_artifact(&data, &target).expect("Extraction should succeed");

        let hello_path = target.join("hello.txt");
        assert!(hello_path.exists());
        assert_eq!(fs::read_to_string(&hello_path).unwrap(), "world");

        // Test aeneas extraction (should extract everything)
        let aeneas_target = temp.path().join("aeneas_extracted");
        let mut enc = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        {
            let mut tar = tar::Builder::new(&mut enc);

            // Add aeneas binary
            let mut header = tar::Header::new_gnu();
            header.set_path("aeneas").unwrap();
            header.set_size(6);
            header.set_cksum();
            tar.append(&header, b"binary" as &[u8]).unwrap();

            // Add backends directory
            let mut header = tar::Header::new_gnu();
            header.set_path("backends/lean/test.lean").unwrap();
            header.set_size(4);
            header.set_cksum();
            tar.append(&header, b"lean" as &[u8]).unwrap();

            tar.finish().unwrap();
        }
        let aeneas_data = enc.finish().unwrap();
        extract_artifact(&aeneas_data, &aeneas_target).expect("Aeneas extraction should succeed");

        assert!(aeneas_target.join("aeneas").exists());
        assert!(aeneas_target.join("backends/lean/test.lean").exists());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let metadata = fs::metadata(&hello_path).unwrap();
            assert!(metadata.permissions().mode() & 0o111 != 0, "Executable bit should be set");
        }
    }

    #[test]
    fn test_download() {
        use std::{
            io::{Read, Write},
            net::TcpListener,
        };

        // Start a minimal mock HTTP server
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let port = listener.local_addr().unwrap().port();
        let url = format!("http://127.0.0.1:{}", port);

        let handle = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut buffer = [0; 1024];
            let _ = stream.read(&mut buffer).unwrap();

            let response = "HTTP/1.1 200 OK\r\nContent-Length: 13\r\n\r\nMock Artifact";
            stream.write_all(response.as_bytes()).unwrap();
        });

        let expected_hash_hex = "5fed9305f5a694b6b33ee9f783596ecf08ed89ea00c2960699ba8285e0d67c71"; // sha256 of "Mock Artifact"
        let expected_hash = decode_hex(expected_hash_hex).expect("Mock hex should be valid");

        let data = download_artifact(&url, &expected_hash).expect("Download should succeed");
        assert_eq!(data, b"Mock Artifact");
        handle.join().unwrap();
    }
}
