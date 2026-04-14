//! Subcommand for installing Anneal dependencies.
//!
//! This module handles the automated download, verification, and installation
//! of `charon`, `charon-driver`, and `aeneas`.

use std::{fs, io::Read, path::Path};

use anyhow::{Context, Result, bail};
use flate2::read::GzDecoder;
use sha2::{Digest, Sha256};
use tar::Archive;

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
            (LinuxX86_64, Tool::Charon) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_X86_64_CHARON")
            }
            (LinuxX86_64, Tool::CharonDriver) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_X86_64_CHARON_DRIVER")
            }
            (LinuxAArch64, Tool::Charon) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_AARCH64_CHARON")
            }
            (LinuxAArch64, Tool::CharonDriver) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_AARCH64_CHARON_DRIVER")
            }
            (MacosAArch64, Tool::Charon) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_AARCH64_CHARON")
            }
            (MacosAArch64, Tool::CharonDriver) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_AARCH64_CHARON_DRIVER")
            }
            (MacosX86_64, Tool::Charon) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_X86_64_CHARON")
            }
            (MacosX86_64, Tool::CharonDriver) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_X86_64_CHARON_DRIVER")
            }
            (LinuxX86_64, Tool::Aeneas) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_X86_64_AENEAS")
            }
            (LinuxAArch64, Tool::Aeneas) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_LINUX_AARCH64_AENEAS")
            }
            (MacosAArch64, Tool::Aeneas) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_AARCH64_AENEAS")
            }
            (MacosX86_64, Tool::Aeneas) => {
                decode_hex_env!("ANNEAL_AENEAS_CHECKSUM_MACOS_X86_64_AENEAS")
            }

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

        // We also hash the individual tool checksums to ensure that updating
        // any component (like the Rust toolchain) results in a new directory.
        let tools = [
            Tool::Charon,
            Tool::CharonDriver,
            Tool::Aeneas,
            Tool::Rustc,
            Tool::RustStd,
            Tool::RustcDev,
            Tool::LlvmTools,
            Tool::Miri,
            Tool::RustSrc,
        ];
        for tool in tools {
            hasher.update(platform.expected_bin_hash(tool));
        }
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

    /// Acquires an exclusive lock on the toolchain directory.
    pub fn lock_exclusive(&self) -> Result<DirLock> {
        DirLock::lock_exclusive(self.root.clone())
    }

    /// Returns a Command for the specified tool, prioritizing the managed
    /// toolchain.
    pub fn command(&self, tool: Tool) -> std::process::Command {
        let bin_name = tool.name();
        let managed_path = self.bin_dir().join(bin_name);

        // If ANNEAL_USE_PATH_FOR_TOOLS is set, we ignore the managed toolchain
        // and look for the tool in the system PATH. This is useful in tests
        // to allow mocking tools via PATH shims, which would otherwise be
        // bypassed by the managed toolchain's absolute paths.
        if std::env::var("ANNEAL_USE_PATH_FOR_TOOLS").is_ok() {
            std::process::Command::new(bin_name)
        } else if managed_path.exists() {
            std::process::Command::new(managed_path)
        } else {
            std::process::Command::new(bin_name)
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

const TOOLS: &[Tool] = &[Tool::Aeneas, Tool::Charon, Tool::CharonDriver];

/// Extracts a tar.gz archive to the target directory.
fn extract_artifact(data: &[u8], target_dir: &Path) -> Result<()> {
    log::info!("Extracting to {:?}...", target_dir);
    let tar = GzDecoder::new(data);
    let mut archive = Archive::new(tar);

    fs::create_dir_all(target_dir).context("Failed to create target directory")?;

    for entry in archive.entries().context("Failed to read archive entries")? {
        let mut entry = entry.context("Failed to get archive entry")?;
        let path = entry.path().context("Failed to get entry path")?.to_path_buf();

        entry.unpack_in(target_dir).context("Failed to unpack archive entry")?;
        let unpacked_path = target_dir.join(&path);

        // Ensure that the extracted file/directory has write permissions.
        // Some archives (like Nix-built ones) may contain read-only files,
        // which prevents us from repairing or corrupting them in tests.
        if unpacked_path.exists() {
            let mut perms = fs::metadata(&unpacked_path)?.permissions();
            if perms.readonly() {
                #[allow(clippy::permissions_set_readonly_false)]
                perms.set_readonly(false);
                fs::set_permissions(&unpacked_path, perms)
                    .context("Failed to set toolchain permissions")?;
            }
        }
    }

    Ok(())
}

fn extract_rust_component(data: &[u8], target_dir: &Path, component_name: &str) -> Result<()> {
    log::info!("Extracting component {} to {:?}...", component_name, target_dir);
    let tar = GzDecoder::new(data);
    let mut archive = Archive::new(tar);

    fs::create_dir_all(target_dir).context("Failed to create target directory")?;

    for entry in archive.entries().context("Failed to read archive entries")? {
        let mut entry = entry.context("Failed to get archive entry")?;
        let path = entry.path().context("Failed to get entry path")?.to_path_buf();

        let mut components = path.components();
        components.next(); // skip top level (e.g. rustc-nightly-x86_64-unknown-linux-gnu)
        components.next(); // skip component name (e.g. rustc)

        let rest = components.as_path();
        if rest.as_os_str().is_empty() {
            continue;
        }

        let target = target_dir.join(rest);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).context("Failed to create parent directory")?;
        }

        entry.unpack(&target).context("Failed to unpack archive entry")?;

        if target.exists() {
            let mut perms = fs::metadata(&target)?.permissions();
            if perms.readonly() {
                #[allow(clippy::permissions_set_readonly_false)]
                perms.set_readonly(false);
                fs::set_permissions(&target, perms)
                    .context("Failed to set toolchain permissions")?;
            }
        }
    }

    Ok(())
}

fn setup_rust_toolchain(toolchain: &Toolchain, platform: Platform) -> Result<()> {
    let sysroot = toolchain.root.join("rust");
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
    let status = std::process::Command::new("elan")
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
    let arch = match platform {
        Platform::LinuxX86_64 => "x86_64-unknown-linux-gnu",
        Platform::LinuxAArch64 => "aarch64-unknown-linux-gnu",
        Platform::MacosAArch64 => "aarch64-apple-darwin",
        Platform::MacosX86_64 => "x86_64-apple-darwin",
    };

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

    let status = std::process::Command::new(&elan_init_path)
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
    let output = std::process::Command::new("elan")
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

    let status = std::process::Command::new("elan")
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
fn prebuild_lean_library(lean_dir: &Path) -> Result<()> {
    println!("Pre-building Aeneas Lean library at {:?}...", lean_dir);

    // Fetch Mathlib cache
    println!("Fetching Mathlib cache...");
    let status = std::process::Command::new("lake")
        .args(["exe", "cache", "get"])
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake exe cache get`")?;

    if !status.success() {
        bail!("Failed to fetch Mathlib cache; refusing to build from scratch");
    }

    // Build the library
    println!("Building Aeneas Lean library...");
    let status = std::process::Command::new("lake")
        .arg("build")
        .current_dir(lean_dir)
        .status()
        .context("Failed to run `lake build`")?;

    if !status.success() {
        bail!("Failed to build Aeneas Lean library");
    }

    println!("Successfully pre-built Aeneas Lean library.");
    Ok(())
}

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

    setup_rust_toolchain(&toolchain, platform)?;

    let tag = env!("ANNEAL_AENEAS_TAG");
    let mut needs_install = false;

    for tool in TOOLS {
        let bin_path = toolchain.bin_dir().join(tool.name());
        if !bin_path.exists() {
            log::info!("{} is missing, re-installing toolchain", tool.name());
            needs_install = true;
            break;
        }

        // Check if an expected SHA-256 checksum is available for this
        // binary. If so, verify that the existing binary matches the
        // expected hash. If the hash does not match, we re-install the
        // entire toolchain component to ensure we have a consistent
        // and verified set of binaries. This protects against
        // accidental corruption of toolchain components and ensures
        // that all binaries match the versions expected by this build
        // of Anneal.
        let expected_bin_hash = platform.expected_bin_hash(*tool);
        let actual_hash = calculate_file_hash(&bin_path)?;
        if actual_hash != expected_bin_hash {
            log::info!(
                "{} hash mismatch (expected {}, got {}), re-installing toolchain",
                tool.name(),
                format_hex(&expected_bin_hash),
                format_hex(&actual_hash)
            );
            needs_install = true;
            break;
        }
    }

    if needs_install {
        // Perform installation. Note that, because we validate SHA-256
        // checksums against values baked into the binary, allowing the user to
        // override the download URL does not represent a security risk.
        let base_url = std::env::var("ANNEAL_SETUP_AENEAS_BASE_URL").unwrap_or_else(|_| {
            "https://github.com/AeneasVerif/aeneas/releases/download".to_string()
        });

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

        extract_artifact(&data, &toolchain.root)?;

        let lean_dir = toolchain.root.join("backends").join("lean");
        if lean_dir.exists() {
            prebuild_lean_library(&lean_dir)?;
        } else {
            log::warn!("Lean directory not found at {:?}", lean_dir);
        }

        println!("Successfully installed toolchain v{tag}");
    } else {
        log::info!("toolchain is already installed and verified");
    }

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
