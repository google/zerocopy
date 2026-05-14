use clap::{Parser, Subcommand};
use sha2::Digest;
use std::process::Command;
use toolchain_config::{Checksum, Config, LocalOverride, RemoteArchive, TarZstLibraryExtractor};

#[derive(Parser)]
#[command(name = "toolchain-config-example-static-toml")]
#[command(about = "Example illustrating static TOML integration using toolchain-config library")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Install,
    Hello,
}

fn decode_hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

fn get_root_dir() -> std::path::PathBuf {
    let home = dirs::home_dir().expect("Could not find home directory");
    home.join(".toolchain-config-example-static-toml").join("toolchain")
}

toolchain_config::auto_install!{
    pub const AUTO_CONFIG = "Cargo.toml";
}

fn main() {
    let cli = Cli::parse();
    let root_dir = get_root_dir();

    let checksum_bytes = decode_hex(env!("TOOLCHAIN_CHECKSUM"));
    let mut hasher = sha2::Sha256::new();
    let mut config = Config::new(
        RemoteArchive::new(env!("TOOLCHAIN_URL"), &TarZstLibraryExtractor),
        Checksum::new(&checksum_bytes, &mut hasher),
    );

    match cli.command {
        Commands::Install => {
            let archive_path;
            let local_override = if std::env::var("__TOOLCHAIN_EXAMPLE_STATIC_TOML").is_ok() {
                println!("Local testing override active. Assembling mock toolchain archive...");
                let manifest_dir = std::env::var("CARGO_MANIFEST_DIR")
                    .expect("CARGO_MANIFEST_DIR environment variable missing");
                let script_path = std::path::Path::new(&manifest_dir).join("build-toolchain.sh");

                let status = Command::new(&script_path)
                    .status()
                    .expect("Failed to execute build-toolchain.sh");
                assert!(status.success(), "build-toolchain.sh script failed");

                archive_path = std::path::Path::new(&manifest_dir).join("toolchain.tar.zst");
                Some(LocalOverride::archive(&archive_path, &TarZstLibraryExtractor))
            } else {
                None
            };

            println!("Provisioning toolchain environment...");
            toolchain_config::install_config(&mut config, local_override, &root_dir)
                .expect("Setup subcommand failed");
            println!("Toolchain successfully set up.");
        }
        Commands::Hello => {
            let toolchain_dir = config.toolchain_dir(&root_dir);
            let hello_bin = toolchain_dir.join("bin").join("hello");

            if !hello_bin.exists() {
                eprintln!(
                    "Error: Toolchain executable missing at {:?}. Please run install first.",
                    hello_bin
                );
                std::process::exit(1);
            }

            let status = Command::new(&hello_bin)
                .status()
                .expect("Failed to delegate execution to bin/hello");
            std::process::exit(status.code().unwrap_or(1));
        }
    }
}
