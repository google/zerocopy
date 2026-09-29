use clap::Parser as _;

#[allow(dead_code)]
#[path = "resolve.rs"]
mod resolve;

mod setup {
    use std::path::PathBuf;

    pub struct Toolchain {
        cargo: PathBuf,
        rustc: PathBuf,
        rust_lib: PathBuf,
    }

    impl Toolchain {
        pub fn from_env() -> Self {
            Self {
                cargo: std::env::var_os("PROBE_CARGO").expect("PROBE_CARGO").into(),
                rustc: std::env::var_os("PROBE_RUSTC").expect("PROBE_RUSTC").into(),
                rust_lib: std::env::var_os("PROBE_RUST_LIB").expect("PROBE_RUST_LIB").into(),
            }
        }
        pub fn rust_lib(&self) -> PathBuf {
            self.rust_lib.clone()
        }
    }

    pub enum Tool {
        Cargo,
        Rustc,
    }
    impl Tool {
        pub fn path(&self, toolchain: &Toolchain) -> PathBuf {
            match self {
                Self::Cargo => toolchain.cargo.clone(),
                Self::Rustc => toolchain.rustc.clone(),
            }
        }
    }
    pub fn rust_library_path_env_var() -> &'static str {
        if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" }
    }
}

mod util {
    use std::path::PathBuf;
    pub struct DirLock {
        pub path: PathBuf,
    }
    impl DirLock {
        pub fn lock_exclusive(path: PathBuf) -> anyhow::Result<Self> {
            std::fs::create_dir_all(&path)?;
            Ok(Self { path })
        }
    }
}

#[derive(clap::Parser)]
struct Cli {
    #[command(flatten)]
    args: resolve::Args,
}

fn main() -> anyhow::Result<()> {
    let args = Cli::parse();
    let roots = resolve::resolve_roots(&args.args, &setup::Toolchain::from_env())?;
    for root in roots.roots {
        println!(
            "{}|{}|{:?}|{}",
            root.name.package_name,
            root.name.target_name,
            root.kind,
            root.manifest_path.display()
        );
    }
    Ok(())
}
