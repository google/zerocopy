#![allow(dead_code)]

mod resolve {
    use std::path::{Path, PathBuf};

    #[derive(Clone, Debug)]
    pub struct AnnealTargetName {
        pub package_name: String,
        pub target_name: String,
    }

    #[repr(u8)]
    #[derive(Clone, Copy, Debug)]
    pub enum AnnealTargetKind { RLib = 1 }

    pub struct AnnealTarget {
        pub name: AnnealTargetName,
        pub kind: AnnealTargetKind,
        pub manifest_path: PathBuf,
    }

    pub struct LockedRoots { root: PathBuf }
    impl LockedRoots {
        pub fn llbc_root(&self) -> &Path { &self.root }
    }
}

#[path = "scanner.rs"]
mod scanner;

fn main() {
    let manifest_path = std::env::args_os().nth(1).expect("manifest path argument");
    let target = resolve::AnnealTarget {
        name: resolve::AnnealTargetName {
            package_name: "unit_key_probe".to_owned(),
            target_name: "unit_key_probe".to_owned(),
        },
        kind: resolve::AnnealTargetKind::RLib,
        manifest_path: manifest_path.into(),
    };
    let artifact = scanner::AnnealArtifact::from(&target);
    for case in ["debug", "release", "cfg_alt"] {
        println!("{case}\t{}\t{}", artifact.artifact_slug(), artifact.llbc_file_name());
    }
}
