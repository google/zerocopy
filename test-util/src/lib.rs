// Copyright 2023 The Fuchsia Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

pub use static_assertions::*;
pub use ui_test::*;

#[rustversion::nightly(2023-05-24)]
pub static TOOLCHAIN: &str = "nightly-2023-05-25";

#[rustversion::stable(1.69.0)]
pub static TOOLCHAIN: &str = "1.69.0";

#[rustversion::stable(1.65.0)]
pub static TOOLCHAIN: &str = "1.65.0";

macro_rules! manifest_path {
    () => {
        concat!(env!("CARGO_MANIFEST_DIR"), "/../Cargo.toml")
    };
}

static MANIFEST: &str = include_str!(manifest_path!());

pub struct PinnedToolchains {
    pub msrv: String,
    pub stable: String,
    pub nightly: String,
}

pub fn pinned_toolchains() -> color_eyre::eyre::Result<PinnedToolchains> {
    use cargo_toml::Manifest;

    #[derive(serde::Deserialize)]
    #[serde(rename_all = "kebab-case")]
    struct Metadata {
        pinned_stable: String,
        pinned_nightly: String,
    }

    let manifest = Manifest::<Metadata>::from_slice_with_metadata(MANIFEST.as_bytes())?;
    let package = manifest.package.expect("expected `package` section");
    let package_metadata = package.metadata.expect("expected `package.metadata` section");

    let msrv = package.rust_version.expect("`package.rust-version` is unset");
    let msrv = msrv.get()?.to_string();
    let stable = package_metadata.pinned_stable;
    let nightly = package_metadata.pinned_nightly;

    Ok(PinnedToolchains { msrv, stable, nightly })
}

/// Bless tests with `cargo test -- -- --bless`.
pub fn should_bless() -> bool {
    std::env::args().any(|arg| arg == "--bless")
}

/// Run (and optionally bless) UI tests in a given folder, within a given toolchain.
pub fn ui_test(toolchain: &str, folder: &str, bless: bool) -> color_eyre::eyre::Result<()> {
    let toolchain = String::from("+") + toolchain;

    // // Make sure we can depend on zerocopy in ui tests.
    // let dependencies_crate_manifest_path =
    //     Some(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml").into());

    // let mut config = ui_test::Config { dependencies_crate_manifest_path, ..Default::default() };

    // if bless {
    //     config.output_conflict_handling = OutputConflictHandling::Bless;
    // }

    // // Place the build artifacts in the `target/ui` directory instead of in the
    // // crate root.
    // config.out_dir = Some("target/ui.rs".into());

    // config.program = CommandBuilder::rustc();
    // config.root_dir = folder.into();
    // config.program.args.insert(0, toolchain.into());

    let mut config = ui_test::Config::rustc(folder.into());
    if bless {
        config.output_conflict_handling = OutputConflictHandling::Bless;
    }

    // Make sure we can depend on zerocopy in ui tests.
    config.dependencies_crate_manifest_path = Some(concat!(env!("CARGO_MANIFEST_DIR"), "/Cargo.toml").into());
    config.out_dir = "target/ui.rs".into();
    config.program.args.insert(0, toolchain.into());

    run_tests(config)
}
