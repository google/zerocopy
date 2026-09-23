use std::fs;

use sha2::{Digest as _, Sha256};

/// This build script reads toolchain versioning metadata from `Cargo.toml` and
/// exposes it to the Rust compiler via environment variables.
///
/// This allows us to "bake in" the specific Aeneas commit hash and Lean
/// toolchain version into the Anneal binary, ensuring that the generated
/// `lakefile.lean` and `lean-toolchain` files are always consistent with the
/// versions specified in `Cargo.toml`.
fn main() {
    // Re-run this script if `Cargo.toml` changes, as that's where the metadata
    // lives.
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=Cargo.toml");

    let cargo_toml_content = fs::read_to_string("Cargo.toml").expect("failed to read Cargo.toml");
    let cargo_toml: toml::Value =
        toml::from_str(&cargo_toml_content).expect("failed to parse Cargo.toml");

    println!("cargo:rustc-env=ANNEAL_EXOCRATE_VERSION_SLUG={}", exocrate_version_slug());

    // We expect the metadata to be under `[package.metadata.build_rs]`.
    let build_rs_metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build_rs"))
        .expect("Cargo.toml must have [package.metadata.build_rs] section");

    let vars = [("aeneas_rev", "ANNEAL_AENEAS_REV"), ("lean_toolchain", "ANNEAL_LEAN_TOOLCHAIN")];

    for (key, env_var) in vars {
        let value = build_rs_metadata
            .get(key)
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("{} must be a string", key));

        println!("cargo:rustc-env={}={}", env_var, value);
    }

    if let Some(exocrate_metadata) = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("exocrate"))
        .and_then(|e| e.as_table())
    {
        for (os, os_table) in exocrate_metadata {
            let Some(os_table) = os_table.as_table() else {
                continue;
            };
            for (arch, config) in os_table {
                let Some(config) = config.as_table() else {
                    continue;
                };
                let env_platform = format!("{}_{}", os, arch).to_uppercase();

                for key in ["sha256", "url"] {
                    let value = config.get(key).and_then(|v| v.as_str()).unwrap_or_else(|| {
                        panic!("package.metadata.exocrate.{os}.{arch}.{key} must be a string")
                    });
                    println!(
                        "cargo:rustc-env=ANNEAL_EXOCRATE_{}_{}={}",
                        env_platform,
                        key.to_uppercase(),
                        value
                    );
                }
            }
        }
    }
}

fn exocrate_version_slug() -> String {
    let mut hasher = Sha256::new();
    for path in ["Cargo.toml", "Cargo.lock"] {
        hasher.update(path.as_bytes());
        hasher.update(fs::read(path).unwrap_or_else(|err| panic!("failed to read {path}: {err}")));
    }
    hasher.update(
        std::env::var("CARGO_CFG_TARGET_OS")
            .expect("CARGO_CFG_TARGET_OS is set by Cargo")
            .as_bytes(),
    );
    hasher.update(
        std::env::var("CARGO_CFG_TARGET_ARCH")
            .expect("CARGO_CFG_TARGET_ARCH is set by Cargo")
            .as_bytes(),
    );
    format!("{:x}", hasher.finalize())
}
