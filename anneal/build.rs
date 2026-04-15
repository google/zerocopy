use std::fs;

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

    // We expect the metadata to be under `[package.metadata.build_rs]`.
    let build_rs_metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build_rs"))
        .expect("Cargo.toml must have [package.metadata.build_rs] section");

    // Key in `Cargo.toml` -> Environment variable name
    let vars = [
        ("aeneas_rev", "ANNEAL_AENEAS_REV"),
        ("lean_toolchain", "ANNEAL_LEAN_TOOLCHAIN"),
        ("charon_rust_toolchain", "ANNEAL_CHARON_RUST_TOOLCHAIN"),
    ];

    for (key, env_var) in vars {
        let value = build_rs_metadata
            .get(key)
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("{} must be a string", key));

        println!("cargo:rustc-env={}={}", env_var, value);
    }

    // Parse [package.metadata.anneal.dependencies]
    if let Some(anneal_metadata) = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("anneal"))
        .and_then(|h| h.get("dependencies"))
        .and_then(|d| d.as_table())
    {
        for (dep_name, dep_meta) in anneal_metadata {
            let dep_upper = dep_name.to_uppercase();
            if let Some(tag) = dep_meta.get("tag").and_then(|t| t.as_str()) {
                println!("cargo:rustc-env=ANNEAL_{}_TAG={}", dep_upper, tag);
            }

            if let Some(date) = dep_meta.get("date").and_then(|t| t.as_str()) {
                println!("cargo:rustc-env=ANNEAL_{}_DATE={}", dep_upper, date);
            }

            if let Some(checksums) = dep_meta.get("checksums").and_then(|c| c.as_table()) {
                for (platform, checksum) in checksums {
                    if let Some(hash) = checksum.as_str() {
                        // Standardize platform name for env var (dashes -> underscores, upper case)
                        let env_platform = platform.replace('-', "_").to_uppercase();
                        println!(
                            "cargo:rustc-env=ANNEAL_{}_CHECKSUM_{}={}",
                            dep_upper, env_platform, hash
                        );
                    }
                }
            }
        }
    }
}
