use std::fs;

/// This build script reads toolchain versioning metadata from `Cargo.toml` and
/// exposes it to the Rust compiler via environment variables.
///
/// This allows us to "bake in" the specific Aeneas commit hash and Lean
/// toolchain version into the Hermes binary, ensuring that the generated
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

    // We expect the metadata to be under `[package.metadata.build-rs]`.
    let metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build-rs"))
        .expect("Cargo.toml must have [package.metadata.build-rs] section");

    // Key in `Cargo.toml` -> Environment variable name
    let vars = [
        ("aeneas_rev", "HERMES_AENEAS_REV"),
        ("lean_toolchain", "HERMES_LEAN_TOOLCHAIN"),
        ("charon_version", "HERMES_CHARON_EXPECTED_VERSION"),
    ];

    for (key, env_var) in vars {
        let value = metadata
            .get(key)
            .and_then(|v| v.as_str())
            .unwrap_or_else(|| panic!("{} must be a string", key));

        println!("cargo:rustc-env={}={}", env_var, value);
    }
}
