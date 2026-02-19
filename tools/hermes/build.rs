use std::{fs, path::Path};

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

    let cargo_toml_path = Path::new("Cargo.toml");
    let cargo_toml_content =
        fs::read_to_string(cargo_toml_path).expect("failed to read Cargo.toml");

    let cargo_toml: toml::Value =
        toml::from_str(&cargo_toml_content).expect("failed to parse Cargo.toml");

    // We expect the metadata to be under `[package.metadata.build-rs]`.
    let metadata = cargo_toml
        .get("package")
        .and_then(|p| p.get("metadata"))
        .and_then(|m| m.get("build-rs"))
        .expect("Cargo.toml must have [package.metadata.build-rs] section");

    let aeneas_rev =
        metadata.get("aeneas_rev").and_then(|v| v.as_str()).expect("aeneas_rev must be a string");

    let lean_toolchain = metadata
        .get("lean_toolchain")
        .and_then(|v| v.as_str())
        .expect("lean_toolchain must be a string");

    println!("cargo:rustc-env=HERMES_AENEAS_REV={}", aeneas_rev);
    println!("cargo:rustc-env=HERMES_LEAN_TOOLCHAIN={}", lean_toolchain);
}
