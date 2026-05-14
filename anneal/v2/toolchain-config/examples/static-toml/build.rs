fn main() {
    println!("cargo:rerun-if-changed=Cargo.toml");

    let os = std::env::consts::OS;
    let arch = std::env::consts::ARCH;

    let content = std::fs::read_to_string("Cargo.toml").expect("Failed to read Cargo.toml");
    let toml: toml::Value = toml::from_str(&content).expect("Failed to parse Cargo.toml");

    let metadata = toml
        .get("package")
        .and_then(|m| m.get("toolchain"))
        .expect("Missing [package.metadata.toolchain] in Cargo.toml");

    let target_table = metadata
        .get(os)
        .and_then(|o| o.get(arch))
        .unwrap_or_else(|| panic!("Missing toolchain configuration for {}.{}", os, arch));

    let checksum = target_table
        .get("checksum")
        .and_then(|c| c.as_str())
        .expect("Missing checksum key");
    let url = target_table
        .get("url")
        .and_then(|u| u.as_str())
        .expect("Missing url key");

    println!("cargo:rustc-env=TOOLCHAIN_CHECKSUM={}", checksum);
    println!("cargo:rustc-env=TOOLCHAIN_URL={}", url);
}
