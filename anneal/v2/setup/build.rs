fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=Cargo.toml");

    println!(
        "cargo:rustc-env=SETUP_ARCHIVE_BASE_URL=https://github.com/google/zerocopy/releases/download/build-2026.04.19.084341-62d9816418bdb3d566381c1a4070784f7cf5380e",
    );
    for arch in ["LINUX_AARCH64", "LINUX_X86_64", "MACOS_AARCH64", "MACOS_X86_64"] {
        println!(
            "cargo:rustc-env=SETUP_ARCHIVE_SHA256_{arch}=54c9eabc88dbb604758edce1b51287ccd69c8a93db003278ea9ad4e97bb24a05",
        );
    }
}
