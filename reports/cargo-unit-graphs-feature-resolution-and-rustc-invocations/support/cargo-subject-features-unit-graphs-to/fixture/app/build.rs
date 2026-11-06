fn main() {
    println!("cargo:rustc-env=PROBE_BUILD_TAG={}", probe_dep::flavor());
}

