#[path = "src/third_party/libc/build.rs"]
pub(crate) mod libc;

fn main() {
    // Avoid unnecessary re-building.
    println!("cargo:rerun-if-changed=build.rs");

    let (minor, _nightly) = libc::rustc_minor_nightly();
    if minor >= 57 {
        println!("cargo:rustc-cfg=zerocopy_panic_in_const_fn");
    }
}
