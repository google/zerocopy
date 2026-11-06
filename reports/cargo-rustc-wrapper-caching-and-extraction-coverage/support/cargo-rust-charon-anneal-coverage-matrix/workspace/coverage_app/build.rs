fn main() {
    println!("cargo:rerun-if-env-changed=PROBE_BUILD_VALUE");
    let value = shared::build_value();
    let out = std::env::var("OUT_DIR").unwrap();
    std::fs::write(format!("{out}/generated.rs"), format!("pub const BUILD_VALUE: u32 = {value};\n")).unwrap();
}
