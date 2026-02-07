use std::env;
use std::fs;
use std::io::Write;
use std::path;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    // env::ARCH doesn't include the full triplet, and as far as I know there isn't a cleaner way of getting the full triplet
    // (see cargo.rs for the rest of this implementation)
    let out = path::PathBuf::from(env::var_os("OUT_DIR").expect("run within cargo"))
        .join("current_target.txt");
    let default_target = env::var("TARGET").expect("run as cargo build script");
    let mut file = fs::File::create(out).expect("can write to OUT_DIR");
    file.write_all(default_target.as_bytes())
        .expect("can write to OUT_DIR");
}
