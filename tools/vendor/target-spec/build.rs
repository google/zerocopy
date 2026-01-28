// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{env, fs, path::Path};

fn main() {
    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("build_target.rs");

    let target = env::var("TARGET").unwrap();

    // Non-x86/amd64 platforms don't have this environment variable defined at all.
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_else(|_| "".to_string());
    // The features are in the format |foo,bar|. Convert to |&["foo", "bar", ]|;
    let mut out = vec!["&["];
    for feature in features.split(',') {
        out.push("\"");
        out.push(feature);
        out.push("\", ");
    }
    out.push("]");
    let features = out.join("");

    fs::write(
        dest_path,
        format!(
            "static BUILD_TARGET: &str = \"{target}\";\n\
            \n\
            static BUILD_TARGET_FEATURES: &[&str] = {features};\
            ",
        ),
    )
    .unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
