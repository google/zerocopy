// Copyright 2026 The Fuchsia Authors
// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT

fn main() {
    // Match the stable-compatible Kbuild selection for the host proc macros.
    if std::env::var_os("CARGO_FEATURE_PROC_MACRO").is_some() {
        println!("cargo:rustc-cfg=wrap_proc_macro");
    }
    if std::env::var_os("CARGO_FEATURE_SPAN_LOCATIONS").is_some() {
        println!("cargo:rustc-cfg=span_locations");
    }
}
