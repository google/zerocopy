// Copyright 2022 Oxide Computer Company
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use std::env;

#[derive(Copy, Clone)]
enum Backend {
    // Standard (read: illumos) probe registration
    Standard,
    // MacOS linker-aware probe registration
    Linker,
    // SystemTap version 3 probes (read: Linux without dtrace)
    Stap3,
    // Provide probe macros, but probes are no-ops (dtrace-less OSes)
    NoOp,
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(usdt_backend_noop)");
    println!("cargo:rustc-check-cfg=cfg(usdt_backend_stapsdt)");
    println!("cargo:rustc-check-cfg=cfg(usdt_backend_linker)");
    println!("cargo:rustc-check-cfg=cfg(usdt_backend_standard)");

    let backend = match env::var("CARGO_CFG_TARGET_OS").ok().as_deref() {
        Some("macos") => Backend::Linker,
        Some("illumos") | Some("solaris") | Some("freebsd") => Backend::Standard,
        Some("linux") => Backend::Stap3,
        _ => Backend::NoOp,
    };

    match backend {
        Backend::NoOp => {
            println!("cargo:rustc-cfg=usdt_backend_noop");
        }
        Backend::Stap3 => {
            println!("cargo:rustc-cfg=usdt_backend_stapsdt");
        }
        Backend::Linker => {
            println!("cargo:rustc-cfg=usdt_backend_linker");
        }
        Backend::Standard => {
            println!("cargo:rustc-cfg=usdt_backend_standard");
        }
    }
}
