// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

exocrate::config! {
    const CONFIG: Config = Config {
        manifest_path: "../Cargo.toml",
        lockfile_path: "../Cargo.lock",
        rel_dir_path: [".anneal", "toolchain"],
    };
}

exocrate::parse_remote_archive! {
    const REMOTE: RemoteArchive = "Cargo.toml" [
        (linux, x86_64),
        (macos, x86_64),
        (linux, aarch64),
        (macos, aarch64),
    ];
}

fn main() {}
