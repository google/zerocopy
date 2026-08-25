// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Refreshes target support after the stable/nightly roller edits a pin.
//!
//! Keep this command line coordinated with
//! `.github/workflows/roll-pinned-toolchain-versions.yml`. The workflow must
//! capture the old pin before editing `zerocopy/Cargo.toml`; this command reads
//! the post-edit manifest and receives that old value explicitly. The library
//! then proves that the pre-existing catalog described the reconstructed old
//! state before it verifies and writes the new state.

use std::{env, path::PathBuf, process};

use zc::inventory::refresh_rust_target_support;

struct Arguments {
    repository: PathBuf,
    pin: String,
    old_version: String,
}

fn parse_arguments(mut args: impl Iterator<Item = String>) -> Result<Arguments, String> {
    let program = args.next().unwrap_or_else(|| "refresh-rust-target-support".to_owned());
    let values = args.collect::<Vec<_>>();
    let [repository_flag, repository, pin_flag, pin, old_flag, old_version] = values.as_slice()
    else {
        return Err(format!(
            "usage: {program} --repository ROOT --pin stable|nightly --old-version VERSION"
        ));
    };
    if repository_flag != "--repository" || pin_flag != "--pin" || old_flag != "--old-version" {
        return Err(format!(
            "usage: {program} --repository ROOT --pin stable|nightly --old-version VERSION"
        ));
    }
    if repository.is_empty()
        || !matches!(pin.as_str(), "stable" | "nightly")
        || old_version.is_empty()
    {
        return Err(format!(
            "usage: {program} --repository ROOT --pin stable|nightly --old-version VERSION"
        ));
    }
    Ok(Arguments {
        repository: repository.into(),
        pin: pin.clone(),
        old_version: old_version.clone(),
    })
}

fn main() {
    let arguments = parse_arguments(env::args()).unwrap_or_else(|error| {
        eprintln!("{error}");
        process::exit(2);
    });
    if let Err(error) =
        refresh_rust_target_support(arguments.repository, &arguments.pin, &arguments.old_version)
    {
        eprintln!("{error}");
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::parse_arguments;

    fn args<'a>(values: &'a [&'a str]) -> impl Iterator<Item = String> + 'a {
        values.iter().map(|value| (*value).to_owned())
    }

    #[test]
    fn accepts_only_the_coordinated_argument_contract() {
        let parsed = parse_arguments(args(&[
            "refresh-rust-target-support",
            "--repository",
            "..",
            "--pin",
            "stable",
            "--old-version",
            "1.93.1",
        ]))
        .unwrap();
        assert_eq!(parsed.repository, std::path::Path::new(".."));
        assert_eq!(parsed.pin, "stable");
        assert_eq!(parsed.old_version, "1.93.1");

        assert!(parse_arguments(args(&[
            "refresh-rust-target-support",
            "--pin",
            "stable",
            "--repository",
            "..",
            "--old-version",
            "1.93.1",
        ]))
        .is_err());

        for invalid in [
            &[
                "refresh-rust-target-support",
                "--repository",
                "",
                "--pin",
                "stable",
                "--old-version",
                "1.93.1",
            ][..],
            &[
                "refresh-rust-target-support",
                "--repository",
                "..",
                "--pin",
                "beta",
                "--old-version",
                "1.93.1",
            ][..],
            &[
                "refresh-rust-target-support",
                "--repository",
                "..",
                "--pin",
                "stable",
                "--old-version",
                "",
            ][..],
            &["refresh-rust-target-support", "--repository", ".."][..],
            &[
                "refresh-rust-target-support",
                "--repository",
                "..",
                "--pin",
                "stable",
                "--old-version",
                "1.93.1",
                "extra",
            ][..],
        ] {
            assert!(parse_arguments(args(invalid)).is_err(), "accepted {invalid:?}");
        }
    }
}
