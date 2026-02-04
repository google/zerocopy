// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// This script is a thin wrapper around Cargo that provides human-friendly
// toolchain names which are automatically translated to the toolchain versions
// we have pinned in CI.
//
//   cargo-zerocopy --version <toolchain-name> # looks up the version for the named toolchain
//   cargo-zerocopy +<toolchain-name> [...]    # runs cargo commands with the named toolchain
//   cargo-zerocopy +all [...]                 # runs cargo commands with each toolchain
//
// The meta-toolchain "all" instructs this script to run the provided command
// once for each "major" toolchain (msrv, stable, nightly). This does not
// include any toolchain which is listed in the `package.metadata.build-rs`
// Cargo.toml section.

use std::{
    env, fmt, fs,
    io::{self, Read as _},
    process::{self, Command, Output},
};

use toml::{map::Map, Value};

#[derive(Debug)]
enum Error {
    NoArguments,
    UnrecognizedArgument(String),
    MissingToolchainVersion,
    UnrecognizedToolchain(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoArguments => write!(f, "No arguments provided"),
            Self::UnrecognizedArgument(arg) => write!(f, "Unrecognized argument: '{arg}'"),
            Self::MissingToolchainVersion => write!(f, "No toolchain version specified after '--version'"),
            Self::UnrecognizedToolchain(name) => write!(f, "Unrecognized toolchain name: `{name}` (options are 'msrv', 'stable', and 'nightly')")
        }
    }
}

impl std::error::Error for Error {}

trait CommandExt {
    fn output_or_exit(&mut self) -> Output;
    fn execute(&mut self);
}

impl CommandExt for Command {
    fn output_or_exit(&mut self) -> Output {
        if let Ok(output) = self.output() {
            if !output.status.success() {
                eprintln!(
                    "[cargo-zerocopy] failed while capturing output from command: {:?}",
                    self
                );
                let stdout = std::str::from_utf8(&output.stdout).unwrap();
                let stderr = std::str::from_utf8(&output.stderr).unwrap();
                eprintln!("[cargo-zerocopy] stdout: {stdout}");
                eprintln!("[cargo-zerocopy] stderr: {stderr}");
                process::exit(output.status.code().unwrap_or(1));
            }
            output
        } else {
            eprintln!("[cargo-zerocopy] failed to run command: {:?}", self);
            process::exit(1);
        }
    }

    fn execute(&mut self) {
        if let Ok(status) = self.status() {
            if !status.success() {
                eprintln!("[cargo-zerocopy] failed while executing command: {:?}", self);
                process::exit(status.code().unwrap_or(1));
            }
        } else {
            eprintln!("[cargo-zerocopy] failed to run command: {:?}", self);
            process::exit(1);
        }
    }
}

struct Versions {
    msrv: String,
    stable: String,
    nightly: String,
    build_rs: Map<String, Value>,
}

impl Versions {
    fn get(&self, name: &str) -> Result<&str, Error> {
        Ok(match name {
            "msrv" => &self.msrv,
            "stable" => &self.stable,
            "nightly" => &self.nightly,
            _ => self
                .build_rs
                .get(name)
                .ok_or(Error::UnrecognizedToolchain(name.to_string()))
                .map(|value| value.as_str().unwrap())?,
        })
    }
}

fn get_toolchain_versions() -> Versions {
    let manifest_text = fs::read_to_string("Cargo.toml").unwrap();
    let manifest = toml::from_str::<Value>(&manifest_text).unwrap();

    let package = manifest.as_table().unwrap()["package"].as_table().unwrap();
    let metadata = package["metadata"].as_table().unwrap();
    let build_rs = metadata["build-rs"].as_table().unwrap();
    let ci = metadata["ci"].as_table().unwrap();

    Versions {
        msrv: package["rust-version"].as_str().unwrap().to_string(),
        stable: ci["pinned-stable"].as_str().unwrap().to_string(),
        nightly: ci["pinned-nightly"].as_str().unwrap().to_string(),
        build_rs: build_rs.clone(),
    }
}

fn is_toolchain_installed(versions: &Versions, name: &str) -> Result<bool, Error> {
    let version = versions.get(name)?;
    let output = rustup(["run", version, "cargo", "version"], None).output().unwrap();
    if output.status.success() {
        let output = rustup([&format!("+{version}"), "component", "list"], None).output_or_exit();
        let stdout = String::from_utf8(output.stdout).unwrap();
        Ok(stdout.contains("rust-src (installed)"))
    } else {
        Ok(false)
    }
}

fn install_toolchain_or_exit(versions: &Versions, name: &str) -> Result<(), Error> {
    eprintln!("[cargo-zerocopy] missing either toolchain '{name}' or component 'rust-src'");
    if env::var("GITHUB_RUN_ID").is_ok() {
        eprintln!("[cargo-zerocopy] detected GitHub Actions environment; auto-installing without waiting for confirmation");
    } else if env::var("CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN").is_ok() {
        eprintln!("[cargo-zerocopy] detected CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN environment variable; auto-installing without waiting for confirmation");
    } else {
        eprintln!("[cargo-zerocopy] set CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 to always install toolchains without prompting");
        loop {
            eprint!("[cargo-zerocopy] would you like to install toolchain '{name}' and component 'rust-src' via 'rustup' (y/n)? ");
            let mut input = [0];
            io::stdin().read_exact(&mut input).unwrap();
            match input[0] as char {
                'y' | 'Y' => break,
                'n' | 'N' => process::exit(1),
                _ => (),
            }
        }
    }

    let version = versions.get(name)?;
    rustup(["toolchain", "install", version, "-c", "rust-src"], None).execute();

    Ok(())
}

fn get_rustflags(name: &str) -> String {
    // See #1792 for context on zerocopy_derive_union_into_bytes.
    let mut flags =
        "--cfg zerocopy_derive_union_into_bytes --cfg __ZEROCOPY_INTERNAL_USE_ONLY_DEV_MODE"
            .to_string();
    flags += &format!(" --cfg __ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN=\"{name}\"");

    if name == "nightly" {
        flags += " --cfg __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS";
    }

    flags
}

fn get_toolchain_rustflags(name: &str) -> String {
    format!("--cfg __ZEROCOPY_TOOLCHAIN=\"{}\"", name)
}

fn rustup<'a>(args: impl IntoIterator<Item = &'a str>, env: Option<(&str, &str)>) -> Command {
    let mut cmd = Command::new("rustup");
    // It's important to set `RUSTUP_TOOLCHAIN` to override any value set while
    // running this program. That variable overrides any `+<version>` CLI
    // argument.
    cmd.args(args).env("RUSTUP_TOOLCHAIN", "");
    if let Some((name, val)) = env {
        cmd.env(name, val);
    }
    cmd
}

fn delegate_cargo() -> Result<(), Error> {
    let mut args = env::args();
    let this = args.next().unwrap();
    let versions = get_toolchain_versions();

    match args.next().as_deref() {
        None => Err(Error::NoArguments),
        Some("--version") => {
            let name = args.next().ok_or(Error::MissingToolchainVersion)?;
            println!("{}", versions.get(&name)?);
            Ok(())
        }
        Some("+all") => {
            eprintln!("[cargo-zerocopy] warning: running the same command for each toolchain (msrv, stable, nightly)");
            let args = args.collect::<Vec<_>>();

            for toolchain in ["msrv", "stable", "nightly"] {
                eprintln!("[cargo-zerocopy] running with toolchain: {toolchain}");
                Command::new(this.clone())
                    .arg(format!("+{toolchain}"))
                    .args(args.clone())
                    .execute();
            }
            Ok(())
        }
        Some(arg) => {
            if let Some(name) = arg.strip_prefix('+') {
                let version = versions.get(name)?;

                if !is_toolchain_installed(&versions, name)? {
                    install_toolchain_or_exit(&versions, name)?;
                }

                let env_rustflags = env::vars()
                    .filter_map(|(k, v)| if k == "RUSTFLAGS" { Some(v) } else { None })
                    .next()
                    .unwrap_or_default();

                let rustflags = format!(
                    "{} {} {}",
                    get_rustflags(name),
                    get_toolchain_rustflags(name),
                    env_rustflags,
                );

                let mut cmd = rustup(["run", version, "cargo"], Some(("RUSTFLAGS", &rustflags)));

                if env::var("CARGO_TARGET_DIR").is_ok() {
                    eprintln!("[cargo-zerocopy] WARNING: `CARGO_TARGET_DIR` is set - this may cause `cargo-zerocopy` to behave unexpectedly");
                } else {
                    cmd.env("CARGO_TARGET_DIR", format!("target/by-toolchain/{}", name));
                }

                // Computes the fully-qualified package name of workspace package `p`.
                let fqpn = |p| {
                    // Generate a lockfile, if absent.
                    // This is a prerequisite of running pkgid.
                    let _ = rustup(["run", version, "cargo", "generate-lockfile"], None)
                        .output_or_exit();

                    let output = rustup(["run", version, "cargo", "pkgid", "-p"], None)
                        .arg(p)
                        .output_or_exit();
                    String::from_utf8(output.stdout).unwrap()
                };

                // Replace `-p<package>`, `-p <package>` and `--package <package`
                // with the equivalent of `-p $(cargo pkgid -p <package>)`. We do
                // this because unqualified package names are sometimes ambiguous
                // if a dev-dependency has taken a dependency on an earlier
                // version of zerocopy or zerocopy-derive.
                loop {
                    let Some(arg) = args.next() else {
                        break;
                    };
                    if arg == "-p" || arg == "--package" {
                        cmd.arg(arg);
                        let Some(arg) = args.next() else {
                            break;
                        };
                        cmd.arg(fqpn(arg));
                    } else if arg.starts_with("-p") {
                        cmd.arg("-p");
                        cmd.arg(fqpn(arg[2..].to_string()));
                    } else {
                        cmd.arg(arg);
                    }
                }

                cmd.execute();

                Ok(())
            } else {
                Err(Error::UnrecognizedArgument(arg.to_string()))
            }
        }
    }
}

fn print_usage() {
    let name = env::args().next().unwrap();

    eprintln!("Usage:");
    eprintln!("  {} --version <toolchain-name>", name);
    eprintln!("  {} +<toolchain-name> [...]", name);
    eprintln!("  {} +all [...]", name);
}

fn main() {
    if let Err(e) = delegate_cargo() {
        eprintln!("Error: {e}");
        print_usage();
        process::exit(1);
    }
}
