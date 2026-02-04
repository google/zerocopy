//! Use `cargo` to build dependencies and make them available in your tests

use bstr::ByteSlice;
use cargo_metadata::{camino::Utf8PathBuf, BuildScript, DependencyKind};
use cargo_platform::Cfg;
use std::{
    collections::{HashMap, HashSet},
    ffi::OsString,
    path::PathBuf,
    process::Command,
    str::FromStr,
};

use crate::{
    build_manager::{Build, BuildManager},
    custom_flags::Flag,
    per_test_config::TestConfig,
    test_result::Errored,
    CommandBuilder, Config, OutputConflictHandling,
};

#[derive(Default, Debug)]
/// Describes where to find the binaries built for the dependencies
pub struct Dependencies {
    /// All paths that must be imported with `-L dependency=`. This is for
    /// finding proc macros run on the host and dependencies for the target.
    pub import_paths: Vec<PathBuf>,
    /// Unnamed dependencies that build scripts asked us to link
    pub import_libs: Vec<PathBuf>,
    /// The name as chosen in the `Cargo.toml` and its corresponding rmeta file.
    pub dependencies: Vec<(String, Vec<Utf8PathBuf>)>,
}

fn cfgs(config: &Config) -> Result<Vec<Cfg>, Errored> {
    let Some(cfg) = &config.program.cfg_flag else {
        return Ok(vec![]);
    };
    let mut cmd = config.program.build(&config.out_dir);
    cmd.arg(cfg);
    cmd.arg("--target").arg(config.target.as_ref().unwrap());
    let output = match cmd.output() {
        Ok(o) => o,
        Err(e) => {
            return Err(Errored {
                command: format!("{cmd:?}"),
                stderr: e.to_string().into_bytes(),
                stdout: vec![],
                errors: vec![],
            })
        }
    };

    if !output.status.success() {
        return Err(Errored {
            command: format!("{cmd:?}"),
            stderr: output.stderr,
            stdout: output.stdout,
            errors: vec![],
        });
    }
    let mut cfgs = vec![];

    let stdout = String::from_utf8(output.stdout).map_err(|e| Errored {
        command: "processing cfg information from rustc as utf8".into(),
        errors: vec![],
        stderr: e.to_string().into_bytes(),
        stdout: vec![],
    })?;
    for line in stdout.lines() {
        cfgs.push(Cfg::from_str(line).map_err(|e| Errored {
            command: "parsing cfgs from rustc output".into(),
            errors: vec![],
            stderr: e.to_string().into_bytes(),
            stdout: vec![],
        })?);
    }

    Ok(cfgs)
}

/// Compiles dependencies and returns the crate names and corresponding rmeta files.
fn build_dependencies_inner(
    config: &Config,
    info: &DependencyBuilder,
) -> Result<Dependencies, Errored> {
    let mut build = info.program.build(&config.out_dir);
    build.arg(&info.crate_manifest_path);

    if let Some(target) = &config.target {
        build.arg(format!("--target={target}"));
    }

    if let Some(packages) = &info.build_std {
        if packages.is_empty() {
            build.arg("-Zbuild-std");
        } else {
            build.arg(format!("-Zbuild-std={packages}"));
        }
    }

    // Reusable closure for setting up the environment both for artifact generation and `cargo_metadata`
    let set_locking = |cmd: &mut Command| {
        if let OutputConflictHandling::Error = config.output_conflict_handling {
            cmd.arg("--locked");
        }
    };

    set_locking(&mut build);
    build.arg("--message-format=json");

    let output = match build.output() {
        Err(e) => {
            return Err(Errored {
                command: format!("{build:?}"),
                stderr: e.to_string().into_bytes(),
                stdout: vec![],
                errors: vec![],
            })
        }
        Ok(o) => o,
    };

    if !output.status.success() {
        let stdout = output
            .stdout
            .lines()
            .flat_map(
                |line| match serde_json::from_slice::<cargo_metadata::Message>(line) {
                    Ok(cargo_metadata::Message::CompilerArtifact(artifact)) => {
                        format!("{artifact:?}\n").into_bytes()
                    }
                    Ok(cargo_metadata::Message::BuildFinished(bf)) => {
                        format!("{bf:?}\n").into_bytes()
                    }
                    Ok(cargo_metadata::Message::BuildScriptExecuted(be)) => {
                        format!("{be:?}\n").into_bytes()
                    }
                    Ok(cargo_metadata::Message::TextLine(s)) => s.into_bytes(),
                    Ok(cargo_metadata::Message::CompilerMessage(msg)) => msg
                        .target
                        .src_path
                        .as_str()
                        .as_bytes()
                        .iter()
                        .copied()
                        .chain([b'\n'])
                        .chain(msg.message.rendered.unwrap_or_default().into_bytes())
                        .collect(),
                    Ok(_) => vec![],
                    Err(_) => line.iter().copied().chain([b'\n']).collect(),
                },
            )
            .collect();
        return Err(Errored {
            command: format!("{build:?}"),
            stderr: output.stderr,
            stdout,
            errors: vec![],
        });
    }

    // Collect all artifacts generated
    let artifact_output = output.stdout;
    let mut import_paths: HashSet<PathBuf> = HashSet::new();
    let mut import_libs: HashSet<PathBuf> = HashSet::new();
    let mut artifacts = HashMap::new();
    for line in artifact_output.lines() {
        let Ok(message) = serde_json::from_slice::<cargo_metadata::Message>(line) else {
            continue;
        };
        match message {
            cargo_metadata::Message::CompilerArtifact(artifact) => {
                if artifact
                    .target
                    .crate_types
                    .iter()
                    .all(|ctype| !matches!(ctype.as_str(), "proc-macro" | "lib" | "rlib"))
                {
                    continue;
                }
                for filename in &artifact.filenames {
                    import_paths.insert(filename.parent().unwrap().into());
                }
                let package_id = artifact.package_id;
                if let Some(prev) = artifacts.insert(
                    package_id.clone(),
                    Ok((artifact.target.name, artifact.filenames)),
                ) {
                    artifacts.insert(
                        package_id.clone(),
                        Err(format!(
                            "{prev:#?} vs {:#?} ({:?})",
                            artifacts[&package_id], artifact.target.crate_types
                        )),
                    );
                }
            }
            cargo_metadata::Message::BuildScriptExecuted(BuildScript {
                linked_libs,
                linked_paths,
                ..
            }) => {
                import_paths.extend(linked_paths.into_iter().map(Into::into));
                import_libs.extend(linked_libs.into_iter().map(Into::into));
            }
            _ => {}
        }
    }

    // Check which crates are mentioned in the crate itself
    let mut metadata = cargo_metadata::MetadataCommand::new().cargo_command();
    metadata
        .arg("--manifest-path")
        .arg(&info.crate_manifest_path);
    info.program.apply_env(&mut metadata);
    set_locking(&mut metadata);
    let output = match metadata.output() {
        Err(e) => {
            return Err(Errored {
                command: format!("{metadata:?}"),
                errors: vec![],
                stderr: e.to_string().into_bytes(),
                stdout: vec![],
            })
        }
        Ok(output) => output,
    };

    if !output.status.success() {
        return Err(Errored {
            command: format!("{metadata:?}"),
            stderr: output.stderr,
            stdout: output.stdout,
            errors: vec![],
        });
    }

    let output = output.stdout;

    let cfg = cfgs(config)?;

    for line in output.lines() {
        if !line.starts_with(b"{") {
            continue;
        }
        let metadata: cargo_metadata::Metadata =
            serde_json::from_slice(line).map_err(|err| Errored {
                command: "decoding cargo metadata json".into(),
                errors: vec![],
                stderr: err.to_string().into_bytes(),
                stdout: vec![],
            })?;
        // Only take artifacts that are defined in the Cargo.toml

        // First, find the root artifact
        let root = metadata
            .packages
            .iter()
            .find(|package| {
                package.manifest_path.as_std_path().canonicalize().unwrap()
                    == info.crate_manifest_path.canonicalize().unwrap()
            })
            .unwrap();

        // Then go over all of its dependencies
        let mut dependencies = root
            .dependencies
            .iter()
            .filter(|dep| matches!(dep.kind, DependencyKind::Normal))
            // Only consider dependencies that are enabled on the current target
            .filter(|dep| match &dep.target {
                Some(platform) => platform.matches(config.target.as_ref().unwrap(), &cfg),
                None => true,
            })
            .map(|dep| {
                for p in &metadata.packages {
                    if p.name != dep.name {
                        continue;
                    }
                    if dep
                        .path
                        .as_ref()
                        .is_some_and(|path| p.manifest_path.parent().unwrap() == path)
                        || dep.req.matches(&p.version)
                    {
                        return (p, dep.rename.clone().unwrap_or_else(|| p.name.clone()));
                    }
                }
                panic!("dep not found: {dep:#?}")
            })
            // Also expose the root crate
            .chain(std::iter::once((root, root.name.clone())))
            .filter_map(|(package, name)| {
                // Get the id for the package matching the version requirement of the dep
                let id = &package.id;
                // Return the name chosen in `Cargo.toml` and the path to the corresponding artifact
                match artifacts.remove(id) {
                    Some(Ok((_, artifacts))) => Some(Ok((name.replace('-', "_"), artifacts))),
                    Some(Err(what)) => Some(Err(Errored {
                        command: what,
                        errors: vec![],
                        stderr: id.to_string().into_bytes(),
                        stdout: "`ui_test` does not support crates that appear as both build-dependencies and core dependencies".as_bytes().into(),
                    })),
                    None => {
                        if name == root.name {
                            // If there are no artifacts, this is the root crate and it is being built as a binary/test
                            // instead of a library. We simply add no artifacts, meaning you can't depend on functions
                            // and types declared in the root crate.
                            None
                        } else {
                            panic!("no artifact found for `{name}`(`{id}`):`\n{}", artifact_output.to_str().unwrap())
                        }
                    }
                }
            })
            .collect::<Result<Vec<_>, Errored>>()?;
        let import_paths = import_paths.into_iter().collect();
        let import_libs = import_libs.into_iter().collect();

        if info.build_std.is_some() {
            let mut build_std_crates = HashSet::new();
            build_std_crates.insert("core");
            build_std_crates.insert("alloc");
            build_std_crates.insert("proc_macro");
            build_std_crates.insert("panic_unwind");
            build_std_crates.insert("compiler_builtins");
            build_std_crates.insert("std");
            build_std_crates.insert("test");
            build_std_crates.insert("panic_abort");

            for (name, artifacts) in artifacts
                .into_iter()
                .filter_map(|(_, artifacts)| artifacts.ok())
            {
                if build_std_crates.remove(name.as_str()) {
                    dependencies.push((format!("noprelude:{name}"), artifacts));
                }
            }
        }

        return Ok(Dependencies {
            dependencies,
            import_paths,
            import_libs,
        });
    }

    Err(Errored {
        command: "looking for json in cargo-metadata output".into(),
        errors: vec![],
        stderr: vec![],
        stdout: vec![],
    })
}

/// Build the dependencies.
#[derive(Debug, Clone)]
pub struct DependencyBuilder {
    /// Path to a `Cargo.toml` that describes which dependencies the tests can access.
    pub crate_manifest_path: PathBuf,
    /// The command to run can be changed from `cargo` to any custom command to build the
    /// dependencies in `crate_manifest_path`.
    pub program: CommandBuilder,
    /// Build with [`build-std`](https://doc.rust-lang.org/1.78.0/cargo/reference/unstable.html#build-std),
    /// which requires the nightly toolchain. The [`String`] can contain the standard library crates to build.
    pub build_std: Option<String>,
}

impl Default for DependencyBuilder {
    fn default() -> Self {
        Self {
            crate_manifest_path: PathBuf::from("Cargo.toml"),
            program: CommandBuilder::cargo(),
            build_std: None,
        }
    }
}

impl Flag for DependencyBuilder {
    fn must_be_unique(&self) -> bool {
        true
    }
    fn clone_inner(&self) -> Box<dyn Flag> {
        Box::new(self.clone())
    }
    fn apply(
        &self,
        cmd: &mut Command,
        config: &TestConfig<'_>,
        build_manager: &BuildManager<'_>,
    ) -> Result<(), Errored> {
        config
            .status
            .update_status("waiting for dependencies to finish building".into());
        let extra_args = build_manager.build(self.clone())?;
        cmd.args(extra_args);
        config.status.update_status(String::new());
        Ok(())
    }
}

impl Build for DependencyBuilder {
    fn build(&self, build_manager: &BuildManager<'_>) -> Result<Vec<OsString>, Errored> {
        build_dependencies(build_manager.config(), self)
    }

    fn description(&self) -> String {
        "Building dependencies".into()
    }
}

/// Compile dependencies and return the right flags
/// to find the dependencies.
pub fn build_dependencies(
    config: &Config,
    info: &DependencyBuilder,
) -> Result<Vec<OsString>, Errored> {
    let dependencies = build_dependencies_inner(config, info)?;
    let mut args = vec![];

    if info.build_std.is_some() {
        args.push("-Zunstable-options".into());
    }

    for (name, artifacts) in dependencies.dependencies {
        for dependency in artifacts {
            args.push("--extern".into());
            let mut dep = OsString::from(&name);
            dep.push("=");
            dep.push(dependency);
            args.push(dep);
        }
    }
    for import_path in dependencies.import_paths {
        args.push("-L".into());
        args.push(import_path.into());
    }
    for import_path in dependencies.import_libs {
        args.push("-l".into());
        args.push(import_path.into());
    }
    Ok(args)
}
