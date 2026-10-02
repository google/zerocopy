// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[cfg(feature = "exocrate_tests")]
fn cargo_anneal_bin_path() -> std::path::PathBuf {
    std::env::var("CARGO_BIN_EXE_cargo-anneal")
        .or_else(|_| std::env::var("CARGO_BIN_EXE_cargo_anneal"))
        .expect("CARGO_BIN_EXE_* not set")
        .into()
}

#[cfg(feature = "exocrate_tests")]
fn cargo_anneal_command(bin_path: &std::path::Path) -> std::process::Command {
    let mut cmd = std::process::Command::new(bin_path);
    cmd.env_clear()
        .env("__ANNEAL_LOCAL_DEV", "1")
        .env("CARGO_MANIFEST_DIR", env!("CARGO_MANIFEST_DIR"));
    cmd
}

#[cfg(feature = "exocrate_tests")]
fn ensure_test_toolchain(bin_path: &std::path::Path) {
    static SETUP_RESULT: std::sync::OnceLock<Result<(), String>> = std::sync::OnceLock::new();

    let result = SETUP_RESULT.get_or_init(|| {
        let manifest_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        let mut cmd = cargo_anneal_command(bin_path);
        let output = cmd
            .arg("setup")
            .arg("--local-archive")
            .arg(manifest_dir.join("target/anneal-exocrate.tar.zst"))
            .output()
            .map_err(|err| format!("failed to execute cargo-anneal setup: {err}"))?;

        if output.status.success() {
            return Ok(());
        }

        Err(format!(
            "cargo-anneal setup failed\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ))
    });

    if let Err(err) = result {
        panic!("{err}");
    }
}

#[cfg(feature = "exocrate_tests")]
#[test]
fn test_generate_subcommand_simple() {
    let temp_dir = tempfile::tempdir().unwrap();
    let project_dir = temp_dir.path().join("project");
    let output_dir = temp_dir.path().join("llbc_out");
    std::fs::create_dir_all(project_dir.join("examples")).unwrap();
    std::fs::write(
        project_dir.join("Cargo.toml"),
        r#"
            [package]
            name = "test_proj"
            version = "0.1.0"
            edition = "2021"

            [[example]]
            name = "simple"
            path = "examples/simple.rs"
        "#,
    )
    .unwrap();
    std::fs::write(
        project_dir.join("examples").join("simple.rs"),
        r#"
            pub fn add(left: usize, right: usize) -> usize {
                left + right
            }

            fn main() {
                println!("Hello, world! {}", add(1, 2));
            }
        "#,
    )
    .unwrap();

    let bin_path = cargo_anneal_bin_path();
    ensure_test_toolchain(&bin_path);

    let mut cmd = cargo_anneal_command(&bin_path);
    if let Some(path) = std::env::var_os("PATH") {
        cmd.env("PATH", path);
    }
    cmd.arg("generate")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .arg("--example")
        .arg("simple")
        .arg("--output-dir")
        .arg(&output_dir);
    cmd.arg("--no-progress");

    let output = cmd.output().expect("failed to execute cargo-anneal");

    println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
    println!("stderr: {}", String::from_utf8_lossy(&output.stderr));

    assert!(output.status.success(), "cargo-anneal failed");

    let mut found_llbc = false;
    if output_dir.exists() {
        for entry in std::fs::read_dir(&output_dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "llbc") {
                found_llbc = true;
                break;
            }
        }
    }

    assert!(found_llbc, "No .llbc file found in output directory {:?}", output_dir);
}

#[cfg(feature = "exocrate_tests")]
#[test]
fn test_generate_multi_crate_type_library_once() {
    let temp_dir = tempfile::tempdir().unwrap();
    let project_dir = temp_dir.path().join("project");
    let output_dir = temp_dir.path().join("llbc_out");
    std::fs::create_dir_all(project_dir.join("src")).unwrap();
    std::fs::write(
        project_dir.join("Cargo.toml"),
        r#"
            [package]
            name = "multi_crate_type"
            version = "0.1.0"
            edition = "2021"

            [lib]
            crate-type = ["rlib", "cdylib"]
        "#,
    )
    .unwrap();
    std::fs::write(
        project_dir.join("src/lib.rs"),
        r#"
            pub fn shared() {}
        "#,
    )
    .unwrap();

    let bin_path = cargo_anneal_bin_path();
    ensure_test_toolchain(&bin_path);

    let mut cmd = cargo_anneal_command(&bin_path);
    if let Some(path) = std::env::var_os("PATH") {
        cmd.env("PATH", path);
    }
    cmd.arg("generate")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .arg("--lib")
        .arg("--output-dir")
        .arg(&output_dir)
        .arg("--no-progress");

    let output = cmd.output().expect("failed to execute cargo-anneal");

    println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
    println!("stderr: {}", String::from_utf8_lossy(&output.stderr));

    assert!(output.status.success(), "cargo-anneal failed");

    let mut llbc_files: Vec<_> = std::fs::read_dir(&output_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.is_file() && path.extension().is_some_and(|ext| ext == "llbc"))
        .collect();
    llbc_files.sort();
    assert_eq!(
        llbc_files.len(),
        1,
        "one Cargo library target should produce one Charon translation; got {llbc_files:#?}"
    );

    let llbc = std::fs::read_to_string(&llbc_files[0]).unwrap();
    assert!(llbc.contains("shared"), "generated LLBC did not contain the library function");
}

#[cfg(feature = "exocrate_tests")]
#[test]
fn test_generate_preserves_cargo_build_environment() {
    let temp_dir = tempfile::tempdir().unwrap();
    let project_dir = temp_dir.path().join("project");
    let output_dir = temp_dir.path().join("llbc_out");
    std::fs::create_dir_all(project_dir.join("src")).unwrap();
    std::fs::write(
        project_dir.join("Cargo.toml"),
        r#"
            [package]
            name = "configured_build"
            version = "0.1.0"
            edition = "2021"

            [lints.rust]
            unexpected_cfgs = { level = "warn", check-cfg = ["cfg(anneal_env_test)"] }
        "#,
    )
    .unwrap();
    std::fs::write(
        project_dir.join("src/lib.rs"),
        r#"
            #[cfg(not(anneal_env_test))]
            compile_error!("RUSTFLAGS was not preserved for Charon's Cargo build");

            #[cfg(anneal_env_test)]
            pub fn configured_build() {}
        "#,
    )
    .unwrap();

    let bin_path = cargo_anneal_bin_path();
    ensure_test_toolchain(&bin_path);

    let mut cmd = cargo_anneal_command(&bin_path);
    if let Some(path) = std::env::var_os("PATH") {
        cmd.env("PATH", path);
    }
    cmd.env("RUSTFLAGS", "--cfg=anneal_env_test")
        .arg("generate")
        .arg("--manifest-path")
        .arg(project_dir.join("Cargo.toml"))
        .arg("--lib")
        .arg("--output-dir")
        .arg(&output_dir)
        .arg("--no-progress");

    let output = cmd.output().expect("failed to execute cargo-anneal");
    println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
    println!("stderr: {}", String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success(), "cargo-anneal failed");

    let llbc_file = std::fs::read_dir(&output_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .find(|path| path.extension().is_some_and(|ext| ext == "llbc"))
        .expect("no LLBC file generated");
    let llbc = std::fs::read_to_string(llbc_file).unwrap();
    assert!(llbc.contains("configured_build"), "generated LLBC omitted cfg-enabled code");
}

#[cfg(feature = "exocrate_tests")]
#[test]
fn test_generate_honors_workspace_default_members() {
    let temp_dir = tempfile::tempdir().unwrap();
    let workspace_dir = temp_dir.path().join("workspace");
    let default_output_dir = temp_dir.path().join("default_llbc");
    let workspace_output_dir = temp_dir.path().join("workspace_llbc");
    for member in ["default_member", "other_member"] {
        std::fs::create_dir_all(workspace_dir.join(member).join("src")).unwrap();
        std::fs::write(
            workspace_dir.join(member).join("Cargo.toml"),
            format!(
                r#"
                    [package]
                    name = "{member}"
                    version = "0.1.0"
                    edition = "2021"
                "#
            ),
        )
        .unwrap();
        std::fs::write(
            workspace_dir.join(member).join("src/lib.rs"),
            format!("pub fn {member}_fn() {{}}\n"),
        )
        .unwrap();
    }
    std::fs::write(
        workspace_dir.join("Cargo.toml"),
        r#"
            [workspace]
            members = ["default_member", "other_member"]
            default-members = ["default_member"]
            resolver = "2"
        "#,
    )
    .unwrap();

    let bin_path = cargo_anneal_bin_path();
    ensure_test_toolchain(&bin_path);

    let generate = |output_dir: &std::path::Path, workspace: bool| {
        let mut cmd = cargo_anneal_command(&bin_path);
        if let Some(path) = std::env::var_os("PATH") {
            cmd.env("PATH", path);
        }
        cmd.arg("generate")
            .arg("--manifest-path")
            .arg(workspace_dir.join("Cargo.toml"))
            .arg("--output-dir")
            .arg(output_dir)
            .arg("--no-progress");
        if workspace {
            cmd.arg("--workspace");
        }
        let output = cmd.output().expect("failed to execute cargo-anneal");
        println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
        println!("stderr: {}", String::from_utf8_lossy(&output.stderr));
        assert!(output.status.success(), "cargo-anneal failed");

        let mut llbc: Vec<_> = std::fs::read_dir(output_dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "llbc"))
            .map(|path| std::fs::read_to_string(path).unwrap())
            .collect();
        llbc.sort();
        llbc
    };

    let default_llbc = generate(&default_output_dir, false);
    assert_eq!(default_llbc.len(), 1, "default selection should translate one member");
    assert!(default_llbc[0].contains("default_member_fn"));
    assert!(!default_llbc[0].contains("other_member_fn"));

    let workspace_llbc = generate(&workspace_output_dir, true);
    assert_eq!(workspace_llbc.len(), 2, "--workspace should translate every member");
    let workspace_llbc = workspace_llbc.concat();
    assert!(workspace_llbc.contains("default_member_fn"));
    assert!(workspace_llbc.contains("other_member_fn"));
}
