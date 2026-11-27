// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Compiler-override and `.cargo/config.toml` policy, hostile environments,
//! and evidence replacement under `--overwrite-artifacts`.

use super::*;

#[test]
fn rejects_compiler_overrides_in_source_root() {
    let staged = new_workspace("anneal-overrides-").stage().unwrap();
    let work = staged.work_dir();
    write_scalar_baseline(work);
    let lean_dir = work.join("lean");

    let base_manifest = "[package]\nname = \"ov\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
                         [lib]\npath = \"lib.rs\"\n";

    for (name, create) in [
        ("cargo-config-toml", Box::new(|p: &Path| {
            fs::create_dir_all(p.join(".cargo")).unwrap();
            fs::write(p.join(".cargo/config.toml"), "[build]\nrustflags = []\n").unwrap();
        }) as Box<dyn Fn(&Path)>),
        ("cargo-config", Box::new(|p: &Path| {
            fs::create_dir_all(p.join(".cargo")).unwrap();
            fs::write(p.join(".cargo/config"), "[build]\nrustflags = []\n").unwrap();
        })),
        ("rust-toolchain-toml", Box::new(|p: &Path| {
            fs::write(p.join("rust-toolchain.toml"), "[toolchain]\nchannel = \"nightly\"\n")
                .unwrap();
        })),
        ("rust-toolchain", Box::new(|p: &Path| {
            fs::write(p.join("rust-toolchain"), "nightly\n").unwrap();
        })),
        ("dot-cargo-file", Box::new(|p: &Path| {
            fs::write(p.join(".cargo"), "not a directory").unwrap();
        })),
        ("dot-cargo-symlink", Box::new(|p: &Path| {
            let target = p.join("outside-cargo-dir");
            fs::create_dir_all(&target).unwrap();
            symlink(&target, p.join(".cargo")).unwrap();
        })),
        ("cargo-config-cfg-target", Box::new(|p: &Path| {
            write_cargo_config(p, "[target.'cfg(all())']\nrustflags = [\"--cfg\", \"x\"]\n");
        })),
        ("cargo-config-target-linker", Box::new(|p: &Path| {
            write_cargo_config(p, "[target.x86_64-unknown-linux-gnu]\nlinker = \"/bin/false\"\n");
        })),
        ("cargo-config-env", Box::new(|p: &Path| {
            write_cargo_config(p, "[env]\nANNEAL_X = \"1\"\n");
        })),
        ("cargo-config-patch", Box::new(|p: &Path| {
            write_cargo_config(p, "[patch.crates-io]\nfoo = { path = \"foo\" }\n");
        })),
        ("cargo-config-net", Box::new(|p: &Path| {
            write_cargo_config(p, "[net]\noffline = true\n");
        })),
        ("cargo-config-top-level-key", Box::new(|p: &Path| {
            write_cargo_config(p, "build.rustc-wrapper = \"/bin/false\"\n");
        })),
        ("cargo-config-alias-then-build", Box::new(|p: &Path| {
            write_cargo_config(p, "[alias]\nb = \"build\"\n[build]\nrustflags = []\n");
        })),
        ("cargo-config-malformed", Box::new(|p: &Path| {
            write_cargo_config(p, "[alias\nb = \"build\"\n");
        })),
        ("cargo-config-symlink-to-benign", Box::new(|p: &Path| {
            fs::create_dir_all(p.join(".cargo")).unwrap();
            fs::write(p.join("benign.toml"), "[alias]\nb = \"build\"\n").unwrap();
            symlink(p.join("benign.toml"), p.join(".cargo/config.toml")).unwrap();
        })),
    ] {
        let pkg = work.join(format!("ov-{name}"));
        fs::create_dir_all(&pkg).unwrap();
        fs::write(pkg.join("Cargo.toml"), base_manifest).unwrap();
        fs::write(pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
        create(&pkg);
        let manifest = pkg.join("Cargo.toml");
        let inv = with_host_cargo_env(
            &staged,
            verify_invocation(&[
                OsStr::new("--manifest-path"),
                manifest.as_os_str(),
                OsStr::new("--proof-dir"),
                lean_dir.as_os_str(),
            ]),
        );
        let res = run_verify_inv(&staged, &inv);
        expect_failed(&res, 1, "unsupported", Some("cargo"), "compiler overrides");
    }
}

/// A passing run's receipt and exported `lean-lib/` never survive a later
/// failing `--overwrite-artifacts` run into the same directory.
#[test]
fn overwrite_artifacts_replaces_passing_evidence_on_later_failure() {
    let staged = new_workspace("anneal-overwrite-evidence-").stage().unwrap();
    let work = staged.work_dir();
    let good_dir = corpus_path("scalar_specs/annotated_id");
    let bad_dir = corpus_path("scalar_specs/wrong_id_returns_zero");
    let rust = work.join("rust");
    let lean = work.join("lean");
    fs::create_dir_all(&rust).unwrap();
    fs::create_dir_all(&lean).unwrap();
    fs::write(rust.join("lib.rs"), fs::read(good_dir.join("lib.rs")).unwrap()).unwrap();
    for name in ["Spec.lean", "Proof.lean"] {
        fs::write(lean.join(name), fs::read(good_dir.join(name)).unwrap()).unwrap();
    }
    let req = subcrate_request_json(&rust, "lib.rs", "annotated_id", &lean);
    let req_path = write_json_file(&work.join("req.json"), &req);
    let art = work.join("evidence");
    let first = run_verify_strs(
        &staged,
        &[
            "--request",
            req_path.to_str().unwrap(),
            "--artifacts",
            art.to_str().unwrap(),
            "--export-lean-lib",
        ],
    );
    expect_verified(&first, "crate_verified", true);
    assert!(art.join("result.json").is_file());
    assert!(art.join("lean-lib").is_dir());

    fs::write(rust.join("lib.rs"), fs::read(bad_dir.join("lib.rs")).unwrap()).unwrap();
    let second = run_verify_strs(
        &staged,
        &[
            "--request",
            req_path.to_str().unwrap(),
            "--artifacts",
            art.to_str().unwrap(),
            "--overwrite-artifacts",
        ],
    );
    expect_failed(&second, 1, "proof_failed", Some("audit"), "Proof.lean");
    assert!(!art.join("result.json").exists());
    assert!(!art.join("lean-lib").exists());
    assert!(art.join("capture/capture.json").is_file());
}

fn write_cargo_config(pkg: &Path, contents: &str) {
    fs::create_dir_all(pkg.join(".cargo")).unwrap();
    fs::write(pkg.join(".cargo/config.toml"), contents).unwrap();
}

/// Crates often ship a `.cargo/config.toml` holding only command aliases
/// (for example `[alias] nightly_docs = ...`). Such files cannot change the
/// compilation the shortcut reproduces, so verification proceeds.
#[test]
fn admits_benign_cargo_config_in_source_root() {
    let staged = new_workspace("anneal-benign-config-").stage().unwrap();
    let work = staged.work_dir();
    write_scalar_baseline(work);
    let lean_dir = work.join("lean");
    let pkg = work.join("benign");
    fs::create_dir_all(&pkg).unwrap();
    fs::write(
        pkg.join("Cargo.toml"),
        "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [lib]\npath = \"lib.rs\"\n",
    )
    .unwrap();
    fs::write(pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
    write_cargo_config(
        &pkg,
        "# Command shortcuts only.\n[alias]\n\
         nightly_docs = \"doc --no-deps -Zunstable-options -Zrustdoc-scrape-examples\"\n\
         xtask = [\"run\", \"--package\", \"xtask\", \"--\"]\n\n\
         [term]\ncolor = \"auto\"\n\n[doc]\nbrowser = \"firefox\"\n",
    );
    let manifest = pkg.join("Cargo.toml");
    let inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let res = run_verify_inv(&staged, &inv);
    expect_verified(&res, "crate_verified", true);
}

#[test]
fn verifies_under_hostile_environment_and_cargo_configs() {
    let staged = new_workspace("anneal-hostile-env-").stage().unwrap();
    let work = staged.work_dir();
    write_scalar_baseline(work);
    // Keep the subject package outside `work` (`cargo-anneal` cwd) so `work`
    // acts strictly as a hostile working directory rather than an ancestor of
    // the package's `workspace_root` (ancestor compiler overrides are tested
    // in `enforces_ancestor_and_cargo_home_compiler_override_policy`).
    let subject = staged.root_dir().join("subject");
    fs::create_dir_all(subject.join(".cargo")).unwrap();
    fs::write(
        subject.join("Cargo.toml"),
        "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [lib]\npath = \"lib.rs\"\n",
    )
    .unwrap();
    fs::write(subject.join("lib.rs"), SCALAR_SOURCE).unwrap();

    // Plant hostile `.cargo/config.toml` in `work` (`cargo-anneal` cwd) and
    // corrupt shared libraries under `LD_LIBRARY_PATH`.
    fs::create_dir_all(work.join(".cargo")).unwrap();
    fs::write(
        work.join(".cargo/config.toml"),
        "[build]\nrustc-wrapper = \"/bin/false\"\nrustflags = [\"--cfg\", \"evil\"]\n",
    )
    .unwrap();
    let evil_lib = work.join("evil-lib");
    fs::create_dir_all(&evil_lib).unwrap();
    for lib in ["libleanshared.so", "librustc_driver.so"] {
        fs::write(evil_lib.join(lib), b"not an ELF shared library").unwrap();
    }

    let manifest = subject.join("Cargo.toml");
    let lean_dir = work.join("lean");
    let inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    )
    .env("XDG_CACHE_HOME", work)
    .env("RUSTC", "/nonexistent/rustc")
    .env("RUSTC_WRAPPER", "/nonexistent/wrapper")
    .env("RUSTC_WORKSPACE_WRAPPER", "/nonexistent/ws-wrapper")
    .env("RUSTFLAGS", "--cfg=hostile")
    .env("CARGO_ENCODED_RUSTFLAGS", "--cfg=hostile")
    .env("RUSTC_LOG", "debug")
    .env("LD_LIBRARY_PATH", &evil_lib)
    .env("LEAN_PATH", work)
    .env("CARGO_TARGET_DIR", "/nonexistent/target");

    let res = run_verify_inv(&staged, &inv);
    let ok = expect_verified(&res, "crate_verified", true);
    assert_eq!(ok.audit["exactType"], true);
    assert!(ok.taint_reasons.is_empty(), "{ok:?}");
}

#[test]
fn enforces_ancestor_and_cargo_home_compiler_override_policy() {
    let staged = new_workspace("anneal-ce3-").stage().unwrap();
    let work = staged.work_dir();
    write_scalar_baseline(work);
    let lean_dir = work.join("lean");
    let base_manifest = "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
                         [lib]\npath = \"lib.rs\"\n";

    // (a) Ancestor above `workspace_root` with `[build]`, `[env]`,
    //     `rust-toolchain.toml`, or symlinked `.cargo` is rejected.
    for (case, setup, expected_reason) in [
        (
            "build-table",
            Box::new(|anc: &Path| {
                write_cargo_config(
                    anc,
                    "[build]\nrustflags = [\"--cfg\", \"ancestor_override\"]\n",
                );
            }) as Box<dyn Fn(&Path)>,
            "table [build]",
        ),
        (
            "env-table",
            Box::new(|anc: &Path| {
                write_cargo_config(anc, "[env]\nRUSTFLAGS = \"--cfg=evil\"\n");
            }),
            "table [env]",
        ),
        (
            "rust-toolchain-toml",
            Box::new(|anc: &Path| {
                fs::write(anc.join("rust-toolchain.toml"), "[toolchain]\nchannel = \"nightly\"\n")
                    .unwrap();
            }),
            "toolchain override",
        ),
        (
            "symlink-dot-cargo",
            Box::new(|anc: &Path| {
                let target = anc.join("real-cargo-dir");
                fs::create_dir_all(&target).unwrap();
                symlink(&target, anc.join(".cargo")).unwrap();
            }),
            "not a regular directory",
        ),
    ] {
        let ancestor_root = work.join(format!("ancestor-bad-{case}"));
        let ws = ancestor_root.join("ws");
        fs::create_dir_all(&ws).unwrap();
        setup(&ancestor_root);
        fs::write(ws.join("Cargo.toml"), base_manifest).unwrap();
        fs::write(ws.join("lib.rs"), SCALAR_SOURCE).unwrap();
        let ws_manifest = ws.join("Cargo.toml");
        let inv = with_host_cargo_env(
            &staged,
            verify_invocation(&[
                OsStr::new("--manifest-path"),
                ws_manifest.as_os_str(),
                OsStr::new("--proof-dir"),
                lean_dir.as_os_str(),
            ]),
        );
        let res = run_verify_inv(&staged, &inv);
        expect_failed(&res, 1, "unsupported", Some("cargo"), expected_reason);
    }

    // (b) `$CARGO_HOME/config.toml` with `[build]` or a symlink is rejected.
    let clean_pkg = work.join("clean-pkg");
    fs::create_dir_all(&clean_pkg).unwrap();
    fs::write(clean_pkg.join("Cargo.toml"), base_manifest).unwrap();
    fs::write(clean_pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
    let clean_manifest = clean_pkg.join("Cargo.toml");

    let bad_cargo_home = work.join("cargo-home-bad");
    fs::create_dir_all(&bad_cargo_home).unwrap();
    fs::write(bad_cargo_home.join("config.toml"), "[build]\nrustc-wrapper = \"/bin/false\"\n")
        .unwrap();
    let bad_home_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            clean_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    )
    .env("CARGO_HOME", &bad_cargo_home);
    let bad_home_res = run_verify_inv(&staged, &bad_home_inv);
    expect_failed(&bad_home_res, 1, "unsupported", Some("cargo"), "table [build]");

    let sym_cargo_home = work.join("cargo-home-symlink");
    fs::create_dir_all(&sym_cargo_home).unwrap();
    fs::write(sym_cargo_home.join("real.toml"), "[net]\noffline = true\n").unwrap();
    symlink(sym_cargo_home.join("real.toml"), sym_cargo_home.join("config.toml")).unwrap();
    let sym_home_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            clean_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    )
    .env("CARGO_HOME", &sym_cargo_home);
    let sym_home_res = run_verify_inv(&staged, &sym_home_inv);
    expect_failed(&sym_home_res, 1, "unsupported", Some("cargo"), "symlink");

    // (c) `CargoConfigPolicy::InWorkspace` vs `CargoConfigPolicy::AmbientHost`:
    //     `[net]`/`[registries]`/`[source]` inside `workspace_root` on a
    //     workspace member crate is REJECTED (`InWorkspace`), while the exact
    //     same config in an ancestor strictly above `workspace_root` and in
    //     `$CARGO_HOME/config.toml` is ALLOWED (`AmbientHost`).
    let benign_toml = "[net]\ngit-fetch-with-cli = true\nretry = 3\n\n\
                       [registries.example]\nindex = \"sparse+https://example.invalid/index/\"\n\n\
                       [source.crates-io]\nreplace-with = \"vendored-sources\"\n\n\
                       [source.vendored-sources]\ndirectory = \"/nonexistent/vendor\"\n";

    let ws_in_workspace = work.join("ws-net-rejected");
    fs::create_dir_all(ws_in_workspace.join("member")).unwrap();
    fs::write(
        ws_in_workspace.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    write_cargo_config(&ws_in_workspace, benign_toml);
    fs::write(ws_in_workspace.join("member/Cargo.toml"), base_manifest).unwrap();
    fs::write(ws_in_workspace.join("member/lib.rs"), SCALAR_SOURCE).unwrap();
    let ws_member_manifest = ws_in_workspace.join("member/Cargo.toml");
    let in_ws_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            ws_member_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let in_ws_res = run_verify_inv(&staged, &in_ws_inv);
    expect_failed(&in_ws_res, 1, "unsupported", Some("cargo"), "table [net]");

    let benign_cargo_home = work.join("cargo-home-benign");
    fs::create_dir_all(&benign_cargo_home).unwrap();
    fs::write(benign_cargo_home.join("config.toml"), benign_toml).unwrap();

    let benign_ancestor = work.join("ancestor-benign");
    let benign_pkg = benign_ancestor.join("pkg");
    fs::create_dir_all(benign_ancestor.join(".cargo")).unwrap();
    fs::create_dir_all(&benign_pkg).unwrap();
    fs::write(benign_ancestor.join(".cargo/config.toml"), benign_toml).unwrap();
    fs::write(benign_pkg.join("Cargo.toml"), base_manifest).unwrap();
    fs::write(benign_pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
    let benign_manifest = benign_pkg.join("Cargo.toml");

    let benign_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            benign_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    )
    .env("CARGO_HOME", &benign_cargo_home);
    let benign_res = run_verify_inv(&staged, &benign_inv);
    expect_verified(&benign_res, "crate_verified", true);
}
