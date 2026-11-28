// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path};

use super::{files::ensure_non_symlink_dir, *};

#[test]
fn cargo_mode_requires_package_manifest_and_creates_proof_files_once() {
    let dir = tempfile::tempdir().unwrap();
    let err = run(InitArgs {
        manifest_path: Some(dir.path().join("Cargo.toml")),
        proof_dir: Some(dir.path().join("proof")),
        select: None,
        standalone: false,
        profile: InitProfile::V1,
    })
    .unwrap_err();
    assert!(err.contains("no Cargo.toml found"), "{err}");

    fs::write(
        dir.path().join("Cargo.toml"),
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    let proof_dir = dir.path().join("proof");
    let ok = run(InitArgs {
        manifest_path: Some(dir.path().join("Cargo.toml")),
        proof_dir: Some(proof_dir.clone()),
        select: Some("zero".into()),
        standalone: false,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(ok.contains("--select zero"), "{ok}");
    assert!(proof_dir.join("Spec.lean").is_file());
    assert!(proof_dir.join("Proof.lean").is_file());

    let second = run(InitArgs {
        manifest_path: Some(dir.path().join("Cargo.toml")),
        proof_dir: Some(proof_dir),
        select: None,
        standalone: false,
        profile: InitProfile::V1,
    })
    .unwrap_err();
    assert!(second.contains("refusing to overwrite existing file"), "{second}");
}

#[test]
fn standalone_mode_scaffolds_runnable_example_and_refuses_symlinks() {
    let dir = tempfile::tempdir().unwrap();
    let out_dir = dir.path().join("hello");
    let summary = run(InitArgs {
        manifest_path: None,
        proof_dir: Some(out_dir.clone()),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(summary.contains("verify --request"), "{summary}");
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(out_dir.join(name).is_file(), "missing {name}");
    }

    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("Spec.lean"), b"-- keep\n").unwrap();
        let link_dir = dir.path().join("link-proof");
        symlink(outside.path(), &link_dir).unwrap();
        for spelling in [
            link_dir.clone(),
            PathBuf::from(format!("{}/", link_dir.display())),
            link_dir.join("."),
        ] {
            let err = run(InitArgs {
                manifest_path: None,
                proof_dir: Some(spelling),
                select: None,
                standalone: true,
                profile: InitProfile::V1,
            })
            .unwrap_err();
            assert!(err.contains("symlink"), "{err}");
        }
        assert_eq!(fs::read(outside.path().join("Spec.lean")).unwrap(), b"-- keep\n");
        assert!(!outside.path().join("Proof.lean").exists());
    }
}

#[test]
fn strip_license_header_handles_comment_blocks_and_preserves_unheaded_text() {
    assert_eq!(
        strip_license_header("// Copyright 2026 Author\n//\n// body\n\npub fn f() {}\n", "//"),
        "pub fn f() {}\n"
    );
    assert_eq!(strip_license_header("-- Copyright 2026 Author\n--\n\nmodule\n", "--"), "module\n");
    assert_eq!(
        strip_license_header("// Copyright 2026 Author\n\n\npub fn f() {}\n", "//"),
        "\npub fn f() {}\n"
    );
    assert_eq!(
        strip_license_header("// Copyright 2026 Author\r\n// line\r\n\r\nbody\r\n", "//"),
        "body\r\n"
    );
    assert_eq!(
        strip_license_header("// Copyright 2026 Author\npub fn f() {}\n", "//"),
        "pub fn f() {}\n"
    );
    assert_eq!(strip_license_header("// Copyright 2026 Author", "//"), "");
    assert_eq!(strip_license_header(STANDALONE_REQUEST_JSON, "//"), STANDALONE_REQUEST_JSON);
    assert_eq!(
        strip_license_header("// Licensed only\n\ncode\n", "//"),
        "// Licensed only\n\ncode\n"
    );
    assert_eq!(strip_license_header("// Copyrighted\n\ncode\n", "//"), "// Copyrighted\n\ncode\n");
    assert_eq!(strip_license_header("// Copyright\n\ncode\n", "//"), "// Copyright\n\ncode\n");
    assert_eq!(strip_license_header("", "//"), "");
    assert_eq!(strip_license_header(" Copyright 2026\n\ncode\n", ""), " Copyright 2026\n\ncode\n");
}

#[test]
fn standalone_scaffolds_match_assets_without_license_headers() {
    let dir = tempfile::tempdir().unwrap();
    let out_dir = dir.path().join("scalar");
    run(InitArgs {
        manifest_path: None,
        proof_dir: Some(out_dir.clone()),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();

    let lib_rs = fs::read_to_string(out_dir.join("lib.rs")).unwrap();
    let request_json = fs::read_to_string(out_dir.join("request.json")).unwrap();
    let spec_lean = fs::read_to_string(out_dir.join("Spec.lean")).unwrap();
    let proof_lean = fs::read_to_string(out_dir.join("Proof.lean")).unwrap();

    assert!(lib_rs.starts_with("pub fn zero()"), "{lib_rs}");
    assert!(request_json.starts_with('{'), "{request_json}");
    assert!(spec_lean.starts_with("module\n"), "{spec_lean}");
    assert!(proof_lean.starts_with("module\n"), "{proof_lean}");

    for (name, generated) in
        [("lib.rs", &lib_rs), ("Spec.lean", &spec_lean), ("Proof.lean", &proof_lean)]
    {
        assert!(!generated.contains("Copyright"), "{name} retained copyright header");
        assert!(!generated.contains("Licensed under"), "{name} retained license header");
    }

    let (lib_header, lib_body) =
        include_str!("../../assets/scalar/lib.rs").split_once("\n\n").unwrap();
    assert!(lib_header.starts_with("// Copyright "));
    assert_eq!(lib_rs, lib_body);

    assert_eq!(request_json, include_str!("../../assets/scalar/request.json"));

    let (spec_header, spec_body) =
        include_str!("../../assets/scalar/Spec.lean").split_once("\n\n").unwrap();
    assert!(spec_header.starts_with("-- Copyright "));
    assert_eq!(spec_lean, spec_body);

    let (proof_header, proof_body) =
        include_str!("../../assets/scalar/Proof.lean").split_once("\n\n").unwrap();
    assert!(proof_header.starts_with("-- Copyright "));
    assert_eq!(proof_lean, proof_body);
}

#[test]
fn ensure_non_symlink_dir_handles_existing_root_dot_and_empty_paths() {
    let dir = tempfile::tempdir().unwrap();
    let existing = dir.path().join("existing");
    fs::create_dir(&existing).unwrap();
    ensure_non_symlink_dir(&existing).unwrap();
    ensure_non_symlink_dir(Path::new(&format!("{}/", existing.display()))).unwrap();

    ensure_non_symlink_dir(Path::new(".")).unwrap();
    ensure_non_symlink_dir(Path::new("./")).unwrap();
    ensure_non_symlink_dir(Path::new("/")).unwrap();

    let empty_err = ensure_non_symlink_dir(Path::new("")).unwrap_err();
    assert!(empty_err.contains("empty"), "{empty_err}");

    for parent_ref in [Path::new(".."), Path::new("../"), Path::new("../.")] {
        let err = ensure_non_symlink_dir(parent_ref).unwrap_err();
        assert!(err.contains("'..'"), "{err}");
    }
    let missing_parent_ref = dir.path().join("missing-before-parent/..");
    let missing_parent_err = ensure_non_symlink_dir(&missing_parent_ref).unwrap_err();
    assert!(missing_parent_err.contains("'..'"), "{missing_parent_err}");
    assert!(!dir.path().join("missing-before-parent").exists());

    let regular_file = dir.path().join("regular");
    fs::write(&regular_file, b"file").unwrap();
    let file_err = ensure_non_symlink_dir(&regular_file).unwrap_err();
    assert!(file_err.contains("non-directory"), "{file_err}");
    let under_file_err = ensure_non_symlink_dir(&regular_file.join("proof")).unwrap_err();
    assert!(under_file_err.contains("non-directory"), "{under_file_err}");
    assert!(!dir.path().join("regular/proof").exists());
}

#[cfg(unix)]
#[test]
fn allows_symlinked_ancestors_while_rejecting_symlink_destinations_and_broken_ancestors() {
    use std::os::unix::fs::symlink;

    let dir = tempfile::tempdir().unwrap();
    let real_root = dir.path().join("private-tmp");
    fs::create_dir(&real_root).unwrap();
    let symlink_parent = dir.path().join("tmp-link");
    symlink(&real_root, &symlink_parent).unwrap();

    // Pre-existing symlinked ancestor (like macOS `/tmp -> private/tmp`)
    // succeeds for nested new directories and existing real subdirectories.
    let nested = symlink_parent.join("nested").join("proof");
    run(InitArgs {
        manifest_path: None,
        proof_dir: Some(nested),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(real_root.join("nested/proof").join(name).is_file(), "missing {name}");
    }

    let existing_sub = real_root.join("existing-dir");
    fs::create_dir(&existing_sub).unwrap();
    run(InitArgs {
        manifest_path: None,
        proof_dir: Some(symlink_parent.join("existing-dir")),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(existing_sub.join("Proof.lean").is_file());

    // Cargo mode under a pre-existing symlinked ancestor also succeeds.
    let crate_real = real_root.join("crate-demo");
    fs::create_dir(&crate_real).unwrap();
    fs::write(
        crate_real.join("Cargo.toml"),
        "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    run(InitArgs {
        manifest_path: Some(symlink_parent.join("crate-demo/Cargo.toml")),
        proof_dir: None,
        select: None,
        standalone: false,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(crate_real.join("proof/Spec.lean").is_file());
    assert!(crate_real.join("proof/Proof.lean").is_file());

    // Dangling symlink destination (with and without trailing `/`) is
    // refused.
    let dangling = dir.path().join("dangling");
    symlink(dir.path().join("absent-target"), &dangling).unwrap();
    for spelling in [dangling.clone(), PathBuf::from(format!("{}/", dangling.display()))] {
        let err = ensure_non_symlink_dir(&spelling).unwrap_err();
        assert!(err.contains("symlink"), "{err}");
    }

    // Dangling symlink ancestor is refused cleanly without creating
    // anything.
    let dangling_child = dangling.join("proof");
    let dangling_err = run(InitArgs {
        manifest_path: None,
        proof_dir: Some(dangling_child),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap_err();
    assert!(dangling_err.contains("cannot inspect symlink directory ancestor"), "{dangling_err}");
    assert!(!dir.path().join("absent-target").exists());

    // Symlinked ancestor targeting a regular file is refused cleanly.
    let regular_file = dir.path().join("file");
    fs::write(&regular_file, b"data").unwrap();
    let file_link = dir.path().join("file-link");
    symlink(&regular_file, &file_link).unwrap();
    let file_link_err = ensure_non_symlink_dir(&file_link.join("proof")).unwrap_err();
    assert!(file_link_err.contains("non-directory"), "{file_link_err}");

    // Symlink loop ancestor is refused cleanly.
    let loop_a = dir.path().join("loop-a");
    let loop_b = dir.path().join("loop-b");
    symlink(&loop_b, &loop_a).unwrap();
    symlink(&loop_a, &loop_b).unwrap();
    let loop_err = ensure_non_symlink_dir(&loop_a.join("proof")).unwrap_err();
    assert!(loop_err.contains("cannot inspect symlink directory ancestor"), "{loop_err}");

    // Paths whose final non-`.` component is `..` are refused, including
    // through symlinked ancestors or trailing separators.
    for parent_spelling in [
        symlink_parent.join(".."),
        PathBuf::from(format!("{}/../", symlink_parent.display())),
        symlink_parent.join("../."),
        real_root.join(".."),
    ] {
        let err = run(InitArgs {
            manifest_path: None,
            proof_dir: Some(parent_spelling),
            select: None,
            standalone: true,
            profile: InitProfile::V1,
        })
        .unwrap_err();
        assert!(err.contains("'..'"), "{err}");
    }
}

#[test]
fn relative_paths_subprocess_helper() {
    let Some(expected_dir) = std::env::var_os("ANNEAL_INIT_SUBPROCESS_DIR") else {
        return;
    };
    assert_eq!(
        fs::canonicalize(std::env::current_dir().unwrap()).unwrap(),
        fs::canonicalize(expected_dir).unwrap()
    );

    let dot_out = run(InitArgs {
        manifest_path: None,
        proof_dir: None,
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(dot_out.contains("verify --request ./request.json"), "{dot_out}");
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(Path::new(name).is_file(), "missing {name} in '.'");
    }

    let nested_out = run(InitArgs {
        manifest_path: None,
        proof_dir: Some(PathBuf::from("a/b/c")),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(nested_out.contains("verify --request a/b/c/request.json"), "{nested_out}");
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(Path::new("a/b/c").join(name).is_file(), "missing {name} in a/b/c");
    }

    let parent_sibling_out = run(InitArgs {
        manifest_path: None,
        proof_dir: Some(PathBuf::from("../proof")),
        select: None,
        standalone: true,
        profile: InitProfile::V1,
    })
    .unwrap();
    assert!(
        parent_sibling_out.contains("verify --request ../proof/request.json"),
        "{parent_sibling_out}"
    );
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(Path::new("../proof").join(name).is_file(), "missing {name} in ../proof");
    }
}

#[test]
fn standalone_accepts_dot_and_relative_nested_paths_in_isolated_cwd() {
    let dir = tempfile::tempdir().unwrap();
    let subdir = dir.path().join("sub");
    fs::create_dir(&subdir).unwrap();
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "init::tests::relative_paths_subprocess_helper"])
        .env("ANNEAL_INIT_SUBPROCESS_DIR", &subdir)
        .current_dir(&subdir)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "subprocess failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
        assert!(subdir.join(name).is_file(), "missing {name} in '.'");
        assert!(subdir.join("a/b/c").join(name).is_file(), "missing {name} in a/b/c");
        assert!(dir.path().join("proof").join(name).is_file(), "missing {name} in ../proof");
    }
}

#[test]
fn rejects_virtual_workspace_manifest() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("Cargo.toml"), "[workspace]\nmembers = [\"crates/a\"]\n").unwrap();
    let err = run(InitArgs {
        manifest_path: Some(dir.path().join("Cargo.toml")),
        proof_dir: Some(dir.path().join("proof")),
        select: None,
        standalone: false,
        profile: InitProfile::V1,
    })
    .unwrap_err();
    assert!(err.contains("virtual workspace"), "{err}");
}

fn write_demo_manifest(dir: &Path) -> PathBuf {
    let manifest = dir.join("Cargo.toml");
    fs::write(&manifest, "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n")
        .unwrap();
    manifest
}

#[derive(clap::Parser)]
struct InitCli {
    #[command(flatten)]
    args: InitArgs,
}

fn parse_init(argv: &[&str]) -> Result<InitArgs, clap::Error> {
    use clap::Parser;
    InitCli::try_parse_from(std::iter::once("init").chain(argv.iter().copied())).map(|cli| cli.args)
}

#[test]
fn default_profile_is_v1_and_output_is_unchanged() {
    let parsed = parse_init(&[]).unwrap();
    assert_eq!(parsed.profile, InitProfile::V1);
    assert_eq!(parse_init(&["--profile", "v1"]).unwrap().profile, InitProfile::V1);

    let dir = tempfile::tempdir().unwrap();
    let manifest = write_demo_manifest(dir.path());
    let proof_dir = dir.path().join("proof");
    let summary = run(InitArgs {
        manifest_path: Some(manifest.clone()),
        proof_dir: Some(proof_dir.clone()),
        select: None,
        standalone: false,
        profile: parsed.profile,
    })
    .unwrap();
    assert_eq!(
        summary,
        format!(
            "Initialized Anneal proof files:\n  {}\n  {}\n\nNext step:\n  Edit Spec.lean and \
             Proof.lean, then run:\n  cargo anneal verify --manifest-path {} --proof-dir {}\n",
            proof_dir.join("Spec.lean").display(),
            proof_dir.join("Proof.lean").display(),
            manifest.display(),
            proof_dir.display()
        )
    );
    let spec = fs::read_to_string(proof_dir.join("Spec.lean")).unwrap();
    let proof = fs::read_to_string(proof_dir.join("Proof.lean")).unwrap();
    assert_eq!(spec, cargo_spec_lean());
    assert_eq!(proof, cargo_proof_lean());
    assert!(spec.contains("def specs : Specs where\n"), "{spec}");
    assert!(!spec.contains("SpecsV2"), "{spec}");
}

#[test]
fn profile_v2_scaffolds_specs_v2_starter() {
    let parsed = parse_init(&["--profile", "v2"]).unwrap();
    assert_eq!(parsed.profile, InitProfile::V2);

    let dir = tempfile::tempdir().unwrap();
    let manifest = write_demo_manifest(dir.path());
    let proof_dir = dir.path().join("proof");
    let summary = run(InitArgs {
        manifest_path: Some(manifest),
        proof_dir: Some(proof_dir.clone()),
        select: Some("load".into()),
        standalone: false,
        profile: parsed.profile,
    })
    .unwrap();
    assert!(summary.contains("--select load\n"), "{summary}");
    assert!(summary.contains("mir_profile_version = 2"), "{summary}");

    let spec = fs::read_to_string(proof_dir.join("Spec.lean")).unwrap();
    let proof = fs::read_to_string(proof_dir.join("Proof.lean")).unwrap();
    assert_eq!(spec, cargo_spec_lean_v2());
    assert_eq!(proof, cargo_proof_lean_v2());
    assert!(spec.starts_with("module\nprelude\npublic import Trusted.MirSemantics\n"));
    assert!(spec.contains("def specs : SpecsV2 where\n"), "{spec}");
    assert!(spec.contains("  safety := fun _ _ => True\n"), "{spec}");
    assert!(spec.contains("  property := fun _ => True\n"), "{spec}");
    assert!(!spec.contains("sorry") && !spec.contains("import Anneal"), "{spec}");
    assert!(proof.starts_with("module\nprelude\npublic import Expected\n"));
    assert!(proof.contains("public theorem verify : Expected.claim := by\n"), "{proof}");
    assert!(proof.contains("UnitTheoremV2") && proof.contains("BodyVerifiedV2"), "{proof}");
}

#[test]
fn profile_conflicts_with_standalone_and_rejects_unknown_values() {
    let err = parse_init(&["--standalone", "--profile", "v2"]).err().unwrap();
    assert_eq!(err.kind(), clap::error::ErrorKind::ArgumentConflict, "{err}");
    let err = parse_init(&["--profile", "v3"]).err().unwrap();
    assert_eq!(err.kind(), clap::error::ErrorKind::InvalidValue, "{err}");
    // The default value alone does not trigger the conflict.
    assert!(parse_init(&["--standalone"]).unwrap().standalone);
}
