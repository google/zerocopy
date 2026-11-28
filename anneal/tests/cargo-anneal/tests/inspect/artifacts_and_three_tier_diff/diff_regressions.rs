// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Three-tier `--diff` regressions, malformed digests, symlinked artifact
//! roots, unrecognized fields, and invariant violations.

use super::*;

/// Runs the sections of `verify_artifacts_and_three_tier_diff_enforced`
/// that the module documentation lists.
pub(super) fn diff_flags_regressions_and_bad_inputs(
    tmp: &tempfile::TempDir,
    art_dir: PathBuf,
    clean: Value,
    clean_path: PathBuf,
) {
    // 3-tier --diff: Tier A downgrade fails --no-regressions; Tier C passes.
    let mut head_downgrade = clean.clone();
    head_downgrade["status"] = json!("tainted_crate_verified");
    head_downgrade["taint_reasons"] = json!(["unsandboxed_elaboration"]);
    head_downgrade["elaboration_sandbox"] = json!("none");
    head_downgrade["deferred"] = json!(["hostile Lean elaborator effects"]);
    let head_down_path = tmp.path().join("head_down.json");
    fs::write(&head_down_path, serde_json::to_vec(&head_downgrade).unwrap()).unwrap();

    let reg_fail = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_down_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(reg_fail.status.code(), Some(1));
    let diff_json: Value = serde_json::from_slice(&reg_fail.stdout).unwrap();
    assert_eq!(diff_json["has_regressions"], true);

    let mut head_timing = clean.clone();
    head_timing["timing_ms"]["total"] = json!(99);
    let head_timing_path = tmp.path().join("head_timing.json");
    fs::write(&head_timing_path, serde_json::to_vec(&head_timing).unwrap()).unwrap();
    let timing_ok = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_timing_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(timing_ok.status.code(), Some(0));

    // Added assumption / deferred / newly-experimental regressions fail
    // `--no-regressions`, whereas taint removal (improvement) exits 0.
    let mut head_assump = clean.clone();
    head_assump["assumptions"] = json!(["Rust MIR semantics", "extra"]);
    let head_assump_path = tmp.path().join("head_assump.json");
    fs::write(&head_assump_path, serde_json::to_vec(&head_assump).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                clean_path.to_str().unwrap(),
                head_assump_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(1)
    );
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                head_down_path.to_str().unwrap(),
                clean_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(0)
    );

    // Missing base `horizon` (unbounded) followed by bounded head fails
    // `--no-regressions`.
    let mut head_bounded = clean.clone();
    head_bounded["horizon"] = json!({"kind": "bounded", "k": 8});
    let head_bounded_path = tmp.path().join("head_bounded.json");
    fs::write(&head_bounded_path, serde_json::to_vec(&head_bounded).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                clean_path.to_str().unwrap(),
                head_bounded_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None,
        )
        .status
        .code(),
        Some(1)
    );

    // Multibyte UTF-8 at byte 12 + ANSI/bidi in digest must never panic.
    let mut bad_digest = clean.clone();
    bad_digest["request_sha256"] = json!("0123456789\u{00E9}\x1b[31m\u{206A}\u{3164}");
    let bad_digest_path = tmp.path().join("bad_digest.json");
    fs::write(&bad_digest_path, serde_json::to_vec(&bad_digest).unwrap()).unwrap();
    for fmt in ["human", "ledger", "markdown"] {
        let out =
            run_inspect(&[bad_digest_path.to_str().unwrap(), "--format", fmt, "--passive"], None);
        assert_eq!(out.status.code(), Some(1), "fmt={fmt}");
        let s = String::from_utf8(out.stdout).unwrap();
        assert!(!s.contains('\x1b'));
        assert!(!s.contains('\u{206A}'));
        assert!(!s.contains('\u{3164}'));
    }

    // `configuration.stdlib_crate` ("core") passes `--unknown-fields deny`.
    let mut stdlib_core = clean.clone();
    stdlib_core["configuration"]["stdlib_crate"] = json!("core");
    let stdlib_core_path = tmp.path().join("stdlib_core.json");
    fs::write(&stdlib_core_path, serde_json::to_vec(&stdlib_core).unwrap()).unwrap();
    let stdlib_ok =
        run_inspect(&[stdlib_core_path.to_str().unwrap(), "--unknown-fields", "deny"], None);
    assert_eq!(
        stdlib_ok.status.code(),
        Some(0),
        "stderr={}",
        String::from_utf8_lossy(&stdlib_ok.stderr)
    );

    // Symlinked artifacts root with trailing `/`, `///`, `/.`, or `/..` must
    // be rejected.
    let sym_root = tmp.path().join("sym_root");
    symlink(&art_dir, &sym_root).unwrap();
    for (suffix, expected_err) in [
        ("/", "regular non-symlink directory"),
        ("///", "regular non-symlink directory"),
        ("/.", "concrete non-dot directory"),
        ("/..", "concrete non-dot directory"),
    ] {
        let trailing = format!("{}{suffix}", sym_root.display());
        let sym_root_fail =
            run_inspect(&[clean_path.to_str().unwrap(), "--verify-artifacts", &trailing], None);
        assert_eq!(sym_root_fail.status.code(), Some(2), "suffix={suffix}");
        let stderr = String::from_utf8_lossy(&sym_root_fail.stderr);
        assert!(stderr.contains(expected_err), "suffix={suffix}, stderr={stderr}");
    }

    // `--diff` fails closed (`exit 1`) on warn-mode unrecognized fields unless
    // `--passive` is supplied.
    let mut ext_head = clean.clone();
    ext_head["future_extension"] = json!("hello");
    let ext_head_path = tmp.path().join("ext_head.json");
    fs::write(&ext_head_path, serde_json::to_vec(&ext_head).unwrap()).unwrap();
    let ext_warn_fail = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), ext_head_path.to_str().unwrap()],
        None,
    );
    assert_eq!(ext_warn_fail.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&ext_warn_fail.stderr).contains("unrecognized"));
    let ext_passive_ok = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), ext_head_path.to_str().unwrap(), "--passive"],
        None,
    );
    assert_eq!(ext_passive_ok.status.code(), Some(0));
    let ext_passive_stdout = String::from_utf8_lossy(&ext_passive_ok.stdout);
    assert!(ext_passive_stdout.contains("[UNVERIFIED EXTENSIONS]"), "{ext_passive_stdout}");
    assert!(ext_passive_stdout.contains("/future_extension"), "{ext_passive_stdout}");
    let ext_passive_md = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            ext_head_path.to_str().unwrap(),
            "--passive",
            "--format",
            "markdown",
        ],
        None,
    );
    assert_eq!(ext_passive_md.status.code(), Some(0));
    let ext_md_out = String::from_utf8_lossy(&ext_passive_md.stdout);
    assert!(ext_md_out.contains("UNVERIFIED EXTENSIONS"), "{ext_md_out}");
    assert!(ext_md_out.contains("`/future_extension`"), "{ext_md_out}");

    // `--diff` surfaces invariant violations instead of `NO REGRESSIONS`.
    let invalid_diff = run_inspect(
        &["--diff", clean_path.to_str().unwrap(), bad_digest_path.to_str().unwrap()],
        None,
    );
    assert_eq!(invalid_diff.status.code(), Some(1));
    let invalid_stdout = String::from_utf8_lossy(&invalid_diff.stdout);
    assert!(invalid_stdout.contains("INVALID ENVELOPE(S)"), "{invalid_stdout}");
    assert!(!invalid_stdout.contains("NO REGRESSIONS"), "{invalid_stdout}");
    assert!(
        String::from_utf8_lossy(&invalid_diff.stderr).contains("invariant violation"),
        "stderr={}",
        String::from_utf8_lossy(&invalid_diff.stderr)
    );
}
