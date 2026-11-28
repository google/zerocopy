// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::*;

#[test]
fn parses_miri_return_lines() {
    assert_eq!(
        parse_miri_output(Some(0), "ANNEAL_MIRI_RET=INT:i32:-20\n", ""),
        ObservedOutcome::Returned {
            value: MirValue::Int { int_kind: IntKind::I32, bits: (-20i32 as u32) as u128 }
        }
    );
    assert_eq!(
        parse_miri_output(Some(0), "ANNEAL_MIRI_RET=OVF:u64:4:true\n", ""),
        ObservedOutcome::Returned {
            value: MirValue::OverflowPair { int_kind: IntKind::U64, bits: 4, overflow: true }
        }
    );
    assert_eq!(
        parse_miri_output(Some(0), "ANNEAL_MIRI_RET=ORDERING:less\n", ""),
        ObservedOutcome::Returned { value: MirValue::Ordering { value: OrderingKind::Less } }
    );
    let dup =
        parse_miri_output(Some(0), "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET=INT:u32:7\n", "");
    assert!(matches!(dup, ObservedOutcome::ToolError { .. }), "{dup:?}");
    let forged_bare = parse_miri_output_with_token(
        Some(0),
        "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
        "",
        Some("deadbeef"),
    );
    assert!(matches!(forged_bare, ObservedOutcome::ToolError { .. }), "{forged_bare:?}");
    let forged_tok = parse_miri_output_with_token(
        Some(0),
        "ANNEAL_MIRI_RET:badtok=INT:u32:99\n",
        "",
        Some("deadbeef"),
    );
    assert!(matches!(forged_tok, ObservedOutcome::ToolError { .. }), "{forged_tok:?}");
    let valid_tok = parse_miri_output_with_token(
        Some(0),
        "ANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
        "",
        Some("deadbeef"),
    );
    assert_eq!(
        valid_tok,
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
    );
}

#[test]
fn parses_miri_ub_abort_unsupported_and_panic() {
    let ub = parse_miri_output(
        Some(1),
        "",
        "error: Undefined Behavior: dividing by zero\n  --> src/ub.rs:5:1\n",
    );
    assert!(matches!(ub, ObservedOutcome::UndefinedBehavior { .. }));

    let abort = parse_miri_output(
        Some(1),
        "",
        "error: abnormal termination: the program aborted execution\n",
    );
    assert!(matches!(abort, ObservedOutcome::AbnormalAbort { .. }));

    let unsup =
        parse_miri_output(Some(1), "", "error: unsupported operation: calling foreign function\n");
    assert!(matches!(unsup, ObservedOutcome::Unsupported { .. }));

    let panic = parse_miri_output(
        Some(101),
        "",
        "thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
    );
    assert!(matches!(panic, ObservedOutcome::Panic { detail } if detail.contains("panicked at ")));

    // Genuine UB alongside panic text must not masquerade as benign Panic.
    let ub_with_panic = parse_miri_output(
        Some(101),
        "",
        "panicked at foo\nerror: Undefined Behavior: entering unreachable code\n",
    );
    assert!(matches!(ub_with_panic, ObservedOutcome::UndefinedBehavior { .. }));

    // Compiler/Miri ICEs must never masquerade as target-program panics.
    let ice = parse_miri_output(Some(101), "", "error: internal compiler error: broken MIR\n");
    assert!(matches!(ice, ObservedOutcome::ToolError { .. }));

    let rustc_panic = parse_miri_output(
        Some(101),
        "",
        "thread 'rustc' panicked at compiler/rustc_mir_transform/src/lib.rs:1:1:\nICE\n",
    );
    assert!(matches!(rustc_panic, ObservedOutcome::ToolError { .. }));

    // Authenticated JSON stderr checks: reject plain-text fixture
    // spoofing, mismatched harness spans, and duplicate diagnostics,
    // while classifying genuine `--error-format=json` Miri output and
    // `PANICKED` stdout tokens.
    let tok_panicked = parse_miri_output_with_token(
        Some(0),
        "ANNEAL_MIRI_RET:deadbeef=PANICKED\n",
        "error: Undefined Behavior: arithmetic overflow\n",
        Some("deadbeef"),
    );
    assert!(matches!(tok_panicked, ObservedOutcome::Panic { .. }), "{tok_panicked:?}");

    let forged_plain_ub = parse_miri_output_with_token(
        Some(101),
        "",
        "error: Undefined Behavior: arithmetic overflow\n\
         thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
        Some("deadbeef"),
    );
    assert!(matches!(forged_plain_ub, ObservedOutcome::ToolError { .. }), "{forged_plain_ub:?}");

    let forged_plain_abort = parse_miri_output_with_token(
        Some(1),
        "",
        "error: Undefined Behavior: forged\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(forged_plain_abort, ObservedOutcome::ToolError { .. }),
        "{forged_plain_abort:?}"
    );

    let multi_json_err = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/h/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(matches!(multi_json_err, ObservedOutcome::ToolError { .. }), "{multi_json_err:?}");

    let wrong_harness_span = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/other/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(wrong_harness_span, ObservedOutcome::ToolError { .. }),
        "{wrong_harness_span:?}"
    );

    // Forged JSON diagnostics emitting empty `spans: []` or only corpus
    // spans without an authenticated harness stack frame must fail closed.
    let forged_empty_spans = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(forged_empty_spans, ObservedOutcome::ToolError { .. }),
        "{forged_empty_spans:?}"
    );

    let forged_corpus_only = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(forged_corpus_only, ObservedOutcome::ToolError { .. }),
        "{forged_corpus_only:?}"
    );

    let wrong_backtrace_tok = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::f\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: main\\n    at /tmp/other/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(wrong_backtrace_tok, ObservedOutcome::ToolError { .. }),
        "{wrong_backtrace_tok:?}"
    );

    let valid_json_ub = parse_miri_output_with_token(
        Some(1),
        "",
        "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::ub\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: bridge::call_case_0\\n    at /tmp/b/bridge.rs:4:5: 4:20\\n2: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
         {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
        Some("deadbeef"),
    );
    assert!(
        matches!(
            valid_json_ub,
            ObservedOutcome::UndefinedBehavior { ref detail }
                if detail == "error: Undefined Behavior: entering unreachable code"
        ),
        "{valid_json_ub:?}"
    );
}

#[test]
fn offline_cargo_config_escapes_vendor_path() {
    let rendered =
        render_vendored_cargo_config(Path::new("/tmp/rust/lib/rustlib/src/rust/library/vendor"))
            .expect("render vendored Cargo config");
    assert!(rendered.contains("replace-with = \"vendored-sources\""), "{rendered}");
    assert!(
        rendered.contains("directory = \"/tmp/rust/lib/rustlib/src/rust/library/vendor\""),
        "{rendered}"
    );
}

#[test]
fn missing_miri_or_vendor_sysroot_fails_closed() {
    let dir = tempfile::tempdir().unwrap();
    let err = MiriSession::prepare(dir.path(), dir.path()).unwrap_err();
    assert!(err.contains("lacks `bin/miri`"), "{err}");

    let fake_sysroot = dir.path().join("sys");
    fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
    fs::write(fake_sysroot.join("bin/miri"), b"fake").unwrap();
    fs::write(fake_sysroot.join("bin/rustc"), b"fake").unwrap();
    fs::write(fake_sysroot.join("bin/cargo"), b"fake").unwrap();
    let cache = dir.path().join("cache");
    let err_vendor = build_offline_miri_sysroot(
        &fake_sysroot,
        &fake_sysroot.join("bin/miri"),
        &cache.join("miri-out"),
    )
    .unwrap_err();
    assert!(err_vendor.contains("vendored `rust-src` crates"), "{err_vendor}");

    let bogus = dir.path().join("bogus-miri");
    fs::create_dir_all(&bogus).unwrap();
    let err_explicit = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
        (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&bogus))
    })
    .unwrap_err();
    assert!(err_explicit.contains("does not contain `lib/rustlib`"), "{err_explicit}");

    // Ambient `MIRI_SYSROOT` is ignored rather than substituting a sysroot.
    let ambient_miri = dir.path().join("ambient-miri");
    fs::create_dir_all(ambient_miri.join("lib/rustlib")).unwrap();
    let err_ambient = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
        (k == "MIRI_SYSROOT").then(|| OsString::from(&ambient_miri))
    })
    .unwrap_err();
    assert!(!err_ambient.contains("MIRI_SYSROOT"), "{err_ambient}");

    #[cfg(unix)]
    {
        let sym = dir.path().join("sym-miri-sysroot");
        std::os::unix::fs::symlink(&ambient_miri, &sym).unwrap();
        let err_sym = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
            (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&sym))
        })
        .unwrap_err();
        assert!(err_sym.contains("must not be a symlink"), "{err_sym}");
    }
}

#[test]
fn rustc_version_tag_requires_metadata_and_harness_emits_typed_ret() {
    let dir = tempfile::tempdir().unwrap();
    let fake_rustc = dir.path().join("rustc");
    fs::write(&fake_rustc, b"fake-rustc").unwrap();

    assert!(parse_rustc_version_tag(&fake_rustc, "rustc 1.98.0-nightly\nhost: x\n").is_err());
    assert!(parse_rustc_version_tag(&fake_rustc, "commit-hash: abcdef123456\n").is_err());
    let tag = parse_rustc_version_tag(
        &fake_rustc,
        "commit-hash: abcdef1234567890\nhost: x86_64-unknown-linux-gnu\n",
    )
    .unwrap();
    assert!(tag.starts_with("abcdef123456-x86_64-unknown-linux-gnu-"), "{tag}");

    let src_file = dir.path().join("f.rs");
    fs::write(&src_file, "#![no_std]\npub fn f() -> u32 { 7 }\n").unwrap();
    let case = LitmusCase {
        id: "c1".to_owned(),
        source_rel: PathBuf::from("f.rs"),
        source_abs: src_file,
        function: "f".to_owned(),
        category: "arith".to_owned(),
        expected: Expectation::Pass,
        miri_ub_contains: None,
        expected_miri: None,
        args: vec![],
        expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
        fuel: 100,
    };
    let bridge = generate_miri_bridge(&[&case]).unwrap();
    assert!(bridge.contains("pub fn call_case_0() -> u32"), "{bridge}");
    assert!(bridge.contains("unsafe { corpus::f() }"), "{bridge}");
    let harness = generate_miri_harness(&[&case]).unwrap();
    assert!(harness.contains("bridge::call_case_0"), "{harness}");

    let bad_case = LitmusCase { function: "evil_macro!".to_owned(), ..case };
    assert!(generate_miri_bridge(&[&bad_case]).is_err());
}

#[test]
fn miri_setup_fingerprint_tracks_binaries_and_rust_src_contents() {
    let dir = tempfile::tempdir().unwrap();
    let sys = dir.path().join("sysroot");
    let bin_dir = sys.join("bin");
    let vendor_dir = sys.join("lib/rustlib/src/rust/library/vendor/dep_a");
    let core_dir = sys.join("lib/rustlib/src/rust/library/core/src");
    fs::create_dir_all(&bin_dir).unwrap();
    fs::create_dir_all(&vendor_dir).unwrap();
    fs::create_dir_all(&core_dir).unwrap();

    fs::write(bin_dir.join("rustc"), b"rustc-v1").unwrap();
    fs::write(bin_dir.join("cargo"), b"cargo-v1").unwrap();
    fs::write(bin_dir.join("miri"), b"miri-v1").unwrap();
    fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v1").unwrap();
    fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() {}\n").unwrap();
    fs::write(core_dir.join("lib.rs"), b"#![no_std]\n").unwrap();

    let ver_tag = "abcdef123456-x86_64-unknown-linux-gnu-001122334455";
    let base_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
    assert_eq!(base_fp.len(), 64);

    // Mutating `miri` without changing `rustc` must change the fingerprint.
    fs::write(bin_dir.join("miri"), b"miri-v2").unwrap();
    let miri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
    assert_ne!(miri_fp, base_fp);

    // Mutating `cargo-miri` must change the fingerprint.
    fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v2").unwrap();
    let cmiri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
    assert_ne!(cmiri_fp, miri_fp);

    // Mutating vendored `rust-src` must change the fingerprint.
    fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() { let _ = 1; }\n").unwrap();
    let src_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
    assert_ne!(src_fp, cmiri_fp);

    // Explicit `ANNEAL_MIRI_SYSROOT` must carry a matching ready stamp.
    let explicit_sys = dir.path().join("explicit-miri-sysroot");
    fs::create_dir_all(explicit_sys.join("lib/rustlib")).unwrap();
    let unstamped = verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp);
    assert!(unstamped.is_err());

    fs::write(explicit_sys.join(".anneal-miri-ready"), expected_miri_ready_stamp(ver_tag, &src_fp))
        .unwrap();
    verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp).unwrap();

    // Stale stamp after `miri` or `rust-src` mutation must fail closed.
    assert!(verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &cmiri_fp).is_err());

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        let fake_rustc = bin_dir.join("rustc");
        fs::write(
            &fake_rustc,
            b"#!/bin/sh\nprintf 'commit-hash: abcdef1234567890\\nhost: x86_64-unknown-linux-gnu\\n'\n",
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let real_tag = rustc_version_tag(&sys).unwrap();
        let real_sha = compute_miri_setup_input_sha256(&sys, &real_tag).unwrap();
        let cache = dir.path().join("cache");

        // Stale stamp from pre-executable `rustc` is rejected by
        // `prepare_with_env` before accepting `ANNEAL_MIRI_SYSROOT`.
        let Err(stale_err) = MiriSession::prepare_with_env(&sys, &cache, |k| {
            (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
        }) else {
            panic!("stale explicit stamp must fail");
        };
        assert!(stale_err.contains("setup stamp does not match"), "{stale_err}");

        // Refreshing the stamp to match current inputs succeeds.
        fs::write(
            explicit_sys.join(".anneal-miri-ready"),
            expected_miri_ready_stamp(&real_tag, &real_sha),
        )
        .unwrap();
        let session = MiriSession::prepare_with_env(&sys, &cache, |k| {
            (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
        })
        .expect("matching explicit stamp must succeed");
        assert_eq!(session.miri_sysroot, fs::canonicalize(&explicit_sys).unwrap());
    }

    // Missing `cargo-miri` fails closed.
    fs::remove_file(bin_dir.join("cargo-miri")).unwrap();
    assert!(compute_miri_setup_input_sha256(&sys, ver_tag).is_err());
}
