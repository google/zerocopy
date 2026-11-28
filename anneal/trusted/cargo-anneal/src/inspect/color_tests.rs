// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use super::{ColorChoice, EnvSnapshot, InspectFormat, resolve_inspect_use_color};

#[test]
fn resolve_inspect_use_color_honors_unified_env_precedence_and_passive_guards() {
    let dumb = EnvSnapshot { term: Some("dumb".into()), ..EnvSnapshot::default() };
    assert!(!resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || true,
        &dumb,
    ));

    let cargo_never = EnvSnapshot {
        cargo_term_color: Some("never".into()),
        clicolor_force: Some("1".into()),
        ..EnvSnapshot::default()
    };
    assert!(!resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || true,
        &cargo_never,
    ));

    let cargo_always = EnvSnapshot {
        cargo_term_color: Some("ALWAYS".into()),
        no_color: Some("1".into()),
        ..EnvSnapshot::default()
    };
    assert!(resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || false,
        &cargo_always,
    ));

    let forced = EnvSnapshot { clicolor_force: Some("1".into()), ..EnvSnapshot::default() };
    assert!(resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || false,
        &forced,
    ));

    // Non-empty `NO_COLOR` overrides `CLICOLOR_FORCE`, while empty
    // `NO_COLOR=""` is treated as unset.
    let no_color = EnvSnapshot {
        no_color: Some("1".into()),
        clicolor_force: Some("1".into()),
        ..EnvSnapshot::default()
    };
    assert!(!resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || true,
        &no_color,
    ));
    let empty_no_color = EnvSnapshot { no_color: Some(String::new()), ..EnvSnapshot::default() };
    assert!(resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || true,
        &empty_no_color,
    ));

    // Passive mode and `--output FILE` suppress `Auto` color and never
    // probe the terminal, even when env force variables are set.
    assert!(!resolve_inspect_use_color(
        true,
        false,
        InspectFormat::Human,
        ColorChoice::Auto,
        || panic!("passive mode must not probe stdout tty"),
        &forced,
    ));
    assert!(!resolve_inspect_use_color(
        false,
        true,
        InspectFormat::Human,
        ColorChoice::Auto,
        || panic!("--output FILE must not probe stdout tty"),
        &cargo_always,
    ));

    // Non-human formats never emit ANSI SGR, even under `--color always`.
    for fmt in [InspectFormat::Json, InspectFormat::Ledger, InspectFormat::Markdown] {
        assert!(!resolve_inspect_use_color(
            false,
            false,
            fmt,
            ColorChoice::Always,
            || panic!("non-human format must not probe stdout tty"),
            &forced,
        ));
    }

    // Explicit `--color always` and `--color never` override env on human
    // output without probing the terminal.
    assert!(resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Always,
        || panic!("--color always must not probe stdout tty"),
        &no_color,
    ));
    assert!(!resolve_inspect_use_color(
        false,
        false,
        InspectFormat::Human,
        ColorChoice::Never,
        || panic!("--color never must not probe stdout tty"),
        &cargo_always,
    ));
}

#[test]
fn receipt_input_cap_hint_honors_ceiling_and_past_tense_growth() {
    use std::fs;

    use super::{InspectParseError, MAX_CONFIGURABLE_RECEIPT_JSON_BYTES, read_receipt_input};

    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("oversize.json");
    fs::write(&path, b"0123456789abcdef").unwrap();

    let err = match read_receipt_input(&path, 8) {
        Err(InspectParseError::Operational(msg)) => msg,
        other => panic!("expected operational error, got {other:?}"),
    };
    assert!(err.contains("pass `--max-receipt-bytes`"), "{err}");

    let f = fs::OpenOptions::new().write(true).create(true).truncate(true).open(&path).unwrap();
    f.set_len((MAX_CONFIGURABLE_RECEIPT_JSON_BYTES as u64) + 1).unwrap();
    drop(f);

    let ceiling_err = match read_receipt_input(&path, MAX_CONFIGURABLE_RECEIPT_JSON_BYTES) {
        Err(InspectParseError::Operational(msg)) => msg,
        other => panic!("expected operational error at ceiling, got {other:?}"),
    };
    assert!(!ceiling_err.contains("pass `--max-receipt-bytes`"), "{ceiling_err}");
}
