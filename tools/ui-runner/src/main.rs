// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{env, path::PathBuf};

use ui_test::Config;

fn main() {
    let rlib_path = PathBuf::from(
        env::var("ZEROCOPY_RLIB_PATH").expect("ZEROCOPY_RLIB_PATH must be set by tests/ui.rs"),
    );
    let derive_path = PathBuf::from(
        env::var("ZEROCOPY_DERIVE_LIB_PATH")
            .expect("ZEROCOPY_DERIVE_LIB_PATH must be set by tests/ui.rs"),
    );
    let static_assertions_path = PathBuf::from(
        env::var("ZEROCOPY_STATIC_ASSERTIONS_PATH")
            .expect("ZEROCOPY_STATIC_ASSERTIONS_PATH must be set by tests/ui.rs"),
    );

    let tests_dir = PathBuf::from(
        env::var("ZEROCOPY_UI_TEST_DIR").expect("ZEROCOPY_UI_TEST_DIR must be set by tests/ui.rs"),
    );
    let toolchain = env::var("ZEROCOPY_UI_TEST_TOOLCHAIN")
        .expect("ZEROCOPY_UI_TEST_TOOLCHAIN must be set by tests/ui.rs");

    let root = env::current_dir().unwrap();
    let mut config = Config::rustc(tests_dir.clone());
    config.out_dir = root.join("target").join("ui-test-artifacts");
    config.program.envs.push(("RUSTUP_TOOLCHAIN".into(), Some(toolchain.into())));

    config.stderr_filter(&root.display().to_string(), "$$WORKSPACE");
    if let Ok(canonical) = std::fs::canonicalize(&root) {
        config.stderr_filter(&canonical.display().to_string(), "$$WORKSPACE");
    }

    // Normalize paths to rustlib source code, which will differ between developer
    // machines and CI runners.
    config.stderr_filter(r"(/[^/]+)+/\.rustup/toolchains/[^/]+/", b"$$RUSTUP_TOOLCHAIN/");

    config.stderr_filter(&tests_dir.display().to_string(), "$$DIR");
    if let Ok(canonical) = std::fs::canonicalize(&tests_dir) {
        config.stderr_filter(&canonical.display().to_string(), "$$DIR");
    }

    if env::args().any(|arg| arg == "--bless") || env::var("BLESS").is_ok() {
        config.output_conflict_handling = ui_test::bless_output_files;
    }

    use ui_test::spanned::Spanned;
    config.comment_start = "//@ui_test";
    config.comment_defaults.base().require_annotations = Spanned::dummy(false).into();
    config.comment_defaults.base().exit_status = Spanned::dummy(1).into();
    config.comment_defaults.base().custom.remove("rustfix");

    config.stderr_filter(r"[^']*\.long-type-\d+\.txt", b"$OUT_DIR/long-type-HASH.txt");

    // NOTE: We intentionally don't respect `RUSTFLAGS` here, as it is too
    // unreliable. Recall that we are only compiling the crate under test,
    // not zerocopy itself. Zerocopy has already been compiled by the time
    // we get here, so these flags only apply to the crate under test.
    // Ignoring `RUSTFLAGS` and specifying our own flags here makes these
    // tests more reproducible.

    // TODO: These seem to have no effect (ie, rustc seems to still discover
    // the real terminal width).
    config.program.envs.push(("TERM".into(), Some("dumb".into())));
    config.program.envs.push(("COLUMNS".into(), Some("100".into())));

    // Set `-Wwarnings` in the `RUSTFLAGS` environment variable to ensure that
    // `.stderr` files reflect what the typical user would encounter.
    config.program.envs.push(("RUSTFLAGS".into(), Some("-Wwarnings".into())));

    config.program.args.push("--extern".into());
    config.program.args.push(format!("zerocopy={}", rlib_path.display()).into());
    config.program.args.push("--extern".into());
    config.program.args.push(format!("zerocopy_renamed={}", rlib_path.display()).into());
    config.program.args.push("--extern".into());
    config.program.args.push(format!("zerocopy_derive={}", derive_path.display()).into());
    config.program.args.push("--extern".into());
    config
        .program
        .args
        .push(format!("static_assertions={}", static_assertions_path.display()).into());

    config.program.args.push("-L".into());
    config
        .program
        .args
        .push(format!("dependency={}", rlib_path.parent().unwrap().display()).into());

    config.program.args.push("-L".into());
    config
        .program
        .args
        .push(format!("dependency={}", derive_path.parent().unwrap().display()).into());

    config.program.args.push("-L".into());
    config
        .program
        .args
        .push(format!("dependency={}", static_assertions_path.parent().unwrap().display()).into());

    let mut external_args = Vec::new();
    for arg in env::args().skip(1) {
        if arg == "--bless" {
            continue;
        } else if let Some(stripped) = arg.strip_prefix("--rustc-arg=") {
            config.program.args.push(stripped.into());
        } else {
            external_args.push(arg);
        }
    }

    let root_path = root.join(&tests_dir).canonicalize().unwrap_or(root.join(&tests_dir));
    // DEBUG: print rustc args
    std::fs::write("ui-runner-config.txt", format!("{:#?}", config.program)).unwrap();
    ui_test::run_tests_generic(
        vec![config],
        |path, _config| {
            let path_str = path.to_string_lossy();
            if path.extension().map(|ext| ext == "rs").unwrap_or(false) {
                let parent = path
                    .parent()
                    .and_then(|p| p.canonicalize().ok())
                    .unwrap_or_else(|| path.parent().unwrap().to_path_buf());
                if parent != root_path {
                    // Ignore files in subdirectories, matching trybuild's shallow globs.
                    // If a user explicitly names it via external_args, we still allow it.
                    if external_args.is_empty()
                        || !external_args.iter().any(|arg| path_str.contains(arg))
                    {
                        return Some(false);
                    }
                }

                if external_args.is_empty()
                    || external_args.iter().any(|arg| path_str.contains(arg))
                {
                    return Some(true);
                }
            }
            Some(false)
        },
        |_, _| {},
        ui_test::status_emitter::Text::verbose(),
    )
    .unwrap();
}
