// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    env,
    fmt::Debug,
    path::{Path, PathBuf},
};

use ui_test::{
    spanned::Spanned,
    status_emitter::{RevisionStyle, StatusEmitter, Summary, TestStatus},
    test_result::TestResult,
    Config,
};

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
    config.program.envs.push(("RUSTUP_TOOLCHAIN".into(), Some(toolchain.clone().into())));

    let toolchain_meta_name = env::var("ZEROCOPY_UI_TEST_TOOLCHAIN_META_NAME")
        .expect("ZEROCOPY_UI_TEST_TOOLCHAIN_META_NAME must be set by tests/ui.rs");
    config.host = Some(toolchain_meta_name.clone());

    let workspace_root =
        env::var("ZEROCOPY_WORKSPACE_ROOT").map(PathBuf::from).unwrap_or_else(|_| root.clone());

    config.stderr_filter(&workspace_root.display().to_string(), "$$WORKSPACE");
    if let Ok(canonical) = std::fs::canonicalize(&workspace_root) {
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

    config.comment_defaults.base().require_annotations = Spanned::dummy(true).into();
    config.comment_defaults.revisions =
        Some(vec!["msrv".to_string(), "stable".to_string(), "nightly".to_string()]);

    #[derive(Debug, Clone)]
    struct IgnoreRevision;

    impl ui_test::custom_flags::Flag for IgnoreRevision {
        fn clone_inner(&self) -> Box<dyn ui_test::custom_flags::Flag> {
            Box::new(self.clone())
        }
        fn test_condition(
            &self,
            _config: &ui_test::Config,
            _comments: &ui_test::Comments,
            _revision: &str,
        ) -> bool {
            true
        }
        fn must_be_unique(&self) -> bool {
            false
        }
    }

    // By default, ui_test runs every revision listed in
    // `Config::comment_defaults.revisions`. We have to set that equal to all
    // three revisions, or else ui_test will treat the unrecognized revisions
    // as errors when it encounters them in annotations. But we also only want
    // it to run the specific revision (ie, toolchain) we've requested. To work
    // around this, we specifically instruct it to ignore all revisions other
    // than the one we're actually running.
    for rev in &["msrv", "stable", "nightly"] {
        if rev != &toolchain_meta_name {
            let revisioned =
                config.comment_defaults.revisioned.entry(vec![rev.to_string()]).or_default();
            revisioned.add_custom("ignore-revision", IgnoreRevision);
        }
    }

    config.comment_defaults.base().exit_status = Spanned::dummy(1).into();
    config.comment_defaults.base().custom.remove("rustfix");

    config.stderr_filter(r"[^']*\.long-type-\d+\.txt", b"$OUT_DIR/long-type-HASH.txt");

    // NOTE: We intentionally don't respect `RUSTFLAGS` here, as it is too
    // unreliable. Recall that we are only compiling the crate under test,
    // not zerocopy itself. Zerocopy has already been compiled by the time
    // we get here, so these flags only apply to the crate under test.
    // Ignoring `RUSTFLAGS` and specifying our own flags here makes these
    // tests more reproducible.

    // FIXME: These seem to have no effect (ie, rustc seems to still discover
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
        OverrideEmitter(ui_test::status_emitter::Text::verbose(), toolchain_meta_name),
    )
    .unwrap();
}

// Used to add the `.msrv`, `.stable`, or `.nightly` suffix to test output files
// (resulting in `.msrv.stderr`, `.stable.stderr`, or `.nightly.stderr`).
struct OverrideEmitter<E>(E, String);

impl<E: StatusEmitter> StatusEmitter for OverrideEmitter<E> {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        let inner = self.0.register_test(path);
        Box::new(RevisionOverrideStatus { inner, override_rev: self.1.clone() })
    }

    fn finalize(
        &self,
        failed: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary> {
        self.0.finalize(failed, succeeded, ignored, filtered, aborted)
    }
}

struct RevisionOverrideStatus {
    inner: Box<dyn TestStatus>,
    override_rev: String,
}

impl TestStatus for RevisionOverrideStatus {
    fn for_revision(&self, revision: &str, style: RevisionStyle) -> Box<dyn TestStatus> {
        let effective_rev = if revision.is_empty() { &self.override_rev } else { revision };
        Box::new(RevisionOverrideStatus {
            inner: self.inner.for_revision(revision, style),
            override_rev: effective_rev.to_string(),
        })
    }

    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        Box::new(RevisionOverrideStatus {
            inner: self.inner.for_path(path),
            override_rev: self.override_rev.clone(),
        })
    }

    fn failed_test<'a>(
        &'a self,
        cmd: &'a str,
        stderr: &'a [u8],
        stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a> {
        self.inner.failed_test(cmd, stderr, stdout)
    }

    fn done(&self, result: &TestResult, aborted: bool) {
        self.inner.done(result, aborted)
    }

    fn path(&self) -> &Path {
        self.inner.path()
    }

    fn revision(&self) -> &str {
        &self.override_rev
    }
}
