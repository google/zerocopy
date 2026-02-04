use std::path::Path;

use ui_test::{spanned::Spanned, *};

fn main() -> Result<()> {
    let path = Path::new(file!()).parent().unwrap();
    let root_dir = path.join("integrations");
    let mut config = Config {
        bless_command: Some("cargo test".to_string()),
        ..Config::cargo(root_dir.clone())
    };

    config.comment_defaults.base().require_annotations = Some(Spanned::dummy(false)).into();

    let args = Args::test()?;
    config.with_args(&args);

    config.program.args = vec![
        "test".into(),
        "--color".into(),
        "never".into(),
        "--quiet".into(),
        "--jobs".into(),
        "1".into(),
        "--no-fail-fast".into(),
    ];
    config
        .program
        .envs
        .push(("RUST_TEST_THREADS".into(), Some("1".into())));

    config
        .program
        .envs
        .push(("BLESS".into(), (!args.check).then(|| String::new().into())));

    config
        .program
        .envs
        .push(("RUST_BACKTRACE".into(), Some("0".into())));

    config.stdout_filter("in ([0-9]m )?[0-9\\.]+s", "");
    config.stdout_filter(r#""--out-dir"(,)? "[^"]+""#, r#""--out-dir"$1 "$$TMP"#);
    config.filter("\\.exe", b"");
    config.filter(
        "( *process didn't exit successfully: `.*)-[0-9a-f]+`",
        "$1-HASH`",
    );
    // Windows io::Error uses "exit code".
    config.filter("exit code", "exit status");
    config.filter(
        "The system cannot find the file specified.",
        "No such file or directory",
    );
    config.filter("RUSTC_BOOTSTRAP=\"1\" ", "");
    config.filter("RUSTC_ICE=\"0\" ", "");
    // The order of the `/deps` directory flag is flaky
    config.stdout_filter("/deps", "");
    config.path_filter(std::path::Path::new(path), "$DIR");
    config.stdout_filter("[0-9a-f]+\\.rmeta", "$$HASH.rmeta");
    // Windows backslashes are sometimes escaped.
    // Insert the replacement filter at the start to make sure the filter for single backslashes
    // runs afterwards.
    config
        .comment_defaults
        .base()
        .normalize_stdout
        .insert(0, (Match::Exact(b"\\\\".to_vec()), b"\\".to_vec()));
    config.stdout_filter(r#"(panic.*)\.rs:[0-9]+:[0-9]+"#, "$1.rs");
    // We don't want to normalize lines starting with `+`, those are diffs of the inner ui_test
    // and normalizing these here doesn't make the "actual output differed from expected" go
    // away, it just makes it impossible to diagnose.
    config.filter(" +[0-9]+: .*\n", "");
    config.filter("                +at \\.?/.*\n", "");
    config.filter(" running on .*", "");
    config.stdout_filter("/target/[^/]+/[^/]+/debug", "/target/$$TMP/$$TRIPLE/debug");
    config.stdout_filter("/target/.tmp[^/ \"]+", "/target/$$TMP");
    // Normalize proc macro filenames on windows to their linux repr
    config.stdout_filter("/([^/\\.]+)\\.dll", "/lib$1.so");
    // Normalize proc macro filenames on mac to their linux repr
    config.stdout_filter("/([^/\\.]+)\\.dylib", "/$1.so");
    config.stdout_filter("(command: )\"[^<rp][^\"]+", "$1\"$$CMD");
    config.filter("(src/.*?\\.rs):[0-9]+:[0-9]+", "$1:LL:CC");
    config.filter("program not found", "No such file or directory");
    config.filter(" \\(os error [0-9]+\\)", "");
    config.filter("note: rustc 1\\..*", "");
    // Cross compilation paths contain an additional target directory name
    config.stderr_filter(
        "(/target/ui/tests/integrations/[^/]+).*debug/deps",
        "$1/debug/deps",
    );
    // abort messages are different on macos
    config.stdout_filter(r#" \(core dumped\)"#, "");
    // abort messages are different on windows
    config.stdout_filter(r#"exit status: 0xc0000409"#, "signal: 6 (SIGABRT)");
    config.filter("\"--target=[^\"]+\"", "");

    let text = ui_test::status_emitter::Text::from(args.format);

    let mut pass_config = config.clone();
    pass_config.comment_defaults.base().exit_status = Some(Spanned::dummy(0)).into();
    let mut panic_config = config;
    panic_config.comment_defaults.base().exit_status = Some(Spanned::dummy(101)).into();

    run_tests_generic(
        vec![pass_config, panic_config],
        |path, config| {
            let fail = path
                .parent()
                .unwrap()
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .ends_with("-fail");
            if cfg!(windows) && path.components().any(|c| c.as_os_str() == "basic-bin") {
                // on windows there's also a .pdb file, so we get additional errors that aren't there on other platforms
                return Some(false);
            }
            if !path.ends_with("Cargo.toml") {
                return None;
            }
            Some(
                path.parent().unwrap().parent().unwrap() == root_dir
                    && match config
                        .comment_defaults
                        .base_immut()
                        .exit_status
                        .as_deref()
                        .unwrap()
                    {
                        0 => !fail,
                        // This is weird, but `cargo test` returns 101 instead of 1 when
                        // multiple [[test]]s exist. If there's only one test, it returns
                        // 1 on failure.
                        101 => fail,
                        _ => unreachable!(),
                    }
                    && default_any_file_filter(path, config),
            )
        },
        |_, _| {},
        (
            text,
            ui_test::status_emitter::Gha::<true> {
                name: "integration tests".into(),
            },
        ),
    )
}
