A stable version of compiletest-rs

## Magic behavior

* Tests are run in order of their filenames (files first, then recursing into folders).
  So if you have any slow tests, prepend them with a small integral number to make them get run first, taking advantage of parallelism as much as possible (instead of waiting for the slow tests at the end).
* `cargo test --test your_test_name -- --help` lists the commands you can specify for filtering, blessing and making your tests less verbose.
    * Since `cargo test` on its own runs all tests, using `cargo test -- --check` will not work on its own, but `cargo test -- --quiet` and `cargo test -- some_test_name` will work just fine, as the CLI matches.
* if there is a `.stdin` file with the same filename as your test, it will be piped as standard input to your program.

## Supported magic comment annotations

If your test tests for failure, you need to add a `//~` annotation where the error is happening
to ensure that the test will always keep failing at the annotated line. These comments can take two forms:

* `//~ LEVEL: XXX` matches by error level and message text
    * `LEVEL` can be one of the following (descending order): `ERROR`, `HELP`, `WARN` or `NOTE`
    * If a level is specified explicitly, *all* diagnostics of that level or higher need an annotation. To avoid this see `//@require-annotations-for-level`
    * This checks the output *before* normalization, so you can check things that get normalized away, but need to
        be careful not to accidentally have a pattern that differs between platforms.
    * if `XXX` is of the form `/XXX/` it is treated as a regex instead of a substring and will succeed if the regex matches.
* `//~ CODE` matches by diagnostic code.
    * `CODE` can take multiple forms such as: `E####`, `lint_name`, `tool::lint_name`.
    * This will only match a diagnostic at the `ERROR` level.

In order to change how a single test is tested, you can add various `//@` comments to the test.
Any other comments will be ignored, and all `//@` comments must be formatted precisely as
their command specifies, or the test will fail without even being run.

* `//@ignore-C` avoids running the test when condition `C` is met.
    * `C` can be `target-XXX`, which checks whether the target triple contains `XXX`.
    * `C` can be `host-XXX`, which checks whether the host triple contains `XXX`.
    * `C` can also be one of `64bit`, `32bit` or `16bit`.
    * `C` can also be `on-host`, which will only run the test during cross compilation testing.
* `//@only-C` **only** runs the test when condition `C` is met. The conditions are the same as with `ignore`.
* `//@needs-asm-support` **only** runs the test when the target supports `asm!`.
* `//@stderr-per-bitwidth` produces one stderr file per bitwidth, as they may differ significantly sometimes
* `//@error-in-other-file: XXX` can be used to check for errors that can't have `//~` patterns due to being reported in other files.
* `//@revisions: XXX YYY` runs the test once for each space separated name in the list
    * emits one stderr file per revision
    * `//~` comments can be restricted to specific revisions by adding the revision name after the `~` in square brackets: `//~[XXX]`
    * `//@` comments can be restricted to specific revisions by adding the revision name after the `@` in square brackets: `//@[XXX]`
        * Note that you cannot add revisions to the `revisions` command.
* `//@compile-flags: XXX` appends `XXX` to the command line arguments passed to the rustc driver
    * you can specify this multiple times, and all the flags will accumulate
* `//@rustc-env: XXX=YYY` sets the env var `XXX` to `YYY` for the rustc driver execution.
    * for Miri these env vars are used during compilation via rustc and during the emulation of the program
    * you can specify this multiple times, accumulating all the env vars
* `//@normalize-stderr-test: "REGEX" -> "REPLACEMENT"` replaces all matches of `REGEX` in the stderr with `REPLACEMENT`. The replacement may specify `$1` and similar backreferences to paste captures.
    * you can specify multiple such commands, there is no need to create a single regex that handles multiple replacements that you want to perform.
* `//@require-annotations-for-level: LEVEL` can be used to change the level of diagnostics that require a corresponding annotation.
    * this is only useful if there are any annotations like `HELP`, `WARN` or `NOTE`, as these would automatically require annotations for all other diagnostics of the same or higher level.
* `//@check-pass` requires that a test has no error annotations, emits no errors, and exits successfully with exit/status code 0.
* `//@edition: EDITION` overwrites the default edition (2021) to the given edition.
* `//@no-rustfix` do not run [rustfix] on tests that have machine applicable suggestions.
* `//@aux-build: filename` looks for a file in the `auxiliary` directory (within the directory of the test), compiles it as a library and links the current crate against it. This allows you import the crate with `extern crate` or just via `use` statements. This will automatically detect aux files that are proc macros and build them as proc macros.
* `//@run` compiles the test and runs the resulting binary. The resulting binary must exit successfully. Stdout and stderr are taken from the resulting binary. Any warnings during compilation are ignored.
    * You can also specify a different exit code/status that is expected via e.g. `//@run: 1` or `//@run: 101` (the latter is the standard Rust exit code for panics).
    * run tests collect the run output into `.run.stderr` and `.run.stdout` respectively.
    * if a `.run.stdin` file exists, it will be piped as standard input to your test's execution.

[rustfix]: https://github.com/rust-lang/rustfix

## Significant differences to compiletest-rs

* `ignore-target-xxx` and `only-target-xxx` requires the `target-` prefix before the `xxx` substring
  to be matched against target triples, whereas compiletest allows plain `ignore-xxx` without the
  `target-` prefix. The substring `xxx` must also be a substring of target triples, and special
  collections such as `macos`/`unix` in compiletest is not supported.
* only supports `ui` tests
* tests are run in named order, so you can prefix slow tests with `0` in order to make them get run first
* `aux-build`s require specifying nested aux builds explicitly and will not allow you to reference sibling `aux-build`s' artifacts.
