# Support material

## `rust_defaults/`

`cases.sh` compiles 13 one-line Rust libraries with the `rustc` on `PATH` and prints `ACCEPT` or `REJECT` with any error code. Temporary files are written under `/tmp`. `cases.out` is the recorded output for `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`.

## `elision_survey/`

`elision_survey` is a syntactic survey of lifetime elision in function signatures, built with `syn` 2.0.119.

To build and run:

```console
cargo build --offline --release
./target/release/elision_survey "$(rustc --print sysroot)/lib/rustlib/src/rust/library/core/src" \
    "$(rustc --print sysroot)/lib/rustlib/src/rust/library/alloc/src" \
    "$(rustc --print sysroot)/lib/rustlib/src/rust/library/std/src"
```

Building with `--offline` requires `syn` in the local Cargo cache; omit the flag to fetch it. Set `SHOW_PARSE_FAILURES=1` to list files that `syn` cannot parse. `survey.out` is the recorded output, with the sysroot prefix replaced by `<rust-src>`. The classification rules and limitations are documented at the top of `src/main.rs`.
