@rem Copyright 2024 The Fuchsia Authors

@rem Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
@rem <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
@rem license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
@rem This file may not be copied, modified, or distributed except according to
@rem those terms.

@rem Build `cargo-zerocopy` without any RUSTFLAGS set in the environment.
@rem Building from `tools` selects `tools\rust-toolchain.toml`, remains outside
@rem Zerocopy's vendored configuration, and keeps the lockfile read-only.
@set SCRIPT_DIR=%~dp0
@set TEMP_RUSTFLAGS=%RUSTFLAGS%
@set RUSTFLAGS=
@pushd "%SCRIPT_DIR%..\tools"
@cargo build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
@set CARGO_ZEROCOPY_BUILD_STATUS=%ERRORLEVEL%
@popd
@set RUSTFLAGS=%TEMP_RUSTFLAGS%
@set TEMP_RUSTFLAGS=
@if not "%CARGO_ZEROCOPY_BUILD_STATUS%"=="0" exit /b %CARGO_ZEROCOPY_BUILD_STATUS%
@rem Thin wrapper around the `cargo-zerocopy` binary in `tools/cargo-zerocopy`
@pushd "%SCRIPT_DIR%"
@..\tools\target\debug\cargo-zerocopy %*
@set CARGO_ZEROCOPY_STATUS=%ERRORLEVEL%
@popd
@exit /b %CARGO_ZEROCOPY_STATUS%
