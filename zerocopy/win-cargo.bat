@rem Copyright 2024 The Fuchsia Authors

@rem Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
@rem <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
@rem license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
@rem This file may not be copied, modified, or distributed except according to
@rem those terms.

@rem Build `cargo-zerocopy` without compiler or output overrides from the
@rem environment. RUSTUP_TOOLCHAIN takes precedence over rust-toolchain.toml,
@rem and CARGO_TARGET_DIR would put the binary somewhere this wrapper does not
@rem execute. Restore all three variables before delegating to cargo-zerocopy.
@setlocal
@set "RUSTFLAGS="
@set "CARGO_TARGET_DIR="
@set "RUSTUP_TOOLCHAIN="
@pushd "%~dp0..\tools"
@cargo build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
@set CARGO_ZEROCOPY_BUILD_STATUS=%ERRORLEVEL%
@popd
@if not "%CARGO_ZEROCOPY_BUILD_STATUS%"=="0" exit /b %CARGO_ZEROCOPY_BUILD_STATUS%
@endlocal
@rem Thin wrapper around the `cargo-zerocopy` binary in `tools/cargo-zerocopy`
@pushd "%~dp0"
@..\tools\target\debug\cargo-zerocopy %*
@set CARGO_ZEROCOPY_STATUS=%ERRORLEVEL%
@popd
@exit /b %CARGO_ZEROCOPY_STATUS%
