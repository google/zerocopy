@rem Copyright 2024 The Fuchsia Authors

@rem Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
@rem <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
@rem license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
@rem This file may not be copied, modified, or distributed except according to
@rem those terms.

@echo off
@rem Parse the tools compiler and pass it to cargo explicitly. An explicit
@rem `+<toolchain>` takes precedence over both RUSTUP_TOOLCHAIN and a persisted
@rem `rustup override set` in this checkout. Keep this parser coordinated with
@rem tools\rust-toolchain.toml, ci\check_tools.sh, and zerocopy\cargo.sh.
setlocal EnableDelayedExpansion
set "TOOLS_TOOLCHAIN="
set "TOOLS_TOOLCHAIN_COUNT=0"
for /f "tokens=1,2,3,4" %%A in ('findstr /B /C:"channel = " "%~dp0..\tools\rust-toolchain.toml"') do (
  if "%%A"=="channel" if "%%B"=="=" if "%%D"=="" (
    set /a TOOLS_TOOLCHAIN_COUNT+=1 >nul
    set "TOOLS_TOOLCHAIN=%%~C"
  )
)
if not "!TOOLS_TOOLCHAIN_COUNT!"=="1" (
  echo Expected one exact channel in tools\rust-toolchain.toml >&2
  exit /b 1
)

@rem Build `cargo-zerocopy` without compiler or output overrides from the
@rem environment. The explicit toolchain is the compiler pin; clearing these
@rem variables also keeps their other effects out of the build. Restore all
@rem three variables before delegating to cargo-zerocopy.
set "RUSTFLAGS="
set "CARGO_TARGET_DIR="
set "RUSTUP_TOOLCHAIN="
pushd "%~dp0..\tools"
cargo +!TOOLS_TOOLCHAIN! build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
set CARGO_ZEROCOPY_BUILD_STATUS=!ERRORLEVEL!
popd
if not "!CARGO_ZEROCOPY_BUILD_STATUS!"=="0" exit /b !CARGO_ZEROCOPY_BUILD_STATUS!
endlocal
@rem Thin wrapper around the `cargo-zerocopy` binary in `tools/cargo-zerocopy`
@pushd "%~dp0"
@..\tools\target\debug\cargo-zerocopy %*
@set CARGO_ZEROCOPY_STATUS=%ERRORLEVEL%
@popd
@exit /b %CARGO_ZEROCOPY_STATUS%
