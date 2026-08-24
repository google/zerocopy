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
@rem tools\rust-toolchain.toml, tools\cargo.sh, and ci\check_tools.sh.
@rem Do not enable delayed expansion here. A checkout path may legally contain
@rem `!`, which delayed expansion would remove while expanding `%~dp0` below.
@rem The small subroutine records loop values without requiring `!variable!`.
@setlocal
@pushd "%~dp0..\tools"
@if errorlevel 1 exit /b 1
@set "TOOLS_TOOLCHAIN="
@set "TOOLS_TOOLCHAIN_COUNT=0"
@for /f "tokens=1,2,3,4" %%A in ('findstr /B /C:"channel = " "rust-toolchain.toml"') do @call :record_tools_toolchain "%%A" "%%B" "%%~C" "%%D"
@if not "%TOOLS_TOOLCHAIN_COUNT%"=="1" (
  @echo Expected one exact channel in tools\rust-toolchain.toml >&2
  @popd
  @exit /b 1
)

@rem Build `cargo-zerocopy` without compiler or output overrides from the
@rem environment. The explicit toolchain is the compiler pin; clearing these
@rem variables also keeps their other effects out of the build. Restore all
@rem three variables before delegating to cargo-zerocopy.
@set "RUSTFLAGS="
@set "CARGO_TARGET_DIR="
@set "RUSTUP_TOOLCHAIN="
@cargo +%TOOLS_TOOLCHAIN% build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
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

:record_tools_toolchain
@if not "%~1"=="channel" exit /b 0
@if not "%~2"=="=" exit /b 0
@if not "%~4"=="" exit /b 0
@set /a TOOLS_TOOLCHAIN_COUNT+=1 >nul
@set "TOOLS_TOOLCHAIN=%~3"
@exit /b 0
