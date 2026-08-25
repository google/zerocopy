@rem Copyright 2024 The Fuchsia Authors

@rem Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
@rem <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
@rem license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
@rem This file may not be copied, modified, or distributed except according to
@rem those terms.

@echo off
@rem Parse the tools compiler and pass it to cargo explicitly. An explicit
@rem `+<toolchain>` takes precedence over both RUSTUP_TOOLCHAIN and a persisted
@rem `rustup override set` in this checkout. This bootstrap parser requires the
@rem complete non-comment file shape: [toolchain], one canonical numeric
@rem channel, then profile = "minimal". A future semantic field must update this
@rem parser deliberately. Keep it coordinated with tools\rust-toolchain.toml,
@rem tools\toolchain.sh, tools\cargo.sh, and ci\check_tools.sh.
@rem Resolve the checkout path before enabling delayed expansion. A checkout
@rem path may legally contain `!`, which delayed expansion would remove while
@rem expanding `%~dp0`. The parser enables it only while already inside tools.
@setlocal EnableExtensions DisableDelayedExpansion
@rem A caller can define an ordinary ERRORLEVEL variable which shadows cmd's
@rem dynamic status value during `%ERRORLEVEL%` and `!ERRORLEVEL!` expansion.
@rem Clear only this local copy so status capture remains trustworthy; the
@rem final ENDLOCAL restores any value the caller supplied.
@set "ERRORLEVEL="
@pushd "%~dp0..\tools"
@if errorlevel 1 exit /b 1
@set "TOOLS_TOOLCHAIN_FILE_VALID=1"
@rem FOR /F collapses whitespace before the token checks below. Reject every
@rem noncanonical space and tab in a semantic line first. The last /C pattern
@rem contains one literal tab.
@findstr /V /B /C:"#" "rust-toolchain.toml" | findstr /R /C:"^ " /C:" $" /C:"  " /C:"	" >nul
@if not errorlevel 1 @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
@rem Delayed expansion makes a single FOR block possible without CALL. Reject
@rem command-interpreter metacharacters before enabling it so a malformed
@rem semantic line can only make validation fail, never change the commands
@rem which validate it. The doubled percent denotes one literal character
@rem after cmd.exe parses this line. `|` is also the FOR /F end-of-line marker
@rem below, so rejecting it prevents a semantic line from being skipped.
@findstr /V /B /C:"#" "rust-toolchain.toml" | ^
  findstr /L /C:"!" /C:"&" /C:"|" /C:"^" /C:"%%" /C:"<" /C:">" ^
    /C:"(" /C:")" >nul
@if not errorlevel 1 @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
@if not "%TOOLS_TOOLCHAIN_FILE_VALID%"=="1" (
  @echo Expected one canonical [toolchain] channel ^
    in tools\rust-toolchain.toml >&2
  @popd
  @exit /b 1
)

@setlocal EnableDelayedExpansion
@set "TOOLS_TOOLCHAIN="
@set "TOOLS_TOOLCHAIN_LINE_COUNT=0"
@set "TOOLS_TOOLCHAIN_CHANNEL_RAW="
@set "TOOLS_TOOLCHAIN_PROFILE_RAW="
@for /f "eol=| tokens=1,2,3,4" %%A in ('findstr /V /B /C:"#" "rust-toolchain.toml"') do (
  @set /a TOOLS_TOOLCHAIN_LINE_COUNT+=1 >nul
  @if "!TOOLS_TOOLCHAIN_LINE_COUNT!"=="1" (
    @if not "%%A"=="[toolchain]" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%B"=="" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
  ) else if "!TOOLS_TOOLCHAIN_LINE_COUNT!"=="2" (
    @if not "%%A"=="channel" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%B"=="=" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%D"=="" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @set "TOOLS_TOOLCHAIN=%%~C"
    @set "TOOLS_TOOLCHAIN_CHANNEL_RAW=%%C"
  ) else if "!TOOLS_TOOLCHAIN_LINE_COUNT!"=="3" (
    @if not "%%A"=="profile" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%B"=="=" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%~C"=="minimal" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @if not "%%D"=="" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
    @set "TOOLS_TOOLCHAIN_PROFILE_RAW=%%C"
  ) else (
    @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
  )
)
@if not "!TOOLS_TOOLCHAIN_LINE_COUNT!"=="3" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"

@rem `%%~C` deliberately removes quotes when recording the channel. Compare
@rem the raw token separately so alternate or missing quotes cannot pass. A
@rem sentinel before each operand also makes an empty token safe.
@set TOOLS_TOOLCHAIN_EXPECTED_CHANNEL_RAW="!TOOLS_TOOLCHAIN!"
@if not x!TOOLS_TOOLCHAIN_CHANNEL_RAW!==x!TOOLS_TOOLCHAIN_EXPECTED_CHANNEL_RAW! ^
  @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
@if not x!TOOLS_TOOLCHAIN_PROFILE_RAW!==x"minimal" ^
  @set "TOOLS_TOOLCHAIN_FILE_VALID=0"

@rem Require exactly three nonempty decimal components. FOR /F collapses
@rem repeated delimiters, so reconstructing the version also rejects leading,
@rem trailing, and repeated dots. Initialize the result to failure because an
@rem empty value causes FOR /F to execute no iterations.
@set "TOOLS_TOOLCHAIN_VERSION_VALID=0"
@for /f "eol=| tokens=1-4 delims=." %%V in ("!TOOLS_TOOLCHAIN!") do (
  @if not "%%V"=="" if not "%%W"=="" if not "%%X"=="" ^
      if "%%Y"=="" if "!TOOLS_TOOLCHAIN!"=="%%V.%%W.%%X" (
    @set "TOOLS_TOOLCHAIN_VERSION_VALID=1"
    @for /f "eol=| delims=0123456789" %%N in ("%%V%%W%%X") do ^
      @set "TOOLS_TOOLCHAIN_VERSION_VALID=0"
  )
)
@if not "!TOOLS_TOOLCHAIN_VERSION_VALID!"=="1" @set "TOOLS_TOOLCHAIN_FILE_VALID=0"
@if not "!TOOLS_TOOLCHAIN_FILE_VALID!"=="1" (
  @echo Expected one canonical [toolchain] channel ^
    in tools\rust-toolchain.toml >&2
  @popd
  @exit /b 1
)

@rem Build `cargo-zerocopy` without output overrides from the environment. The
@rem explicit toolchain pins the outer Cargo invocation; export that same pin
@rem so nested Cargo or build-script children cannot recover the caller's
@rem override. Endlocal restores all three variables before cargo-zerocopy.
@set "RUSTFLAGS="
@set "CARGO_TARGET_DIR="
@set "RUSTUP_TOOLCHAIN=!TOOLS_TOOLCHAIN!"
@cargo +!TOOLS_TOOLCHAIN! build --locked --manifest-path Cargo.toml -p cargo-zerocopy -q
@set "CARGO_ZEROCOPY_BUILD_STATUS=!ERRORLEVEL!"
@popd
@endlocal & @set "CARGO_ZEROCOPY_BUILD_STATUS=%CARGO_ZEROCOPY_BUILD_STATUS%"
@if not "%CARGO_ZEROCOPY_BUILD_STATUS%"=="0" exit /b %CARGO_ZEROCOPY_BUILD_STATUS%
@rem Thin wrapper around the `cargo-zerocopy` binary in `tools/cargo-zerocopy`
@rem Keep this working directory coordinated with cargo-zerocopy's `ci` route,
@rem tools\zc\src\cli.rs, and zerocopy\cargo.sh. The typed CI commands pass `..`
@rem as the repository root, so both wrappers must run from this directory.
@pushd "%~dp0"
@if errorlevel 1 exit /b 1
@..\tools\target\debug\cargo-zerocopy %*
@set "CARGO_ZEROCOPY_STATUS=%ERRORLEVEL%"
@popd
@endlocal & @exit /b %CARGO_ZEROCOPY_STATUS%
