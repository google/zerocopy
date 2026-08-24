#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -eo pipefail
cd "$(dirname "$0")/../tools"

# shellcheck source=../tools/toolchain.sh
source ./toolchain.sh

# The stable-toolchain roller intentionally updates these two files together.
# Check the copy here as well so a hand edit cannot make local tool builds use
# a different compiler from the stable CI lane. Require one exact declaration
# in each file; a future reorganization must update this check explicitly.
# `tools/cargo.sh` and `zerocopy/win-cargo.bat` also parse the tools channel so
# they can defeat persisted rustup directory overrides. The Unix scripts share
# `tools/toolchain.sh`; keep its exact format coordinated with the independent
# batch parser. A pre-existing Windows worktree may still contain CRLF TOML, so
# the bootstrap parser accepts well-formed CRLF but rejects bare CR.
#
# Store the parser output before comparing the two pins. Do not use `mapfile`:
# macOS still ships Bash 3.2, which does not provide that builtin.
if ! TOOLS_CHANNEL="$(
  zc_read_exact_rust_version_assignment rust-toolchain.toml toolchain channel
)"; then
  echo "Expected one canonical [toolchain] channel" \
    "in tools/rust-toolchain.toml" >&2
  exit 1
fi
if ! STABLE_CHANNEL="$(
  zc_read_exact_rust_version_assignment \
    ../zerocopy/Cargo.toml package.metadata.ci pinned-stable
)"; then
  echo "Expected one canonical [package.metadata.ci] pinned-stable" \
    "in zerocopy/Cargo.toml" >&2
  exit 1
fi
if [[ -z "$TOOLS_CHANNEL" || "$TOOLS_CHANNEL" == *$'\n'* || \
      -z "$STABLE_CHANNEL" || "$STABLE_CHANNEL" == *$'\n'* ]]; then
  echo "Expected one tools channel and one Zerocopy stable channel" >&2
  exit 1
fi
if [[ "$TOOLS_CHANNEL" != "$STABLE_CHANNEL" ]]; then
  echo "Tools compiler $TOOLS_CHANNEL does not match Zerocopy stable" \
    "compiler $STABLE_CHANNEL" >&2
  exit 1
fi

# Exercise the bootstrap parser independently of this checkout. Existing
# Git-for-Windows worktrees can retain CRLF after pulling `.gitattributes`, but
# every table and assignment choice is otherwise a strict coordination
# contract. Keep these hostile fixtures synchronized with `tools/toolchain.sh`
# and the independent live-file parser in `zerocopy/win-cargo.bat`.
#
# The parser opens its input twice so it can detect NUL before Bash `read`
# discards that byte. Materialize each fixture instead of piping through
# /dev/stdin; production callers likewise provide ordinary repository files.
TOOLS_CHANNEL_FIXTURE_DIR="$(mktemp -d)"
TOOLS_CHANNEL_FIXTURE="$TOOLS_CHANNEL_FIXTURE_DIR/rust-toolchain.toml"
cleanup_tools_channel_fixture() {
  rm -f "$TOOLS_CHANNEL_FIXTURE"
  rmdir "$TOOLS_CHANNEL_FIXTURE_DIR"
}
trap cleanup_tools_channel_fixture EXIT

write_tools_channel_fixture() {
  printf '%s' "$1" > "$TOOLS_CHANNEL_FIXTURE"
}

write_tools_channel_fixture $'# channel = "ignored"\n[toolchain]\nchannel = "1.2.3"\n'
if ! PARSED_LF_CHANNEL="$(
  zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" toolchain channel
)" || [[ "$PARSED_LF_CHANNEL" != "1.2.3" ]]; then
  echo "Tools channel parser rejected a canonical LF declaration" >&2
  exit 1
fi
write_tools_channel_fixture \
  $'[toolchain]\r\nchannel = "1.2.3"\r\nnote = "write \\"unsafe\\""\r\nprofile = "minimal"\r\n'
if ! PARSED_CRLF_CHANNEL="$(
  zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" toolchain channel
)" || [[ "$PARSED_CRLF_CHANNEL" != "1.2.3" ]]; then
  echo "Tools channel parser rejected a canonical CRLF declaration" >&2
  exit 1
fi

CANONICAL_TOOLCHAIN=$'[toolchain]\nchannel = "1.2.3"\n'

# A quoted key containing a literal dot is one TOML component, not a dotted
# path. Keep this accepted fixture coordinated with the segment-aware alias
# check in `tools/toolchain.sh`; flattening quotes before comparison would
# incorrectly reject this unrelated table.
write_tools_channel_fixture \
  "${CANONICAL_TOOLCHAIN}"$'["toolchain.unrelated"]\nnote = "accepted"\n'
if ! PARSED_LITERAL_DOT_CHANNEL="$(
  zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" toolchain channel
)" || [[ "$PARSED_LITERAL_DOT_CHANNEL" != "1.2.3" ]]; then
  echo "Tools channel parser confused a literal dot with a dotted key" >&2
  exit 1
fi

expect_tools_channel_rejected() {
  local description="$1"
  local source="$2"
  write_tools_channel_fixture "$source"
  if zc_read_exact_rust_version_assignment \
      "$TOOLS_CHANNEL_FIXTURE" toolchain channel >/dev/null; then
    echo "Tools channel parser accepted $description" >&2
    return 1
  fi
}

expect_tools_channel_rejected "an assignment without its table" \
  $'channel = "1.2.3"\n'
expect_tools_channel_rejected "an assignment in the wrong table" \
  $'[other]\nchannel = "1.2.3"\n'
expect_tools_channel_rejected "a noncanonical table header" \
  $'[ toolchain ]\nchannel = "1.2.3"\n'
expect_tools_channel_rejected "a duplicate table" \
  "${CANONICAL_TOOLCHAIN}"$'[toolchain]\n'
expect_tools_channel_rejected "a duplicate assignment" \
  "${CANONICAL_TOOLCHAIN}"$'channel = "4.5.6"\n'
expect_tools_channel_rejected "a compact assignment" \
  "${CANONICAL_TOOLCHAIN}"$'channel="4.5.6"\n'
expect_tools_channel_rejected "a leading-space assignment" \
  "${CANONICAL_TOOLCHAIN}"$' channel = "4.5.6"\n'
expect_tools_channel_rejected "a trailing-space assignment" \
  "${CANONICAL_TOOLCHAIN}"$'channel = "4.5.6" \n'
expect_tools_channel_rejected "an assignment with an inline comment" \
  "${CANONICAL_TOOLCHAIN}"$'channel = "4.5.6" # duplicate authority\n'
expect_tools_channel_rejected "a nonnumeric channel" \
  "${CANONICAL_TOOLCHAIN}"$'channel = "nightly"\n'
expect_tools_channel_rejected "a quoted channel key" \
  "${CANONICAL_TOOLCHAIN}"$'"channel" = "4.5.6"\n'
expect_tools_channel_rejected "a channel key with a short Unicode escape" \
  "${CANONICAL_TOOLCHAIN}"$'"\\u0063hannel" = "4.5.6"\n'
expect_tools_channel_rejected "a channel key with a long Unicode escape" \
  "${CANONICAL_TOOLCHAIN}"$'"\\U00000063hannel" = "4.5.6"\n'
expect_tools_channel_rejected "an escaped duplicate table" \
  "${CANONICAL_TOOLCHAIN}"$'["tool\\u0063hain"]\n'
expect_tools_channel_rejected "a dotted channel assignment" \
  "${CANONICAL_TOOLCHAIN}"$'[other]\ntoolchain.channel = "4.5.6"\n'
expect_tools_channel_rejected "an inline-table channel assignment" \
  "${CANONICAL_TOOLCHAIN}"$'other = {channel = "4.5.6"}\n'
expect_tools_channel_rejected "a duplicate noncanonical table" \
  "${CANONICAL_TOOLCHAIN}"$'[ toolchain ]\n'
expect_tools_channel_rejected "a duplicate double-quoted table" \
  "${CANONICAL_TOOLCHAIN}"$'["toolchain"]\n'
expect_tools_channel_rejected "a duplicate single-quoted table" \
  "${CANONICAL_TOOLCHAIN}"$"['toolchain']\n"
expect_tools_channel_rejected "a conflicting quoted array table" \
  "${CANONICAL_TOOLCHAIN}"$'[["toolchain"]]\n'
expect_tools_channel_rejected "an assignment after leaving its table" \
  "${CANONICAL_TOOLCHAIN}"$'[other]\nchannel = "4.5.6"\n'
expect_tools_channel_rejected "an assignment inside a multiline string" \
  $'[toolchain]\nnote = """\nchannel = "9.9.9"\n"""\n'
expect_tools_channel_rejected "a table inside a multiline literal string" \
  $'[other]\nnote = \047\047\047\n[toolchain]\nchannel = "9.9.9"\n\047\047\047\n'
expect_tools_channel_rejected "an unterminated bare CR" \
  "${CANONICAL_TOOLCHAIN}"$'profile = "minimal"\r'
expect_tools_channel_rejected "an embedded bare CR" \
  "${CANONICAL_TOOLCHAIN}"$'profile = "mini\rmal"\n'
expect_tools_channel_rejected "an unterminated declaration" \
  "${CANONICAL_TOOLCHAIN}"$'profile = "minimal"'

# Exercise a dotted expected path independently. TOML permits a different key
# spelling for every component, so a mixed quoted/bare duplicate must not
# evade the same one-table contract. Conversely, quotes can make a dot literal
# inside one component; those unrelated paths must remain accepted.
CANONICAL_CI_METADATA=$'[package.metadata.ci]\npinned-stable = "1.2.3"\n'
write_tools_channel_fixture \
  "${CANONICAL_CI_METADATA}"$'[ "package" . metadata . \047ci\047 ] # duplicate\n'
if zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" package.metadata.ci pinned-stable \
    >/dev/null; then
  echo "Tools channel parser accepted a mixed-quoted duplicate table" >&2
  exit 1
fi
write_tools_channel_fixture \
  "${CANONICAL_CI_METADATA}"$'["package.metadata.ci"]\n[package."metadata.ci"]\n[target.\047cfg(any())\047.dependencies]\n'
if ! PARSED_LITERAL_DOT_METADATA="$(
  zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" package.metadata.ci pinned-stable
)" || [[ "$PARSED_LITERAL_DOT_METADATA" != "1.2.3" ]]; then
  echo "Tools channel parser confused quoted dotted components with a path" >&2
  exit 1
fi

printf '[toolchain]\nchannel = "1.2' > "$TOOLS_CHANNEL_FIXTURE"
printf '\0' >> "$TOOLS_CHANNEL_FIXTURE"
printf '.3"\n' >> "$TOOLS_CHANNEL_FIXTURE"
if zc_read_exact_rust_version_assignment \
    "$TOOLS_CHANNEL_FIXTURE" toolchain channel >/dev/null; then
  echo "Tools channel parser accepted a NUL byte" >&2
  exit 1
fi

if zc_read_exact_rust_version_assignment \
    /dev/null/missing toolchain channel \
    >/dev/null 2>&1; then
  echo "Tools channel parser accepted an input it could not open" >&2
  exit 1
fi

# RUSTUP_TOOLCHAIN overrides tools/rust-toolchain.toml. Use an intentionally
# invalid value to prove that the Unix wrapper's explicit pin defeats this
# ambient override while it builds cargo-zerocopy, then reports the configured
# stable version.
WRAPPER_STABLE="$(
  RUSTUP_TOOLCHAIN=zerocopy-ci-intentionally-invalid \
    ../zerocopy/cargo.sh --version stable
)"
if [[ "$WRAPPER_STABLE" != "$STABLE_CHANNEL" ]]; then
  echo "cargo.sh resolved stable to $WRAPPER_STABLE, expected $STABLE_CHANNEL" \
    >&2
  exit 1
fi

# Prove that the shared Unix wrapper defeats an ambient rustup override. Keep
# the lockfile read-only: repository tools are part of CI's trusted setup, so
# an unreviewed dependency change must never be created as a side effect of
# testing them.
RUSTUP_TOOLCHAIN=zerocopy-ci-intentionally-invalid \
  ./cargo.sh test --locked --workspace
