#!/bin/bash
#
# Copyright 2023 The Fuchsia Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

# Usage: `pkg-meta <crate-name> <selector>`
#
# Extracts metadata from zerocopy's `Cargo.toml` file.
function pkg-meta {
    if [[ $# != 2 ]]; then
        echo "Usage: pkg-meta <crate-name> <selector>" >&2
        return 1
    fi
    cargo metadata --no-deps --format-version 1 | jq -r ".packages[] | select(.name == \"$1\").$2"
}

# Usage: `msrv <crate-name>`
#
# Extracts the `rust_version` package metadata key.
function msrv {
    if [[ $# != 1 ]]; then
        echo "Usage: msrv <crate-name>" >&2
        return 1
    fi
    pkg-meta $1 rust_version
}

# Usage: `version <crate-name>`
#
# Extracts the `version` mackage metadata key.
function version {
    if [[ $# != 1 ]]; then
        echo "Usage: version <crate-name>" >&2
        return 1
    fi
    pkg-meta $1 version
}

# Usage: `get-toolchain-by-name <toolchain-name>`
#
# Gets the real toolchain descriptor based on its human-readable name ("msrv",
# "stable", or "nightly").
function get-toolchain-by-name {
    if [[ $# != 1 ]]; then
        echo "Usage: get-toolchain-by-name <toolchain-name>" >&2
        return 1
    fi

    case "$1" in
        msrv)
            echo "$(pkg-meta zerocopy rust_version)"
            return 0
        ;;
        stable)
            echo "$(pkg-meta zerocopy 'metadata.ci."pinned-stable"')"
            return 0
        ;;
        nightly)
            echo "$(pkg-meta zerocopy 'metadata.ci."pinned-nightly"')"
            return 0
        ;;
        *)
            echo "Unrecognized toolchain: $1" >&2
            return 1
        ;;
    esac
}

function test-check {
    if [[ $# != 5 && ($# != 6 || "$6" != "--verbose") ]]; then
        echo "Usage: test-check <toolchain-name> <toolchain> <crate> <target> <features> [--verbose]" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"
    VERBOSE="$6"

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    #
    # Note that we don't quote `$VERBOSE` since it may be empty, in which case
    # we need it to not result in an empty string being passed as a separate
    # arguemnt.
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    cargo "+$TOOLCHAIN" check --package "$CRATE" --target "$TARGET" $FEATURES --tests $VERBOSE
}

function test-build {
    if [[ $# != 5 && ($# != 6 || "$6" != "--verbose") ]]; then
        echo "Usage: test-build <toolchain-name> <toolchain> <crate> <target> <features> [--verbose]" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"
    VERBOSE="$6"

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    #
    # Note that we don't quote `$VERBOSE` since it may be empty, in which case
    # we need it to not result in an empty string being passed as a separate
    # arguemnt.
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    cargo "+$TOOLCHAIN" build --package "$CRATE" --target "$TARGET" $FEATURES $VERBOSE
}

function test-tests {
    if [[ $# != 5 && ($# != 6 || "$6" != "--verbose") ]]; then
        echo "Usage: test-tests <toolchain-name> <toolchain> <crate> <target> <features> [--verbose]" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"
    VERBOSE="$6"

    # Only run tests when targetting x86 (32- or 64-bit) - we're executing on
    # x86_64, so we can't run tests for any non-x86 target.
    #
    # TODO(https://github.com/dtolnay/trybuild/issues/184#issuecomment-1269097742):
    # Run compile tests when building for other targets.
    if [[ !("$TARGET" =~ 'x86_64' || "$TARGET" =~ 'i686') ]]; then
        echo "Not targetting x86 or x86_64; skipping..." >&2
        return 0
    fi

    if [[ ! ("$OSTYPE" =~ 'linux') ]]; then
        echo "Running tests from an operating system other than Linux is not supported; skipping..." >&2
        return 0
    fi

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    #
    # Note that we don't quote `$VERBOSE` since it may be empty, in which case
    # we need it to not result in an empty string being passed as a separate
    # arguemnt.
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    TARGET_CC="$TARGET" cargo "+$TOOLCHAIN" test --package "$CRATE" --target "$TARGET" $FEATURES $VERBOSE
}

function test-miri {
    if [[ $# != 5 && ($# != 6 || "$6" != "--verbose") ]]; then
        echo "Usage: test-miri <toolchain-name> <toolchain> <crate> <target> <features> [--verbose]" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"
    VERBOSE="$6"

    # Only nightly has a working Miri, so we skip installing on all other
    # toolchains.
    #
    # TODO(#22): Re-enable testing on wasm32-wasi once it works.
    if [[ "$TOOLCHAIN_NAME" != 'nightly' || "$TARGET" == 'wasm32-wasi' ]]; then
        return 0
    fi

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    #
    # Note that we don't quote `$VERBOSE` since it may be empty, in which case
    # we need it to not result in an empty string being passed as a separate
    # arguemnt.
    #
    # Skip the `ui` test since it invokes the compiler, which we can't do from
    # Miri (and wouldn't want to do anyway).
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    cargo "+$TOOLCHAIN" miri test --package "$CRATE" --target "$TARGET" $FEATURES $VERBOSE -- --skip ui
}

function test-clippy {
    if [[ $# != 5 && ($# != 6 || "$6" != "--verbose") ]]; then
        echo "Usage: test-clippy <toolchain-name> <toolchain> <crate> <target> <features> [--verbose]" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"
    VERBOSE="$6"

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    #
    # Note that we don't quote `$VERBOSE` since it may be empty, in which case
    # we need it to not result in an empty string being passed as a separate
    # arguemnt.
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    cargo "+$TOOLCHAIN" clippy --package "$CRATE" --target "$TARGET" $FEATURES --tests $VERBOSE
}

function test-doc {
    if [[ $# != 5 ]]; then
        echo "Usage: test-doc <toolchain-name> <toolchain> <crate> <target> <features>" >&2
        return 1
    fi

    TOOLCHAIN_NAME="$1"
    TOOLCHAIN="$2"
    CRATE="$3"
    TARGET="$4"
    FEATURES="$5"

    # When the `alloc` feature is disabled, `cargo doc` fails because we link to
    # `alloc::vec::Vec` in a doc comment, and the `alloc` crate is not in scope
    # without the `alloc` feature. This isn't a big deal because we care
    # primarily about `cargo doc` working for `docs.rs`, which enables the
    # `alloc` feature.
    if [[ "$FEATURES" == '' || "$FEATURES" == '--no-default-features' ]]; then
        return 0
    fi

    # Note that we don't quote `$FEATURES` since it sometimes needs to expand to
    # multiple arguments (the `--features` flag followed by the name of a
    # feature).
    ensure-toolchain-target-installed "$TOOLCHAIN" "$TARGET" && \
    cargo "+$TOOLCHAIN" doc --package "$CRATE" $FEATURES
}

function test-check-fmt {
    ROOT=$(git rev-parse --show-toplevel)                       && \
    cargo fmt --check --package zerocopy                        && \
    cargo fmt --check --package zerocopy-derive                 && \
    rustfmt --check $ROOT/tests/ui-nightly/*.rs                 && \
    rustfmt --check $ROOT/zerocopy-derive/tests/ui-nightly/*.rs
}

function test-check-readme {
    ROOT=$(git rev-parse --show-toplevel)            && \
    # TODO: Factor this out so that we can install in CI but
    # check-and-offer-to-install in development.
    # cargo install cargo-readme --version 3.2.0       && \
    diff <($ROOT/generate-readme.sh) $ROOT/README.md
}

# Make sure that the MSRV in zerocopy's and zerocopy-derive's `Cargo.toml` files
# are the same.
function test-check-msrvs {
    ver_zerocopy=$(msrv zerocopy)               && \
    ver_zerocopy_derive=$(msrv zerocopy-derive) && \

    if [[ "$ver_zerocopy" == "$ver_zerocopy_derive" ]]; then
        echo "Same MSRV ($ver_zerocopy) found for zerocopy and zerocopy-derive."
        true
    else
        echo "Different MSRVs found for zerocopy ($ver_zerocopy) and zerocopy-derive ($ver_zerocopy_derive)."
        false
    fi
}

# Make sure that both crates are at the same version, and that zerocopy depends
# exactly upon the current version of zerocopy-derive. See `INTERNAL.md` for an
# explanation of why we do this.
function test-check-versions {
    ver_zerocopy=$(version zerocopy)                               && \
    ver_zerocopy_derive=$(version zerocopy-derive)                 && \
    zerocopy_derive_dep_ver=$(pkg-meta zerocopy \
        'dependencies[] | select(.name == "zerocopy-derive").req') && \

    if [[ "$ver_zerocopy" == "$ver_zerocopy_derive" ]]; then
        echo "Same crate version ($ver_zerocopy) found for zerocopy and zerocopy-derive."
    else
        echo "Different crate versions found for zerocopy ($ver_zerocopy) and zerocopy-derive ($ver_zerocopy_derive)."
        false
    fi && \

    # Note the leading `=` sign - the dependency needs to be an exact one.
    if [[ "$zerocopy_derive_dep_ver" == "=$ver_zerocopy_derive" ]]; then
        echo "zerocopy depends upon same version of zerocopy-derive in-tree ($zerocopy_derive_dep_ver)."
    else
        echo "zerocopy depends upon different version of zerocopy-derive ($zerocopy_derive_dep_ver) than the one in-tree ($ver_zerocopy_derive)."
        false
    fi
}

# Usage: `run-test-in-github-action <test-function> [<test-arg>...]`
#
# Runs the named test function with optional arguments, piping the output to the
# appropriate locations and exiting with the return code of the function.
function run-test-in-github-action {
    if [[ $# == 0 ]]; then
        echo "Usage: run-test-in-github-action <test-function> [<test-arg>...]" >&2
        return 1
    fi

    OUTPUT="$($@)"
    RESULT=$?
    echo "$OUTPUT" | tee -a $GITHUB_STEP_SUMMARY >&2
    exit $RESULT
}

# Usage: `ensure-toolchain-target-installed <toolchain> <target>`
#
# Verifies that the given toolchain/target combination is installed; if it
# isn't, an error message is printed to stderr, and the user is prompted to
# install the missing toolchain or target. `<target>` must not contain any regex
# meta-characters, as it is passed to `grep`.
function ensure-toolchain-target-installed {
    if [[ $# != 2 ]]; then
        echo "Usage: ensure-toolchain-target-installed <toolchain> <target>" >&2
        return 1
    fi

    TOOLCHAIN="$1"
    TARGET="$2"

    ( \
        rustup run "$TOOLCHAIN" true || \
        prompt-user "Would you like to install $TOOLCHAIN via rustup?" 1 "rustup install $TOOLCHAIN" \
    ) && \
    if ! rustup "+$TOOLCHAIN" target list | grep "^$TARGET (installed)$" > /dev/null; then
        echo "Target $TARGET not installed for toolchain $TOOLCHAIN" >&2
        prompt-user "Would you like to install $TARGET via rustup?" 1 "rustup +$TOOLCHAIN target add $TARGET"
    fi
}

# Usage: `prompt-user <prompt> <default-return-code> <command> [<command-arg>...]`
#
# Prompts the user to approve an action, running the action if the user accepts.
function prompt-user {
    if [[ $# < 3 ]]; then
        echo "Usage: prompt-user <prompt> <default-return-code> <command> [<command-arg>...]" >&2
        return 1
    fi

    PROMPT="$1"
    DEFAULT_RETURN_CODE="$2"
    COMMAND="${@:3}"

    while true; do
        echo -n "$PROMPT (y/n) "
        read answer

        case "$answer" in
            y)
                $COMMAND
                return $?
            ;;
            n)
                return "$DEFAULT_RETURN_CODE"
            ;;
            *)
                echo "Unrecognized response: $answer" >&2
            ;;
        esac
    done
}
