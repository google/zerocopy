#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Install host packages without allowing a transient apt or mirror failure to
# occupy a hosted runner indefinitely. This helper is only for idempotent CI
# setup; build and test commands must stay outside its retry boundary.

set -euo pipefail

if [[ $# -eq 0 ]]; then
    echo "usage: $0 PACKAGE [PACKAGE ...]" >&2
    exit 2
fi

# Accept package names, not arbitrary apt expressions. Keeping the interface
# this narrow makes workflow call sites easy to audit and prevents a future
# matrix value from becoming an apt option or version-policy override.
for package in "$@"; do
    if [[ ! "$package" =~ ^[a-z0-9][a-z0-9+.-]*(:[a-z0-9][a-z0-9-]*)?$ ]]; then
        echo "$0: invalid Debian package name: $package" >&2
        exit 2
    fi
done

readonly max_attempts=3
readonly update_timeout=120s
readonly install_timeout=300s
readonly kill_grace=10s

# apt's own acquisition timeouts bound individual network operations, while
# GNU timeout bounds the complete command, including DNS, mirror fallback,
# lock acquisition, maintainer scripts, and any failure mode apt does not know
# how to time out itself. The outer bound is what prevents the six-hour hangs
# this helper was introduced to address.
readonly -a apt_options=(
    -o Acquire::Retries=2
    -o Acquire::http::Timeout=30
    -o Acquire::https::Timeout=30
    -o DPkg::Lock::Timeout=60
)

run_apt() {
    local command_timeout="$1"
    shift
    sudo timeout --kill-after="$kill_grace" "$command_timeout" \
        env DEBIAN_FRONTEND=noninteractive \
        apt-get "${apt_options[@]}" "$@"
}

for ((attempt = 1; attempt <= max_attempts; attempt++)); do
    if run_apt "$update_timeout" update; then
        if run_apt "$install_timeout" \
            --yes --no-install-recommends install -- "$@"; then
            exit 0
        else
            status=$?
        fi
    else
        status=$?
    fi

    if [[ $attempt -eq $max_attempts ]]; then
        echo "$0: apt setup failed after $max_attempts attempts" >&2
        exit "$status"
    fi

    # Use a short then longer jittered delay so simultaneous runner failures do
    # not immediately stampede the same mirror. These are the only sleeps and
    # retries in this helper; a successful install returns immediately.
    if [[ $attempt -eq 1 ]]; then
        delay=$((5 + RANDOM % 11))
    else
        delay=$((15 + RANDOM % 16))
    fi
    echo "$0: apt setup attempt $attempt failed; retrying in ${delay}s" >&2
    sleep "$delay"
done
