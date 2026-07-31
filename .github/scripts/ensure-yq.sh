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

script_name=".github/scripts/ensure-yq.sh"
yq_version=4.44.1

# ci.yml supplies YQ_VERSION to every hosted installation. Local hooks do not,
# so this script also owns the default. Reject a hosted mismatch in either
# direction instead of silently running different YAML parsers in different
# policy checks.
if [ -n "${YQ_VERSION:-}" ] && [ "$YQ_VERSION" != "$yq_version" ]; then
    echo "$script_name: YQ_VERSION must match the v$yq_version helper pin" >&2
    exit 1
fi

yq_expected_version="yq (https://github.com/mikefarah/yq/) version v$yq_version"
yq_bin="${YQ:-}"
if [ -z "$yq_bin" ]; then
    yq_bin="$(command -v yq || true)"
fi
if [ -n "$yq_bin" ] && \
    [ "$("$yq_bin" --version 2>/dev/null || true)" != "$yq_expected_version" ]; then
    if [ -n "${YQ:-}" ]; then
        echo "$script_name: YQ must be mikefarah/yq v$yq_version" >&2
        exit 1
    fi
    yq_bin=""
fi

sha256_file() {
    if command -v sha256sum >/dev/null; then
        sha256sum "$1" | cut -d ' ' -f 1
    elif command -v shasum >/dev/null; then
        shasum -a 256 "$1" | cut -d ' ' -f 1
    else
        echo "$script_name: sha256sum or shasum is required" >&2
        return 1
    fi
}

if [ -z "$yq_bin" ]; then
    # These are SHA-256 values for the uncompressed binaries in the checksum
    # manifest attached to the v4.44.1 release. A yq upgrade must update the
    # version, URLs, and all four hashes together.
    case "$(uname -s)/$(uname -m)" in
        Linux/x86_64)
            yq_platform=linux_amd64
            yq_sha256=6dc2d0cd4e0caca5aeffd0d784a48263591080e4a0895abe69f3a76eb50d1ba3
            ;;
        Linux/aarch64 | Linux/arm64)
            yq_platform=linux_arm64
            yq_sha256=8c12fcc10e14774ca6624cc282f092a526568b036fe1192258c3aecbad56d063
            ;;
        Darwin/x86_64)
            yq_platform=darwin_amd64
            yq_sha256=114d0fab983929a76b39d792dea339b07631e0fb2f195d9e43815f907308e309
            ;;
        Darwin/arm64)
            yq_platform=darwin_arm64
            yq_sha256=638ea9b4e7a89e12159e5077556f0d10559b49df3ec67504dd2a567fec2bb47e
            ;;
        *)
            echo "$script_name: yq v$yq_version has no pinned binary for $(uname -s)/$(uname -m)" >&2
            exit 1
            ;;
    esac

    yq_dir="${XDG_CACHE_HOME:-$HOME/.cache}/zerocopy/yq-v$yq_version-$yq_platform"
    yq_bin="$yq_dir/yq"
    yq_actual_sha256=""
    if [ -f "$yq_bin" ]; then
        yq_actual_sha256="$(sha256_file "$yq_bin")"
    fi
    if [ "$yq_actual_sha256" != "$yq_sha256" ]; then
        if ! command -v curl >/dev/null; then
            echo "$script_name: curl is required to install yq" >&2
            exit 1
        fi

        echo "$script_name: yq not found, installing..." >&2
        yq_tmp="$(mktemp -d "${TMPDIR:-/tmp}/zerocopy-yq.XXXXXXXX")"
        trap 'rm -rf "$yq_tmp"' EXIT
        yq_download="$yq_tmp/yq"
        curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
            --connect-timeout 15 --max-time 30 \
            --retry 5 --retry-all-errors --retry-max-time 60 \
            --output "$yq_download" \
            "https://github.com/mikefarah/yq/releases/download/v${yq_version}/yq_${yq_platform}"
        yq_actual_sha256="$(sha256_file "$yq_download")"
        if [ "$yq_actual_sha256" != "$yq_sha256" ]; then
            echo "$script_name: yq checksum mismatch: expected $yq_sha256, got $yq_actual_sha256" >&2
            exit 1
        fi

        mkdir -p "$yq_dir"
        yq_candidate="$yq_dir/.yq.$$"
        install -m 0755 "$yq_download" "$yq_candidate"
        mv -f "$yq_candidate" "$yq_bin"
        rm -rf "$yq_tmp"
        trap - EXIT
    fi
fi

printf '%s\n' "$yq_bin"
