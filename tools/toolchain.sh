#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Shared bootstrap parser for exact Rust-version assignments in repository
# TOML. This code runs before the typed Rust audit can normalize repository
# text, so it accepts LF and well-formed CRLF directly. A carriage return in
# any other position, including an unterminated final line, fails closed.
#
# Keep the two callers (`cargo.sh` and `../ci/check_tools.sh`) coordinated with
# the independent parser in `../zerocopy/win-cargo.bat`. The key argument is a
# fixed repository constant, not user input.
zc_read_exact_rust_version_assignment() {
  if [[ $# -ne 2 ]]; then
    return 2
  fi

  local path="$1"
  local key="$2"
  local line=""
  local normalized
  local prefix="$key = \""
  local suffix='"'
  local version
  local versions=""
  local rust_version_ere='^[0-9]+\.[0-9]+\.[0-9]+$'

  # Reject an unavailable input before entering the loop so callers receive a
  # useful status rather than an empty, apparently successful result. The
  # conditional around the loop also preserves a redirection failure if the
  # file becomes unavailable between this check and opening it.
  [[ -r "$path" ]] || return 1
  if ! while true; do
    line=""
    if IFS= read -r line; then
      :
    elif [[ -n "$line" ]]; then
      # `read` saw bytes without a terminating LF. In particular, do not
      # mistake a final bare CR for the end of a CRLF record.
      return 1
    else
      break
    fi

    case "$line" in
      *$'\r')
        normalized="${line%$'\r'}"
        # Removing the one CR which belongs to CRLF must leave no other CR.
        [[ "$normalized" != *$'\r'* ]] || return 1
        ;;
      *$'\r'*)
        return 1
        ;;
      *)
        normalized="$line"
        ;;
    esac

    if [[ "$normalized" == "$prefix"*"$suffix" ]]; then
      version="${normalized#"$prefix"}"
      version="${version%"$suffix"}"
      if [[ "$version" =~ $rust_version_ere ]]; then
        if [[ -n "$versions" ]]; then
          versions+=$'\n'
        fi
        versions+="$version"
      fi
    fi
  done < "$path"; then
    return 1
  fi

  printf '%s' "$versions"
}
