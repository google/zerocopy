#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Shared bootstrap parser for one exact Rust-version assignment in one exact
# TOML table. This code runs before the typed Rust audit can normalize
# repository text, so it accepts LF and well-formed CRLF directly. A carriage
# return in any other position, including an unterminated final line, fails
# closed.
#
# Keep the two callers (`cargo.sh` and `../ci/check_tools.sh`) coordinated with
# the independent parser in `../zerocopy/win-cargo.bat`. The table and key
# arguments are fixed repository constants, not user input. This is
# intentionally a narrow recognizer rather than a partial TOML parser: any
# alternate spelling of the target assignment must fail and force the
# bootstrap contract to be updated deliberately.
zc_read_exact_rust_version_assignment() {
  if [[ $# -ne 3 ]]; then
    return 2
  fi

  local path="$1"
  local expected_table="$2"
  local key="$3"
  local line=""
  local normalized
  local compact_header
  local expected_header="[$expected_table]"
  local expected_table_count=0
  local in_expected_table=0
  local assignment_count=0
  local prefix="$key = \""
  local suffix='"'
  local assignment_ere="(^|[.{,[:space:]])[\"']?$key[\"']?[[:space:]]*="
  local version
  local selected_version=""
  local rust_version_ere='^[0-9]+\.[0-9]+\.[0-9]+$'

  # Reject an unavailable input before entering the loop so callers receive a
  # useful status rather than an empty, apparently successful result. The
  # conditional around the loop also preserves a redirection failure if the
  # file becomes unavailable between this check and opening it.
  [[ -r "$path" ]] || return 1

  # Bash `read` silently removes NUL bytes. Detect one before the line parser
  # can turn a noncanonical file into canonical-looking text. All callers pass
  # reopenable repository or fixture paths: this preflight and the loop below
  # deliberately open the file independently.
  if IFS= read -r -d '' normalized < "$path"; then
    return 1
  fi
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

    if [[ -z "$normalized" || "$normalized" =~ ^[[:space:]]*# ]]; then
      continue
    fi

    # A line-oriented recognizer cannot distinguish apparent tables or
    # assignments inside TOML multiline strings. Neither coordinated input
    # needs multiline strings today, so reject both delimiter forms. If one is
    # introduced later, replace this recognizer with a parser which tracks TOML
    # string state rather than letting embedded text gain bootstrap authority.
    if [[ "$normalized" == *'"""'* || "$normalized" == *"'''"* ]]; then
      return 1
    fi

    # A table header with any alternate spacing is deliberately not the
    # expected canonical header. It still leaves the expected table so an
    # exact-looking assignment beneath another table cannot be accepted.
    if [[ "$normalized" =~ ^[[:space:]]*\[ ]]; then
      if [[ "$normalized" == "$expected_header" ]]; then
        expected_table_count=$((expected_table_count + 1))
        [[ $expected_table_count -eq 1 ]] || return 1
        in_expected_table=1
      else
        compact_header="${normalized//[[:space:]]/}"
        if [[ "$compact_header" == "$expected_header" || \
              "$compact_header" == "$expected_header"#* ]]; then
          return 1
        fi
        in_expected_table=0
      fi
      continue
    fi

    if [[ "$normalized" == "$prefix"*"$suffix" ]]; then
      version="${normalized#"$prefix"}"
      version="${version%"$suffix"}"
      [[ $in_expected_table -eq 1 ]] || return 1
      [[ "$version" =~ $rust_version_ere ]] || return 1
      assignment_count=$((assignment_count + 1))
      [[ $assignment_count -eq 1 ]] || return 1
      selected_version="$version"
      continue
    fi

    # Catch compact, spaced, quoted, dotted, and inline-table spellings of the
    # same key.
    # False positives are intentionally fail-closed: if a future TOML value
    # needs to contain assignment-like text, update this bootstrap grammar and
    # its hostile fixtures together.
    if [[ "$normalized" =~ $assignment_ere ]]; then
      return 1
    fi
  done < "$path"; then
    return 1
  fi

  [[ $expected_table_count -eq 1 && $assignment_count -eq 1 ]] || return 1
  printf '%s' "$selected_version"
}
