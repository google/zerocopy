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
  local expected_header="[$expected_table]"
  local expected_table_path_ere=""
  local expected_table_header_ere
  local expected_array_table_header_ere
  local separator=""
  local part
  local -a expected_table_parts
  local expected_table_count=0
  local in_expected_table=0
  local assignment_count=0
  local prefix="$key = \""
  local suffix='"'
  local assignment_ere="(^|[.{,[:space:]])[\"']?$key[\"']?[[:space:]]*="
  local unicode_escape_ere='\\(u[[:xdigit:]]{4}|U[[:xdigit:]]{8})'
  local version
  local selected_version=""
  local rust_version_ere='^[0-9]+\.[0-9]+\.[0-9]+$'

  # These values are fixed repository constants, but they are interpolated
  # into regular expressions below. Reject an accidental future caller which
  # would give punctuation regex meaning instead of silently widening the
  # bootstrap grammar.
  [[ "$expected_table" =~ ^[A-Za-z0-9_-]+(\.[A-Za-z0-9_-]+)*$ ]] || return 2
  [[ "$key" =~ ^[A-Za-z0-9_-]+$ ]] || return 2

  # TOML permits each component of a dotted key to be bare, basic quoted, or
  # literal quoted. Build the exact semantic spelling of the expected path so
  # quoted aliases are rejected without confusing a literal dot inside one
  # quoted component with a separator. For example, `["package".metadata.ci]`
  # aliases `[package.metadata.ci]`, while `["package.metadata.ci"]` names one
  # unrelated component and remains valid. Unicode escapes are handled by the
  # global fail-closed check below.
  IFS='.' read -r -a expected_table_parts <<< "$expected_table"
  for part in "${expected_table_parts[@]}"; do
    expected_table_path_ere+="$separator($part|\"$part\"|'$part')"
    separator='[[:space:]]*\.[[:space:]]*'
  done
  expected_table_header_ere="^[[:space:]]*\\[[[:space:]]*${expected_table_path_ere}[[:space:]]*\\][[:space:]]*(#.*)?$"
  expected_array_table_header_ere="^[[:space:]]*\\[[[:space:]]*\\[[[:space:]]*${expected_table_path_ere}[[:space:]]*\\][[:space:]]*\\][[:space:]]*(#.*)?$"

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

    # TOML basic quoted keys and table names decode Unicode escapes before
    # comparing identifiers. For example, `"\u0063hannel"` is another
    # spelling of `channel`, but the deliberately textual checks below cannot
    # recognize that semantic duplicate. Decoding TOML escapes here would turn
    # this bootstrap recognizer into a partial parser, so fail closed on either
    # Unicode-escape form anywhere in a semantic line. Ordinary escapes such as
    # `\"` remain accepted in unrelated values. If a coordinated input ever
    # needs a Unicode escape, replace this recognizer with a parser and update
    # the hostile fixtures in `../ci/check_tools.sh` at the same time.
    if [[ "$normalized" =~ $unicode_escape_ere ]]; then
      return 1
    fi

    # A table header with any alternate spacing is deliberately not the
    # expected canonical header. It still leaves the expected table so an
    # exact-looking assignment beneath another table cannot be accepted.
    #
    # Quoted TOML keys are another spelling of a bare key. For example,
    # `["toolchain"]` and `['toolchain']` both reopen `[toolchain]`. Array
    # tables receive the same treatment because defining `[[toolchain]]`
    # alongside `[toolchain]` is also a semantic collision. Keep these checks
    # coordinated with the hostile fixtures in `../ci/check_tools.sh`.
    if [[ "$normalized" =~ ^[[:space:]]*\[ ]]; then
      if [[ "$normalized" == "$expected_header" ]]; then
        expected_table_count=$((expected_table_count + 1))
        [[ $expected_table_count -eq 1 ]] || return 1
        in_expected_table=1
      else
        if [[ "$normalized" =~ $expected_table_header_ere || \
              "$normalized" =~ $expected_array_table_header_ere ]]; then
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
