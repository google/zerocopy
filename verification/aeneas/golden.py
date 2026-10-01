#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compare Aeneas snapshots with narrowly defined, literal-aware fuzziness."""

import argparse
import difflib
import re
from pathlib import Path

FILES = ("Types.lean", "Funs.lean", "TypesExternal_Template.lean",
         "FunsExternal_Template.lean")
HANDWRITTEN = {"TypesExternal.lean", "FunsExternal.lean"}
CHAR = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\\r\n])'")
HEADER = """/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

"""


def normalize(source):
    # Preserve code, indentation, line boundaries, and literal bytes. Comments
    # become a space (not concatenation), retaining their newlines. Only empty
    # nonliteral lines and nonliteral trailing horizontal spaces are dropped.
    lines = []
    line = []
    i = 0

    def emit(char, literal=False):
        if char == "\n":
            finish()
        else:
            line.append((char, literal))

    def finish():
        while line and line[-1][0] in " \t\r" and not line[-1][1]:
            line.pop()
        if line:
            lines.append("".join(char for char, _ in line))
        line.clear()

    while i < len(source):
        if source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            emit(" ")
            i = end
        elif source.startswith("/-", i):
            depth = 1
            emit(" ")
            i += 2
            while depth:
                if i == len(source):
                    raise ValueError("Unterminated Lean block comment")
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    if source[i] == "\n":
                        emit("\n")
                    i += 1
        elif source[i] == '"' or source[i] == "«":
            end_char = '"' if source[i] == '"' else "»"
            # Raw and interpolated strings need their own lexer. This pinned
            # generator emits neither; fail closed if an upgrade adds them.
            if end_char == '"' and (re.search(r"r#*$", source[:i]) or
                                     source[:i].endswith('!')):
                raise ValueError("Unsupported raw or interpolated Lean string")
            emit(source[i], True)
            i += 1
            while True:
                if i == len(source):
                    raise ValueError("Unterminated Lean literal")
                char = source[i]
                # Preserve empty lines INSIDE literals, unlike empty code lines.
                if char == "\n" and not line:
                    line.append(("", True))
                emit(char, True)
                i += 1
                if char == end_char:
                    break
                if char == "\\" and end_char == '"':
                    if i == len(source):
                        raise ValueError("Unterminated Lean escape")
                    emit(source[i], True)
                    i += 1
        elif source[i] == "'" and (match := CHAR.match(source, i)):
            for char in match[0]:
                emit(char, True)
            i = match.end()
        else:
            emit(source[i])
            i += 1
    finish()
    return lines


def files(directory, live=False):
    actual = {str(p.relative_to(directory)) for p in directory.rglob("*") if p.is_file()}
    if live:
        actual -= HANDWRITTEN
    if actual != set(FILES):
        raise ValueError(f"Unexpected generated file set in {directory}: "
                         f"missing={sorted(set(FILES) - actual)}, "
                         f"extra={sorted(actual - set(FILES))}")
    return {name: (directory / name).read_bytes().decode("utf-8") for name in FILES}


def compare(live, golden):
    generated = files(live, live=True)
    checked_in = files(golden)
    differences = []
    for name in FILES:
        before, after = normalize(checked_in[name]), normalize(generated[name])
        if before != after:
            differences.extend(difflib.unified_diff(
                before, after, fromfile=f"golden/{name}",
                tofile=f"live/{name}", lineterm=""))
    return differences


def update(live, golden):
    generated = files(live, live=True)
    # Validate the complete candidate before changing any checked-in file.
    for source in generated.values():
        normalize(source)
    if golden.exists():
        actual = {str(p.relative_to(golden)) for p in golden.rglob("*") if p.is_file()}
        if actual - set(FILES):
            raise ValueError(f"Unexpected checked-in generated files: {sorted(actual - set(FILES))}")
    golden.mkdir(parents=True, exist_ok=True)
    for name in FILES:
        (golden / name).write_text(HEADER + generated[name], encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["compare", "update"])
    parser.add_argument("live", type=Path)
    parser.add_argument("golden", type=Path)
    args = parser.parse_args()
    if args.command == "update":
        update(args.live, args.golden)
    else:
        differences = compare(args.live, args.golden)
        if differences:
            print("\n".join(differences))
            raise SystemExit("Aeneas goldens differ. Review the extraction and run "
                             "bash verification/aeneas/run.sh --update-goldens")
        print("Live Aeneas output matches goldens under the fuzzy comparison")


if __name__ == "__main__":
    main()
