#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate extraction, repair a pinned naming collision, and share Lake deps."""

import argparse
import json
import re
from pathlib import Path


def check_llbc(path):
    data = json.loads(path.read_text())
    # Charon can exit successfully even when extraction was incomplete.
    if data.get("has_errors") is not False:
        raise ValueError("Charon LLBC is missing has_errors: false")
    if not isinstance(data.get("translated"), dict):
        raise ValueError("Charon LLBC is missing the translated crate")


def rename_copy_fields(types, funs):
    # At this exact pin ZeroablePrimitive inherits Copy for both Self and its
    # associated NonZeroInner. Aeneas gives both projections the same name.
    # Rename ONLY the second projection and its initializer; retain both types
    # and both dictionaries. Never change the translated helper bodies.
    edits = [
        (types, '"markerCopyInst", "markerCopyInst"',
         '"markerCopyInst", "innerCopyInst"'),
        (types, "markerCopyInst : core.marker.Copy Self_NonZeroInner",
         "innerCopyInst : core.marker.Copy Self_NonZeroInner"),
        (funs, "markerCopyInst := core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy",
         "innerCopyInst := core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy"),
    ]
    for content, old, _ in edits:
        if content.count(old) != 1:
            raise ValueError(f"Pinned Aeneas naming workaround no longer matches: {old}")
    types = types.replace(edits[0][1], edits[0][2]).replace(edits[1][1], edits[1][2])
    funs = funs.replace(edits[2][1], edits[2][2])
    return types, funs


def share_manifest(workspace, backend):
    # Read the upstream lockfile and reuse the dependencies fetched into the
    # backend. A separate `lake update` here would clone and cache Mathlib twice.
    upstream = json.loads((backend / "lake-manifest.json").read_text())
    packages = [{
        "type": "path", "scope": "", "name": "aeneas", "inherited": False,
        "dir": str(backend), "manifestFile": "lake-manifest.json",
        "configFile": "lakefile.lean",
    }]
    for dep in upstream["packages"]:
        directory = backend / ".lake/packages" / dep["name"]
        if not directory.is_dir():
            raise ValueError(f"Missing pinned Lean dependency: {directory}")
        packages.append({
            "type": "path", "scope": dep["scope"], "name": dep["name"],
            "inherited": True, "dir": str(directory),
            "manifestFile": dep["manifestFile"], "configFile": dep["configFile"],
        })
    manifest = {
        "version": upstream["version"], "packagesDir": ".lake/packages",
        "packages": packages, "name": "zerocopyVerification", "lakeDir": ".lake",
        "fixedToolchain": False,
    }
    (workspace / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (workspace / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\n'
        f'require aeneas from {json.dumps(str(backend))}\n'
        'package zerocopyVerification\n'
        '@[default_target] lean_lib Zerocopy\n'
        'lean_lib Contracts\n'
        'lean_lib Arithmetic\n'
        '@[default_target] lean_lib LayoutMath\n'
        'lean_lib LayoutModel\n'
        '@[default_target] lean_lib Corollaries\n'
        '@[default_target] lean_lib ContractTests\n'
        '@[default_target] lean_lib Proofs\n'
        'lean_lib Obligations\n'
        '@[default_target] lean_lib Required\n'
    )


def mathlib_imports(backend):
    pattern = re.compile(r"^(?:(?:public|private|protected|meta)\s+)*import\s+(.+)$")
    modules = set()
    for path in backend.rglob("*.lean"):
        if ".lake" in path.relative_to(backend).parts:
            continue
        for line in path.read_text().splitlines():
            match = pattern.match(line.strip())
            if match:
                modules.update(m for m in match[1].split() if m.startswith("Mathlib."))
    if not modules:
        raise ValueError("No Mathlib imports found in the pinned Aeneas backend")
    return sorted(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["llbc", "prepare", "workspace", "mathlib-imports"])
    parser.add_argument("path", type=Path)
    parser.add_argument("--backend", type=Path)
    args = parser.parse_args()
    if args.command == "llbc":
        check_llbc(args.path)
    elif args.command == "mathlib-imports":
        print("\n".join(mathlib_imports(args.path)))
    elif args.command == "prepare":
        types = args.path / "Zerocopy/Types.lean"
        funs = args.path / "Zerocopy/Funs.lean"
        types_text, funs_text = rename_copy_fields(types.read_text(), funs.read_text())
        types.write_text(types_text)
        funs.write_text(funs_text)
    if args.command in ("prepare", "workspace"):
        if args.backend is None:
            parser.error(f"{args.command} requires --backend")
        share_manifest(args.path, args.backend.resolve())


if __name__ == "__main__":
    main()
