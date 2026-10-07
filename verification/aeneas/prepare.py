#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Prepare the pinned extraction without changing its translated behavior.

Reject error-bearing LLBC even when Charon exits successfully. Repair only the
known duplicate dictionary name, then point the Lean project at already-fetched
backend dependencies. Native imports remain responsible for module ordering.
"""

import argparse
import json
import re
from pathlib import Path


def check_llbc(path):
    """Require Charon's explicit success flag and an actual translated crate."""
    data = json.loads(path.read_text())
    # Charon can exit successfully even when extraction was incomplete.
    if data.get("has_errors") is not False:
        raise ValueError("Charon LLBC is missing has_errors: false")
    if not isinstance(data.get("translated"), dict):
        raise ValueError("Charon LLBC is missing the translated crate")


def rename_copy_fields(types, funs):
    """Apply the exact naming repair only after every expected match is unique."""
    # At this exact pin ZeroablePrimitive inherits Copy for both Self and its
    # associated NonZeroInner. Aeneas gives both projections the same name.
    # Rename ONLY the second projection and its initializer; retain both types
    # and both dictionaries. Never change the translated helper bodies.
    contents = {'types': types, 'funs': funs}
    edits = [
        ('types', '"markerCopyInst", "markerCopyInst"',
         '"markerCopyInst", "innerCopyInst"'),
        ('types', "markerCopyInst : core.marker.Copy Self_NonZeroInner",
         "innerCopyInst : core.marker.Copy Self_NonZeroInner"),
        ('funs', "markerCopyInst := core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy",
         "innerCopyInst := core.num.niche_types.NonZeroUsizeInner.Insts.CoreMarkerCopy"),
    ]
    for name, old, _ in edits:
        if contents[name].count(old) != 1:
            raise ValueError(f"Pinned Aeneas naming workaround no longer matches: {old}")
    for name, old, new in edits:
        contents[name] = contents[name].replace(old, new)
    return contents['types'], contents['funs']


def share_manifest(workspace, backend, rust_model):
    """Reuse pinned packages and discover library roots from assembled modules.

    Each root is a default build target except Check, which the driver also runs
    explicitly to refresh audit reports even when Lake has cached its imports.
    """
    # Read the upstream lockfile and reuse the dependencies fetched into the
    # backend. A separate `lake update` here would clone and cache Mathlib twice.
    upstream = json.loads((backend / "lake-manifest.json").read_text())
    packages = [{
        "type": "path", "scope": "", "name": "aeneas", "inherited": False,
        "dir": str(backend), "manifestFile": "lake-manifest.json",
        "configFile": "lakefile.lean",
    }]
    if not (rust_model / "lakefile.lean").is_file():
        raise ValueError(f"Missing shared Rust Lean package: {rust_model}")
    packages.append({
        "type": "path", "scope": "", "name": "rust_model", "inherited": False,
        "dir": str(rust_model), "manifestFile": "lake-manifest.json",
        "configFile": "lakefile.lean",
    })
    companion = rust_model / "aeneas"
    if not (companion / "lakefile.lean").is_file():
        raise ValueError(f"Missing shared Rust Aeneas package: {companion}")
    packages.append({
        "type": "path", "scope": "", "name": "rust_model_aeneas", "inherited": False,
        "dir": str(companion), "manifestFile": "lake-manifest.json",
        "configFile": "lakefile.lean",
    })
    for dep in upstream["packages"]:
        # Anneal vendors each dependency at the path in its manifest. These
        # paths can leave the backend directory; they are not Lake Git caches.
        if dep["type"] != "path":
            raise ValueError(f"Expected vendored Lean path dependency: {dep['name']}")
        directory = (backend / dep["dir"]).resolve()
        if not directory.is_dir():
            raise ValueError(f"Missing pinned Lean dependency: {directory}")
        packages.append({**dep, "inherited": True, "dir": str(directory)})
    manifest = {
        "version": upstream["version"], "packagesDir": ".lake/packages",
        "packages": packages, "name": "zerocopyVerification", "lakeDir": ".lake",
        "fixedToolchain": False,
    }
    (workspace / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    # Native proof modules use Lake's import graph. Discover their library roots
    # rather than maintaining a second assembly order in this script.
    libraries = {path.stem for path in workspace.glob('*.lean')
                 if path.name != 'lakefile.lean'}
    declarations = ''.join(
        ('' if name == 'Check' else '@[default_target] ') + f'lean_lib {name}\n'
        for name in sorted(libraries))
    (workspace / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\n'
        f'require aeneas from {json.dumps(str(backend))}\n'
        f'require rust_model from {json.dumps(str(rust_model))}\n'
        # Source builds share the already installed backend. This is a path
        # to that backend, not an independently selected version or toolchain.
        f'require rust_model_aeneas from {json.dumps(str(companion))} with\n'
        f'  Lean.NameMap.insert {{}} `aeneasPath {json.dumps(str(backend))}\n'
        'package zerocopyVerification where\n'
        '  moreLeanArgs := #["-DwarningAsError=true"]\n' + declarations)


def mathlib_imports(backend, proof_sources=None):
    """Collect native Mathlib imports while excluding fetched dependency trees.

    Include handwritten proof submodules when supplied. Their imports determine
    which cache artifacts the workflow needs; an unrelated .lake checkout must
    not enlarge that request.
    """
    pattern = re.compile(r"^(?:(?:public|private|protected|meta)\s+)*import\s+(.+)$")
    modules = set()
    roots = [backend] if proof_sources is None else [backend, proof_sources]
    for root in roots:
        for path in root.rglob('*.lean'):
            if ".lake" in path.relative_to(root).parts:
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
    parser.add_argument("--proof-sources", type=Path)
    args = parser.parse_args()
    if args.command == "llbc":
        check_llbc(args.path)
    elif args.command == "mathlib-imports":
        print("\n".join(mathlib_imports(args.path, args.proof_sources)))
    elif args.command == "prepare":
        types = args.path / "Zerocopy/Types.lean"
        funs = args.path / "Zerocopy/Funs.lean"
        types_text, funs_text = rename_copy_fields(types.read_text(), funs.read_text())
        types.write_text(types_text)
        funs.write_text(funs_text)
    if args.command == "workspace":
        if args.backend is None:
            parser.error(f"{args.command} requires --backend")
        share_manifest(args.path, args.backend.resolve(),
                       Path(__file__).resolve().parents[2] / "anneal/lean")


if __name__ == "__main__":
    main()
