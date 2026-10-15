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
from output import write_text


def check_llbc(path):
    """Require Charon's explicit success flag and an actual translated crate."""
    data = json.loads(path.read_text())
    # Charon can exit successfully even when extraction was incomplete.
    if data.get("has_errors") is not False:
        raise ValueError("Charon LLBC is missing has_errors: false")
    if not isinstance(data.get("translated"), dict):
        raise ValueError("Charon LLBC is missing the translated crate")


def rename_copy_fields(types, funs):
    """Repair the duplicate Copy label, retaining every original dictionary.

    At the pinned Aeneas version, ZeroablePrimitive inherits Copy for Self and
    NonZeroInner with the same generated field name. Repair each initializer
    structurally: arbitrary occurrences in other functions must not be renamed.
    """
    label = '"markerCopyInst", "markerCopyInst"'
    declaration = "markerCopyInst : core.marker.Copy Self_NonZeroInner"
    if types.count(label) != 1 or types.count(declaration) != 1:
        raise ValueError("Pinned Aeneas naming workaround no longer matches the trait")
    pattern = re.compile(
        r"^(  )markerCopyInst := (core\.num\.niche_types\.NonZero(?:U|I)(?:8|16|32|64|128|size)Inner\.Insts\.CoreMarkerCopy)$",
        re.MULTILINE)
    matches = pattern.findall(funs)
    if not matches or len({value for _, value in matches}) != len(matches):
        raise ValueError("Pinned Aeneas naming workaround lacks unique inner dictionaries")
    types = types.replace(label, '"markerCopyInst", "innerCopyInst"')
    types = types.replace(declaration, "innerCopyInst : core.marker.Copy Self_NonZeroInner")
    funs = pattern.sub(r"\1innerCopyInst := \2", funs)
    return types, funs


def retain_native_models(funs):
    """Elaborate native bodies with only the semantic providers they use.

    The Lean command parses the original declaration, preserves its argument
    prefix, and adds an implicit provider suffix when an external operation
    needs one. No function expression or Rust argument is replaced here.
    Unsupported declaration forms fail in that command rather than being
    silently edited by a second Lean parser.
    """
    if 'public import NativeModels\n' in funs or 'native_models def' in funs:
        raise ValueError('Native model extension must be applied exactly once')
    if funs.count('public import Aeneas\n') != 1:
        raise ValueError('Native function imports changed')
    funs = funs.replace('public import Aeneas\n',
                        'public import Aeneas\npublic import NativeModels\n')
    starts = list(re.finditer(r'^def\s+([A-Za-z_][A-Za-z_0-9.]*)\b', funs, re.MULTILINE))
    if not starts:
        raise ValueError('Native function inventory is empty')
    definitions = {match[1]: funs[match.start():
        starts[index + 1].start() if index + 1 < len(starts) else len(funs)]
        for index, match in enumerate(starts)}
    # A missed dependency fails Lean elaboration because no model provider is
    # available. Restrict the extension to the actual primitive's dependency
    # closure so unrelated native proof terms and anonymous arguments retain
    # their ordinary upstream elaboration.
    dependent = {'core.mem.zeroed'}
    while True:
        found = {name for name, definition in definitions.items()
                 if any(re.search(r'(?<![A-Za-z_0-9.])(?:Zerocopy\.)?' + re.escape(callee)
                                  + r'(?![A-Za-z_0-9.])', definition)
                        for callee in dependent)}
        if found <= dependent:
            break
        dependent.update(found)
    for match in reversed(starts):
        header = definitions[match[1]].split(':=', 1)[0]
        if (match[1] in dependent and re.search(r'[({][^(){}]*:\s*Type\b', header)):
            funs = funs[:match.start()] + 'native_models ' + funs[match.start():]
    return funs


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
    write_text(workspace / "lake-manifest.json", json.dumps(manifest, indent=2) + "\n")
    # Native proof modules use Lake's import graph. Discover their library roots
    # rather than maintaining a second assembly order in this script.
    libraries = {path.stem for path in workspace.glob('*.lean')
                 if path.name != 'lakefile.lean'}
    declarations = ''.join(
        ('' if name == 'Check' else '@[default_target] ') + f'lean_lib {name}\n'
        for name in sorted(libraries))
    write_text(workspace / "lakefile.lean", 'import Lake\nopen Lake DSL\n'
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
        funs_text = retain_native_models(funs_text)
        write_text(types, types_text)
        write_text(funs, funs_text)
    if args.command == "workspace":
        if args.backend is None:
            parser.error(f"{args.command} requires --backend")
        share_manifest(args.path, args.backend.resolve(),
                       Path(__file__).resolve().parents[2] / "anneal/lean")


if __name__ == "__main__":
    main()
