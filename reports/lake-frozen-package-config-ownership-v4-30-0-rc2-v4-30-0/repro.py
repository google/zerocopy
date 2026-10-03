#!/usr/bin/env python3
"""Generate the tiny Lake sources/consumers; does not run or freeze anything.

Example: python3 repro.py --out /tmp/lake-ownership-rc2 \
  --toolchain leanprover/lean4:v4.30.0-rc2

Use the matching installed Lean/Lake tuple; prime once with the printed command,
then make the two producer directories read-only before consumer commands.
Run RC2 and final in separate --out directories; OLeans are not cross-version.
"""

import argparse
import json
import os
from pathlib import Path


def write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)


def make_consumer(path, shared, pad, toolchain, name="consumer_a", manifest=True,
                  reverse=False):
    path.mkdir(parents=True, exist_ok=False)
    write(path / "lean-toolchain", toolchain + "\n")
    packages = [("probe_shared", shared), ("probe_pad", pad)]
    if reverse:
        packages.reverse()
    requires = "".join(f'require {n} from "{p}"\n' for n, p in packages)
    write(path / "lakefile.lean", f'''import Lake
open Lake DSL
{requires}package {name}
@[default_target] lean_lib Client where
  roots := #[`Client]
''')
    write(path / "Client.lean", "import Shared\ndef clientValue : Nat := sharedValue + 1\n")
    if manifest:
        entries = [{"type": "path", "name": n, "dir": os.path.relpath(p, path),
                    "inherited": False} for n, p in packages]
        data = {"version": "1.2.0", "packagesDir": ".lake/packages",
                "packages": entries, "name": name, "lakeDir": ".lake",
                "fixedToolchain": False}
        write(path / "lake-manifest.json", json.dumps(data, indent=2) + "\n")


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument("--out", type=Path, required=True)
ap.add_argument("--toolchain", required=True)
args = ap.parse_args()
root = args.out.resolve()
root.mkdir(parents=True, exist_ok=False)
shared, pad = root / "source/probe_shared", root / "source/probe_pad"
write(shared / "lean-toolchain", args.toolchain + "\n")
write(shared / "lakefile.lean", "import Lake\nopen Lake DSL\npackage probe_shared\nlean_lib Shared where\n  roots := #[`Shared]\n")
write(shared / "Shared.lean", "def sharedValue : Nat := 7\n")
write(pad / "lean-toolchain", args.toolchain + "\n")
write(pad / "lakefile.lean", "import Lake\nopen Lake DSL\npackage probe_pad\n")
work = root / "work"
make_consumer(work / "primer", shared, pad, args.toolchain)
make_consumer(work / "a", shared, pad, args.toolchain)
make_consumer(work / "nested/deeper/b", shared, pad, args.toolchain)
make_consumer(work / "name", shared, pad, args.toolchain, name="consumer_renamed")
make_consumer(work / "index", shared, pad, args.toolchain, reverse=True)
make_consumer(work / "no-manifest", shared, pad, args.toolchain, manifest=False)
make_consumer(work / "old", shared, pad, args.toolchain)
print("1. Prime: cd", work / "primer", "&& lake --keep-toolchain --no-cache build Client")
print("2. Freeze both source packages, then run fresh consumers a, nested/deeper/b, name, index, no-manifest, old in that order.")
print("3. Use lake --keep-toolchain --no-cache build Client; add --old for old.")
print("4. Edit only work/a/Client.lean; repeat build twice to test private edit and no-op.")
print("5. For --no-build: make a separate healthy copy of source packages, prime it, remove its Shared.olean, freeze it, and use a fresh consumer.")
