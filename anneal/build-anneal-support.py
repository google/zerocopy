#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
"""Compile unchanged Anneal support once in new trusted archive staging.

The unified SDK publishes source and the RC2 legacy olean/ilean family. Consumer
policy remains in its local facade, and environment reflection runs there when
called. This emits no native support library and rebuilds no imported package.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess


def build(root: Path, source: Path, platform: str):
    if root.is_symlink():
        raise ValueError("support compilation requires physical archive staging")
    root = root.resolve(strict=True)
    runtime = root / "lean"
    project = root / "aeneas/backends/lean"
    packages = root / "aeneas/packages"
    if (root / "lean-sdk").exists() or (root / "lean-sdk").is_symlink():
        raise ValueError("support compilation must precede SDK assembly")
    if platform not in {"aarch64-darwin", "x86_64-darwin", "aarch64-linux", "x86_64-linux"}:
        raise ValueError("unsupported RC2 platform")
    retained = runtime / "src/lean/AnnealSupport.lean"
    recipe = runtime / "src/anneal/build-anneal-support.py"
    outputs = [runtime / "lib/lean" / ("AnnealSupport." + suffix) for suffix in ("olean", "ilean")]
    if any(p.exists() or p.is_symlink() for p in [retained, recipe, *outputs]):
        raise FileExistsError("support publisher outputs must be fresh")
    # Refuse dangling or live staging links before creating output directories,
    # including an ancestor that could redirect writes into an old SDK/runtime.
    for destination in [retained, recipe, *outputs, runtime / "bin/lean"]:
        candidate = root
        for part in destination.relative_to(root).parts:
            candidate = candidate / part
            if candidate.is_symlink():
                raise ValueError("support compilation requires physical runtime staging")
    plugin = project / ".lake/build/lib" / ("libaeneas_AeneasMeta." + ("dylib" if platform.endswith("-darwin") else "so"))
    if not plugin.is_file() or plugin.is_symlink():
        raise FileNotFoundError("selected AeneasMeta plugin is required")
    owners = [runtime, project] + [p for p in sorted(packages.iterdir()) if p.is_dir() and p.name != ".lake"]
    imports = [runtime / "lib/lean"] + [p / ".lake/build/lib/lean" for p in owners[1:] if (p / ".lake/build/lib/lean").is_dir()]
    retained.parent.mkdir(parents=True, exist_ok=True)
    recipe.parent.mkdir(parents=True, exist_ok=True)
    outputs[0].parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, retained)
    shutil.copyfile(Path(__file__).resolve(), recipe)
    env = dict(os.environ)
    env.update(LEAN_SYSROOT=str(runtime), LEAN_PATH=os.pathsep.join(map(str, imports)),
               LEAN_SRC_PATH=os.pathsep.join(map(str, [runtime / "src/lean", *owners[1:]])),
               LEAN_NUM_THREADS="1")
    loader = os.pathsep.join(map(str, [runtime / "lib/lean", runtime / "lib", plugin.parent]))
    env.update(DYLD_LIBRARY_PATH=loader, LD_LIBRARY_PATH=loader)
    subprocess.run([str(runtime / "bin/lean"), "--root=" + str(retained.parent),
                    "--load-dynlib=" + str(plugin), "-o", str(outputs[0]), "-i", str(outputs[1]),
                    str(retained)], env=env, check=True)
    if not all(p.is_file() and not p.is_symlink() for p in outputs):
        raise ValueError("support compiler did not emit the complete olean/ilean family")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--platform", required=True)
    args = parser.parse_args()
    build(args.root, args.source, args.platform)
