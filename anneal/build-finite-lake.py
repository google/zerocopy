#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
"""Compile the finite Lake helper in new trusted archive staging only.

Source/recipe bytes are retained with the executable for publisher identity.
Native relocation and closure admission follow compilation, before SDK assembly.
This is a producer operation, never a consumer repair or an SDK startup build.
"""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def build(root: Path, source: Path, platform: str):
    if root.is_symlink() or (root / "lean").is_symlink():
        raise ValueError("publisher staging must be physical")
    root = root.resolve(strict=True)
    runtime = root / "lean"
    if (root / "lean-sdk").exists() or (root / "lean-sdk").is_symlink():
        raise ValueError("finite compilation must precede SDK assembly")
    if platform not in {"aarch64-darwin", "x86_64-darwin", "aarch64-linux", "x86_64-linux"}:
        raise ValueError("unsupported RC2 platform")
    executable = runtime / "bin/anneal-finite-lake"
    retained = runtime / "src/anneal"
    if executable.exists() or executable.is_symlink() or retained.exists() or retained.is_symlink():
        raise FileExistsError("finite publisher outputs must be fresh")
    # Reject redirected producer writes and compiler selectors before creating
    # any outputs, including live or dangling links in staging ancestors.
    for destination in [retained, executable, runtime / "bin/lean", runtime / "bin/leanc"]:
        candidate = root
        for part in destination.relative_to(root).parts:
            candidate = candidate / part
            if candidate.is_symlink():
                raise ValueError("finite compilation requires physical runtime staging")
    retained.mkdir(parents=True)
    shutil.copyfile(source, retained / "FiniteLake.lean")
    shutil.copyfile(Path(__file__).resolve(), retained / "build-finite-lake.py")
    env = dict(os.environ)
    env.update(LEAN_SYSROOT=str(runtime), LEAN_PATH=str(runtime / "lib/lean"),
               LEAN_SRC_PATH=str(runtime / "src/lean"), LEAN_NUM_THREADS="1")
    loader = os.pathsep.join(map(str, [runtime / "lib/lean", runtime / "lib"]))
    env.update(DYLD_LIBRARY_PATH=loader, LD_LIBRARY_PATH=loader)
    # Compiler intermediates are private producer scratch, not SDK imports.
    with tempfile.TemporaryDirectory(prefix="finite-lake-") as temporary:
        output = Path(temporary)
        subprocess.run([str(runtime / "bin/lean"), "--root=" + str(retained),
                        "-o", str(output / "FiniteLake.olean"), "-c", str(output / "FiniteLake.c"),
                        str(retained / "FiniteLake.lean")], env=env, check=True)
        origin = "@executable_path" if platform.endswith("-darwin") else "$ORIGIN"
        # RC2's -leanshared selects plugin flags, which leave Lean runtime
        # symbols unresolved on ELF. Match its executable runtime providers
        # explicitly on Linux, preserving the admitted Darwin link recipe.
        runtime_links = (["-lInit_shared", "-lleanshared_2", "-lleanshared_1", "-lleanshared"]
                         if platform.endswith("-linux") else [])
        subprocess.run([str(runtime / "bin/leanc"), "-O1", "-rdynamic", "-leanshared",
                        str(output / "FiniteLake.c"), "-L", str(runtime / "lib/lean"), "-lLake_shared",
                        *runtime_links,
                        "-Wl,-rpath," + origin + "/../lib/lean", "-Wl,-rpath," + origin + "/../lib",
                        "-o", str(executable)], env=env, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--platform", required=True)
    args = parser.parse_args()
    build(args.root, args.source, args.platform)
