#!/usr/bin/env python3
"""Prune unused Lake source and build artifacts from vendored packages."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
from pathlib import Path


IMPORT_RE = re.compile(r"^(?:public\s+)?(?:protected\s+)?(?:private\s+)?(?:meta\s+)?import\s+(.+)$")
MATHLIB_TRACE_RE = re.compile(r"((?:Mathlib)(?:\.[A-Za-z0-9_']+)*)")

PACKAGE_META_FILES = [
    ".gitignore",
    ".gitattributes",
    "README.md",
    "LICENSE",
    "bors.toml",
    ".pre-commit-config.yaml",
    ".gitpod.yml",
]
PACKAGE_META_DIRS = [
    ".github",
    ".vscode",
    ".devcontainer",
    ".docker",
    "docs",
    "tests",
    "test",
]


def module_name_from_lean_path(pkg_dir: Path, path: Path) -> str | None:
    rel = path.relative_to(pkg_dir)
    if rel == Path("lakefile.lean") or path.suffix != ".lean":
        return None
    return ".".join(rel.with_suffix("").parts)


def imported_mathlib_modules(path: Path) -> set[str]:
    imports = set()
    with path.open(encoding="utf-8") as f:
        for line in f:
            match = IMPORT_RE.match(line.strip())
            if match is None:
                continue
            imports.update(module for module in match.group(1).split() if module.startswith("Mathlib"))
    return imports


def imported_mathlib_modules_from_trace(path: Path) -> set[str]:
    try:
        with path.open(encoding="utf-8") as f:
            content = json.load(f)
    except (OSError, json.JSONDecodeError):
        return set()
    return set(MATHLIB_TRACE_RE.findall(json.dumps(content)))


def is_within(path: Path, parent: Path) -> bool:
    return path == parent or parent in path.parents


def walk_without_metadata(root: Path):
    for dir_path, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {".git"}]
        yield Path(dir_path), dirs, files


def walk_without_build_metadata(root: Path):
    for dir_path, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        yield Path(dir_path), dirs, files


def collect_mathlib_closure(project_root: Path, packages_root: Path) -> set[str] | None:
    mathlib_dir = packages_root / "mathlib"
    if not mathlib_dir.is_dir():
        return None

    mathlib_imports: dict[str, set[str]] = {}
    seeds: set[str] = set()
    for scan_root in [project_root, packages_root]:
        for root, _dirs, files in walk_without_metadata(scan_root):
            is_mathlib = is_within(root, mathlib_dir)
            for filename in files:
                path = root / filename
                if path.suffix == ".lean":
                    if is_mathlib:
                        module_name = module_name_from_lean_path(mathlib_dir, path)
                        if module_name is not None:
                            mathlib_imports[module_name] = imported_mathlib_modules(path)
                    else:
                        seeds.update(imported_mathlib_modules(path))
                elif path.suffix == ".trace" and not is_mathlib:
                    seeds.update(imported_mathlib_modules_from_trace(path))

    closure: set[str] = set()
    stack = list(seeds)
    while stack:
        module_name = stack.pop()
        if module_name in closure:
            continue
        closure.add(module_name)
        stack.extend(mathlib_imports.get(module_name, ()) - closure)

    print(
        "Mathlib reachability pruning will keep "
        f"{len(closure)} modules seeded from {len(seeds)} direct imports."
    )
    return closure


def remove_empty_dirs(pkg_dir: Path) -> None:
    for root, _dirs, _files in os.walk(pkg_dir, topdown=False):
        path = Path(root)
        if path == pkg_dir:
            continue
        if not any(path.iterdir()):
            path.rmdir()


def remove_package_metadata(pkg_dir: Path) -> None:
    for name in PACKAGE_META_FILES:
        path = pkg_dir / name
        if path.exists():
            path.unlink()
    for name in PACKAGE_META_DIRS:
        path = pkg_dir / name
        if path.exists():
            shutil.rmtree(path, ignore_errors=True)
    for archive in pkg_dir.rglob("*.ltar"):
        archive.unlink()
    remove_empty_dirs(pkg_dir)


def remove_build_artifacts(pkg_dir: Path, module_path: str) -> None:
    for subdir in ["lib/lean", "ir"]:
        build_dir = pkg_dir / ".lake" / "build" / subdir
        if not build_dir.exists():
            continue
        module_dir = build_dir / os.path.dirname(module_path)
        module_name = os.path.basename(module_path)
        if not module_dir.exists():
            continue
        for path in module_dir.iterdir():
            if path.name.startswith(module_name + "."):
                path.unlink()


def prune_package(pkg_dir: Path, mathlib_closure: set[str] | None) -> None:
    print(f"Pruning package at: {pkg_dir}")
    traces_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    if not traces_dir.exists():
        print(f"No build traces found for {pkg_dir}, skipping pruning.")
        return

    all_lean_files = []
    for root, _dirs, files in walk_without_build_metadata(pkg_dir):
        for filename in files:
            path = root / filename
            if path.suffix == ".lean":
                all_lean_files.append(path.relative_to(pkg_dir))

    print(f"  - Found {len(all_lean_files)} total .lean files.")
    if pkg_dir.name == "mathlib":
        if mathlib_closure is None:
            print("  - No Mathlib reachability closure found; keeping all modules.")
            used_modules = {str(path.with_suffix("")) for path in all_lean_files}
        else:
            used_modules = {module.replace(".", os.sep) for module in mathlib_closure}
    else:
        used_modules = {str(path.with_suffix("")) for path in all_lean_files}
        print("  - Keeping all Lean modules for non-Mathlib package.")

    print(f"  - Keeping {len(used_modules)} modules.")
    unused_count = 0
    for rel_lean in all_lean_files:
        if rel_lean == Path("lakefile.lean"):
            continue
        module_path = str(rel_lean.with_suffix(""))
        if module_path in used_modules:
            continue
        (pkg_dir / rel_lean).unlink()
        unused_count += 1
        remove_build_artifacts(pkg_dir, module_path)

    print(f"  - Deleted {unused_count} unused .lean files and their build artifacts.")
    remove_package_metadata(pkg_dir)


def prune_root_mathlib_cache(project_root: Path) -> None:
    root_mathlib_build = project_root / ".lake" / "build" / "lib" / "lean" / "Mathlib"
    if root_mathlib_build.exists():
        print("Deleting root Mathlib build cache...")
        shutil.rmtree(root_mathlib_build)
    lib_lean_dir = project_root / ".lake" / "build" / "lib" / "lean"
    if lib_lean_dir.exists():
        for path in lib_lean_dir.iterdir():
            if path.name.startswith("Mathlib."):
                path.unlink()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--packages-root", type=Path, required=True)
    args = parser.parse_args()

    project_root = args.project_root.resolve()
    packages_root = args.packages_root.resolve()
    mathlib_closure = collect_mathlib_closure(project_root, packages_root)
    if packages_root.exists():
        for pkg_dir in sorted(path for path in packages_root.iterdir() if path.is_dir()):
            prune_package(pkg_dir, mathlib_closure)
    prune_root_mathlib_cache(project_root)


if __name__ == "__main__":
    main()
