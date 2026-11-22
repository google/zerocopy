# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate an unpacked Anneal toolchain bundle and emit GITHUB_ENV exports.

Ensures every directory component from any cache root down to the bundle root is
a regular non-symlink directory, every inode inside the bundle is confined to
that root (allowing only internal relative file symlinks such as `.so` aliases),
and every exported entrypoint path traverses zero symlinks.
"""

import argparse
import json
import os
from pathlib import Path
import stat
import sys


LEAN_ONLY_FILES = ("lean/bin/lean",)
FULL_BUNDLE_FILES = (
    "rust/bin/rustc",
    "rust/bin/rustdoc",
    "lean/bin/lean",
    "bin/anneal-rustc-capture",
    "share/anneal/correspondence-provenance.json",
    "share/anneal/trusted/audit/TrustedBoundary.lean",
)
FULL_BUNDLE_DIRS = ("rust", "rust/lib", "lean", "bin", "share/anneal")


def _check_env_safe(value: str, label: str) -> None:
    if "\n" in value or "\r" in value or "\0" in value:
        raise SystemExit(f"forbidden control character in {label}: {value!r}")


def _resolve_regular_dir(path: Path, label: str) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise SystemExit(f"{label} must be a regular directory: {path}")
    return path.resolve(strict=True)


def _walk_non_symlink_dirs(base: Path, rel_parts: tuple[str, ...]) -> Path:
    cur = base
    for part in rel_parts:
        if part in ("", ".", ".."):
            raise SystemExit(f"invalid relative path segment: {part!r}")
        cur = cur / part
        if cur.is_symlink() or not cur.is_dir():
            raise SystemExit(
                f"bundle ancestor must be a regular directory: {cur}"
            )
    return cur.resolve(strict=True)


def _walk_error(exc: OSError) -> None:
    raise SystemExit(f"cannot traverse bundle directory: {exc}")


def verify_bundle_tree(
    root: Path,
    *,
    cache_root: Path | None = None,
    lean_only: bool = False,
) -> tuple[Path, Path | None]:
    """Verify confinement of `root` and return resolved `(root, cache_root)`."""
    real_cache: Path | None = None
    if cache_root is not None:
        real_cache = _resolve_regular_dir(cache_root, "cache root")
        raw_cache = cache_root.absolute()
        raw_root = root.absolute()
        if raw_root == raw_cache or not raw_root.is_relative_to(raw_cache):
            raise SystemExit(
                f"bundle root {root} must reside strictly inside {cache_root}"
            )
        rel_parts = raw_root.relative_to(raw_cache).parts
        real_root = _walk_non_symlink_dirs(real_cache, rel_parts)
    else:
        real_root = _resolve_regular_dir(root, "bundle root")

    for dirpath, dirnames, filenames in os.walk(
        real_root, followlinks=False, onerror=_walk_error
    ):
        base = Path(dirpath)
        for name in dirnames + filenames:
            entry = base / name
            mode = entry.lstat().st_mode
            if stat.S_ISLNK(mode):
                raw_target = Path(os.readlink(entry))
                if raw_target.is_absolute():
                    raise SystemExit(
                        f"absolute symlink forbidden: {entry} -> {raw_target}"
                    )
                cur_lex = entry.parent
                for part in raw_target.parts:
                    if part in ("", "."):
                        continue
                    cur_lex = (
                        cur_lex.parent if part == ".." else cur_lex / part
                    )
                    if not cur_lex.is_relative_to(real_root):
                        raise SystemExit(
                            "symlink escapes bundle root: "
                            f"{entry} -> {raw_target}"
                        )
                if cur_lex == real_root:
                    raise SystemExit(
                        f"symlink targets bundle root: {entry} -> {raw_target}"
                    )
                try:
                    resolved = entry.resolve(strict=True)
                except (OSError, RuntimeError) as exc:
                    raise SystemExit(
                        f"broken symlink: {entry} -> {raw_target} ({exc})"
                    ) from exc
                if (
                    not resolved.is_relative_to(real_root)
                    or not resolved.is_file()
                ):
                    raise SystemExit(
                        "unconfined or directory symlink in bundle: "
                        f"{entry} -> {raw_target}"
                    )
            elif not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise SystemExit(f"unexpected special file in bundle: {entry}")

    required_dirs = ("lean",) if lean_only else FULL_BUNDLE_DIRS
    required_files = LEAN_ONLY_FILES if lean_only else FULL_BUNDLE_FILES
    for rel_dir in required_dirs:
        _walk_non_symlink_dirs(real_root, Path(rel_dir).parts)
    for rel_file in required_files:
        parts = Path(rel_file).parts
        parent = _walk_non_symlink_dirs(real_root, parts[:-1])
        leaf = parent / parts[-1]
        if leaf.is_symlink() or not leaf.is_file():
            raise SystemExit(f"installed tool is missing or symlinked: {leaf}")
    return real_root, real_cache


def discover_single_bundle(cache_root: Path) -> Path:
    """Return the unique bundle path under `<cache_root>/anneal/toolchain`."""
    real_cache = _resolve_regular_dir(cache_root, "cache root")
    toolchain_parent = _walk_non_symlink_dirs(
        real_cache, ("anneal", "toolchain")
    )
    entries = list(toolchain_parent.iterdir())
    if any(entry.is_symlink() for entry in entries):
        raise SystemExit("symlink forbidden directly under anneal/toolchain")
    roots = [entry for entry in entries if entry.is_dir()]
    if len(roots) != 1:
        raise SystemExit("setup must produce exactly one fresh installation")
    return cache_root / "anneal" / "toolchain" / roots[0].name


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--root", type=Path, help="Extracted bundle root path.")
    group.add_argument(
        "--discover-single",
        action="store_true",
        help="Discover the unique bundle under <cache-root>/anneal/toolchain.",
    )
    parser.add_argument(
        "--cache-root",
        type=Path,
        help="XDG_CACHE_HOME directory containing anneal/toolchain/...",
    )
    parser.add_argument(
        "--lean-only",
        action="store_true",
        help="Validate only lean/bin/lean and emit ANNEAL_TEST_INSTALL_ROOT.",
    )
    parser.add_argument(
        "--diagnostics",
        type=Path,
        help="Optional path to write installation.json evidence.",
    )
    parser.add_argument(
        "--source-revision",
        help="Source revision string recorded when --diagnostics is set.",
    )
    args = parser.parse_args(argv)

    if args.discover_single and args.cache_root is None:
        raise SystemExit("--discover-single requires --cache-root")
    if not args.lean_only and args.cache_root is None:
        raise SystemExit("full bundle export requires --cache-root")
    if args.diagnostics is not None and not args.source_revision:
        raise SystemExit("--diagnostics requires --source-revision")

    target_root = (
        discover_single_bundle(args.cache_root)
        if args.discover_single
        else args.root
    )
    real_root, real_cache = verify_bundle_tree(
        target_root, cache_root=args.cache_root, lean_only=args.lean_only
    )
    _check_env_safe(str(real_root), "ANNEAL_TEST_INSTALL_ROOT")

    if args.lean_only:
        print(f"ANNEAL_TEST_INSTALL_ROOT={real_root}")
        return 0

    assert real_cache is not None
    _check_env_safe(str(real_cache), "XDG_CACHE_HOME")
    rust_lib = real_root / "rust/lib"
    print(f"XDG_CACHE_HOME={real_cache}")
    print(f"ANNEAL_TEST_INSTALL_ROOT={real_root}")
    print(f"ANNEAL_TEST_RUST_SYSROOT={real_root / 'rust'}")
    print(f"ANNEAL_LEAN={real_root / 'lean/bin/lean'}")
    print(f"ANNEAL_CAPTURE={real_root / 'bin/anneal-rustc-capture'}")
    print(f"ANNEAL_SYSROOT={real_root / 'rust'}")
    print(f"RUSTC={real_root / 'rust/bin/rustc'}")
    print(f"RUSTDOC={real_root / 'rust/bin/rustdoc'}")
    print(f"LD_LIBRARY_PATH={rust_lib}")
    print(f"RUSTFLAGS=-Lnative={rust_lib} -Clink-arg=-Wl,-rpath,{rust_lib}")

    if args.diagnostics is not None:
        evidence = {
            "source_revision": args.source_revision,
            "fresh_installation_root": str(real_root),
            "rustc": str(real_root / "rust/bin/rustc"),
            "rustdoc": str(real_root / "rust/bin/rustdoc"),
            "lean": str(real_root / "lean/bin/lean"),
            "driver": str(real_root / "bin/anneal-rustc-capture"),
            "inspector_source": str(
                real_root / "share/anneal/trusted/audit/TrustedBoundary.lean"
            ),
        }
        args.diagnostics.write_text(json.dumps(evidence, indent=2) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
