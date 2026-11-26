#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Prebuild content-addressed `.olean` artifacts for bundled Anneal Lean files.

Compiles `TrustedBoundary.lean`, `trusted/lean/Trusted*.lean`, and all
`theory/bundle-manifest.json` modules against the pinned Lean toolchain and
emits `<output-dir>/manifest.json` matching `cargo_anneal::olean_cache`'s v2
key schema so cold `cargo-anneal verify` runs skip recompiling static bundled
libraries with zero new trust assumptions.
"""

from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import struct
import subprocess
import sys
import tempfile

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

try:
    from anneal_ci_lib import (  # noqa: E402
        atomic_write_text,
        default_anneal_root,
        sha256_bytes,
        sha256_file,
        sha256_raw_file as _lib_sha256_raw_file,
    )
except ImportError as exc:
    if not (
        isinstance(exc, ModuleNotFoundError)
        and exc.name == "anneal_ci_lib"
        and not (_CI_DIR / "anneal_ci_lib.py").is_file()
    ):
        raise
    # `anneal/flake.nix` copies `./ci/prebuild_bundled_oleans.py` into the Nix
    # store as a standalone single file without sibling `ci/` modules.
    def default_anneal_root(script_file: str | Path | None = None) -> Path:
        anchor = Path(script_file) if script_file is not None else Path(__file__)
        return anchor.resolve().parent.parent

    def sha256_bytes(data: bytes) -> str:
        return hashlib.sha256(data).hexdigest()

    def sha256_raw_file(path: Path) -> bytes:
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"expected regular file in sysroot: {path}")
        h = hashlib.sha256()
        with path.open("rb") as f:
            while chunk := f.read(1024 * 1024):
                h.update(chunk)
        return h.digest()

    def sha256_file(path: Path) -> str:
        h = hashlib.sha256()
        with path.open("rb") as f:
            while chunk := f.read(1024 * 1024):
                h.update(chunk)
        return h.hexdigest()

    def atomic_write_text(
        path: Path,
        text: str,
        *,
        mode: int | None = None,
    ) -> None:
        if path.is_symlink():
            raise ValueError(f"output file must not be a symlink: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        fd, tmp_name = tempfile.mkstemp(
            prefix=f".{path.name}.",
            suffix=".tmp",
            dir=str(path.parent),
        )
        tmp_path = Path(tmp_name)
        try:
            with os.fdopen(fd, "wb") as f:
                f.write(text.encode("utf-8"))
                f.flush()
                if mode is not None:
                    os.fchmod(f.fileno(), mode)
                os.fsync(f.fileno())
            os.replace(tmp_path, path)
        except BaseException:
            tmp_path.unlink(missing_ok=True)
            raise
else:
    def sha256_raw_file(path: Path) -> bytes:
        return _lib_sha256_raw_file(
            path,
            reject_symlink=True,
            missing_label="sysroot",
            exc_type=RuntimeError,
        )

CACHE_FORMAT_VERSION = 2
OLEAN_PARTS = ("olean", "olean.server", "olean.private")
IR_PARTS = ("ir.sig", "ir")
SYSROOT_MANIFEST_PARTS = OLEAN_PARTS + IR_PARTS
SYSROOT_PACKAGES = ("Init", "Std", "Lean")
LIBRARY_LOCK_TREES = (
    ("lean/lib/lean/Init/**", "lib/lean/Init"),
    ("lean/lib/lean/Std/**", "lib/lean/Std"),
    ("lean/src/lean/Init/**", "src/lean/Init"),
    ("lean/src/lean/Std/**", "src/lean/Std"),
)
CANONICAL_COMPILE_FLAGS = [
    "-j1",
    "-t0",
    "-DElab.async=false",
    "-Ddebug.skipKernelTC=false",
]
TRUSTED_SOURCE_RE = re.compile(r'"(trusted/lean/(?:Trusted\.lean|Trusted/[^"]+\.lean))"')
IDENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
SHA256_HEX_RE = re.compile(r"^[0-9a-fA-F]{64}$")


def source_starts_with_module_keyword(raw: bytes) -> bool:
    """Mirror `stage::source_starts_with_module_keyword` across comments."""
    i = 0
    n = len(raw)
    while i < n:
        if raw[i : i + 1] in b" \t\n\r\x0c":
            i += 1
            continue
        if raw[i : i + 2] == b"--":
            nl = raw.find(b"\n", i)
            i = n if nl < 0 else nl + 1
            continue
        if raw[i : i + 2] == b"/-":
            i += 2
            depth = 1
            while i < n and depth > 0:
                if raw[i : i + 2] == b"/-":
                    depth += 1
                    i += 2
                elif raw[i : i + 2] == b"-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        break
    if not raw[i:].startswith(b"module"):
        return False
    after = raw[i + 6 : i + 7]
    return not after or after in b" \t\n\r\x0c" or raw[i + 6 :].startswith((b"--", b"/-"))


def module_name_from_rel(rel_path: str, prefix: str) -> str:
    if not rel_path.startswith(prefix) or not rel_path.endswith(".lean"):
        raise ValueError(f"unexpected bundled Lean path {rel_path!r} (expected prefix {prefix!r})")
    stem = rel_path[len(prefix) : -len(".lean")]
    parts = stem.split("/")
    if not all(IDENT_RE.match(p) for p in parts):
        raise ValueError(f"invalid Lean module components in {rel_path!r}")
    return ".".join(parts)


def load_trusted_module_sources(anneal_root: Path) -> dict[str, Path]:
    trusted_bundle_rs = anneal_root / "trusted/cargo-anneal/src/trusted_bundle.rs"
    text = trusted_bundle_rs.read_text(encoding="utf-8")
    start = text.find("pub const TRUSTED_BUNDLE_SOURCES")
    if start < 0:
        raise RuntimeError(f"missing TRUSTED_BUNDLE_SOURCES in {trusted_bundle_rs}")
    end = text.find("];", start)
    if end < 0:
        raise RuntimeError(f"unterminated TRUSTED_BUNDLE_SOURCES in {trusted_bundle_rs}")
    modules: dict[str, Path] = {}
    for rel in TRUSTED_SOURCE_RE.findall(text[start:end]):
        mod = module_name_from_rel(rel, "trusted/lean/")
        path = anneal_root / rel
        if not path.is_file():
            raise RuntimeError(f"missing bundled trusted module {path}")
        modules[mod] = path
    if not modules:
        raise RuntimeError("discovered 0 bundled Trusted.* modules")
    return modules


def load_theory_module_sources(anneal_root: Path) -> dict[str, Path]:
    manifest_path = anneal_root / "theory/bundle-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("schema_version") not in (1, 2):
        raise RuntimeError(f"unsupported theory manifest schema_version in {manifest_path}")
    modules: dict[str, Path] = {}
    for entry in manifest["modules"]:
        rel = entry["path"]
        expected_sha = entry["sha256"]
        mod = module_name_from_rel(rel, "theory/")
        path = anneal_root / rel
        if not path.is_file():
            raise RuntimeError(f"missing bundled theory module {path}")
        actual_sha = sha256_file(path)
        if actual_sha != expected_sha.lower():
            raise RuntimeError(
                f"theory manifest digest mismatch for {rel}: expected {expected_sha}, got {actual_sha}"
            )
        modules[mod] = path
    if not modules:
        raise RuntimeError("discovered 0 bundled theory modules")
    return modules


def is_allowed_pinned_library_module(module: str) -> bool:
    """Return True iff `module` lies strictly beneath `Init.*` or `Std.*`."""
    parts = module.split(".")
    return (
        len(parts) >= 2
        and all(IDENT_RE.match(p) for p in parts)
        and parts[0] in ("Init", "Std")
    )


def compute_sysroot_tree_digest(root_dir: Path, jobs: int) -> str:
    """Compute recursive `<rel>\\0<32B-sha256>` tree digest matching Rust."""
    if root_dir.is_symlink():
        raise RuntimeError(f"symlink forbidden in sysroot: {root_dir}")
    if not root_dir.is_dir():
        raise RuntimeError(f"expected sysroot directory: {root_dir}")
    files: list[tuple[str, Path]] = []
    for dirpath, dirnames, filenames in os.walk(root_dir, followlinks=False):
        dp = Path(dirpath)
        for name in sorted(dirnames):
            child = dp / name
            if child.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {child}")
        for name in sorted(filenames):
            child = dp / name
            if child.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {child}")
            if not child.is_file():
                raise RuntimeError(f"unexpected file type in sysroot: {child}")
            rel_posix = child.relative_to(root_dir).as_posix()
            files.append((rel_posix, child))
    files.sort(key=lambda pair: pair[0].encode("utf-8"))
    if len(files) <= 1 or jobs <= 1:
        digests = [sha256_raw_file(p) for _, p in files]
    else:
        with ThreadPoolExecutor(max_workers=max(1, min(jobs, 4))) as pool:
            digests = list(pool.map(lambda pair: sha256_raw_file(pair[1]), files))
    outer = hashlib.sha256()
    for (rel_posix, _), digest_bytes in zip(files, digests):
        outer.update(rel_posix.encode("utf-8"))
        outer.update(b"\x00")
        outer.update(digest_bytes)
    return outer.hexdigest()


def render_library_lock_for_prefix(lean_prefix: Path, jobs: int = 1) -> str:
    """Compute canonical 4-line `library-lock.json` text for `lean_prefix`."""
    lines = [
        f"{compute_sysroot_tree_digest(lean_prefix / rel_dir, jobs)}  {label}\n"
        for label, rel_dir in LIBRARY_LOCK_TREES
    ]
    return "".join(lines)


def parse_and_verify_library_lock(
    library_lock_path: Path, lean_prefix: Path, jobs: int
) -> dict[str, str]:
    """Parse strict 4-line `library-lock.json` and verify all 4 sysroot trees."""
    if library_lock_path.is_symlink() or not library_lock_path.is_file():
        raise RuntimeError(f"expected regular library-lock file: {library_lock_path}")
    raw = library_lock_path.read_text(encoding="utf-8")
    if "\r" in raw:
        raise RuntimeError(f"invalid library-lock CR line ending in {library_lock_path}")
    normalized = raw[:-1] if raw.endswith("\n") else raw
    expected_labels = {label for label, _ in LIBRARY_LOCK_TREES}
    seen: dict[str, str] = {}
    for line in normalized.split("\n"):
        if "  " not in line:
            raise RuntimeError(f"invalid library-lock line in {library_lock_path}: {line!r}")
        digest, label = line.split("  ", 1)
        if not SHA256_HEX_RE.match(digest) or label not in expected_labels or label in seen:
            raise RuntimeError(f"invalid library-lock entry in {library_lock_path}: {line!r}")
        seen[label] = digest.lower()
    if len(seen) != len(LIBRARY_LOCK_TREES):
        raise RuntimeError(f"incomplete library-lock in {library_lock_path}")
    for label, rel_dir in LIBRARY_LOCK_TREES:
        actual = compute_sysroot_tree_digest(lean_prefix / rel_dir, jobs)
        if actual != seen[label]:
            raise RuntimeError(
                f"sysroot tree {label} SHA-256 mismatch: expected {seen[label]}, got {actual}"
            )
    return seen


def compute_sysroot_manifest(
    lib_dir: Path,
    jobs: int,
) -> tuple[str, dict[str, str]]:
    """Compute strict `walk_and_hash_sysroot_dir` digest over `lib/lean`."""
    if not lib_dir.is_dir():
        raise RuntimeError(f"expected sysroot lib directory: {lib_dir}")

    files_to_hash: list[tuple[str, Path]] = []
    for pkg in SYSROOT_PACKAGES:
        for ext in SYSROOT_MANIFEST_PARTS:
            rel = f"{pkg}.{ext}"
            p = lib_dir / rel
            if p.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {p}")
            if p.exists():
                if not p.is_file():
                    raise RuntimeError(f"unexpected file type in sysroot: {p}")
                files_to_hash.append((rel, p))
        pkg_dir = lib_dir / pkg
        if pkg_dir.is_symlink():
            raise RuntimeError(f"symlink forbidden in sysroot: {pkg_dir}")
        if pkg_dir.exists() and not pkg_dir.is_dir():
            raise RuntimeError(f"unexpected file type in sysroot: {pkg_dir}")
        for dirpath, dirnames, filenames in os.walk(pkg_dir, followlinks=False):
            dp = Path(dirpath)
            for name in sorted(dirnames):
                child = dp / name
                if child.is_symlink():
                    raise RuntimeError(f"symlink forbidden in sysroot: {child}")
            for name in sorted(filenames):
                child = dp / name
                if child.is_symlink():
                    raise RuntimeError(f"symlink forbidden in sysroot: {child}")
                if not child.is_file():
                    raise RuntimeError(f"unexpected file type in sysroot: {child}")
                rel_str = child.relative_to(lib_dir).as_posix()
                if any(rel_str.endswith(f".{ext}") for ext in SYSROOT_MANIFEST_PARTS):
                    files_to_hash.append((rel_str, child))

    # Hash sysroot files in parallel, matching `walk_and_hash_sysroot_dir`.
    path_shas: dict[str, str] = {}
    with ThreadPoolExecutor(max_workers=max(1, min(jobs, 4))) as pool:
        futs = {pool.submit(sha256_file, p): (rel, p) for rel, p in files_to_hash}
        entries: list[tuple[str, str]] = []
        for fut in futs:
            rel, path = futs[fut]
            digest = fut.result()
            entries.append((rel, digest))
            path_shas[str(path)] = digest
    entries.sort(key=lambda pair: pair[0])
    manifest_text = "".join(f"{rel}:{sha}\n" for rel, sha in entries)
    manifest_sha = sha256_bytes(manifest_text.encode("utf-8"))
    return manifest_sha, path_shas


def collect_sysroot_artifacts(
    lib_dir: Path,
    sysroot_modules: set[str],
    path_shas: dict[str, str],
) -> tuple[dict[str, list[list[str]]], dict[str, list[str]]]:
    """Collect `.olean*` and `.ir*` artifacts for resolved sysroot modules."""
    sysroot_arts: dict[str, list[list[str]]] = {}
    sysroot_part_shas: dict[str, list[str]] = {}
    for mod in sorted(sysroot_modules):
        mod_rel = mod.replace(".", "/")
        oleans: list[str] = []
        part_shas: list[str] = []
        for ext in OLEAN_PARTS:
            p = lib_dir / f"{mod_rel}.{ext}"
            if p.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {p}")
            if p.is_file():
                ps = str(p)
                oleans.append(ps)
                part_shas.append(path_shas.get(ps) or sha256_file(p))
        if not oleans:
            raise RuntimeError(f"missing sysroot .olean for module {mod}")
        irs = []
        for ext in IR_PARTS:
            p = lib_dir / f"{mod_rel}.{ext}"
            if p.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {p}")
            if p.is_file():
                irs.append(str(p))
        sysroot_arts[mod] = [oleans, irs]
        sysroot_part_shas[mod] = part_shas

    return sysroot_arts, sysroot_part_shas


def run_lean(
    lean_exec: Path,
    args: list[str],
    *,
    cwd: Path,
    lean_path: str | None = None,
) -> subprocess.CompletedProcess[str]:
    env: dict[str, str] = {}
    for k in (
        "HOME",
        "TMPDIR",
        "LANG",
        "LC_ALL",
        "LEAN_SYSROOT",
        "LD_LIBRARY_PATH",
        "DYLD_LIBRARY_PATH",
    ):
        if k in os.environ:
            env[k] = os.environ[k]
    env["PATH"] = os.environ.get("PATH", "/usr/bin:/bin")
    if lean_path is not None:
        env["LEAN_PATH"] = lean_path
    return subprocess.run(
        [str(lean_exec), *args],
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
    )


def validate_resolved_library_graph(
    resolved_graph: dict[str, list[dict]],
    resolve_roots: set[str],
    foundation_graph: dict[str, list[dict]],
) -> None:
    """Verify `resolve-imports` output contains only pinned `Init.*`/`Std.*` modules."""
    for req_mod in sorted(resolve_roots):
        if req_mod not in resolved_graph:
            raise RuntimeError(f"resolve-imports omitted requested root {req_mod}")
    for mod_name, edges in resolved_graph.items():
        if not is_allowed_pinned_library_module(mod_name):
            raise RuntimeError(f"resolve-imports returned disallowed module {mod_name}")
        for edge in edges:
            edge_mod = edge["module"]
            if edge_mod not in resolved_graph:
                raise RuntimeError(
                    f"resolve-imports graph missing edge {mod_name} -> {edge_mod}"
                )
            if not is_allowed_pinned_library_module(edge_mod):
                raise RuntimeError(
                    f"resolve-imports returned disallowed edge {mod_name} -> {edge_mod}"
                )
        if mod_name in foundation_graph and foundation_graph[mod_name] != edges:
            raise RuntimeError(
                f"resolved foundation import edges changed for {mod_name}"
            )


def transitive_closure(graph: dict[str, list[dict]], direct_edges: list[dict]) -> list[str]:
    seen: set[str] = set()
    stack = [e["module"] for e in direct_edges]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        for edge in graph.get(mod, ()):
            dep = edge["module"]
            if dep not in seen:
                stack.append(dep)
    return sorted(seen)


def _feed_len_str(h, value: str) -> None:
    raw = value.encode("utf-8")
    h.update(struct.pack("<Q", len(raw)))
    h.update(raw)


def compute_transitive_module_sha256(
    module: str,
    dep_part_shas: dict[str, list[str]],
    full_graph: dict[str, list[dict]],
    memo: dict[str, str],
    visiting: set[str],
) -> str:
    """Compute canonical bottom-up Merkle digest matching `olean_cache.rs`."""
    cached = memo.get(module)
    if cached is not None:
        return cached
    if module in visiting:
        raise RuntimeError(f"import cycle detected at {module}")
    if module not in dep_part_shas:
        raise RuntimeError(f"missing artifact digests for import {module}")
    if module not in full_graph:
        raise RuntimeError(f"missing import graph entry for {module}")
    visiting.add(module)
    try:
        part_shas = dep_part_shas[module]
        sorted_edges = sorted(
            full_graph[module],
            key=lambda e: (e["module"], bool(e["isExported"]), bool(e["importAll"]), bool(e["isMeta"])),
        )
        dep_hashes = [
            compute_transitive_module_sha256(
                e["module"], dep_part_shas, full_graph, memo, visiting
            )
            for e in sorted_edges
        ]
        h = hashlib.sha256()
        h.update(b"anneal-olean-transitive-v1\0")
        h.update(struct.pack("<Q", len(part_shas)))
        for sha in part_shas:
            _feed_len_str(h, sha.lower())
        h.update(struct.pack("<Q", len(sorted_edges)))
        for edge, dep_transitive in zip(sorted_edges, dep_hashes):
            _feed_len_str(h, edge["module"])
            h.update(
                bytes(
                    [
                        int(bool(edge["isExported"])),
                        int(bool(edge["importAll"])),
                        int(bool(edge["isMeta"])),
                    ]
                )
            )
            _feed_len_str(h, dep_transitive.lower())
        digest = h.hexdigest()
        memo[module] = digest
        return digest
    finally:
        visiting.remove(module)


def compute_cache_key(entry: dict) -> str:
    """Mirror `OleanCacheKeyInput::cache_key` (`v2`) for manifest entries."""
    h = hashlib.sha256()
    h.update(b"anneal-olean-cache-v2\0")
    kind = entry["kind"]
    if kind == "inspector":
        h.update(b"inspector\0")
    elif kind == "module":
        h.update(b"module\0")
    else:
        raise ValueError(f"unexpected cache entry kind {kind!r}")
    _feed_len_str(h, entry["module"])
    _feed_len_str(h, entry["lean_sha256"].lower())
    _feed_len_str(h, entry["sysroot_manifest_sha256"].lower())
    _feed_len_str(h, entry["source_sha256"].lower())
    h.update(bytes([int(bool(entry["is_module"]))]))
    flags = entry["flags"]
    h.update(struct.pack("<Q", len(flags)))
    for flag in flags:
        _feed_len_str(h, flag)
    imports = entry["imports"]
    h.update(struct.pack("<Q", len(imports)))
    for imp in imports:
        _feed_len_str(h, imp["module"])
        h.update(
            bytes(
                [
                    int(bool(imp["is_exported"])),
                    int(bool(imp["import_all"])),
                    int(bool(imp["is_meta"])),
                ]
            )
        )
        part_shas = imp["part_sha256s"]
        h.update(struct.pack("<Q", len(part_shas)))
        for sha in part_shas:
            _feed_len_str(h, sha.lower())
        _feed_len_str(h, imp["transitive_sha256"].lower())
    return h.hexdigest()


def prebuild(
    *,
    anneal_root: Path,
    lean_bin: Path,
    lean_exec: Path,
    lean_prefix: Path,
    output_dir: Path,
    jobs: int,
) -> dict:
    lean_bin_resolved = lean_bin.resolve(strict=True)
    lean_exec_resolved = lean_exec.resolve(strict=True)
    lean_prefix_resolved = lean_prefix.resolve(strict=True)
    if not lean_bin_resolved.is_file():
        raise RuntimeError(f"missing --lean-bin executable: {lean_bin_resolved}")
    if not lean_exec_resolved.is_file():
        raise RuntimeError(f"missing --lean-exec executable: {lean_exec_resolved}")

    lean_sha256 = sha256_file(lean_bin_resolved)
    foundation_lock = json.loads(
        (anneal_root / "trusted/lean/foundation-lock.json").read_text(encoding="utf-8")
    )
    parse_and_verify_library_lock(
        anneal_root / "trusted/audit/library-lock.json",
        lean_prefix_resolved,
        jobs,
    )
    foundation_graph: dict[str, list[dict]] = dict(foundation_lock["graph"])
    sysroot_graph: dict[str, list[dict]] = dict(foundation_graph)

    foundation_mods = set(foundation_lock["modules"].keys())
    sysroot_manifest_sha256, path_shas = compute_sysroot_manifest(
        lean_prefix_resolved / "lib/lean",
        jobs,
    )

    bundled_sources: dict[str, Path] = {}
    bundled_sources.update(load_trusted_module_sources(anneal_root))
    bundled_sources.update(load_theory_module_sources(anneal_root))

    inspector_sources: dict[str, Path] = {}
    for stem in ("TrustedBoundary", "SpecPreflight"):
        src = anneal_root / f"trusted/audit/{stem}.lean"
        if not src.is_file():
            raise RuntimeError(f"missing inspector source: {src}")
        inspector_sources[stem] = src

    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_entries: list[dict] = []

    with tempfile.TemporaryDirectory(prefix="anneal-prebuild-") as tmp_str:
        tmp = Path(tmp_str)
        control_dir = tmp / "control"
        control_dir.mkdir(parents=True)
        entry_file = control_dir / "TrustedBoundaryEntry.lean"
        entry_file.write_text("import TrustedBoundary\n", encoding="utf-8")

        inspector_outputs: dict[str, Path] = {}
        for stem, inspector_src in inspector_sources.items():
            staged_inspector = control_dir / f"{stem}.lean"
            inspector_bytes = inspector_src.read_bytes()
            staged_inspector.write_bytes(inspector_bytes)

            inspector_out = output_dir / f"{stem}.olean"
            compile_ins = run_lean(
                lean_exec_resolved,
                [
                    *CANONICAL_COMPILE_FLAGS[:1],
                    "-M2048",
                    *CANONICAL_COMPILE_FLAGS[1:],
                    "-R",
                    str(control_dir),
                    "-o",
                    str(inspector_out),
                    str(staged_inspector),
                ],
                cwd=tmp,
                lean_path=str(lean_prefix_resolved / "lib/lean"),
            )
            if compile_ins.returncode != 0:
                raise RuntimeError(
                    f"failed compiling {stem}.lean (rc={compile_ins.returncode}):\n"
                    f"stdout:\n{compile_ins.stdout}\nstderr:\n{compile_ins.stderr}"
                )
            inspector_outputs[stem] = inspector_out
            inspector_olean_sha = sha256_file(inspector_out)
            manifest_entries.append(
                {
                    "kind": "inspector",
                    "module": stem,
                    "lean_sha256": lean_sha256,
                    "sysroot_manifest_sha256": sysroot_manifest_sha256,
                    "source_sha256": sha256_bytes(inspector_bytes),
                    "is_module": source_starts_with_module_keyword(inspector_bytes),
                    "flags": list(CANONICAL_COMPILE_FLAGS),
                    "imports": [],
                    "parts": [
                        {
                            "suffix": "olean",
                            "path": f"{stem}.olean",
                            "sha256": inspector_olean_sha,
                        }
                    ],
                }
            )

        # Reuse compiled `TrustedBoundary.olean` directly to parse headers cleanly.
        headers_req = tmp / "headers.req.json"
        headers_res = tmp / "headers.res.json"
        headers_req.write_text(
            json.dumps(
                {
                    "mode": "headers",
                    "sysroot": str(lean_prefix_resolved),
                    "foundation": sorted(foundation_mods),
                    "sources": [[m, str(bundled_sources[m])] for m in sorted(bundled_sources)],
                }
            ),
            encoding="utf-8",
        )
        # Copy `TrustedBoundary.olean` into `control_dir` so `LEAN_PATH=control`
        # resolves without exposing anything else in `output_dir`.
        shutil.copyfile(inspector_outputs["TrustedBoundary"], control_dir / "TrustedBoundary.olean")
        headers_proc = run_lean(
            lean_exec_resolved,
            ["-j1", "-M2048", "--run", str(entry_file), str(headers_req), str(headers_res)],
            cwd=tmp,
            lean_path=os.pathsep.join(
                [str(control_dir), str(lean_prefix_resolved / "lib/lean")]
            ),
        )
        if headers_proc.returncode != 0:
            raise RuntimeError(
                f"TrustedBoundary headers failed (rc={headers_proc.returncode}):\n"
                f"stdout:\n{headers_proc.stdout}\nstderr:\n{headers_proc.stderr}"
            )
        parsed_headers = json.loads(headers_res.read_text(encoding="utf-8"))
        if not parsed_headers.get("ok"):
            raise RuntimeError(f"TrustedBoundary headers returned failure: {parsed_headers}")

        bundled_edges: dict[str, list[dict]] = {}
        bundled_is_module: dict[str, bool] = {}
        resolve_roots: set[str] = set()
        for item in parsed_headers["result"]["headers"]:
            mod = item["module"]
            bundled_edges[mod] = item["imports"]
            if "isModule" in item:
                bundled_is_module[mod] = bool(item["isModule"])
            else:
                bundled_is_module[mod] = source_starts_with_module_keyword(
                    bundled_sources[mod].read_bytes()
                )
            for edge in item["imports"]:
                dep = edge["module"]
                if dep in bundled_sources or dep in sysroot_graph:
                    continue
                if not is_allowed_pinned_library_module(dep):
                    raise RuntimeError(
                        f"bundled module {mod} imports disallowed external module {dep}"
                    )
                resolve_roots.add(dep)

        if resolve_roots:
            resolve_req = tmp / "resolve.req.json"
            resolve_res = tmp / "resolve.res.json"
            resolve_req.write_text(
                json.dumps(
                    {
                        "mode": "resolve-imports",
                        "sysroot": str(lean_prefix_resolved),
                        "modules": sorted(resolve_roots),
                    }
                ),
                encoding="utf-8",
            )
            resolve_proc = run_lean(
                lean_exec_resolved,
                ["-j1", "-M2048", "--run", str(entry_file), str(resolve_req), str(resolve_res)],
                cwd=tmp,
                lean_path=os.pathsep.join(
                    [str(control_dir), str(lean_prefix_resolved / "lib/lean")]
                ),
            )
            if resolve_proc.returncode != 0:
                raise RuntimeError(
                    f"TrustedBoundary resolve-imports failed (rc={resolve_proc.returncode}):\n"
                    f"stdout:\n{resolve_proc.stdout}\nstderr:\n{resolve_proc.stderr}"
                )
            parsed_resolve = json.loads(resolve_res.read_text(encoding="utf-8"))
            if not parsed_resolve.get("ok"):
                raise RuntimeError(
                    f"TrustedBoundary resolve-imports returned failure: {parsed_resolve}"
                )
            resolved_graph = parsed_resolve["result"]["graph"]
            validate_resolved_library_graph(resolved_graph, resolve_roots, foundation_graph)
            sysroot_graph.update(resolved_graph)

        for mod, edges in bundled_edges.items():
            for edge in edges:
                dep = edge["module"]
                if dep not in bundled_sources and dep not in sysroot_graph:
                    raise RuntimeError(
                        f"bundled module {mod} imports unresolved external module {dep}"
                    )

        sysroot_mods = foundation_mods | set(sysroot_graph.keys())
        sysroot_arts, dep_part_shas = collect_sysroot_artifacts(
            lean_prefix_resolved / "lib/lean",
            sysroot_mods,
            path_shas,
        )

        full_graph = dict(sysroot_graph)
        full_graph.update(bundled_edges)
        full_arts = dict(sysroot_arts)

        # Schedule dynamic parallel compilation over the DAG of bundled modules.
        pending = set(bundled_sources.keys())
        in_flight: dict[object, tuple[str, Path, bytes, bool, list[dict]]] = {}
        compiled_entries: dict[str, dict] = {}
        transitive_memo: dict[str, str] = {}
        setup_dir = tmp / "setups"
        setup_dir.mkdir(parents=True)

        with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
            while pending or in_flight:
                ready = sorted(
                    m
                    for m in pending
                    if all(e["module"] not in pending and e["module"] not in {v[0] for v in in_flight.values()} for e in bundled_edges[m])
                )
                for mod in ready:
                    pending.remove(mod)
                    edges = bundled_edges[mod]
                    closure = transitive_closure(full_graph, edges)
                    import_arts = {dep: full_arts[dep] for dep in closure}
                    src_path = bundled_sources[mod]
                    src_bytes = src_path.read_bytes()
                    is_mod = bundled_is_module[mod]
                    setup_path = setup_dir / f"{mod}.setup.json"
                    setup_path.write_text(
                        json.dumps(
                            {
                                "name": mod,
                                "isModule": is_mod,
                                "imports": edges,
                                "importArts": import_arts,
                                "dynlibs": [],
                                "plugins": [],
                                "options": {},
                            }
                        ),
                        encoding="utf-8",
                    )
                    out_olean = output_dir / "lib" / f"{mod.replace('.', '/')}.olean"
                    out_olean.parent.mkdir(parents=True, exist_ok=True)
                    args = [
                        CANONICAL_COMPILE_FLAGS[0],
                        "-M2048",
                        *CANONICAL_COMPILE_FLAGS[1:],
                        "--setup",
                        str(setup_path),
                        "-o",
                        str(out_olean),
                        str(src_path),
                    ]
                    fut = pool.submit(run_lean, lean_exec_resolved, args, cwd=tmp)
                    in_flight[fut] = (mod, out_olean, src_bytes, is_mod, edges)

                if not in_flight:
                    raise RuntimeError(f"dependency cycle across bundled modules: {sorted(pending)}")

                done, _ = wait(in_flight.keys(), return_when=FIRST_COMPLETED)
                for fut in done:
                    mod, out_olean, src_bytes, is_mod, edges = in_flight.pop(fut)
                    res = fut.result()
                    if res.returncode != 0:
                        raise RuntimeError(
                            f"failed compiling bundled module {mod} (rc={res.returncode}):\n"
                            f"stdout:\n{res.stdout}\nstderr:\n{res.stderr}"
                        )
                    rel_stem = f"lib/{mod.replace('.', '/')}"
                    oleans: list[str] = []
                    part_shas: list[str] = []
                    part_records: list[dict] = []
                    for ext in OLEAN_PARTS:
                        part_file = output_dir / f"{rel_stem}.{ext}"
                        if part_file.is_file():
                            sha = sha256_file(part_file)
                            oleans.append(str(part_file))
                            part_shas.append(sha)
                            part_records.append(
                                {
                                    "suffix": ext,
                                    "path": f"{rel_stem}.{ext}",
                                    "sha256": sha,
                                }
                            )
                    if not part_records or part_records[0]["suffix"] != "olean":
                        raise RuntimeError(f"compiler omitted primary .olean for {mod}")

                    for ext in IR_PARTS:
                        ir_file = output_dir / f"{rel_stem}.{ext}"
                        if ir_file.is_file():
                            ir_file.unlink()
                    full_arts[mod] = [oleans, []]
                    dep_part_shas[mod] = part_shas
                    compiled_entries[mod] = {
                        "kind": "module",
                        "module": mod,
                        "lean_sha256": lean_sha256,
                        "sysroot_manifest_sha256": sysroot_manifest_sha256,
                        "source_sha256": sha256_bytes(src_bytes),
                        "is_module": is_mod,
                        "flags": list(CANONICAL_COMPILE_FLAGS),
                        "imports": [
                            {
                                "module": e["module"],
                                "is_exported": e["isExported"],
                                "import_all": e["importAll"],
                                "is_meta": e["isMeta"],
                                "part_sha256s": dep_part_shas[e["module"]],
                                "transitive_sha256": compute_transitive_module_sha256(
                                    e["module"],
                                    dep_part_shas,
                                    full_graph,
                                    transitive_memo,
                                    set(),
                                ),
                            }
                            for e in edges
                        ],
                        "parts": part_records,
                    }

        for mod in sorted(compiled_entries):
            manifest_entries.append(compiled_entries[mod])

    manifest = {"schema_version": CACHE_FORMAT_VERSION, "entries": manifest_entries}
    atomic_write_text(
        output_dir / "manifest.json",
        json.dumps(manifest, indent=2) + "\n",
        mode=0o644,
    )
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=default_anneal_root(__file__),
    )
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--lean-exec", type=Path)
    parser.add_argument("--lean-prefix", type=Path)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=max(1, min(os.cpu_count() or 1, 4)))
    args = parser.parse_args()

    lean_bin = args.lean_bin
    lean_exec = args.lean_exec or lean_bin
    if args.lean_prefix is not None:
        lean_prefix = args.lean_prefix
    else:
        proc = subprocess.run(
            [str(lean_exec), "--print-prefix"], capture_output=True, text=True, check=True
        )
        lean_prefix = Path(proc.stdout.strip())

    manifest = prebuild(
        anneal_root=args.anneal_root.resolve(),
        lean_bin=lean_bin,
        lean_exec=lean_exec,
        lean_prefix=lean_prefix,
        output_dir=args.output_dir.resolve(),
        jobs=args.jobs,
    )
    print(f"Prebuilt {len(manifest['entries'])} bundled .olean entries into {args.output_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
