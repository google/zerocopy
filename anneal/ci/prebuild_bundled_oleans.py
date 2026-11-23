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
emits `<output-dir>/manifest.json` matching `cargo_anneal::olean_cache`'s v1
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
import subprocess
import sys
import tempfile

CACHE_FORMAT_VERSION = 1
OLEAN_PARTS = ("olean", "olean.server", "olean.private")
IR_PARTS = ("ir.sig", "ir")
SYSROOT_PACKAGES = ("Init", "Std", "Lean")
CANONICAL_COMPILE_FLAGS = [
    "-j1",
    "-t0",
    "-DElab.async=false",
    "-Ddebug.skipKernelTC=false",
]
TRUSTED_SOURCE_RE = re.compile(r'"(trusted/lean/(?:Trusted\.lean|Trusted/[^"]+\.lean))"')
IDENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def source_starts_with_module_keyword(raw: bytes) -> bool:
    """Mirror `stage::source_starts_with_module_keyword` across comments."""
    i = 0
    n = len(raw)
    while i < n:
        if raw[i : i + 1].isspace():
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
    return not after or after.isspace()


def module_name_from_rel(rel_path: str, prefix: str) -> str:
    if not rel_path.startswith(prefix) or not rel_path.endswith(".lean"):
        raise ValueError(f"unexpected bundled Lean path {rel_path!r} (expected prefix {prefix!r})")
    stem = rel_path[len(prefix) : -len(".lean")]
    parts = stem.split("/")
    if not all(IDENT_RE.match(p) for p in parts):
        raise ValueError(f"invalid Lean module components in {rel_path!r}")
    return ".".join(parts)


def load_trusted_module_sources(anneal_root: Path) -> dict[str, Path]:
    bundle_rs = anneal_root / "trusted/cargo-anneal/src/bundle.rs"
    text = bundle_rs.read_text(encoding="utf-8")
    start = text.find("pub const TRUSTED_BUNDLE_SOURCES")
    if start < 0:
        raise RuntimeError(f"missing TRUSTED_BUNDLE_SOURCES in {bundle_rs}")
    end = text.find("];", start)
    if end < 0:
        raise RuntimeError(f"unterminated TRUSTED_BUNDLE_SOURCES in {bundle_rs}")
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
    if manifest.get("schema_version") != 1:
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


def compute_sysroot_manifest_and_artifacts(
    lib_dir: Path,
    foundation_modules: set[str],
    library_modules: set[str],
    jobs: int,
) -> tuple[str, dict[str, list[list[str]]], dict[str, list[str]]]:
    """Compute strict `walk_and_hash_sysroot_dir` digest plus sysroot artifacts."""
    if not lib_dir.is_dir():
        raise RuntimeError(f"expected sysroot lib directory: {lib_dir}")

    files_to_hash: list[tuple[str, Path]] = []
    for pkg in SYSROOT_PACKAGES:
        for ext in OLEAN_PARTS:
            rel = f"{pkg}.{ext}"
            p = lib_dir / rel
            if p.is_symlink():
                raise RuntimeError(f"symlink forbidden in sysroot: {p}")
            if p.exists():
                if not p.is_file():
                    raise RuntimeError(f"unexpected file type in sysroot: {p}")
                files_to_hash.append((rel, p))
        pkg_dir = lib_dir / pkg
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
                if any(rel_str.endswith(f".{ext}") for ext in OLEAN_PARTS):
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

    sysroot_arts: dict[str, list[list[str]]] = {}
    sysroot_part_shas: dict[str, list[str]] = {}
    for mod in sorted(foundation_modules | library_modules):
        mod_rel = mod.replace(".", "/")
        oleans: list[str] = []
        part_shas: list[str] = []
        for ext in OLEAN_PARTS:
            p = lib_dir / f"{mod_rel}.{ext}"
            if p.is_file():
                ps = str(p)
                oleans.append(ps)
                part_shas.append(path_shas.get(ps) or sha256_file(p))
        if not oleans:
            raise RuntimeError(f"missing sysroot .olean for locked module {mod}")
        irs = [
            str(lib_dir / f"{mod_rel}.{ext}")
            for ext in IR_PARTS
            if (lib_dir / f"{mod_rel}.{ext}").is_file()
        ]
        sysroot_arts[mod] = [oleans, irs]
        sysroot_part_shas[mod] = part_shas

    return manifest_sha, sysroot_arts, sysroot_part_shas


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
    library_lock = json.loads(
        (anneal_root / "trusted/audit/library-lock.json").read_text(encoding="utf-8")
    )
    sysroot_graph: dict[str, list[dict]] = {}
    sysroot_graph.update(foundation_lock["graph"])
    sysroot_graph.update(library_lock["graph"])

    foundation_mods = set(foundation_lock["modules"].keys())
    library_mods = set(library_lock["modules"].keys())
    sysroot_manifest_sha256, sysroot_arts, dep_part_shas = compute_sysroot_manifest_and_artifacts(
        lean_prefix_resolved / "lib/lean",
        foundation_mods,
        library_mods,
        jobs,
    )

    bundled_sources: dict[str, Path] = {}
    bundled_sources.update(load_trusted_module_sources(anneal_root))
    bundled_sources.update(load_theory_module_sources(anneal_root))

    inspector_src = anneal_root / "trusted/audit/TrustedBoundary.lean"
    if not inspector_src.is_file():
        raise RuntimeError(f"missing inspector source: {inspector_src}")

    output_dir.mkdir(parents=True, exist_ok=True)
    manifest_entries: list[dict] = []

    with tempfile.TemporaryDirectory(prefix="anneal-prebuild-") as tmp_str:
        tmp = Path(tmp_str)
        control_dir = tmp / "control"
        control_dir.mkdir(parents=True)
        staged_inspector = control_dir / "TrustedBoundary.lean"
        inspector_bytes = inspector_src.read_bytes()
        staged_inspector.write_bytes(inspector_bytes)
        entry_file = control_dir / "TrustedBoundaryEntry.lean"
        entry_file.write_text("import TrustedBoundary\n", encoding="utf-8")

        inspector_out = output_dir / "TrustedBoundary.olean"
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
                f"failed compiling TrustedBoundary.lean (rc={compile_ins.returncode}):\n"
                f"stdout:\n{compile_ins.stdout}\nstderr:\n{compile_ins.stderr}"
            )
        inspector_olean_sha = sha256_file(inspector_out)
        manifest_entries.append(
            {
                "kind": "inspector",
                "module": "TrustedBoundary",
                "lean_sha256": lean_sha256,
                "sysroot_manifest_sha256": sysroot_manifest_sha256,
                "source_sha256": sha256_bytes(inspector_bytes),
                "is_module": source_starts_with_module_keyword(inspector_bytes),
                "flags": list(CANONICAL_COMPILE_FLAGS),
                "imports": [],
                "parts": [
                    {
                        "suffix": "olean",
                        "path": "TrustedBoundary.olean",
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
        shutil.copyfile(inspector_out, control_dir / "TrustedBoundary.olean")
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
        for item in parsed_headers["result"]["headers"]:
            mod = item["module"]
            bundled_edges[mod] = item["imports"]
            for edge in item["imports"]:
                dep = edge["module"]
                if dep not in bundled_sources and dep not in sysroot_graph:
                    raise RuntimeError(
                        f"bundled module {mod} imports unlocked sysroot/external module {dep}"
                    )

        full_graph = dict(sysroot_graph)
        full_graph.update(bundled_edges)
        full_arts = dict(sysroot_arts)

        # Schedule dynamic parallel compilation over the DAG of bundled modules.
        pending = set(bundled_sources.keys())
        in_flight: dict[object, tuple[str, Path, bytes, bool, list[dict]]] = {}
        compiled_entries: dict[str, dict] = {}
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
                    is_mod = source_starts_with_module_keyword(src_bytes)
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
                            }
                            for e in edges
                        ],
                        "parts": part_records,
                    }

        for mod in sorted(compiled_entries):
            manifest_entries.append(compiled_entries[mod])

    manifest = {"schema_version": CACHE_FORMAT_VERSION, "entries": manifest_entries}
    (output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
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
