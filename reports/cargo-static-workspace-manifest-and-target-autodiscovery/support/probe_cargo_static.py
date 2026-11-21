#!/usr/bin/env python3
"""Static Cargo workspace/target/closure discovery prototype & differential probe.

Implements Cargo's workspace member discovery, target auto-discovery, dependency
path resolution, lockfile resolution, and `.cargo/config(.toml)` walk purely from
filesystem inspection + stdlib `tomllib` (zero `cargo`/`rustc`/build-script execution),
matching `rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0`.

Differential tests compare the static implementation against real
`cargo metadata --no-deps --format-version 1` on:
  1. All 4 workspaces of `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`
     (`zerocopy`, `anneal`, `exocrate`, `tools`) exported read-only via `git archive`.
  2. A synthetic edge-case suite exercising subtle Cargo rules + a live offline
     `cargo fetch` `.cargo/config.toml` code-execution probe.
"""

from __future__ import annotations

import dataclasses
import fnmatch
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import tomllib
from pathlib import Path
from typing import Any


# ---------------------------------------------------------------------------
# Path utilities matching `crates/cargo-util/src/paths.rs` & `pathdiff`
# ---------------------------------------------------------------------------


def normalize_path(path: Path) -> Path:
    """Lexical path normalization matching `cargo_util::paths::normalize_path`."""
    is_abs = path.is_absolute()
    parts: list[str] = []
    for part in path.parts:
        if part in ("/", ""):
            continue
        if part == ".":
            continue
        if part == "..":
            if parts and parts[-1] != "..":
                parts.pop()
            elif not is_abs:
                parts.append("..")
        else:
            parts.append(part)
    if is_abs:
        return Path("/").joinpath(*parts) if parts else Path("/")
    return Path(*parts) if parts else Path(".")


def resolve_relative_path(old_root: Path, new_root: Path, rel_path: str) -> str:
    """Matches `src/workspace/workspace.rs::resolve_relative_path` (`pathdiff::diff_paths`)."""
    joined = normalize_path(old_root / rel_path)
    return os.path.relpath(joined, new_root)


def path_starts_with(path: Path, prefix: Path) -> bool:
    """Component-wise prefix check matching Rust `Path::starts_with`."""
    p_parts = path.parts
    pre_parts = prefix.parts
    if len(pre_parts) > len(p_parts):
        return False
    return p_parts[: len(pre_parts)] == pre_parts


# ---------------------------------------------------------------------------
# Rust `glob = "0.3.3"` compatible glob expansion (`MatchOptions::new()`)
# ---------------------------------------------------------------------------


def _glob_component_regex(pat: str) -> re.Pattern[str]:
    """Translate a single path-component glob pattern to regex (`glob = 0.3.3` defaults).

    In `glob::glob` (`MatchOptions::new()`):
      - `case_sensitive = true`
      - `require_literal_separator = false` (handled per-component during dir walk)
      - `require_literal_leading_dot = false` (so `*` matches dotfiles like `.hidden`)
      - Supports `*`, `?`, `[abc]`, `[!abc]`
    """
    out = ["^"]
    i = 0
    n = len(pat)
    while i < n:
        c = pat[i]
        if c == "*":
            out.append(".*")
            i += 1
        elif c == "?":
            out.append(".")
            i += 1
        elif c == "[":
            j = i + 1
            if j < n and pat[j] == "!":
                j += 1
            if j < n and pat[j] == "]":
                j += 1
            while j < n and pat[j] != "]":
                j += 1
            if j >= n:
                out.append(r"\[")
                i += 1
            else:
                inner = pat[i + 1 : j]
                if inner.startswith("!"):
                    inner = "^" + inner[1:]
                inner = inner.replace("\\", r"\\")
                out.append(f"[{inner}]")
                i = j + 1
        else:
            out.append(re.escape(c))
            i += 1
    out.append("$")
    return re.compile("".join(out))


def expand_cargo_member_glob(root_dir: Path, pattern: str) -> list[Path]:
    """Expand a `workspace.members` / `default-members` glob matching `glob::glob`.

    Uses `root_dir / pattern` as passed to `glob::glob`.
    Returns sorted matching paths (both files and dirs, before Cargo's `is_dir()` filter).
    """
    joined = root_dir / pattern
    # Split pattern into root anchor + relative components
    # Normalize redundant slashes but keep `..` intact as `Path.parts` does.
    parts = list(joined.parts)
    if not parts:
        return []
    if parts[0] == "/":
        base = Path("/")
        comps = parts[1:]
    else:
        base = Path(".")
        comps = parts

    results: set[Path] = set()

    def walk(cur: Path, idx: int) -> None:
        if idx == len(comps):
            if cur.exists() or cur.is_symlink():
                results.add(cur)
            return
        comp = comps[idx]
        if comp == "**":
            # `**` matches 0 or more directory levels (including dotfiles!)
            walk(cur, idx + 1)
            if cur.is_dir():
                try:
                    entries = sorted(os.scandir(cur), key=lambda e: e.name)
                except OSError:
                    return
                for entry in entries:
                    if entry.is_dir(follow_symlinks=True):
                        walk(cur / entry.name, idx)
        elif any(ch in comp for ch in "*?["):
            if not cur.is_dir():
                return
            rx = _glob_component_regex(comp)
            try:
                entries = sorted(os.scandir(cur), key=lambda e: e.name)
            except OSError:
                return
            for entry in entries:
                if rx.match(entry.name):
                    walk(cur / entry.name, idx + 1)
        else:
            nxt = cur / comp
            if idx + 1 == len(comps):
                if nxt.exists() or nxt.is_symlink():
                    results.add(nxt)
            else:
                if nxt.is_dir():
                    walk(nxt, idx + 1)

    walk(base, 0)
    return sorted(results)


# ---------------------------------------------------------------------------
# Static Cargo data structures
# ---------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class StaticTarget:
    kinds: tuple[str, ...]
    name: str
    src_path: str  # absolute normalized path


@dataclasses.dataclass(frozen=True)
class StaticPathDep:
    name: str          # actual package name (`package` if renamed, else toml key)
    rename: str | None # toml key if `package` is specified, else None
    kind: str | None   # None (normal), "dev", "build"
    target: str | None # cfg/triple string from `[target.<k>.*]`
    path: str          # absolute normalized directory path


@dataclasses.dataclass
class StaticPackage:
    name: str
    edition: str
    manifest_path: str
    package_root: str
    readme: str | None
    license_file: str | None
    targets: list[StaticTarget]
    path_deps: list[StaticPathDep]
    include: list[str]
    exclude: list[str]
    has_workspace_table: bool
    package_workspace_pointer: str | None
    unsupported_features: list[str]


@dataclasses.dataclass
class StaticConfigFile:
    path: str
    precedence_rank: int  # 0 = highest precedence (closest to cwd)
    included_from: str | None
    vendored_dirs: list[str]
    local_registries: list[str]
    patch_paths: list[str]
    lockfile_path: str | None
    exec_or_network_keys: list[str]


@dataclasses.dataclass
class StaticWorkspaceDiscovery:
    workspace_root: str
    root_manifest: str
    is_virtual: bool
    members: dict[str, StaticPackage]        # manifest_path -> StaticPackage
    default_members: list[str]               # manifest_paths
    external_path_deps: dict[str, StaticPackage]  # transitive path deps outside members
    patch_path_deps: list[str]               # resolved dirs from root `[patch]` & config `[patch]`
    replace_path_deps: list[str]             # resolved dirs from root `[replace]`
    lockfile_path: str                       # resolved Cargo.lock path
    lockfile_exists: bool
    config_files: list[StaticConfigFile]
    rust_toolchain_files: list[str]          # informational (rustup, not cargo)
    warnings: list[str]


DEFAULT_README_FILES = ("README.md", "README.txt", "README")

# Config keys that execute external commands, alter compiler/linker/runner, or
# affect network / credential / source resolution during `cargo fetch` or build.
DANGEROUS_CONFIG_PATHS: tuple[tuple[str, ...], ...] = (
    ("build", "rustc"),
    ("build", "rustc-wrapper"),
    ("build", "rustc-workspace-wrapper"),
    ("build", "rustdoc"),
    ("build", "dep-info-basedir"),
    ("alias",),
    ("credential-alias",),
    ("registry", "global-credential-providers"),
    ("registries",),
    ("net", "git-fetch-with-cli"),
    ("http", "proxy"),
    ("http", "cainfo"),
    ("env",),
    ("target",),
    ("source",),
    ("patch",),
    ("paths",),
    ("path-bases",),
    ("resolver", "lockfile-path"),
)


# ---------------------------------------------------------------------------
# Static `.cargo/config(.toml)` & `rust-toolchain(.toml)` discovery
# ---------------------------------------------------------------------------


def _resolve_config_root_rel(config_file: Path, rel: str) -> Path:
    """Matches `Definition::root`: directory ABOVE `.cargo/config.toml`."""
    root = config_file.parent.parent
    p = Path(rel)
    return normalize_path(p if p.is_absolute() else root / p)


def _resolve_config_parent_rel(config_file: Path, rel: str) -> Path:
    """Matches `Definition::parent`: directory containing the config file (`.cargo/`)."""
    parent = config_file.parent
    p = Path(rel)
    return normalize_path(p if p.is_absolute() else parent / p)


def _find_config_in_dir(cargo_dir: Path) -> Path | None:
    """Matches `ConfigLoader::get_file_path`: `.cargo/config` wins over `.cargo/config.toml`."""
    legacy = cargo_dir / "config"
    toml_path = cargo_dir / "config.toml"
    if legacy.exists():
        return legacy
    if toml_path.exists():
        return toml_path
    return None


def discover_cargo_configs(
    cwd: Path,
    *,
    stop_at: Path | None = None,
    cargo_home: Path | None = None,
) -> list[StaticConfigFile]:
    """Walk ancestors from `cwd` matching `ConfigLoader::walk_tree` + `include`."""
    cwd = normalize_path(cwd.resolve())
    stop_norm = normalize_path(stop_at.resolve()) if stop_at else None

    discovered_paths: list[tuple[Path, str | None]] = []
    seen_dirs: set[Path] = set()

    cur = cwd
    while True:
        cargo_dir = cur / ".cargo"
        cfg = _find_config_in_dir(cargo_dir)
        if cfg is not None:
            discovered_paths.append((cfg, None))
        try:
            seen_dirs.add(cargo_dir.resolve())
        except OSError:
            seen_dirs.add(cargo_dir)
        if stop_norm is not None and cur == stop_norm:
            break
        if cur.parent == cur:
            break
        cur = cur.parent

    if cargo_home is not None:
        ch_res = cargo_home.resolve() if cargo_home.exists() else cargo_home
        if ch_res not in seen_dirs and cargo_home not in seen_dirs:
            cfg = _find_config_in_dir(cargo_home)
            if cfg is not None:
                discovered_paths.append((cfg, None))

    # Expand `include` recursively (precedence: including file > included files)
    ordered_configs: list[StaticConfigFile] = []
    seen_files: set[Path] = set()

    def parse_one(cfg_path: Path, included_from: str | None) -> None:
        norm = normalize_path(cfg_path)
        if norm in seen_files:
            raise ValueError(f"config `include` cycle detected: {norm}")
        seen_files.add(norm)
        with open(norm, "rb") as f:
            data = tomllib.load(f)

        vendored: list[str] = []
        local_regs: list[str] = []
        patch_paths: list[str] = []
        lockfile_override: str | None = None
        dangerous: list[str] = []

        # Inspect `[source.*]`
        sources = data.get("source")
        if isinstance(sources, dict):
            for sname, sdef in sources.items():
                if isinstance(sdef, dict):
                    if isinstance(sdef.get("directory"), str):
                        vendored.append(str(_resolve_config_root_rel(norm, sdef["directory"])))
                    if isinstance(sdef.get("local-registry"), str):
                        local_regs.append(str(_resolve_config_root_rel(norm, sdef["local-registry"])))

        # Inspect `[patch.*]`
        patches = data.get("patch")
        if isinstance(patches, dict):
            for _src, pmap in patches.items():
                if isinstance(pmap, dict):
                    for _pkg, pdep in pmap.items():
                        if isinstance(pdep, dict) and isinstance(pdep.get("path"), str):
                            patch_paths.append(str(_resolve_config_root_rel(norm, pdep["path"])))

        # Inspect `[resolver] lockfile-path`
        resolver = data.get("resolver")
        if isinstance(resolver, dict) and isinstance(resolver.get("lockfile-path"), str):
            lockfile_override = str(_resolve_config_root_rel(norm, resolver["lockfile-path"]))

        # Audit executable / network / environment / override keys
        for key_path in DANGEROUS_CONFIG_PATHS:
            node: Any = data
            found = True
            for k in key_path:
                if isinstance(node, dict) and k in node:
                    node = node[k]
                else:
                    found = False
                    break
            if found:
                dangerous.append(".".join(key_path))

        rank = len(ordered_configs)
        ordered_configs.append(
            StaticConfigFile(
                path=str(norm),
                precedence_rank=rank,
                included_from=included_from,
                vendored_dirs=vendored,
                local_registries=local_regs,
                patch_paths=patch_paths,
                lockfile_path=lockfile_override,
                exec_or_network_keys=dangerous,
            )
        )

        # Follow `include` (lower precedence than the file containing it)
        inc_val = data.get("include")
        if inc_val is not None:
            entries = inc_val if isinstance(inc_val, list) else [inc_val]
            for entry in entries:
                if isinstance(entry, str):
                    inc_path = _resolve_config_parent_rel(norm, entry)
                    optional = False
                elif isinstance(entry, dict) and isinstance(entry.get("path"), str):
                    inc_path = _resolve_config_parent_rel(norm, entry["path"])
                    optional = bool(entry.get("optional", False))
                else:
                    continue
                if optional and not inc_path.exists():
                    continue
                parse_one(inc_path, str(norm))

    for cfg_path, inc_from in discovered_paths:
        parse_one(cfg_path, inc_from)

    return ordered_configs


def discover_rust_toolchain_files(cwd: Path, *, stop_at: Path | None = None) -> list[str]:
    """Walk ancestors matching `rustup/src/config.rs::find_override_from_dir_walk`."""
    cwd = normalize_path(cwd.resolve())
    stop_norm = normalize_path(stop_at.resolve()) if stop_at else None
    found: list[str] = []
    cur = cwd
    while True:
        # `rust-toolchain` wins over `rust-toolchain.toml` if both exist in same dir
        legacy = cur / "rust-toolchain"
        toml_f = cur / "rust-toolchain.toml"
        if legacy.is_file():
            found.append(str(legacy))
        elif toml_f.is_file():
            found.append(str(toml_f))
        if stop_norm is not None and cur == stop_norm:
            break
        if cur.parent == cur:
            break
        cur = cur.parent
    return found


# ---------------------------------------------------------------------------
# Static Manifest & Workspace Parser
# ---------------------------------------------------------------------------


class StaticCargoAnalyzer:
    def __init__(self, *, search_stop_at: Path | None = None, cargo_home: Path | None = None):
        self.search_stop_at = normalize_path(search_stop_at.resolve()) if search_stop_at else None
        self.cargo_home = normalize_path(cargo_home.resolve()) if cargo_home else None
        self._raw_cache: dict[Path, dict[str, Any]] = {}
        self.warnings: list[str] = []

    def _load_raw(self, manifest_path: Path) -> dict[str, Any]:
        manifest_path = normalize_path(manifest_path)
        if manifest_path not in self._raw_cache:
            with open(manifest_path, "rb") as f:
                self._raw_cache[manifest_path] = tomllib.load(f)
        return self._raw_cache[manifest_path]

    @staticmethod
    def _get_pkg_table(raw: dict[str, Any]) -> dict[str, Any] | None:
        return raw.get("package") or raw.get("project")

    @staticmethod
    def _is_excluded(root_dir: Path, ws_table: dict[str, Any], manifest_path: Path) -> bool:
        """Exact match for `WorkspaceRootConfig::is_excluded` (`src/workspace/workspace.rs:1973-1987`)."""
        excludes = ws_table.get("exclude") or []
        excluded = any(path_starts_with(manifest_path, root_dir / ex) for ex in excludes)
        members = ws_table.get("members")
        if members is not None:
            explicit_member = any(
                path_starts_with(manifest_path, root_dir / mem) for mem in members
            )
        else:
            explicit_member = False
        return (not explicit_member) and excluded

    def _get_ws_root_from_manifest(self, self_path: Path, look_from: Path) -> Path | None:
        raw = self._load_raw(self_path)
        ws = raw.get("workspace")
        pkg = self._get_pkg_table(raw)
        pkg_ws = pkg.get("workspace") if isinstance(pkg, dict) else None
        if ws is not None and pkg_ws is not None:
            raise ValueError(f"cannot specify both `[workspace]` and `package.workspace` in {self_path}")
        if ws is not None:
            root_dir = self_path.parent
            if not self._is_excluded(root_dir, ws, look_from):
                return self_path
            return None
        if isinstance(pkg_ws, str):
            return normalize_path(self_path.parent / pkg_ws / "Cargo.toml")
        return None

    def find_workspace_root(self, manifest_path: Path) -> Path | None:
        """Matches `Workspace::find_root` (`src/workspace/workspace.rs:820-838`)."""
        manifest_path = normalize_path(manifest_path)
        direct = self._get_ws_root_from_manifest(manifest_path, manifest_path)
        if direct is not None:
            return direct
        # Walk ancestors starting at `manifest_path.parent.parent` (`skip(2)` on manifest_path)
        cur = manifest_path.parent.parent
        last = manifest_path.parent
        while True:
            if cur == last:
                break
            if str(cur).endswith("target/package"):
                break
            if self.cargo_home is not None and last == self.cargo_home:
                break
            cand = cur / "Cargo.toml"
            if cand.exists():
                found = self._get_ws_root_from_manifest(cand, manifest_path)
                if found is not None:
                    return found
            if self.search_stop_at is not None and cur == self.search_stop_at:
                break
            last = cur
            cur = cur.parent
        return None

    @staticmethod
    def _expand_members_paths(root_dir: Path, globs: list[str]) -> list[tuple[Path, str | None]]:
        """Matches `WorkspaceRootConfig::members_paths` (`src/workspace/workspace.rs:2036-2068`)."""
        expanded_list: list[tuple[Path, str | None]] = []
        for g in globs:
            pathbuf = root_dir / g
            expanded = expand_cargo_member_glob(root_dir, g)
            if not expanded:
                expanded_list.append((pathbuf, None))
            else:
                used_glob = len(expanded) > 1 or expanded[0] != pathbuf
                g_label = g if used_glob else None
                for ep in expanded:
                    if ep.is_dir():
                        expanded_list.append((ep, g_label))
        return expanded_list

    # -------------------------------------------------------------------
    # Target normalization matching `src/workspace/parser/targets.rs`
    # -------------------------------------------------------------------

    @staticmethod
    def _are_normalized(toml_targets: list[dict[str, Any]] | None, autodiscover: bool | None) -> bool:
        if autodiscover is not False:
            return False
        if toml_targets is None:
            return True
        return all(("name" in t and "path" in t) for t in toml_targets)

    @staticmethod
    def _infer_from_directory(package_root: Path, relpath: Path) -> list[tuple[str, Path]]:
        """Exact match for `infer_from_directory` / `infer_any` (`targets.rs:747-798`).

        CRITICAL: Uses `entry.is_dir(follow_symlinks=False)` matching Rust
        `DirEntry::file_type().is_dir()` — symlinks to directories are NOT followed
        as subdirectories, whereas symlinks to `.rs` files match the `else if` branch!
        """
        directory = package_root / relpath
        if not directory.is_dir():
            return []
        out: list[tuple[str, Path]] = []
        try:
            entries = list(os.scandir(directory))
        except OSError:
            return []
        for entry in entries:
            if entry.name.startswith("."):
                continue
            # `follow_symlinks=False` matches `std::fs::DirEntry::file_type()`!
            is_dir = False
            try:
                is_dir = entry.is_dir(follow_symlinks=False)
            except OSError:
                is_dir = False
            if is_dir:
                main_rs = Path(entry.path) / "main.rs"
                if main_rs.exists():  # `main.exists()` follows symlinks
                    out.append((entry.name, relpath / entry.name / "main.rs"))
            elif Path(entry.name).suffix == ".rs":
                stem = Path(entry.name).stem
                out.append((stem, relpath / entry.name))
        return out

    @classmethod
    def _inferred_bins(cls, package_root: Path, package_name: str) -> list[tuple[str, Path]]:
        res: list[tuple[str, Path]] = []
        if (package_root / "src" / "main.rs").exists():
            res.append((package_name, Path("src/main.rs")))
        res.extend(cls._infer_from_directory(package_root, Path("src/bin")))
        return res

    @staticmethod
    def _legacy_bin_path(package_root: Path, name: str, has_lib: bool) -> Path | None:
        if not has_lib:
            p = Path("src") / f"{name}.rs"
            if (package_root / p).exists():
                return p
        p = Path("src/main.rs")
        if (package_root / p).exists():
            return p
        p = Path("src/bin/main.rs")
        if (package_root / p).exists():
            return p
        return None

    @staticmethod
    def _toml_targets_and_inferred(
        toml_targets: list[dict[str, Any]] | None,
        inferred: list[tuple[str, Path]],
        package_root: Path,
        autodiscover: bool | None,
        edition: str,
    ) -> list[dict[str, Any]]:
        inferred_dicts = [{"name": n, "path": str(p)} for (n, p) in inferred]
        if toml_targets is None:
            if autodiscover is False:
                res: list[dict[str, Any]] = []
            else:
                res = inferred_dicts
        else:
            targets = [dict(t) for t in toml_targets]
            seen_names = {t.get("name") for t in targets}
            seen_paths = {
                (package_root / t["path"]) if "path" in t else None for t in targets
            }
            rem = [
                t
                for t in inferred_dicts
                if t["name"] not in seen_names and (package_root / t["path"]) not in seen_paths
            ]
            if autodiscover is None:
                auto_eff = edition != "2015"
            else:
                auto_eff = autodiscover
            if auto_eff:
                targets.extend(rem)
            res = targets
        res.sort(key=lambda t: t.get("name", ""))
        return res

    @staticmethod
    def _resolve_target_path(
        target: dict[str, Any],
        inferred: list[tuple[str, Path]],
        kind: str,
        package_root: Path,
        edition: str,
        legacy_fn=None,
    ) -> Path:
        if "path" in target:
            return normalize_path(Path(target["path"]))
        name = target["name"]
        matches = [p for (n, p) in inferred if n == name]
        if len(matches) == 1:
            return normalize_path(matches[0])
        if edition == "2015" and legacy_fn is not None:
            lp = legacy_fn(target)
            if lp is not None:
                return normalize_path(lp)
        if len(matches) == 0:
            raise ValueError(f"cannot find {kind} target `{name}` in {package_root}")
        raise ValueError(f"ambiguous {kind} target `{name}` in {package_root}: {matches}")

    def _extract_targets(
        self,
        raw: dict[str, Any],
        pkg: dict[str, Any],
        package_root: Path,
        package_name: str,
        edition: str,
    ) -> list[StaticTarget]:
        targets: list[StaticTarget] = []

        # 1. [lib] (`normalize_lib`, `targets.rs:147-217`)
        orig_lib = raw.get("lib")
        autolib = pkg.get("autolib")
        lib_norm: dict[str, Any] | None = None
        if self._are_normalized([orig_lib] if orig_lib is not None else None, autolib):
            if orig_lib is not None:
                lib_norm = dict(orig_lib)
                lib_norm["path"] = str(normalize_path(Path(lib_norm["path"])))
        else:
            inferred_lib = Path("src/lib.rs") if (package_root / "src/lib.rs").exists() else None
            if orig_lib is not None:
                lib_norm = dict(orig_lib)
            elif inferred_lib is not None:
                lib_norm = {"path": str(inferred_lib)}
            if lib_norm is not None:
                lib_norm.setdefault("name", package_name.replace("-", "_"))
                if "path" not in lib_norm:
                    if inferred_lib is not None:
                        lib_norm["path"] = str(inferred_lib)
                    elif edition == "2015" and (package_root / "src" / f"{lib_norm['name']}.rs").exists():
                        lib_norm["path"] = str(Path("src") / f"{lib_norm['name']}.rs")
                    else:
                        raise ValueError(f"cannot find lib target in {package_root}")
                lib_norm["path"] = str(normalize_path(Path(lib_norm["path"])))

        if lib_norm is not None:
            crate_types = lib_norm.get("crate-type") or lib_norm.get("crate_type")
            proc_macro = lib_norm.get("proc-macro")
            if proc_macro is None:
                proc_macro = lib_norm.get("proc_macro")
            if proc_macro is None and crate_types and "proc-macro" in crate_types:
                proc_macro = True
            if crate_types:
                kinds = tuple(crate_types)
            elif proc_macro:
                kinds = ("proc-macro",)
            else:
                kinds = ("lib",)
            targets.append(
                StaticTarget(
                    kinds=kinds,
                    name=lib_norm["name"],
                    src_path=str(normalize_path(package_root / lib_norm["path"])),
                )
            )
        has_lib = lib_norm is not None

        # 2. [[bin]] (`normalize_bins`, `targets.rs:292-367`)
        orig_bins = raw.get("bin")
        autobins = pkg.get("autobins")
        if self._are_normalized(orig_bins, autobins):
            norm_bins = [dict(b) for b in (orig_bins or [])]
        else:
            inf_bins = self._inferred_bins(package_root, package_name)
            norm_bins = self._toml_targets_and_inferred(
                orig_bins, inf_bins, package_root, autobins, edition
            )
            for b in norm_bins:
                p = self._resolve_target_path(
                    b,
                    inf_bins,
                    "bin",
                    package_root,
                    edition,
                    legacy_fn=lambda t: self._legacy_bin_path(package_root, t["name"], has_lib),
                )
                b["path"] = str(p)
        for b in norm_bins:
            targets.append(
                StaticTarget(
                    kinds=("bin",),
                    name=b["name"],
                    src_path=str(normalize_path(package_root / b["path"])),
                )
            )

        # 3. [[example]], [[test]], [[bench]]
        for toml_key, dir_name, auto_key, kind_str in (
            ("example", "examples", "autoexamples", "example"),
            ("test", "tests", "autotests", "test"),
            ("bench", "benches", "autobenches", "bench"),
        ):
            orig = raw.get(toml_key)
            auto_flag = pkg.get(auto_key)
            if self._are_normalized(orig, auto_flag):
                norm_t = [dict(t) for t in (orig or [])]
            else:
                inf = self._infer_from_directory(package_root, Path(dir_name))
                norm_t = self._toml_targets_and_inferred(
                    orig, inf, package_root, auto_flag, edition
                )
                legacy_fn = None
                if kind_str == "bench":
                    legacy_fn = (
                        lambda t: Path("src/bench.rs")
                        if t["name"] == "bench" and (package_root / "src/bench.rs").is_file()
                        else None
                    )
                for t in norm_t:
                    p = self._resolve_target_path(
                        t, inf, kind_str, package_root, edition, legacy_fn=legacy_fn
                    )
                    t["path"] = str(p)
            for t in norm_t:
                targets.append(
                    StaticTarget(
                        kinds=(kind_str,),
                        name=t["name"],
                        src_path=str(normalize_path(package_root / t["path"])),
                    )
                )

        # 4. package.build (`normalize_build`, `targets.rs:1114-1150`)
        build_val = pkg.get("build")
        build_scripts: list[str] = []
        if build_val is None:
            if (package_root / "build.rs").is_file():
                build_scripts = ["build.rs"]
        elif build_val is False:
            build_scripts = []
        elif build_val is True:
            build_scripts = ["build.rs"]
        elif isinstance(build_val, str):
            build_scripts = [str(normalize_path(Path(build_val)))]
        elif isinstance(build_val, list):
            build_scripts = [str(normalize_path(Path(s))) for s in build_val]

        for script in build_scripts:
            sp = Path(script)
            targets.append(
                StaticTarget(
                    kinds=("custom-build",),
                    name=f"build-script-{sp.stem}",
                    src_path=str(normalize_path(package_root / sp)),
                )
            )

        return targets

    # -------------------------------------------------------------------
    # Package & dependency parsing with workspace inheritance
    # -------------------------------------------------------------------

    @staticmethod
    def _default_readme(root_dir: Path) -> str | None:
        for fname in DEFAULT_README_FILES:
            if (root_dir / fname).is_file():
                return fname
        return None

    @classmethod
    def _normalize_readme_val(cls, root_dir: Path, val: Any) -> str | None:
        if val is None:
            return cls._default_readme(root_dir)
        if val is False:
            return None
        if val is True:
            return "README.md"
        if isinstance(val, str):
            return val
        return None

    def _load_ws_inheritable(
        self, manifest_path: Path, ws_root_manifest: Path | None
    ) -> tuple[Path, dict[str, Any]] | None:
        if ws_root_manifest is None:
            ws_root_manifest = self.find_workspace_root(manifest_path)
        if ws_root_manifest is None:
            return None
        raw = self._load_raw(ws_root_manifest)
        ws = raw.get("workspace")
        if not isinstance(ws, dict):
            return None
        return (ws_root_manifest.parent, ws)

    def parse_package(
        self, manifest_path: Path, ws_root_manifest: Path | None = None
    ) -> StaticPackage:
        manifest_path = normalize_path(manifest_path)
        package_root = manifest_path.parent
        raw = self._load_raw(manifest_path)
        pkg = self._get_pkg_table(raw)
        if not isinstance(pkg, dict):
            raise ValueError(f"not a package manifest: {manifest_path}")

        unsupported: list[str] = []
        inh_cache: list[tuple[Path, dict[str, Any]] | None] = []

        def get_inh() -> tuple[Path, dict[str, Any]]:
            if not inh_cache:
                inh_cache.append(self._load_ws_inheritable(manifest_path, ws_root_manifest))
            if inh_cache[0] is None:
                raise ValueError(f"failed to find workspace root for inheritance in {manifest_path}")
            return inh_cache[0]

        name = pkg["name"]

        # Edition (with workspace inheritance; default "2015")
        ed_raw = pkg.get("edition")
        if isinstance(ed_raw, dict) and ed_raw.get("workspace") is True:
            _ws_dir, ws_tbl = get_inh()
            edition = str((ws_tbl.get("package") or {}).get("edition", "2015"))
        elif isinstance(ed_raw, str):
            edition = ed_raw
        else:
            edition = "2015"

        # Readme (`parser/mod.rs:774-786`, `864-890`, `1146-1155`)
        rd_raw = pkg.get("readme")
        if isinstance(rd_raw, dict) and rd_raw.get("workspace") is True:
            ws_dir, ws_tbl = get_inh()
            ws_rd = self._normalize_readme_val(ws_dir, (ws_tbl.get("package") or {}).get("readme"))
            if ws_rd is None:
                raise ValueError(f"workspace.package.readme not defined for {manifest_path}")
            readme = resolve_relative_path(ws_dir, package_root, ws_rd)
        else:
            readme = self._normalize_readme_val(package_root, rd_raw)

        # License-file (`parser/mod.rs:805-814`, `1138-1143`)
        lf_raw = pkg.get("license-file")
        if isinstance(lf_raw, dict) and lf_raw.get("workspace") is True:
            ws_dir, ws_tbl = get_inh()
            ws_lf = (ws_tbl.get("package") or {}).get("license-file")
            if not isinstance(ws_lf, str):
                raise ValueError(f"workspace.package.license-file not defined for {manifest_path}")
            license_file: str | None = resolve_relative_path(ws_dir, package_root, ws_lf)
        elif isinstance(lf_raw, str):
            license_file = lf_raw
        else:
            license_file = None

        # Include / exclude (for reporting only — NOT used to prune CI closure!)
        def inherit_list(field: str) -> list[str]:
            val = pkg.get(field)
            if isinstance(val, dict) and val.get("workspace") is True:
                _ws_dir, ws_tbl = get_inh()
                return list((ws_tbl.get("package") or {}).get(field) or [])
            return list(val or [])

        inc_list = inherit_list("include")
        exc_list = inherit_list("exclude")

        # Targets
        targets = self._extract_targets(raw, pkg, package_root, name, edition)

        # Dependencies across ALL tables
        path_deps: list[StaticPathDep] = []

        def collect_dep_table(
            tbl: dict[str, Any] | None, dep_kind: str | None, target_cfg: str | None
        ) -> None:
            if not isinstance(tbl, dict):
                return
            for toml_key, spec in tbl.items():
                if not isinstance(spec, dict):
                    continue
                resolved_spec = spec
                base_dir = package_root
                if spec.get("workspace") is True:
                    ws_dir, ws_tbl = get_inh()
                    ws_deps = ws_tbl.get("dependencies") or {}
                    if toml_key not in ws_deps:
                        raise ValueError(f"workspace dependency `{toml_key}` not found")
                    ws_spec = ws_deps[toml_key]
                    if not isinstance(ws_spec, dict):
                        continue
                    resolved_spec = ws_spec
                    base_dir = ws_dir

                if "base" in resolved_spec:
                    base_name = resolved_spec["base"]
                    if base_name == "workspace":
                        ws_dir, _ = get_inh()
                        base_dir = ws_dir
                    else:
                        unsupported.append(f"path-bases:{base_name}")
                        continue

                rel_p = resolved_spec.get("path")
                if isinstance(rel_p, str):
                    abs_dep_dir = normalize_path(base_dir / rel_p)
                    actual_pkg = resolved_spec.get("package")
                    if isinstance(actual_pkg, str):
                        dep_name = actual_pkg
                        rename: str | None = toml_key
                    else:
                        dep_name = toml_key
                        rename = None
                    path_deps.append(
                        StaticPathDep(
                            name=dep_name,
                            rename=rename,
                            kind=dep_kind,
                            target=target_cfg,
                            path=str(abs_dep_dir),
                        )
                    )

        collect_dep_table(raw.get("dependencies"), None, None)
        collect_dep_table(raw.get("dev-dependencies") or raw.get("dev_dependencies"), "dev", None)
        collect_dep_table(
            raw.get("build-dependencies") or raw.get("build_dependencies"), "build", None
        )
        targets_tbl = raw.get("target")
        if isinstance(targets_tbl, dict):
            for cfg_key, plat in targets_tbl.items():
                if not isinstance(plat, dict):
                    continue
                collect_dep_table(plat.get("dependencies"), None, cfg_key)
                collect_dep_table(
                    plat.get("build-dependencies") or plat.get("build_dependencies"),
                    "build",
                    cfg_key,
                )
                collect_dep_table(
                    plat.get("dev-dependencies") or plat.get("dev_dependencies"),
                    "dev",
                    cfg_key,
                )

        return StaticPackage(
            name=name,
            edition=edition,
            manifest_path=str(manifest_path),
            package_root=str(package_root),
            readme=readme,
            license_file=license_file,
            targets=targets,
            path_deps=path_deps,
            include=inc_list,
            exclude=exc_list,
            has_workspace_table=("workspace" in raw),
            package_workspace_pointer=pkg.get("workspace") if isinstance(pkg.get("workspace"), str) else None,
            unsupported_features=unsupported,
        )

    def discover_workspace(
        self, manifest_path: Path, *, cwd: Path | None = None
    ) -> StaticWorkspaceDiscovery:
        current_manifest = normalize_path(manifest_path.resolve())
        root_manifest_opt = self.find_workspace_root(current_manifest)
        root_manifest = root_manifest_opt if root_manifest_opt is not None else current_manifest
        ws_root_dir = root_manifest.parent

        raw_root = self._load_raw(root_manifest)
        ws_table = raw_root.get("workspace")
        is_virtual = self._get_pkg_table(raw_root) is None

        members: dict[str, StaticPackage] = {}
        member_order: list[Path] = []
        seen_members: set[Path] = set()
        ws_roots_in_members: list[Path] = []

        def find_path_deps(mp: Path, is_path_dep: bool) -> None:
            mp = normalize_path(mp)
            if mp in seen_members:
                return
            if (
                is_path_dep
                and not path_starts_with(mp.parent, ws_root_dir)
                and self.find_workspace_root(mp) != root_manifest_opt
            ):
                return
            if ws_table is not None and self._is_excluded(ws_root_dir, ws_table, mp):
                return
            seen_members.add(mp)
            member_order.append(mp)
            raw_m = self._load_raw(mp)
            if raw_m.get("workspace") is not None:
                ws_roots_in_members.append(mp.parent)
            if self._get_pkg_table(raw_m) is None:
                return
            sp = self.parse_package(mp, ws_root_manifest=root_manifest_opt)
            members[str(mp)] = sp
            for pdep in sp.path_deps:
                find_path_deps(Path(pdep.path) / "Cargo.toml", True)

        if root_manifest_opt is None:
            sp = self.parse_package(current_manifest, ws_root_manifest=None)
            members[str(current_manifest)] = sp
            member_order.append(current_manifest)
            default_members = [str(current_manifest)]
        else:
            assert isinstance(ws_table, dict)
            members_paths = self._expand_members_paths(
                ws_root_dir, list(ws_table.get("members") or [])
            )
            for p, _g in members_paths:
                find_path_deps(p / "Cargo.toml", False)
            find_path_deps(root_manifest, False)

            if len(ws_roots_in_members) > 1:
                raise ValueError(
                    f"multiple workspace roots found in the same workspace: {ws_roots_in_members}"
                )

            # `default-members` (`src/workspace/workspace.rs:865-922`)
            raw_def = ws_table.get("default-members")
            if root_manifest == current_manifest and raw_def is not None:
                def_paths = self._expand_members_paths(ws_root_dir, list(raw_def))
                default_members = []
                for p, _g in def_paths:
                    np = normalize_path(p)
                    dm = np / "Cargo.toml"
                    if str(dm) not in members:
                        in_orig = any(normalize_path(m) == np for (m, _) in members_paths)
                        if in_orig and self._is_excluded(ws_root_dir, ws_table, np):
                            continue
                        raise ValueError(f"default-member {np} is not a workspace member")
                    default_members.append(str(dm))
            elif is_virtual:
                default_members = [str(mp) for mp in member_order if str(mp) in members]
            else:
                default_members = [str(current_manifest)]

        # Extract `[patch.*]` and `[replace]` path deps from root manifest
        patch_paths: list[str] = []
        raw_patch = raw_root.get("patch")
        if isinstance(raw_patch, dict):
            for _src, pmap in raw_patch.items():
                if isinstance(pmap, dict):
                    for _pkg, spec in pmap.items():
                        if isinstance(spec, dict) and isinstance(spec.get("path"), str):
                            patch_paths.append(str(normalize_path(ws_root_dir / spec["path"])))

        replace_paths: list[str] = []
        raw_replace = raw_root.get("replace")
        if isinstance(raw_replace, dict):
            for _spec_key, spec in raw_replace.items():
                if isinstance(spec, dict) and isinstance(spec.get("path"), str):
                    replace_paths.append(str(normalize_path(ws_root_dir / spec["path"])))

        # Discover `.cargo/config(.toml)` & `rust-toolchain(.toml)` from `cwd` (default: ws_root_dir)
        effective_cwd = cwd if cwd is not None else ws_root_dir
        configs = discover_cargo_configs(
            effective_cwd, stop_at=self.search_stop_at, cargo_home=self.cargo_home
        )
        for cfg in configs:
            for pp in cfg.patch_paths:
                if pp not in patch_paths:
                    patch_paths.append(pp)

        toolchains = discover_rust_toolchain_files(effective_cwd, stop_at=self.search_stop_at)

        # Lockfile path (`resolver.lockfile-path` highest-precedence config override, else ws_root/Cargo.lock)
        lockfile_path = ws_root_dir / "Cargo.lock"
        for cfg in configs:
            if cfg.lockfile_path is not None:
                lockfile_path = Path(cfg.lockfile_path)
                break

        # Transitive closure of EXTERNAL path deps (including path deps outside ws_root
        # AND patched/replaced crates, which are NOT workspace members but ARE compiled!)
        external_path_deps: dict[str, StaticPackage] = {}
        queue: list[Path] = []
        for sp in members.values():
            for pdep in sp.path_deps:
                queue.append(Path(pdep.path) / "Cargo.toml")
        for pp in patch_paths + replace_paths:
            queue.append(Path(pp) / "Cargo.toml")

        while queue:
            mp = normalize_path(queue.pop())
            ms = str(mp)
            if ms in members or ms in external_path_deps:
                continue
            if not mp.exists():
                self.warnings.append(f"missing external path dep manifest: {mp}")
                continue
            ext_pkg = self.parse_package(mp, ws_root_manifest=None)
            external_path_deps[ms] = ext_pkg
            for pdep in ext_pkg.path_deps:
                queue.append(Path(pdep.path) / "Cargo.toml")

        return StaticWorkspaceDiscovery(
            workspace_root=str(ws_root_dir),
            root_manifest=str(root_manifest),
            is_virtual=is_virtual,
            members=members,
            default_members=default_members,
            external_path_deps=external_path_deps,
            patch_path_deps=sorted(set(patch_paths)),
            replace_path_deps=sorted(set(replace_paths)),
            lockfile_path=str(lockfile_path),
            lockfile_exists=lockfile_path.is_file(),
            config_files=configs,
            rust_toolchain_files=toolchains,
            warnings=list(self.warnings),
        )


# ---------------------------------------------------------------------------
# Differential comparison against real `cargo metadata --no-deps --format-version 1`
# ---------------------------------------------------------------------------


def run_cargo_metadata(
    manifest_path: Path, *, cwd: Path, cargo_home: Path
) -> tuple[int, dict[str, Any] | None, str]:
    env = os.environ.copy()
    env["CARGO_HOME"] = str(cargo_home)
    proc = subprocess.run(
        [
            "cargo",
            "metadata",
            "--no-deps",
            "--format-version",
            "1",
            "--manifest-path",
            str(manifest_path),
        ],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return proc.returncode, None, proc.stderr.strip()
    return 0, json.loads(proc.stdout), proc.stderr.strip()


def diff_static_vs_cargo(
    static: StaticWorkspaceDiscovery, meta: dict[str, Any]
) -> list[str]:
    diffs: list[str] = []

    if static.workspace_root != meta["workspace_root"]:
        diffs.append(
            f"workspace_root mismatch: static={static.workspace_root!r} vs cargo={meta['workspace_root']!r}"
        )

    cargo_pkgs_by_manifest = {p["manifest_path"]: p for p in meta["packages"]}
    cargo_id_to_manifest = {p["id"]: p["manifest_path"] for p in meta["packages"]}

    static_member_manifests = set(static.members.keys())
    cargo_member_manifests = {cargo_id_to_manifest[mid] for mid in meta["workspace_members"]}
    if static_member_manifests != cargo_member_manifests:
        diffs.append(
            f"workspace_members mismatch: static={sorted(static_member_manifests)} vs cargo={sorted(cargo_member_manifests)}"
        )

    static_def_manifests = set(static.default_members)
    cargo_def_manifests = {
        cargo_id_to_manifest[mid] for mid in meta.get("workspace_default_members", [])
    }
    if static_def_manifests != cargo_def_manifests:
        diffs.append(
            f"workspace_default_members mismatch: static={sorted(static_def_manifests)} vs cargo={sorted(cargo_def_manifests)}"
        )

    for mp in sorted(static_member_manifests & cargo_member_manifests):
        sp = static.members[mp]
        cp = cargo_pkgs_by_manifest[mp]

        if sp.name != cp["name"]:
            diffs.append(f"{mp}: name static={sp.name!r} vs cargo={cp['name']!r}")
        if sp.edition != cp["edition"]:
            diffs.append(f"{mp}: edition static={sp.edition!r} vs cargo={cp['edition']!r}")
        if sp.readme != cp.get("readme"):
            diffs.append(f"{mp}: readme static={sp.readme!r} vs cargo={cp.get('readme')!r}")
        if sp.license_file != cp.get("license_file"):
            diffs.append(
                f"{mp}: license_file static={sp.license_file!r} vs cargo={cp.get('license_file')!r}"
            )

        static_targets = {(tuple(sorted(t.kinds)), t.name, t.src_path) for t in sp.targets}
        cargo_targets = {
            (tuple(sorted(t["kind"])), t["name"], t["src_path"]) for t in cp["targets"]
        }
        if static_targets != cargo_targets:
            diffs.append(
                f"{mp}: targets mismatch:\n"
                f"  only_in_static={sorted(static_targets - cargo_targets)}\n"
                f"  only_in_cargo ={sorted(cargo_targets - static_targets)}"
            )

        static_pdeps = {
            (d.name, d.rename, d.kind, d.target, d.path) for d in sp.path_deps
        }
        cargo_pdeps = {
            (d["name"], d.get("rename"), d.get("kind"), d.get("target"), d["path"])
            for d in cp["dependencies"]
            if d.get("path") is not None
        }
        if static_pdeps != cargo_pdeps:
            diffs.append(
                f"{mp}: path_deps mismatch:\n"
                f"  only_in_static={sorted(static_pdeps - cargo_pdeps)}\n"
                f"  only_in_cargo ={sorted(cargo_pdeps - static_pdeps)}"
            )

    return diffs


# ---------------------------------------------------------------------------
# Suite A: `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0`
# ---------------------------------------------------------------------------


def run_zerocopy_suite(repo_dir: Path, rev: str) -> dict[str, Any]:
    status_before = subprocess.run(
        ["git", "-C", str(repo_dir), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout

    results: dict[str, Any] = {
        "repository": "google/zerocopy",
        "revision": rev,
        "workspaces": {},
    }

    with tempfile.TemporaryDirectory(prefix="track4_zerocopy_") as td:
        td_path = Path(td)
        export_dir = td_path / "repo"
        export_dir.mkdir()
        cargo_home = td_path / "cargo_home"
        cargo_home.mkdir()

        # Extract exact pinned commit read-only via `git archive`
        tar_proc = subprocess.run(
            ["git", "-C", str(repo_dir), "archive", "--format=tar", rev],
            capture_output=True,
            check=True,
        )
        with tempfile.TemporaryFile() as tf:
            tf.write(tar_proc.stdout)
            tf.seek(0)
            with tarfile.open(fileobj=tf, mode="r:") as tar:
                tar.extractall(path=export_dir, filter="data")

        for ws_rel in ("zerocopy", "anneal", "exocrate", "tools"):
            ws_dir = export_dir / ws_rel
            manifest = ws_dir / "Cargo.toml"
            analyzer = StaticCargoAnalyzer(search_stop_at=export_dir, cargo_home=cargo_home)
            static = analyzer.discover_workspace(manifest, cwd=ws_dir)
            rc, meta, stderr = run_cargo_metadata(manifest, cwd=ws_dir, cargo_home=cargo_home)
            assert rc == 0 and meta is not None, f"cargo metadata failed for {ws_rel}: {stderr}"
            diffs = diff_static_vs_cargo(static, meta)
            results["workspaces"][ws_rel] = {
                "match": len(diffs) == 0,
                "diffs": diffs,
                "is_virtual": static.is_virtual,
                "member_count": len(static.members),
                "members": [
                    {
                        "name": sp.name,
                        "edition": sp.edition,
                        "manifest_rel": os.path.relpath(sp.manifest_path, export_dir),
                        "readme": sp.readme,
                        "license_file": sp.license_file,
                        "target_count": len(sp.targets),
                        "targets_by_kind": _summarize_targets(sp.targets),
                        "path_dep_count": len(sp.path_deps),
                        "path_deps": [
                            {
                                "name": d.name,
                                "rename": d.rename,
                                "kind": d.kind,
                                "target": d.target,
                                "path_rel": os.path.relpath(d.path, export_dir),
                            }
                            for d in sp.path_deps
                        ],
                        "package_exclude": sp.exclude,
                        "package_include": sp.include,
                    }
                    for sp in static.members.values()
                ],
                "default_members_rel": [
                    os.path.relpath(m, export_dir) for m in static.default_members
                ],
                "lockfile_rel": os.path.relpath(static.lockfile_path, export_dir),
                "lockfile_exists": static.lockfile_exists,
                "config_files": [
                    {
                        "path_rel": os.path.relpath(c.path, export_dir),
                        "vendored_dirs_rel": [
                            os.path.relpath(v, export_dir) for v in c.vendored_dirs
                        ],
                        "exec_or_network_keys": c.exec_or_network_keys,
                    }
                    for c in static.config_files
                ],
            }

    status_after = subprocess.run(
        ["git", "-C", str(repo_dir), "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    results["repo_status_unchanged"] = status_before == status_after
    return results


def _summarize_targets(targets: list[StaticTarget]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for t in targets:
        k = ",".join(t.kinds)
        counts[k] = counts.get(k, 0) + 1
    return dict(sorted(counts.items()))


# ---------------------------------------------------------------------------
# Suite B: Synthetic edge-case differential suite + `cargo fetch` exec probe
# ---------------------------------------------------------------------------


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _mk_lib(pkg_dir: Path, name: str, extra_toml: str = "", edition: str = "2021") -> None:
    _write(
        pkg_dir / "Cargo.toml",
        f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "{edition}"\n{extra_toml}',
    )
    _write(pkg_dir / "src/lib.rs", "pub fn f() {}\n")


def run_synthetic_suite() -> dict[str, Any]:
    cases: dict[str, Any] = {}

    def run_diff_case(name: str, builder, manifest_rel: str = "Cargo.toml", expect_error: bool = False):
        with tempfile.TemporaryDirectory(prefix=f"track4_syn_{name}_") as td:
            root = Path(td) / "ws"
            root.mkdir()
            cargo_home = Path(td) / "cargo_home"
            cargo_home.mkdir()
            builder(Path(td), root)
            manifest = root / manifest_rel
            rc, meta, stderr = run_cargo_metadata(manifest, cwd=manifest.parent, cargo_home=cargo_home)
            analyzer = StaticCargoAnalyzer(search_stop_at=Path(td), cargo_home=cargo_home)
            if expect_error:
                static_err = None
                try:
                    analyzer.discover_workspace(manifest, cwd=manifest.parent)
                except Exception as e:
                    static_err = str(e)
                cases[name] = {
                    "expect_error": True,
                    "cargo_rc": rc,
                    "cargo_stderr_head": stderr.splitlines()[:3],
                    "static_error": static_err,
                    "match": (rc != 0) and (static_err is not None),
                }
            else:
                if rc != 0 or meta is None:
                    cases[name] = {"match": False, "cargo_rc": rc, "cargo_stderr": stderr}
                    return
                static = analyzer.discover_workspace(manifest, cwd=manifest.parent)
                diffs = diff_static_vs_cargo(static, meta)
                cases[name] = {
                    "match": len(diffs) == 0,
                    "diffs": diffs,
                    "member_names": sorted(sp.name for sp in static.members.values()),
                    "default_member_names": sorted(
                        static.members[m].name for m in static.default_members
                    ),
                    "external_path_dep_names": sorted(
                        sp.name for sp in static.external_path_deps.values()
                    ),
                    "patch_path_count": len(static.patch_path_deps),
                    "replace_path_count": len(static.replace_path_deps),
                    "lockfile_rel": os.path.relpath(static.lockfile_path, Path(td)),
                }

    # 1. Empty [workspace] + transitive implicit path deps (incl. cfg(any()))
    def c1(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\n[package]\nname = "root"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dependencies]\na = { path = "a" }\n'
            "[target.'cfg(any())'.dependencies]\nb = { path = \"b\" }\n",
        )
        _write(root / "src/lib.rs", "")
        _mk_lib(root / "a", "a", '[dev-dependencies]\nc = { path = "../c" }\n')
        _mk_lib(root / "b", "b")
        _mk_lib(root / "c", "c")

    run_diff_case("1_empty_ws_implicit_transitive_path_deps", c1)

    # 2. External path dep outside workspace root (NOT a member, IS in external closure)
    def c2(td: Path, root: Path) -> None:
        _mk_lib(td / "ext_crate", "ext_crate")
        _write(
            root / "Cargo.toml",
            '[workspace]\n[package]\nname = "root"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dependencies]\next_crate = { path = "../ext_crate" }\n',
        )
        _write(root / "src/lib.rs", "")

    run_diff_case("2_external_path_dep_outside_ws_root", c2)

    # 3. External path dep outside ws root WITH `package.workspace = "../ws"` -> IS a member!
    def c3(td: Path, root: Path) -> None:
        _mk_lib(td / "ext_member", "ext_member", 'workspace = "../ws"\n')
        _write(
            root / "Cargo.toml",
            '[workspace]\n[package]\nname = "root"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dependencies]\next_member = { path = "../ext_member" }\n',
        )
        _write(root / "src/lib.rs", "")

    run_diff_case("3_external_path_dep_with_package_workspace_pointer", c3)

    # 4a. workspace.exclude wins over glob member (and skips dir without Cargo.toml!)
    def c4a(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/*"]\nexclude = ["crates/skip_me", "crates/not_a_crate"]\n',
        )
        _mk_lib(root / "crates/keep_me", "keep_me")
        _mk_lib(root / "crates/skip_me", "skip_me")
        (root / "crates/not_a_crate").mkdir(parents=True)
        _write(root / "crates/README.md", "plain file filtered by is_dir()\n")

    run_diff_case("4a_exclude_wins_over_glob_and_skips_noncrate_dir", c4a)

    # 4b. Literal member overrides parent `workspace.exclude`!
    def c4b(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/keep_me"]\nexclude = ["crates"]\n',
        )
        _mk_lib(root / "crates/keep_me", "keep_me")
        _mk_lib(root / "crates/other", "other")

    run_diff_case("4b_literal_member_overrides_parent_exclude", c4b)

    # 4c. Globs in `workspace.exclude` do NOT expand (Path::starts_with literal)!
    def c4c(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/*"]\nexclude = ["crates/*"]\n',
        )
        _mk_lib(root / "crates/still_included", "still_included")

    run_diff_case("4c_glob_in_exclude_does_not_expand", c4c)

    # 5a. Hidden directory matched by `members = ["crates/*"]` & `**` recursive glob
    def c5a(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/*", "deep/**"]\nexclude = ["deep/sub"]\n',
        )
        _mk_lib(root / "crates/.hidden_crate", "hidden_crate")
        _mk_lib(root / "deep/sub/leaf", "leaf")

    # Wait: if deep/sub is excluded, deep/sub/leaf starts with deep/sub! Let's test deep/a/leaf without excluding it.
    def c5a_clean(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/*", "deep/**/pkg"]\n',
        )
        _mk_lib(root / "crates/.hidden_crate", "hidden_crate")
        _mk_lib(root / "deep/x/y/pkg", "deep_pkg")

    run_diff_case("5a_glob_matches_hidden_dir_and_doublestar", c5a_clean)

    # 5b. Unexcluded directory without Cargo.toml matched by glob -> HARD ERROR
    def c5b(_td: Path, root: Path) -> None:
        _write(root / "Cargo.toml", '[workspace]\nmembers = ["crates/*"]\n')
        _mk_lib(root / "crates/good", "good")
        (root / "crates/empty_dir").mkdir(parents=True)

    run_diff_case("5b_glob_matching_dir_without_manifest_errors", c5b, expect_error=True)

    # 6a. Path dep on nested [workspace] WITHOUT exclude -> ERROR (multiple workspace roots)
    def c6a(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\n[package]\nname = "root"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dependencies]\nnested = { path = "nested" }\n',
        )
        _write(root / "src/lib.rs", "")
        _write(
            root / "nested/Cargo.toml",
            '[workspace]\n[package]\nname = "nested"\nversion = "0.1.0"\nedition = "2021"\n',
        )
        _write(root / "nested/src/lib.rs", "")

    run_diff_case("6a_nested_workspace_path_dep_without_exclude_errors", c6a, expect_error=True)

    # 6b. Path dep on nested [workspace] WITH exclude -> succeeds, external path dep
    def c6b(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nexclude = ["nested"]\n[package]\nname = "root"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dependencies]\nnested = { path = "nested" }\n',
        )
        _write(root / "src/lib.rs", "")
        _write(
            root / "nested/Cargo.toml",
            '[workspace]\n[package]\nname = "nested"\nversion = "0.1.0"\nedition = "2021"\n',
        )
        _write(root / "nested/src/lib.rs", "")

    run_diff_case("6b_nested_workspace_path_dep_with_exclude_ok", c6b)

    # 7. workspace.dependencies relative path inheritance + uninherited workspace path dep
    def c7(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/app"]\n'
            '[workspace.dependencies]\n'
            'shared = { path = "libs/shared" }\n'
            'unused_local = { path = "libs/unused" }\n',
        )
        _mk_lib(root / "crates/app", "app", "[dependencies]\nshared = { workspace = true }\n")
        _mk_lib(root / "libs/shared", "shared")
        _mk_lib(root / "libs/unused", "unused_local")

    run_diff_case("7_workspace_deps_relative_path_and_uninherited", c7)

    # 8a. [patch.crates-io] path dep (not member, in closure)
    def c8a(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["app"]\n'
            '[patch.crates-io]\npatched = { path = "patches/patched" }\n',
        )
        _mk_lib(root / "app", "app")
        _mk_lib(root / "patches/patched", "patched")

    run_diff_case("8a_patch_crates_io_path_dep", c8a)

    # 8b. [replace] path dep (deprecated, still parsed)
    def c8b(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["app"]\n'
            '[replace]\n"repl:0.1.0" = { path = "repls/repl" }\n',
        )
        _mk_lib(root / "app", "app")
        _mk_lib(root / "repls/repl", "repl")

    run_diff_case("8b_replace_path_dep", c8b)

    # 9. Edition 2015 vs 2024 autotests & explicit [[test]] interaction
    def c9(_td: Path, root: Path) -> None:
        _write(root / "Cargo.toml", '[workspace]\nmembers = ["e2015_auto", "e2015_expl", "e2024_expl", "e2024_off"]\n')
        # e2015 without [[test]]: auto-discovers both
        _mk_lib(root / "e2015_auto", "e2015_auto", edition="2015")
        _write(root / "e2015_auto/tests/t1.rs", "")
        _write(root / "e2015_auto/tests/t2/main.rs", "")
        # e2015 WITH explicit [[test]]: disables auto-discovery of t2!
        _mk_lib(root / "e2015_expl", "e2015_expl", '[[test]]\nname = "t1"\n', edition="2015")
        _write(root / "e2015_expl/tests/t1.rs", "")
        _write(root / "e2015_expl/tests/t2/main.rs", "")
        # e2024 WITH explicit [[test]]: STILL auto-discovers t2!
        _mk_lib(root / "e2024_expl", "e2024_expl", '[[test]]\nname = "t1"\n', edition="2024")
        _write(root / "e2024_expl/tests/t1.rs", "")
        _write(root / "e2024_expl/tests/t2/main.rs", "")
        # e2024 with autotests = false + explicit [[test]] omitting path: infers t1, skips t2!
        _mk_lib(root / "e2024_off", "e2024_off", 'autotests = false\n[[test]]\nname = "t1"\n', edition="2024")
        _write(root / "e2024_off/tests/t1.rs", "")
        _write(root / "e2024_off/tests/t2/main.rs", "")

    run_diff_case("9_edition_2015_vs_2024_autotests", c9)

    # 10. autolib = false vs explicit [lib] without path/name
    def c10(_td: Path, root: Path) -> None:
        _write(root / "Cargo.toml", '[workspace]\nmembers = ["no_lib", "expl_lib"]\n')
        _write(
            root / "no_lib/Cargo.toml",
            '[package]\nname = "no-lib"\nversion = "0.1.0"\nedition = "2021"\nautolib = false\n',
        )
        _write(root / "no_lib/src/lib.rs", "")
        _write(root / "no_lib/src/main.rs", "fn main() {}\n")

        _write(
            root / "expl_lib/Cargo.toml",
            '[package]\nname = "expl-lib"\nversion = "0.1.0"\nedition = "2021"\nautolib = false\n'
            "[lib]\nproc-macro = true\n",
        )
        _write(root / "expl_lib/src/lib.rs", "")

    run_diff_case("10_autolib_false_and_inferred_lib", c10)

    # 11. autobins = false + explicit [[bin]] omitting path (src/main.rs & src/bin/tool/main.rs)
    def c11(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[package]\nname = "my-cli"\nversion = "0.1.0"\nedition = "2024"\nautobins = false\n'
            '[[bin]]\nname = "my-cli"\n'
            '[[bin]]\nname = "tool"\n',
        )
        _write(root / "src/main.rs", "fn main() {}\n")
        _write(root / "src/bin/tool/main.rs", "fn main() {}\n")
        _write(root / "src/bin/ignored_bin.rs", "fn main() {}\n")

    run_diff_case("11_autobins_false_explicit_bin_inferred_path", c11)

    # 12. Depth limit, dotfiles, non-.rs, symlink file vs symlink dir in tests/
    def c12(td: Path, root: Path) -> None:
        _mk_lib(root, "sym_test")
        _write(root / "tests/good_file.rs", "")
        _write(root / "tests/good_sub/main.rs", "")
        _write(root / "tests/too_deep/nested/main.rs", "")
        _write(root / "tests/helper_mod/mod.rs", "")
        _write(root / "tests/.dotfile.rs", "")
        _write(root / "tests/.dotdir/main.rs", "")
        _write(root / "tests/not_rust.txt", "")
        # External symlink targets
        ext_file = td / "target_test.rs"
        _write(ext_file, "")
        os.symlink(ext_file, root / "tests/sym_file.rs")
        ext_dir = td / "target_dir"
        _write(ext_dir / "main.rs", "")
        os.symlink(ext_dir, root / "tests/sym_dir")
        # Symlinked main.rs inside a real subdir -> IS followed by main.exists()!
        (root / "tests/real_sub_sym_main").mkdir(parents=True)
        os.symlink(ext_file, root / "tests/real_sub_sym_main/main.rs")

    run_diff_case("12_target_depth_dotfiles_and_symlinks", c12)

    # 13. package.build modes (omitted+file, omitted+dir, false, true-missing, custom)
    def c13(_td: Path, root: Path) -> None:
        _write(root / "Cargo.toml", '[workspace]\nmembers = ["b_auto", "b_dir", "b_false", "b_true", "b_custom"]\n')
        _mk_lib(root / "b_auto", "b_auto")
        _write(root / "b_auto/build.rs", "fn main() {}\n")
        _mk_lib(root / "b_dir", "b_dir")
        (root / "b_dir/build.rs").mkdir()
        _mk_lib(root / "b_false", "b_false", "build = false\n")
        _write(root / "b_false/build.rs", "fn main() {}\n")
        _mk_lib(root / "b_true", "b_true", "build = true\n")
        _mk_lib(root / "b_custom", "b_custom", 'build = "scripts/gen.rs"\n')
        _write(root / "b_custom/scripts/gen.rs", "fn main() {}\n")

    run_diff_case("13_package_build_modes", c13)

    # 14. readme & license-file auto-detection & workspace inheritance
    def c14(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["p_auto_txt", "p_true", "p_false", "p_inh"]\n'
            '[workspace.package]\nlicense-file = "LICENSES/CUSTOM"\n',
        )
        _write(root / "README.txt", "ws readme\n")
        _write(root / "LICENSES/CUSTOM", "license\n")
        _mk_lib(root / "p_auto_txt", "p_auto_txt")
        _write(root / "p_auto_txt/README.txt", "txt\n")
        _write(root / "p_auto_txt/README", "plain\n")
        _mk_lib(root / "p_true", "p_true", "readme = true\n")
        _write(root / "p_true/README.txt", "ignored because readme=true forces README.md\n")
        _mk_lib(root / "p_false", "p_false", "readme = false\n")
        _write(root / "p_false/README.md", "suppressed\n")
        _mk_lib(
            root / "p_inh",
            "p_inh",
            "readme.workspace = true\nlicense-file.workspace = true\n",
        )

    run_diff_case("14_readme_and_license_file_inheritance", c14)

    # 15. Deprecated [project] & underscore dependency tables (Edition 2021)
    def c15(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["legacy"]\n',
        )
        _write(
            root / "legacy/Cargo.toml",
            '[project]\nname = "legacy"\nversion = "0.1.0"\nedition = "2021"\n'
            '[dev_dependencies]\nd1 = { path = "../d1" }\n'
            '[build_dependencies]\nd2 = { path = "../d2" }\n'
            "[target.'cfg(unix)'.dev_dependencies]\nd3 = { path = \"../d3\" }\n",
        )
        _write(root / "legacy/src/lib.rs", "")
        _mk_lib(root / "d1", "d1")
        _mk_lib(root / "d2", "d2")
        _mk_lib(root / "d3", "d3")

    run_diff_case("15_deprecated_project_and_underscore_dep_tables", c15)

    # 16. default-members with excluded member
    def c16(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[workspace]\nmembers = ["crates/*"]\nexclude = ["crates/b"]\n'
            'default-members = ["crates/*"]\n',
        )
        _mk_lib(root / "crates/a", "a")
        _mk_lib(root / "crates/b", "b")

    run_diff_case("16_default_members_with_excluded_member", c16)

    # 17. Config discovery precedence (.cargo/config > .cargo/config.toml),
    # `include`, upward walk from cwd, and LIVE OFFLINE `cargo fetch` code-execution probe!
    with tempfile.TemporaryDirectory(prefix="track4_syn_17_config_") as td:
        td_path = Path(td)
        cargo_home = td_path / "cargo_home"
        cargo_home.mkdir()
        parent = td_path / "repo"
        ws = parent / "subws"
        _mk_lib(ws, "cfg_probe")
        _write(
            ws / "Cargo.lock",
            '# This file is automatically @generated by Cargo.\nversion = 4\n\n'
            '[[package]]\nname = "cfg_probe"\nversion = "0.1.0"\n',
        )

        # Parent has `.cargo/config.toml` with `include = ["extra.toml"]`
        _write(parent / ".cargo/config.toml", 'include = ["extra.toml"]\n[env]\nFROM_PARENT = "1"\n')
        _write(parent / ".cargo/extra.toml", '[env]\nFROM_INCLUDE = "1"\n')

        # Workspace has BOTH `.cargo/config` (legacy, wins!) and `.cargo/config.toml`
        canary_out = td_path / "wrapper_executed.txt"
        wrapper_script = td_path / "evil_wrapper.sh"
        _write(
            wrapper_script,
            f'#!/bin/sh\necho "EXECUTED:$*" >> "{canary_out}"\nexec "$@"\n',
        )
        os.chmod(wrapper_script, 0o755)
        _write(
            ws / ".cargo/config",
            f'[build]\nrustc-wrapper = "{wrapper_script}"\n',
        )
        _write(
            ws / ".cargo/config.toml",
            '[build]\nrustc-wrapper = "/nonexistent/should_be_shadowed"\n',
        )

        analyzer = StaticCargoAnalyzer(search_stop_at=td_path, cargo_home=cargo_home)
        static = analyzer.discover_workspace(ws / "Cargo.toml", cwd=ws)

        # Probe 17a: `cargo fetch --offline --locked` from `ws` (where `.cargo/config` is discovered)
        env = os.environ.copy()
        env["CARGO_HOME"] = str(cargo_home)
        p_exec = subprocess.run(
            ["cargo", "fetch", "--offline", "--locked"],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        exec_happened = canary_out.exists()
        exec_lines = canary_out.read_text().splitlines() if exec_happened else []

        # Probe 17b: Does `--config 'build.rustc-wrapper=""'` neutralize it?
        if canary_out.exists():
            canary_out.unlink()
        p_neutral = subprocess.run(
            ["cargo", "fetch", "--offline", "--locked", "--config", 'build.rustc-wrapper=""'],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        exec_after_cli_override = canary_out.exists()

        # Probe 17c: Does running from `parent` with `--manifest-path subws/Cargo.toml` skip `subws/.cargo/config`?
        if canary_out.exists():
            canary_out.unlink()
        p_from_parent = subprocess.run(
            [
                "cargo",
                "fetch",
                "--offline",
                "--locked",
                "--manifest-path",
                str(ws / "Cargo.toml"),
            ],
            cwd=str(parent),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        exec_from_parent = canary_out.exists()

        cases["17_config_precedence_include_and_cargo_fetch_exec"] = {
            "match": True,
            "discovered_configs_rel": [
                {
                    "path_rel": os.path.relpath(c.path, td_path),
                    "rank": c.precedence_rank,
                    "included_from_rel": (
                        os.path.relpath(c.included_from, td_path) if c.included_from else None
                    ),
                    "exec_or_network_keys": c.exec_or_network_keys,
                }
                for c in static.config_files
            ],
            "legacy_config_shadowed_config_toml": (
                all(not c.path.endswith("subws/.cargo/config.toml") for c in static.config_files)
                and any(c.path.endswith("subws/.cargo/config") for c in static.config_files)
            ),
            "cargo_fetch_rc": p_exec.returncode,
            "cargo_fetch_executed_rustc_wrapper": exec_happened,
            "cargo_fetch_wrapper_invocations": exec_lines[:5],
            "cargo_fetch_cli_override_rc": p_neutral.returncode,
            "cargo_fetch_executed_after_cli_empty_override": exec_after_cli_override,
            "cargo_fetch_from_parent_rc": p_from_parent.returncode,
            "cargo_fetch_from_parent_skipped_subdir_config": not exec_from_parent,
        }

    # 18. `[env] LD_PRELOAD` + `[build] rustc` + `[build] rustc-workspace-wrapper`
    # during `cargo fetch --offline --locked`, plus isolated-cwd `--manifest-path` bypass!
    with tempfile.TemporaryDirectory(prefix="track4_syn_18_fetch_env_") as td:
        td_path = Path(td)
        cargo_home = td_path / "cargo_home"
        cargo_home.mkdir()
        repo = td_path / "repo"
        ws = repo / "ws"
        _mk_lib(ws, "env_probe")
        _write(
            ws / "Cargo.lock",
            '# This file is automatically @generated by Cargo.\nversion = 4\n\n'
            '[[package]]\nname = "env_probe"\nversion = "0.1.0"\n',
        )
        iso_cwd = td_path / "isolated_cwd"
        iso_cwd.mkdir()

        env = os.environ.copy()
        env["CARGO_HOME"] = str(cargo_home)

        # 18a: `[env] LD_PRELOAD` reaches `rustc` even with NO wrapper!
        _write(
            repo / ".cargo/config.toml",
            '[env]\nLD_PRELOAD = "/nonexistent_canary_preload.so"\n'
            '[build]\nrustflags = ["--invalid-canary-flag-xyz"]\n',
        )
        p_ld = subprocess.run(
            ["cargo", "fetch", "--offline", "--locked"],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )
        ld_preload_reached_rustc = "nonexistent_canary_preload.so" in p_ld.stderr

        # 18b: Same workspace invoked from `isolated_cwd` via `--manifest-path` bypasses
        # ALL repo `.cargo/config(.toml)` files cleanly!
        p_iso = subprocess.run(
            [
                "cargo",
                "fetch",
                "--offline",
                "--locked",
                "--manifest-path",
                str(ws / "Cargo.toml"),
            ],
            cwd=str(iso_cwd),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

        # 18c: `[build] rustc` directly executes arbitrary binary during `cargo fetch`
        rustc_canary = td_path / "fake_rustc_ran.txt"
        fake_rustc = td_path / "fake_rustc.sh"
        _write(fake_rustc, f'#!/bin/sh\necho "FAKE_RUSTC:$*" >> "{rustc_canary}"\nexec rustc "$@"\n')
        os.chmod(fake_rustc, 0o755)
        _write(repo / ".cargo/config.toml", f'[build]\nrustc = "{fake_rustc}"\n')
        p_rustc = subprocess.run(
            ["cargo", "fetch", "--offline", "--locked"],
            cwd=str(ws),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

        cases["18_cargo_fetch_ld_preload_and_isolated_cwd_mitigation"] = {
            "match": (
                ld_preload_reached_rustc
                and p_iso.returncode == 0
                and ("nonexistent_canary_preload.so" not in p_iso.stderr)
                and rustc_canary.exists()
            ),
            "ld_preload_reached_rustc": ld_preload_reached_rustc,
            "ld_preload_stderr_lines": [
                ln for ln in p_ld.stderr.splitlines() if "LD_PRELOAD" in ln or "invalid-canary" in ln
            ],
            "isolated_cwd_fetch_rc": p_iso.returncode,
            "isolated_cwd_bypassed_repo_config": (
                p_iso.returncode == 0 and "nonexistent_canary_preload.so" not in p_iso.stderr
            ),
            "build_rustc_executed_during_fetch": rustc_canary.exists(),
            "build_rustc_invocations": rustc_canary.read_text().splitlines() if rustc_canary.exists() else [],
        }

    # 19. Literal nonexistent member in `workspace.members` -> HARD ERROR
    def c19(_td: Path, root: Path) -> None:
        _write(root / "Cargo.toml", '[workspace]\nmembers = ["does_not_exist"]\n')

    run_diff_case("19_literal_missing_member_errors", c19, expect_error=True)

    # 20. Omitted `package.edition` defaults to Edition 2015 (explicit [[test]] suppresses autotests)
    def c20(_td: Path, root: Path) -> None:
        _write(
            root / "Cargo.toml",
            '[package]\nname = "no_ed"\nversion = "0.1.0"\n[[test]]\nname = "t1"\n',
        )
        _write(root / "src/lib.rs", "")
        _write(root / "tests/t1.rs", "")
        _write(root / "tests/t2.rs", "")

    run_diff_case("20_omitted_edition_defaults_to_2015", c20)

    return cases


def main(argv: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(
        description="Static Cargo workspace/target discovery differential probe against cargo metadata."
    )
    parser.add_argument(
        "--repo-path",
        type=Path,
        default=None,
        help="Optional local clone of google/zerocopy to run Suite A (via read-only git archive).",
    )
    parser.add_argument(
        "--rev",
        default="907b9175fee081872ec883ca4709e6ad922f8ed0",
        help="Git revision to archive from --repo-path (default: 907b9175fee081872ec883ca4709e6ad922f8ed0).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional output path for JSON results (omitted unless specified).",
    )
    args = parser.parse_args(argv)

    cargo_ver = subprocess.run(
        ["cargo", "--version"], capture_output=True, text=True, check=True
    ).stdout.strip()

    zc_results = run_zerocopy_suite(args.repo_path, args.rev) if args.repo_path else None
    syn_results = run_synthetic_suite()

    report = {
        "cargo_version": cargo_ver,
        "python_version": sys.version.split()[0],
        "cargo_source_revision": "rust-lang/cargo@930a674da900a73c1dfbe16be62c42e75bdfdfc0",
        "zerocopy_suite": zc_results,
        "synthetic_suite": syn_results,
    }

    if args.out is not None:
        serialized = json.dumps(report, indent=2) + "\n"
        home_str = str(Path.home())
        if home_str:
            serialized = serialized.replace(home_str, "<HOME>")
        args.out.write_text(serialized, encoding="utf-8")

    all_ok = True
    print(f"Cargo version: {cargo_ver}")
    if zc_results is not None:
        print(f"\n=== Suite A: google/zerocopy@{args.rev} ===")
        for ws_name, ws_res in zc_results["workspaces"].items():
            status = "PASS" if ws_res["match"] else "FAIL"
            print(
                f"  [{status}] {ws_name}: {ws_res['member_count']} member(s), "
                f"virtual={ws_res['is_virtual']}, lockfile={ws_res['lockfile_rel']} "
                f"(exists={ws_res['lockfile_exists']}), configs={len(ws_res['config_files'])}"
            )
            if not ws_res["match"]:
                all_ok = False
                for d in ws_res["diffs"]:
                    print(f"      DIFF: {d}")
        print(f"  repo_status_unchanged={zc_results['repo_status_unchanged']}")

    print("\n=== Suite B: Synthetic Edge-Case Differential Suite ===")
    for cname, cres in syn_results.items():
        status = "PASS" if cres.get("match") else "FAIL"
        print(f"  [{status}] {cname}")
        if not cres.get("match"):
            all_ok = False
            print(f"      DETAILS: {json.dumps(cres, indent=2)}")

    c17 = syn_results["17_config_precedence_include_and_cargo_fetch_exec"]
    print("\n=== Probe 17: cargo fetch + .cargo/config execution ===")
    print(f"  legacy_config_shadowed_config_toml: {c17['legacy_config_shadowed_config_toml']}")
    print(f"  cargo_fetch_executed_rustc_wrapper: {c17['cargo_fetch_executed_rustc_wrapper']}")
    print(f"  invocations: {c17['cargo_fetch_wrapper_invocations']}")
    print(f"  executed_after_cli_empty_override: {c17['cargo_fetch_executed_after_cli_empty_override']}")
    print(f"  from_parent_skipped_subdir_config: {c17['cargo_fetch_from_parent_skipped_subdir_config']}")

    if args.out is not None:
        print(f"\nWrote {args.out}")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
