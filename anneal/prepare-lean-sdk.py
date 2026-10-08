#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
"""Publish a thin, relocatable Lean installation from a trusted build.

The catalog command runs immediately after the trusted producer build and
before pruning/candidate staging. Its RC2 family policy comes from source
format, not surviving sidecars. Assembly checks those expectations, then pins
the consumed runtime/native bytes after the publisher's explicit relocation
step. Hashes and headers do not prove arbitrary source-to-binary correspondence
or native ABI compatibility: the pinned inputs and coherent producer build
remain trusted. Consumers rely on continued archive immutability; they do not
walk this publisher catalog on every invocation.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess


TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
COMPILER_HASH = "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
VERSION = "4.30.0-rc2"
PLATFORMS = {"x86_64-linux", "aarch64-linux", "x86_64-darwin", "aarch64-darwin"}
LEGACY = ("olean", "ilean")
# RC2's writeModule/saveModuleData and LeanIR emit these split files. This
# pinned format does not emit a separate .ir.sig companion.
SPLIT = (*LEGACY, "olean.private", "olean.server", "ir")
ELF_SYSTEM = {"libc.so.6", "libm.so.6", "libdl.so.2", "libpthread.so.0", "librt.so.1",
              "libutil.so.1", "libstdc++.so.6", "libgcc_s.so.1", "libgmp.so.10", "libz.so.1",
              "libffi.so.8", "libssl.so.3", "libcrypto.so.3", "libtinfo.so.6", "libncurses.so.6"}
ELF_INTERPRETERS = {"x86_64-linux": "/lib64/ld-linux-x86-64.so.2",
                    "aarch64-linux": "/lib/ld-linux-aarch64.so.1"}


def encoded(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def checked(path: Path, root: Path) -> Path:
    """Every referenced input, including a symlink target, stays in its owner."""
    physical = path.resolve(strict=True)
    if not physical.is_relative_to(root.resolve(strict=True)) or not physical.is_file():
        raise ValueError(f"missing, escaping, or non-file input: {path}")
    return physical


def files(root: Path, owner: Path | None = None):
    """Walk consumed trees including directory links, rejecting cycles/escapes."""
    if not root.is_dir():
        raise ValueError(f"missing input directory: {root}")
    owner = (root if owner is None else owner).resolve(strict=True)

    def visit(path: Path, ancestors: frozenset[Path]):
        physical = path.resolve(strict=True)
        if not physical.is_relative_to(owner):
            raise ValueError(f"escaping input: {path}")
        if physical.is_dir():
            if physical in ancestors:
                raise ValueError(f"cyclic input: {path}")
            for child in sorted(path.iterdir()):
                yield from visit(child, ancestors | {physical})
        elif physical.is_file():
            yield path
        else:
            raise ValueError(f"non-file input: {path}")

    yield from visit(root, frozenset())


def is_split(source: Path) -> bool:
    """Recognize RC2's leading module directive, handling nested comments.

    This profile supports the producer's ordinary legacy/module source modes.
    A producer using an independent experimental.module override needs its own
    reviewed profile; the supported cached sources and Aeneas build do not.
    """
    text = source.read_text(encoding="utf-8-sig")
    pos = 0
    while True:
        while pos < len(text) and text[pos].isspace():
            pos += 1
        if text.startswith("--", pos):
            newline = text.find("\n", pos)
            pos = len(text) if newline < 0 else newline + 1
        elif text.startswith("/-", pos):
            depth = 1
            pos += 2
            while depth and pos < len(text):
                if text.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif text.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            if depth:
                raise ValueError(f"unterminated source comment: {source}")
        else:
            token = text[pos:pos + 6]
            return token == "module" and (pos + 6 == len(text) or not (text[pos + 6].isalnum() or text[pos + 6] in "_'"))


def check_olean(path: Path):
    # RC2's version/Git fields are 33/40 bytes. Pin this format instead of
    # silently extrapolating it to another compiler tuple.
    expected = b"olean\x02\x01" + VERSION.encode().ljust(33, b"\0") + COMPILER_HASH.encode()
    with path.open("rb") as stream:
        header = stream.read(len(expected))
    if header != expected:
        raise ValueError(f"incompatible RC2 compiled artifact: {path}")


def check_native(path: Path, platform: str):
    """Architecture/format check, not a general native ABI proof."""
    with path.open("rb") as stream:
        header = stream.read(32)
    if platform.endswith("-linux"):
        machine = 183 if platform.startswith("aarch64-") else 62
        if len(header) < 20 or header[:6] != b"\x7fELF\x02\x01" or struct.unpack_from("<H", header, 18)[0] != machine:
            raise ValueError(f"incompatible native ELF input: {path}")
    else:
        cpu = 0x0100000C if platform.startswith("aarch64-") else 0x01000007
        if len(header) < 8 or header[:4] != b"\xcf\xfa\xed\xfe" or struct.unpack_from("<I", header, 4)[0] != cpu:
            raise ValueError(f"incompatible native Mach-O input: {path}")


def _profile(platform: str):
    if platform not in PLATFORMS:
        raise ValueError(f"unsupported RC2 platform profile: {platform}")


def parse_native(text: str, platform: str) -> dict:
    """Parse publisher-only otool -l/readelf -dW/-lW inspection output."""
    result = {"needed": [], "rpaths": [], "identity": None, "interpreter": None}
    if platform.endswith("-darwin"):
        command = None
        for line in text.splitlines():
            stripped = line.strip()
            if stripped.startswith("cmd "):
                command = stripped.split()[1]
            elif command == "LC_RPATH" and stripped.startswith("path "):
                result["rpaths"].append(stripped[5:].rsplit(" (offset ", 1)[0])
            elif stripped.startswith("name "):
                name = stripped[5:].rsplit(" (offset ", 1)[0]
                if command == "LC_ID_DYLIB":
                    result["identity"] = name
                elif command == "LC_LOAD_DYLINKER":
                    result["interpreter"] = name
                elif command in {"LC_LOAD_DYLIB", "LC_LOAD_WEAK_DYLIB", "LC_REEXPORT_DYLIB", "LC_LOAD_UPWARD_DYLIB"}:
                    result["needed"].append(name)
    else:
        for line in text.splitlines():
            for tag, key in (("NEEDED", "needed"), ("RPATH", "rpaths"), ("RUNPATH", "rpaths"), ("SONAME", "identity")):
                if "(" + tag + ")" in line:
                    match = re.search(r"\[([^\]]*)\]", line)
                    if not match:
                        raise ValueError("malformed ELF dynamic inspection")
                    value = match.group(1)
                    if key == "identity":
                        result[key] = value
                    elif key == "rpaths":
                        result[key].extend(value.split(":"))
                    else:
                        result[key].append(value)
            match = re.search(r"Requesting program interpreter: ([^\]]+)\]", line)
            if match:
                result["interpreter"] = match.group(1)
    return result


def _tool(arguments: list[str]) -> str:
    # These are static publisher inspectors/relocators, never Lean/Lake.
    process = subprocess.run(arguments, check=True, capture_output=True, text=True)
    return process.stdout


def native_dependencies(path: Path, platform: str) -> dict:
    if platform.endswith("-darwin"):
        return parse_native(_tool(["otool", "-l", str(path)]), platform)
    return parse_native(_tool(["readelf", "-dW", str(path)]) + "\n" + _tool(["readelf", "-lW", str(path)]), platform)


def _system_absolute(path: str, platform: str) -> bool:
    if ".." in Path(path).parts:
        return False
    if platform.endswith("-darwin"):
        return path.startswith(("/usr/lib/", "/System/Library/Frameworks/"))
    if path == ELF_INTERPRETERS[platform]:
        return True
    return path.startswith(("/lib/", "/lib64/", "/usr/lib/", "/usr/lib64/")) and Path(path).name in ELF_SYSTEM


def loader_closure(root: Path, plugin: Path, platform: str, *, relocate=False, hashes=None,
                   extra_images: tuple[Path, ...] = ()) -> dict:
    """Resolve every reachable native image against exact archive providers.

    System libraries are explicit platform assumptions, not silently resolved
    through Nix/store or arbitrary host search paths. The installed SDK mirrors
    the runtime's lib layout; copied launcher @executable_path/$ORIGIN paths
    therefore refer to the same coherent payload through its relative links.
    """
    runtime = root / "lean"
    search = [runtime / "lib", runtime / "lib/lean", plugin.parent]
    allowed = [runtime, plugin.parent]
    executable = runtime / "bin"
    pending = [executable / "lean", executable / "lake", plugin, *extra_images]
    visited = {}
    system = set()

    def owned(path):
        physical = path.resolve(strict=True)
        if not physical.is_file() or not any(physical.is_relative_to(owner.resolve()) for owner in allowed):
            raise ValueError(f"native dependency outside archive providers: {path}")
        return physical

    # Validate all roots before any relocation. Never partially modify a plugin
    # before discovering that its purported staging runtime is missing.
    for path in pending:
        owned(path)
    if relocate and (root / "lean-sdk").exists():
        raise ValueError("native relocation cannot alter an assembled SDK")

    def expand(value, image):
        value = value.replace("${ORIGIN}", str(image.parent)).replace("$ORIGIN", str(image.parent))
        value = value.replace("@loader_path", str(image.parent)).replace("@executable_path", str(executable))
        if not value or "$" in value or "@" in value or not Path(value).is_absolute():
            raise ValueError(f"unsupported native loader search path: {value}")
        path = Path(value).resolve(strict=True)
        if not path.is_dir() or not any(path.is_relative_to(owner.resolve()) for owner in allowed):
            raise ValueError(f"native loader search path outside archive: {value}")
        return path

    def resolve(reference, image, rpaths):
        if reference.startswith("/"):
            if _system_absolute(reference, platform):
                system.add(reference)
                return None
            raise ValueError(f"non-system absolute native reference: {reference}")
        if reference.startswith("@loader_path/") or reference.startswith("@executable_path/") or reference.startswith(("$ORIGIN/", "${ORIGIN}/")):
            parent, name = reference.rsplit("/", 1)
            return owned(expand(parent, image) / name)
        if reference.startswith("@rpath/"):
            name = reference[len("@rpath/"):]
        elif "/" not in reference and "$" not in reference and "@" not in reference:
            name = reference
        else:
            raise ValueError(f"unsupported native dependency: {reference}")
        found = {owned(directory / name) for directory in [*rpaths, *search] if (directory / name).exists()}
        if len(found) > 1:
            raise ValueError(f"ambiguous native dependency provider: {reference}")
        if found:
            return found.pop()
        # glibc can name the platform loader in DT_NEEDED as well as PT_INTERP.
        # Admit exactly this profile's loader, not the other architecture's.
        if platform.endswith("-linux") and (name in ELF_SYSTEM or name == Path(ELF_INTERPRETERS[platform]).name):
            system.add(name)
            return None
        raise ValueError(f"missing native dependency: {reference}")

    while pending:
        image = owned(pending.pop())
        relative = str(image.relative_to(root))
        if relative in visited:
            continue
        check_native(image, platform)
        information = native_dependencies(image, platform)
        if relocate:
            if not platform.endswith("-darwin"):
                raise ValueError("Mach-O relocator requires Darwin profile")
            identity = information["identity"]
            changed = False
            if identity and identity.startswith("/") and not _system_absolute(identity, platform):
                _tool(["install_name_tool", "-id", "@rpath/" + image.name, str(image)])
                changed = True
            for reference in information["needed"]:
                if reference.startswith("/") and not _system_absolute(reference, platform):
                    basename = Path(reference).name
                    resolve("@rpath/" + basename, image, [])  # Exact provider, never fabricate one.
                    _tool(["install_name_tool", "-change", reference, "@rpath/" + basename, str(image)])
                    changed = True
            for value in information["rpaths"]:
                if value.startswith("/") and not _system_absolute(value, platform):
                    _tool(["install_name_tool", "-delete_rpath", value, str(image)])
                    changed = True
            if changed:
                # Editing load commands invalidates an existing ad-hoc signature
                # on arm64. Re-sign only this new staged image, without a signing
                # identity/Keychain lookup; pin the resulting bytes at assembly.
                _tool(["codesign", "--force", "--sign", "-", "--timestamp=none", str(image)])
            information = native_dependencies(image, platform)
        interpreter = information["interpreter"]
        expected_interpreter = "/usr/lib/dyld" if platform.endswith("-darwin") else ELF_INTERPRETERS[platform]
        if interpreter is not None and interpreter != expected_interpreter:
            raise ValueError(f"non-system native interpreter: {interpreter}")
        identity = information["identity"]
        if identity and identity.startswith("/") and not _system_absolute(identity, platform):
            raise ValueError(f"non-relocatable native install identity: {identity}")
        rpaths = []
        for value in information["rpaths"]:
            if value.startswith("/"):
                if not _system_absolute(value, platform):
                    raise ValueError(f"non-system absolute native rpath: {value}")
            else:
                rpaths.append(expand(value, image))
        for reference in information["needed"]:
            dependency = resolve(reference, image, rpaths)
            if dependency is not None:
                pending.append(dependency)
        image_hash = None if relocate else (hashes.get(image) if hashes is not None else None)
        if image_hash is None and not relocate:
            image_hash = digest(image)
        visited[relative] = {"sha256": image_hash, "loader": information}
    return {"images": visited, "system": sorted(system)}


def make_catalog(runtime: Path, project: Path, packages: Path, platform: str,
                 mathlib_exports: set[str] | None = None) -> dict:
    """Capture trusted producer expectations before pruning, not a candidate.

    Initial exported module enumeration relies on successful trusted build and
    hash-pinned runtime/cache inputs. Required family selection is independent
    of candidate inventory. Explicit intended Mathlib exports come from the
    producer's reachability decision before the pruning operation.
    """
    _profile(platform)
    runtime, project, packages = (p.resolve(strict=True) for p in (runtime, project, packages))
    if (project / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise ValueError("Aeneas producer toolchain does not match RC2 profile")
    producers = [("lean", runtime, Path("lean"), runtime / "lib/lean",
                  [runtime / "src/lean", runtime / "src/lean/lake"]),
                 ("aeneas", project, Path("aeneas/backends/lean"), project / ".lake/build/lib/lean", [project])]
    for package in sorted(packages.iterdir()):
        if not package.is_dir() or package.name == ".lake":
            continue
        if package.is_symlink():
            raise ValueError("producer package roots must be physical")
        lib = package / ".lake/build/lib/lean"
        if lib.is_dir():
            producers.append((package.name, package, Path("aeneas/packages") / package.name, lib, [package]))
        elif package.name == "mathlib" or lib.is_symlink():
            raise ValueError("required or dangling package compiled exports")
        # Source-only Cli is not a compiled provider and is not fabricated.
    modules = {}
    input_hashes = {}
    def sha(path):
        physical = path.resolve(strict=True)
        if physical not in input_hashes:
            input_hashes[physical] = digest(path)
        return input_hashes[physical]
    for provider, owner, prefix, lib, roots in producers:
        inventory = list(files(lib, owner))
        if provider == "aeneas":
            # Cache extraction can mirror Mathlib into the project build root.
            # prune_root_mathlib_cache later removes this cache; the canonical
            # package producer owns its selected exports, never these copies.
            inventory = [path for path in inventory
                         if path.relative_to(lib).parts[0] != "Mathlib"
                         and not path.relative_to(lib).parts[0].startswith("Mathlib.")]
        oleans = {p.relative_to(lib).with_suffix("") for p in inventory if p.suffix == ".olean"}
        # An orphan companion cannot disappear by shrinking the module list.
        for path in inventory:
            rel = path.relative_to(lib)
            for family in SPLIT:
                suffix = "." + family
                if str(rel).endswith(suffix) and Path(str(rel)[:-len(suffix)]) not in oleans:
                    raise ValueError(f"orphan module family input: {path}")
        if provider == "mathlib" and mathlib_exports is not None:
            selected = {Path(*name.split(".")) for name in mathlib_exports}
            if not selected <= oleans:
                raise ValueError("intended Mathlib export is missing before pruning")
        else:
            selected = oleans
        for module_path in sorted(selected):
            name = ".".join(module_path.parts)
            if not name or name in modules:
                raise ValueError(f"duplicate exact module provider: {name}")
            sources = [root / module_path.with_suffix(".lean") for root in roots
                       if (root / module_path.with_suffix(".lean")).exists() or (root / module_path.with_suffix(".lean")).is_symlink()]
            if len(sources) != 1:
                raise ValueError(f"module requires exactly one corresponding source: {name}")
            source = sources[0]
            checked(source, owner)
            required = SPLIT if is_split(source) else LEGACY
            family = {}
            for suffix in required:
                artifact = lib / (str(module_path) + "." + suffix)
                checked(artifact, owner)
                if suffix != "ilean":
                    check_olean(artifact)
                family[suffix] = {"path": str(prefix / artifact.relative_to(owner)), "sha256": sha(artifact)}
            # Reject mixed source-format families, instead of silently treating
            # an independent producer option as this reviewed source profile.
            if required == LEGACY and any((lib / (str(module_path) + "." + suffix)).exists() for suffix in SPLIT[2:]):
                raise ValueError(f"source/build module-format disagreement: {name}")
            modules[name] = {"provider": provider, "source": {"path": str(prefix / source.relative_to(owner)),
                            "sha256": sha(source)}, "artifacts": family}
    if not modules:
        raise ValueError("no compiled module exports")
    plugin_name = "libaeneas_AeneasMeta." + ("dylib" if platform.endswith("-darwin") else "so")
    plugin = project / ".lake/build/lib" / plugin_name
    checked(plugin, project)
    check_native(plugin, platform)
    for name in ("lean", "lake"):
        executable = runtime / "bin" / name
        checked(executable, runtime)
        if executable.is_symlink() or not executable.stat().st_mode & 0o111:
            raise ValueError("real executable Lean/Lake launcher pair required")
        check_native(executable, platform)
    runtime_inventory = {}
    for directory in ("bin", "lib", "include"):
        for path in files(runtime / directory, runtime):
            with path.open("rb") as stream:
                magic = stream.read(4)
            runtime_inventory[str(path.relative_to(runtime))] = {
                "sha256": sha(path), "publisher_relocation": (magic == b"\x7fELF" and bool(path.stat().st_mode & 0o111)) or magic == b"\xcf\xfa\xed\xfe"}
    native_inventory = {}
    for path in files(plugin.parent, project):
        if path.suffix == ".dylib" or re.search(r"\.so(?:\.\d+)*$", path.name):
            checked(path, project)
            native_inventory[str(Path("aeneas/backends/lean") / path.relative_to(project))] = sha(path)
    return {"schema": 1, "lean_toolchain": TOOLCHAIN, "compiler_hash": COMPILER_HASH,
            "platform": platform, "profile": "rc2-source-module-directive-v1",
            "plugin": {"path": str(Path("aeneas/backends/lean/.lake/build/lib") / plugin_name),
                       "producer_sha256": sha(plugin)}, "modules": modules,
            "runtime_inventory": runtime_inventory,
            "native_inventory": native_inventory,
            "trust": "hash-pinned runtime/cache inputs, successful coherent producer build; catalog captured before pruning"}


def _archive_path(root: Path, relative: str) -> Path:
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts or not rel.parts or rel.parts[0] not in ("lean", "aeneas"):
        raise ValueError(f"invalid archive input path: {relative}")
    path = root / rel
    checked(path, root / rel.parts[0])
    return path


def catalog_finite(root: Path, catalog: dict) -> dict:
    """Extend pre-pruning exports with a freshly built staged native producer.

    Source/recipe stay exact; executable relocation is checked and its final
    bytes plus actual loader closure enter assembly identity. Old catalogs may
    still publish descriptor1; production's new workflow always calls this.
    """
    root = root.resolve(strict=True)
    if (root / "lean-sdk").exists() or "finite_lake" in catalog:
        raise ValueError("finite producer capture requires fresh staging")
    _profile(catalog["platform"])
    path = root / "lean/bin/anneal-finite-lake"
    if path.is_symlink() or not path.stat().st_mode & 0o111:
        raise ValueError("finite helper must be a real executable")
    checked(path, root / "lean")
    check_native(path, catalog["platform"])
    result = json.loads(json.dumps(catalog))
    source = _archive_path(root, "lean/src/anneal/FiniteLake.lean")
    recipe = _archive_path(root, "lean/src/anneal/build-finite-lake.py")
    helper_hash = digest(path)
    result["finite_lake"] = {
        "path": "lean/bin/anneal-finite-lake", "producer_sha256": helper_hash, "protocol": 1,
        "source": {"path": str(source.relative_to(root)), "sha256": digest(source)},
        "recipe": {"path": str(recipe.relative_to(root)), "sha256": digest(recipe)}}
    result["runtime_inventory"]["bin/anneal-finite-lake"] = {
        "sha256": helper_hash, "publisher_relocation": True}
    return result


def finite_producer(root: Path, catalog: dict) -> tuple[Path | None, dict | None]:
    if "finite_lake" not in catalog:
        return None, None
    row = catalog["finite_lake"]
    if not isinstance(row, dict) or set(row) != {"path", "producer_sha256", "protocol", "source", "recipe"} or type(row["protocol"]) is not int or row["protocol"] != 1 or row["path"] != "lean/bin/anneal-finite-lake":
        raise ValueError("unsupported finite publisher protocol")
    identity = {"protocol": 1}
    for key, expected in [("source", "lean/src/anneal/FiniteLake.lean"),
                          ("recipe", "lean/src/anneal/build-finite-lake.py")]:
        value = row[key]
        if not isinstance(value, dict) or set(value) != {"path", "sha256"} or value["path"] != expected:
            raise ValueError("finite source/recipe ownership mismatch")
        path = _archive_path(root, value["path"])
        if digest(path) != value["sha256"]:
            raise ValueError("finite source/recipe changed since producer capture")
        identity[key] = value
    helper = _archive_path(root, row["path"])
    if helper.is_symlink() or not helper.stat().st_mode & 0o111:
        raise ValueError("finite helper must be a real executable")
    check_native(helper, catalog["platform"])
    expected = catalog["runtime_inventory"].get("bin/anneal-finite-lake")
    if expected != {"sha256": row["producer_sha256"], "publisher_relocation": True}:
        raise ValueError("finite helper has no coherent runtime producer")
    return helper, identity


def catalog_support(root: Path, catalog: dict) -> dict:
    """Add only the freshly compiled invariant module to the unified view.

    Local Config, strict sorry handlers and consumer calls are not SDK exports.
    The admitted immutable module map itself selects support sharing.
    """
    root = root.resolve(strict=True)
    if (root / "lean-sdk").exists() or (root / "lean-sdk").is_symlink() or "anneal_support" in catalog or "AnnealSupport" in catalog["modules"]:
        raise ValueError("support producer capture requires fresh staging")
    source = _archive_path(root, "lean/src/lean/AnnealSupport.lean")
    recipe = _archive_path(root, "lean/src/anneal/build-anneal-support.py")
    if is_split(source):
        raise ValueError("AnnealSupport requires unchanged legacy source format")
    result = json.loads(json.dumps(catalog))
    artifacts = {}
    for suffix in LEGACY:
        relative = "lean/lib/lean/AnnealSupport." + suffix
        path = _archive_path(root, relative)
        if path.is_symlink():
            raise ValueError("support compiler artifacts must be physical")
        if suffix != "ilean":
            check_olean(path)
        runtime_relative = str(path.relative_to(root / "lean"))
        if runtime_relative in result["runtime_inventory"]:
            raise ValueError("support artifact already in runtime producer capture")
        artifacts[suffix] = {"path": relative, "sha256": digest(path)}
        result["runtime_inventory"][runtime_relative] = {
            "sha256": artifacts[suffix]["sha256"], "publisher_relocation": False}
    result["modules"]["AnnealSupport"] = {"provider": "lean",
        "source": {"path": str(source.relative_to(root)), "sha256": digest(source)},
        "artifacts": artifacts}
    result["anneal_support"] = {"recipe": {"path": str(recipe.relative_to(root)), "sha256": digest(recipe)}}
    return result


def support_producer(root: Path, catalog: dict) -> dict | None:
    if "anneal_support" not in catalog:
        return None
    row = catalog["anneal_support"]
    if not isinstance(row, dict) or set(row) != {"recipe"}:
        raise ValueError("unsupported support publisher fields")
    recipe = row["recipe"]
    if not isinstance(recipe, dict) or set(recipe) != {"path", "sha256"} or recipe["path"] != "lean/src/anneal/build-anneal-support.py":
        raise ValueError("support recipe ownership mismatch")
    if digest(_archive_path(root, recipe["path"])) != recipe["sha256"]:
        raise ValueError("support recipe changed since producer capture")
    module = catalog["modules"].get("AnnealSupport")
    if not isinstance(module, dict) or module.get("provider") != "lean" or module.get("source", {}).get("path") != "lean/src/lean/AnnealSupport.lean" or set(module.get("artifacts", {})) != set(LEGACY):
        raise ValueError("support has no coherent module producer")
    for suffix, artifact in module["artifacts"].items():
        expected = {"sha256": artifact["sha256"], "publisher_relocation": False}
        if catalog["runtime_inventory"].get("lib/lean/AnnealSupport." + suffix) != expected:
            raise ValueError("support has no coherent runtime producer")
    return row


def link_overlay(sdk: Path, archive: Path, links: dict[Path, Path]):
    """Compact complete immutable subtrees; merge partial namespaces exactly."""
    def materialize(prefix: Path, entries: dict[Path, Path]):
        destination = sdk / prefix
        if prefix in entries:
            if len(entries) != 1:
                raise ValueError("SDK file/directory collision")
            destination.symlink_to(os.path.relpath(entries[prefix], destination.parent))
            return
        sample, target = next(iter(entries.items()))
        tail = sample.relative_to(prefix)
        candidate = target.parents[len(tail.parts) - 1]
        if prefix.parts and all(path == candidate / name.relative_to(prefix) for name, path in entries.items()):
            try:
                actual = set(files(candidate, archive))
            except (OSError, ValueError, RuntimeError):
                # Unrelated source administration can prevent compaction; it
                # does not become an input merely because it is nearby.
                actual = None
            if actual == set(entries.values()):
                destination.symlink_to(os.path.relpath(candidate, destination.parent), target_is_directory=True)
                return
        destination.mkdir(exist_ok=True)
        children = {}
        for relative, target in entries.items():
            child = prefix / relative.relative_to(prefix).parts[0]
            children.setdefault(child, {})[relative] = target
        for child, subset in sorted(children.items()):
            materialize(child, subset)
    materialize(Path(), links)


def assemble(root: Path, catalog: dict, *, allow_native_relocation: bool = False) -> dict:
    """Validate first; create new root/lean-sdk; reference large inputs in place.

    Native/runtime staging may have been transformed by the trusted publisher
    (e.g. Linux ELF relocation). Source/module hashes must still match the
    pre-pruning catalog. Final consumed native/runtime hashes enter SDK identity;
    they are not represented as equal to pre-transformation producer bytes.
    """
    root = root.resolve(strict=True)
    sdk = root / "lean-sdk"
    if sdk.exists() or sdk.is_symlink():
        raise FileExistsError("SDK assembly requires a new destination")
    if catalog.get("schema") != 1 or catalog.get("lean_toolchain") != TOOLCHAIN or catalog.get("compiler_hash") != COMPILER_HASH or catalog.get("profile") != "rc2-source-module-directive-v1":
        raise ValueError("unsupported publisher catalog/profile")
    platform = catalog["platform"]
    _profile(platform)
    finite_helper, finite_identity = finite_producer(root, catalog)
    support_identity = support_producer(root, catalog)
    modules = catalog["modules"]
    if not isinstance(modules, dict) or not modules:
        raise ValueError("missing expected exported module catalog")
    links = {}
    verified_hashes = {}
    for name, row in modules.items():
        parts = name.split(".")
        if any(not part or part in (".", "..") or "/" in part or "\\" in part for part in parts):
            raise ValueError("invalid exact module name")
        source = _archive_path(root, row["source"]["path"])
        required = set(SPLIT if is_split(source) else LEGACY)
        if set(row["artifacts"]) != required:
            raise ValueError(f"expected profile is incomplete or incoherent: {name}")
        module = Path(*parts)
        provider = row["provider"]
        if not isinstance(provider, str) or not provider or "/" in provider or "\\" in provider or provider in (".", ".."):
            raise ValueError("invalid provider identity")
        provider_prefix = Path("lean") if provider == "lean" else Path("aeneas/backends/lean") if provider == "aeneas" else Path("aeneas/packages") / provider
        expected_sources = [provider_prefix / "src/lean" / module.with_suffix(".lean"),
                            provider_prefix / "src/lean/lake" / module.with_suffix(".lean")] if provider == "lean" else [provider_prefix / module.with_suffix(".lean")]
        if source.relative_to(root) not in expected_sources:
            raise ValueError("source/provider mismatch")
        inputs = [(source, row["source"]["sha256"], Path("src/lean") / module.with_suffix(".lean"))]
        for suffix, artifact in row["artifacts"].items():
            path = _archive_path(root, artifact["path"])
            lib = Path("lib/lean") if provider == "lean" else Path(".lake/build/lib/lean")
            if path.relative_to(root) != provider_prefix / lib / (str(module) + "." + suffix):
                raise ValueError("artifact/provider mismatch")
            checked(path, root / provider_prefix)
            if suffix != "ilean":
                check_olean(path)
            inputs.append((path, artifact["sha256"], Path("lib/lean") / (str(module) + "." + suffix)))
        checked(source, root / provider_prefix)
        for path, expected_hash, destination in inputs:
            actual_hash = digest(path)
            if actual_hash != expected_hash:
                raise ValueError(f"input changed since trusted producer catalog: {path}")
            verified_hashes[path.resolve(strict=True)] = actual_hash
            if destination in links:
                raise ValueError("duplicate exact SDK file")
            links[destination] = path
    runtime = root / "lean"
    final_runtime = {}
    expected_runtime = catalog["runtime_inventory"]
    # Conservatively pin the full runtime support trees, including helpers not
    # invoked by ordinary proof consumers. Pruning that identity further is a
    # separate reviewed optimization. Do not infer helper ABI requirements from
    # this proof/native-plugin profile (RC2 aarch64's unused leantar is x86_64).
    for directory in ("bin", "lib", "include"):
        # Lean include is needed by native tool operations; do not silently omit
        # it merely because the current proof fixture does not invoke a C compiler.
        for path in files(runtime / directory, runtime):
            relative = str(path.relative_to(runtime))
            if relative not in expected_runtime:
                raise ValueError("unaccounted runtime file in staged candidate")
            physical = path.resolve(strict=True)
            actual_hash = verified_hashes.get(physical)
            if actual_hash is None:
                actual_hash = digest(path)
            expectation = expected_runtime[relative]
            if actual_hash != expectation["sha256"]:
                if not (allow_native_relocation and expectation["publisher_relocation"]):
                    raise ValueError(f"runtime changed since trusted producer catalog: {path}")
                if relative in ("bin/lean", "bin/lake"):
                    check_native(path, platform)
            final_runtime[relative] = actual_hash
            verified_hashes[physical] = actual_hash
    if set(final_runtime) != set(expected_runtime):
        raise ValueError("expected runtime support file missing after staging")
    for name in ("lean", "lake"):
        path = runtime / "bin" / name
        if path.is_symlink() or not path.stat().st_mode & 0o111:
            raise ValueError("real executable Lean/Lake launcher pair required")
        check_native(path, platform)
    plugin = _archive_path(root, catalog["plugin"]["path"])
    check_native(plugin, platform)
    plugin_hash = digest(plugin)
    if plugin_hash != catalog["plugin"]["producer_sha256"] and not allow_native_relocation:
        raise ValueError("native plugin changed outside trusted publisher relocation")
    verified_hashes[plugin.resolve(strict=True)] = plugin_hash
    native_closure = loader_closure(root, plugin, platform, hashes=verified_hashes,
                                   extra_images=(finite_helper,) if finite_helper else ())
    for relative, image in native_closure["images"].items():
        if Path(relative).is_relative_to("lean"):
            continue  # Complete runtime hashes were checked above.
        expected = catalog["native_inventory"].get(relative)
        if expected is None or (image["sha256"] != expected and not allow_native_relocation):
            raise ValueError(f"unaccounted or changed native provider image: {relative}")
    plugin_relative = "../" + catalog["plugin"]["path"]
    module_bytes = encoded({"schema": 1, "modules": sorted(modules)})
    descriptor = {"schema": 1, "lean_toolchain": TOOLCHAIN, "compiler_hash": COMPILER_HASH,
                  "platform": platform, "runtime": "../lean", "source_roots": ["src/lean"],
                  "import_roots": ["lib/lean"], "loader_roots": ["lib", "lib/lean", "../" + str(plugin.parent.relative_to(root))],
                  "plugins": [{"path": plugin_relative, "name": "aeneas_AeneasMeta"}],
                  "modules": "modules.json", "modules_sha256": hashlib.sha256(module_bytes).hexdigest()}
    if finite_helper is not None:
        descriptor.update(schema=2, finite_lake={"path": "bin/anneal-finite-lake",
                          "sha256": verified_hashes[finite_helper.resolve(strict=True)], "protocol": 1})
    # Paths are archive-relative, so moving the entire archive keeps identity.
    # Full producer/catalog envelope hashes and all Rust bytes are excluded.
    content = {"descriptor": dict(descriptor), "modules": modules, "runtime": final_runtime,
               "plugin": {"path": catalog["plugin"]["path"], "sha256": plugin_hash}, "native_closure": native_closure}
    if finite_identity is not None:
        content["finite_lake_producer"] = finite_identity
    if support_identity is not None:
        content["anneal_support_producer"] = support_identity
    descriptor["id"] = hashlib.sha256(encoded(content)).hexdigest()
    # All validation precedes destination creation. If an IO failure occurs
    # afterward, retain the incomplete destination; never adopt/repair it.
    sdk.mkdir()
    link_overlay(sdk, root, links)
    # Non-module runtime support (shared/static libraries, compiler helpers and
    # headers) remains in the original runtime. Module families have an exact
    # merged overlay, so Shared.A and Shared.B may have distinct producers.
    for directory in ("bin", "lib", "include"):
        destination_dir = sdk / directory
        destination_dir.mkdir(exist_ok=True)
        for target in sorted((runtime / directory).iterdir()):
            if directory == "bin" and target.name in ("lean", "lake", "anneal-finite-lake"):
                shutil.copy2(target, destination_dir / target.name, follow_symlinks=False)
            elif directory == "lib" and target.name == "lean":
                for support in sorted(target.iterdir()):
                    if not (sdk / "lib/lean" / support.name).exists():
                        # A directory already represented by module families is
                        # kept as the overlay; runtime support files at its root
                        # still get links below. No unprofiled module is exported.
                        if support.is_dir() or (support.is_file() and support.suffix not in (".olean", ".ilean", ".ir", ".private", ".server")):
                            (sdk / "lib/lean" / support.name).symlink_to(os.path.relpath(support, sdk / "lib/lean"))
            else:
                (destination_dir / target.name).symlink_to(os.path.relpath(target, destination_dir))
    # Support inputs can share a directory with exported modules. Merge those
    # files without replacing the exact module-family overlay or copying bytes.
    for relative in sorted(final_runtime):
        rel = Path(relative)
        if not rel.is_relative_to("lib/lean") or any(str(rel).endswith("." + family) for family in SPLIT):
            continue
        destination = sdk / rel
        if not destination.exists():
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.symlink_to(os.path.relpath(runtime / rel, destination.parent))
    for filename, data in (("modules.json", module_bytes), ("sdk.json", encoded(descriptor)),
                           ("publisher-catalog.json", encoded({"producer": catalog, "published": content}))):
        with (sdk / filename).open("xb") as stream:
            stream.write(data)
    for base, directories, filenames in os.walk(sdk, followlinks=False):
        for name in filenames:
            path = Path(base) / name
            if not path.is_symlink():
                path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
        for name in directories:
            path = Path(base) / name
            if not path.is_symlink():
                path.chmod(stat.S_IMODE(path.stat().st_mode) & ~0o222)
    sdk.chmod(stat.S_IMODE(sdk.stat().st_mode) & ~0o222)
    return descriptor


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    producer = commands.add_parser("catalog")
    for arg in ("runtime", "project-root", "packages-root", "output", "pruner"):
        producer.add_argument("--" + arg, type=Path, required=True)
    producer.add_argument("--platform", required=True)
    publish = commands.add_parser("assemble")
    publish.add_argument("--root", type=Path, required=True)
    publish.add_argument("--catalog", type=Path, required=True)
    publish.add_argument("--allow-native-relocation", action="store_true",
                         help="trust the producer's explicit native relocation step; pin its resulting bytes")
    relocation = commands.add_parser("relocate-darwin")
    relocation.add_argument("--root", type=Path, required=True)
    relocation.add_argument("--catalog", type=Path, required=True)
    finite = commands.add_parser("catalog-finite")
    finite.add_argument("--root", type=Path, required=True)
    finite.add_argument("--catalog", type=Path, required=True)
    finite.add_argument("--output", type=Path, required=True)
    support = commands.add_parser("catalog-support")
    support.add_argument("--root", type=Path, required=True)
    support.add_argument("--catalog", type=Path, required=True)
    support.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "catalog":
        spec = importlib.util.spec_from_file_location("lean_sdk_pruning_policy", args.pruner)
        pruner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(pruner)
        exports = pruner.collect_mathlib_closure(args.project_root.resolve(), args.packages_root.resolve())
        catalog = make_catalog(args.runtime, args.project_root, args.packages_root, args.platform, exports)
        with args.output.open("xb") as stream:
            stream.write(encoded(catalog))
    elif args.command == "catalog-finite":
        catalog = catalog_finite(args.root, json.loads(args.catalog.read_text()))
        with args.output.open("xb") as stream:
            stream.write(encoded(catalog))
    elif args.command == "catalog-support":
        catalog = catalog_support(args.root, json.loads(args.catalog.read_text()))
        with args.output.open("xb") as stream:
            stream.write(encoded(catalog))
    elif args.command == "relocate-darwin":
        root = args.root.resolve(strict=True)
        catalog = json.loads(args.catalog.read_text())
        if not catalog["platform"].endswith("-darwin"):
            raise ValueError("Darwin relocation requires a Darwin producer")
        helper, _ = finite_producer(root, catalog)
        loader_closure(root, _archive_path(root, catalog["plugin"]["path"]), catalog["platform"],
                       relocate=True, extra_images=(helper,) if helper else ())
    else:
        assemble(args.root, json.loads(args.catalog.read_text()), allow_native_relocation=args.allow_native_relocation)


if __name__ == "__main__":
    main()
