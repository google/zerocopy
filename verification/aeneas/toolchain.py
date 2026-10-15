# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Read Anneal's archive identity and validate the local CLI patch installation.

The flake lock identifies the upstream sources; the archive supplies their runtime
versions. This module stores no independent upstream pin and never edits metadata.
"""
import argparse
import ctypes
import errno
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import shlex
import subprocess

PATCH_SHA256 = "a61422f5483f4f753164e0e9e209cc0c872f8072c3318728746665f878bf6b19"
PATCH_SUFFIX = "+nominal-tuple-structs.1"


def digest(path):
    result = hashlib.sha256()
    with path.open('rb') as file:
        for block in iter(lambda: file.read(1024 * 1024), b''):
            result.update(block)
    return result.hexdigest()


def publish_installation(source, destination):
    """Atomically rename a staged directory only if the destination is absent."""
    if source.is_symlink() or not source.is_dir():
        raise ValueError(f"Publication source must be a physical directory: {source}")
    library = ctypes.CDLL(None, use_errno=True)
    host = platform.system()
    if host == "Darwin":
        # SDK sys/stdio.h: renamex_np(..., RENAME_EXCL), RENAME_EXCL = 4.
        rename = getattr(library, "renamex_np", None)
        if rename is None:
            raise OSError(errno.ENOSYS, "Exclusive directory rename is unavailable")
        rename.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint]
        rename.restype = ctypes.c_int
        result = rename(os.fsencode(source), os.fsencode(destination), 4)
    elif host == "Linux":
        # Linux uapi/linux/fs.h and fcntl.h: RENAME_NOREPLACE = 1, AT_FDCWD = -100.
        rename = getattr(library, "renameat2", None)
        if rename is None:
            raise OSError(errno.ENOSYS, "Exclusive directory rename is unavailable")
        rename.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int,
                           ctypes.c_char_p, ctypes.c_uint]
        rename.restype = ctypes.c_int
        result = rename(-100, os.fsencode(source), -100, os.fsencode(destination), 1)
    else:
        raise OSError(errno.ENOSYS, f"Exclusive directory rename is unsupported on {host}")
    if result != 0:
        code = ctypes.get_errno()
        raise OSError(code, f"Publication rejected; source preserved at {source}: " + os.strerror(code),
                      str(destination))


def build_identity(repo):
    """Bind the archive producer and patched builder, without adding upstream pins."""
    files = ["anneal/flake.lock", "anneal/flake.nix", "anneal/v1/Cargo.toml",
             "anneal/rewrite-lake-vendor.py", "anneal/prune-lake-cache.py",
             "verification/aeneas/build-aeneas.nix", "verification/aeneas/build-aeneas.sh",
             "verification/aeneas/setup.sh", "verification/aeneas/toolchain.py",
             "verification/aeneas/patches/use-tuple-structs.patch",
             "verification/aeneas/patches/admission-snapshot.patch"]
    lean_root = repo / "anneal/lean"
    # The companion manifest is generated with checkout-specific paths. The
    # authoritative top-level manifest remains an archive build input.
    files += [str(p.relative_to(repo)) for p in lean_root.rglob("*")
              if p.is_file() and ".lake" not in p.relative_to(lean_root).parts
              and p.relative_to(lean_root) != Path("aeneas/lake-manifest.json")]
    return {"schema": 1, "platform": [platform.system(), platform.machine()],
            "inputs": {name: digest(repo / name) for name in sorted(files)}}


def cache_key(repo):
    return hashlib.sha256(json.dumps(build_identity(repo), sort_keys=True).encode()).hexdigest()


def payload_digest(tools):
    """Hash every installed runtime and library byte, including Lean build artifacts.

    Payload symlinks must stay within the installation. Hash their spelling too,
    so replacing an adapter does not preserve the installation's identity.
    """
    result = hashlib.sha256()
    for path in sorted(tools.rglob("*")):
        if path == tools / "aeneas-build.json":
            continue
        relative = str(path.relative_to(tools))
        if path.is_symlink():
            if not path.resolve().is_relative_to(tools.resolve()):
                raise ValueError(f"Runtime payload symlink leaves installation: {relative}")
            value = [relative, "symlink", os.readlink(path)]
        elif path.is_file():
            value = [relative, "file", digest(path), bool(path.stat().st_mode & 0o111)]
        elif path.is_dir():
            value = [relative, "directory"]
        else:
            raise ValueError(f"Unsupported runtime payload entry: {relative}")
        result.update(json.dumps(value).encode() + b"\n")
    return result.hexdigest()


def load_metadata(repo, tools):
    lock = json.loads((repo / "anneal/flake.lock").read_text())
    nodes = lock["nodes"]
    aeneas = nodes[nodes[lock["root"]]["inputs"]["aeneas"]]
    charon = nodes[aeneas["inputs"]["charon"]]
    data = json.loads((tools / "bundle/aeneas/metadata.json").read_text())
    fields = {"aeneas-release", "aeneas-revision", "aeneas-source-nar-hash",
              "charon-revision", "lean-toolchain", "rust-toolchain-date",
              "rust-toolchain-version"}
    if not isinstance(data, dict) or set(data) != fields or not all(isinstance(v, str) for v in data.values()):
        raise ValueError("Invalid Anneal archive metadata")
    expected = {"aeneas-revision": aeneas["locked"]["rev"],
                "aeneas-source-nar-hash": aeneas["locked"]["narHash"],
                "charon-revision": charon["locked"]["rev"]}
    for key, value in expected.items():
        if data.get(key) != value:
            raise ValueError(f"Anneal archive identity mismatch: {key}")
    if not re.fullmatch(r"nightly-\d{4}\.\d{2}\.\d{2}-" + expected["aeneas-revision"][:7], data["aeneas-release"]):
        raise ValueError("Anneal archive release/source mismatch")
    if not re.fullmatch(r"\d+\.\d+\.\d+", data["lean-toolchain"]):
        raise ValueError("Invalid archive Lean version")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", data["rust-toolchain-date"]):
        raise ValueError("Invalid archive Rust date")
    if data["rust-toolchain-version"] != "nightly-" + data["rust-toolchain-date"]:
        raise ValueError("Anneal archive Rust date/version mismatch")
    if digest(repo / "verification/aeneas/patches/use-tuple-structs.patch") != PATCH_SHA256:
        raise ValueError("Checked-in CLI patch digest mismatch")
    return data


def runtime_env(tools):
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join([str(tools / "rust/bin"), str(tools / "lean/bin"), str(tools), env.get("PATH", "")])
    libs = os.pathsep.join(str(tools / p) for p in ["rust/lib", "lean/lib", "lean/lib/lean"])
    for key in ["LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"]:
        env[key] = libs + (os.pathsep + env[key] if env.get(key) else "")
    env["LEAN_SYSROOT"] = str(tools / "lean")
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"
    return env


def output(tools, binary, *args):
    return subprocess.check_output([str(tools / binary), *args], env=runtime_env(tools), text=True).strip()


def probe(tools, data, patched):
    version = data["aeneas-release"] + (PATCH_SUFFIX if patched else "")
    actual = output(tools, "aeneas", "-version")
    allowed = {"aeneas " + version}
    if not patched:
        allowed.add("aeneas " + data["aeneas-revision"][:7])
    if actual not in allowed:
        raise ValueError(f"Aeneas version mismatch: {actual}")
    charon = output(tools, "charon", "version")
    if not charon.endswith(" (" + data["charon-revision"] + ")"):
        raise ValueError("Charon revision mismatch")
    if output(tools, "charon", "toolchain-version") != data["rust-toolchain-version"]:
        raise ValueError("Charon Rust toolchain mismatch")
    rust = output(tools, "rust/bin/rustc", "--version")
    if not rust.startswith("rustc ") or "-nightly (" not in rust:
        raise ValueError("Invalid bundled nightly Rust compiler")
    lean = output(tools, "lean/bin/lean", "--version")
    if not lean.startswith("Lean (version " + data["lean-toolchain"] + ","):
        raise ValueError("Bundled Lean version mismatch")
    if (tools / "backends/lean/lean-toolchain").read_text().strip() != "leanprover/lean4:v" + data["lean-toolchain"]:
        raise ValueError("Backend Lean version mismatch")
    return charon.split(" (", 1)[0]


def provenance(tools, data, repo=None):
    result = {"metadata": data, "source_rev": data["aeneas-revision"],
            "source_nar_hash": data["aeneas-source-nar-hash"],
            "patch_sha256": PATCH_SHA256,
            "admission_patch_sha256": digest(Path(__file__).with_name("patches") / "admission-snapshot.patch"),
            "version": data["aeneas-release"] + PATCH_SUFFIX,
            "binary_sha256": digest(tools / "aeneas"),
            "upstream_binary_sha256": digest(tools / "aeneas-upstream"),
            "runtime_binary_sha256": {name: digest(tools / name) for name in
                                      ["charon", "charon-driver", "rust/bin/rustc",
                                       "rust/bin/cargo", "lean/bin/lean", "lean/bin/lake"]},
            "libraries": {p.name: digest(p) for p in sorted((tools / "libs").glob("*.dylib"))}}
    if repo is not None:
        result["build_identity"] = build_identity(repo)
        result["payload_sha256"] = payload_digest(tools)
    return result


def validate(repo, tools, patched=True, cache=False):
    data = load_metadata(repo, tools)
    if patched:
        record = json.loads((tools / "aeneas-build.json").read_text())
        if cache and "build_identity" not in record:
            raise ValueError("Shared cache requires source/config provenance from a fresh installation")
        expected = provenance(tools, data, repo if "build_identity" in record else None)
        if record != expected:
            raise ValueError("Patched CLI provenance mismatch; rebuild in a fresh installation")
        upstream = output(tools, "aeneas-upstream", "-version")
        if upstream not in {"aeneas " + data["aeneas-release"], "aeneas " + data["aeneas-revision"][:7]}:
            raise ValueError("Upstream comparison binary version mismatch")
    charon_version = probe(tools, data, patched)
    return data, charon_version


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "shell", "record", "cache-key", "publish"])
    parser.add_argument("tools", type=Path, nargs="?")
    parser.add_argument("destination", type=Path, nargs="?")
    parser.add_argument("--cache", action="store_true")
    parser.add_argument("--upstream", action="store_true")
    args = parser.parse_intermixed_args()
    repo = Path(__file__).resolve().parents[2]
    if args.command == "cache-key":
        print(cache_key(repo))
        return
    if args.tools is None:
        parser.error("tools is required")
    if args.command == "publish":
        if args.destination is None:
            parser.error("publish requires a destination")
        publish_installation(args.tools.absolute(), args.destination.absolute())
        return
    if args.destination is not None:
        parser.error("destination is only supported for publish")
    tools = args.tools.resolve()
    if args.command == "record":
        data = load_metadata(repo, tools)
        probe(tools, data, True)
        record = tools / "aeneas-build.json"
        if record.exists() or record.is_symlink():
            raise ValueError("Refusing to overwrite CLI provenance")
        contents = json.dumps(provenance(tools, data, repo), indent=2) + "\n"
        with record.open("x") as destination:
            destination.write(contents)
        return
    data, charon = validate(repo, tools, patched=not args.upstream, cache=args.cache)
    if args.command == "shell":
        values = {"AENEAS_RELEASE": data["aeneas-release"], "AENEAS_REV": data["aeneas-revision"],
                  "AENEAS_SOURCE_NAR_HASH": data["aeneas-source-nar-hash"],
                  "AENEAS_VERSION": data["aeneas-release"] + PATCH_SUFFIX,
                  "AENEAS_PATCH_SHA256": PATCH_SHA256, "CHARON_VERSION": charon,
                  "CHARON_REV": data["charon-revision"],
                  "AENEAS_RUST_TOOLCHAIN": data["rust-toolchain-version"],
                  "AENEAS_LEAN_TOOLCHAIN": "leanprover/lean4:v" + data["lean-toolchain"],
                  "AENEAS_LEAN_VERSION": data["lean-toolchain"]}
        for key, value in values.items():
            print(key + "=" + shlex.quote(value))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit("Invalid Anneal toolchain: " + str(error))
