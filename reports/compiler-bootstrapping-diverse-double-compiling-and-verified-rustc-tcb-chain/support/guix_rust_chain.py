#!/usr/bin/env python3
"""Recover the Rust bootstrap chain encoded in GNU Guix `gnu/packages/rust.scm`.

Usage:
    python3 guix_rust_chain.py <path to rust.scm>

The file is not on GitHub; fetch it at an immutable Guix commit, e.g.
    https://codeberg.org/guix/guix/raw/commit/<commit>/gnu/packages/rust.scm

What is parsed (all from the file text, nothing hardcoded):
  * `(define-public rust-bootstrap-X.Y` packages: rustc built by mrustc.
  * `(define-public rust-X.Y` packages and the `rust-bootstrapped-package
    <base> "<version>"` call inside each, which names the previous compiler.
  * `(if (supported-package? rust-bootstrap-X.Y) ... rust-bootstrap-X.Y ...)`
    native-input overrides, which splice an mrustc-built compiler into the
    chain in place of `<base>` on supported systems.
  * `(define-public rust` and its `(base-rust rust-X.Y)` binding.
  * `%mrustc-commit-X.Y` pins.

Output: JSON with the per-package edges and the chain lengths from each
mrustc-built entry point to the default `rust` package.
"""

import hashlib
import json
import re
import sys


def parse(src: str) -> dict:
    lines = src.split("\n")
    heads = []
    for i, line in enumerate(lines):
        m = re.match(r"\(define-public (rust(?:-bootstrap)?(?:-[0-9.]+)?)\s*$", line)
        if m:
            heads.append((i, m.group(1)))
    # A package body runs to the next top-level form.
    top = [i for i, line in enumerate(lines) if line.startswith("(")]
    packages = {}
    for i, name in heads:
        end = next((t for t in top if t > i), len(lines))
        body = "\n".join(lines[i:end])
        boot = re.search(
            r"rust-bootstrapped-package\s+(?:;[^\n]*\n\s*)*(rust[-a-z0-9.]*)\s+\"([0-9.]+)\"", body
        )
        version = re.search(r"\(version \"([0-9.]+)\"\)", body)
        splice = re.search(r"\(supported-package\? (rust-bootstrap-[0-9.]+)\)", body)
        direct = re.findall(r"^\s+(rust-bootstrap-[0-9.]+)\s*$", body, flags=re.M)
        base_binding = re.search(r"\(base-rust (rust-[0-9.]+)\)", body)
        packages[name] = {
            "line": i + 1,
            "bootstrapped_from": boot.group(1) if boot else None,
            "version": boot.group(2) if boot else (version.group(1) if version else None),
            "conditional_mrustc_input": splice.group(1) if splice else None,
            "unconditional_mrustc_input": direct[0] if (direct and not splice) else None,
            "base_rust_binding": base_binding.group(1) if base_binding else None,
        }
    mrustc_pins = dict(re.findall(r"\(define %mrustc-commit-([0-9.]+) \"([0-9a-f]{40})\"\)", src))
    return {"packages": packages, "mrustc_commit_pins": mrustc_pins}


def chain_from(packages: dict, entry: str, default: str) -> list:
    """Walk from the default package back to `entry`, taking a splice at `entry`."""
    path = []
    cur = default
    seen = set()
    while cur and cur not in seen:
        seen.add(cur)
        p = packages[cur]
        path.append((cur, p["version"]))
        if entry in (p["conditional_mrustc_input"], p["unconditional_mrustc_input"]):
            path.append((entry, packages[entry]["version"]))
            return list(reversed(path))
        cur = p["bootstrapped_from"]
    return []


def main() -> int:
    raw = open(sys.argv[1], "rb").read()
    info = parse(raw.decode("utf-8"))
    pk = info["packages"]
    default_base = pk["rust"]["base_rust_binding"]
    out = {
        "rust_scm_sha256": hashlib.sha256(raw).hexdigest(),
        "mrustc_commit_pins": info["mrustc_commit_pins"],
        "default_rust_package_base": default_base,
        "default_rust_version": pk[default_base]["version"] if default_base else None,
        "mrustc_built_entry_points": sorted(n for n in pk if n.startswith("rust-bootstrap-")),
        "rustc_built_packages": len([n for n in pk if re.fullmatch(r"rust-[0-9.]+", n)]),
        "chains": {},
        "packages": pk,
    }
    for entry in out["mrustc_built_entry_points"]:
        chain = chain_from(pk, entry, default_base) if default_base else []
        out["chains"][entry] = {
            "versions": [v for _, v in chain],
            "rustc_builds_including_mrustc_built": len(chain),
            "rustc_by_rustc_builds": max(len(chain) - 1, 0),
        }
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
