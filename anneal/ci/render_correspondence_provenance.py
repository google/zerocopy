#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Render canonical `correspondence-provenance.json` from source inputs.

Produces byte-for-byte identical JSON to Rust's
`trusted_bundle::render_correspondence_provenance` so Nix archive builds and
`cargo-anneal` verification receipts share one verified schema and inventory.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys


def _require_regular_file(path: Path, label: str, *, root: Path | None = None) -> bytes:
    """Verify ancestor dirs (from `root` if given) and leaf are non-symlinks."""
    if root is not None:
        rel = path.relative_to(root)
        cur = root
        for part in rel.parent.parts:
            cur = cur / part
            try:
                pst = cur.lstat()
            except OSError as exc:
                raise ValueError(f"missing {label} parent: {cur} ({exc})") from exc
            if stat.S_ISLNK(pst.st_mode) or not stat.S_ISDIR(pst.st_mode):
                raise ValueError(f"{label} parent must be a regular directory: {cur}")
    try:
        st = path.lstat()
    except OSError as exc:
        raise ValueError(f"missing {label}: {path} ({exc})") from exc
    if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
        raise ValueError(f"{label} must be a regular file: {path}")
    return path.read_bytes()


def _walk_regular_tree(root: Path, prefix: str, suffix: str | None = None) -> dict[str, str]:
    """Walk `root` without following symlinks and hash matching regular files."""
    try:
        root_st = root.lstat()
    except OSError as exc:
        raise ValueError(f"missing directory {prefix}: {root} ({exc})") from exc
    if stat.S_ISLNK(root_st.st_mode) or not stat.S_ISDIR(root_st.st_mode):
        raise ValueError(f"directory {prefix} must be a regular directory: {root}")

    def _raise_walk_error(err: OSError) -> None:
        raise ValueError(f"cannot traverse directory under {prefix}: {err}") from err

    hashes: dict[str, str] = {}
    for dirpath, dirnames, filenames in os.walk(
        root, followlinks=False, onerror=_raise_walk_error
    ):
        base = Path(dirpath)
        for name in dirnames:
            entry = base / name
            st = entry.lstat()
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
                raise ValueError(f"symlink or non-directory forbidden under {prefix}: {entry}")
        for name in filenames:
            entry = base / name
            st = entry.lstat()
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
                raise ValueError(f"symlink or non-regular file forbidden under {prefix}: {entry}")
            rel = f"{prefix}/{entry.relative_to(root).as_posix()}"
            if suffix is None or rel.endswith(suffix):
                hashes[rel] = hashlib.sha256(entry.read_bytes()).hexdigest()
    return dict(sorted(hashes.items()))


def _extract_string_array(rust_src: str, const_name: str) -> list[str]:
    pattern = re.compile(
        rf"pub const {re.escape(const_name)}:\s*&\[&str\]\s*=\s*&\[(.*?)\];",
        re.DOTALL,
    )
    match = pattern.search(rust_src)
    if match is None:
        raise ValueError(f"could not locate {const_name} in trusted_bundle.rs")
    return re.findall(r'"([^"]+)"', match.group(1))


def _decode_rust_string_escapes(raw: str) -> str:
    """Decode Rust string literal escapes while preserving UTF-8 characters."""
    out: list[str] = []
    i = 0
    n = len(raw)
    simple = {
        "n": "\n",
        "r": "\r",
        "t": "\t",
        "\\": "\\",
        '"': '"',
        "'": "'",
        "0": "\0",
    }
    while i < n:
        ch = raw[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        i += 1
        if i >= n:
            raise ValueError("unterminated escape in Rust string literal")
        esc = raw[i]
        i += 1
        if esc == "\n" or (esc == "\r" and i < n and raw[i] == "\n"):
            # Rust string continuation (`\` + LF/CRLF): omit the newline and any
            # following ASCII spaces, tabs, or newlines (including blank lines).
            if esc == "\r":
                i += 1
            while i < n and raw[i] in (" ", "\t", "\r", "\n"):
                i += 1
        elif esc in simple:
            out.append(simple[esc])
        elif esc == "x":
            hex_digits = raw[i : i + 2]
            if len(hex_digits) != 2:
                raise ValueError("invalid \\x escape in Rust string literal")
            code = int(hex_digits, 16)
            if code > 0x7F:
                raise ValueError("non-ASCII \\x escape in Rust string literal")
            out.append(chr(code))
            i += 2
        elif esc == "u" and i < n and raw[i] == "{":
            end = raw.find("}", i + 1)
            if end < 0:
                raise ValueError("unterminated \\u{...} escape in Rust string literal")
            out.append(chr(int(raw[i + 1 : end], 16)))
            i = end + 1
        else:
            raise ValueError(f"unsupported Rust string escape \\{esc}")
    return "".join(out)


def _extract_rust_string_const(rust_src: str, const_name: str) -> str:
    pattern = re.compile(
        rf'pub const {re.escape(const_name)}:\s*&str\s*=\s*"((?:[^"\\]|\\.)*)";',
        re.DOTALL,
    )
    match = pattern.search(rust_src)
    if match is None:
        raise ValueError(f"could not locate {const_name} in trusted_bundle.rs")
    return _decode_rust_string_escapes(match.group(1))


def _no_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    obj: dict[str, object] = {}
    for k, v in pairs:
        if k in obj:
            raise ValueError(f"duplicate JSON key: {k!r}")
        obj[k] = v
    return obj


def _is_sha256_hex(value: str) -> bool:
    return len(value) == 64 and all(c in "0123456789abcdefABCDEF" for c in value)


def render_provenance_json(
    *,
    trusted_bundle_rs: Path,
    upstream_pin: Path,
    correspondence_adapters_dir: Path,
    correspondence_proofs_dir: Path,
    trusted_lean_dir: Path,
    anneal_root: Path | None = None,
) -> str:
    """Validate inputs and return canonical `correspondence-provenance.json`."""
    rust_src = _require_regular_file(
        trusted_bundle_rs, "trusted_bundle.rs", root=anneal_root
    ).decode("utf-8")
    sysroot_sha = _extract_rust_string_const(rust_src, "LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256")
    if not _is_sha256_hex(sysroot_sha):
        raise ValueError(f"invalid sysroot manifest sha256: {sysroot_sha!r}")
    note = _extract_rust_string_const(rust_src, "CORRESPONDENCE_PROVENANCE_NOTE")

    trusted_sources = _extract_string_array(rust_src, "TRUSTED_BUNDLE_SOURCES")
    expected_trusted_lean = sorted(
        p for p in trusted_sources if p.startswith("trusted/lean/")
    )
    expected_adapters = sorted(_extract_string_array(rust_src, "CORRESPONDENCE_ADAPTER_PATHS"))
    expected_proofs = sorted(_extract_string_array(rust_src, "CORRESPONDENCE_PROOF_PATHS"))

    pin_bytes = _require_regular_file(upstream_pin, "UPSTREAM_PIN.json", root=anneal_root)
    upstream_pin_sha256 = hashlib.sha256(pin_bytes).hexdigest()
    pin = json.loads(pin_bytes.decode("utf-8"), object_pairs_hook=_no_duplicate_keys)
    if not isinstance(pin, dict):
        raise ValueError(f"expected JSON object in {upstream_pin}")
    for field in ("repository", "commit", "upstream_lean_toolchain", "build_lean_toolchain"):
        if not isinstance(pin.get(field), str) or not pin[field]:
            raise ValueError(
                f"empty or missing provenance metadata field {field} in {upstream_pin}"
            )

    raw_patched = pin.get("patched_files")
    if not isinstance(raw_patched, list) or any(
        not isinstance(e, dict) or not isinstance(e.get("path"), str) for e in raw_patched
    ):
        raise ValueError(f"malformed patched_files list in {upstream_pin}")

    patched_files = []
    seen_patched: set[str] = set()
    for entry in sorted(raw_patched, key=lambda e: e["path"]):
        path = entry.get("path")
        up_sha = entry.get("upstream_sha256")
        pa_sha = entry.get("patched_sha256")
        if (
            not isinstance(path, str)
            or not path
            or path in seen_patched
            or not isinstance(up_sha, str)
            or not _is_sha256_hex(up_sha)
            or not isinstance(pa_sha, str)
            or not _is_sha256_hex(pa_sha)
        ):
            raise ValueError(f"invalid patched_files entry in {upstream_pin}: {path!r}")
        seen_patched.add(path)
        patched_files.append(
            {
                "path": path,
                "upstream_sha256": up_sha,
                "patched_sha256": pa_sha,
            }
        )

    adapters = _walk_regular_tree(
        correspondence_adapters_dir, "trusted/correspondence", suffix=".lean"
    )
    if list(adapters.keys()) != expected_adapters:
        raise ValueError(
            "correspondence adapter inventory mismatch: "
            f"expected {expected_adapters}, found {list(adapters.keys())}"
        )

    proofs = _walk_regular_tree(correspondence_proofs_dir, "correspondence", suffix=".lean")
    if list(proofs.keys()) != expected_proofs:
        raise ValueError(
            "correspondence proof inventory mismatch: "
            f"expected {expected_proofs}, found {list(proofs.keys())}"
        )

    trusted_lean_all = _walk_regular_tree(trusted_lean_dir, "trusted/lean")
    trusted_lean: dict[str, str] = {}
    for rel in expected_trusted_lean:
        if rel not in trusted_lean_all:
            raise ValueError(f"missing canonical trusted/lean source: {rel}")
        trusted_lean[rel] = trusted_lean_all[rel]

    provenance = {
        "schema_version": 1,
        "upstream_repository": pin["repository"],
        "upstream_commit": pin["commit"],
        "upstream_lean_toolchain": pin["upstream_lean_toolchain"],
        "build_lean_toolchain": pin["build_lean_toolchain"],
        "upstream_pin_sha256": upstream_pin_sha256,
        "sysroot_foundation_manifest_sha256": sysroot_sha,
        "patched_files": patched_files,
        "correspondence_adapters": adapters,
        "correspondence_proofs": proofs,
        "trusted_lean": trusted_lean,
        "note": note,
    }
    return json.dumps(provenance, separators=(",", ":"), ensure_ascii=False)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anneal-root", type=Path)
    parser.add_argument("--trusted-bundle-rs", type=Path)
    parser.add_argument("--upstream-pin", type=Path)
    parser.add_argument("--correspondence-adapters-dir", type=Path)
    parser.add_argument("--correspondence-proofs-dir", type=Path)
    parser.add_argument("--trusted-lean-dir", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)

    root = args.anneal_root
    def resolve(explicit: Path | None, default_rel: str) -> Path:
        if explicit is not None:
            return explicit
        if root is not None:
            return root / default_rel
        raise SystemExit(f"missing required path argument for {default_rel}")

    payload = render_provenance_json(
        trusted_bundle_rs=resolve(
            args.trusted_bundle_rs, "trusted/cargo-anneal/src/trusted_bundle.rs"
        ),
        upstream_pin=resolve(args.upstream_pin, "vendor/lean-miri/UPSTREAM_PIN.json"),
        correspondence_adapters_dir=resolve(
            args.correspondence_adapters_dir, "trusted/correspondence"
        ),
        correspondence_proofs_dir=resolve(args.correspondence_proofs_dir, "correspondence"),
        trusted_lean_dir=resolve(args.trusted_lean_dir, "trusted/lean"),
        anneal_root=(
            root
            if all(
                x is None
                for x in (
                    args.trusted_bundle_rs,
                    args.upstream_pin,
                    args.correspondence_adapters_dir,
                    args.correspondence_proofs_dir,
                    args.trusted_lean_dir,
                )
            )
            else None
        ),
    )
    if args.output is not None:
        args.output.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
