#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify bijective alignment of Cargo.toml, ci/pins/, and ci/checks.toml."""

from pathlib import Path
import re
import sys
import tomllib


def load_toml(path: Path) -> dict:
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    if not isinstance(data, dict):
        raise SystemExit(f"{path}: expected top-level TOML table")
    return data


def require_str_match(table: dict, key: str, pattern: str, path: str) -> str:
    val = table.get(key)
    if not isinstance(val, str) or not re.fullmatch(pattern, val):
        raise SystemExit(f"{path}: invalid {key} {val!r}")
    return val


def pin_arg_name(pin_id: str, key: str) -> str:
    norm_pin = re.sub(r"[^A-Za-z0-9]", "_", pin_id).upper()
    norm_key = re.sub(r"[^A-Za-z0-9]", "_", key).upper()
    return f"PIN_{norm_pin}__{norm_key}"


def verify_rust_toolchains(repo_root: Path) -> set[str]:
    pins_path = repo_root / "ci/pins/rust-toolchains.toml"
    cargo_path = repo_root / "zerocopy/Cargo.toml"

    pins = load_toml(pins_path)
    cargo = load_toml(cargo_path)

    pkg = cargo.get("package", {})
    meta = pkg.get("metadata", {})
    ci_meta = meta.get("ci", {})
    build_rs = meta.get("build-rs", {})

    expected: dict[str, str] = {
        "msrv": str(pkg["rust-version"]),
        "stable": str(ci_meta["pinned-stable"]),
        "nightly": str(ci_meta["pinned-nightly"]),
    }
    for key, val in build_rs.items():
        if not isinstance(val, str):
            raise SystemExit(
                f"{cargo_path}: non-string build-rs value for {key!r}"
            )
        expected[key] = val

    if pins != expected:
        missing = sorted(set(expected) - set(pins))
        extra = sorted(set(pins) - set(expected))
        mismatched = sorted(
            k for k in (set(expected) & set(pins)) if pins[k] != expected[k]
        )
        details = []
        if missing:
            details.append(f"missing in {pins_path}: {missing}")
        if extra:
            details.append(f"extra in {pins_path}: {extra}")
        if mismatched:
            details.append(
                "mismatched values: "
                + ", ".join(
                    f"{k}: pins={pins[k]!r} != Cargo.toml={expected[k]!r}"
                    for k in mismatched
                )
            )
        raise SystemExit(
            "ci/pins/rust-toolchains.toml out of sync with zerocopy/Cargo.toml: "
            + "; ".join(details)
        )
    return set(expected.keys())


def verify_other_pins(repo_root: Path) -> None:
    kani = load_toml(repo_root / "ci/pins/kani-pin.toml")
    require_str_match(
        kani, "version", r"[0-9]+\.[0-9]+\.[0-9]+", "ci/pins/kani-pin.toml"
    )
    require_str_match(
        kani, "bundle-sha256", r"[0-9a-f]{64}", "ci/pins/kani-pin.toml"
    )

    semver = load_toml(repo_root / "ci/pins/semver-baseline.toml")
    require_str_match(
        semver,
        "version",
        r"[0-9]+\.[0-9]+\.[0-9]+",
        "ci/pins/semver-baseline.toml",
    )
    require_str_match(
        semver,
        "crate-sha256",
        r"[0-9a-f]{64}",
        "ci/pins/semver-baseline.toml",
    )
    require_str_match(
        semver, "skip", r"true|false", "ci/pins/semver-baseline.toml"
    )
    require_str_match(
        semver,
        "tool-version",
        r"[0-9]+\.[0-9]+\.[0-9]+",
        "ci/pins/semver-baseline.toml",
    )
    require_str_match(
        semver,
        "tool-sha256",
        r"[0-9a-f]{64}",
        "ci/pins/semver-baseline.toml",
    )

    seed = load_toml(repo_root / "ci/pins/layout-seed.toml")
    require_str_match(seed, "seed", r"[0-9]+", "ci/pins/layout-seed.toml")


def verify_dockerfile_coverage(
    repo_root: Path, expected_toolchains: set[str]
) -> None:
    docker_dir = repo_root / "ci/docker"
    dockerfiles = sorted(docker_dir.glob("zc-*.Dockerfile"))
    if not dockerfiles:
        return
    declared: set[str] = set()
    by_file: dict[str, set[str]] = {}
    for df in dockerfiles:
        text = df.read_text(encoding="utf-8")
        args = set(
            re.findall(r"^ARG\s+(PIN_RUST_TOOLCHAINS__[A-Z0-9_]+)$", text, re.M)
        )
        by_file[df.name] = args
        declared |= args

    has_nightly_df = "zc-nightly.Dockerfile" in by_file
    required = {
        pin_arg_name("rust-toolchains", tc)
        for tc in expected_toolchains
        if has_nightly_df or tc != "nightly"
    }
    missing = sorted(required - declared)
    extra = sorted(declared - required)
    if missing or extra:
        raise SystemExit(
            "ci/docker/zc-*.Dockerfile toolchain ARGs out of sync: "
            f"missing={missing}, extra={extra}"
        )

    if (
        "zc-stable-msrv.Dockerfile" in by_file
        and "zc-build-rs.Dockerfile" in by_file
    ):
        sm_expected = {
            pin_arg_name("rust-toolchains", "msrv"),
            pin_arg_name("rust-toolchains", "stable"),
        }
        if by_file["zc-stable-msrv.Dockerfile"] != sm_expected:
            raise SystemExit(
                "ci/docker/zc-stable-msrv.Dockerfile must declare only "
                f"{sorted(sm_expected)}, got "
                f"{sorted(by_file['zc-stable-msrv.Dockerfile'])}"
            )
        build_rs_required = {
            pin_arg_name("rust-toolchains", tc)
            for tc in expected_toolchains
            if tc not in {"msrv", "stable", "nightly"}
        } | {pin_arg_name("rust-toolchains", "stable")}
        if by_file["zc-build-rs.Dockerfile"] != build_rs_required:
            raise SystemExit(
                "ci/docker/zc-build-rs.Dockerfile must declare "
                f"{sorted(build_rs_required)}, got "
                f"{sorted(by_file['zc-build-rs.Dockerfile'])}"
            )


def verify_checks_toml_coverage(
    repo_root: Path, expected_toolchains: set[str]
) -> None:
    checks_path = repo_root / "ci/checks.toml"
    if not checks_path.is_file():
        return
    checks_data = load_toml(checks_path)
    tested: set[str] = set()
    for entry in checks_data.get("checks", []):
        matrix = entry.get("matrix", {})
        if "toolchain" in matrix and isinstance(matrix["toolchain"], list):
            tested.update(str(v) for v in matrix["toolchain"])
        env = entry.get("env", {})
        tc_env = env.get("TOOLCHAIN")
        if isinstance(tc_env, str) and not tc_env.startswith("${"):
            tested.add(tc_env)
    if tested != expected_toolchains:
        missing = sorted(expected_toolchains - tested)
        extra = sorted(tested - expected_toolchains)
        raise SystemExit(
            "ci/checks.toml tested toolchains mismatch: "
            f"missing={missing}, extra={extra}"
        )


def main() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    expected_toolchains = verify_rust_toolchains(repo_root)
    verify_other_pins(repo_root)
    verify_dockerfile_coverage(repo_root, expected_toolchains)
    verify_checks_toml_coverage(repo_root, expected_toolchains)


if __name__ == "__main__":
    main()
