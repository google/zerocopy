#!/usr/bin/env python3
"""Revalidate Cargo lockfile/vendoring asymmetry and theory-carrier crate packaging.

Runs offline against a temporary Cargo local registry inside a self-cleaning
TemporaryDirectory and verifies:
  1. Upstream `[dev-dependencies]` are excluded from downstream `Cargo.lock`
     and `cargo vendor`.
  2. Upstream `optional = true` `[dependencies]` are excluded from downstream
     `Cargo.lock` and `cargo vendor` when inactive, included when activated by a
     feature, and included when declared directly on a workspace member.
  3. Upstream `[target.'cfg(any())'.dependencies]` are unconditionally included
     in downstream `Cargo.lock` and `cargo vendor` despite never being compiled.
  4. A `#![no_std]` `rust-version = "1.56.0"` theory-carrier crate carrying
     `.lean` files packages cleanly and records per-file SHA-256 digests in
     `.cargo-checksum.json` under `cargo vendor`.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile


def run(cmd: list[str], cwd: pathlib.Path) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
        )
    return proc


def lock_package_names(lockfile: pathlib.Path) -> list[str]:
    return sorted(
        line.split('"')[1]
        for line in lockfile.read_text(encoding="utf-8").splitlines()
        if line.startswith("name = ")
    )


def main() -> int:
    cargo_ver = run(["cargo", "--version"], pathlib.Path(".")).stdout.strip()
    print(f"cargo: {cargo_ver}")

    with tempfile.TemporaryDirectory(prefix="cargo_spec_pkg_probe_") as tmp_str:
        tmp = pathlib.Path(tmp_str)
        reg_dir = tmp / "local_reg"
        (reg_dir / "index").mkdir(parents=True)

        cfg_toml = (
            "[source.crates-io]\n"
            'replace-with = "local-reg"\n\n'
            "[source.local-reg]\n"
            f'local-registry = "{reg_dir.as_posix()}"\n'
        )

        def mk_crate(
            name: str,
            cargo_toml: str,
            lib_rs: str = "#![no_std]\n",
            extra_files: dict[str, str] | None = None,
        ) -> pathlib.Path:
            crate_dir = tmp / "src_crates" / name
            (crate_dir / "src").mkdir(parents=True)
            (crate_dir / ".cargo").mkdir(parents=True)
            (crate_dir / ".cargo" / "config.toml").write_text(cfg_toml, encoding="utf-8")
            (crate_dir / "Cargo.toml").write_text(cargo_toml, encoding="utf-8")
            (crate_dir / "src" / "lib.rs").write_text(lib_rs, encoding="utf-8")
            for rel, content in (extra_files or {}).items():
                dest = crate_dir / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(content, encoding="utf-8")
            return crate_dir

        def publish_local(
            crate_dir: pathlib.Path,
            name: str,
            vers: str,
            deps: list[dict[str, object]],
            features: dict[str, list[str]] | None = None,
            rust_version: str | None = None,
        ) -> str:
            run(["cargo", "package", "--no-verify", "--allow-dirty", "--offline"], crate_dir)
            tarball = crate_dir / "target" / "package" / f"{name}-{vers}.crate"
            cksum = hashlib.sha256(tarball.read_bytes()).hexdigest()
            shutil.copy2(tarball, reg_dir / f"{name}-{vers}.crate")
            idx_path = reg_dir / "index" / name[:2] / name[2:4] / name
            idx_path.parent.mkdir(parents=True, exist_ok=True)
            entry: dict[str, object] = {
                "name": name,
                "vers": vers,
                "deps": deps,
                "cksum": cksum,
                "features": features or {},
                "yanked": False,
            }
            if rust_version is not None:
                entry["rust_version"] = rust_version
            with idx_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(entry) + "\n")
            return cksum

        for leaf in ("dep-dev", "dep-opt", "dep-cfgany"):
            d = mk_crate(
                leaf,
                f'[package]\nname = "{leaf}"\nversion = "0.1.0"\nedition = "2021"\n',
            )
            publish_local(d, leaf, "0.1.0", [])

        theory_crate = mk_crate(
            "foo-spec-theory",
            '[package]\nname = "foo-spec-theory"\nversion = "0.1.0"\n'
            'edition = "2021"\nrust-version = "1.56.0"\n',
            lib_rs="#![no_std]\n",
            extra_files={"theory/Foo.lean": "prelude\ndef fooSpec : Prop := True\n"},
        )
        theory_cksum = publish_local(
            theory_crate, "foo-spec-theory", "0.1.0", [], rust_version="1.56.0"
        )

        upstream = mk_crate(
            "upstream-lib",
            """[package]
name = "upstream-lib"
version = "0.1.0"
edition = "2021"

[dependencies]
dep-opt = { version = "0.1.0", optional = true }

[target.'cfg(any())'.dependencies]
dep-cfgany = "0.1.0"

[dev-dependencies]
dep-dev = "0.1.0"
""",
        )
        publish_local(
            upstream,
            "upstream-lib",
            "0.1.0",
            [
                {
                    "name": "dep-opt",
                    "req": "^0.1.0",
                    "features": [],
                    "optional": True,
                    "default_features": True,
                    "target": None,
                    "kind": "normal",
                },
                {
                    "name": "dep-cfgany",
                    "req": "^0.1.0",
                    "features": [],
                    "optional": False,
                    "default_features": True,
                    "target": "cfg(any())",
                    "kind": "normal",
                },
                {
                    "name": "dep-dev",
                    "req": "^0.1.0",
                    "features": [],
                    "optional": False,
                    "default_features": True,
                    "target": None,
                    "kind": "dev",
                },
            ],
            {"dep-opt": ["dep:dep-opt"]},
        )

        # Case A: upstream optional dep disabled downstream.
        app_a = mk_crate(
            "downstream-app",
            """[package]
name = "downstream-app"
version = "0.1.0"
edition = "2021"

[dependencies]
upstream-lib = "0.1.0"
foo-spec-theory = "0.1.0"
""",
        )
        run(["cargo", "generate-lockfile", "--offline"], app_a)
        run(
            ["cargo", "vendor", "--respect-source-config", "--offline", str(app_a / "vendor")],
            app_a,
        )
        lock_a = lock_package_names(app_a / "Cargo.lock")
        vendor_a = sorted(p.name for p in (app_a / "vendor").iterdir())
        assert lock_a == ["dep-cfgany", "downstream-app", "foo-spec-theory", "upstream-lib"], lock_a
        assert vendor_a == ["dep-cfgany", "foo-spec-theory", "upstream-lib"], vendor_a

        ck_obj = json.loads(
            (app_a / "vendor" / "foo-spec-theory" / ".cargo-checksum.json").read_text(
                encoding="utf-8"
            )
        )
        assert ck_obj["package"] == theory_cksum, ck_obj
        assert "theory/Foo.lean" in ck_obj["files"], ck_obj
        assert "Cargo.toml.orig" in ck_obj["files"], ck_obj

        # Case B: upstream optional dep enabled downstream.
        app_b = mk_crate(
            "downstream-app-b",
            """[package]
name = "downstream-app-b"
version = "0.1.0"
edition = "2021"

[dependencies]
upstream-lib = { version = "0.1.0", features = ["dep-opt"] }
""",
        )
        run(["cargo", "generate-lockfile", "--offline"], app_b)
        run(
            ["cargo", "vendor", "--respect-source-config", "--offline", str(app_b / "vendor")],
            app_b,
        )
        lock_b = lock_package_names(app_b / "Cargo.lock")
        vendor_b = sorted(p.name for p in (app_b / "vendor").iterdir())
        assert lock_b == ["dep-cfgany", "dep-opt", "downstream-app-b", "upstream-lib"], lock_b
        assert vendor_b == ["dep-cfgany", "dep-opt", "upstream-lib"], vendor_b

        # Case C: direct optional dep of workspace member (disabled).
        app_c = mk_crate(
            "downstream-app-c",
            """[package]
name = "downstream-app-c"
version = "0.1.0"
edition = "2021"

[dependencies]
dep-opt = { version = "0.1.0", optional = true }
""",
        )
        run(["cargo", "generate-lockfile", "--offline"], app_c)
        run(
            ["cargo", "vendor", "--respect-source-config", "--offline", str(app_c / "vendor")],
            app_c,
        )
        lock_c = lock_package_names(app_c / "Cargo.lock")
        vendor_c = sorted(p.name for p in (app_c / "vendor").iterdir())
        assert lock_c == ["dep-opt", "downstream-app-c"], lock_c
        assert vendor_c == ["dep-opt"], vendor_c

        print("ALL ASSERTIONS PASSED:")
        print(f"  Case A (upstream opt disabled): lock={lock_a} vendor={vendor_a}")
        print(f"  Case B (upstream opt enabled):  lock={lock_b} vendor={vendor_b}")
        print(f"  Case C (workspace opt disabled): lock={lock_c} vendor={vendor_c}")
        print(f"  Theory carrier checksum files:  {sorted(ck_obj['files'].keys())}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
