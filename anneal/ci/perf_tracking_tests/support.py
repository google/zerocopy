# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`_make_record` and the synthetic repository fixture shared by the
`perf_tracking.py` tests."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import stat
import subprocess

import perf_tracking
import prebuild_bundled_oleans


def _make_record(
    *,
    sha_idx: int = 1,
    unix_ts: int = 1795416000,
    profile: str = "github-ubuntu-24.04-x86_64",
    cpu_model: str = "AMD EPYC 7763 64-Core Processor",
    metrics: dict[str, float | int] | None = None,
) -> dict:
    sha = f"{sha_idx:040x}"
    return {
        "schema": perf_tracking.RECORD_SCHEMA,
        "commit": {
            "sha": sha,
            "short_sha": sha[:12],
            "timestamp": "2026-11-23T06:00:00Z",
            "unix_ts": unix_ts,
            "subject": f"Commit {sha_idx}",
            "branch": "main",
        },
        "environment": {
            "profile": profile,
            "os": "Linux",
            "arch": "x86_64",
            "cpu_model": cpu_model,
            "vcpu_count": 4,
            "ram_total_kib": 16374212,
            "lean_version": "4.34.1",
            "rustc_version": "rustc 1.98.0-nightly",
        },
        "sampling": {
            "verify_repeats": 3,
            "aggregation": "median",
            "rss_method": "usr_bin_time",
        },
        "metrics": metrics
        if metrics is not None
        else {
            "verify.scalar.cold_prebuilt_total_ms": 10000.0,
            "memory_rss.verify_scalar.cold_prebuilt_maxrss_kib": 512000,
            "artifact_size.bundled_olean.total_bytes": 10000000,
            "zerocopy_proofs.suite.verified_units_count": 5,
        },
    }


class SyntheticRepoFixture:
    def _build_synthetic_repo(self, root: Path) -> dict[str, Path]:
        repo = root / "repo"
        anneal = repo / "anneal"
        (anneal / "trusted/audit").mkdir(parents=True)
        (anneal / "trusted/lean/Trusted").mkdir(parents=True)
        (anneal / "trusted/cargo-anneal/src").mkdir(parents=True)
        (anneal / "trusted/cargo-anneal/tests/fixtures/scalar").mkdir(parents=True)
        (anneal / "theory/Anneal").mkdir(parents=True)
        (repo / "zerocopy/src").mkdir(parents=True)
        (repo / "zerocopy/proofs/01_demo").mkdir(parents=True)

        (repo / "zerocopy/src/lib.rs").write_text("pub fn id(x: u8) -> u8 { x }\n")
        (anneal / "trusted/audit/TrustedBoundary.lean").write_text("-- inspector\n")
        (anneal / "trusted/lean/Trusted.lean").write_text("prelude\nimport Init.Core\n")
        (anneal / "trusted/lean/Trusted/MirAst.lean").write_text(
            "prelude\nimport Trusted\n"
        )
        (anneal / "trusted/cargo-anneal/src/trusted_bundle.rs").write_text(
            'pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[\n'
            '    "trusted/lean/Trusted.lean",\n'
            '    "trusted/lean/Trusted/MirAst.lean",\n'
            '];\n'
        )
        wp = anneal / "theory/Anneal/MirWp.lean"
        wp.write_text("prelude\nimport Trusted.MirAst\n")
        wp_sha = hashlib.sha256(wp.read_bytes()).hexdigest()
        (anneal / "theory/bundle-manifest.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "modules": [
                        {"path": "theory/Anneal/MirWp.lean", "sha256": wp_sha}
                    ],
                }
            )
        )
        # Mock Lean sysroot + binary inside an omnibus-style bundle dir
        # (`bundle/lean` beside `bundle/share/anneal/prebuilt/manifest.json`).
        bundle_dir = root / "bundle"
        lean_prefix = bundle_dir / "lean"
        (lean_prefix / "lib/lean/Init").mkdir(parents=True)
        (lean_prefix / "lib/lean/Std").mkdir(parents=True)
        (lean_prefix / "src/lean/Init").mkdir(parents=True)
        (lean_prefix / "src/lean/Std").mkdir(parents=True)
        (lean_prefix / "bin").mkdir(parents=True)
        (bundle_dir / "share/anneal/prebuilt").mkdir(parents=True)
        (bundle_dir / "share/anneal/prebuilt/manifest.json").write_text(
            json.dumps({"schema_version": 1, "entries": []}),
            encoding="utf-8",
        )
        (lean_prefix / "lib/lean/Init/Core.olean").write_bytes(b"core")

        (anneal / "trusted/lean/foundation-lock.json").write_text(
            json.dumps({"modules": {"Init.Core": {}}, "graph": {"Init.Core": []}})
        )
        (anneal / "trusted/audit/library-lock.json").write_text(
            prebuild_bundled_oleans.render_library_lock_for_prefix(lean_prefix),
            encoding="utf-8",
        )

        # Scalar fixture
        scalar_dir = anneal / "trusted/cargo-anneal/tests/fixtures/scalar"
        for name in ("lib.rs", "Spec.lean", "Proof.lean"):
            (scalar_dir / name).write_text("// stub\n")
        (scalar_dir / "request.json").write_text(
            json.dumps({"scope": {"kind": "selected_unit", "roots": ["zero"]}})
        )

        # Zerocopy proof unit
        unit_dir = repo / "zerocopy/proofs/01_demo"
        (unit_dir / "Spec.lean").write_text(
            "-- spec\ndef specs : Specs := ⟨(), ()⟩\n", encoding="utf-8"
        )
        (unit_dir / "Proof.lean").write_text("prelude\n", encoding="utf-8")
        (unit_dir / "request.json").write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "compilation": {
                        "source_root": "../../src",
                        "crate_root": "lib.rs",
                        "crate_name": "zerocopy",
                        "edition": "2021",
                        "target": "x86_64-unknown-linux-gnu",
                        "cfg": [],
                        "env": {"CARGO_PKG_VERSION": "0.1.0"},
                        "source_files": ["lib.rs"],
                    },
                    "scope": {"kind": "selected_unit", "roots": ["id"]},
                    "proof": {
                        "source_root": ".",
                        "sources": [
                            {
                                "module": "Spec",
                                "path": "Spec.lean",
                                "role": "specification",
                            },
                            {
                                "module": "Proof",
                                "path": "Proof.lean",
                                "role": "proof",
                            },
                        ],
                    },
                }
            ),
            encoding="utf-8",
        )

        # Initialize git repo so commit metadata collection succeeds.
        for cmd in (
            ["git", "init", "-q"],
            ["git", "config", "user.name", "Test"],
            ["git", "config", "user.email", "test@example.com"],
            ["git", "add", "."],
            ["git", "commit", "-qm", "Initial synthetic repo"],
        ):
            subprocess.run(cmd, cwd=repo, check=True)

        lean_log = root / "lean_invocations.jsonl"
        fake_lean = lean_prefix / "bin/lean"
        fake_lean.write_text(
            f"""#!/usr/bin/env python3
import json, pathlib, sys
args = sys.argv[1:]
if "--version" in args:
    print("Lean (version 4.34.1, mock)")
    sys.exit(0)
if "--print-prefix" in args:
    # Return the invoked prefix (2 levels above bin/lean) so mirrored prefixes
    # report their own path accurately without resolving back to bundle/.
    print(pathlib.Path(__file__).resolve().parent.parent)
    sys.exit(0)
if "--run" in args:
    res = {{
        "ok": True,
        "result": {{
            "headers": [
                {{"module": "Trusted", "imports": [{{"module": "Init.Core", "isExported": True, "importAll": False, "isMeta": False}}]}},
                {{"module": "Trusted.MirAst", "imports": [{{"module": "Trusted", "isExported": True, "importAll": False, "isMeta": False}}]}},
                {{"module": "Anneal.MirWp", "imports": [{{"module": "Trusted.MirAst", "isExported": True, "importAll": False, "isMeta": False}}]}},
            ]
        }},
    }}
    pathlib.Path(args[-1]).write_text(json.dumps(res))
    sys.exit(0)
if "-o" in args:
    out = pathlib.Path(args[args.index("-o") + 1])
    with open({str(lean_log)!r}, "a", encoding="utf-8") as logf:
        logf.write(json.dumps({{"src": args[-1], "args": args}}) + "\\n")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(b"olean-public-" + out.name.encode())
    out.with_suffix(".olean.server").write_bytes(b"srv")
    out.with_suffix(".olean.private").write_bytes(b"priv-bytes")
    sys.exit(0)
sys.exit(1)
""",
            encoding="utf-8",
        )
        fake_lean.chmod(stat.S_IRWXU)

        # Mock cargo-anneal CLI + auxiliary binaries
        bin_dir = root / "bin"
        bin_dir.mkdir()
        cli_log = root / "cli_invocations.jsonl"
        fake_cli = bin_dir / "cargo-anneal"
        fake_cli.write_text(
            f"""#!/usr/bin/env python3
import hashlib, json, os, pathlib, sys
args = sys.argv[1:]
req_path = pathlib.Path(args[args.index("--request") + 1])
req = json.loads(req_path.read_text())
roots = req["scope"]["roots"]
instantiations = req["scope"].get("instantiations", [])
lean_arg = pathlib.Path(args[args.index("--lean") + 1]) if "--lean" in args else None
has_prebuilt = False
if lean_arg is not None:
    has_prebuilt = (lean_arg.parent.parent.parent / "share/anneal/prebuilt/manifest.json").is_file()
xdg = pathlib.Path(os.environ.get("XDG_CACHE_HOME", ""))
marker = xdg / "anneal/olean-cache/warm.marker"
if "--no-cache" not in args and "--no-rebuild-bundled" not in args and not has_prebuilt:
    marker.parent.mkdir(parents=True, exist_ok=True)
    marker.write_text("warm\\n", encoding="utf-8")
if "--no-rebuild-bundled" in args and not has_prebuilt and not marker.is_file():
    sys.stderr.write("missing disk cache under --no-rebuild-bundled\\n")
    sys.exit(1)
with open({str(cli_log)!r}, "a", encoding="utf-8") as logf:
    logf.write(json.dumps({{"args": args, "has_prebuilt": has_prebuilt, "has_marker": marker.is_file()}}) + "\\n")
fmt = "human"
if "--format" in args:
    fmt_idx = args.index("--format")
    if fmt_idx + 1 < len(args):
        fmt = args[fmt_idx + 1]
if fmt != "json":
    print("[SCOPED] VERIFIED (human default; --format json omitted)")
    sys.exit(0)
timing = {{"capture": 12.5, "proof_and_audit": 40.0, "total": 55.0}}
if "--no-cache" in args:
    timing = {{"capture": 15.0, "proof_and_audit": 120.0, "total": 140.0}}
receipt = {{
    "schema_version": 3,
    "status": "selected_unit_verified",
    "taint_reasons": [],
    "elaboration_sandbox": "linux_bwrap",
    "assumptions": [
        "faithful pinned compiler capture",
        "experimental pointer-free MIR semantics",
        "Lean kernel and admitted foundation",
        "intact compiler and verification environment",
    ],
    "deferred": [
        "complete review-surface reporting",
        "source-to-deployed-binary correspondence",
    ],
    "spec_warnings": [],
    "correspondence_provenance": {{
        "schema_version": 1,
        "upstream_repository": "https://github.com/proofs-rs/lean-miri",
        "upstream_commit": "c92d1d97",
        "upstream_lean_toolchain": "leanprover/lean4:v4.35.0",
        "build_lean_toolchain": "leanprover/lean4:v4.34.1",
        "upstream_pin_sha256": "a" * 64,
        "sysroot_foundation_manifest_sha256": "b" * 64,
        "patched_files": [],
        "minirust_upstream": {{
            "upstream_repository": "https://github.com/minirust/minirust",
            "upstream_commit": "d821c6e3",
            "upstream_pin_sha256": "f" * 64,
            "tarball_sha256": "0" * 64,
            "manifest_sha256": "1" * 64,
            "file_count": 1,
            "files": {{"spec/lang/syntax.md": "2" * 64}},
        }},
        "correspondence_adapters": {{
            "trusted/correspondence/Trusted/Correspondence.lean": "c" * 64,
        }},
        "correspondence_proofs": {{
            "correspondence/Anneal/MirCorrespondenceProof.lean": "d" * 64,
        }},
        "trusted_lean": {{
            "trusted/lean/Trusted/MirSemantics.lean": "e" * 64,
        }},
        "note": "pass2",
    }},
    "scope": {{
        "kind": "selected_unit",
        "roots": roots,
        **({{"instantiations": instantiations}} if instantiations else {{}}),
    }},
    "selected": [
        {{"def_id": i, "path": p, "body_index": i}}
        for i, p in enumerate(
            list(roots)
            + [
                f"{{e['path']}}::<{{', '.join(e['args'])}}>"
                if e.get("args")
                else e["path"]
                for e in (instantiations or [])
            ]
        )
    ] or [{{"def_id": 0, "path": "stub", "body_index": 0}}],
    "sources": [
        {{
            "relative_path": src,
            "sha256": hashlib.sha256(
                (
                    req_path.parent
                    / req.get("compilation", {{}}).get("source_root", ".")
                    / src
                ).read_bytes()
            ).hexdigest()
            if "compilation" in req
            else "srcsha",
        }}
        for src in req.get("compilation", {{}}).get("source_files", [])
    ],
    "configuration": {{
        k: v
        for k, v in req.get("compilation", {{}}).items()
        if k not in ("source_root", "source_files")
    }} | {{
        "crate_type": "lib",
        "panic": "unwind",
        "opt_level": 0,
        "debug_assertions": False,
        "overflow_checks": False,
        "mir_preserve_ub": True,
        "pointer_bits": 64,
        "endian": "little",
        "declared_source_files": req.get("compilation", {{}}).get(
            "source_files", []
        ),
    }},
    "request_sha256": "reqsha",
    "capture_sha256": "capsha",
    "specification_manifest_sha256": "specsha",
    "model_manifest_sha256": "modsha",
    "timing_ms": timing,
    "audit": {{
        "replay": True,
        "exactType": True,
        "checkedAlternateProofs": 0,
        "replayedDeclarations": 10,
        "sorryDeclarations": [],
        "axioms": ["propext"],
        "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
        "subject": "Captured.program",
        "expected": "Expected.claim",
        "specification": "Spec.specs",
        "theorem": "Proof.verify",
        "bindings": {{
            "requestSha256": "reqsha",
            "captureSha256": "capsha",
            "specificationManifestSha256": "specsha",
            "modelManifestSha256": "modsha",
        }},
    }},
}}
print(json.dumps(receipt))
""",
            encoding="utf-8",
        )
        fake_cli.chmod(stat.S_IRWXU)

        fake_capture = bin_dir / "anneal-rustc-capture"
        fake_capture.write_bytes(b"capture-bin-bytes")
        fake_capture.chmod(stat.S_IRWXU)
        fake_auditor = bin_dir / "anneal-audit"
        fake_auditor.write_bytes(b"auditor-bin")
        fake_auditor.chmod(stat.S_IRWXU)

        rust_sysroot = root / "rust_sysroot"
        (rust_sysroot / "bin").mkdir(parents=True)
        rustc = rust_sysroot / "bin/rustc"
        rustc.write_text("#!/bin/sh\necho 'rustc 1.98.0-nightly'\n")
        rustc.chmod(stat.S_IRWXU)

        archive = root / "omnibus.tar.zst"
        archive.write_bytes(b"zstd-archive-payload")

        fake_time = root / "time"
        fake_time.write_text(
            "#!/usr/bin/env python3\n"
            "import pathlib, subprocess, sys\n"
            "args = sys.argv[1:]\n"
            "out = pathlib.Path(args[args.index('-o') + 1])\n"
            "cmd = args[args.index('--') + 1:]\n"
            "res = subprocess.run(cmd)\n"
            "out.write_text('__ANNEAL_TIME_MAXRSS_KIB__=16384\\n')\n"
            "sys.exit(res.returncode)\n",
            encoding="utf-8",
        )
        fake_time.chmod(stat.S_IRWXU)

        return {
            "repo": repo,
            "anneal": anneal,
            "bundle": bundle_dir,
            "cli": fake_cli,
            "cli_log": cli_log,
            "capture": fake_capture,
            "auditor": fake_auditor,
            "sysroot": rust_sysroot,
            "lean": fake_lean,
            "lean_log": lean_log,
            "archive": archive,
            "time_bin": fake_time,
        }
