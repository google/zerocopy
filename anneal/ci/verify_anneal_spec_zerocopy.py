#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify `anneal-spec` zerocopy proofs, negatives, and Lean compilation."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.append(_CI_DIR)

import anneal_ci_lib
from verify_zerocopy import env_tool, is_safe_relative_filename, validate_receipt


def load_strict_json(text):
    """Parse JSON, rejecting duplicate object keys like `verify_zerocopy`."""
    return json.loads(
        text, object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys
    )


ALLOWED_EXTRA_FILES = frozenset({"spec.rs", "spec_span_map.json"})
NEG_UNIT = "02_unit_pointer_metadata"
LEAN_COMPILE_FIXTURE = "tests/lean_compile"
SPEC_IMPORT_ROOT = "Trusted.MirSemantics"
TRUSTED_IMPORT_RE = re.compile(
    r"^[ \t]*(?:public[ \t]+)?import[ \t]+(Trusted(?:\.[A-Za-z0-9_]+)*)[ \t]*$",
    re.M,
)


def discover_spec_units(proofs_dir, src_dir):
    """Validate `proofs_dir` hygiene and return ordered `(unit_dir, req)`."""
    if not proofs_dir.is_dir() or proofs_dir.is_symlink():
        raise RuntimeError(f"invalid anneal-spec proofs directory: {proofs_dir}")
    resolved_src = src_dir.resolve(strict=True)
    if not (resolved_src / "lib.rs").is_file():
        raise RuntimeError(f"zerocopy crate root missing: {resolved_src / 'lib.rs'}")

    units = []
    for entry in sorted(proofs_dir.iterdir(), key=lambda p: p.name):
        if entry.is_symlink():
            raise RuntimeError(f"symlink disallowed in proofs tree: {entry}")
        if not entry.is_dir():
            raise RuntimeError(f"unexpected entry in proofs tree: {entry}")

        unit_files = []
        for child in sorted(entry.iterdir(), key=lambda p: p.name):
            if child.is_symlink():
                raise RuntimeError(f"symlink disallowed in proof unit: {child}")
            if not child.is_file():
                raise RuntimeError(f"unexpected non-file entry in unit: {child}")
            unit_files.append(child.name)

        req_path = entry / "request.json"
        if not req_path.is_file():
            raise RuntimeError(f"missing request.json in proof unit: {entry}")
        request = load_strict_json(req_path.read_text(encoding="utf-8"))

        compilation = request.get("compilation")
        if not isinstance(compilation, dict):
            raise RuntimeError(f"{entry.name}: missing compilation table")
        source_root = compilation.get("source_root")
        if (
            not isinstance(source_root, str)
            or not source_root
            or Path(source_root).is_absolute()
        ):
            raise RuntimeError(
                f"{entry.name}: source_root must be relative: {source_root!r}"
            )
        unit_src = (entry / source_root).resolve(strict=True)
        if unit_src != resolved_src:
            raise RuntimeError(
                f"{entry.name}: source_root {source_root!r} != {resolved_src}"
            )

        scope = request.get("scope")
        roots = scope.get("roots") if isinstance(scope, dict) else None
        if (
            not isinstance(scope, dict)
            or scope.get("kind") != "selected_unit"
            or not isinstance(roots, list)
            or not roots
            or not all(isinstance(r, str) and r for r in roots)
        ):
            raise RuntimeError(f"{entry.name}: invalid selected_unit scope")

        proof = request.get("proof")
        if not isinstance(proof, dict) or proof.get("source_root") != ".":
            raise RuntimeError(f"{entry.name}: proof.source_root must be '.'")
        sources = proof.get("sources")
        if not isinstance(sources, list) or not sources:
            raise RuntimeError(f"{entry.name}: proof.sources must be non-empty")

        declared = {"request.json"} | ALLOWED_EXTRA_FILES
        for extra in ALLOWED_EXTRA_FILES:
            if not (entry / extra).is_file():
                raise RuntimeError(f"{entry.name}: missing {extra}")
        for source in sources:
            filename = source.get("path") if isinstance(source, dict) else None
            if not is_safe_relative_filename(filename) or not filename.endswith(
                ".lean"
            ):
                raise RuntimeError(f"{entry.name}: invalid source {filename!r}")
            if not (entry / filename).is_file():
                raise RuntimeError(f"{entry.name}: missing {filename}")
            declared.add(filename)

        unexpected = set(unit_files) - declared
        if unexpected:
            raise RuntimeError(
                f"{entry.name}: undeclared files: {sorted(unexpected)}"
            )
        units.append((entry, request))

    if not units:
        raise RuntimeError(f"no units discovered under {proofs_dir}")
    return units


def check_freshness(arguments, unit_dir):
    """Run `anneal-spec-lower --check` on `unit_dir`."""
    rel_spec = os.path.relpath(unit_dir / "spec.rs", arguments.src_root)
    proc = subprocess.run(
        [
            str(arguments.lower),
            "--src-root",
            str(arguments.src_root),
            "--check",
            str(unit_dir),
            rel_spec,
        ],
        capture_output=True,
        text=True,
        timeout=arguments.timeout,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"{unit_dir.name}: Spec.lean freshness check failed "
            f"(exit {proc.returncode}): {proc.stdout}{proc.stderr}"
        )


def trusted_module_order(trusted_root, root_module=SPEC_IMPORT_ROOT):
    """Return `(module, source)` for `root_module`'s `Trusted.*` closure.

    Modules come in dependency order, so each compiles after its imports.
    """
    sources = {}
    for path in [trusted_root / "Trusted.lean", *(trusted_root / "Trusted").rglob("*.lean")]:
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"invalid Trusted Lean source: {path}")
        rel = path.relative_to(trusted_root).with_suffix("")
        sources[".".join(rel.parts)] = path
    order = []
    state = {}

    def visit(module, chain):
        if state.get(module) == "done":
            return
        if state.get(module) == "active":
            raise RuntimeError(f"Trusted import cycle: {' -> '.join(chain)}")
        if module not in sources:
            raise RuntimeError(f"missing Trusted module {module} (via {' -> '.join(chain)})")
        state[module] = "active"
        text = sources[module].read_text(encoding="utf-8")
        for dep in TRUSTED_IMPORT_RE.findall(text):
            visit(dep, [*chain, dep])
        state[module] = "done"
        order.append((module, sources[module]))

    visit(root_module, [root_module])
    return order


def _run_lean_silently(arguments, lean_args, lib_dir, what):
    """Run Lean with `LEAN_PATH=lib_dir`; any message is a failure.

    Generated Lean must compile without warnings too, since `sorry` and
    linter findings surface only as warnings.
    """
    env = {"PATH": "/usr/bin:/bin", "LEAN_PATH": str(lib_dir)}
    for key in ("HOME", "TMPDIR", "LEAN_SYSROOT", "LD_LIBRARY_PATH"):
        if key in os.environ:
            env[key] = os.environ[key]
    proc = subprocess.run(
        [str(arguments.lean), *lean_args],
        env=env,
        capture_output=True,
        text=True,
        timeout=arguments.timeout,
        check=False,
    )
    if proc.returncode != 0 or proc.stdout or proc.stderr:
        raise RuntimeError(
            f"lean-compile: {what} failed (exit {proc.returncode}): "
            f"{proc.stdout}{proc.stderr}"
        )


def run_lean_compile_check(arguments, work_dir):
    """Compile the lowering fixture's generated `Spec.lean` and `Check.lean`.

    The zerocopy units only cover the lowerings their specifications use, so
    `tests/lean_compile/spec.rs` exercises every lowering that names a Lean
    library function. Its `Spec.lean` is built against `Trusted` `.olean`s
    compiled from this checkout, and `Check.lean` pins what its helpers mean.
    """
    fixture = arguments.src_root / LEAN_COMPILE_FIXTURE
    out_dir = work_dir / "lean-compile"
    lib_dir = out_dir / "lib"
    lib_dir.mkdir(parents=True)
    lower_proc = subprocess.run(
        [
            str(arguments.lower),
            "--src-root",
            str(arguments.src_root),
            "--out-dir",
            str(out_dir),
            f"{LEAN_COMPILE_FIXTURE}/spec.rs",
        ],
        capture_output=True,
        text=True,
        timeout=arguments.timeout,
        check=False,
    )
    if lower_proc.returncode != 0:
        raise RuntimeError(
            "lean-compile: anneal-spec-lower failed: "
            f"{lower_proc.stdout}{lower_proc.stderr}"
        )
    modules = trusted_module_order(arguments.trusted_lean)
    for module, source in modules:
        olean = lib_dir / f"{module.replace('.', '/')}.olean"
        olean.parent.mkdir(parents=True, exist_ok=True)
        _run_lean_silently(
            arguments,
            [f"--root={arguments.trusted_lean}", "-o", str(olean), str(source)],
            lib_dir,
            module,
        )
    # `cargo-anneal` compiles the specification with auto-bound implicits
    # disabled, so an unbound name in a generated declaration must fail here
    # too rather than silently becoming a universally quantified variable.
    _run_lean_silently(
        arguments,
        [
            "-DautoImplicit=false",
            "-DrelaxedAutoImplicit=false",
            f"--root={out_dir}",
            "-o",
            str(lib_dir / "Spec.olean"),
            str(out_dir / "Spec.lean"),
        ],
        lib_dir,
        "generated Spec.lean",
    )
    _run_lean_silently(
        arguments, [str(fixture / "Check.lean")], lib_dir, "Check.lean"
    )
    return {"status": "compiled", "trusted_modules": len(modules)}


def verify_unit(arguments, unit_dir, request, artifacts_root):
    """Run `cargo-anneal verify` on one unit and validate its Receipt v3."""
    check_freshness(arguments, unit_dir)
    cmd = [
        str(arguments.cli),
        "verify",
        "--format",
        "json",
        "--request",
        str(unit_dir / "request.json"),
        "--capture",
        str(arguments.capture),
        "--sysroot",
        str(arguments.sysroot),
        "--lean",
        str(arguments.lean),
        "--artifacts",
        str(artifacts_root / unit_dir.name),
    ]
    started = time.monotonic()
    proc = subprocess.run(
        cmd,
        cwd=unit_dir,
        capture_output=True,
        text=True,
        timeout=arguments.timeout,
        check=False,
    )
    elapsed = round(time.monotonic() - started, 3)
    (artifacts_root / f"{unit_dir.name}.stdout").write_text(
        proc.stdout, encoding="utf-8"
    )
    (artifacts_root / f"{unit_dir.name}.stderr").write_text(
        proc.stderr, encoding="utf-8"
    )
    receipt = validate_receipt(
        unit_dir.name,
        proc.returncode,
        proc.stdout,
        proc.stderr,
        request["scope"]["roots"],
        expected_profile=1,
        expected_spec_decl=request["proof"]["specification"],
        expected_proof_thm=request["proof"]["theorem"],
    )
    return unit_dir.name, {
        "status": receipt["status"],
        "axioms": receipt["audit"]["axioms"],
        "elaboration_sandbox": receipt["elaboration_sandbox"],
        "wall_seconds": elapsed,
    }


def _rewrite_source_root(unit_dir, src_dir):
    req_path = unit_dir / "request.json"
    req = load_strict_json(req_path.read_text(encoding="utf-8"))
    req["compilation"]["source_root"] = os.path.relpath(src_dir, unit_dir)
    req_path.write_text(json.dumps(req, indent=2) + "\n", encoding="utf-8")


def run_negative_controls(arguments, base_unit_dir, work_dir):
    """Confirm mutated Rust specs and mismatched signatures fail closed."""
    results = {}
    for case in ("mutated_spec_rs", "mismatched_signature"):
        neg_dir = work_dir / f"neg-{case}"
        shutil.copytree(base_unit_dir, neg_dir)
        _rewrite_source_root(neg_dir, arguments.src_dir)
        if case == "mutated_spec_rs":
            spec_rs = neg_dir / "spec.rs"
            src_text = spec_rs.read_text(encoding="utf-8")
            mutated = src_text.replace(
                "ensures(|count| count == 0)",
                "ensures(|count| count == 1)",
                1,
            )
            if mutated == src_text:
                raise RuntimeError("failed to mutate negative-control spec.rs")
            spec_rs.write_text(mutated, encoding="utf-8")
            lower_proc = subprocess.run(
                [
                    str(arguments.lower),
                    "--out-dir",
                    str(neg_dir),
                    str(spec_rs),
                ],
                capture_output=True,
                text=True,
                timeout=arguments.timeout,
                check=False,
            )
            if lower_proc.returncode != 0:
                raise RuntimeError(
                    f"{case}: anneal-spec-lower failed: "
                    f"{lower_proc.stdout}{lower_proc.stderr}"
                )
        else:
            spec_lean = neg_dir / "Spec.lean"
            lean_text = spec_lean.read_text(encoding="utf-8")
            mutated = lean_text.replace(
                "ret := .int .isize false }",
                "ret := .int .i32 false }",
                1,
            )
            if mutated == lean_text:
                raise RuntimeError(
                    "failed to mutate ContractSignature in Spec.lean"
                )
            spec_lean.write_text(mutated, encoding="utf-8")

        art_dir = work_dir / f"neg-artifacts-{case}"
        proc = subprocess.run(
            [
                str(arguments.cli),
                "verify",
                "--format",
                "json",
                "--request",
                str(neg_dir / "request.json"),
                "--capture",
                str(arguments.capture),
                "--sysroot",
                str(arguments.sysroot),
                "--lean",
                str(arguments.lean),
                "--artifacts",
                str(art_dir),
            ],
            cwd=neg_dir,
            capture_output=True,
            text=True,
            timeout=arguments.timeout,
            check=False,
        )
        (work_dir / f"neg-{case}.stdout").write_text(
            proc.stdout, encoding="utf-8"
        )
        (work_dir / f"neg-{case}.stderr").write_text(
            proc.stderr, encoding="utf-8"
        )
        if proc.returncode == 0:
            raise RuntimeError(
                f"{case}: negative control unexpectedly succeeded: {proc.stdout}"
            )
        try:
            receipt = load_strict_json(proc.stdout)
        except ValueError as exc:
            raise RuntimeError(
                f"{case}: invalid negative-control JSON receipt: {exc}\n"
                f"stdout={proc.stdout[:800]}\nstderr={proc.stderr[:800]}"
            ) from exc
        if receipt.get("status") != "proof_failed":
            raise RuntimeError(
                f"{case}: expected status 'proof_failed', got {receipt!r}"
            )
        results[case] = {"status": receipt["status"], "exit": proc.returncode}
    return results


def run_suite(arguments, work_dir):
    """Run all positive unit verifications and negative controls."""
    lean_compile = run_lean_compile_check(arguments, work_dir)
    units = discover_spec_units(arguments.proofs_dir, arguments.src_dir)
    workers = max(1, min(arguments.jobs, len(units)))
    started = time.monotonic()
    unit_results = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [
            pool.submit(verify_unit, arguments, unit_dir, request, work_dir)
            for unit_dir, request in units
        ]
        for future in futures:
            name, record = future.result()
            unit_results[name] = record
    neg_base = next((u for u, _ in units if u.name == NEG_UNIT), None)
    if neg_base is None:
        raise RuntimeError(f"missing negative-control base unit {NEG_UNIT}")
    negatives = run_negative_controls(arguments, neg_base, work_dir)
    summary = {
        "units": unit_results,
        "unit_count": len(unit_results),
        "negatives": negatives,
        "lean_compile": lean_compile,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (work_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    return summary


def main(argv=None):
    anneal_root = Path(__file__).resolve().parents[1]
    repo_root = anneal_root.parent
    spec_root = anneal_root / "tools/anneal-spec"

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--proofs-dir",
        type=Path,
        default=spec_root / "tests/zerocopy",
    )
    parser.add_argument("--src-root", type=Path, default=spec_root)
    parser.add_argument("--src-dir", type=Path, default=repo_root / "zerocopy/src")
    parser.add_argument(
        "--trusted-lean", type=Path, default=anneal_root / "trusted/lean"
    )
    parser.add_argument(
        "--lean-compile-only",
        action="store_true",
        help="Only lower and compile the tests/lean_compile fixture.",
    )
    parser.add_argument("--artifacts-dir", type=Path)
    parser.add_argument(
        "--jobs", type=int, default=min(4, max(1, os.cpu_count() or 1))
    )
    parser.add_argument("--timeout", type=int, default=600)
    for name in ("cli", "capture", "sysroot", "lean", "lower"):
        parser.add_argument(f"--{name}", type=Path)

    arguments = parser.parse_args(argv)
    env_fallbacks = {
        "cli": env_tool(["ANNEAL_CLI", "ANNEAL_TEST_CARGO_ANNEAL"]),
        "capture": env_tool(["ANNEAL_CAPTURE"], "bin/anneal-rustc-capture"),
        "sysroot": env_tool(["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"], "rust"),
        "lean": env_tool(["ANNEAL_LEAN"], "lean/bin/lean"),
        "lower": env_tool(["ANNEAL_SPEC_LOWER"]),
    }
    for name, fallback in env_fallbacks.items():
        if getattr(arguments, name) is None:
            setattr(arguments, name, fallback)
    required_tools = (
        ("lean", "lower")
        if arguments.lean_compile_only
        else ("cli", "capture", "sysroot", "lean", "lower")
    )
    for required in required_tools:
        val = getattr(arguments, required)
        if val is None:
            parser.error(f"the following arguments are required: --{required}")
        setattr(arguments, required, val.resolve(strict=True))

    arguments.proofs_dir = arguments.proofs_dir.resolve(strict=True)
    arguments.src_root = arguments.src_root.resolve(strict=True)
    arguments.src_dir = arguments.src_dir.resolve(strict=True)
    arguments.trusted_lean = arguments.trusted_lean.resolve(strict=True)

    def run(work_dir):
        if arguments.lean_compile_only:
            print(json.dumps(run_lean_compile_check(arguments, work_dir), indent=2))
        else:
            run_suite(arguments, work_dir)

    if arguments.artifacts_dir is not None:
        arguments.artifacts_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        run(arguments.artifacts_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(
            prefix="anneal-spec-zerocopy-"
        ) as tmp:
            run(Path(tmp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
