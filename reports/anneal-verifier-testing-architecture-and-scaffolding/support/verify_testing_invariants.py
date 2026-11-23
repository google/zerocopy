#!/usr/bin/env python3
"""Standalone standard-library probes for verifier toolchain testing invariants.

Verifies:
1. Workspace boundary lattice (`trusted/` vs `tests/` + `testkit` dependency monotonicity,
   `publish = false` enforcement, and `build.rs` prohibition) and optional checkout
   LOC/test-suite inventory when `--anneal-root` is provided.
2. Hermetic split-store symlink simulation:
   - `PermissionError` (`EACCES`) on naive `shutil.rmtree` of `0o555`/`0o444` simulated
     store trees vs. top-down owner-write restoration (`u+rwx` on directories before unlink);
   - `cwd` vs. `DT_RUNPATH` disjointness (`canon_cwd.starts_with(runpath_dir)`);
   - Host-path cross-package symlink rejection (`!canon_target.starts_with(canon_root)`) vs.
     unprivileged `bwrap --ro-bind <store> /nix/store` acceptance (`both_in_nix_store == True`
     and read-only mount enforcement).
3. Packaged Lean umbrella reachability vs. `theory/bundle-manifest.json` divergence
   when `--anneal-root` is provided.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile


def parse_lean_imports(src_text: str) -> list[str]:
    """Parse Lean header `import <Module>` edges skipping `--` and nested `/- ... -/` comments."""
    tokens: list[str] = []
    i = 0
    n = len(src_text)
    while i < n:
        if src_text[i].isspace():
            i += 1
            continue
        if src_text.startswith("--", i):
            nl = src_text.find("\n", i + 2)
            i = n if nl == -1 else nl + 1
            continue
        if src_text.startswith("/-", i):
            depth = 1
            i += 2
            while i < n and depth > 0:
                if src_text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src_text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        start = i
        while (
            i < n
            and not src_text[i].isspace()
            and not src_text.startswith("--", i)
            and not src_text.startswith("/-", i)
        ):
            i += 1
        tokens.append(src_text[start:i])
        if len(tokens) > 400:
            break

    imports: list[str] = []
    idx = 0
    while idx < len(tokens):
        tok = tokens[idx]
        if tok in ("prelude", "module", "public", "meta"):
            idx += 1
            continue
        if tok == "import":
            idx += 1
            if idx < len(tokens) and tokens[idx] == "all":
                idx += 1
            if idx < len(tokens):
                imports.append(tokens[idx])
                idx += 1
            continue
        break
    return imports


def check_boundary_lattice() -> dict:
    """Evaluate strict-target (`to in trusted/`) vs. monotonic 2-zone (`zone(to) <= zone(from)`) rules."""

    def zone_of(rel: str) -> int | None:
        if rel.startswith("trusted/"):
            return 0
        if rel.startswith("tests/"):
            return 1
        return None

    members = {
        "trusted/audit",
        "trusted/cargo-anneal",
        "trusted/rustc-capture",
        "tests/audit",
        "tests/cargo-anneal",
        "tests/rustc-capture",
        "tests/testkit",
        "tests/testkit_pub_true",
        "tests/testkit_with_build",
    }
    cases = [
        ("trusted/cargo-anneal", "trusted/audit", False, False, "trusted_to_trusted", True, True),
        ("trusted/audit", "tests/testkit", True, False, "trusted_to_testkit_forbidden", False, False),
        ("trusted/cargo-anneal", "tests/cargo-anneal", True, False, "trusted_to_tests_forbidden", False, False),
        ("tests/audit", "trusted/audit", True, False, "tests_to_trusted", True, True),
        ("tests/audit", "tests/testkit", True, False, "tests_to_testkit_shared_harness", False, True),
        ("tests/cargo-anneal", "tests/testkit", True, False, "tests_to_testkit_cargo_anneal", False, True),
        ("tests/rustc-capture", "tests/testkit", True, False, "tests_to_testkit_capture", False, True),
        ("tests/testkit", "trusted/cargo-anneal", True, False, "testkit_to_trusted", True, True),
        ("tests/testkit", "theory", True, False, "testkit_to_outside_forbidden", False, False),
        ("tests/testkit", "tests/unlisted", True, False, "testkit_to_nonmember_forbidden", False, False),
        ("tests/testkit_pub_true", "trusted/audit", False, False, "test_member_missing_publish_false", False, False),
        ("tests/testkit_with_build", "trusted/audit", True, True, "test_member_with_build_rs", False, False),
    ]

    rows = []
    for src, dst, publish_false, has_build_rs, label, exp_strict, exp_lattice in cases:
        z_src = zone_of(src)
        z_dst = zone_of(dst)
        member_ok = (src in members) and (dst in members) and (not has_build_rs)
        pub_ok = (z_src != 1) or publish_false
        strict_admits = member_ok and pub_ok and (z_src in (0, 1)) and (z_dst == 0)
        lattice_admits = (
            member_ok
            and pub_ok
            and (z_src in (0, 1))
            and (z_dst in (0, 1))
            and (z_dst <= z_src)
        )
        assert strict_admits == exp_strict, f"strict mismatch on {label}"
        assert lattice_admits == exp_lattice, f"lattice mismatch on {label}"
        rows.append({
            "case": label,
            "from": src,
            "to": dst,
            "strict_target_rule": strict_admits,
            "monotonic_lattice_rule": lattice_admits,
        })
    return {"cases_verified": len(rows), "comparison": rows}


def check_split_store_and_readonly_cleanup() -> dict:
    """Verify read-only `0o555` teardown, `cwd`/`DT_RUNPATH` disjointness, and `bwrap` `/nix/store` mount."""
    with tempfile.TemporaryDirectory(prefix="verifier-testing-probe-") as tmp:
        root = Path(tmp)
        ro_pkg = root / "ro_test/0001-pkg/lib"
        ro_pkg.mkdir(parents=True)
        (ro_pkg / "libfoo.so").write_bytes(b"stub")
        os.chmod(ro_pkg / "libfoo.so", 0o444)
        os.chmod(ro_pkg, 0o555)
        os.chmod(ro_pkg.parent, 0o555)

        naive_eacces = False
        try:
            shutil.rmtree(root / "ro_test")
        except PermissionError:
            naive_eacces = True
        assert naive_eacces, "expected naive rmtree on 0o555 directory to fail with PermissionError"

        for dirpath, _, _ in os.walk(root / "ro_test", topdown=True):
            p = Path(dirpath)
            os.chmod(p, stat.S_IMODE(p.lstat().st_mode) | 0o700)
        shutil.rmtree(root / "ro_test")
        guarded_ok = not (root / "ro_test").exists()
        assert guarded_ok, "expected top-down chmod u+rwx + rmtree to clean 0o555 tree"

        fake_store = root / "store"
        work_dir = root / "work"
        unwrapped = fake_store / "0001-lean-unwrapped/lib/lean/Init"
        joined = fake_store / "0002-lean-joined/lib/lean"
        unwrapped.mkdir(parents=True)
        joined.mkdir(parents=True)
        work_dir.mkdir(parents=True)
        (unwrapped.parent / "Init.olean").write_bytes(b"olean-header")
        os.symlink("../../../0001-lean-unwrapped/lib/lean/Init.olean", joined / "Init.olean")
        os.symlink("../../../0001-lean-unwrapped/lib/lean/Init", joined / "Init")

        canon_joined = joined.resolve()
        canon_target = (joined / "Init.olean").resolve()
        host_stays_within_joined = str(canon_target).startswith(str(canon_joined) + "/")
        assert not host_stays_within_joined

        canon_root = root.resolve()
        canon_work = work_dir.resolve()
        canon_store_lib = (fake_store / "0001-lean-unwrapped/lib").resolve()
        cwd_overlaps_parent = str(canon_work).startswith(str(canon_root) + "/")
        cwd_overlaps_sibling_store = str(canon_work).startswith(str(canon_store_lib) + "/")
        assert cwd_overlaps_parent and not cwd_overlaps_sibling_store

        bwrap = shutil.which("bwrap")
        bwrap_result: dict = {"available": bool(bwrap)}
        if bwrap:
            cmd = [
                bwrap,
                "--unshare-all",
                "--die-with-parent",
                "--new-session",
                "--clearenv",
                "--tmpfs",
                "/",
                "--proc",
                "/proc",
                "--dev",
                "/dev",
                "--ro-bind",
                "/usr",
                "/usr",
                "--ro-bind-try",
                "/lib",
                "/lib",
                "--ro-bind-try",
                "/lib64",
                "/lib64",
                "--ro-bind-try",
                "/bin",
                "/bin",
                "--ro-bind",
                str(fake_store),
                "/nix/store",
                "--",
                sys.executable,
                "-I",
                "-c",
                (
                    "import json, os; "
                    "r = os.path.realpath('/nix/store/0002-lean-joined/lib/lean'); "
                    "t = os.path.realpath('/nix/store/0002-lean-joined/lib/lean/Init.olean'); "
                    "ro = False\n"
                    "try:\n"
                    "  open('/nix/store/0002-lean-joined/write_probe', 'w')\n"
                    "except OSError:\n"
                    "  ro = True\n"
                    "print(json.dumps({'canon_root': r, 'canon_target': t, "
                    "'both_in_nix_store': r.startswith('/nix/store/') and t.startswith('/nix/store/'), "
                    "'read_only_enforced': ro}))"
                ),
            ]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=15, check=False)
            bwrap_result["exit_code"] = proc.returncode
            if proc.returncode == 0:
                bwrap_result.update(json.loads(proc.stdout.strip()))
                assert bwrap_result["both_in_nix_store"] is True
                assert bwrap_result["read_only_enforced"] is True
            else:
                bwrap_result["stderr"] = proc.stderr.strip()

        return {
            "naive_rmtree_failed_eacces_on_0o555": naive_eacces,
            "guarded_topdown_chmod_cleanup_succeeded": guarded_ok,
            "host_cross_pkg_symlink_stays_within_joined_root": host_stays_within_joined,
            "cwd_overlaps_enclosing_temp_root": cwd_overlaps_parent,
            "cwd_overlaps_disjoint_sibling_store_lib": cwd_overlaps_sibling_store,
            "bwrap_nix_store_mount_simulation": bwrap_result,
        }


def inspect_anneal_checkout(anneal_root: Path) -> dict:
    """Measure exact TCB/test inventory and Lean umbrella DAG metrics on an `anneal/` checkout."""
    trusted_dir = anneal_root / "trusted"
    all_trusted = sorted(p for p in trusted_dir.rglob("*") if p.is_file())
    prod_files = [p for p in all_trusted if "/tests/" not in p.as_posix()]
    test_files = [p for p in all_trusted if "/tests/" in p.as_posix()]
    prod_loc = sum(len(p.read_bytes().splitlines()) for p in prod_files)
    test_loc = sum(len(p.read_bytes().splitlines()) for p in test_files)

    # Support BOTH pre-migration (`trusted/*/tests/*.rs`) and post-migration (`tests/*/tests/*.rs`)
    integration_bins = sorted(trusted_dir.glob("*/tests/*.rs")) + sorted(
        (anneal_root / "tests").glob("*/tests/*.rs")
    )
    bin_rows = []
    for p in integration_bins:
        txt = p.read_text(encoding="utf-8")
        bin_rows.append({
            "path": p.relative_to(anneal_root).as_posix(),
            "lines": len(txt.splitlines()),
            "tests": len(re.findall(r"#\[\s*test\b", txt)),
            "ignored": len(re.findall(r"#\[\s*ignore\b", txt)),
        })

    # Umbrella DAG reachability vs `theory/bundle-manifest.json`
    trusted_lean = anneal_root / "trusted/lean"
    theory_dir = anneal_root / "theory"
    bundle_manifest = json.loads((theory_dir / "bundle-manifest.json").read_text(encoding="utf-8"))
    bundled_set = {
        m["path"].removeprefix("theory/").removesuffix(".lean").replace("/", ".")
        for m in bundle_manifest["modules"]
    }

    sources: dict[str, tuple[str, int]] = {}
    deps: dict[str, list[str]] = {}
    queue = ["Anneal"]
    while queue:
        mod = queue.pop(0)
        if mod in sources:
            continue
        rel = Path(mod.replace(".", "/") + ".lean")
        if (trusted_lean / rel).is_file():
            zone, src_path = "trusted", trusted_lean / rel
        elif (theory_dir / rel).is_file():
            zone, src_path = "theory", theory_dir / rel
        else:
            raise RuntimeError(f"unresolved Lean module {mod}")
        imps = [
            i
            for i in parse_lean_imports(src_path.read_text(encoding="utf-8"))
            if i == "Trusted"
            or i.startswith("Trusted.")
            or i == "Anneal"
            or i.startswith("Anneal.")
        ]
        for i in imps:
            if i not in sources:
                queue.append(i)
        sources[mod] = (zone, len(src_path.read_bytes().splitlines()))
        deps[mod] = imps

    memo: dict[str, tuple[int, int, list[str]]] = {}

    def crit(m: str) -> tuple[int, int, list[str]]:
        if m in memo:
            return memo[m]
        _, loc = sources[m]
        if not deps[m]:
            res = (1, loc, [m])
        else:
            best = max((crit(d) for d in deps[m]), key=lambda x: x[1])
            res = (best[0] + 1, best[1] + loc, best[2] + [m])
        memo[m] = res
        return res

    cp_depth, cp_loc, cp_chain = crit("Anneal")
    umbrella_theory = {m: loc for m, (z, loc) in sources.items() if z == "theory"}
    unbundled = {m: loc for m, loc in umbrella_theory.items() if m not in bundled_set}

    gm_txt = (anneal_root / "ci/check_guard_mutation.py").read_text(encoding="utf-8")
    mir_guards = len(re.findall(r'MirSemanticsGuard\(\s*guard_id="', gm_txt))
    audit_guards = len(re.findall(r'AuditHeaderGuard\(\s*guard_id="', gm_txt))

    return {
        "trusted_total_files": len(all_trusted),
        "trusted_total_lines": prod_loc + test_loc,
        "trusted_non_test_files": len(prod_files),
        "trusted_non_test_lines": prod_loc,
        "trusted_embedded_test_files": len(test_files),
        "trusted_embedded_test_lines": test_loc,
        "integration_binaries_count": len(bin_rows),
        "integration_binaries": bin_rows,
        "guard_mutation_mir_guards": mir_guards,
        "guard_mutation_audit_guards": audit_guards,
        "guard_mutation_total": mir_guards + audit_guards,
        "umbrella_reachable_modules": len(sources),
        "umbrella_total_lines": sum(loc for _, loc in sources.values()),
        "umbrella_trusted_modules": sum(1 for z, _ in sources.values() if z == "trusted"),
        "umbrella_theory_modules": len(umbrella_theory),
        "bundle_manifest_theory_modules": len(bundled_set),
        "umbrella_unbundled_theory_modules": len(unbundled),
        "umbrella_unbundled_theory_lines": sum(unbundled.values()),
        "critical_path_depth": cp_depth,
        "critical_path_lines": cp_loc,
        "critical_path_modules": cp_chain,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=None,
        help="Optional path to `anneal/` checkout for live repository inventory checks",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional output JSON path",
    )
    args = parser.parse_args()

    result: dict = {
        "boundary_lattice": check_boundary_lattice(),
        "split_store_and_readonly_cleanup": check_split_store_and_readonly_cleanup(),
    }
    if args.anneal_root is not None:
        result["anneal_checkout_inventory"] = inspect_anneal_checkout(args.anneal_root)

    rendered = json.dumps(result, indent=2) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
