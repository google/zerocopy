#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Verify and query the 6-dimension PL, compiler, FFI, runtime, tooling, and verification taxonomy ledger."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG_DIR = HERE.parent
REPORTS_DIR = PKG_DIR.parent
REPO_ROOT = REPORTS_DIR.parent

SELF_SLUG = "pl-compiler-ffi-verification-problem-landscape-and-taxonomy"
SLUG_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
ALLOWED_BARRIER_CLASSES = {
    "undecidability",
    "impossibility_theorem",
    "semantic_chasm",
    "algorithmic_complexity",
    "hardware_physics",
    "socio_technical_tcb",
    "verification_scaling",
}


def validate_ledger(ledger: dict) -> tuple[list[str], dict]:
    """Validate structural integrity, cross-references, and corpus catalog membership."""
    errors: list[str] = []

    if ledger.get("schema") != "pl-compiler-ffi-verification-taxonomy/1":
        errors.append(f"Unexpected schema: {ledger.get('schema')!r}")
    if ledger.get("package_slug") != SELF_SLUG:
        errors.append(f"Unexpected package_slug: {ledger.get('package_slug')!r}")

    dimensions = ledger.get("dimensions", [])
    domain_pkgs = ledger.get("domain_packages", [])
    xref_pkgs = ledger.get("cross_referenced_packages", [])
    triangles = ledger.get("ffi_impossibility_triangles", [])
    open_problems = ledger.get("open_research_problems", [])

    if len(dimensions) != 6:
        errors.append(f"Expected exactly 6 taxonomy dimensions, found {len(dimensions)}")
    if len(domain_pkgs) != 38:
        errors.append(f"Expected exactly 38 domain packages, found {len(domain_pkgs)}")
    if len(xref_pkgs) < 30:
        errors.append(f"Expected at least 30 cross-referenced packages, found {len(xref_pkgs)}")
    if len(triangles) != 4:
        errors.append(f"Expected exactly 4 FFI impossibility triangles, found {len(triangles)}")
    if len(open_problems) < 25:
        errors.append(f"Expected at least 25 open research problems, found {len(open_problems)}")

    dim_ids: list[str] = []
    dim_id_set: set[str] = set()
    dim_dom_map: dict[str, set[str]] = {}
    dim_xref_map: dict[str, set[str]] = {}
    dim_op_map: dict[str, set[str]] = {}

    for idx, d in enumerate(dimensions, 1):
        did = d.get("id", "")
        if not did or not SLUG_RE.fullmatch(did):
            errors.append(f"dimensions[{idx - 1}]: invalid id {did!r}")
        elif did in dim_id_set:
            errors.append(f"Duplicate dimension id: {did!r}")
        else:
            dim_ids.append(did)
            dim_id_set.add(did)
        if d.get("number") != idx:
            errors.append(f"Dimension {did!r}: expected number {idx}, found {d.get('number')!r}")
        for req_key in (
            "title",
            "summary",
            "primary_topics",
            "irreducible_laws_and_barriers",
            "historical_contingencies_refuted",
            "domain_packages",
            "cross_referenced_packages",
            "open_problem_ids",
        ):
            if not d.get(req_key):
                errors.append(f"Dimension {did!r}: missing or empty {req_key!r}")
        dim_dom_map[did] = set(d.get("domain_packages", []))
        dim_xref_map[did] = set(d.get("cross_referenced_packages", []))
        dim_op_map[did] = set(d.get("open_problem_ids", []))

    # Validate 38 domain packages and exact partition across the 6 dimensions
    domain_slugs: set[str] = set()
    assigned_dom_by_dim: dict[str, set[str]] = {did: set() for did in dim_ids}
    for i, pkg in enumerate(domain_pkgs):
        slug = pkg.get("slug", "")
        if not SLUG_RE.fullmatch(slug):
            errors.append(f"domain_packages[{i}]: invalid slug {slug!r}")
        elif slug in domain_slugs:
            errors.append(f"Duplicate domain package slug: {slug!r}")
        else:
            domain_slugs.add(slug)

        did = pkg.get("dimension_id", "")
        if did not in dim_id_set:
            errors.append(f"domain_packages[{slug}]: unknown dimension_id {did!r}")
        else:
            assigned_dom_by_dim[did].add(slug)

        for sdid in pkg.get("secondary_dimensions", []):
            if sdid not in dim_id_set:
                errors.append(f"domain_packages[{slug}]: unknown secondary_dimension {sdid!r}")
            elif sdid == did:
                errors.append(f"domain_packages[{slug}]: secondary_dimensions repeats primary {did!r}")

        for req_key in ("title", "topics", "probes", "core_tensions", "findings_outline"):
            if not pkg.get(req_key):
                errors.append(f"domain_packages[{slug}]: missing or empty {req_key!r}")
        if not isinstance(pkg.get("subject_count"), int) or pkg["subject_count"] < 1:
            errors.append(f"domain_packages[{slug}]: subject_count must be positive int")
        for probe in pkg.get("probes", []):
            if not isinstance(probe, str) or not probe.endswith(".py"):
                errors.append(f"domain_packages[{slug}]: invalid probe script {probe!r}")

    if len(domain_slugs) != 38:
        errors.append(f"Expected 38 unique domain slugs, found {len(domain_slugs)}")

    partition_union: set[str] = set()
    for did in dim_ids:
        if dim_dom_map[did] != assigned_dom_by_dim[did]:
            errors.append(
                f"Dimension {did!r} domain_packages mismatch: "
                f"dim_only={sorted(dim_dom_map[did] - assigned_dom_by_dim[did])}, "
                f"pkg_only={sorted(assigned_dom_by_dim[did] - dim_dom_map[did])}"
            )
        overlap = partition_union & dim_dom_map[did]
        if overlap:
            errors.append(f"Domain packages assigned to multiple dimensions: {sorted(overlap)}")
        partition_union |= dim_dom_map[did]

    if partition_union != domain_slugs:
        errors.append(
            f"Dimension partition does not cover all 38 domain packages: "
            f"missing={sorted(domain_slugs - partition_union)}"
        )

    # Validate cross-referenced packages
    xref_slugs: set[str] = set()
    assigned_xref_by_dim: dict[str, set[str]] = {did: set() for did in dim_ids}
    for i, xp in enumerate(xref_pkgs):
        slug = xp.get("slug", "")
        if not SLUG_RE.fullmatch(slug):
            errors.append(f"cross_referenced_packages[{i}]: invalid slug {slug!r}")
        elif slug in xref_slugs:
            errors.append(f"Duplicate cross-referenced package slug: {slug!r}")
        elif slug in domain_slugs:
            errors.append(f"Cross-referenced package overlaps domain_packages: {slug!r}")
        else:
            xref_slugs.add(slug)

        did = xp.get("dimension_id", "")
        if did not in dim_id_set:
            errors.append(f"cross_referenced_packages[{slug}]: unknown dimension_id {did!r}")
        else:
            assigned_xref_by_dim[did].add(slug)

        if not xp.get("topics") or not xp.get("role"):
            errors.append(f"cross_referenced_packages[{slug}]: missing topics or role")

    for did in dim_ids:
        if dim_xref_map[did] != assigned_xref_by_dim[did]:
            errors.append(f"Dimension {did!r} cross_referenced_packages mismatch")

    all_indexed_slugs = domain_slugs | xref_slugs

    # Validate 4 FFI impossibility triangles
    tri_ids: set[str] = set()
    for i, tri in enumerate(triangles):
        tid = tri.get("id", "")
        if not tid or tid in tri_ids:
            errors.append(f"ffi_impossibility_triangles[{i}]: missing or duplicate id {tid!r}")
        tri_ids.add(tid)
        if len(tri.get("vertices", [])) != 3:
            errors.append(f"Triangle {tid!r}: must declare exactly 3 vertices")
        for req_key in ("name", "incompatible_triple", "formal_mechanism", "system_resolutions", "primary_packages"):
            if not tri.get(req_key):
                errors.append(f"Triangle {tid!r}: missing or empty {req_key!r}")
        if isinstance(tri.get("system_resolutions"), dict) and len(tri["system_resolutions"]) < 3:
            errors.append(f"Triangle {tid!r}: expected at least 3 concrete system_resolutions")
        for pslug in tri.get("primary_packages", []):
            if pslug not in all_indexed_slugs:
                errors.append(f"Triangle {tid!r}: unindexed package {pslug!r}")

    # Validate open research problems
    op_ids: set[str] = set()
    assigned_ops_by_dim: dict[str, set[str]] = {did: set() for did in dim_ids}
    barrier_counts: dict[str, int] = {}
    for i, op in enumerate(open_problems):
        oid = op.get("id", "")
        if not oid or oid in op_ids:
            errors.append(f"open_research_problems[{i}]: missing or duplicate id {oid!r}")
        op_ids.add(oid)
        did = op.get("dimension_id", "")
        if did not in dim_id_set:
            errors.append(f"Open problem {oid!r}: unknown dimension_id {did!r}")
        else:
            assigned_ops_by_dim[did].add(oid)
        bcls = op.get("barrier_class", "")
        if bcls not in ALLOWED_BARRIER_CLASSES:
            errors.append(f"Open problem {oid!r}: invalid barrier_class {bcls!r}")
        else:
            barrier_counts[bcls] = barrier_counts.get(bcls, 0) + 1
        for req_key in ("title", "statement", "why_open", "relevant_packages", "falsification_or_progress_trigger"):
            if not op.get(req_key):
                errors.append(f"Open problem {oid!r}: missing or empty {req_key!r}")
        for pslug in op.get("relevant_packages", []):
            if pslug not in all_indexed_slugs:
                errors.append(f"Open problem {oid!r}: unindexed package {pslug!r}")

    for did in dim_ids:
        if dim_op_map[did] != assigned_ops_by_dim[did]:
            errors.append(f"Dimension {did!r} open_problem_ids mismatch")

    # Verify declared counts match
    expected_counts = {
        "dimensions": len(dimensions),
        "domain_packages": len(domain_slugs),
        "cross_referenced_packages": len(xref_slugs),
        "total_mapped_packages": len(domain_slugs) + len(xref_slugs),
        "ffi_impossibility_triangles": len(triangles),
        "open_research_problems": len(open_problems),
    }
    if ledger.get("counts") != expected_counts:
        errors.append(f"counts mismatch: declared={ledger.get('counts')}, actual={expected_counts}")

    # Check CATALOG.json when running inside full corpus vs. isolated candidate sandbox
    cat_path = REPO_ROOT / "CATALOG.json"
    catalog_mode = "absent"
    catalog_size = 0
    if cat_path.is_file():
        cat_data = json.loads(cat_path.read_text(encoding="utf-8"))
        cat_reports = cat_data.get("reports", {})
        catalog_size = len(cat_reports)
        if catalog_size >= 370:
            catalog_mode = "full_corpus_subset_verified"
            allowed_full = set(cat_reports.keys()) | domain_slugs | {SELF_SLUG}
            missing_all = all_indexed_slugs - allowed_full
            if missing_all:
                errors.append(
                    f"CATALOG.json subset check failed: slugs missing from corpus: {sorted(missing_all)}"
                )
            missing_xrefs = xref_slugs - set(cat_reports.keys())
            if missing_xrefs:
                errors.append(
                    f"CATALOG.json missing cross-referenced packages: {sorted(missing_xrefs)}"
                )
        elif catalog_size < 50:
            catalog_mode = "isolated_sandbox_schema_verified"
        else:
            catalog_mode = "partial_corpus_schema_verified"

    summary = {
        "counts": expected_counts,
        "barrier_class_distribution": dict(sorted(barrier_counts.items())),
        "catalog_mode": catalog_mode,
        "catalog_report_count": catalog_size,
    }
    return errors, summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dimension",
        default="",
        help="Filter printed dimensions, packages, and open problems by dimension id, number, or title substring",
    )
    parser.add_argument(
        "--barrier",
        default="",
        help="Filter printed open problems by barrier_class substring",
    )
    parser.add_argument(
        "--triangles",
        action="store_true",
        help="Print detailed summary of the 4 FFI impossibility triangles",
    )
    parser.add_argument(
        "--open-problems",
        action="store_true",
        help="Print open research problems matching active filters",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit query/verification summary as machine-readable JSON",
    )
    args = parser.parse_args(argv)

    ledger = json.loads((HERE / "taxonomy_ledger.json").read_text(encoding="utf-8"))
    errors, summary = validate_ledger(ledger)
    if errors:
        for err in errors:
            sys.stderr.write(f"[FAIL] {err}\n")
        return 1

    dim_filter = args.dimension.strip().lower()
    shown_dims = ledger["dimensions"]
    if dim_filter:
        shown_dims = [
            d
            for d in shown_dims
            if dim_filter in d["id"].lower()
            or dim_filter in d["title"].lower()
            or dim_filter == str(d["number"])
            or dim_filter == f"d{d['number']}"
        ]
    shown_dim_ids = {d["id"] for d in shown_dims}

    shown_ops = [
        op
        for op in ledger["open_research_problems"]
        if op["dimension_id"] in shown_dim_ids
        and (not args.barrier or args.barrier.lower() in op["barrier_class"].lower())
    ]

    if args.json:
        payload = {
            "status": "ok",
            "summary": summary,
            "dimensions": shown_dims,
            "ffi_impossibility_triangles": ledger["ffi_impossibility_triangles"] if args.triangles or not dim_filter else [],
            "open_research_problems": shown_ops if args.open_problems or args.barrier or dim_filter else [],
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    c = summary["counts"]
    print(
        f"Verified {c['dimensions']} dimensions | {c['domain_packages']} domain packages | "
        f"{c['cross_referenced_packages']} cross-referenced packages ({c['total_mapped_packages']} total) | "
        f"{c['ffi_impossibility_triangles']} FFI triangles | {c['open_research_problems']} open problems | "
        f"catalog_mode={summary['catalog_mode']} (catalog_size={summary['catalog_report_count']})"
    )
    for d in shown_dims:
        print(
            f"  [D{d['number']} {d['id']}] {d['title']} "
            f"(domain={len(d['domain_packages'])}, xref={len(d['cross_referenced_packages'])}, ops={len(d['open_problem_ids'])})"
        )
        if dim_filter:
            for slug in d["domain_packages"]:
                print(f"    - domain: {slug}")
            for slug in d["cross_referenced_packages"]:
                print(f"    - xref:   {slug}")

    if args.triangles:
        print("FFI Impossibility Triangles:")
        for t in ledger["ffi_impossibility_triangles"]:
            print(f"  [{t['id']}] {t['name']}: {' | '.join(t['vertices'])}")

    if args.open_problems or args.barrier:
        print(f"Open Research Problems ({len(shown_ops)}):")
        for op in shown_ops:
            print(f"  [{op['id']} | {op['barrier_class']}] {op['title']} ({op['dimension_id']})")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
