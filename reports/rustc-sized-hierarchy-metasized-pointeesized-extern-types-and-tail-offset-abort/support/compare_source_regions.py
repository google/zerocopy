#!/usr/bin/env python3
"""Locate and compare the source regions this report cites across revisions.

For each `rust-lang/rust` revision given on the command line the script downloads
the cited files from `raw.githubusercontent.com` (or reads them from
`--cache-dir/<sha>/<path>` when present), extracts each cited region by a start
anchor plus brace matching, and records its 1-based line range, a SHA-256 of the
region text, and whether the text is identical to the first revision's.

Usage
  python3 compare_source_regions.py --out source_region_continuity.json \
      [--cache-dir DIR] <sha> [<sha> ...]

Python 3.10+, standard library only.  Network access to raw.githubusercontent.com
is needed for files that are not in the cache.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import urllib.request
from pathlib import Path

REPO = "rust-lang/rust"

# (label, path, mode, start regex[, line count])
#   mode "block": from the first line matching the regex to the line on which the
#                 first brace opened at or after that line is closed again;
#   mode "lines": the matching line plus (count - 1) following lines;
#   mode "file":  the whole file.
REGIONS = [
    ("core::marker::Sized", "library/core/src/marker.rs", "block", r"^pub trait Sized: MetaSized \{"),
    ("core::marker::MetaSized", "library/core/src/marker.rs", "block", r"^pub trait MetaSized: PointeeSized \{"),
    ("core::marker::PointeeSized", "library/core/src/marker.rs", "block", r"^pub trait PointeeSized \{"),
    ("core::mem::size_of_val", "library/core/src/mem/mod.rs", "block", r"^pub const fn size_of_val<T: \?Sized>\(val: &T\) -> usize \{"),
    ("core::mem::align_of_val", "library/core/src/mem/mod.rs", "block", r"^pub const fn align_of_val<T: \?Sized>\(val: &T\) -> usize \{"),
    ("core::ptr::Pointee", "library/core/src/ptr/metadata.rs", "lines", r"^pub trait Pointee: PointeeSized \{", 1),
    ("core::ptr::Thin", "library/core/src/ptr/metadata.rs", "lines", r"^pub trait Thin = Pointee<Metadata = \(\)> \+ PointeeSized;", 1),
    ("codegen size_and_align_of_dst", "compiler/rustc_codegen_ssa/src/size_of_val.rs", "block", r"^pub fn size_and_align_of_dst<"),
    ("codegen PlaceRef::project_field", "compiler/rustc_codegen_ssa/src/mir/place.rs", "block", r"^    pub fn project_field<"),
    ("interpreter project_field", "compiler/rustc_const_eval/src/interpret/projection.rs", "block", r"^    pub fn project_field<"),
    ("interpreter size_and_align_from_meta", "compiler/rustc_const_eval/src/interpret/eval_context.rs", "block", r"^    pub\(super\) fn size_and_align_from_meta\("),
    ("interpreter walk_value", "compiler/rustc_const_eval/src/interpret/visitor.rs", "block", r"^    fn walk_value\("),
    ("ExternTypeField message", "compiler/rustc_middle/src/mir/interpret/error.rs", "lines", r"`extern type` field does not have a known offset", 1),
    ("lowering add_implicit_sizedness_bounds", "compiler/rustc_hir_analysis/src/hir_ty_lowering/bounds.rs", "block", r"^    (pub\(crate\) )?fn add_implicit_sizedness_bounds\("),
    ("Ty::has_trivial_sizedness", "compiler/rustc_middle/src/ty/sty.rs", "block", r"^    pub fn has_trivial_sizedness\("),
    ("sizedness_constraint_for_ty", "compiler/rustc_ty_utils/src/ty.rs", "block", r"^fn sizedness_constraint_for_ty<"),
    ("assemble_builtin_sized_candidate", "compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs", "block", r"^    fn assemble_builtin_sized_candidate\("),
    ("place_unalignment", "compiler/rustc_const_eval/src/util/alignment.rs", "block", r"^pub fn place_unalignment<"),
    ("removed feature unsized_tuple_coercion", "compiler/rustc_feature/src/removed.rs", "lines", r"\(removed, unsized_tuple_coercion,", 2),
    ("miri sb_retag_place", "src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs", "block", r"^    fn sb_retag_place\("),
    ("miri tb NewPermission::new", "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs", "block", r"^    fn new\($"),
    ("miri tb_reborrow", "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs", "block", r"^    fn tb_reborrow\("),
    ("miri tb_retag_place", "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs", "block", r"^    fn tb_retag_place\("),
    ("miri Permission::associated_access", "src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs", "block", r"^    pub fn associated_access\("),
    ("miri visit_freeze_sensitive", "src/tools/miri/src/helpers.rs", "block", r"^    fn visit_freeze_sensitive\("),
    ("miri ExternTypeReborrow title", "src/tools/miri/src/diagnostics.rs", "lines", r"reborrow of a reference to `extern type` is not properly supported", 1),
    ("ui test extern-types-field-offset.rs", "tests/ui/extern/extern-types-field-offset.rs", "file", ""),
    ("ui test extern-types-field-offset.run.stderr", "tests/ui/extern/extern-types-field-offset.run.stderr", "file", ""),
    ("ui test extern-types-size_of_val.rs", "tests/ui/extern/extern-types-size_of_val.rs", "file", ""),
    ("ui test extern-types-size_of_val.stderr", "tests/ui/extern/extern-types-size_of_val.stderr", "file", ""),
    ("miri test pass/extern_types.rs", "src/tools/miri/tests/pass/extern_types.rs", "file", ""),
    ("miri test fail/extern-type-field-offset.rs", "src/tools/miri/tests/fail/extern-type-field-offset.rs", "file", ""),
]


def load(sha: str, path: str, cache: Path | None) -> bytes | None:
    if cache is not None:
        cached = cache / sha / path
        if cached.is_file():
            return cached.read_bytes()
    url = f"https://raw.githubusercontent.com/{REPO}/{sha}/{path}"
    try:
        with urllib.request.urlopen(url, timeout=60) as resp:
            data = resp.read()
    except Exception as exc:  # noqa: BLE001 - recorded in the output
        print(f"fetch failed: {url}: {exc}", file=sys.stderr)
        return None
    if cache is not None:
        target = cache / sha / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return data


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()


def extract(lines: list[str], mode: str, start_re: str, count: int) -> tuple[int, int] | None:
    if mode == "file":
        return (1, len(lines))
    pat = re.compile(start_re)
    start = next((i for i, ln in enumerate(lines) if pat.search(ln)), None)
    if start is None:
        return None
    if mode == "lines":
        return (start + 1, min(len(lines), start + count))
    depth = 0
    opened = False
    for i in range(start, len(lines)):
        for ch in lines[i]:
            if ch == "{":
                depth += 1
                opened = True
            elif ch == "}":
                depth -= 1
        if opened and depth == 0:
            return (start + 1, i + 1)
    return None


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("shas", nargs="+", help="full 40-hex rust-lang/rust revisions; the first is the baseline")
    ap.add_argument("--out", default=None)
    ap.add_argument("--cache-dir", default=None)
    args = ap.parse_args()
    cache = Path(args.cache_dir) if args.cache_dir else None

    result = {"repository": REPO, "revisions": args.shas, "regions": []}
    for label, path, mode, start_re, *rest in REGIONS:
        count = rest[0] if rest else 0
        entry = {"label": label, "path": path, "mode": mode, "per_revision": {}}
        baseline = None
        for sha in args.shas:
            data = load(sha, path, cache)
            if data is None:
                entry["per_revision"][sha] = {"status": "file_unavailable"}
                continue
            lines = data.decode("utf-8", errors="replace").splitlines()
            span = extract(lines, mode, start_re, count)
            if span is None:
                entry["per_revision"][sha] = {"status": "anchor_not_found", "file_git_blob": git_blob_sha1(data)}
                continue
            text = "\n".join(ln.rstrip() for ln in lines[span[0] - 1: span[1]]) + "\n"
            digest = hashlib.sha256(text.encode()).hexdigest()
            if baseline is None:
                baseline = digest
            entry["per_revision"][sha] = {
                "status": "ok",
                "lines": f"{span[0]}-{span[1]}",
                "region_sha256": digest,
                "identical_to_baseline": digest == baseline,
                "file_git_blob": git_blob_sha1(data),
            }
        result["regions"].append(entry)

    text = json.dumps(result, indent=1) + "\n"
    if args.out:
        Path(args.out).write_text(text)
    else:
        sys.stdout.write(text)
    for entry in result["regions"]:
        cells = []
        for sha in args.shas:
            pr = entry["per_revision"][sha]
            if pr["status"] != "ok":
                cells.append(f"{sha[:10]}:{pr['status']}")
            else:
                cells.append(f"{sha[:10]}:L{pr['lines']}{'=' if pr['identical_to_baseline'] else '*'}")
        print(f"{entry['label']:<44} " + "  ".join(cells), file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
