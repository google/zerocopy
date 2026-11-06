#!/usr/bin/env python3
"""Freeze the 41 published #3732 source packages and the bounded #3731 map."""
import hashlib
import json
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORTS = ROOT / "reports"
SOURCE_COMMITS = ("e2692485db6b8417bf415c83223cfc5a99e73e4f", "0c504d98f5abafcbbd1460738e6d753378a6460e")

# Each short name has exactly one match in the frozen census. Empty tuples mean
# the #3732 packages add no ID-specific evidence, even if they offer background.
ID_SOURCES = {
    "I001": ("dafny-boogie", "proof-maintenance", "why3-", "lcf-", "fstar-"),
    "I002": ("rls-rust-analyzer-architecture-evolution", "rls-rust-analyzer-architecture-transition", "rls-to-rust-analyzer", "kotlin-swift", "typescript-host", "coq-rocq"),
    "I005": ("build-systems-a-la-carte", "salsa-rustc", "roslyn-", "self-adjusting", "persistent-data", "mvcc-"),
    "I007": ("isabelle-pide-document-processing-2008", "coq-rocq", "netstack3-", "theseus-", "redleaf-"),
    "I009": ("cargo-rustc", "functional-core-effects-hidden", "self-adjusting", "nix-guix-functional"),
    "I010": ("mvcc-", "roslyn-", "nix-guix-immutable", "reconciliation-"),
    "I011": ("adapton-", "mvcc-", "theseus-", "nix-guix-immutable"),
    "I015": ("early-cutoff", "salsa-rustc", "self-adjusting", "adapton-"),
    "I020": ("gopls-", "haskell-ide", "kotlin-swift", "cargo-rustc"),
    "I056": ("early-cutoff", "salsa-rustc", "self-adjusting", "persistent-data", "adapton-"),
    "I057": (),
    "I058": ("clangd-", "gopls-"),
    "I059": (),
    "I060": ("optimistic-edits", "mvcc-"),
    "I061": (),
    "I062": (),
    "I063": ("reconciliation-", "typescript-host"),
    "I064": ("typescript-host", "roslyn-", "gopls-", "reconciliation-"),
    "I096": ("haskell-ide", "typescript-host", "kotlin-swift", "clangd-"),
    "I144": ("information-hiding", "make-ninja", "buck-to", "compatibility-constrained", "functional-core-effect-boundaries", "functional-core-effects-hidden", "tock-asterinas-safe-interface-boundaries-2015", "tock-asterinas-safe-interface-boundaries-2017", "tock-asterinas-trusted", "lcf-", "fstar-"),
    "I145": ("adapton-", "nix-guix-functional", "nix-guix-immutable", "why3-", "theseus-", "lcf-"),
    "I157": ("typescript-host", "coq-rocq", "kotlin-swift", "isabelle-pide-document-processing-evolution", "lcf-"),
    "I159": ("rls-rust-analyzer-architecture-evolution", "rls-rust-analyzer-architecture-transition", "rls-to-rust-analyzer", "salsa-rustc", "buck-to", "redleaf-", "tock-asterinas-trusted", "fstar-"),
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    names = []
    for commit in SOURCE_COMMITS:
        paths = subprocess.check_output(["git", "diff-tree", "--no-commit-id", "--name-only", "-r", commit], cwd=ROOT, text=True).splitlines()
        names.extend(Path(path).parent.name for path in paths if path.startswith("reports/") and path.endswith("/REPORT.md"))
    assert len(names) == len(set(names)) == 41
    def expand(short):
        hits = [name for name in names if name.startswith(short)]
        assert len(hits) == 1, (short, hits)
        return hits[0]
    mapping = {item: [expand(short) for short in shorts] for item, shorts in ID_SOURCES.items()}
    assert len(mapping) == 23 and sum(not x for x in mapping.values()) == 4
    referenced = {name for value in mapping.values() for name in value}
    census = []
    for name in names:
        folder = REPORTS / name
        files = sorted(path for path in folder.rglob("*") if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
        census.append({"package": name, "commit": SOURCE_COMMITS[0] if name != "lcf-abstract-theorem-values-trust-boundaries-1978-2026" else SOURCE_COMMITS[1],
                       "mapped_ids": sorted(item for item, packages in mapping.items() if name in packages),
                       "report_sha256": sha(folder / "REPORT.md"),
                       "files": [{"path": path.relative_to(ROOT).as_posix(), "sha256": sha(path), "size": path.stat().st_size} for path in files]})
    assert len(referenced) >= 30
    (HERE / "id-map.json").write_text(json.dumps(mapping, indent=2, sort_keys=True) + "\n")
    (HERE / "source-census.json").write_text(json.dumps(census, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"packages": len(census), "mapped_packages": len(referenced), "mapped_ids": sum(bool(x) for x in mapping.values()), "unmapped_ids": [x for x,y in mapping.items() if not y]}, sort_keys=True))

if __name__ == "__main__":
    main()
