#!/usr/bin/env python3
"""Inventory only already cached pins relevant to this paired-upgrade probe."""
import hashlib
import json
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
OLD = TOOLS / "scratch/20260928-reference-open-checks/aeneas_revision/old"
NEW = TOOLS / "aeneas-release"


def item(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size,
            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}


bundles = {}
for name, root, rust, aeneas_commit, charon_pin in (
    ("june1", OLD, "nightly-2026-04-18-aarch64-apple-darwin",
     "f95a80abaf554d4612cb60ef9ec8e849139bec44", "42836b36b666a980cbc9d438a8aed340ad3b848b"),
    ("june3", NEW, "nightly-2026-05-31-aarch64-apple-darwin",
     "ac9f1bc5262a5e4ff1e24ca78617121382202727", "a535e914f74db4fd9e6be7048f4233270d8945c0"),
):
    rustbin = TOOLS / "rustup/toolchains" / rust / "bin"
    bundles[name] = {"aeneas_source_commit": aeneas_commit, "charon_source_pin": charon_pin,
                     "rust_toolchain": rust, "rust_toolchain_file": (root / "rust-toolchain").read_text(),
                     "lean_toolchain_file": (root / "backends/lean/lean-toolchain").read_text().strip(),
                     "aeneas": item(root / "aeneas"), "charon": item(root / "charon"),
                     "charon_driver": item(root / "charon-driver"),
                     "rustc": item(rustbin / "rustc"), "cargo": item(rustbin / "cargo"),
                     "aeneas_olean": item(root / "backends/lean/.lake/build/lib/lean/Aeneas.olean")}

elan = TOOLS / "elan/toolchains"
lean_pins = {}
for root in sorted(p for p in elan.iterdir() if p.is_dir()):
    if (root / "bin/lean").is_file() and (root / "bin/lake").is_file():
        lean_pins[root.name] = {"lean": item(root / "bin/lean"), "lake": item(root / "bin/lake")}
nix_lean = [item(p) for p in sorted(Path("/nix/store").glob("*lean-toolchain*/bin/lean")) if p.is_file()]
unpaired_charon = {}
for name in ("old", "may31"):
    p = TOOLS / "scratch/20260928-reference-open-checks/charon_revision" / name / "charon"
    if p.is_file():
        unpaired_charon[name] = item(p)

result = {"bundles": bundles, "lean_pins": lean_pins, "nix_lean_pins": nix_lean,
          "unpaired_cached_charon": unpaired_charon,
          "disk_free_bytes_before_run": shutil.disk_usage(HERE).free,
          "scope": "Known cached release bundles, Elan toolchains and Nix Lean toolchain paths; no downloads or installs."}
later = []
for name in list(lean_pins) + [Path(x["path"]).parents[1].name for x in nix_lean]:
    match = re.search(r"v(\d+)\.(\d+)\.(\d+)", name)
    if match and tuple(map(int, match.groups())) > (4, 30, 0):
        later.append(name)
result["f03_later_than_4_30_pins"] = later
result["f03_later_than_4_30_available"] = bool(later)
assert not result["f03_later_than_4_30_available"]
(HERE / "local-pin-inventory.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
print("cached bundles", list(bundles), "elan pins", list(lean_pins), "nix Lean pins", len(nix_lean))
