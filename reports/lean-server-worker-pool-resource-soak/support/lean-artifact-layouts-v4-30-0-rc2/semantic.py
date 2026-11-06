#!/usr/bin/env python3
"""One direct Lean visibility control for split annotations."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "semantic-work"
LEAN = Path(os.environ["LEAN_BIN"]).resolve()
EVENTS = []


def sha(x):
    return hashlib.sha256(x if isinstance(x, bytes) else x.encode()).hexdigest()


def run(label, argv):
    t = time.monotonic()
    p = subprocess.run(argv, cwd=WORK, env=dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(WORK)),
                       text=True, capture_output=True, timeout=15)
    result = {"label": label, "argv": argv, "rc": p.returncode,
              "stdout": p.stdout, "stderr": p.stderr,
              "wall_ms": round((time.monotonic() - t) * 1000, 1)}
    EVENTS.append(result)
    return p


if WORK.exists():
    shutil.rmtree(WORK)
WORK.mkdir()
sources = {
    "Shared.lean": "def modelValue : Nat := 7\ntheorem helper (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  rw [h]; rfl\n",
    "AnnOne.lean": "import Shared\ntheorem claimOne (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact helper n h\n",
    "AnnTwoWithoutImport.lean": "import Shared\ntheorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact claimOne n h\n",
    "AnnTwoWithImport.lean": "import AnnOne\ntheorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact claimOne n h\n",
    "Combined.lean": "import Shared\ntheorem claimOne (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact helper n h\ntheorem claimTwo (n : Nat) (h : n = modelValue) : n + 1 = 8 := by\n  exact claimOne n h\n",
}
for name, text in sources.items():
    (WORK / name).write_text(text)
assert run("compile-Shared", [str(LEAN), "--json", "-o", "Shared.olean", "Shared.lean"]).returncode == 0
assert run("compile-AnnOne", [str(LEAN), "--json", "-o", "AnnOne.olean", "AnnOne.lean"]).returncode == 0
without = run("without-import", [str(LEAN), "--json", "AnnTwoWithoutImport.lean"])
with_import = run("with-import", [str(LEAN), "--json", "AnnTwoWithImport.lean"])
combined = run("combined", [str(LEAN), "--json", "Combined.lean"])
assert without.returncode != 0 and "Unknown identifier `claimOne`" in without.stdout
assert with_import.returncode == 0 and combined.returncode == 0
out = {"lean_sha256": sha(LEAN.read_bytes()),
       "source_hashes": {name: sha(text) for name, text in sources.items()},
       "olean_hashes": {name: sha((WORK / name).read_bytes()) for name in ("Shared.olean", "AnnOne.olean")},
       "events": EVENTS,
       "interpretation": "A split sibling cannot use claimOne without importing AnnOne; the declared import or same-file order makes it visible."}
data = json.dumps(out, indent=2) + "\n"
data = data.replace(str(LEAN), "$LEAN_BIN").replace(str(WORK), "$WORK")
(ROOT / "semantic-results.json").write_text(data)
print(json.dumps({"without_import_rc": without.returncode,
                  "with_import_rc": with_import.returncode, "combined_rc": combined.returncode}))
