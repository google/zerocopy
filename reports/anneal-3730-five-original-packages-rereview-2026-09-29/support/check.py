#!/usr/bin/env python3
"""Read-only verification of retained five-package review decisions."""
import hashlib
import json
from pathlib import Path

package = Path(__file__).resolve().parents[1]
reports = package.parent
review = json.loads((package / "support/review.json").read_text())
assert len(review["dispositions"]) == 5
assert len(review["files_sha256"]) == 18
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
for member, expected in review["files_sha256"].items():
    assert sha(reports / member) == expected, member
model = json.loads((reports / "anneal-interactive-model-probes-2026-09-29/support/model-probes.json").read_text())
cases = model["identity_ablation"]["cases"]
assert len(cases) == len({tuple(c["changed_fields"]) for c in cases}) == 10
assert any(c["changed_fields"] == ["llbc"] for c in cases)
checker = (reports / "lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/support/check.py").read_text()
assert 'for name, document_version in (("NewOpen.lean", 1), ("OldOpen.lean", 2)):' in checker
assert '"Tactic `rfl` failed" in item.get("message", "")' in checker
print("PASS: five dispositions, 18 retained file hashes, ten distinct identity deltas, Lean diagnostic assertions")
