"""Read-only validation of the frozen public file projection."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / "package-manifest.json").read_text())
errors = []
for row in manifest["files"]:
    path = root / row["path"]
    if not path.is_file():
        errors.append("missing: " + row["path"])
        continue
    data = path.read_bytes()
    if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
        errors.append("identity: " + row["path"])
    if re.search(rb"/Users/[A-Za-z0-9_.-]+/|/private/(?:tmp|var)/", data):
        errors.append("private display path: " + row["path"])
report = (root / "REPORT.md").read_text()
for target in re.findall(r"\]\(([^)]+)\)", report):
    if not target.startswith("http") and not (root / target.split("#")[0]).is_file():
        errors.append("report link: " + target)
metadata = json.loads((root / "REPORT.json").read_text())
if set(metadata) != {"topics", "subjects", "observed_at"}:
    errors.append("REPORT.json fields")
if report.count("Authored by an AI agent acting on joshlf's behalf.") != 1:
    errors.append("AI disclosure count")
print(json.dumps(dict(status="pass" if not errors else "fail", checked_files=len(manifest["files"]), errors=errors), indent=2))
raise SystemExit(bool(errors))
