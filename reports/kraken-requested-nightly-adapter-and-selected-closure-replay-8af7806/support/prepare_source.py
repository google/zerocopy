"""Copy only exact manifest-bound source files into a fresh owned build directory."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(__file__).resolve().parent.parent
source = Path(sys.argv[1]).resolve(strict=True)
destination = root / "kraken-source"
if destination.exists() or destination.is_symlink():
    raise SystemExit("Use a fresh package replay copy; kraken-source already exists")
manifest = json.loads((root / "source-copy-manifest.json").read_text())
prepared = []
for row in manifest["source_files"]:
    relative = Path(row["path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise SystemExit("Unsafe manifest path")
    path = source / relative
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(source):
        raise SystemExit("Source identity/type: " + str(relative))
    data = path.read_bytes()
    if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
        raise SystemExit("Source content: " + str(relative))
    prepared.append((relative, data))
destination.mkdir()
for relative, data in prepared:
    path = destination / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
print(json.dumps(dict(status="pass", copied_source_files=len(manifest["source_files"]), old_build_objects_copied=False)))
