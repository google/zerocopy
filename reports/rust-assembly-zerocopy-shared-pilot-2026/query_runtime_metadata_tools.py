"""Read-only identities for the two parent-authorized reader/wrapper tools."""
from pathlib import Path
import hashlib
import json
import os
import stat
import sys


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def identify(name):
    path = Path(name)
    resolved = path.resolve(strict=True)
    link = os.readlink(path) if path.is_symlink() else None
    return {"path": str(path), "resolved": str(resolved),
            "bytes": path.stat().st_size, "sha256": digest(path),
            "mode": oct(stat.S_IMODE(path.stat().st_mode)),
            "path_is_symlink": path.is_symlink(),
            "path_lstat_mode": oct(stat.S_IMODE(path.lstat().st_mode)),
            "link_target": link,
            "link_literal_sha256": hashlib.sha256(os.fsencode(link)).hexdigest() if link is not None else None,
            "resolved_target": {"path": str(resolved), "bytes": resolved.stat().st_size,
                                "sha256": digest(resolved),
                                "mode": oct(stat.S_IMODE(resolved.stat().st_mode))}}


print(json.dumps({"actual_python_executable": sys.executable,
                  "python_version": sys.version,
                  "tools": [identify("/usr/bin/env"), identify("/usr/bin/python3")],
                  "scope": "Read-only file identity; trusted reader/wrapper implementations; no target call"}, indent=2))
