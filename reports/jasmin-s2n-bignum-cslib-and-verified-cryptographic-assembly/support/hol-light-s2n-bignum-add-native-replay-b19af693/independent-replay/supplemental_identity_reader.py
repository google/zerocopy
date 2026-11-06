"""PROPOSED READ-ONLY QUERY. Not launched during the preparation review.

Direct ELF loader/DSO paths supplement, rather than replace, the author's
69-tool/2417-library inventories. This is not an observed process-mapping census.
"""
import hashlib
import json
import os
import stat
from pathlib import Path


def record(path):
    p = Path(path)
    q = p.resolve(strict=True)
    data = q.read_bytes()
    return {"path": str(p), "resolved": str(q), "symlink": p.is_symlink(),
            "link_target": os.readlink(p) if p.is_symlink() else None,
            "mode": oct(stat.S_IMODE(p.stat().st_mode)), "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


paths = [
    "/home/opam/anneal-cross-source-sha256sum.txt",
    "/home/opam/anneal-cross-output/selected.native",
    "/home/opam/anneal-cross-output/selected_inlined.ml",
    "/home/opam/anneal-cross-output/audit/AnnealDriver.ml",
    "/home/opam/anneal-cross-output/audit/AnnealSelectedAudit.ml",
    "/home/opam/anneal-cross-output/audit/build-selected-preserving.sh",
    "/lib/ld-linux-aarch64.so.1",
    "/lib/aarch64-linux-gnu/libgmp.so.10",
    "/lib/aarch64-linux-gnu/libm.so.6",
    "/lib/aarch64-linux-gnu/libc.so.6",
]
optional = ["/etc/ld.so.cache", "/etc/ld.so.conf", "/etc/ld.so.preload"]
optional += [str(p) for p in sorted(Path("/etc/ld.so.conf.d").glob("*.conf"))]
environment_keys = ["OPAMROOT", "OPAMSWITCH", "PATH", "LC_ALL", "HOLLIGHT_DIR",
                    "HOLLIGHT_LOAD_PATH", "LD_LIBRARY_PATH", "LD_PRELOAD", "LD_AUDIT",
                    "CAML_LD_LIBRARY_PATH", "OCAML_TOPLEVEL_PATH", "OCAMLPATH",
                    "OCAMLLIB", "OCAMLRUNPARAM"]
print(json.dumps({
    "classification": "Supplemental fresh identities; direct expected loader/DSO locations, not actual process maps or full OS closure",
    "uname": list(os.uname()),
    "files": [record(p) for p in paths],
    "loader_configuration": [{"path": p, "exists": Path(p).exists(),
                               "identity": record(p) if Path(p).exists() else None}
                              for p in optional],
    "effective_selected_environment": {k: os.environ.get(k) for k in environment_keys},
}, indent=2))
