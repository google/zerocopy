#!/usr/bin/env python3
"""Census of the `src/stage0` seed manifest of a rust-lang/rust revision.

Usage:
    python3 rustc_stage0_census.py [--rev <40-hex commit>] [--file <local src/stage0>]

By default the manifest is downloaded from raw.githubusercontent.com at the
pinned revision below (the `1.99.1` release tag). Every number printed is
computed from the manifest text; nothing is hardcoded.

`src/stage0` format (see `src/bootstrap/bootstrap.py::parse_stage0_file` at the
same revision): `key=value` lines; keys that start with `dist/` map a download
path to the SHA-256 that `bootstrap.py::get` requires before using the file.
"""

import argparse
import collections
import hashlib
import json
import re
import shutil
import subprocess
import sys
import urllib.request

DEFAULT_REV = "58cf8f9c35b355199727627d07ae34a4e2846d67"  # rust-lang/rust tag 1.99.1
RAW = "https://raw.githubusercontent.com/rust-lang/rust/{rev}/{path}"


def fetch(rev: str, path: str) -> bytes:
    url = RAW.format(rev=rev, path=path)
    # Prefer curl over HTTP/1.1: some proxies truncate urllib's chunked reads.
    if shutil.which("curl"):
        r = subprocess.run(
            ["curl", "-sSLf", "--http1.1", "--max-time", "60", url],
            capture_output=True,
            check=True,
        )
        return r.stdout
    with urllib.request.urlopen(url, timeout=60) as r:
        return r.read()


def census(stage0: bytes) -> dict:
    config = {}
    artifacts = {}
    for raw in stage0.decode("utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition("=")
        if key.startswith("dist/"):
            artifacts[key] = value
        else:
            config[key] = value

    by_component = collections.Counter()
    by_ext = collections.Counter()
    hosts = collections.defaultdict(set)
    versions = set()
    bad_digest = 0
    pat = re.compile(
        r"^dist/(?P<date>\d{4}-\d{2}-\d{2})/(?P<comp>[a-z][a-z-]*?)-"
        r"(?P<ver>\d+\.\d+\.\d+|nightly|beta)-(?P<target>.+?)\.(?P<ext>tar\.gz|tar\.xz|msi|pkg)$"
    )
    unparsed = []
    for path, digest in artifacts.items():
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            bad_digest += 1
        m = pat.match(path)
        if not m:
            unparsed.append(path)
            continue
        by_component[m["comp"]] += 1
        by_ext[m["ext"]] += 1
        hosts[m["comp"]].add(m["target"])
        versions.add((m["date"], m["ver"]))

    return {
        "stage0_sha256": hashlib.sha256(stage0).hexdigest(),
        "config": config,
        "artifact_entries": len(artifacts),
        "entries_by_component": dict(sorted(by_component.items())),
        "entries_by_extension": dict(sorted(by_ext.items())),
        "distinct_targets_by_component": {k: len(v) for k, v in sorted(hosts.items())},
        "distinct_date_version_pairs": sorted(versions),
        "non_sha256_values": bad_digest,
        "unparsed_paths": unparsed,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rev", default=DEFAULT_REV)
    ap.add_argument("--file")
    args = ap.parse_args()
    if args.file:
        data = open(args.file, "rb").read()
        version = None
    else:
        data = fetch(args.rev, "src/stage0")
        version = fetch(args.rev, "src/version").decode().strip()
    out = {"repository": "rust-lang/rust", "revision": args.rev, "src_version": version}
    out.update(census(data))
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
