#!/usr/bin/env python3
"""List every blob path in a GitHub tree at a pinned commit, descending into
subtrees whenever the recursive tree API response is truncated.
Usage: list_tree.py owner/repo sha > paths.tsv   (columns: path, blob_sha, size)
Requires an authenticated `gh` CLI (read-only GET requests only)."""
import json
import subprocess
import sys

repo, sha = sys.argv[1], sys.argv[2]


def api(path):
    out = subprocess.run(["gh", "api", path], capture_output=True, text=True, check=True).stdout
    return json.loads(out)


def walk(tree_sha, prefix):
    d = api(f"repos/{repo}/git/trees/{tree_sha}?recursive=1")
    if not d["truncated"]:
        for e in d["tree"]:
            if e["type"] == "blob":
                yield prefix + e["path"], e["sha"], e.get("size", 0)
        return
    # truncated: list one level and recurse into subtrees
    d1 = api(f"repos/{repo}/git/trees/{tree_sha}")
    for e in d1["tree"]:
        if e["type"] == "blob":
            yield prefix + e["path"], e["sha"], e.get("size", 0)
        elif e["type"] == "tree":
            yield from walk(e["sha"], prefix + e["path"] + "/")


root = api(f"repos/{repo}/commits/{sha}")["commit"]["tree"]["sha"]
for p, s, z in walk(root, ""):
    print(f"{p}\t{s}\t{z}")
