#!/usr/bin/env python3
"""File-count and byte-size census over a GitHub Git-trees API response.

Usage:
    gh api "repos/<owner>/<repo>/git/trees/<tree-or-commit-sha>?recursive=1" > tree.json
    python3 git_tree_census.py tree.json name=<regex> [name=<regex> ...]

Each `name=<regex>` selects blobs whose path matches the regular expression
(`re.search`) and reports how many there are and their total size in bytes, as
recorded by Git (the `size` field of each blob entry). Nothing is hardcoded.

Selections used for `git_tree_census_result.json`:
  thepowersgang/mrustc commit tree:
      all_c_cpp='\\.(cpp|hpp|h|c)$'   src_c_cpp='^src/.*\\.(cpp|hpp|h|c)$'
  ammkrn/nanoda_lib commit tree:
      src_rs_non_test='^src/(?!tests/).*\\.rs$'
  digama0/lean4lean commit tree:
      checker='^Lean4Lean/(?!(Theory|Verify|Experimental|Std|Tests)(/|\\.lean)).*\\.lean$'
      verify='^Lean4Lean/Verify(/|\\.lean).*'
  leanprover/lean4 `stage0` subtree (tree 2d2706e9bcba6cf49b549ba0f5d8d90fb621d205
  of commit 5045d0056413266e57c625dcd7c365b10e377c52):
      stdlib_c='^stdlib/.*\\.c$'   src_all='^src/'
"""

import json
import re
import sys


def main() -> int:
    tree = json.load(open(sys.argv[1]))
    blobs = [e for e in tree["tree"] if e["type"] == "blob"]
    out = {
        "tree_sha": tree.get("sha"),
        "truncated": tree.get("truncated"),
        "blobs": len(blobs),
        "bytes": sum(e["size"] for e in blobs),
        "selections": {},
    }
    for arg in sys.argv[2:]:
        name, _, pattern = arg.partition("=")
        rx = re.compile(pattern)
        sel = [e for e in blobs if rx.search(e["path"])]
        out["selections"][name] = {
            "regex": pattern,
            "files": len(sel),
            "bytes": sum(e["size"] for e in sel),
        }
    json.dump(out, sys.stdout, indent=2, sort_keys=True)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
